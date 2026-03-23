#include <stdarg.h>
#include <stddef.h>
#include <setjmp.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/stat.h>
#include <cmocka.h>
/* cmocka < 1.0 didn't support these features we need */
#ifndef assert_ptr_equal
  #define assert_ptr_equal(a, b)                                      \
    _assert_int_equal(cast_ptr_to_largest_integral_type(a),           \
                      cast_ptr_to_largest_integral_type(b), __FILE__, \
                      __LINE__)
  #define CMUnitTest UnitTest
  #define cmocka_unit_test unit_test
  #define cmocka_run_group_tests(t, setup, teardown) run_tests(t)
#endif

extern void mock_assert(const int result, const char *const expression,
                        const char *const file, const int line);
#undef assert
#define assert(expression) \
  mock_assert((int)(expression), #expression, __FILE__, __LINE__);

#include "afl-fuzz.h"
#include "value-profile.h"

#ifndef ARRAY_SIZE
  #define ARRAY_SIZE(x) (sizeof(x) / sizeof((x)[0]))
#endif

/*
  Test model:
  - synthetic VP sites are reachable only when bytes marked PATH match
  - bytes marked VP affect per-site slot distances
  - all remaining bytes are neutral

  The suite runs phase1 + phase2 and verifies classification for
  contiguous, interleaved, multi-site, and multi-slot layouts, plus
  conservative/error paths.
 */
#define VP_TAINT_TEST_LEN 32U

/* Contiguous baseline layout constants. */
#define VP_TAINT_PATH_BEG 0U
#define VP_TAINT_VP_BEG 8U
#define VP_TAINT_NEUTRAL_BEG 16U
#define VP_TAINT_PATH_BLOCK_LEN 8U
#define VP_TAINT_VP_BLOCK_LEN 8U
#define VP_TAINT_NEUTRAL_BLOCK_LEN 16U

#define VP_TAINT_PATH_BYTE 0x41U
#define VP_TAINT_VP_BYTE 0x42U
#define VP_TAINT_VP_BYTE_2 0x44U
#define VP_TAINT_NEUTRAL_BYTE 0x43U

#define VP_TAINT_MODEL_MAX_SITES 4U
#define VP_TAINT_MODEL_MAX_SLOTS 4U

typedef enum {

  VP_TAINT_MODE_EQ = 0,
  VP_TAINT_MODE_LT_ONLY = 1,

} vp_taint_mode_t;

typedef struct {

  u8  used;
  u16 slot_key;
  u8  byte_used[VP_TAINT_TEST_LEN];
  u8  byte_target[VP_TAINT_TEST_LEN];
  u8  byte_mode[VP_TAINT_TEST_LEN];

} vp_taint_model_slot_t;

typedef struct {

  u8  used;
  u16 site_id;
  u8  path_used[VP_TAINT_TEST_LEN];
  u8  path_byte[VP_TAINT_TEST_LEN];
  u8  n_slots;
  vp_taint_model_slot_t slots[VP_TAINT_MODEL_MAX_SLOTS];

} vp_taint_model_site_t;

typedef struct {

  u16 site_id;
  u16 rel;

} vp_taint_owner_ref_t;

typedef struct {

  u8  vp_sensitive[VP_TAINT_TEST_LEN];
  u8  non_neutral[VP_TAINT_TEST_LEN];
  u8  path_sensitive[VP_TAINT_TEST_LEN];
  u8  neutral[VP_TAINT_TEST_LEN];
  u16 site_ids[VP_TAINT_MODEL_MAX_SITES];
  u32 site_sensitive_cnts[VP_TAINT_MODEL_MAX_SITES];
  u32 site_cnt;
  u32 exec_cnt;

} vp_taint_analysis_result_t;

static u8                  vp_taint_test_input[VP_TAINT_TEST_LEN];
static vp_taint_model_site_t vp_taint_model_sites[VP_TAINT_MODEL_MAX_SITES];
static u8                 *vp_taint_exec_buf;
static u32                 vp_taint_exec_len;
static afl_state_t        *vp_taint_exec_afl;
static u8                  vp_taint_force_run_error;
static u8                  vp_taint_force_stop_soon;

/* Stubs for symbols referenced by afl-fuzz-vp-taint.c. */
u32 write_to_testcase(afl_state_t *afl, void **mem, u32 len, u32 fix) {

  (void)fix;
  vp_taint_exec_afl = afl;
  vp_taint_exec_buf = (u8 *)*mem;
  vp_taint_exec_len = len;
  return len;

}

u8 *queue_testcase_get(afl_state_t *afl, struct queue_entry *q) {

  (void)afl;
  (void)q;
  return vp_taint_test_input;

}

void vp_runtime_set_site_filter(afl_state_t *afl, const u16 *site_ids,
                                u32 site_cnt) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (!vp) return;

  memset(vp->filter_bitmap, 0, sizeof(vp->filter_bitmap));
  for (u32 i = 0; i < site_cnt; ++i) {

    u16 site_id = site_ids[i];
    vp->filter_bitmap[site_id >> 6] |= (1ULL << (site_id & 63));

  }

  vp->filter_enabled = site_cnt ? 1U : 0U;

}

void vp_runtime_clear_site_filter(afl_state_t *afl) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (!vp) return;

  vp->filter_enabled = 0;
  memset(vp->filter_bitmap, 0, sizeof(vp->filter_bitmap));

}

u8 vp_runtime_observe_begin(afl_state_t *afl, const u16 *site_ids, u32 site_cnt,
                            vp_site_t *saved_sites,
                            vp_runtime_observe_mode_t mode) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (!vp || !site_ids || !site_cnt || !saved_sites) return 0;

  for (u32 i = 0; i < site_cnt; ++i) {

    u16 site_id = site_ids[i];
    saved_sites[i] = vp->site[site_id];

    switch (mode) {

      case VP_RUNTIME_OBSERVE_TAINT:
        memset(&vp->site[site_id].slots, 0xFF,
               sizeof(vp->site[site_id].slots));
        vp->site[site_id].valid_mask = 0;
        vp->site[site_id].touched_mask = 0;
        vp->site[site_id].protected_mask = 0;
        break;

      case VP_RUNTIME_OBSERVE_TRIM:
        memset(&vp->site[site_id], 0, sizeof(vp_site_t));
        vp->site[site_id].exec_seen = vp->exec_id;
        break;

      default:
        return 0;

    }

  }

  vp_runtime_set_site_filter(afl, site_ids, site_cnt);
  return 1;

}

void vp_runtime_observe_end(afl_state_t *afl, const u16 *site_ids, u32 site_cnt,
                            const vp_site_t *saved_sites) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (!vp || !site_ids || !site_cnt || !saved_sites) return;

  for (u32 i = 0; i < site_cnt; ++i) {

    vp->site[site_ids[i]] = saved_sites[i];

  }

  vp_runtime_clear_site_filter(afl);

}

AFL_RAND_RETURN rand_next(afl_state_t *afl) {

  (void)afl;
  static AFL_RAND_RETURN s = 0x9e3779b97f4a7c15ULL;
  s = s * 6364136223846793005ULL + 1ULL;
  return s;

}

static u64 vp_taint_fake_time_ms;
static u64 vp_taint_fake_time_step = 1;
u64        get_cur_time(void) {

  u64 now = vp_taint_fake_time_ms;
  vp_taint_fake_time_ms += vp_taint_fake_time_step;
  return now;

}

static void vp_taint_model_reset(void) {

  memset(vp_taint_test_input, VP_TAINT_NEUTRAL_BYTE, VP_TAINT_TEST_LEN);
  memset(vp_taint_model_sites, 0, sizeof(vp_taint_model_sites));
  vp_taint_force_run_error = 0;
  vp_taint_force_stop_soon = 0;

}

static vp_taint_model_site_t *vp_taint_model_site_get(u32 model_site_idx,
                                                       u16 site_id) {

  assert_true(model_site_idx < VP_TAINT_MODEL_MAX_SITES);
  vp_taint_model_site_t *site = &vp_taint_model_sites[model_site_idx];
  site->used = 1;
  site->site_id = site_id;
  return site;

}

static vp_taint_model_slot_t *vp_taint_model_slot_get(vp_taint_model_site_t *site,
                                                       u32 slot_idx,
                                                       u16 slot_key) {

  assert_true(slot_idx < VP_TAINT_MODEL_MAX_SLOTS);
  vp_taint_model_slot_t *slot = &site->slots[slot_idx];
  slot->used = 1;
  slot->slot_key = slot_key;
  if (site->n_slots < slot_idx + 1) site->n_slots = (u8)(slot_idx + 1);
  return slot;

}

static void vp_taint_model_set_path_range(u32 model_site_idx, u16 site_id,
                                          u32 start, u32 len,
                                          u8 path_byte) {

  vp_taint_model_site_t *site = vp_taint_model_site_get(model_site_idx, site_id);
  assert_true(start + len <= VP_TAINT_TEST_LEN);

  for (u32 i = start; i < start + len; ++i) {

    site->path_used[i] = 1;
    site->path_byte[i] = path_byte;
    vp_taint_test_input[i] = path_byte;

  }

}

static void vp_taint_model_set_vp_range_eq(u32 model_site_idx, u16 site_id,
                                           u32 slot_idx, u16 slot_key,
                                           u32 start, u32 len,
                                           u8 target_byte) {

  vp_taint_model_site_t *site = vp_taint_model_site_get(model_site_idx, site_id);
  vp_taint_model_slot_t *slot = vp_taint_model_slot_get(site, slot_idx, slot_key);
  assert_true(start + len <= VP_TAINT_TEST_LEN);

  for (u32 i = start; i < start + len; ++i) {

    slot->byte_used[i] = 1;
    slot->byte_target[i] = target_byte;
    slot->byte_mode[i] = VP_TAINT_MODE_EQ;
    vp_taint_test_input[i] = target_byte;

  }

}

static void vp_taint_model_set_vp_range_lt(u32 model_site_idx, u16 site_id,
                                           u32 slot_idx, u16 slot_key,
                                           u32 start, u32 len,
                                           u8 target_byte) {

  vp_taint_model_site_t *site = vp_taint_model_site_get(model_site_idx, site_id);
  vp_taint_model_slot_t *slot = vp_taint_model_slot_get(site, slot_idx, slot_key);
  assert_true(start + len <= VP_TAINT_TEST_LEN);

  for (u32 i = start; i < start + len; ++i) {

    slot->byte_used[i] = 1;
    slot->byte_target[i] = target_byte;
    slot->byte_mode[i] = VP_TAINT_MODE_LT_ONLY;
    vp_taint_test_input[i] = target_byte;

  }

}

static void vp_taint_model_set_neutral_range(u32 start, u32 len) {

  assert_true(start + len <= VP_TAINT_TEST_LEN);

  for (u32 i = start; i < start + len; ++i) {

    vp_taint_test_input[i] = VP_TAINT_NEUTRAL_BYTE;

    for (u32 s = 0; s < VP_TAINT_MODEL_MAX_SITES; ++s) {

      vp_taint_model_sites[s].path_used[i] = 0;
      vp_taint_model_sites[s].path_byte[i] = 0;
      for (u32 k = 0; k < VP_TAINT_MODEL_MAX_SLOTS; ++k) {

        vp_taint_model_sites[s].slots[k].byte_used[i] = 0;
        vp_taint_model_sites[s].slots[k].byte_target[i] = 0;
        vp_taint_model_sites[s].slots[k].byte_mode[i] = VP_TAINT_MODE_EQ;

      }

    }

  }

}

static u8 vp_taint_model_path_ok(const vp_taint_model_site_t *site,
                                 const u8 *buf) {

  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i) {

    if (site->path_used[i] && buf[i] != site->path_byte[i]) return 0;

  }

  return 1;

}

static u16 vp_taint_model_slot_dist(const vp_taint_model_slot_t *slot,
                                    const u8 *buf) {

  u32 dist = 1;
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i) {

    if (!slot->byte_used[i]) continue;

    if (slot->byte_mode[i] == VP_TAINT_MODE_EQ) {

      if (buf[i] != slot->byte_target[i]) dist++;

    } else {

      if (buf[i] < slot->byte_target[i]) {

        dist += (u32)(slot->byte_target[i] - buf[i]);

      }

    }

  }

  if (dist > 0xffffU) dist = 0xffffU;
  return (u16)dist;

}

fsrv_run_result_t fuzz_run_target(afl_state_t *afl, afl_forkserver_t *fsrv,
                                  u32 timeout) {

  (void)fsrv;
  (void)timeout;

  assert_ptr_equal(afl, vp_taint_exec_afl);
  assert_non_null(afl->shm.vp_map);

  vp_map_t *vp = afl->shm.vp_map;
  ++vp->exec_id;
  if (!vp->exec_id) ++vp->exec_id;

  if (!vp_taint_exec_buf || vp_taint_exec_len < VP_TAINT_TEST_LEN)
    return FSRV_RUN_ERROR;

  if (vp_taint_force_run_error) {

    vp_taint_force_run_error = 0;
    return FSRV_RUN_ERROR;

  }

  if (vp_taint_force_stop_soon) {

    vp_taint_force_stop_soon = 0;
    afl->stop_soon = 1;

  }

  for (u32 s = 0; s < VP_TAINT_MODEL_MAX_SITES; ++s) {

    vp_taint_model_site_t *model = &vp_taint_model_sites[s];
    if (!model->used) continue;
    if (!vp_taint_model_path_ok(model, vp_taint_exec_buf)) continue;
    if (vp->filter_enabled &&
        !(vp->filter_bitmap[model->site_id >> 6] &
          (1ULL << (model->site_id & 63)))) {

      continue;

    }

    assert_true(model->site_id < CMP_MAP_W);
    vp_site_t *site = &vp->site[model->site_id];

    site->exec_seen = vp->exec_id;
    site->valid_mask = 0;
    site->touched_mask = 0;
    site->protected_mask = 0;

    for (u32 k = 0; k < model->n_slots; ++k) {

      vp_taint_model_slot_t *slot = &model->slots[k];
      if (!slot->used) continue;

      site->valid_mask |= (u16)(1U << k);
      site->touched_mask |= (u16)(1U << k);
      site->protected_mask |= (u16)(1U << k);
      site->slots[k].slot_key = slot->slot_key;
      site->slots[k].best_dist = vp_taint_model_slot_dist(slot, vp_taint_exec_buf);

    }

  }

  return FSRV_RUN_OK;

}

/* remap exit -> assert, then use cmocka's mock_assert
   (compile with `--wrap=exit`) */
extern void exit(int status);
extern void __real_exit(int status);
void        __wrap_exit(int status) {

  (void)status;
  assert(0);

}

/* ignore all printfs */
#undef printf
extern int printf(const char *format, ...);
int        __wrap_printf(const char *format, ...) {

  (void)format;
  return 1;

}

/* Pull in internal VP taint helpers for white-box classification tests. */
#include "../../src/afl-fuzz-vp-taint.c"

static void vp_taint_bitmap_from_list(const struct queue_entry *q,
                                      u8 *bitmap, u32 len) {

  memset(bitmap, 0, len);
  for (u32 n = 0; q && n < q->vp_taint_cnt; ++n) {

    const vp_taint_site_t *node = &q->vp_taint[n];
    if (!node->sensitive_cnt) continue;
    for (u32 i = 0; i < node->sensitive_cnt; ++i) {

      assert_true(node->sensitive_positions[i] < len);
      bitmap[node->sensitive_positions[i]] = 1;

    }

  }

}

static size_t vp_taint_frontier_span(u32 slots) {

  return (size_t)slots * VP_RUNTIME_SLOT_REPLICA_LIMIT;

}

static void vp_taint_rebuild_owned_sites(afl_state_t *afl, struct queue_entry *q) {

  u16 *old_sites = q->vp_owned_sites;
  u32  old_cnt = q->vp_owned_site_cnt;

  q->vp_owned_sites = NULL;
  q->vp_owned_site_cnt = 0;
  q->vp_owned_site_cap = 0;
  q->vp_ref_cnt = 0;

  size_t span = vp_taint_frontier_span(afl->value_profile_slots);
  for (u32 site = 0; site < CMP_MAP_W; ++site) {

    u8 found = 0;
    for (size_t rel = 0; rel < span; ++rel) {

      size_t idx = (size_t)site * span + rel;
      if (afl->vp_frontier[idx].owner != q) continue;
      found = 1;
      ++q->vp_ref_cnt;

    }

    if (!found) continue;

    q->vp_owned_sites =
        ck_realloc(q->vp_owned_sites, (q->vp_owned_site_cnt + 1) * sizeof(u16));
    q->vp_owned_sites[q->vp_owned_site_cnt++] = (u16)site;
    q->vp_owned_site_cap = q->vp_owned_site_cnt;

  }

  u8 changed = old_cnt != q->vp_owned_site_cnt;
  if (!changed && old_cnt) {

    changed =
        (u8)(memcmp(old_sites, q->vp_owned_sites, old_cnt * sizeof(u16)) != 0);

  }

  ck_free(old_sites);
  if (changed) { vp_taint_note_owned_sites_changed(q); }

}

static void vp_taint_frontier_set_owners(afl_state_t *afl, struct queue_entry *q,
                                         const vp_taint_owner_ref_t *owners,
                                         u32 n_owners) {

  size_t span = vp_taint_frontier_span(afl->value_profile_slots);

  for (u32 i = 0; i < n_owners; ++i) {

    assert_true(owners[i].site_id < CMP_MAP_W);
    assert_true(owners[i].rel < span);

    size_t idx = (size_t)owners[i].site_id * span + owners[i].rel;
    afl->vp_frontier[idx].owner = q;
    afl->vp_frontier[idx].dist = 5;

  }

  vp_taint_rebuild_owned_sites(afl, q);

}

static void vp_taint_collect_site_stats(const struct queue_entry *q,
                                        vp_taint_analysis_result_t *out) {

  out->site_cnt = 0;
  for (u32 n = 0; q && n < q->vp_taint_cnt; ++n) {

    const vp_taint_site_t *node = &q->vp_taint[n];
    assert_true(out->site_cnt < VP_TAINT_MODEL_MAX_SITES);
    out->site_ids[out->site_cnt] = node->site_id;
    out->site_sensitive_cnts[out->site_cnt] = node->sensitive_cnt;
    out->site_cnt++;

  }

}

static u32 vp_taint_result_site_cnt(const vp_taint_analysis_result_t *res,
                                    u16 site_id, u8 *found) {

  for (u32 i = 0; i < res->site_cnt; ++i) {

    if (res->site_ids[i] == site_id) {

      *found = 1;
      return res->site_sensitive_cnts[i];

    }

  }

  *found = 0;
  return 0;

}

static void vp_taint_mk_state_dirs(const char *out_dir) {

  char p1[PATH_MAX], p2[PATH_MAX], p3[PATH_MAX], p4[PATH_MAX];
  snprintf(p1, sizeof(p1), "%s/queue", out_dir);
  snprintf(p2, sizeof(p2), "%s/queue/.state", out_dir);
  snprintf(p3, sizeof(p3), "%s/queue/.state/vp_taint", out_dir);
  snprintf(p4, sizeof(p4), "%s/queue/.state/deterministic_done", out_dir);
  (void)mkdir(p1, 0700);
  (void)mkdir(p2, 0700);
  (void)mkdir(p3, 0700);
  (void)mkdir(p4, 0700);

}

static void vp_taint_run_analysis(u32 value_profile_slots,
                                  const vp_taint_owner_ref_t *owners,
                                  u32 n_owners, u32 phase1_limit,
                                  u32 phase2_limit,
                                  vp_taint_analysis_result_t *out) {

  afl_state_t        afl;
  struct queue_entry q;
  vp_taint_resume_t *st = NULL;
  u16               *owned_sites = NULL;
  u32                n_owned = 0;
  vp_site_t         *saved_sites = NULL;
  vp_taint_exec_result_t baseline;
  u8                *changed_buf = NULL;
  u8                *changed_alt = NULL;
  u8                *non_neutral = NULL;
  u64                start_ms;
  size_t             frontier_n;

  memset(out, 0, sizeof(*out));
  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = value_profile_slots;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;
  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 1;
  q.fname = (u8 *)"vp-taint-unit";
  q.len = VP_TAINT_TEST_LEN;

  vp_taint_frontier_set_owners(&afl, &q, owners, n_owners);

  collect_owned_sites(&afl, &q, &owned_sites, &n_owned);
  assert_non_null(owned_sites);
  assert_true(n_owned > 0);

  st = ck_alloc(sizeof(vp_taint_resume_t));
  assert_non_null(st);
  st->n_owned = n_owned;
  st->owned_sites = owned_sites;
  owned_sites = NULL;

  saved_sites = ck_alloc(n_owned * sizeof(vp_site_t));
  assert_non_null(saved_sites);
  baseline.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));
  assert_non_null(baseline.sites);

  assert_int_equal(vp_taint_exec(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN,
                                 st->owned_sites, st->n_owned, &baseline,
                                 saved_sites),
                   0);

  changed_buf = ck_alloc(VP_TAINT_TEST_LEN);
  changed_alt = ck_alloc(VP_TAINT_TEST_LEN);
  memcpy(changed_buf, vp_taint_test_input, VP_TAINT_TEST_LEN);
  memcpy(changed_alt, vp_taint_test_input, VP_TAINT_TEST_LEN);
  random_replace_vp(&afl, changed_buf, VP_TAINT_TEST_LEN);
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; i++) {

    changed_alt[i] ^= 0xFF;
    if (changed_alt[i] == vp_taint_test_input[i]) changed_alt[i] ^= 0xA5;

  }

  if (!phase1_limit && !phase2_limit) {

    vp_taint_fake_time_ms = AFL_VP_TAINT_TIMEOUT_MS + 1U;
    start_ms = 0;

  } else {

    start_ms = get_cur_time();

  }

  st->baseline_sites = baseline.sites;

  non_neutral = vp_taint_phase1(&afl, vp_taint_test_input, changed_buf,
                                changed_alt, VP_TAINT_TEST_LEN, st->owned_sites,
                                baseline.sites, st->n_owned, saved_sites,
                                &out->exec_cnt, start_ms);
  assert_non_null(non_neutral);
  memcpy(out->non_neutral, non_neutral, VP_TAINT_TEST_LEN);

  st->non_neutral = non_neutral;
  st->sensitive_cnts = ck_alloc(st->n_owned * sizeof(u32));
  st->sensitive_caps = ck_alloc(st->n_owned * sizeof(u32));
  st->sensitive_bufs = ck_alloc(st->n_owned * sizeof(u32 *));
  vp_taint_build_phase2_order(&afl, st, VP_TAINT_TEST_LEN);

  vp_taint_phase2(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN, st->non_neutral,
                  st->owned_sites, st->baseline_sites, st->n_owned, saved_sites,
                  st->sensitive_cnts, st->sensitive_caps, st->sensitive_bufs,
                  st->phase2_order, st->phase2_cnt, &st->phase2_next_idx,
                  &out->exec_cnt, start_ms);

  q.vp_taint_resume = st;
  vp_taint_build_list_from_resume(&q);
  vp_taint_resume_free(&q);
  st = NULL;

  vp_taint_bitmap_from_list(&q, out->vp_sensitive, VP_TAINT_TEST_LEN);
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i) {

    out->path_sensitive[i] = (u8)(out->non_neutral[i] && !out->vp_sensitive[i]);
    out->neutral[i] = (u8)!out->non_neutral[i];

  }

  vp_taint_collect_site_stats(&q, out);

  if (q.vp_taint) vp_taint_free(&q);
  ck_free(changed_alt);
  ck_free(changed_buf);
  ck_free(saved_sites);
  if (st) {

    q.vp_taint_resume = st;
    vp_taint_resume_free(&q);

  }
  ck_free(owned_sites);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

}

static void test_vp_taint_classifies_vp_path_and_neutral_bytes(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, VP_TAINT_PATH_BEG, VP_TAINT_PATH_BLOCK_LEN,
                                VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, VP_TAINT_VP_BEG,
                                 VP_TAINT_VP_BLOCK_LEN, VP_TAINT_VP_BYTE);
  vp_taint_model_set_neutral_range(VP_TAINT_NEUTRAL_BEG,
                                   VP_TAINT_NEUTRAL_BLOCK_LEN);

  vp_taint_run_analysis(1, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  for (u32 i = VP_TAINT_PATH_BEG;
       i < VP_TAINT_PATH_BEG + VP_TAINT_PATH_BLOCK_LEN;
       ++i) {

    assert_int_equal(res.vp_sensitive[i], 0);
    assert_int_equal(res.path_sensitive[i], 1);
    assert_int_equal(res.neutral[i], 0);

  }

  for (u32 i = VP_TAINT_VP_BEG; i < VP_TAINT_VP_BEG + VP_TAINT_VP_BLOCK_LEN;
       ++i) {

    assert_int_equal(res.vp_sensitive[i], 1);
    assert_int_equal(res.path_sensitive[i], 0);
    assert_int_equal(res.neutral[i], 0);

  }

  for (u32 i = VP_TAINT_NEUTRAL_BEG;
       i < VP_TAINT_NEUTRAL_BEG + VP_TAINT_NEUTRAL_BLOCK_LEN; ++i) {

    assert_int_equal(res.vp_sensitive[i], 0);
    assert_int_equal(res.path_sensitive[i], 0);
    assert_int_equal(res.neutral[i], 1);

  }

}

static void test_vp_taint_classifies_interleaved_regions(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};

  /* Interleaved 8-byte chunks: path, neutral, vp, path. */
  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_neutral_range(8, 8);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 16, 8, VP_TAINT_VP_BYTE);
  vp_taint_model_set_path_range(0, 0, 24, 8, VP_TAINT_PATH_BYTE);

  vp_taint_run_analysis(1, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  for (u32 i = 0; i < 8; ++i) {

    assert_int_equal(res.vp_sensitive[i], 0);
    assert_int_equal(res.path_sensitive[i], 1);
    assert_int_equal(res.neutral[i], 0);

  }

  for (u32 i = 8; i < 16; ++i) {

    assert_int_equal(res.vp_sensitive[i], 0);
    assert_int_equal(res.path_sensitive[i], 0);
    assert_int_equal(res.neutral[i], 1);

  }

  for (u32 i = 16; i < 24; ++i) {

    assert_int_equal(res.vp_sensitive[i], 1);
    assert_int_equal(res.path_sensitive[i], 0);
    assert_int_equal(res.neutral[i], 0);

  }

  for (u32 i = 24; i < 32; ++i) {

    assert_int_equal(res.vp_sensitive[i], 0);
    assert_int_equal(res.path_sensitive[i], 1);
    assert_int_equal(res.neutral[i], 0);

  }

}

static void test_vp_taint_multi_site_ownership(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {
      {.site_id = 0, .rel = 0}, {.site_id = 1, .rel = 0}};
  u8  found0, found1;
  u32 cnt0, cnt1;

  vp_taint_model_reset();

  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1010, 8, 4, VP_TAINT_VP_BYTE);

  vp_taint_model_set_path_range(1, 1, 16, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(1, 1, 0, 0x2020, 24, 4, VP_TAINT_VP_BYTE_2);

  vp_taint_run_analysis(1, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  for (u32 i = 8; i < 12; ++i)
    assert_int_equal(res.vp_sensitive[i], 1);
  for (u32 i = 24; i < 28; ++i)
    assert_int_equal(res.vp_sensitive[i], 1);

  for (u32 i = 12; i < 16; ++i)
    assert_int_equal(res.vp_sensitive[i], 0);
  for (u32 i = 28; i < 32; ++i)
    assert_int_equal(res.vp_sensitive[i], 0);

  cnt0 = vp_taint_result_site_cnt(&res, 0, &found0);
  cnt1 = vp_taint_result_site_cnt(&res, 1, &found1);
  assert_true(found0);
  assert_true(found1);
  assert_int_equal(res.site_cnt, 2);
  assert_int_equal(cnt0, 4);
  assert_int_equal(cnt1, 4);

}

static void test_vp_taint_asymmetric_perturbation_finds_vp_byte(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};
  u8  found;
  u32 cnt;

  /* Byte 8 only reacts when moved below target; +1 has no effect. */
  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_lt(0, 0, 0, 0x3333, 8, 1, 0x80);

  vp_taint_run_analysis(1, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  assert_int_equal(res.vp_sensitive[8], 1);
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i) {

    if (i == 8) continue;
    assert_int_equal(res.vp_sensitive[i], 0);

  }

  cnt = vp_taint_result_site_cnt(&res, 0, &found);
  assert_true(found);
  assert_int_equal(cnt, 1);

}

static void test_vp_taint_phase1_budget_zero_is_conservative(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 8, VP_TAINT_VP_BYTE);

  vp_taint_run_analysis(1, owners, ARRAY_SIZE(owners), 0, 0, &res);

  assert_int_equal(res.exec_cnt, 0);
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i) {

    assert_int_equal(res.non_neutral[i], 1);
    assert_int_equal(res.neutral[i], 0);
    assert_int_equal(res.vp_sensitive[i], 0);

  }

}

static void test_vp_taint_phase1_inconclusive_exec_is_conservative(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};
  u16               *owned_sites = NULL;
  u32                n_owned = 0;
  vp_site_t         *saved_sites = NULL;
  vp_taint_exec_result_t baseline;
  u8                *changed_buf = NULL;
  u8                *changed_alt = NULL;
  u8                *non_neutral = NULL;
  u32                exec_cnt = 0;
  u64                start_ms;
  size_t             frontier_n;

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 8, VP_TAINT_VP_BYTE);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 1;
  q.fname = (u8 *)"vp-taint-unit";
  q.len = VP_TAINT_TEST_LEN;
  vp_taint_frontier_set_owners(&afl, &q, owners, ARRAY_SIZE(owners));

  collect_owned_sites(&afl, &q, &owned_sites, &n_owned);
  assert_non_null(owned_sites);
  assert_int_equal(n_owned, 1);

  saved_sites = ck_alloc(n_owned * sizeof(vp_site_t));
  assert_non_null(saved_sites);
  baseline.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));
  assert_non_null(baseline.sites);

  assert_int_equal(vp_taint_exec(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN,
                                 owned_sites, n_owned, &baseline, saved_sites),
                   0);

  changed_buf = ck_alloc(VP_TAINT_TEST_LEN);
  changed_alt = ck_alloc(VP_TAINT_TEST_LEN);
  memcpy(changed_buf, vp_taint_test_input, VP_TAINT_TEST_LEN);
  memcpy(changed_alt, vp_taint_test_input, VP_TAINT_TEST_LEN);
  random_replace_vp(&afl, changed_buf, VP_TAINT_TEST_LEN);
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i) {

    changed_alt[i] ^= 0xFF;
    if (changed_alt[i] == vp_taint_test_input[i]) changed_alt[i] ^= 0xA5;

  }

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;
  start_ms = get_cur_time();

  vp_taint_force_run_error = 1;
  non_neutral = vp_taint_phase1(
      &afl, vp_taint_test_input, changed_buf, changed_alt, VP_TAINT_TEST_LEN,
      owned_sites, baseline.sites, n_owned, saved_sites, &exec_cnt, start_ms);

  assert_non_null(non_neutral);
  assert_int_equal(exec_cnt, 0);
  for (u32 i = 0; i < VP_TAINT_TEST_LEN; ++i)
    assert_int_equal(non_neutral[i], 1);

  ck_free(non_neutral);
  ck_free(changed_alt);
  ck_free(changed_buf);
  ck_free(baseline.sites);
  ck_free(saved_sites);
  ck_free(owned_sites);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

}

static void test_vp_taint_phase2_inconclusive_exec_advances_progress(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};
  u16               *owned_sites = NULL;
  u32                n_owned = 0;
  vp_site_t         *saved_sites = NULL;
  vp_taint_exec_result_t baseline;
  u8                *non_neutral = NULL;
  u32               *sensitive_cnts = NULL;
  u32               *sensitive_caps = NULL;
  u32              **sensitive_bufs = NULL;
  u32               *phase2_order = NULL;
  u32                phase2_cnt = 0;
  u32                phase2_next_idx = 0;
  u32                exec_cnt = 0;
  u64                start_ms;
  size_t             frontier_n;

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 8, VP_TAINT_VP_BYTE);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 1;
  q.fname = (u8 *)"vp-taint-unit";
  q.len = VP_TAINT_TEST_LEN;
  vp_taint_frontier_set_owners(&afl, &q, owners, ARRAY_SIZE(owners));

  collect_owned_sites(&afl, &q, &owned_sites, &n_owned);
  assert_non_null(owned_sites);
  assert_int_equal(n_owned, 1);

  saved_sites = ck_alloc(n_owned * sizeof(vp_site_t));
  assert_non_null(saved_sites);
  baseline.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));
  assert_non_null(baseline.sites);

  assert_int_equal(vp_taint_exec(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN,
                                 owned_sites, n_owned, &baseline, saved_sites),
                   0);

  non_neutral = ck_alloc(VP_TAINT_TEST_LEN);
  memset(non_neutral, 0, VP_TAINT_TEST_LEN);
  non_neutral[VP_TAINT_VP_BEG] = 1;

  phase2_cnt = 1;
  phase2_order = ck_alloc(sizeof(u32));
  phase2_order[0] = VP_TAINT_VP_BEG;

  sensitive_cnts = ck_alloc(n_owned * sizeof(u32));
  sensitive_caps = ck_alloc(n_owned * sizeof(u32));
  sensitive_bufs = ck_alloc(n_owned * sizeof(u32 *));

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;
  start_ms = get_cur_time();

  vp_taint_force_run_error = 1;
  vp_taint_phase2(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN, non_neutral,
                  owned_sites, baseline.sites, n_owned, saved_sites,
                  sensitive_cnts, sensitive_caps, sensitive_bufs, phase2_order,
                  phase2_cnt, &phase2_next_idx, &exec_cnt, start_ms);

  assert_int_equal(phase2_next_idx, 1);
  assert_int_equal(sensitive_cnts[0], 1);
  assert_non_null(sensitive_bufs[0]);
  assert_int_equal(sensitive_bufs[0][0], VP_TAINT_VP_BEG);

  vp_taint_force_run_error = 1;
  start_ms = get_cur_time();
  vp_taint_phase2(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN, non_neutral,
                  owned_sites, baseline.sites, n_owned, saved_sites,
                  sensitive_cnts, sensitive_caps, sensitive_bufs, phase2_order,
                  phase2_cnt, &phase2_next_idx, &exec_cnt, start_ms);

  assert_int_equal(phase2_next_idx, 1);
  assert_int_equal(sensitive_cnts[0], 1);

  ck_free(sensitive_bufs[0]);
  ck_free(sensitive_bufs);
  ck_free(sensitive_caps);
  ck_free(sensitive_cnts);
  ck_free(phase2_order);
  ck_free(non_neutral);
  ck_free(baseline.sites);
  ck_free(saved_sites);
  ck_free(owned_sites);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

}

static void test_vp_taint_exec_restores_state_on_error_and_stopsoon(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  u16               *owned_sites = NULL;
  u32                n_owned = 0;
  vp_site_t         *saved_sites = NULL;
  vp_taint_exec_result_t result;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};
  size_t             frontier_n;

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 8, VP_TAINT_VP_BYTE);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 1;
  q.fname = (u8 *)"vp-taint-unit";
  q.len = VP_TAINT_TEST_LEN;

  vp_taint_frontier_set_owners(&afl, &q, owners, ARRAY_SIZE(owners));

  collect_owned_sites(&afl, &q, &owned_sites, &n_owned);
  assert_non_null(owned_sites);
  assert_int_equal(n_owned, 1);

  saved_sites = ck_alloc(n_owned * sizeof(vp_site_t));
  assert_non_null(saved_sites);
  result.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));
  assert_non_null(result.sites);

  afl.shm.vp_map->site[0].valid_mask = 0x55AA;
  afl.shm.vp_map->site[0].slots[0].slot_key = 0xBEEF;
  afl.shm.vp_map->site[0].slots[0].best_dist = 0x7777;

  vp_taint_force_run_error = 1;
  assert_int_equal(vp_taint_exec(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN,
                                 owned_sites, n_owned, &result, saved_sites),
                   1);
  assert_int_equal(afl.shm.vp_map->site[0].valid_mask, 0x55AA);
  assert_int_equal(afl.shm.vp_map->site[0].slots[0].slot_key, 0xBEEF);
  assert_int_equal(afl.shm.vp_map->site[0].slots[0].best_dist, 0x7777);

  afl.stop_soon = 0;
  afl.shm.vp_map->site[0].valid_mask = 0x1234;
  afl.shm.vp_map->site[0].slots[0].slot_key = 0x4321;
  afl.shm.vp_map->site[0].slots[0].best_dist = 0x2468;

  vp_taint_force_stop_soon = 1;
  assert_int_equal(vp_taint_exec(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN,
                                 owned_sites, n_owned, &result, saved_sites),
                   1);
  assert_int_equal(afl.stop_soon, 1);
  assert_int_equal(afl.shm.vp_map->site[0].valid_mask, 0x1234);
  assert_int_equal(afl.shm.vp_map->site[0].slots[0].slot_key, 0x4321);
  assert_int_equal(afl.shm.vp_map->site[0].slots[0].best_dist, 0x2468);

  ck_free(result.sites);
  ck_free(saved_sites);
  ck_free(owned_sites);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

}

static void test_vp_taint_exec_filters_non_owned_sites(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  u16               *owned_sites = NULL;
  u32                n_owned = 0;
  vp_site_t         *saved_sites = NULL;
  vp_taint_exec_result_t result;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};
  size_t             frontier_n;

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 4, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 4, VP_TAINT_VP_BYTE);
  vp_taint_model_set_path_range(1, 1, 16, 4, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(1, 1, 0, 0x2222, 24, 4, VP_TAINT_VP_BYTE_2);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 9;
  q.fname = (u8 *)"vp-taint-filter-unit";
  q.len = VP_TAINT_TEST_LEN;

  vp_taint_frontier_set_owners(&afl, &q, owners, ARRAY_SIZE(owners));

  collect_owned_sites(&afl, &q, &owned_sites, &n_owned);
  assert_non_null(owned_sites);
  assert_int_equal(n_owned, 1);

  saved_sites = ck_alloc(n_owned * sizeof(vp_site_t));
  assert_non_null(saved_sites);
  result.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));
  assert_non_null(result.sites);

  afl.shm.vp_map->site[1].valid_mask = 0x1234;
  afl.shm.vp_map->site[1].slots[0].slot_key = 0xABCD;
  afl.shm.vp_map->site[1].slots[0].best_dist = 0x5678;

  assert_int_equal(vp_taint_exec(&afl, vp_taint_test_input, VP_TAINT_TEST_LEN,
                                 owned_sites, n_owned, &result, saved_sites),
                   0);
  assert_int_equal(afl.shm.vp_map->filter_enabled, 0);
  assert_int_equal(afl.shm.vp_map->site[1].valid_mask, 0x1234);
  assert_int_equal(afl.shm.vp_map->site[1].slots[0].slot_key, 0xABCD);
  assert_int_equal(afl.shm.vp_map->site[1].slots[0].best_dist, 0x5678);

  ck_free(result.sites);
  ck_free(saved_sites);
  ck_free(owned_sites);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

}

static void test_vp_taint_multi_slot_state_changes(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {
      {.site_id = 0, .rel = 0},
      {.site_id = 0, .rel = VP_RUNTIME_SLOT_REPLICA_LIMIT}};
  u8  found;
  u32 cnt;

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1111, 8, 4, VP_TAINT_VP_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 1, 0x2222, 12, 4, VP_TAINT_VP_BYTE_2);

  vp_taint_run_analysis(2, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  for (u32 i = 8; i < 16; ++i)
    assert_int_equal(res.vp_sensitive[i], 1);

  cnt = vp_taint_result_site_cnt(&res, 0, &found);
  assert_true(found);
  assert_int_equal(res.site_cnt, 1);
  assert_int_equal(cnt, 8);

}

/* Multi-slot classification must include bytes that only perturb one slot. */
static void test_vp_taint_metric1_only_changes_are_sensitive(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {
      {.site_id = 0, .rel = 0},
      {.site_id = 0, .rel = VP_RUNTIME_SLOT_REPLICA_LIMIT}};
  u8  found;
  u32 cnt;

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x400, 8, 1, VP_TAINT_VP_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 1, 0x401, 9, 1, VP_TAINT_VP_BYTE_2);

  vp_taint_run_analysis(2, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  assert_int_equal(res.vp_sensitive[8], 1);
  assert_int_equal(res.vp_sensitive[9], 1);

  cnt = vp_taint_result_site_cnt(&res, 0, &found);
  assert_true(found);
  assert_int_equal(cnt, 2);

}

static void test_vp_taint_sub8_interleaving_relaxed_invariants(void **state) {

  (void)state;
  vp_taint_analysis_result_t res;
  const vp_taint_owner_ref_t owners[] = {{.site_id = 0, .rel = 0}};

  vp_taint_model_reset();

  /* Per-byte interleave: path, vp, neutral repeated. */
  for (u32 i = 0; i < 24; i += 3) {

    vp_taint_model_set_path_range(0, 0, i, 1, VP_TAINT_PATH_BYTE);
    vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, i + 1, 1, VP_TAINT_VP_BYTE);
    vp_taint_model_set_neutral_range(i + 2, 1);

  }

  vp_taint_run_analysis(1, owners, ARRAY_SIZE(owners), 2048, 4096, &res);

  for (u32 i = 0; i < 24; i += 3) {

    assert_int_equal(res.vp_sensitive[i], 0);
    assert_int_equal(res.vp_sensitive[i + 1], 1);
    assert_int_equal(res.vp_sensitive[i + 2], 0);

  }

  for (u32 i = 24; i < VP_TAINT_TEST_LEN; ++i) {

    assert_int_equal(res.vp_sensitive[i], 0);

  }

}

static void test_vp_taint_state_save_and_load(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q_save, q_load;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-state-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  char               state_file[PATH_MAX];
  u8                *fname = NULL;

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  memset(&afl, 0, sizeof(afl));
  memset(&q_save, 0, sizeof(q_save));
  memset(&q_load, 0, sizeof(q_load));

  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  fname = alloc_printf("%s/queue/id:000001", tmp_dir);
  q_save.fname = fname;
  q_save.len = VP_TAINT_TEST_LEN;
  q_save.vp_taint_done = 1;
  q_save.vp_taint_analyzed_cnt = 1;
  q_save.vp_taint_analyzed_sites = ck_alloc(sizeof(u16));
  q_save.vp_taint_analyzed_sites[0] = 7;

  q_save.vp_taint = ck_alloc(sizeof(vp_taint_site_t));
  q_save.vp_taint_cnt = 1;
  q_save.vp_taint[0].site_id = 7;
  q_save.vp_taint[0].sensitive_cnt = 2;
  q_save.vp_taint[0].sensitive_positions = ck_alloc(2 * sizeof(u32));
  q_save.vp_taint[0].sensitive_positions[0] = 3;
  q_save.vp_taint[0].sensitive_positions[1] = 11;

  vp_taint_save_state(&afl, &q_save);

  q_load.fname = fname;
  q_load.len = VP_TAINT_TEST_LEN;
  vp_taint_load_state(&afl, &q_load);

  assert_non_null(q_load.vp_taint);
  assert_int_equal(q_load.vp_taint_done, 1);
  assert_int_equal(q_load.vp_taint_cnt, 1);
  assert_int_equal(q_load.vp_taint_analyzed_cnt, 1);
  assert_non_null(q_load.vp_taint_analyzed_sites);
  assert_int_equal(q_load.vp_taint_analyzed_sites[0], 7);
  assert_int_equal(q_load.vp_taint[0].site_id, 7);
  assert_int_equal(q_load.vp_taint[0].sensitive_cnt, 2);
  assert_int_equal(q_load.vp_taint[0].sensitive_positions[0], 3);
  assert_int_equal(q_load.vp_taint[0].sensitive_positions[1], 11);

  if (q_load.vp_taint) vp_taint_free(&q_load);
  if (q_save.vp_taint) vp_taint_free(&q_save);
  ck_free(fname);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000001",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_state_load_rejects_truncated_file(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-corrupt-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  char               state_file[PATH_MAX];
  u8                *fname = NULL;

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  fname = alloc_printf("%s/queue/id:000003", tmp_dir);
  q.fname = fname;
  q.len = VP_TAINT_TEST_LEN;

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000003",
           tmp_dir);

  {

    FILE *fp = fopen(state_file, "wb");
    assert_non_null(fp);

    vp_taint_file_header_t hdr = {.magic = VP_TAINT_FILE_MAGIC,
                                  .version = VP_TAINT_FILE_VERSION,
                                  .len = VP_TAINT_TEST_LEN,
                                  .analyzed_site_cnt = 1,
                                  .sensitive_site_cnt = 1,
                                  .slot_count = 1};
    vp_taint_file_site_t site = {.site_id = 0, .reserved = 0, .sensitive_cnt = 2};
    u16                  analyzed_site = 0;
    u32                  only_one_pos = 7;

    assert_int_equal(fwrite(&hdr, sizeof(hdr), 1, fp), 1);
    assert_int_equal(fwrite(&analyzed_site, sizeof(analyzed_site), 1, fp), 1);
    assert_int_equal(fwrite(&site, sizeof(site), 1, fp), 1);
    assert_int_equal(fwrite(&only_one_pos, sizeof(only_one_pos), 1, fp), 1);
    fclose(fp);

  }

  vp_taint_load_state(&afl, &q);
  assert_null(q.vp_taint);
  assert_int_equal(q.vp_taint_done, 0);
  assert_int_equal(access(state_file, F_OK), -1);

  ck_free(fname);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_state_load_rejects_unsorted_sites(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-unsorted-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  char               state_file[PATH_MAX];
  u8                *fname = NULL;

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  fname = alloc_printf("%s/queue/id:000010", tmp_dir);
  q.fname = fname;
  q.len = VP_TAINT_TEST_LEN;

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000010",
           tmp_dir);

  {

    FILE *fp = fopen(state_file, "wb");
    assert_non_null(fp);

    vp_taint_file_header_t hdr = {.magic = VP_TAINT_FILE_MAGIC,
                                  .version = VP_TAINT_FILE_VERSION,
                                  .len = VP_TAINT_TEST_LEN,
                                  .analyzed_site_cnt = 2,
                                  .sensitive_site_cnt = 1,
                                  .slot_count = 1};
    vp_taint_file_site_t site = {.site_id = 5, .reserved = 0, .sensitive_cnt = 1};
    u16                  analyzed_sites[2] = {7, 5};
    u32                  pos = 7;

    assert_int_equal(fwrite(&hdr, sizeof(hdr), 1, fp), 1);
    assert_int_equal(fwrite(analyzed_sites, sizeof(analyzed_sites), 1, fp), 1);
    assert_int_equal(fwrite(&site, sizeof(site), 1, fp), 1);
    assert_int_equal(fwrite(&pos, sizeof(pos), 1, fp), 1);
    fclose(fp);

  }

  vp_taint_load_state(&afl, &q);
  assert_null(q.vp_taint);
  assert_int_equal(q.vp_taint_done, 0);
  assert_int_equal(access(state_file, F_OK), -1);

  ck_free(fname);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_state_save_and_load_empty_result(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q_save, q_load;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-empty-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  char               state_file[PATH_MAX];
  u8                *fname = NULL;

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  memset(&afl, 0, sizeof(afl));
  memset(&q_save, 0, sizeof(q_save));
  memset(&q_load, 0, sizeof(q_load));

  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  fname = alloc_printf("%s/queue/id:000005", tmp_dir);
  q_save.fname = fname;
  q_save.len = VP_TAINT_TEST_LEN;
  q_save.vp_taint_done = 1;
  q_save.vp_taint_analyzed_cnt = 1;
  q_save.vp_taint_analyzed_sites = ck_alloc(sizeof(u16));
  q_save.vp_taint_analyzed_sites[0] = 5;

  vp_taint_save_state(&afl, &q_save);

  q_load.fname = fname;
  q_load.len = VP_TAINT_TEST_LEN;
  vp_taint_load_state(&afl, &q_load);

  assert_null(q_load.vp_taint);
  assert_int_equal(q_load.vp_taint_done, 1);
  assert_int_equal(q_load.vp_taint_analyzed_cnt, 1);
  assert_non_null(q_load.vp_taint_analyzed_sites);
  assert_int_equal(q_load.vp_taint_analyzed_sites[0], 5);

  vp_taint_free(&q_load);
  vp_taint_free(&q_save);

  ck_free(fname);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000005",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_keeps_initial_result_when_owned_sites_change(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  u8                 vp_sensitive[VP_TAINT_TEST_LEN];
  size_t             frontier_n;
  size_t             span;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-drift-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  u8                *fname = NULL;
  char               state_file[PATH_MAX];

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 4, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1111, 8, 4, VP_TAINT_VP_BYTE);
  vp_taint_model_set_path_range(1, 1, 16, 4, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(1, 1, 0, 0x2222, 24, 4, VP_TAINT_VP_BYTE_2);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;
  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  fname = alloc_printf("%s/queue/id:000004", tmp_dir);
  q.fname = fname;
  q.id = 4;
  q.len = VP_TAINT_TEST_LEN;

  span = vp_taint_frontier_span(afl.value_profile_slots);
  afl.vp_frontier[0 * span + 0].owner = &q;
  afl.vp_frontier[0 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;
  vp_taint_analyze(&afl, &q);
  assert_int_equal(q.vp_taint_done, 1);
  assert_non_null(q.vp_taint);
  assert_int_equal(vp_taint_covers_owned_sites(&q), 1);
  assert_int_equal(q.vp_taint_generation, q.vp_owned_sites_generation);

  vp_taint_bitmap_from_list(&q, vp_sensitive, VP_TAINT_TEST_LEN);
  for (u32 i = 8; i < 12; ++i)
    assert_int_equal(vp_sensitive[i], 1);
  for (u32 i = 24; i < 28; ++i)
    assert_int_equal(vp_sensitive[i], 0);

  afl.vp_frontier[0 * span + 0].owner = NULL;
  afl.vp_frontier[0 * span + 0].dist = VP_DIST_UNSOLVED;
  afl.vp_frontier[1 * span + 0].owner = &q;
  afl.vp_frontier[1 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);
  assert_int_equal(vp_taint_covers_owned_sites(&q), 0);
  assert_true(q.vp_taint_generation != q.vp_owned_sites_generation);

  vp_taint_analyze(&afl, &q);
  assert_int_equal(q.vp_taint_done, 1);
  assert_non_null(q.vp_taint);
  assert_null(q.vp_taint_resume);

  vp_taint_bitmap_from_list(&q, vp_sensitive, VP_TAINT_TEST_LEN);
  for (u32 i = 8; i < 12; ++i)
    assert_int_equal(vp_sensitive[i], 1);
  for (u32 i = 24; i < 28; ++i)
    assert_int_equal(vp_sensitive[i], 0);

  if (q.vp_taint) vp_taint_free(&q);
  vp_taint_resume_free(&q);
  ck_free(fname);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000004",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_unanalyzed_empty_result_does_not_cover_owned(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  size_t             frontier_n;
  size_t             span;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 123;
  q.vp_taint_done = 1;
  q.vp_taint = NULL;

  span = vp_taint_frontier_span(afl.value_profile_slots);
  afl.vp_frontier[0 * span + 0].owner = &q;
  afl.vp_frontier[0 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  assert_int_equal(vp_taint_covers_owned_sites(&q), 0);
  assert_true(q.vp_taint_generation != q.vp_owned_sites_generation);

  ck_free(afl.vp_frontier);

}

static void test_vp_taint_analyzed_empty_result_is_current_when_owned_covered(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  size_t             frontier_n;
  size_t             span;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  q.id = 124;
  q.vp_taint_done = 1;
  q.vp_taint = NULL;
  q.vp_taint_analyzed_cnt = 1;
  q.vp_taint_analyzed_sites = ck_alloc(sizeof(u16));
  q.vp_taint_analyzed_sites[0] = 0;

  span = vp_taint_frontier_span(afl.value_profile_slots);
  afl.vp_frontier[0 * span + 0].owner = &q;
  afl.vp_frontier[0 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  assert_int_equal(vp_taint_covers_owned_sites(&q), 1);
  assert_int_equal(q.vp_taint_generation, q.vp_owned_sites_generation);

  vp_taint_free(&q);
  ck_free(afl.vp_frontier);

}

static void test_vp_taint_owned_generation_tracks_unique_site_set(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  size_t             frontier_n;
  size_t             span;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 2;

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  span = vp_taint_frontier_span(afl.value_profile_slots);
  afl.vp_frontier[0 * span + 0].owner = &q;
  afl.vp_frontier[0 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);
  assert_int_equal(q.vp_owned_sites_generation, 1);

  afl.vp_frontier[0 * span + 0].owner = NULL;
  afl.vp_frontier[0 * span + 0].dist = VP_DIST_UNSOLVED;
  afl.vp_frontier[0 * span + 1].owner = &q;
  afl.vp_frontier[0 * span + 1].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);
  assert_int_equal(q.vp_owned_sites_generation, 1);

  afl.vp_frontier[1 * span + 0].owner = &q;
  afl.vp_frontier[1 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);
  assert_int_equal(q.vp_owned_sites_generation, 2);

  afl.vp_frontier[1 * span + 0].owner = NULL;
  afl.vp_frontier[1 * span + 0].dist = VP_DIST_UNSOLVED;
  vp_taint_rebuild_owned_sites(&afl, &q);
  assert_int_equal(q.vp_owned_sites_generation, 3);

  ck_free(q.vp_owned_sites);
  ck_free(afl.vp_frontier);

}

static void test_vp_taint_state_load_marks_current_when_owned_sites_covered(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q_save, q_load;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-load-current-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  char               state_file[PATH_MAX];
  u8                *fname = NULL;

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  memset(&afl, 0, sizeof(afl));
  memset(&q_save, 0, sizeof(q_save));
  memset(&q_load, 0, sizeof(q_load));

  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  fname = alloc_printf("%s/queue/id:000008", tmp_dir);
  q_save.fname = fname;
  q_save.len = VP_TAINT_TEST_LEN;
  q_save.vp_taint_done = 1;
  q_save.vp_taint_analyzed_cnt = 1;
  q_save.vp_taint_analyzed_sites = ck_alloc(sizeof(u16));
  q_save.vp_taint_analyzed_sites[0] = 5;

  vp_taint_save_state(&afl, &q_save);

  q_load.fname = fname;
  q_load.len = VP_TAINT_TEST_LEN;
  q_load.vp_owned_sites = ck_alloc(sizeof(u16));
  q_load.vp_owned_sites[0] = 5;
  q_load.vp_owned_site_cnt = 1;
  q_load.vp_owned_site_cap = 1;
  q_load.vp_owned_sites_generation = 7;
  vp_taint_load_state(&afl, &q_load);

  assert_int_equal(q_load.vp_taint_done, 1);
  assert_int_equal(q_load.vp_taint_generation, 7);
  assert_int_equal(q_load.vp_taint_stale_visits, 0);
  assert_int_equal(vp_taint_covers_owned_sites(&q_load), 1);

  vp_taint_free(&q_load);
  vp_taint_free(&q_save);
  ck_free(q_load.vp_owned_sites);
  ck_free(fname);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000008",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_state_load_marks_stale_when_owned_site_missing(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q_save, q_load;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-load-stale-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  char               state_file[PATH_MAX];
  u8                *fname = NULL;

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  memset(&afl, 0, sizeof(afl));
  memset(&q_save, 0, sizeof(q_save));
  memset(&q_load, 0, sizeof(q_load));

  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;

  fname = alloc_printf("%s/queue/id:000009", tmp_dir);
  q_save.fname = fname;
  q_save.len = VP_TAINT_TEST_LEN;
  q_save.vp_taint_done = 1;
  q_save.vp_taint_analyzed_cnt = 1;
  q_save.vp_taint_analyzed_sites = ck_alloc(sizeof(u16));
  q_save.vp_taint_analyzed_sites[0] = 5;

  vp_taint_save_state(&afl, &q_save);

  q_load.fname = fname;
  q_load.len = VP_TAINT_TEST_LEN;
  q_load.vp_owned_sites = ck_alloc(sizeof(u16));
  q_load.vp_owned_sites[0] = 6;
  q_load.vp_owned_site_cnt = 1;
  q_load.vp_owned_site_cap = 1;
  q_load.vp_owned_sites_generation = 7;
  vp_taint_load_state(&afl, &q_load);

  assert_int_equal(q_load.vp_taint_done, 1);
  assert_int_equal(q_load.vp_taint_generation, 0);
  assert_int_equal(vp_taint_covers_owned_sites(&q_load), 0);

  vp_taint_free(&q_load);
  vp_taint_free(&q_save);
  ck_free(q_load.vp_owned_sites);
  ck_free(fname);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000009",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_second_call_is_noop_after_completion(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  size_t             frontier_n;
  size_t             span;
  char               tmp_tpl[] = "/tmp/afl-vp-taint-stable-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  u8                *fname = NULL;
  char               state_file[PATH_MAX];

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 8, VP_TAINT_VP_BYTE);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;
  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  fname = alloc_printf("%s/queue/id:000006", tmp_dir);
  q.fname = fname;
  q.id = 6;
  q.len = VP_TAINT_TEST_LEN;

  span = vp_taint_frontier_span(afl.value_profile_slots);
  afl.vp_frontier[0 * span + 0].owner = &q;
  afl.vp_frontier[0 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;
  vp_taint_analyze(&afl, &q);

  assert_int_equal(q.vp_taint_done, 1);
  assert_non_null(q.vp_taint);
  assert_null(q.vp_taint_resume);
  vp_taint_site_t *first_list = q.vp_taint;

  /* Completed analysis should be reused as-is on subsequent calls. */
  vp_taint_analyze(&afl, &q);

  assert_int_equal(q.vp_taint_done, 1);
  assert_ptr_equal(q.vp_taint, first_list);
  assert_null(q.vp_taint_resume);

  if (q.vp_taint) vp_taint_free(&q);
  vp_taint_resume_free(&q);
  ck_free(fname);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000006",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_analyze_resumes_after_timeout(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  u8                 vp_sensitive[VP_TAINT_TEST_LEN];
  char               tmp_tpl[] = "/tmp/afl-vp-taint-resume-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  u8                *fname = NULL;
  size_t             frontier_n;
  char               state_file[PATH_MAX];

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 8, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1234, 8, 8, VP_TAINT_VP_BYTE);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;
  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  fname = alloc_printf("%s/queue/id:000002", tmp_dir);
  q.fname = fname;
  q.id = 2;
  q.len = VP_TAINT_TEST_LEN;
  afl.vp_frontier[0].owner = &q;
  afl.vp_frontier[0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = AFL_VP_TAINT_TIMEOUT_MS;
  vp_taint_analyze(&afl, &q);
  assert_null(q.vp_taint);
  assert_non_null(q.vp_taint_resume);

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;
  vp_taint_analyze(&afl, &q);
  assert_non_null(q.vp_taint);
  assert_null(q.vp_taint_resume);

  vp_taint_bitmap_from_list(&q, vp_sensitive, VP_TAINT_TEST_LEN);
  for (u32 i = 8; i < 16; ++i) {

    assert_int_equal(vp_sensitive[i], 1);

  }

  if (q.vp_taint) vp_taint_free(&q);
  vp_taint_resume_free(&q);
  ck_free(fname);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000002",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

static void test_vp_taint_resume_restarts_after_owned_sites_generation_change(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  u8                 vp_sensitive[VP_TAINT_TEST_LEN];
  char               tmp_tpl[] = "/tmp/afl-vp-taint-gen-XXXXXX";
  char              *tmp_dir = mkdtemp(tmp_tpl);
  u8                *fname = NULL;
  size_t             frontier_n;
  size_t             span;
  char               state_file[PATH_MAX];

  assert_non_null(tmp_dir);
  vp_taint_mk_state_dirs(tmp_dir);

  vp_taint_model_reset();
  vp_taint_model_set_path_range(0, 0, 0, 4, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(0, 0, 0, 0x1111, 8, 4, VP_TAINT_VP_BYTE);
  vp_taint_model_set_path_range(1, 1, 16, 4, VP_TAINT_PATH_BYTE);
  vp_taint_model_set_vp_range_eq(1, 1, 0, 0x2222, 24, 4, VP_TAINT_VP_BYTE_2);

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));

  afl.value_profile_active = 1;
  afl.value_profile_level = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_slots = 1;
  afl.fixed_seed = 1;
  afl.rand_seed[0] = 1;
  afl.rand_seed[1] = 2;
  afl.rand_seed[2] = 3;
  afl.out_dir = (u8 *)tmp_dir;
  afl.perm = 0600;

  afl.shm.vp_map = ck_alloc(sizeof(vp_map_t));
  assert_non_null(afl.shm.vp_map);

  frontier_n = (size_t)CMP_MAP_W * afl.value_profile_slots *
               VP_RUNTIME_SLOT_REPLICA_LIMIT;
  afl.vp_frontier = ck_alloc(frontier_n * sizeof(vp_frontier_entry_t));
  assert_non_null(afl.vp_frontier);
  for (size_t i = 0; i < frontier_n; ++i) {

    afl.vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

  fname = alloc_printf("%s/queue/id:000007", tmp_dir);
  q.fname = fname;
  q.id = 7;
  q.len = VP_TAINT_TEST_LEN;

  span = vp_taint_frontier_span(afl.value_profile_slots);
  afl.vp_frontier[0 * span + 0].owner = &q;
  afl.vp_frontier[0 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = AFL_VP_TAINT_TIMEOUT_MS;
  vp_taint_analyze(&afl, &q);
  assert_null(q.vp_taint);
  assert_non_null(q.vp_taint_resume);

  afl.vp_frontier[0 * span + 0].owner = NULL;
  afl.vp_frontier[0 * span + 0].dist = VP_DIST_UNSOLVED;
  afl.vp_frontier[1 * span + 0].owner = &q;
  afl.vp_frontier[1 * span + 0].dist = 5;
  vp_taint_rebuild_owned_sites(&afl, &q);

  vp_taint_fake_time_ms = 0;
  vp_taint_fake_time_step = 1;
  vp_taint_analyze(&afl, &q);
  assert_non_null(q.vp_taint);
  assert_null(q.vp_taint_resume);

  vp_taint_bitmap_from_list(&q, vp_sensitive, VP_TAINT_TEST_LEN);
  for (u32 i = 8; i < 12; ++i) {

    assert_int_equal(vp_sensitive[i], 0);

  }

  for (u32 i = 24; i < 28; ++i) {

    assert_int_equal(vp_sensitive[i], 1);

  }

  vp_taint_free(&q);
  vp_taint_resume_free(&q);
  ck_free(fname);
  ck_free(afl.vp_frontier);
  ck_free(afl.shm.vp_map);

  snprintf(state_file, sizeof(state_file), "%s/queue/.state/vp_taint/id:000007",
           tmp_dir);
  unlink(state_file);

  {

    char p[PATH_MAX];
    snprintf(p, sizeof(p), "%s/queue/.state/vp_taint", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state/deterministic_done", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue/.state", tmp_dir);
    rmdir(p);
    snprintf(p, sizeof(p), "%s/queue", tmp_dir);
    rmdir(p);
    rmdir(tmp_dir);

  }

}

int main(int argc, char **argv) {

  (void)argc;
  (void)argv;

  const struct CMUnitTest tests[] = {
      cmocka_unit_test(test_vp_taint_classifies_vp_path_and_neutral_bytes),
      cmocka_unit_test(test_vp_taint_classifies_interleaved_regions),
      cmocka_unit_test(test_vp_taint_multi_site_ownership),
      cmocka_unit_test(test_vp_taint_asymmetric_perturbation_finds_vp_byte),
      cmocka_unit_test(test_vp_taint_phase1_budget_zero_is_conservative),
      cmocka_unit_test(test_vp_taint_phase1_inconclusive_exec_is_conservative),
      cmocka_unit_test(test_vp_taint_phase2_inconclusive_exec_advances_progress),
      cmocka_unit_test(test_vp_taint_exec_restores_state_on_error_and_stopsoon),
      cmocka_unit_test(test_vp_taint_exec_filters_non_owned_sites),
      cmocka_unit_test(test_vp_taint_multi_slot_state_changes),
      cmocka_unit_test(test_vp_taint_metric1_only_changes_are_sensitive),
      cmocka_unit_test(test_vp_taint_sub8_interleaving_relaxed_invariants),
      cmocka_unit_test(test_vp_taint_state_save_and_load),
      cmocka_unit_test(test_vp_taint_state_load_rejects_truncated_file),
      cmocka_unit_test(test_vp_taint_state_load_rejects_unsorted_sites),
      cmocka_unit_test(test_vp_taint_state_save_and_load_empty_result),
      cmocka_unit_test(test_vp_taint_state_load_marks_current_when_owned_sites_covered),
      cmocka_unit_test(test_vp_taint_state_load_marks_stale_when_owned_site_missing),
      cmocka_unit_test(test_vp_taint_keeps_initial_result_when_owned_sites_change),
      cmocka_unit_test(test_vp_taint_unanalyzed_empty_result_does_not_cover_owned),
      cmocka_unit_test(test_vp_taint_analyzed_empty_result_is_current_when_owned_covered),
      cmocka_unit_test(test_vp_taint_owned_generation_tracks_unique_site_set),
      cmocka_unit_test(test_vp_taint_second_call_is_noop_after_completion),
      cmocka_unit_test(test_vp_taint_analyze_resumes_after_timeout),
      cmocka_unit_test(
          test_vp_taint_resume_restarts_after_owned_sites_generation_change)};

  __real_exit(cmocka_run_group_tests(tests, NULL, NULL));

  /* fake return for dumb compilers */
  return 0;

}
