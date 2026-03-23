#include <stdarg.h>
#include <stddef.h>
#include <setjmp.h>
#include <assert.h>
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

typedef struct {

  afl_state_t *afl;
  u32          site;
  u8           shape;
  u64          v0;
  u64          v1;
  u8           enabled;
  u8           result;

} cmplog_stub_cfg_t;

static cmplog_stub_cfg_t cmplog_stub_cfg;

/* Stubs for functions referenced by afl-fuzz-valprof.o. */
u32 write_to_testcase(afl_state_t *afl, void **mem, u32 len, u32 fix) {

  (void)afl;
  (void)mem;
  (void)fix;
  return len;

}


fsrv_run_result_t fuzz_run_target(afl_state_t *afl, afl_forkserver_t *fsrv,
                                  u32 timeout) {

  (void)timeout;

  if (cmplog_stub_cfg.enabled && cmplog_stub_cfg.afl == afl &&
      fsrv == &afl->cmplog_fsrv && afl->shm.cmp_map) {

    struct cmp_map *cmp = afl->shm.cmp_map;
    cmp->headers[cmplog_stub_cfg.site].hits = 1;
    cmp->headers[cmplog_stub_cfg.site].type = CMP_TYPE_INS;
    cmp->headers[cmplog_stub_cfg.site].shape = cmplog_stub_cfg.shape;
    cmp->log[cmplog_stub_cfg.site][0].v0 = cmplog_stub_cfg.v0;
    cmp->log[cmplog_stub_cfg.site][0].v1 = cmplog_stub_cfg.v1;
    return (fsrv_run_result_t)cmplog_stub_cfg.result;

  }

  return FSRV_RUN_OK;

}

u8 *queue_testcase_get(afl_state_t *afl, struct queue_entry *q) {

  static u8 dummy[4];
  (void)afl;
  (void)q;
  return dummy;

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

/* Deterministic clock for vp_update_activation(). */
static u64 fake_time_ms;
u64        get_cur_time(void) {

  return fake_time_ms;

}

static void test_mode2_activation_and_deactivation(void **state) {

  (void)state;

  afl_state_t afl;
  memset(&afl, 0, sizeof(afl));

  afl.value_profile_mode = 2;
  afl.value_profile_stagnation_secs = 60;
  fake_time_ms = 61000;
  afl.start_time = 0;
  afl.queue_cycle = 7;

  vp_update_activation(&afl);
  assert_int_equal(afl.value_profile_active, 1);
  assert_int_equal(afl.value_profile_enabled_cycle, 7);
  assert_int_equal(afl.score_changed, 1);

  /* A fresh edge find in the same cycle should not disable VP yet. */
  afl.score_changed = 0;
  afl.last_cov_find_time = fake_time_ms;
  vp_update_activation(&afl);
  assert_int_equal(afl.value_profile_active, 1);
  assert_int_equal(afl.value_profile_enabled_cycle, 7);
  assert_int_equal(afl.score_changed, 0);

  /* Disable after one full cycle once edge coverage recovers. */
  afl.score_changed = 0;
  afl.queue_cycle = 8;
  afl.last_cov_find_time = fake_time_ms;
  vp_update_activation(&afl);
  assert_int_equal(afl.value_profile_active, 0);
  assert_int_equal(afl.value_profile_enabled_cycle, 0);
  assert_int_equal(afl.score_changed, 1);

}

static void test_non_stagnation_mode_is_noop(void **state) {

  (void)state;

  afl_state_t afl;
  memset(&afl, 0, sizeof(afl));

  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_enabled_cycle = 5;
  afl.score_changed = 0;

  vp_update_activation(&afl);
  assert_int_equal(afl.value_profile_active, 1);
  assert_int_equal(afl.value_profile_enabled_cycle, 5);
  assert_int_equal(afl.score_changed, 0);

}

static void setup_vp_frontier(afl_state_t *afl, u32 slots);
static void free_vp_frontier(afl_state_t *afl);

static inline size_t vp_test_slot_replicas(afl_state_t *afl) {

  return afl->value_profile_source == VP_SOURCE_RUNTIME_SHM
             ? VP_RUNTIME_SLOT_REPLICA_LIMIT
             : 1U;

}

static inline size_t vp_test_frontier_idx(afl_state_t *afl, u32 site, u32 rel) {

  return (size_t)site * afl->value_profile_slots * vp_test_slot_replicas(afl) +
         rel;

}

static inline size_t vp_test_runtime_frontier_idx(afl_state_t *afl, u32 site,
                                                  u32 slot_rel, u32 replica) {

  return vp_test_frontier_idx(afl, site,
                              slot_rel * VP_RUNTIME_SLOT_REPLICA_LIMIT +
                                  replica);

}

static void test_wide_ins_compare_keeps_vp_site_active(void **state) {

  (void)state;

  afl_state_t         afl;
  struct cmp_map     *cmp;
  struct queue_entry  old_q, new_q;
  struct queue_entry *vp_saved;

  memset(&afl, 0, sizeof(afl));
  memset(&old_q, 0, sizeof(old_q));
  memset(&new_q, 0, sizeof(new_q));

  cmp = calloc(1, sizeof(struct cmp_map));
  assert_non_null(cmp);
  afl.shm.cmp_map = cmp;
  afl.value_profile_level = 2;
  afl.value_profile_source = VP_SOURCE_CMPLOG_INLINE;

  setup_vp_frontier(&afl, 1);

  old_q.exec_us = 100;
  old_q.len = 100;
  old_q.vp_ref_cnt = 1;
  new_q.exec_us = 1;
  new_q.len = 1;

  /* 16-byte compare with identical low half and differing high half. */
  cmp->headers[0].hits = 1;
  cmp->headers[0].type = CMP_TYPE_INS;
  cmp->headers[0].shape = 15;                                   /* 16 bytes */
  cmp->log[0][0].v0 = 0x1122334455667788ULL;
  cmp->log[0][0].v1 = 0x1122334455667788ULL;
  cmp->log[0][0].v0_128 = 0x1ULL;
  cmp->log[0][0].v1_128 = 0x2ULL;
  afl.vp_trigger_bitmap[0] = 1;

  afl.vp_frontier[0].owner = &old_q;
  afl.vp_frontier[0].dist = 10;
  afl.vp_frontier[0].tag = 0;
  afl.vp_frontier[0].cost = 10000;
  afl.top_rated_vp[0] = &old_q;
  afl.top_rated_vp_dist[0] = 10;

  vp_frontier_apply(&afl, &new_q);

  vp_saved = afl.top_rated_vp[0];
  assert_ptr_equal(vp_saved, &new_q);
  assert_int_equal(old_q.vp_ref_cnt, 0);
  assert_true(new_q.vp_ref_cnt > 0);
  assert_true(afl.top_rated_vp_dist[0] < 65);
  assert_true(afl.top_rated_vp_dist[0] != 0xffffffff);

  free_vp_frontier(&afl);
  free(cmp);

}

static void test_solved_wide_ins_compare_does_not_consume_vp_bits(
    void **state) {

  (void)state;

  afl_state_t     afl;
  struct cmp_map *cmp;
  u8             *virgin;
  u32             bits;

  memset(&afl, 0, sizeof(afl));

  cmp = calloc(1, sizeof(struct cmp_map));
  assert_non_null(cmp);
  virgin = calloc(1, VALUE_PROFILE_MAP_SIZE);
  assert_non_null(virgin);
  memset(virgin, 0xff, VALUE_PROFILE_MAP_SIZE);

  afl.shm.cmp_map = cmp;
  afl.virgin_val_prof = virgin;

  cmp->headers[0].hits = 1;
  cmp->headers[0].type = CMP_TYPE_INS;
  cmp->headers[0].shape = 15;                                   /* 16 bytes */
  cmp->log[0][0].v0 = 0x1122334455667788ULL;
  cmp->log[0][0].v1 = 0x1122334455667788ULL;
  cmp->log[0][0].v0_128 = 0x99aabbccddeeff00ULL;
  cmp->log[0][0].v1_128 = 0x99aabbccddeeff00ULL;

  bits = vp_check_cmpmap(&afl);
  assert_int_equal(bits, 0);

  free(virgin);
  free(cmp);

}

static void test_solved_rtn_compare_does_not_consume_vp_bits(void **state) {

  (void)state;

  afl_state_t            afl;
  struct cmp_map        *cmp;
  struct cmpfn_operands *rtn;
  u8                    *virgin;
  u32                    bits;

  memset(&afl, 0, sizeof(afl));

  cmp = calloc(1, sizeof(struct cmp_map));
  assert_non_null(cmp);
  virgin = calloc(1, VALUE_PROFILE_MAP_SIZE);
  assert_non_null(virgin);
  memset(virgin, 0xff, VALUE_PROFILE_MAP_SIZE);

  afl.shm.cmp_map = cmp;
  afl.virgin_val_prof = virgin;

  cmp->headers[0].hits = 1;
  cmp->headers[0].type = CMP_TYPE_RTN;
  rtn = (struct cmpfn_operands *)cmp->log[0];

  /* String-like compare with equal content must not consume VP bits. */
  rtn[0].v0_len = 0x80 + 5;
  rtn[0].v1_len = 0x80 + 5;
  memcpy(rtn[0].v0, "AAAA", 5);
  memcpy(rtn[0].v1, "AAAA", 5);

  bits = vp_check_cmpmap(&afl);
  assert_int_equal(bits, 0);

  free(virgin);
  free(cmp);

}

static void setup_vp_frontier(afl_state_t *afl, u32 slots) {

  size_t n = (size_t)CMP_MAP_W * slots * vp_test_slot_replicas(afl);
  afl->value_profile_level = 1;
  afl->value_profile_slots = slots;
  afl->top_rated_vp = calloc(CMP_MAP_W, sizeof(struct queue_entry *));
  assert_non_null(afl->top_rated_vp);
  afl->top_rated_vp_dist = calloc(CMP_MAP_W, sizeof(u32));
  assert_non_null(afl->top_rated_vp_dist);
  for (u32 i = 0; i < CMP_MAP_W; ++i) {

    afl->top_rated_vp_dist[i] = VP_DIST_UNSOLVED;

  }

  afl->vp_frontier = calloc(n, sizeof(vp_frontier_entry_t));
  assert_non_null(afl->vp_frontier);
  for (size_t i = 0; i < n; ++i) {

    afl->vp_frontier[i].dist = VP_DIST_UNSOLVED;

  }

}

static void free_vp_frontier(afl_state_t *afl) {

  free(afl->vp_frontier);
  free(afl->vp_runtime_slot_mask);
  free(afl->top_rated_vp_dist);
  free(afl->top_rated_vp);

}

static void test_runtime_frontier_update_with_overflow_scan(void **state) {

  (void)state;

  afl_state_t        afl;
  vp_map_t          *vp;
  struct queue_entry q;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  q.exec_us = 3;
  q.len = 7;

  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.queue_cycle = 1;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 4);

  vp->exec_id = 1;
  vp->enabled = 1;
  vp->control_len = 1;
  vp->control[0] = 7;
  vp->site[7].valid_mask = 1;
  vp->site[7].touched_mask = 1;
  vp->site[7].slots[0].slot_key = 3;
  vp->site[7].slots[0].best_dist = 9;

  assert_true(vp_frontier_would_improve(&afl));
  vp_frontier_apply(&afl, &q);

  assert_ptr_equal(afl.top_rated_vp[7], &q);
  assert_int_equal(afl.top_rated_vp_dist[7], 9);
  assert_true(q.vp_ref_cnt > 0);

  free_vp_frontier(&afl);
  free(vp);

}

static void test_runtime_frontier_keeps_separate_metric_tags(void **state) {

  (void)state;

  afl_state_t        afl;
  vp_map_t          *vp;
  struct queue_entry q;
  u32                site = 23;
  size_t             idx0, idx1;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  q.exec_us = 5;
  q.len = 11;

  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.queue_cycle = 1;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 4);

  vp->exec_id = 1;
  vp->enabled = 1;
  vp->control_len = 1;
  vp->control[0] = (u16)site;
  vp->site[site].valid_mask = 0x3;
  vp->site[site].touched_mask = 0x3;
  /* Same compare hit, two metric tags: hamming (bit 0 clear) and
     absolute-distance (bit 0 set). */
  vp->site[site].slots[0].slot_key = 8;
  vp->site[site].slots[0].best_dist = 2;
  vp->site[site].slots[1].slot_key = 9;
  vp->site[site].slots[1].best_dist = 11;

  assert_true(vp_frontier_would_improve(&afl));
  vp_frontier_apply(&afl, &q);

  idx0 = vp_test_runtime_frontier_idx(&afl, site, 0, 0);
  idx1 = vp_test_runtime_frontier_idx(&afl, site, 1, 0);
  assert_ptr_equal(afl.vp_frontier[idx0].owner, &q);
  assert_ptr_equal(afl.vp_frontier[idx1].owner, &q);
  assert_int_equal(afl.vp_frontier[idx0].tag, 8);
  assert_int_equal(afl.vp_frontier[idx0].dist, 2);
  assert_int_equal(afl.vp_frontier[idx1].tag, 9);
  assert_int_equal(afl.vp_frontier[idx1].dist, 11);
  assert_int_equal(q.vp_ref_cnt, 2);
  assert_ptr_equal(afl.top_rated_vp[site], &q);
  assert_int_equal(afl.top_rated_vp_dist[site], 2);

  free_vp_frontier(&afl);
  free(vp);

}

static void test_runtime_frontier_keeps_best_replicas_per_slot(void **state) {

  (void)state;

  afl_state_t        afl;
  vp_map_t          *vp;
  struct queue_entry q[5];
  u32                site = 29;
  u32                dist[5] = {25, 20, 15, 10, 30};
  size_t             idx[VP_RUNTIME_SLOT_REPLICA_LIMIT];

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  for (u32 i = 0; i < 5; ++i) {

    q[i].exec_us = 7 + i;
    q[i].len = 13 + i;

  }

  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.queue_cycle = 1;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 4);

  vp->exec_id = 1;
  vp->enabled = 1;
  vp->control_len = 1;
  vp->control[0] = (u16)site;
  vp->site[site].valid_mask = 0x1;
  vp->site[site].protected_mask = 0x1;
  vp->site[site].touched_mask = 0x1;
  vp->site[site].slots[0].slot_key = 0;

  for (u32 i = 0; i < 5; ++i) {

    vp->exec_id = i + 1;
    vp->site[site].touched_mask = 0x1;
    vp->site[site].slots[0].best_dist = dist[i];
    assert_true(vp_frontier_would_improve(&afl) || i == 4);
    vp_frontier_apply(&afl, &q[i]);

  }

  for (u32 i = 0; i < VP_RUNTIME_SLOT_REPLICA_LIMIT; ++i) {

    idx[i] = vp_test_runtime_frontier_idx(&afl, site, 0, i);

  }

  assert_ptr_equal(afl.vp_frontier[idx[0]].owner, &q[0]);
  assert_ptr_equal(afl.vp_frontier[idx[1]].owner, &q[1]);
  assert_ptr_equal(afl.vp_frontier[idx[2]].owner, &q[2]);
  assert_ptr_equal(afl.vp_frontier[idx[3]].owner, &q[3]);
  for (u32 i = 0; i < VP_RUNTIME_SLOT_REPLICA_LIMIT; ++i) {

    assert_int_equal(afl.vp_frontier[idx[i]].tag, 0);
    assert_true(afl.vp_frontier[idx[i]].is_protected);

  }

  assert_int_equal(q[0].vp_ref_cnt, 1);
  assert_int_equal(q[1].vp_ref_cnt, 1);
  assert_int_equal(q[2].vp_ref_cnt, 1);
  assert_int_equal(q[3].vp_ref_cnt, 1);
  assert_int_equal(q[4].vp_ref_cnt, 0);
  assert_ptr_equal(afl.top_rated_vp[site], &q[3]);
  assert_int_equal(afl.top_rated_vp_dist[site], 10);

  free_vp_frontier(&afl);
  free(vp);

}

static void test_runtime_frontier_keeps_three_scalar_hit_pairs(void **state) {

  (void)state;

  afl_state_t        afl;
  vp_map_t          *vp;
  struct queue_entry q;
  u32                site = 31;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  q.exec_us = 9;
  q.len = 17;

  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.queue_cycle = 1;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 6);

  vp->exec_id = 1;
  vp->enabled = 1;
  vp->control_len = 1;
  vp->control[0] = (u16)site;
  vp->site[site].valid_mask = 0x3f;
  vp->site[site].protected_mask = 0x3f;
  vp->site[site].touched_mask = 0x3f;
  /* Three scalar hits with two metrics each should occupy distinct slot pairs
     once imported into a six-slot frontier. */
  vp->site[site].slots[0].slot_key = 0;
  vp->site[site].slots[0].best_dist = 7;
  vp->site[site].slots[1].slot_key = 1;
  vp->site[site].slots[1].best_dist = 12;
  vp->site[site].slots[2].slot_key = 2;
  vp->site[site].slots[2].best_dist = 5;
  vp->site[site].slots[3].slot_key = 3;
  vp->site[site].slots[3].best_dist = 11;
  vp->site[site].slots[4].slot_key = 4;
  vp->site[site].slots[4].best_dist = 3;
  vp->site[site].slots[5].slot_key = 5;
  vp->site[site].slots[5].best_dist = 9;

  assert_true(vp_frontier_would_improve(&afl));
  vp_frontier_apply(&afl, &q);

  for (u32 i = 0; i < 6; ++i) {

    size_t idx = vp_test_runtime_frontier_idx(&afl, site, i, 0);
    assert_ptr_equal(afl.vp_frontier[idx].owner, &q);
    assert_int_equal(afl.vp_frontier[idx].tag, i);
    assert_true(afl.vp_frontier[idx].is_protected);

  }

  assert_int_equal(q.vp_ref_cnt, 6);
  assert_ptr_equal(afl.top_rated_vp[site], &q);
  assert_int_equal(afl.top_rated_vp_dist[site], 3);

  free_vp_frontier(&afl);
  free(vp);

}

static void test_l1_favoring_marks_best_entry_per_runtime_slot(void **state) {

  (void)state;

  afl_state_t         afl;
  struct queue_entry  q_best0, q_other0, q_best1;
  u32                 site0 = 5, site1 = 9;
  size_t              idx0, idx1, idx2;

  memset(&afl, 0, sizeof(afl));
  memset(&q_best0, 0, sizeof(q_best0));
  memset(&q_other0, 0, sizeof(q_other0));
  memset(&q_best1, 0, sizeof(q_best1));
  afl.smallest_favored = -1;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  setup_vp_frontier(&afl, 4);

  q_best0.id = 10;
  q_other0.id = 20;
  q_best1.id = 30;

  idx0 = vp_test_runtime_frontier_idx(&afl, site0, 0, 0);
  idx1 = vp_test_runtime_frontier_idx(&afl, site0, 0, 1);
  idx2 = vp_test_runtime_frontier_idx(&afl, site1, 0, 0);

  afl.vp_frontier[idx0].owner = &q_best0;
  afl.vp_frontier[idx0].tag = 1;
  afl.vp_frontier[idx0].dist = 7;
  afl.vp_frontier[idx0].cost = 100;
  afl.vp_frontier[idx0].is_protected = 1;

  afl.vp_frontier[idx1].owner = &q_other0;
  afl.vp_frontier[idx1].tag = 1;
  afl.vp_frontier[idx1].dist = 9;
  afl.vp_frontier[idx1].cost = 200;
  afl.vp_frontier[idx1].is_protected = 0;

  afl.vp_frontier[idx2].owner = &q_best1;
  afl.vp_frontier[idx2].tag = 2;
  afl.vp_frontier[idx2].dist = 5;
  afl.vp_frontier[idx2].cost = 300;
  afl.vp_frontier[idx2].is_protected = 1;

  vp_mark_favored_runtime_slots(&afl);

  assert_true(q_best0.favored);
  assert_false(q_other0.favored);
  assert_true(q_best1.favored);
  assert_int_equal(afl.queued_favored, 2);
  assert_int_equal(afl.pending_favored, 2);
  assert_int_equal(afl.smallest_favored, 10);

  free_vp_frontier(&afl);

}

static void test_l1_favoring_uses_runtime_slot_mask(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q_masked, q_unmasked;
  u32                site_masked = 13, site_unmasked = 17;
  size_t             idx_masked, idx_unmasked;

  memset(&afl, 0, sizeof(afl));
  memset(&q_masked, 0, sizeof(q_masked));
  memset(&q_unmasked, 0, sizeof(q_unmasked));
  afl.smallest_favored = -1;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  setup_vp_frontier(&afl, 4);
  afl.vp_runtime_slot_mask = calloc(CMP_MAP_W, sizeof(u16));
  assert_non_null(afl.vp_runtime_slot_mask);

  q_masked.id = 10;
  q_unmasked.id = 20;

  idx_masked = vp_test_runtime_frontier_idx(&afl, site_masked, 0, 0);
  idx_unmasked = vp_test_runtime_frontier_idx(&afl, site_unmasked, 0, 0);

  afl.vp_frontier[idx_masked].owner = &q_masked;
  afl.vp_frontier[idx_masked].tag = 1;
  afl.vp_frontier[idx_masked].dist = 7;
  afl.vp_frontier[idx_masked].cost = 100;
  afl.vp_frontier[idx_masked].is_protected = 1;

  afl.vp_frontier[idx_unmasked].owner = &q_unmasked;
  afl.vp_frontier[idx_unmasked].tag = 2;
  afl.vp_frontier[idx_unmasked].dist = 5;
  afl.vp_frontier[idx_unmasked].cost = 90;
  afl.vp_frontier[idx_unmasked].is_protected = 1;

  /* Sparse scanner should consider only masked runtime slots. */
  afl.vp_runtime_slot_mask[site_masked] = 1U;

  vp_mark_favored_runtime_slots(&afl);

  assert_true(q_masked.favored);
  assert_false(q_unmasked.favored);
  assert_int_equal(afl.queued_favored, 1);
  assert_int_equal(afl.pending_favored, 1);
  assert_int_equal(afl.smallest_favored, 10);

  free_vp_frontier(&afl);

}

static void test_l1_runtime_slot_mask_clears_stale_external_disable(
    void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  u32                site = 13;
  size_t             idx;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  afl.smallest_favored = -1;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  setup_vp_frontier(&afl, 4);
  afl.vp_runtime_slot_mask = calloc(CMP_MAP_W, sizeof(u16));
  assert_non_null(afl.vp_runtime_slot_mask);

  idx = vp_test_runtime_frontier_idx(&afl, site, 0, 0);
  afl.vp_frontier[idx].owner = &q;
  afl.vp_frontier[idx].tag = 1;
  afl.vp_frontier[idx].dist = 7;
  afl.vp_frontier[idx].cost = 100;
  afl.vp_frontier[idx].is_protected = 1;
  afl.vp_runtime_slot_mask[site] = 1U;

  /* Simulate disable from a non-VP path (for example redundant disabling). */
  q.disabled = 1;

  vp_mark_favored_runtime_slots(&afl);

  assert_false(q.favored);
  assert_int_equal(afl.vp_runtime_slot_mask[site], 0U);
  assert_int_equal(afl.queued_favored, 0);
  assert_int_equal(afl.pending_favored, 0);

  free_vp_frontier(&afl);

}

static void test_runtime_frontier_retains_protected_same_tag_on_equal_dist(
    void **state) {

  (void)state;

  afl_state_t         afl;
  vp_map_t           *vp;
  struct queue_entry  q_overflow, q_home;
  u32                 site = 37;
  size_t              idx0, idx1;

  memset(&afl, 0, sizeof(afl));
  memset(&q_overflow, 0, sizeof(q_overflow));
  memset(&q_home, 0, sizeof(q_home));
  q_overflow.exec_us = 10;
  q_overflow.len = 10;
  q_home.exec_us = 10;
  q_home.len = 10;

  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.queue_cycle = 1;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 1);

  vp->exec_id = 1;
  vp->enabled = 1;
  vp->control_len = 1;
  vp->control[0] = (u16)site;
  vp->site[site].valid_mask = 0x1;
  vp->site[site].touched_mask = 0x1;
  vp->site[site].protected_mask = 0x0;
  vp->site[site].slots[0].slot_key = 0;
  vp->site[site].slots[0].best_dist = 7;

  assert_true(vp_frontier_would_improve(&afl));
  vp_frontier_apply(&afl, &q_overflow);

  idx0 = vp_test_runtime_frontier_idx(&afl, site, 0, 0);
  assert_ptr_equal(afl.vp_frontier[idx0].owner, &q_overflow);
  assert_false(afl.vp_frontier[idx0].is_protected);

  vp->exec_id = 2;
  vp->site[site].touched_mask = 0x1;
  vp->site[site].protected_mask = 0x1;
  vp->site[site].slots[0].slot_key = 0;
  vp->site[site].slots[0].best_dist = 7;

  assert_true(vp_frontier_would_improve(&afl));
  vp_frontier_apply(&afl, &q_home);

  idx1 = vp_test_runtime_frontier_idx(&afl, site, 0, 1);
  assert_ptr_equal(afl.vp_frontier[idx0].owner, &q_overflow);
  assert_false(afl.vp_frontier[idx0].is_protected);
  assert_ptr_equal(afl.vp_frontier[idx1].owner, &q_home);
  assert_true(afl.vp_frontier[idx1].is_protected);
  assert_int_equal(q_overflow.vp_ref_cnt, 1);
  assert_int_equal(q_home.vp_ref_cnt, 1);

  free_vp_frontier(&afl);
  free(vp);

}

static void test_runtime_trim_guard_preserve_and_regress(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  vp_map_t          *vp;
  vp_trim_guard_t   *guard;
  u32                site = 11;
  size_t             idx;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 1);

  q.vp_ref_cnt = 1;
  q.exec_us = 3;
  q.len = 9;
  idx = vp_test_frontier_idx(&afl, site, 0);
  afl.vp_frontier[idx].owner = &q;
  afl.vp_frontier[idx].dist = 5;
  afl.vp_frontier[idx].tag = 7;
  afl.vp_frontier[idx].cost = 100;

  vp->enabled = 1;
  vp->exec_id = 4;
  vp->site[site].valid_mask = 0x3;
  vp->site[site].touched_mask = 0x2;
  vp->site[site].slots[1].slot_key = 0xaa;
  vp->site[site].slots[1].best_dist = 17;

  guard = vp_trim_guard_init(&afl, &q);
  assert_non_null(guard);

  vp_trim_guard_before_exec(guard);
  vp->site[site].valid_mask = 1;
  vp->site[site].touched_mask = 1;
  vp->site[site].slots[0].slot_key = 7;
  vp->site[site].slots[0].best_dist = 4;
  assert_true(vp_trim_guard_preserved(guard, NULL, 0, 0, 0));
  vp_trim_guard_after_exec(guard);

  assert_int_equal(vp->site[site].valid_mask, 0x3);
  assert_int_equal(vp->site[site].touched_mask, 0x2);
  assert_int_equal(vp->site[site].slots[1].slot_key, 0xaa);
  assert_int_equal(vp->site[site].slots[1].best_dist, 17);

  vp_trim_guard_before_exec(guard);
  vp->site[site].valid_mask = 1;
  vp->site[site].touched_mask = 1;
  vp->site[site].slots[0].slot_key = 7;
  vp->site[site].slots[0].best_dist = 6;
  assert_false(vp_trim_guard_preserved(guard, NULL, 0, 0, 0));
  vp_trim_guard_after_exec(guard);

  vp_trim_guard_destroy(guard);
  free_vp_frontier(&afl);
  free(vp);

}

static void test_runtime_observe_helper_resets_and_restores_sites(
    void **state) {

  (void)state;

  afl_state_t afl;
  vp_map_t   *vp;
  u16         site_ids[2] = {3, 9};
  vp_site_t   saved[2];
  vp_site_t   orig0, orig1, untouched;

  memset(&afl, 0, sizeof(afl));
  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.shm.vp_map = vp;
  vp->enabled = 1;
  vp->exec_id = 7;

  vp->site[3].exec_seen = 11;
  vp->site[3].hit_count = 2;
  vp->site[3].valid_mask = 0x3;
  vp->site[3].touched_mask = 0x1;
  vp->site[3].protected_mask = 0x2;
  vp->site[3].slots[0].slot_key = 0x1111;
  vp->site[3].slots[0].best_dist = 9;

  vp->site[9].exec_seen = 13;
  vp->site[9].hit_count = 4;
  vp->site[9].valid_mask = 0x7;
  vp->site[9].touched_mask = 0x4;
  vp->site[9].protected_mask = 0x1;
  vp->site[9].slots[1].slot_key = 0x2222;
  vp->site[9].slots[1].best_dist = 5;

  vp->site[4].exec_seen = 21;
  vp->site[4].valid_mask = 0x9;
  vp->site[4].slots[0].slot_key = 0x3333;
  vp->site[4].slots[0].best_dist = 12;

  orig0 = vp->site[3];
  orig1 = vp->site[9];
  untouched = vp->site[4];

  assert_true(vp_runtime_observe_begin(&afl, site_ids, 2, saved,
                                       VP_RUNTIME_OBSERVE_TAINT));
  assert_true(vp->filter_enabled);
  assert_int_equal(vp->site[3].valid_mask, 0);
  assert_int_equal(vp->site[3].touched_mask, 0);
  assert_int_equal(vp->site[3].protected_mask, 0);
  assert_int_equal(vp->site[3].slots[0].slot_key, 0xffff);
  assert_int_equal(vp->site[3].slots[0].best_dist, 0xffff);
  assert_memory_equal(&vp->site[4], &untouched, sizeof(vp_site_t));

  vp->site[3].valid_mask = 1;
  vp->site[9].valid_mask = 1;
  vp_runtime_observe_end(&afl, site_ids, 2, saved);

  assert_false(vp->filter_enabled);
  assert_memory_equal(&vp->site[3], &orig0, sizeof(vp_site_t));
  assert_memory_equal(&vp->site[9], &orig1, sizeof(vp_site_t));
  assert_memory_equal(&vp->site[4], &untouched, sizeof(vp_site_t));

  assert_true(vp_runtime_observe_begin(&afl, site_ids, 2, saved,
                                       VP_RUNTIME_OBSERVE_TRIM));
  assert_true(vp->filter_enabled);
  assert_int_equal(vp->site[3].exec_seen, vp->exec_id);
  assert_int_equal(vp->site[3].hit_count, 0);
  assert_int_equal(vp->site[3].valid_mask, 0);
  assert_int_equal(vp->site[3].slots[0].slot_key, 0);
  assert_int_equal(vp->site[3].slots[0].best_dist, 0);

  vp->site[3].valid_mask = 1;
  vp->site[9].valid_mask = 1;
  vp_runtime_observe_end(&afl, site_ids, 2, saved);

  assert_false(vp->filter_enabled);
  assert_memory_equal(&vp->site[3], &orig0, sizeof(vp_site_t));
  assert_memory_equal(&vp->site[9], &orig1, sizeof(vp_site_t));

  free(vp);

}

static void test_runtime_trim_guard_distinguishes_runtime_slots(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  vp_map_t          *vp;
  vp_trim_guard_t   *guard;
  u32                site = 41;
  size_t             idx0, idx1;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  vp = calloc(1, sizeof(vp_map_t));
  assert_non_null(vp);

  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_RUNTIME_SHM;
  afl.shm.vp_map = vp;
  setup_vp_frontier(&afl, 2);

  q.vp_ref_cnt = 2;
  q.exec_us = 3;
  q.len = 9;
  idx0 = vp_test_runtime_frontier_idx(&afl, site, 0, 0);
  idx1 = vp_test_runtime_frontier_idx(&afl, site, 1, 0);
  afl.vp_frontier[idx0].owner = &q;
  afl.vp_frontier[idx0].dist = 5;
  afl.vp_frontier[idx0].tag = 7;
  afl.vp_frontier[idx0].cost = 100;
  afl.vp_frontier[idx1].owner = &q;
  afl.vp_frontier[idx1].dist = 5;
  afl.vp_frontier[idx1].tag = 7;
  afl.vp_frontier[idx1].cost = 100;

  vp->enabled = 1;
  vp->exec_id = 4;

  guard = vp_trim_guard_init(&afl, &q);
  assert_non_null(guard);

  vp_trim_guard_before_exec(guard);
  vp->site[site].valid_mask = 0x1;
  vp->site[site].touched_mask = 0x1;
  vp->site[site].slots[0].slot_key = 7;
  vp->site[site].slots[0].best_dist = 4;
  assert_false(vp_trim_guard_preserved(guard, NULL, 0, 0, 0));
  vp_trim_guard_after_exec(guard);

  vp_trim_guard_before_exec(guard);
  vp->site[site].valid_mask = 0x3;
  vp->site[site].touched_mask = 0x3;
  vp->site[site].slots[0].slot_key = 7;
  vp->site[site].slots[0].best_dist = 4;
  vp->site[site].slots[1].slot_key = 7;
  vp->site[site].slots[1].best_dist = 4;
  assert_true(vp_trim_guard_preserved(guard, NULL, 0, 0, 0));
  vp_trim_guard_after_exec(guard);

  vp_trim_guard_destroy(guard);
  free_vp_frontier(&afl);
  free(vp);

}

static void test_cmplog_inline_trim_guard_preserve_and_regress(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  struct cmp_map    *cmp;
  vp_trim_guard_t   *guard;
  u32                site = 19;
  size_t             idx;

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  cmp = calloc(1, sizeof(struct cmp_map));
  assert_non_null(cmp);

  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_CMPLOG_INLINE;
  afl.shm.cmp_map = cmp;
  setup_vp_frontier(&afl, 1);

  q.vp_ref_cnt = 1;
  idx = vp_test_frontier_idx(&afl, site, 0);
  afl.vp_frontier[idx].owner = &q;
  afl.vp_frontier[idx].dist = 3;
  afl.vp_frontier[idx].tag = 0;
  afl.vp_frontier[idx].cost = 100;

  guard = vp_trim_guard_init(&afl, &q);
  assert_non_null(guard);

  cmp->headers[site].hits = 1;
  cmp->headers[site].type = CMP_TYPE_INS;
  cmp->headers[site].shape = 0;
  cmp->log[site][0].v0 = 0x1;
  cmp->log[site][0].v1 = 0x2;
  assert_true(vp_trim_guard_preserved(guard, NULL, 0, 0, 0));

  cmp->headers[site].hits = 1;
  cmp->headers[site].type = CMP_TYPE_INS;
  cmp->headers[site].shape = 0;
  cmp->log[site][0].v0 = 0x0;
  cmp->log[site][0].v1 = 0xf0;
  assert_false(vp_trim_guard_preserved(guard, NULL, 0, 0, 0));

  vp_trim_guard_destroy(guard);
  free_vp_frontier(&afl);
  free(cmp);

}

static void test_cmplog_child_trim_guard_preserve_and_regress(void **state) {

  (void)state;

  afl_state_t        afl;
  struct queue_entry q;
  struct cmp_map    *cmp;
  vp_trim_guard_t   *guard;
  u32                site = 13;
  size_t             idx;
  u8                 in_buf[6] = {1, 2, 3, 4, 5, 6};

  memset(&afl, 0, sizeof(afl));
  memset(&q, 0, sizeof(q));
  memset(&cmplog_stub_cfg, 0, sizeof(cmplog_stub_cfg));
  cmp = calloc(1, sizeof(struct cmp_map));
  assert_non_null(cmp);

  afl.value_profile_mode = 1;
  afl.value_profile_active = 1;
  afl.value_profile_source = VP_SOURCE_CMPLOG_CHILD;
  afl.shm.cmp_map = cmp;
  afl.cmplog_binary = (u8 *)"dummy-cmplog";
  afl.cmplog_max_filesize = 4096;
  afl.fsrv.map_size = 1;
  afl.fsrv.trace_bits = calloc(1, 1);
  afl.map_tmp_buf = calloc(1, 1);
  assert_non_null(afl.fsrv.trace_bits);
  assert_non_null(afl.map_tmp_buf);
  setup_vp_frontier(&afl, 1);

  q.vp_ref_cnt = 1;
  idx = vp_test_frontier_idx(&afl, site, 0);
  afl.vp_frontier[idx].owner = &q;
  afl.vp_frontier[idx].dist = 2;
  afl.vp_frontier[idx].tag = 0;
  afl.vp_frontier[idx].cost = 100;

  guard = vp_trim_guard_init(&afl, &q);
  assert_non_null(guard);

  cmplog_stub_cfg.enabled = 1;
  cmplog_stub_cfg.afl = &afl;
  cmplog_stub_cfg.site = site;
  cmplog_stub_cfg.shape = 0;
  cmplog_stub_cfg.v0 = 0x1;
  cmplog_stub_cfg.v1 = 0x2;
  cmplog_stub_cfg.result = FSRV_RUN_OK;
  assert_true(vp_trim_guard_preserved(guard, in_buf, sizeof(in_buf), 1, 1));

  cmplog_stub_cfg.v0 = 0x0;
  cmplog_stub_cfg.v1 = 0xf0;
  assert_false(vp_trim_guard_preserved(guard, in_buf, sizeof(in_buf), 1, 1));

  cmplog_stub_cfg.enabled = 0;
  vp_trim_guard_destroy(guard);
  free_vp_frontier(&afl);
  free(afl.fsrv.trace_bits);
  free(afl.map_tmp_buf);
  free(cmp);

}

static void test_trim_deferred_cleared_on_last_ref_drop(void **state) {

  (void)state;

  afl_state_t         afl;
  struct cmp_map     *cmp;
  struct queue_entry  old_q, new_q;
  u32                 site = 3;
  size_t              idx;

  memset(&afl, 0, sizeof(afl));
  memset(&old_q, 0, sizeof(old_q));
  memset(&new_q, 0, sizeof(new_q));
  cmp = calloc(1, sizeof(struct cmp_map));
  assert_non_null(cmp);

  afl.value_profile_level = 2;
  afl.value_profile_source = VP_SOURCE_CMPLOG_INLINE;
  afl.queue_cycle = 5;
  afl.shm.cmp_map = cmp;
  afl.vp_trigger_bitmap[site >> 6] = 1ULL << (site & 63);
  setup_vp_frontier(&afl, 1);

  old_q.vp_ref_cnt = 1;
  old_q.trim_done = 1;
  old_q.vp_trim_deferred = 1;
  old_q.exec_us = 10;
  old_q.len = 100;

  new_q.exec_us = 1;
  new_q.len = 8;

  idx = vp_test_frontier_idx(&afl, site, 0);
  afl.vp_frontier[idx].owner = &old_q;
  afl.vp_frontier[idx].dist = 10;
  afl.vp_frontier[idx].tag = 0;
  afl.vp_frontier[idx].cost = 1000;
  afl.top_rated_vp[site] = &old_q;
  afl.top_rated_vp_dist[site] = 10;

  cmp->headers[site].hits = 1;
  cmp->headers[site].type = CMP_TYPE_INS;
  cmp->headers[site].shape = 0;
  cmp->log[site][0].v0 = 0x1;
  cmp->log[site][0].v1 = 0x2;

  vp_frontier_apply(&afl, &new_q);

  assert_int_equal(old_q.vp_ref_cnt, 0);
  assert_int_equal(old_q.vp_trim_deferred, 0);
  assert_int_equal(old_q.trim_done, 0);
  assert_true(new_q.vp_ref_cnt > 0);
  assert_ptr_equal(afl.top_rated_vp[site], &new_q);

  free_vp_frontier(&afl);
  free(cmp);

}

int main(int argc, char **argv) {

  (void)argc;
  (void)argv;

  const struct CMUnitTest tests[] = {

      cmocka_unit_test(test_mode2_activation_and_deactivation),
      cmocka_unit_test(test_non_stagnation_mode_is_noop),
      cmocka_unit_test(test_wide_ins_compare_keeps_vp_site_active),
      cmocka_unit_test(test_solved_wide_ins_compare_does_not_consume_vp_bits),
      cmocka_unit_test(test_solved_rtn_compare_does_not_consume_vp_bits),
      cmocka_unit_test(test_runtime_frontier_update_with_overflow_scan),
      cmocka_unit_test(test_runtime_frontier_keeps_separate_metric_tags),
      cmocka_unit_test(test_runtime_frontier_keeps_best_replicas_per_slot),
      cmocka_unit_test(test_runtime_frontier_keeps_three_scalar_hit_pairs),
      cmocka_unit_test(test_l1_favoring_marks_best_entry_per_runtime_slot),
      cmocka_unit_test(test_l1_favoring_uses_runtime_slot_mask),
      cmocka_unit_test(
          test_l1_runtime_slot_mask_clears_stale_external_disable),
      cmocka_unit_test(
          test_runtime_frontier_retains_protected_same_tag_on_equal_dist),
      cmocka_unit_test(test_runtime_observe_helper_resets_and_restores_sites),
      cmocka_unit_test(test_runtime_trim_guard_preserve_and_regress),
      cmocka_unit_test(test_runtime_trim_guard_distinguishes_runtime_slots),
      cmocka_unit_test(test_cmplog_inline_trim_guard_preserve_and_regress),
      cmocka_unit_test(test_cmplog_child_trim_guard_preserve_and_regress),
      cmocka_unit_test(test_trim_deferred_cleared_on_last_ref_drop)};

  __real_exit(cmocka_run_group_tests(tests, NULL, NULL));

  // fake return for dumb compilers
  return 0;

}
