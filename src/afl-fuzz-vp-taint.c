/*
   american fuzzy lop++ - VP taint analysis
   ----------------------------------------

   Originally written by Michal Zalewski

   Now maintained by Marc Heuse <mh@mh-sec.de>,
                     Dominik Meier <mail@dmnk.co>,
                     Andrea Fioraldi <andreafioraldi@gmail.com>, and
                     Heiko Eissfeldt <heiko.eissfeldt@hexco.de>

   Copyright 2016, 2017 Google Inc. All rights reserved.
   Copyright 2019-2026 AFLplusplus Project. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     https://www.apache.org/licenses/LICENSE-2.0

   VP taint analysis identifies which input bytes affect VP distances
   at each owned frontier site, then biases havoc mutations toward
   those bytes.

 */

#include "afl-fuzz.h"
#include "value-profile.h"

/* ---- internal types ---- */

/* Per-site status from one execution. */
typedef struct {

  u16       site_id;
  u8        fired;                /* site appeared in this execution        */
  u16       valid_mask;           /* per-exec active slots for this site    */
  vp_slot_t slots[VP_MAX_SLOTS];

} vp_taint_site_status_t;

/* Collected execution result for taint analysis. */
typedef struct {

  u32                     n_sites;
  vp_taint_site_status_t *sites;

} vp_taint_exec_result_t;

/* Range for Phase 1 binary search. */
typedef struct vp_taint_range {

  u32                    start;
  u32                    end;
  struct vp_taint_range *next;

} vp_taint_range_t;

/* Per-entry resumable analysis state (in-memory only). */
struct vp_taint_resume {

  u32                     phase2_next_idx;
  u32                     phase2_cnt;
  u32                    *phase2_order;
  u32                     n_owned;
  u16                    *owned_sites;
  vp_taint_site_status_t *baseline_sites;
  u8                     *non_neutral;
  u32                    *sensitive_cnts;
  u32                    *sensitive_caps;
  u32                   **sensitive_bufs;
  u32                     exec_cnt;

};

typedef struct {

  u32 magic;
  u32 version;
  u32 len;
  u32 site_cnt;

} vp_taint_file_header_t;

typedef struct {

  u16 site_id;
  u16 reserved;
  u32 sensitive_cnt;

} vp_taint_file_site_t;

#define VP_TAINT_FILE_MAGIC 0x56505431U                           /* "VPT1" */
#define VP_TAINT_FILE_VERSION 1U

static void collect_owned_sites(afl_state_t *afl, struct queue_entry *q,
                                u16 **out_sites, u32 *out_cnt);

/* ---- helpers ---- */

static inline u8 vp_taint_timed_out(u64 start_ms) {

  return unlikely(get_cur_time() - start_ms >= AFL_VP_TAINT_TIMEOUT_MS);

}

/* Generate a buffer where each byte differs from the original. */
static void random_replace_vp(afl_state_t *afl, u8 *buf, u32 len) {

  for (u32 i = 0; i < len; i++) {

    u8 c;
    do {

      c = rand_below(afl, 256);

    } while (c == buf[i]);

    buf[i] = c;

  }

}

/* Compute the frontier span per site.  Mirrors vp_frontier_site_span()
   which is static in afl-fuzz-valprof.c. */
static inline size_t vp_taint_site_span(afl_state_t *afl) {

  size_t replicas = (afl->value_profile_source == VP_SOURCE_RUNTIME_SHM)
                        ? VP_RUNTIME_SLOT_REPLICA_LIMIT
                        : 1U;
  return (size_t)afl->value_profile_slots * replicas;

}

/* Active runtime slot bitmask for configured slot count (1..16). */
static inline u16 vp_taint_site_active_mask(const afl_state_t *afl) {

  u16 slots = (u16)MIN(afl->value_profile_slots, (u32)VP_MAX_SLOTS);
  if (slots >= VP_MAX_SLOTS) return 0xffffU;
  return (u16)((1U << slots) - 1U);

}

/* Compare per-site VP slot state for one execution using a caller-supplied
   slot mask. */
static inline u8 vp_taint_site_state_changed_mask(
    const afl_state_t *afl, const vp_taint_site_status_t *baseline,
    const vp_taint_site_status_t *current, u16 slot_mask) {

  u16 active_mask = vp_taint_site_active_mask(afl);
  u16 use_mask = (u16)(slot_mask & active_mask);
  if (!use_mask) use_mask = active_mask;

  u16 base_valid = (u16)(baseline->valid_mask & use_mask);
  u16 cur_valid = (u16)(current->valid_mask & use_mask);
  if (base_valid != cur_valid) return 1;

  u16 bits = (u16)((base_valid | cur_valid) & use_mask);
  while (bits) {

    u16 slot = (u16)__builtin_ctz((u32)bits);
    if (baseline->slots[slot].slot_key != current->slots[slot].slot_key ||
        baseline->slots[slot].best_dist != current->slots[slot].best_dist)
      return 1;
    bits = (u16)(bits & (bits - 1U));

  }

  return 0;

}

/* Conservative inclusion signal: any active slot state changed. */
static inline u8 vp_taint_site_state_changed(
    const afl_state_t *afl, const vp_taint_site_status_t *baseline,
    const vp_taint_site_status_t *current) {

  return vp_taint_site_state_changed_mask(afl, baseline, current,
                                          vp_taint_site_active_mask(afl));

}

/* Check whether queue entry q owns any frontier slot for the given site. */
u8 vp_taint_site_owned(afl_state_t *afl, u16 site_id, struct queue_entry *q) {

  size_t span = vp_taint_site_span(afl);
  size_t base = (size_t)site_id * span;
  for (size_t rel = 0; rel < span; rel++) {

    if (afl->vp_frontier[base + rel].owner == q) return 1;

  }

  return 0;

}

u8 vp_taint_has_missing_owned_sites(afl_state_t *afl, struct queue_entry *q) {

  if (!afl || !q || !q->vp_ref_cnt || !q->vp_taint_done || !q->vp_taint)
    return 0;

  u16 *owned_sites = NULL;
  u32  n_owned = 0;
  collect_owned_sites(afl, q, &owned_sites, &n_owned);
  if (!n_owned) {

    ck_free(owned_sites);
    return 0;

  }

  u8 missing = 0;
  for (u32 i = 0; i < n_owned; i++) {

    u16 sid = owned_sites[i];
    u8  found = 0;
    for (vp_taint_site_t *node = q->vp_taint; node; node = node->next) {

      if (node->site_id == sid) {

        found = 1;
        break;

      }

    }

    if (!found) {

      missing = 1;
      break;

    }

  }

  ck_free(owned_sites);
  return missing;

}

/* Enumerate owned frontier sites for queue entry q by scanning the
   frontier directly. Single-pass with vp_ref_cnt-based early exit. */
static void collect_owned_sites(afl_state_t *afl, struct queue_entry *q,
                                u16 **out_sites, u32 *out_cnt) {

  if (!out_sites || !out_cnt) return;

  if (!afl || !q || !afl->vp_frontier || !q->vp_ref_cnt) {

    *out_sites = NULL;
    *out_cnt = 0;
    return;

  }

  u32    refs_left = q->vp_ref_cnt;
  size_t span = vp_taint_site_span(afl);

  /* Pre-allocate for worst case: one site per ref. */
  u16 *sites = ck_alloc(refs_left * sizeof(u16));
  u32  cnt = 0;

  for (u32 site = 0; site < CMP_MAP_W && refs_left; site++) {

    size_t base = (size_t)site * span;
    u8     found = 0;

    for (size_t rel = 0; rel < span; rel++) {

      vp_frontier_entry_t *e = &afl->vp_frontier[base + rel];
      if (e->owner == q) {

        found = 1;
        refs_left--;

      }

    }

    if (found) {

      sites[cnt] = (u16)site;
      cnt++;

    }

  }

  if (!cnt) {

    ck_free(sites);
    *out_sites = NULL;
    *out_cnt = 0;
    return;

  }

  *out_sites = sites;
  *out_cnt = cnt;

}

/* Execute buf and read the VP map to determine which owned sites fired
   and their per-exec distances.

   Reachability: checked via exec_seen == exec_id (not control[]).
   Distance:     site state is reset before execution and restored
                 afterward, so we read actual per-exec distances.

   saved_sites: caller-provided buffer of n_owned vp_site_t entries
                (avoids per-exec allocation). */
static u8 vp_taint_exec(afl_state_t *afl, u8 *buf, u32 len, u16 *owned_sites,
                        u32 n_owned, vp_taint_exec_result_t *result,
                        vp_site_t *saved_sites) {

  vp_map_t *vp = afl->shm.vp_map;

  /* Save entire vp_site_t for owned sites.  The VP hooks modify
     valid_mask, slot_key, protected_mask, touched_mask, hit_count,
     exec_seen — not just best_dist.  We must restore ALL of it to
     avoid corrupting the VP map for subsequent frontier decisions. */
  for (u32 i = 0; i < n_owned; i++) {

    saved_sites[i] = vp->site[owned_sites[i]];

    /* Reset all slots so the hooks record actual per-exec distances. */
    memset(&vp->site[owned_sites[i]].slots, 0xFF,
           sizeof(vp->site[owned_sites[i]].slots));
    vp->site[owned_sites[i]].valid_mask = 0;
    vp->site[owned_sites[i]].touched_mask = 0;
    vp->site[owned_sites[i]].protected_mask = 0;

  }

  /* Raw execution: write_to_testcase + fuzz_run_target.
     We deliberately skip common_fuzz_stuff / save_if_interesting
     because taint analysis is purely observational. */
  void *exec_mem = buf;
  u32   exec_len = write_to_testcase(afl, &exec_mem, len, 0);
  if (!exec_len) {

    for (u32 i = 0; i < n_owned; i++)
      vp->site[owned_sites[i]] = saved_sites[i];
    return 1;

  }

  fsrv_run_result_t fault =
      fuzz_run_target(afl, &afl->fsrv, afl->fsrv.exec_tmout);

  if (afl->stop_soon || fault != FSRV_RUN_OK) {

    for (u32 i = 0; i < n_owned; i++)
      vp->site[owned_sites[i]] = saved_sites[i];
    return 1;

  }

  /* Read per-exec results using exec_seen for reachability.
     We read all VP_MAX_SLOTS from the map (which always has 16 slots
     per site in the vp_site_t struct); unreset slots stay at 0xFFFF
     and are filtered by the d < 0xFFFF check. */
  u64 cur_exec_id = vp->exec_id;
  u16 active_mask = vp_taint_site_active_mask(afl);

  result->n_sites = n_owned;
  for (u32 i = 0; i < n_owned; i++) {

    u16 sid = owned_sites[i];
    result->sites[i].site_id = sid;
    result->sites[i].fired = (vp->site[sid].exec_seen == cur_exec_id);

    if (result->sites[i].fired) {

      result->sites[i].valid_mask =
          (u16)(vp->site[sid].valid_mask & active_mask);
      memcpy(result->sites[i].slots, vp->site[sid].slots,
             sizeof(result->sites[i].slots));

    } else {

      result->sites[i].valid_mask = 0;
      memset(result->sites[i].slots, 0, sizeof(result->sites[i].slots));

    }

  }

  /* Restore entire site state. */
  for (u32 i = 0; i < n_owned; i++) {

    vp->site[owned_sites[i]] = saved_sites[i];

  }

  return 0;

}

/* Insert a range into the linked list, sorted by size (largest first). */
static void range_insert_sorted(vp_taint_range_t **head, u32 start, u32 end) {

  vp_taint_range_t *r = ck_alloc(sizeof(vp_taint_range_t));
  r->start = start;
  r->end = end;
  r->next = NULL;

  u32 size = end - start + 1;

  vp_taint_range_t **pp = head;
  while (*pp) {

    u32 cur_size = (*pp)->end - (*pp)->start + 1;
    if (size >= cur_size) break;
    pp = &(*pp)->next;

  }

  r->next = *pp;
  *pp = r;

}

/* Free all ranges. */
static void range_free_all(vp_taint_range_t *head) {

  while (head) {

    vp_taint_range_t *next = head->next;
    ck_free(head);
    head = next;

  }

}

/* ---- Phase 1: binary search for neutral regions ---- */

/* Criterion: distance-based.  Randomize a byte range and check whether
   ANY owned site's VP slot state changes from baseline. If all states
   remain identical, the range is neutral (no VP-sensitive bytes).

   Returns a bitmap of non-neutral byte positions (caller must free).
   Updates *exec_cnt with the number of executions used. */
static u8 *vp_taint_phase1(afl_state_t *afl, u8 *orig_buf, u8 *changed_buf,
                           u8 *changed_buf_alt, u32 len, u16 *owned_sites,
                           vp_taint_site_status_t *baseline_sites, u32 n_owned,
                           vp_site_t *saved_sites, u32 *exec_cnt,
                           u64 start_ms) {

  u8                    *non_neutral = ck_alloc(len);
  vp_taint_exec_result_t result;
  result.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));

  /* Working buffer — start as copy of original. */
  u8 *work_buf = ck_alloc(len);
  memcpy(work_buf, orig_buf, len);

  /* Start with the full range. */
  vp_taint_range_t *ranges = NULL;
  range_insert_sorted(&ranges, 0, len - 1);

  while (ranges && !vp_taint_timed_out(start_ms)) {

    /* Pop the largest range. */
    vp_taint_range_t *r = ranges;
    u32               start = r->start;
    u32               end = r->end;
    ranges = r->next;
    ck_free(r);

    /* Apply changed bytes for this range. */
    memcpy(work_buf + start, changed_buf + start, end - start + 1);

    if (vp_taint_exec(afl, work_buf, len, owned_sites, n_owned, &result,
                      saved_sites)) {

      /* Inconclusive execution (timeout/stop/error): keep current range
         conservative and stop; caller will resume later if possible. */
      range_insert_sorted(&ranges, start, end);
      goto phase1_done;

    }

    (*exec_cnt)++;

    /* Check if any owned site's VP slot state changed from baseline.
       This is the key difference from the old reachability-based
       criterion: we detect bytes that affect VP runtime state, not
       just bytes that affect whether the comparison site is reached. */
    u8 any_changed = 0;
    for (u32 i = 0; i < n_owned; i++) {

      if (!result.sites[i].fired) {

        /* Site stopped firing — range definitely affects something. */
        any_changed = 1;
        break;

      }

      if (vp_taint_site_state_changed(afl, &baseline_sites[i],
                                      &result.sites[i])) {

        /* VP slot state changed — range contains VP-sensitive bytes. */
        any_changed = 1;
        break;

      }

    }

    /* Restore original bytes for this range. */
    memcpy(work_buf + start, orig_buf + start, end - start + 1);

    /* A second pattern check reduces accidental neutral classification
       caused by replacement collisions/cancellations. */
    if (!any_changed && !vp_taint_timed_out(start_ms)) {

      memcpy(work_buf + start, changed_buf_alt + start, end - start + 1);

      if (vp_taint_exec(afl, work_buf, len, owned_sites, n_owned, &result,
                        saved_sites)) {

        range_insert_sorted(&ranges, start, end);
        goto phase1_done;

      }

      (*exec_cnt)++;

      for (u32 i = 0; i < n_owned; i++) {

        if (!result.sites[i].fired ||
            vp_taint_site_state_changed(afl, &baseline_sites[i],
                                        &result.sites[i])) {

          any_changed = 1;
          break;

        }

      }

      memcpy(work_buf + start, orig_buf + start, end - start + 1);

    }

    if (any_changed) {

      /* Range contains non-neutral bytes. */
      u32 range_size = end - start + 1;
      if (range_size <= VP_TAINT_MIN_RANGE) {

        /* Can't split further — mark all bytes as non-neutral. */
        memset(non_neutral + start, 1, range_size);

      } else {

        /* Split in half. */
        u32 mid = start + range_size / 2;
        range_insert_sorted(&ranges, start, mid - 1);
        range_insert_sorted(&ranges, mid, end);

      }

    }

    /* If no site state changed, range is neutral — leave non_neutral as 0. */

  }

  /* Any remaining ranges that were never tested: mark as non-neutral
     to be safe. */
  vp_taint_range_t *remaining = ranges;
  while (remaining) {

    memset(non_neutral + remaining->start, 1,
           remaining->end - remaining->start + 1);
    remaining = remaining->next;

  }

phase1_done:
  range_free_all(ranges);
  ck_free(work_buf);
  ck_free(result.sites);

  return non_neutral;

}

/* ---- Phase 2: per-byte perturbation ---- */

/* For each non-neutral byte, perturb it by +1/-1 and check if VP distances
   change.  Builds per-site taint masks. */
static void vp_taint_phase2(afl_state_t *afl, u8 *orig_buf, u32 len,
                            u8 *non_neutral, u16 *owned_sites,
                            vp_taint_site_status_t *baseline_sites, u32 n_owned,
                            vp_site_t *saved_sites, u32 *sensitive_cnts,
                            u32 *sensitive_caps, u32 **sensitive_bufs,
                            u32 *phase2_order, u32 phase2_cnt,
                            u32 *phase2_next_idx, u32 *exec_cnt, u64 start_ms) {

  vp_taint_exec_result_t result;
  result.sites = ck_alloc(n_owned * sizeof(vp_taint_site_status_t));

  /* Working buffer — copy once, then flip/restore individual bytes
     to avoid a full memcpy per perturbation. */
  u8 *work_buf = ck_alloc(len);
  memcpy(work_buf, orig_buf, len);

  /* Per-site flag: already recorded byte b as sensitive on a prior attempt.
     Prevents duplicates when attempt 0 succeeds for site X but fails for
     site Y, causing attempt 1 to re-add byte b to site X. */
  u8 *site_resolved = ck_alloc(n_owned);

  for (u32 idx = *phase2_next_idx; idx < phase2_cnt; idx++) {

    if (vp_taint_timed_out(start_ms)) {

      *phase2_next_idx = idx;
      goto phase2_done;

    }

    u32 b = phase2_order[idx];
    if (b >= len || !non_neutral[b]) {

      *phase2_next_idx = idx + 1;
      continue;

    }

    u8 orig_val = orig_buf[b];
    memset(site_resolved, 0, n_owned);

    /* Try +1/-1 first; a third fallback value catches non-local effects. */
    u8 attempts[3] = {(u8)(orig_val + 1), (u8)(orig_val - 1),
                      (u8)(orig_val ^ 0xFF)};
    for (u32 attempt = 0; attempt < 3; attempt++) {

      u8 perturbed = attempts[attempt];

      /* Skip if perturbation is a no-op. */
      if (perturbed == orig_val) continue;
      if (attempt > 0 && perturbed == attempts[attempt - 1]) continue;
      if (attempt > 1 && perturbed == attempts[attempt - 2]) continue;

      if (vp_taint_timed_out(start_ms)) {

        work_buf[b] = orig_val;
        *phase2_next_idx = idx;
        goto phase2_done;

      }

      work_buf[b] = perturbed;

      if (vp_taint_exec(afl, work_buf, len, owned_sites, n_owned, &result,
                        saved_sites)) {

        work_buf[b] = orig_val;
        *phase2_next_idx = idx;
        goto phase2_done;

      }

      (*exec_cnt)++;

      /* For each owned site, check reachability and VP slot-state change. */
      u8 all_resolved = 1;
      for (u32 i = 0; i < n_owned; i++) {

        if (site_resolved[i]) continue;

        if (result.sites[i].fired &&
            vp_taint_site_state_changed(afl, &baseline_sites[i],
                                        &result.sites[i])) {

          /* VP state changed in any active slot: byte b is VP-sensitive. */
          if (sensitive_cnts[i] >= sensitive_caps[i]) {

            u32 new_cap = sensitive_caps[i] ? sensitive_caps[i] * 2 : 32;
            sensitive_bufs[i] =
                ck_realloc(sensitive_bufs[i], new_cap * sizeof(u32));
            sensitive_caps[i] = new_cap;

          }

          u32 insert_idx = sensitive_cnts[i]++;
          sensitive_bufs[i][insert_idx] = b;

          site_resolved[i] = 1;

        } else if (!result.sites[i].fired) {

          /* Site didn't fire — this perturbation broke the path.
             Try the other perturbation on next attempt. */
          all_resolved = 0;

        } else {

          /* Site fired but did not change; keep unresolved so attempt #2
             can still reveal one-sided sensitivity. */
          all_resolved = 0;

        }

      }

      /* Restore byte before next iteration. */
      work_buf[b] = orig_val;

      if (all_resolved) break;

    }

    *phase2_next_idx = idx + 1;

  }

phase2_done:
  ck_free(site_resolved);
  ck_free(work_buf);
  ck_free(result.sites);

}

static void vp_taint_build_phase2_order(afl_state_t *afl, vp_taint_resume_t *st,
                                        u32 len) {

  u32 cnt = 0;
  for (u32 i = 0; i < len; i++) {

    if (st->non_neutral[i]) cnt++;

  }

  st->phase2_cnt = cnt;
  st->phase2_next_idx = 0;
  if (!cnt) return;

  st->phase2_order = ck_alloc(cnt * sizeof(u32));
  u32 pos = 0;
  for (u32 i = 0; i < len; i++) {

    if (st->non_neutral[i]) st->phase2_order[pos++] = i;

  }

  /* Shuffle once to avoid low-offset bias under timeout-driven resume. */
  for (u32 i = cnt - 1; i > 0; i--) {

    u32 j = rand_below(afl, i + 1);
    u32 t = st->phase2_order[i];
    st->phase2_order[i] = st->phase2_order[j];
    st->phase2_order[j] = t;

  }

}

void vp_taint_resume_free(struct queue_entry *q) {

  if (!q || !q->vp_taint_resume) return;

  vp_taint_resume_t *st = q->vp_taint_resume;

  if (st->sensitive_bufs) {

    for (u32 i = 0; i < st->n_owned; i++)
      ck_free(st->sensitive_bufs[i]);

  }

  ck_free(st->sensitive_bufs);
  ck_free(st->sensitive_caps);
  ck_free(st->sensitive_cnts);
  ck_free(st->phase2_order);
  ck_free(st->non_neutral);
  ck_free(st->baseline_sites);
  ck_free(st->owned_sites);
  ck_free(st);

  q->vp_taint_resume = NULL;

}

static void vp_taint_build_list_from_resume(struct queue_entry *q) {

  vp_taint_resume_t *st = q->vp_taint_resume;
  if (!st) return;
  if (!st->owned_sites || !st->sensitive_cnts || !st->sensitive_bufs) return;

  for (u32 i = 0; i < st->n_owned; i++) {

    if (!st->sensitive_cnts[i]) {

      ck_free(st->sensitive_bufs[i]);
      st->sensitive_bufs[i] = NULL;
      continue;

    }

    vp_taint_site_t *node = ck_alloc(sizeof(vp_taint_site_t));
    node->site_id = st->owned_sites[i];
    node->sensitive_cnt = st->sensitive_cnts[i];
    node->sensitive_positions =
        ck_realloc(st->sensitive_bufs[i], st->sensitive_cnts[i] * sizeof(u32));
    st->sensitive_bufs[i] = NULL;
    node->next = q->vp_taint;
    q->vp_taint = node;

  }

}

static void vp_taint_state_filename(afl_state_t *afl, struct queue_entry *q,
                                    char *buf, size_t buf_len) {

  const char *base = strrchr((char *)q->fname, '/');
  base = base ? base + 1 : (char *)q->fname;
  snprintf(buf, buf_len, "%s/queue/.state/vp_taint/%s", afl->out_dir, base);

}

static void vp_taint_delete_state(afl_state_t *afl, struct queue_entry *q) {

  if (!afl || !q || !afl->out_dir || !q->fname) return;
  char fn[PATH_MAX];
  vp_taint_state_filename(afl, q, fn, sizeof(fn));
  unlink(fn);

}

static u8 vp_taint_read_exact(int fd, void *buf, size_t len) {

  u8 *p = (u8 *)buf;
  while (len) {

    ssize_t r = read(fd, p, len);
    if (r <= 0) return 0;
    p += (size_t)r;
    len -= (size_t)r;

  }

  return 1;

}

static u8 vp_taint_write_exact(int fd, const void *buf, size_t len) {

  const u8 *p = (const u8 *)buf;
  while (len) {

    ssize_t w = write(fd, p, len);
    if (w <= 0) return 0;
    p += (size_t)w;
    len -= (size_t)w;

  }

  return 1;

}

static void vp_taint_free_site_list(vp_taint_site_t *head) {

  while (head) {

    vp_taint_site_t *next = head->next;
    ck_free(head->sensitive_positions);
    ck_free(head);
    head = next;

  }

}

static void vp_taint_save_state(afl_state_t *afl, struct queue_entry *q) {

  if (!afl || !q || !q->vp_taint_done) return;

  char fn[PATH_MAX];
  vp_taint_state_filename(afl, q, fn, sizeof(fn));

  u32 site_cnt = 0;
  for (vp_taint_site_t *n = q->vp_taint; n; n = n->next) {

    if (n->sensitive_cnt) site_cnt++;

  }

  vp_taint_file_header_t hdr = {.magic = VP_TAINT_FILE_MAGIC,
                                .version = VP_TAINT_FILE_VERSION,
                                .len = q->len,
                                .site_cnt = site_cnt};

  int fd = open(fn, O_WRONLY | O_CREAT | O_TRUNC, afl->perm);
  if (fd < 0) return;

  u8 ok = vp_taint_write_exact(fd, &hdr, sizeof(hdr));
  for (vp_taint_site_t *n = q->vp_taint; ok && n; n = n->next) {

    if (!n->sensitive_cnt) continue;

    vp_taint_file_site_t sh = {

        .site_id = n->site_id,
        .reserved = 0,
        .sensitive_cnt = n->sensitive_cnt};
    ok = vp_taint_write_exact(fd, &sh, sizeof(sh));
    if (!ok) break;
    ok = vp_taint_write_exact(fd, n->sensitive_positions,
                              n->sensitive_cnt * sizeof(u32));

  }

  close(fd);
  if (!ok) unlink(fn);

}

void vp_taint_load_state(afl_state_t *afl, struct queue_entry *q) {

  if (!afl || !q || q->vp_taint_done || q->vp_taint || !afl->out_dir) return;
  if (afl->value_profile_level != 1) return;

  char fn[PATH_MAX];
  vp_taint_state_filename(afl, q, fn, sizeof(fn));

  int fd = open(fn, O_RDONLY);
  if (fd < 0) return;

  vp_taint_file_header_t hdr;
  if (!vp_taint_read_exact(fd, &hdr, sizeof(hdr)) ||
      hdr.magic != VP_TAINT_FILE_MAGIC ||
      hdr.version != VP_TAINT_FILE_VERSION || hdr.len != q->len) {

    close(fd);
    return;

  }

  if (hdr.site_cnt > CMP_MAP_W) {

    close(fd);
    unlink(fn);
    return;

  }

  vp_taint_site_t *loaded = NULL;
  u8               ok = 1;

  for (u32 i = 0; i < hdr.site_cnt; i++) {

    vp_taint_file_site_t sh;
    if (!vp_taint_read_exact(fd, &sh, sizeof(sh))) {

      ok = 0;
      break;

    }

    if (!sh.sensitive_cnt || sh.sensitive_cnt > q->len) {

      ok = 0;
      break;

    }

    vp_taint_site_t *node = ck_alloc(sizeof(vp_taint_site_t));
    node->site_id = sh.site_id;
    node->sensitive_cnt = sh.sensitive_cnt;
    node->sensitive_positions = ck_alloc(sh.sensitive_cnt * sizeof(u32));
    if (!vp_taint_read_exact(fd, node->sensitive_positions,
                             sh.sensitive_cnt * sizeof(u32))) {

      ck_free(node->sensitive_positions);
      ck_free(node);
      ok = 0;
      break;

    }

    for (u32 j = 0; j < sh.sensitive_cnt; j++) {

      if (node->sensitive_positions[j] >= q->len) {

        ok = 0;
        break;

      }

    }

    if (!ok) {

      ck_free(node->sensitive_positions);
      ck_free(node);
      break;

    }

    node->next = loaded;
    loaded = node;

  }

  close(fd);

  if (!ok) {

    vp_taint_free_site_list(loaded);
    unlink(fn);
    return;

  }

  q->vp_taint = loaded;
  q->vp_taint_done = 1;
  q->vp_taint_needs_refresh = 0;
  q->vp_taint_refresh_streak = 0;

}

/* ---- main entry point ---- */

void vp_taint_analyze(afl_state_t *afl, struct queue_entry *q) {

  if (!afl->value_profile_active || afl->value_profile_level != 1) return;
  if (!q->vp_ref_cnt) return;
  if (!afl->shm.vp_map) return;
  if (q->len < 2) return;

  /* One-time per-entry analysis. Once persisted, keep and reuse it
     independently of later frontier ownership churn. */
  if (q->vp_taint_done && !q->vp_taint_resume) return;

  if (!q->vp_taint_done && q->vp_taint && !q->vp_taint_resume) {

    vp_taint_free(q);
    vp_taint_delete_state(afl, q);

  }

  u64 start_ms = get_cur_time();
  u8 *orig_buf = queue_testcase_get(afl, q);
  if (!orig_buf) return;

  if (!q->vp_taint_resume) {

    /* First run for this entry: collect baseline and build phase-2 plan. */
    vp_taint_resume_t *st = ck_alloc(sizeof(vp_taint_resume_t));
    q->vp_taint_resume = st;

    collect_owned_sites(afl, q, &st->owned_sites, &st->n_owned);
    if (!st->n_owned) {

      vp_taint_resume_free(q);
      return;

    }

    vp_site_t *saved_sites = ck_alloc(st->n_owned * sizeof(vp_site_t));
    vp_taint_exec_result_t baseline_result;
    baseline_result.sites =
        ck_alloc(st->n_owned * sizeof(vp_taint_site_status_t));

    if (vp_taint_exec(afl, orig_buf, q->len, st->owned_sites, st->n_owned,
                      &baseline_result, saved_sites)) {

      ck_free(baseline_result.sites);
      ck_free(saved_sites);
      /* Baseline replay failed (timeout/error/stop). Drop partial state so the
         next visit starts from a clean analysis state instead of dereferencing
         uninitialized resume buffers. */
      vp_taint_resume_free(q);
      return;

    }

    u32 kept = 0;
    for (u32 i = 0; i < st->n_owned; i++) {

      if (baseline_result.sites[i].fired &&
          baseline_result.sites[i].valid_mask) {

        if (kept != i) {

          st->owned_sites[kept] = st->owned_sites[i];
          baseline_result.sites[kept] = baseline_result.sites[i];

        }

        kept++;

      }

    }

    st->n_owned = kept;
    if (!st->n_owned) {

      ck_free(baseline_result.sites);
      ck_free(saved_sites);
      goto finalize_resume;

    }

    st->baseline_sites = ck_alloc(st->n_owned * sizeof(vp_taint_site_status_t));
    memcpy(st->baseline_sites, baseline_result.sites,
           st->n_owned * sizeof(vp_taint_site_status_t));

    u8 *changed_buf = ck_alloc(q->len);
    u8 *changed_alt = ck_alloc(q->len);
    memcpy(changed_buf, orig_buf, q->len);
    memcpy(changed_alt, orig_buf, q->len);
    random_replace_vp(afl, changed_buf, q->len);

    for (u32 i = 0; i < q->len; i++) {

      changed_alt[i] ^= 0xFF;
      if (changed_alt[i] == orig_buf[i]) changed_alt[i] ^= 0xA5;

    }

    st->non_neutral = vp_taint_phase1(
        afl, orig_buf, changed_buf, changed_alt, q->len, st->owned_sites,
        st->baseline_sites, st->n_owned, saved_sites, &st->exec_cnt, start_ms);

    st->sensitive_cnts = ck_alloc(st->n_owned * sizeof(u32));
    st->sensitive_caps = ck_alloc(st->n_owned * sizeof(u32));
    st->sensitive_bufs = ck_alloc(st->n_owned * sizeof(u32 *));

    vp_taint_build_phase2_order(afl, st, q->len);

    ck_free(changed_alt);
    ck_free(changed_buf);
    ck_free(baseline_result.sites);
    ck_free(saved_sites);

  }

  if (vp_taint_timed_out(start_ms)) { return; }

  if (q->vp_taint_resume && q->vp_taint_resume->n_owned &&
      q->vp_taint_resume->phase2_next_idx < q->vp_taint_resume->phase2_cnt) {

    vp_taint_resume_t *st = q->vp_taint_resume;
    vp_site_t         *saved_sites = ck_alloc(st->n_owned * sizeof(vp_site_t));

    vp_taint_phase2(afl, orig_buf, q->len, st->non_neutral, st->owned_sites,
                    st->baseline_sites, st->n_owned, saved_sites,
                    st->sensitive_cnts, st->sensitive_caps, st->sensitive_bufs,
                    st->phase2_order, st->phase2_cnt, &st->phase2_next_idx,
                    &st->exec_cnt, start_ms);

    ck_free(saved_sites);

    if (st->phase2_next_idx < st->phase2_cnt) { return; }

  }

finalize_resume:
  if (q->vp_taint_resume) {

    vp_taint_build_list_from_resume(q);
    vp_taint_resume_free(q);

  }

  q->vp_taint_done = 1;
  q->vp_taint_needs_refresh = 0;
  q->vp_taint_refresh_streak = 0;

  vp_taint_save_state(afl, q);

}

/* ---- biased position selection ---- */

u32 vp_taint_rand_pos(afl_state_t *afl, vp_taint_site_t *site, u32 max_pos) {

  if (!max_pos) return 0;

  if (!site || !site->sensitive_cnt) { return rand_below(afl, max_pos); }

  /* Skip bias when taint is too broad to be useful. */
  if (site->sensitive_cnt >= (max_pos * 3) / 4) {

    return rand_below(afl, max_pos);

  }

  /* With VP_TAINT_BIAS% probability, pick from sensitive positions. */
  if (rand_below(afl, 100) < VP_TAINT_BIAS) {

    u32 idx = rand_below(afl, site->sensitive_cnt);
    u32 pos = site->sensitive_positions[idx];

    if (pos < max_pos) { return pos; }

  }

  return rand_below(afl, max_pos);

}

/* ---- cleanup ---- */

void vp_taint_free(struct queue_entry *q) {

  if (!q || !q->vp_taint) {

    if (q) {

      q->vp_taint = NULL;
      q->vp_taint_done = 0;
      q->vp_taint_needs_refresh = 0;
      q->vp_taint_refresh_streak = 0;
      q->vp_taint_refresh_cooldown = 0;

    }

    return;

  }

  vp_taint_site_t *node = q->vp_taint;
  while (node) {

    vp_taint_site_t *next = node->next;
    ck_free(node->sensitive_positions);
    ck_free(node);
    node = next;

  }

  q->vp_taint = NULL;
  q->vp_taint_done = 0;
  q->vp_taint_needs_refresh = 0;
  q->vp_taint_refresh_streak = 0;
  q->vp_taint_refresh_cooldown = 0;

}

