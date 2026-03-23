/*
   american fuzzy lop++ - value profiling
   --------------------------------------

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

   Value profiling provides an additional gradient signal by tracking
   how close comparison operands are to matching. It considers inputs
   that bring operands closer as "interesting".

 */

#include "afl-fuzz.h"
#include "cmplog.h"
#include "bitops.h"
#include "value-profile.h"
#include <assert.h>

/* CmpLog marks string-like routine compares as 0x80 + len.
   stop_at_zero is deliberately not reset between the two operand-length
   decodes. Once either operand is 0x80-tagged, the compare uses
   stop-at-NUL semantics for VP processing. */
static inline u32 decode_rtn_len(u8 raw_len, u8 *stop_at_zero) {

  if (raw_len >= 0x80) {

    *stop_at_zero = 1;
    return (u32)(raw_len - 0x80);

  }

  return (u32)raw_len;

}

/* Parse one RTN compare entry: decode operand lengths, then walk the
   two buffers to find how many leading bytes match (prefix_len) out of
   the shorter operand length (max_len).  Returns 1 if the compare is
   solved (full-length equality, or NUL-terminated equality for
   string-like compares). */
static inline u8 analyze_rtn_compare(const struct cmpfn_operands *rtn,
                                     u32 *max_len_out, u32 *prefix_len_out) {

  u8  stop_at_zero = 0;
  u32 len0 = decode_rtn_len(rtn->v0_len, &stop_at_zero);
  u32 len1 = decode_rtn_len(rtn->v1_len, &stop_at_zero);
  u32 max_len = MIN(len0, len1);
  if (!max_len || max_len > 32) max_len = 32;

  u32 prefix_len = 0;
  while (prefix_len < max_len && rtn->v0[prefix_len] == rtn->v1[prefix_len]) {

    if (stop_at_zero && rtn->v0[prefix_len] == 0) {

      *max_len_out = max_len;
      *prefix_len_out = prefix_len;
      return 1;

    }

    prefix_len++;

  }

  *max_len_out = max_len;
  *prefix_len_out = prefix_len;
  return (prefix_len == max_len);

}

/* True absolute distance bucket for 128-bit values represented as hi:lo words.
   Returns 0 for equal values, otherwise 1..128. */
static inline u32 compute_abs_dist_bucket_128(u64 v0_lo, u64 v0_hi, u64 v1_lo,
                                              u64 v1_hi) {

  if (v0_lo == v1_lo && v0_hi == v1_hi) return 0;

  u64 d_lo, d_hi;
  if (v0_hi > v1_hi || (v0_hi == v1_hi && v0_lo >= v1_lo)) {

    d_lo = v0_lo - v1_lo;
    d_hi = v0_hi - v1_hi - (v0_lo < v1_lo);

  } else {

    d_lo = v1_lo - v0_lo;
    d_hi = v1_hi - v0_hi - (v1_lo < v0_lo);

  }

  if (d_hi) return 64 + bit_length_u64(d_hi);
  return bit_length_u64(d_lo);

}

/* Load and mask instruction compare operands according to compare width.
   shape is in bytes (already decoded via SHAPE_BYTES). */
static inline void load_ins_operands(const struct cmp_operands *op, u32 shape,
                                     u64 *v0_lo, u64 *v0_hi, u64 *v1_lo,
                                     u64 *v1_hi) {

  if (shape > 16) shape = 16;   /* cmp_operands stores up to 128-bit values */

  *v0_lo = op->v0;
  *v1_lo = op->v1;
  *v0_hi = 0;
  *v1_hi = 0;

  if (shape < 8) {

    u64 mask = (1ULL << (shape * 8)) - 1;
    *v0_lo &= mask;
    *v1_lo &= mask;
    return;

  }

  if (shape > 8) {

    *v0_hi = op->v0_128;
    *v1_hi = op->v1_128;

    if (shape < 16) {

      u32 hi_bits = (shape - 8) * 8;
      u64 hi_mask = (1ULL << hi_bits) - 1;
      *v0_hi &= hi_mask;
      *v1_hi &= hi_mask;

    }

  }

}

/* Absolute distance bucket for scalar (<=8-byte) compares.
   Returns 0 for equal values, otherwise clzll(diff) + 1. */
static inline u32 compute_abs_dist_bucket(u64 v0, u64 v1, u32 shape) {

  if (v0 == v1) return 0;

  /* Only 4-byte compares need explicit width wrapping.
     For 1/2-byte compares, integer promotion before subtraction already gives
     the intended result once operands are width-masked.
     8-byte compares naturally use full-width subtraction.
     For 4-byte compares, force uint32_t wrap first so upper 32 bits do not
     pollute the clzll result. */
  if (shape == 4) {

    u32 diff32 = (u32)v0 - (u32)v1;
    return (u32)__builtin_clzll((u64)diff32) + 1;

  }

  return (u32)__builtin_clzll(v0 - v1) + 1;

}

typedef enum {

  VP_DIST_WRAPPED = 0,
  VP_DIST_EXACT = 1,

} vp_scalar_dist_mode_t;

/* True absolute distance bucket for scalar (<=8-byte) compares.
   Returns 0 for equal values, otherwise 1..64. */
static inline u32 compute_abs_dist_exact(u64 v0, u64 v1) {

  u64 diff = (v0 > v1) ? (v0 - v1) : (v1 - v0);
  return diff ? (64 - (u32)__builtin_clzll(diff)) : 0;

}

/* Compute INS compare metrics used by VP feature extraction and ranking.
   Returns 0 when operands are equal (solved compare), otherwise 1 and writes:
     - hamming_out: bit hamming distance
     - abs_dist_out: scalar absolute-distance metric selected by scalar_mode,
                     or full 128-bit absolute distance for wide compares. */
static inline u8 compute_ins_metrics(const struct cmp_operands *op, u32 shape,
                                     vp_scalar_dist_mode_t scalar_mode,
                                     u32 *hamming_out, u32 *abs_dist_out) {

  u64 v0_lo, v0_hi, v1_lo, v1_hi;
  load_ins_operands(op, shape, &v0_lo, &v0_hi, &v1_lo, &v1_hi);

  /* A single CMP site can be hit multiple times per execution with different
     operands (e.g. a loop comparing input[i] == key[i] — hit 0 may be solved
     while hit 3 is not).  Skip solved hits; other hits at the same site may
     still be unsolved and need VP tracking. */
  if (v0_lo == v1_lo && v0_hi == v1_hi) return 0;

  if (shape > 8) {

    /* Wide compares always use full 128-bit resolution. */
    *hamming_out = popcount_u64(v0_lo ^ v1_lo) + popcount_u64(v0_hi ^ v1_hi);
    *abs_dist_out = compute_abs_dist_bucket_128(v0_lo, v0_hi, v1_lo, v1_hi);

  } else {

    *hamming_out = popcount_u64(v0_lo ^ v1_lo);
    *abs_dist_out = (scalar_mode == VP_DIST_WRAPPED)
                        ? compute_abs_dist_bucket(v0_lo, v1_lo, shape)
                        : compute_abs_dist_exact(v0_lo, v1_lo);

  }

  return 1;

}

/* Prepare per-execution runtime VP state before running the main target. */
void vp_prepare_exec(afl_state_t *afl, afl_forkserver_t *fsrv) {

  if (!afl->value_profile_mode) return;
  if (fsrv != &afl->fsrv) return;

  if (unlikely(!fsrv->use_value_profile)) {

    FATAL(
        "Value profiling requires target support for value profile runtime "
        "SHM. Recompile the target with "
        "AFL_LLVM_VALUE_PROFILE=1 (or AFL_LLVM_VALUEPROFILE=1).");

  }

  if (unlikely(!afl->shm.vp_map)) {

    FATAL(
        "Value profile runtime map missing although value profiling was "
        "selected.");

  }

  vp_map_t *vp = afl->shm.vp_map;
  vp->enabled = afl->value_profile_active ? 1U : 0U;
  if (!vp->enabled) return;

  ++vp->exec_id;
  if (unlikely(!vp->exec_id)) { ++vp->exec_id; }
  vp->control_len = 0;

}

void vp_runtime_set_site_filter(afl_state_t *afl, const u16 *site_ids,
                                u32 site_cnt) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (unlikely(!vp)) return;

  memset(vp->filter_bitmap, 0, sizeof(vp->filter_bitmap));
  for (u32 i = 0; i < site_cnt; ++i) {

    u16 site_id = site_ids[i];
    vp->filter_bitmap[site_id >> 6] |= (1ULL << (site_id & 63));

  }

  vp->filter_enabled = site_cnt ? 1U : 0U;

}

void vp_runtime_clear_site_filter(afl_state_t *afl) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (unlikely(!vp)) return;

  vp->filter_enabled = 0;
  memset(vp->filter_bitmap, 0, sizeof(vp->filter_bitmap));

}

u8 vp_runtime_observe_begin(afl_state_t *afl, const u16 *site_ids, u32 site_cnt,
                            vp_site_t                *saved_sites,
                            vp_runtime_observe_mode_t mode) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (unlikely(!vp || !vp->enabled || !site_ids || !site_cnt || !saved_sites))
    return 0;

  for (u32 i = 0; i < site_cnt; ++i) {

    u16 site_id = site_ids[i];
    saved_sites[i] = vp->site[site_id];

    switch (mode) {

      case VP_RUNTIME_OBSERVE_TAINT:
        memset(&vp->site[site_id].slots, 0xFF, sizeof(vp->site[site_id].slots));
        vp->site[site_id].valid_mask = 0;
        vp->site[site_id].touched_mask = 0;
        vp->site[site_id].protected_mask = 0;
        break;

      case VP_RUNTIME_OBSERVE_TRIM:
        memset(&vp->site[site_id], 0, sizeof(vp_site_t));
        vp->site[site_id].exec_seen = vp->exec_id;
        break;

      default:
        while (i--) {

          vp->site[site_ids[i]] = saved_sites[i];

        }

        return 0;

    }

  }

  vp_runtime_set_site_filter(afl, site_ids, site_cnt);
  return 1;

}

void vp_runtime_observe_end(afl_state_t *afl, const u16 *site_ids, u32 site_cnt,
                            const vp_site_t *saved_sites) {

  vp_map_t *vp = afl ? afl->shm.vp_map : NULL;
  if (unlikely(!vp || !site_ids || !site_cnt || !saved_sites)) return;

  for (u32 i = 0; i < site_cnt; ++i) {

    vp->site[site_ids[i]] = saved_sites[i];

  }

  vp_runtime_clear_site_filter(afl);

}

typedef struct {

  vp_map_t *vp;
  u32       control_len;
  u32       pos;

} vp_runtime_site_iter_t;

/* Iterate runtime VP sites listed in control[].
   Runtime SHM is producer-owned by target hooks, so debug builds assert
   index bounds while release builds keep the hot path branch-free. */
static inline void vp_runtime_site_iter_init(vp_runtime_site_iter_t *it,
                                             vp_map_t               *vp) {

  assert(vp);
  it->vp = vp;
  it->control_len = MIN(vp->control_len, (u32)VP_CONTROL_CAP);
  it->pos = 0;

}

static inline u8 vp_runtime_site_iter_next(vp_runtime_site_iter_t *it,
                                           u32 *site, vp_site_t **site_state) {

  if (it->pos >= it->control_len) return 0;

  u32 k = it->vp->control[it->pos++];
  assert(k < CMP_MAP_W);
  *site = k;
  if (site_state) *site_state = &it->vp->site[k];
  return 1;

}

/* Mask runtime slot updates to valid+touched+active for this site. */
static inline u16 vp_runtime_site_changed_mask(const vp_site_t *site,
                                               u16              active_mask) {

  return (u16)(site->touched_mask & site->valid_mask & active_mask);

}

/* First frontier slot index for a compare site. */
static inline u32 vp_frontier_slot_replicas(afl_state_t *afl) {

  (void)afl;
  return VP_RUNTIME_SLOT_REPLICA_LIMIT;

}

static inline size_t vp_frontier_site_span(afl_state_t *afl) {

  return (size_t)afl->value_profile_slots * vp_frontier_slot_replicas(afl);

}

static inline size_t vp_site_base(afl_state_t *afl, u32 site) {

  return (size_t)site * vp_frontier_site_span(afl);

}

static inline size_t vp_runtime_slot_base(afl_state_t *afl, u32 site,
                                          u16 slot_rel) {

  return vp_site_base(afl, site) +
         (size_t)slot_rel * VP_RUNTIME_SLOT_REPLICA_LIMIT;

}

static inline u8 vp_runtime_frontier_entry_is_favor_candidate(
    const vp_frontier_entry_t *entry) {

  struct queue_entry *q = entry->owner;
  return q && !q->disabled && entry->dist && entry->dist < VP_DIST_UNSOLVED;

}

static inline void vp_runtime_slot_mask_recompute(afl_state_t *afl, u32 site,
                                                  u16 slot_rel) {

  if (unlikely(!afl->vp_runtime_slot_mask)) return;

  u8 has_favor_candidate = 0;
  for (u16 replica = 0; replica < VP_RUNTIME_SLOT_REPLICA_LIMIT; ++replica) {

    size_t idx = vp_runtime_slot_base(afl, site, slot_rel) + replica;
    if (vp_runtime_frontier_entry_is_favor_candidate(&afl->vp_frontier[idx])) {

      has_favor_candidate = 1;
      break;

    }

  }

  u16 bit = (u16)(1U << slot_rel);
  if (has_favor_candidate) {

    afl->vp_runtime_slot_mask[site] |= bit;

  } else {

    afl->vp_runtime_slot_mask[site] &= (u16)~bit;

  }

}

/* Cost tie-breaker used for equal-distance frontier candidates. */
static inline u64 vp_entry_cost(const struct queue_entry *q) {

  return (u64)q->exec_us * (u64)q->len;

}

/* Frontier ordering: lower distance wins; for ties, lower cost wins. */
static inline u8 vp_is_better(u32 cand_dist, u64 cand_cost, u32 old_dist,
                              u64 old_cost) {

  if (old_dist >= VP_DIST_UNSOLVED) return 1;
  if (cand_dist < old_dist) return 1;
  if (cand_dist == old_dist && cand_cost < old_cost) return 1;
  return 0;

}

static inline void vp_owned_site_add(struct queue_entry *q, u16 site_id) {

  if (!q) return;

  u8  found = 0;
  u32 pos = vp_sorted_u16_lower_bound(q->vp_owned_sites, q->vp_owned_site_cnt,
                                      site_id, &found);
  if (found) return;

  if (q->vp_owned_site_cnt == q->vp_owned_site_cap) {

    u32 new_cap = q->vp_owned_site_cap ? q->vp_owned_site_cap << 1 : 4;
    q->vp_owned_sites =
        ck_realloc(q->vp_owned_sites, new_cap * sizeof(*q->vp_owned_sites));
    q->vp_owned_site_cap = new_cap;

  }

  if (pos < q->vp_owned_site_cnt) {

    memmove(&q->vp_owned_sites[pos + 1], &q->vp_owned_sites[pos],
            (q->vp_owned_site_cnt - pos) * sizeof(*q->vp_owned_sites));

  }

  q->vp_owned_sites[pos] = site_id;
  ++q->vp_owned_site_cnt;
  vp_taint_note_owned_sites_changed(q);

}

static inline void vp_owned_site_remove(struct queue_entry *q, u16 site_id) {

  if (!q || !q->vp_owned_site_cnt) return;

  u8  found = 0;
  u32 pos = vp_sorted_u16_lower_bound(q->vp_owned_sites, q->vp_owned_site_cnt,
                                      site_id, &found);
  if (!found) return;

  if (pos + 1 < q->vp_owned_site_cnt) {

    memmove(&q->vp_owned_sites[pos], &q->vp_owned_sites[pos + 1],
            (q->vp_owned_site_cnt - pos - 1) * sizeof(*q->vp_owned_sites));

  }

  --q->vp_owned_site_cnt;
  vp_taint_note_owned_sites_changed(q);

}

static inline u8 vp_site_owned_elsewhere(afl_state_t *afl, u16 site_id,
                                         const struct queue_entry *q,
                                         size_t                    skip_idx) {

  if (!afl || !q || !afl->vp_frontier) return 0;

  size_t base = vp_site_base(afl, site_id);
  size_t span = vp_frontier_site_span(afl);
  for (size_t rel = 0; rel < span; ++rel) {

    size_t idx = base + rel;
    if (idx == skip_idx) continue;
    if (afl->vp_frontier[idx].owner == q) return 1;

  }

  return 0;

}

/* Disable stale VP-only entries once they are no longer referenced by any
   frontier slot and have survived at least one queue cycle. */
static inline void vp_maybe_disable_entry(afl_state_t        *afl,
                                          struct queue_entry *q) {

  if (!q || q->disabled || !q->vp_only || q->has_new_cov || q->vp_ref_cnt)
    return;
  if (!q->vp_last_ref_cycle || afl->queue_cycle <= q->vp_last_ref_cycle) return;

  q->disabled = 1;
  q->perf_score = 0;
  if (afl->active_items) { --afl->active_items; }
  if (!q->was_fuzzed && afl->pending_not_fuzzed) { --afl->pending_not_fuzzed; }
  q->was_fuzzed = 1;
  afl->score_changed = 1;
  afl->reinit_table = 1;

}

/* Drop one frontier reference from q and trigger delayed disable logic when
   refcount reaches zero. */
static inline void vp_dec_ref(afl_state_t *afl, struct queue_entry *q) {

  if (!q || !q->vp_ref_cnt) return;
  --q->vp_ref_cnt;
  if (!q->vp_ref_cnt) {

    if (q->vp_trim_deferred) {

      q->trim_done = 0;
      q->vp_trim_deferred = 0;

    }

    q->vp_last_ref_cycle = afl->queue_cycle;
    vp_maybe_disable_entry(afl, q);

  }

}

/* Increment frontier reference count for q. */
static inline void vp_inc_ref(struct queue_entry *q) {

  if (!q) return;
  ++q->vp_ref_cnt;

}

/* Reset one frontier slot to the empty sentinel state. */
static inline void vp_clear_slot(afl_state_t *afl, size_t idx) {

  size_t              site_span = vp_frontier_site_span(afl);
  u16                 site_id = (u16)(idx / site_span);
  struct queue_entry *old = afl->vp_frontier[idx].owner;
  if (old) {

    if (!vp_site_owned_elsewhere(afl, site_id, old, idx)) {

      vp_owned_site_remove(old, site_id);

    }

    vp_dec_ref(afl, old);

  }

  afl->vp_frontier[idx].owner = NULL;
  afl->vp_frontier[idx].dist = VP_DIST_UNSOLVED;
  afl->vp_frontier[idx].tag = 0;
  afl->vp_frontier[idx].cost = ~(u64)0;
  afl->vp_frontier[idx].is_protected = 0;

  if (afl->vp_runtime_slot_mask) {

    u32 site = (u32)(idx / site_span);
    u16 slot_rel = (u16)(((idx % site_span) / VP_RUNTIME_SLOT_REPLICA_LIMIT));
    vp_runtime_slot_mask_recompute(afl, site, slot_rel);

  }

}

/* Recompute top_rated_vp/site distance from all active slots of one site. */
static inline void vp_refresh_site_winner(afl_state_t *afl, u32 site) {

  size_t              base = vp_site_base(afl, site);
  size_t              span = vp_frontier_site_span(afl);
  struct queue_entry *best_q = NULL;
  u32                 best_dist = VP_DIST_UNSOLVED;
  u64                 best_cost = ~(u64)0;

  for (size_t i = 0; i < span; ++i) {

    size_t              idx = base + i;
    struct queue_entry *owner = afl->vp_frontier[idx].owner;
    u32                 dist = afl->vp_frontier[idx].dist;
    if (!owner || owner->disabled || dist >= VP_DIST_UNSOLVED) {

      if (owner && owner->disabled) vp_clear_slot(afl, idx);
      continue;

    }

    u64 cost = afl->vp_frontier[idx].cost;
    if (!best_q || dist < best_dist ||
        (dist == best_dist && cost < best_cost)) {

      best_q = owner;
      best_dist = dist;
      best_cost = cost;

    }

  }

  if (!best_q) {

    if (afl->top_rated_vp[site] ||
        afl->top_rated_vp_dist[site] != VP_DIST_UNSOLVED) {

      afl->top_rated_vp[site] = NULL;
      afl->top_rated_vp_dist[site] = VP_DIST_UNSOLVED;
      afl->score_changed = 1;

    }

    return;

  }

  if (afl->top_rated_vp[site] != best_q ||
      afl->top_rated_vp_dist[site] != best_dist) {

    afl->top_rated_vp[site] = best_q;
    afl->top_rated_vp_dist[site] = best_dist;
    afl->score_changed = 1;

  }

}

/* Re-scan is only needed on content change, or when cached winner became
   stale due to delayed disable. */
static inline u8 vp_site_refresh_needed(afl_state_t *afl, u32 site,
                                        u8 site_changed) {

  return site_changed ||
         (afl->top_rated_vp[site] && afl->top_rated_vp[site]->disabled);

}

typedef struct {

  u16 slot_rel;
  u16 tag;
  u32 dist;
  u8  is_protected;

} vp_site_candidate_t;

static inline u8 vp_runtime_entry_precedes(u32 cand_dist, u64 cand_cost,
                                           u8 cand_is_protected, u32 old_dist,
                                           u64 old_cost, u8 old_is_protected);

/* Frontier slot validity check shared by scan paths. */
static inline u8 vp_frontier_slot_is_empty(const struct queue_entry *owner,
                                           u32                       dist) {

  return !owner || owner->disabled || dist >= VP_DIST_UNSOLVED;

}

/* Active runtime-slot mask for configured slot count (1..16). */
static inline u16 vp_active_slot_mask(u16 max_slot_count) {

  return (u16)((1U << max_slot_count) - 1U);

}

/* Collect runtime-slot (tag,dist) candidates for one site from changed bits. */
static inline u32 vp_collect_runtime_site_candidates(const vp_site_t *site,
                                                     u16 active_mask,
                                                     vp_site_candidate_t *out,
                                                     u32                  cap) {

  u32 n = 0;
  u16 changed = vp_runtime_site_changed_mask(site, active_mask);

  for (u16 bits = changed; bits && n < cap; bits = (u16)(bits & (bits - 1U))) {

    u16 i = (u16)__builtin_ctz((u32)bits);
    u16 dist = site->slots[i].best_dist;
    if (!dist) continue;

    out[n].slot_rel = i;
    out[n].tag = site->slots[i].slot_key;
    out[n].dist = dist;
    out[n].is_protected = (u8)((site->protected_mask >> i) & 1U);
    ++n;

  }

  return n;

}

void vp_mark_favored_runtime_slots(afl_state_t *afl) {

  if (!afl->vp_frontier || !afl->value_profile_active) return;

  u16 slot_cfg_mask = afl->value_profile_slots == 16
                          ? 0xffffU
                          : (u16)((1U << afl->value_profile_slots) - 1U);

  for (u32 site = 0; site < CMP_MAP_W; ++site) {

    u16 slot_mask = afl->vp_runtime_slot_mask ? afl->vp_runtime_slot_mask[site]
                                              : slot_cfg_mask;
    slot_mask &= slot_cfg_mask;

    for (u16 bits = slot_mask; bits; bits = (u16)(bits & (bits - 1U))) {

      u16    slot_rel = (u16)__builtin_ctz((u32)bits);
      u16    slot_bit = (u16)(1U << slot_rel);
      u8     has_favor_candidate = 0;
      size_t slot_base = vp_runtime_slot_base(afl, site, slot_rel);

      u8 used = 0;
      for (u16 pick = 0; pick < VP_RUNTIME_SLOT_FAVOR_LIMIT; ++pick) {

        size_t best_idx = SIZE_MAX;
        for (u16 replica = 0; replica < VP_RUNTIME_SLOT_REPLICA_LIMIT;
             ++replica) {

          if (used & (1U << replica)) continue;

          size_t               idx = slot_base + replica;
          vp_frontier_entry_t *entry = &afl->vp_frontier[idx];
          struct queue_entry  *q = entry->owner;
          if (!q || q->disabled || entry->dist == 0 ||
              entry->dist >= VP_DIST_UNSOLVED)
            continue;

          has_favor_candidate = 1;

          if (best_idx == SIZE_MAX ||
              vp_runtime_entry_precedes(
                  entry->dist, entry->cost, entry->is_protected,
                  afl->vp_frontier[best_idx].dist,
                  afl->vp_frontier[best_idx].cost,
                  afl->vp_frontier[best_idx].is_protected)) {

            best_idx = idx;

          }

        }

        if (best_idx == SIZE_MAX) break;
        used |= 1U << (u16)(best_idx - slot_base);

        struct queue_entry *q = afl->vp_frontier[best_idx].owner;
        if (!q || q->disabled || q->favored) continue;

        q->favored = 1;
        ++afl->queued_favored;

        if (!q->was_fuzzed) {

          ++afl->pending_favored;
          if (unlikely(afl->smallest_favored < 0 ||
                       afl->smallest_favored > (s64)q->id)) {

            afl->smallest_favored = (s64)q->id;

          }

        }

      }

      if (afl->vp_runtime_slot_mask && !has_favor_candidate) {

        /* Self-heal stale bits when owners were disabled outside VP paths. */
        afl->vp_runtime_slot_mask[site] &= (u16)~slot_bit;

      }

    }

  }

}

typedef struct {

  size_t base;                   /* First frontier index for this site      */
  u32    site;                   /* Compare site index                      */
  u16    slots;                  /* Active slots for this run (1..16)       */
  s32    first_empty_rel;        /* First empty slot (relative), else -1    */
  s32    worst_rel;              /* Worst resident slot (relative), else -1 */
  u32    worst_dist;             /* Distance of worst_rel                   */
  u64    worst_cost;             /* Cost tie-break value of worst_rel       */

} vp_frontier_site_ctx_t;

static inline size_t vp_frontier_site_abs_idx(const vp_frontier_site_ctx_t *ctx,
                                              u16 rel_idx) {

  return ctx->base + (size_t)rel_idx;

}

typedef struct {

  size_t base;                 /* First replica index for this runtime slot */
  u32    site;                 /* Compare site index                        */
  u16    slot_rel;             /* Runtime slot index within site            */
  u16    replicas;             /* Replica count per runtime slot            */
  s32    first_empty_rel;      /* First empty replica, else -1              */
  s32    worst_rel;            /* Worst retained replica, else -1           */
  u32    worst_dist;           /* Distance of worst_rel                     */
  u64    worst_cost;           /* Cost of worst_rel                         */
  u8     worst_is_protected;   /* Protected status of worst_rel             */

} vp_frontier_runtime_slot_ctx_t;

static inline size_t vp_frontier_runtime_slot_abs_idx(
    const vp_frontier_runtime_slot_ctx_t *ctx, u16 rel_idx) {

  return ctx->base + (size_t)rel_idx;

}

static inline u8 vp_runtime_entry_precedes(u32 cand_dist, u64 cand_cost,
                                           u8 cand_is_protected, u32 old_dist,
                                           u64 old_cost, u8 old_is_protected) {

  if (cand_dist < old_dist) return 1;
  if (cand_dist > old_dist) return 0;
  if (cand_cost < old_cost) return 1;
  if (cand_cost > old_cost) return 0;
  return cand_is_protected && !old_is_protected;

}

static inline void vp_frontier_runtime_slot_ctx_recompute(
    afl_state_t *afl, vp_frontier_runtime_slot_ctx_t *ctx) {

  ctx->first_empty_rel = -1;
  ctx->worst_rel = -1;
  ctx->worst_dist = 0;
  ctx->worst_cost = 0;
  ctx->worst_is_protected = 0;
  u8 has_favor_candidate = 0;

  for (u16 rel_idx = 0; rel_idx < ctx->replicas; ++rel_idx) {

    size_t               idx = vp_frontier_runtime_slot_abs_idx(ctx, rel_idx);
    vp_frontier_entry_t *entry = &afl->vp_frontier[idx];
    struct queue_entry  *owner = entry->owner;
    u32                  dist = entry->dist;

    if (vp_frontier_slot_is_empty(owner, dist)) {

      if (ctx->first_empty_rel < 0) ctx->first_empty_rel = (s32)rel_idx;
      continue;

    }

    if (dist != 0) { has_favor_candidate = 1; }

    if (ctx->worst_rel < 0 ||
        vp_runtime_entry_precedes(ctx->worst_dist, ctx->worst_cost,
                                  ctx->worst_is_protected, dist, entry->cost,
                                  entry->is_protected)) {

      ctx->worst_rel = (s32)rel_idx;
      ctx->worst_dist = dist;
      ctx->worst_cost = entry->cost;
      ctx->worst_is_protected = entry->is_protected;

    }

  }

  if (afl->vp_runtime_slot_mask) {

    u16 bit = (u16)(1U << ctx->slot_rel);
    if (has_favor_candidate) {

      afl->vp_runtime_slot_mask[ctx->site] |= bit;

    } else {

      afl->vp_runtime_slot_mask[ctx->site] &= (u16)~bit;

    }

  }

}

static inline void vp_frontier_runtime_slot_ctx_init(
    afl_state_t *afl, u32 site, u16 slot_rel, u8 clear_stale,
    vp_frontier_runtime_slot_ctx_t *ctx) {

  ctx->base = vp_runtime_slot_base(afl, site, slot_rel);
  ctx->site = site;
  ctx->slot_rel = slot_rel;
  ctx->replicas = VP_RUNTIME_SLOT_REPLICA_LIMIT;

  if (clear_stale) {

    for (u16 rel_idx = 0; rel_idx < ctx->replicas; ++rel_idx) {

      size_t              idx = vp_frontier_runtime_slot_abs_idx(ctx, rel_idx);
      struct queue_entry *owner = afl->vp_frontier[idx].owner;
      if (owner && owner->disabled) { vp_clear_slot(afl, idx); }

    }

  }

  vp_frontier_runtime_slot_ctx_recompute(afl, ctx);

}

static inline s32 vp_frontier_runtime_slot_find_owner(
    afl_state_t *afl, vp_frontier_runtime_slot_ctx_t *ctx,
    const struct queue_entry *q) {

  for (u16 rel_idx = 0; rel_idx < ctx->replicas; ++rel_idx) {

    size_t idx = vp_frontier_runtime_slot_abs_idx(ctx, rel_idx);
    if (afl->vp_frontier[idx].owner == q &&
        afl->vp_frontier[idx].dist < VP_DIST_UNSOLVED)
      return (s32)rel_idx;

  }

  return -1;

}

static inline u8 vp_frontier_runtime_slot_would_improve_ctx(
    vp_frontier_runtime_slot_ctx_t *ctx, u32 dist, u8 is_protected) {

  if (!dist || dist >= VP_DIST_UNSOLVED) return 0;
  if (ctx->first_empty_rel >= 0) return 1;

  assert(ctx->worst_rel >= 0);
  return vp_runtime_entry_precedes(dist, 0, is_protected, ctx->worst_dist, 0,
                                   ctx->worst_is_protected);

}

static inline u8 vp_frontier_runtime_slot_apply_ctx(
    afl_state_t *afl, struct queue_entry *q,
    vp_frontier_runtime_slot_ctx_t *ctx, u16 tag, u32 dist, u64 cost,
    u8 is_protected) {

  if (!dist || dist >= VP_DIST_UNSOLVED) return 0;

  s32    chosen_rel = vp_frontier_runtime_slot_find_owner(afl, ctx, q);
  size_t chosen_idx;

  if (chosen_rel >= 0) {

    chosen_idx = vp_frontier_runtime_slot_abs_idx(ctx, (u16)chosen_rel);
    vp_frontier_entry_t *entry = &afl->vp_frontier[chosen_idx];
    if (tag == entry->tag &&
        !vp_runtime_entry_precedes(dist, cost, is_protected, entry->dist,
                                   entry->cost, entry->is_protected))
      return 0;

  } else if (ctx->first_empty_rel >= 0) {

    chosen_rel = ctx->first_empty_rel;
    chosen_idx = vp_frontier_runtime_slot_abs_idx(ctx, (u16)chosen_rel);

  } else {

    assert(ctx->worst_rel >= 0);
    if (!vp_runtime_entry_precedes(dist, cost, is_protected, ctx->worst_dist,
                                   ctx->worst_cost, ctx->worst_is_protected))
      return 0;
    chosen_rel = ctx->worst_rel;
    chosen_idx = vp_frontier_runtime_slot_abs_idx(ctx, (u16)chosen_rel);

  }

  struct queue_entry *old = afl->vp_frontier[chosen_idx].owner;
  if (old && old != q) {

    if (!vp_site_owned_elsewhere(afl, (u16)ctx->site, old, chosen_idx)) {

      vp_owned_site_remove(old, (u16)ctx->site);

    }

    vp_dec_ref(afl, old);

  }

  if (old != q) {

    vp_inc_ref(q);
    vp_owned_site_add(q, (u16)ctx->site);

  }

  afl->vp_frontier[chosen_idx].owner = q;
  afl->vp_frontier[chosen_idx].tag = tag;
  afl->vp_frontier[chosen_idx].dist = dist;
  afl->vp_frontier[chosen_idx].cost = cost;
  afl->vp_frontier[chosen_idx].is_protected = is_protected;
  vp_frontier_runtime_slot_ctx_recompute(afl, ctx);
  return 1;

}

/* Recompute first-empty and worst-slot summaries from current slot contents. */
static inline void vp_frontier_site_ctx_recompute(afl_state_t            *afl,
                                                  vp_frontier_site_ctx_t *ctx) {

  ctx->first_empty_rel = -1;
  ctx->worst_rel = -1;
  ctx->worst_dist = 0;
  ctx->worst_cost = 0;

  for (u16 rel_idx = 0; rel_idx < ctx->slots; ++rel_idx) {

    size_t               idx = vp_frontier_site_abs_idx(ctx, rel_idx);
    vp_frontier_entry_t *entry = &afl->vp_frontier[idx];
    struct queue_entry  *owner = entry->owner;
    u32                  dist = entry->dist;

    if (vp_frontier_slot_is_empty(owner, dist)) {

      if (ctx->first_empty_rel < 0) ctx->first_empty_rel = (s32)rel_idx;
      continue;

    }

    if (ctx->worst_rel < 0 || dist > ctx->worst_dist ||
        (dist == ctx->worst_dist && entry->cost > ctx->worst_cost)) {

      ctx->worst_rel = (s32)rel_idx;
      ctx->worst_dist = dist;
      ctx->worst_cost = entry->cost;

    }

  }

}

/* Initialize per-site frontier context once; optionally purge disabled owners.
 */
static inline void vp_frontier_site_ctx_init(afl_state_t *afl, u32 site,
                                             u8 clear_stale,
                                             vp_frontier_site_ctx_t *ctx) {

  ctx->base = vp_site_base(afl, site);
  ctx->site = site;
  ctx->slots = (u16)afl->value_profile_slots;

  if (clear_stale) {

    for (u16 rel_idx = 0; rel_idx < ctx->slots; ++rel_idx) {

      size_t              idx = vp_frontier_site_abs_idx(ctx, rel_idx);
      struct queue_entry *owner = afl->vp_frontier[idx].owner;
      if (owner && owner->disabled) { vp_clear_slot(afl, idx); }

    }

  }

  vp_frontier_site_ctx_recompute(afl, ctx);

}

/* Find the worst active slot for a tag (highest dist, then highest cost).
   Returns relative slot index or -1 if tag is not present. */
static inline s32 vp_frontier_site_find_worst_tag(afl_state_t            *afl,
                                                  vp_frontier_site_ctx_t *ctx,
                                                  u16                     tag) {

  assert(ctx->first_empty_rel < 0);

  s32 worst_tag_rel = -1;
  u32 worst_tag_dist = 0;
  u64 worst_tag_cost = 0;

  for (u16 rel_idx = 0; rel_idx < ctx->slots; ++rel_idx) {

    size_t               idx = vp_frontier_site_abs_idx(ctx, rel_idx);
    vp_frontier_entry_t *entry = &afl->vp_frontier[idx];
    if (entry->tag != tag) continue;

    if (worst_tag_rel < 0 || entry->dist > worst_tag_dist ||
        (entry->dist == worst_tag_dist && entry->cost > worst_tag_cost)) {

      worst_tag_rel = (s32)rel_idx;
      worst_tag_dist = entry->dist;
      worst_tag_cost = entry->cost;

    }

  }

  return worst_tag_rel;

}

/* Probe-only decision used for admission, using caller-provided site context.
 */
static inline u8 vp_frontier_site_would_improve_ctx(afl_state_t            *afl,
                                                    vp_frontier_site_ctx_t *ctx,
                                                    u16 tag, u32 dist,
                                                    u8 is_protected) {

  if (!dist || dist >= VP_DIST_UNSOLVED) return 0;
  if (ctx->first_empty_rel >= 0) return 1;

  s32 tag_rel = vp_frontier_site_find_worst_tag(afl, ctx, tag);
  if (tag_rel >= 0) {

    size_t idx = vp_frontier_site_abs_idx(ctx, (u16)tag_rel);
    return dist < afl->vp_frontier[idx].dist ||
           (dist == afl->vp_frontier[idx].dist && is_protected &&
            !afl->vp_frontier[idx].is_protected);

  }

  assert(ctx->worst_rel >= 0);
  return dist < ctx->worst_dist;

}

/* Apply one candidate to a site context; updates frontier slots in-place and
   refreshes cached first-empty / worst summaries only on successful updates. */
static inline u8 vp_frontier_site_apply_ctx(afl_state_t            *afl,
                                            struct queue_entry     *q,
                                            vp_frontier_site_ctx_t *ctx,
                                            u16 tag, u32 dist, u64 cost,
                                            u8 is_protected) {

  if (!dist || dist >= VP_DIST_UNSOLVED) return 0;

  s32    chosen_rel = -1;
  size_t chosen_idx;
  if (ctx->first_empty_rel >= 0) {

    chosen_rel = ctx->first_empty_rel;
    chosen_idx = vp_frontier_site_abs_idx(ctx, (u16)chosen_rel);

  } else {

    s32 tag_rel = vp_frontier_site_find_worst_tag(afl, ctx, tag);
    if (tag_rel >= 0) {

      chosen_rel = tag_rel;
      chosen_idx = vp_frontier_site_abs_idx(ctx, (u16)chosen_rel);
      if (!vp_is_better(dist, cost, afl->vp_frontier[chosen_idx].dist,
                        afl->vp_frontier[chosen_idx].cost) &&
          !(dist == afl->vp_frontier[chosen_idx].dist && is_protected &&
            !afl->vp_frontier[chosen_idx].is_protected))
        return 0;

    } else {

      assert(ctx->worst_rel >= 0);
      if (!vp_is_better(dist, cost, ctx->worst_dist, ctx->worst_cost)) return 0;
      chosen_rel = ctx->worst_rel;
      chosen_idx = vp_frontier_site_abs_idx(ctx, (u16)chosen_rel);

    }

  }

  struct queue_entry *old = afl->vp_frontier[chosen_idx].owner;
  if (old && old != q) {

    if (!vp_site_owned_elsewhere(afl, (u16)ctx->site, old, chosen_idx)) {

      vp_owned_site_remove(old, (u16)ctx->site);

    }

    vp_dec_ref(afl, old);

  }

  if (old != q) {

    vp_inc_ref(q);
    vp_owned_site_add(q, (u16)ctx->site);

  }

  afl->vp_frontier[chosen_idx].owner = q;
  afl->vp_frontier[chosen_idx].tag = tag;
  afl->vp_frontier[chosen_idx].dist = dist;
  afl->vp_frontier[chosen_idx].cost = cost;
  afl->vp_frontier[chosen_idx].is_protected = is_protected;
  vp_frontier_site_ctx_recompute(afl, ctx);
  return 1;

}

/* RTN distance metric 1: remaining suffix weight plus first
   differing-byte hamming distance (sequential gradient). */
static inline u32 vp_rtn_compare_dist(const struct cmpfn_operands *rtn,
                                      u32 max_len, u32 prefix_len) {

  u32 rem = max_len - prefix_len;
  return (rem - 1U) * 8U +
         popcount_u8(rtn->v0[prefix_len] ^ rtn->v1[prefix_len]);

}

/* RTN distance metric 2: sum of per-byte hamming distances across ALL
   differing bytes.  Gives gradient signal for every byte position, not
   just the first mismatch.  Range: 1..256 for max_len up to 32. */
static inline u32 vp_rtn_compare_dist_allbytes(const struct cmpfn_operands *rtn,
                                               u32 max_len, u32 prefix_len) {

  u32 total = 0;
  for (u32 i = prefix_len; i < max_len; ++i) {

    total += popcount_u8(rtn->v0[i] ^ rtn->v1[i]);

  }

  return total > 0 ? total : 1;

}

/* Build an RTN slot tag from length class and per-class ordinal. */
static inline u16 vp_rtn_compare_tag(u32 max_len, u8 ord_in_len_class[32]) {

  u32 len_class = MIN(MAX(max_len, 1U), 32U) - 1U;
  u32 ord = ord_in_len_class[len_class]++;
  return (u16)(0x8000U | ((len_class & 31U) << 5) | (ord & 31U));

}

static inline void vp_frontier_site_clear_stale(afl_state_t *afl, u32 site) {

  size_t base = vp_site_base(afl, site);
  size_t span = vp_frontier_site_span(afl);
  for (size_t rel = 0; rel < span; ++rel) {

    size_t              idx = base + rel;
    struct queue_entry *owner = afl->vp_frontier[idx].owner;
    if (owner && owner->disabled) { vp_clear_slot(afl, idx); }

  }

}

static inline u8 vp_apply_runtime_site_candidates(
    afl_state_t *afl, struct queue_entry *q, u32 site,
    vp_site_candidate_t *candidates, u32 cand_count, u64 cost) {

  u8 site_changed = 0;
  if (cand_count) { vp_frontier_site_clear_stale(afl, site); }

  for (u32 i = 0; i < cand_count; ++i) {

    vp_frontier_runtime_slot_ctx_t ctx;
    vp_frontier_runtime_slot_ctx_init(afl, site, candidates[i].slot_rel, 0,
                                      &ctx);

    if (vp_frontier_runtime_slot_apply_ctx(afl, q, &ctx, candidates[i].tag,
                                           candidates[i].dist, cost,
                                           candidates[i].is_protected))
      site_changed = 1;

  }

  if (vp_site_refresh_needed(afl, site, site_changed)) {

    vp_refresh_site_winner(afl, site);

  }

  return site_changed;

}

typedef struct {

  u32 site;
  u32 max_dist;
  u16 slot_rel;
  u16 tag;
  u16 need;
  u16 seen;

} vp_trim_req_t;

struct vp_trim_guard {

  afl_state_t        *afl;
  struct queue_entry *q;
  u8                  active;
  u8                  runtime_sandboxed;
  u16                 slots;
  vp_trim_req_t      *req;
  u32                 req_cnt;
  u32                 req_cap;
  u16                *site_ids;
  u32                 site_cnt;
  u32                 site_cap;
  size_t             *owned_idx;
  u32                 owned_cnt;
  u32                 owned_cap;
  vp_site_t          *site_backup;

};

static inline void vp_trim_guard_destroy_req(vp_trim_guard_t *guard) {

  if (!guard) return;
  if (guard->req) { ck_free(guard->req); }
  if (guard->site_ids) { ck_free(guard->site_ids); }
  if (guard->owned_idx) { ck_free(guard->owned_idx); }
  if (guard->site_backup) { ck_free(guard->site_backup); }
  ck_free(guard);

}

static inline void vp_trim_guard_add_site(vp_trim_guard_t *guard, u32 site) {

  if (guard->site_cnt == guard->site_cap) {

    u32 new_cap = guard->site_cap ? guard->site_cap << 1 : 8;
    guard->site_ids = ck_realloc(guard->site_ids, new_cap * sizeof(u16));
    guard->site_cap = new_cap;

  }

  guard->site_ids[guard->site_cnt++] = (u16)site;

}

static inline void vp_trim_guard_add_req(vp_trim_guard_t *guard, u32 site,
                                         u32 site_req_start, u16 slot_rel,
                                         u16 tag, u32 max_dist) {

  for (u32 i = site_req_start; i < guard->req_cnt; ++i) {

    vp_trim_req_t *r = &guard->req[i];
    if (r->slot_rel == slot_rel && r->tag == tag && r->max_dist == max_dist) {

      if (r->need < 0xffffU) { ++r->need; }
      return;

    }

  }

  if (guard->req_cnt == guard->req_cap) {

    u32 new_cap = guard->req_cap ? guard->req_cap << 1 : 8;
    guard->req = ck_realloc(guard->req, new_cap * sizeof(vp_trim_req_t));
    guard->req_cap = new_cap;

  }

  vp_trim_req_t *r = &guard->req[guard->req_cnt++];
  r->site = site;
  r->slot_rel = slot_rel;
  r->tag = tag;
  r->max_dist = max_dist;
  r->need = 1;
  r->seen = 0;

}

static inline void vp_trim_guard_add_owned(vp_trim_guard_t *guard, size_t idx) {

  if (guard->owned_cnt == guard->owned_cap) {

    u32 new_cap = guard->owned_cap ? guard->owned_cap << 1 : 8;
    guard->owned_idx = ck_realloc(guard->owned_idx, new_cap * sizeof(size_t));
    guard->owned_cap = new_cap;

  }

  guard->owned_idx[guard->owned_cnt++] = idx;

}

static inline void vp_trim_guard_reset_seen(vp_trim_guard_t *guard) {

  for (u32 i = 0; i < guard->req_cnt; ++i) {

    guard->req[i].seen = 0;

  }

}

static inline u8 vp_trim_guard_all_seen(const vp_trim_guard_t *guard) {

  for (u32 i = 0; i < guard->req_cnt; ++i) {

    if (guard->req[i].seen < guard->req[i].need) return 0;

  }

  return 1;

}

/* Assign one observed (site,slot,tag,dist) candidate to the strictest
   unsatisfied guarded requirement that it can satisfy. */
static inline void vp_trim_guard_assign_candidate(vp_trim_guard_t *guard,
                                                  u32 site, u16 slot_rel,
                                                  u16 tag, u32 dist) {

  s32 best = -1;
  u32 best_max_dist = ~(u32)0;

  for (u32 i = 0; i < guard->req_cnt; ++i) {

    vp_trim_req_t *r = &guard->req[i];
    if (r->site != site || r->slot_rel != slot_rel || r->tag != tag ||
        r->seen >= r->need || dist > r->max_dist)
      continue;

    if (best < 0 || r->max_dist < best_max_dist) {

      best = (s32)i;
      best_max_dist = r->max_dist;

    }

  }

  if (best >= 0) { ++guard->req[best].seen; }

}

static inline u8 vp_trim_guard_eval_runtime(vp_trim_guard_t *guard) {

  afl_state_t *afl = guard->afl;
  vp_map_t    *vp = afl->shm.vp_map;
  if (unlikely(!vp || !vp->enabled)) return 0;

  u16 active_mask = vp_active_slot_mask((u16)afl->value_profile_slots);
  for (u32 i = 0; i < guard->site_cnt; ++i) {

    u32                 site_id = guard->site_ids[i];
    vp_site_candidate_t candidates[VP_MAX_SLOTS];
    u32                 cand_count = vp_collect_runtime_site_candidates(
        &vp->site[site_id], active_mask, candidates, VP_MAX_SLOTS);

    for (u32 j = 0; j < cand_count; ++j) {

      vp_trim_guard_assign_candidate(guard, site_id, candidates[j].slot_rel,
                                     candidates[j].tag, candidates[j].dist);

    }

  }

  return vp_trim_guard_all_seen(guard);

}

vp_trim_guard_t *vp_trim_guard_init(afl_state_t *afl, struct queue_entry *q) {

  if (unlikely(!afl || !q || !afl->vp_frontier || !afl->value_profile_active ||
               !q->vp_ref_cnt))
    return NULL;

  vp_trim_guard_t *guard = ck_alloc(sizeof(vp_trim_guard_t));
  guard->afl = afl;
  guard->q = q;
  guard->slots = (u16)vp_frontier_site_span(afl);

  u32 refs_left = q->vp_ref_cnt;
  for (u32 site = 0; site < CMP_MAP_W && refs_left; ++site) {

    size_t base = vp_site_base(afl, site);
    u8     site_added = 0;
    u32    site_req_start = guard->req_cnt;
    for (u16 rel = 0; rel < guard->slots && refs_left; ++rel) {

      vp_frontier_entry_t *entry = &afl->vp_frontier[base + rel];
      if (entry->owner != q || entry->dist >= VP_DIST_UNSOLVED) continue;

      if (!site_added) {

        vp_trim_guard_add_site(guard, site);
        site_added = 1;

      }

      vp_trim_guard_add_owned(guard, base + rel);
      u16 slot_rel = (u16)(rel / VP_RUNTIME_SLOT_REPLICA_LIMIT);
      vp_trim_guard_add_req(guard, site, site_req_start, slot_rel, entry->tag,
                            entry->dist);
      --refs_left;

    }

  }

  if (!guard->req_cnt) {

    vp_trim_guard_destroy_req(guard);
    return NULL;

  }

  if (guard->site_cnt) {

    guard->site_backup = ck_alloc(guard->site_cnt * sizeof(vp_site_t));

  }

  guard->active = 1;
  return guard;

}

void vp_trim_guard_before_exec(vp_trim_guard_t *guard) {

  if (unlikely(!guard || !guard->active)) return;

  guard->runtime_sandboxed =
      vp_runtime_observe_begin(guard->afl, guard->site_ids, guard->site_cnt,
                               guard->site_backup, VP_RUNTIME_OBSERVE_TRIM);

}

u8 vp_trim_guard_preserved(vp_trim_guard_t *guard, u8 *in_buf, u32 cur_len,
                           u32 remove_pos, u32 remove_len) {

  if (unlikely(!guard || !guard->active || !guard->req_cnt)) return 1;
  (void)in_buf;
  (void)cur_len;
  (void)remove_pos;
  (void)remove_len;
  vp_trim_guard_reset_seen(guard);

  return vp_trim_guard_eval_runtime(guard);

}

void vp_trim_guard_after_exec(vp_trim_guard_t *guard) {

  if (unlikely(!guard || !guard->active)) return;
  if (!guard->runtime_sandboxed) return;

  vp_runtime_observe_end(guard->afl, guard->site_ids, guard->site_cnt,
                         guard->site_backup);
  guard->runtime_sandboxed = 0;

}

void vp_trim_guard_refresh_owner_cost(vp_trim_guard_t *guard) {

  if (unlikely(!guard || !guard->active || !guard->afl || !guard->q ||
               !guard->afl->vp_frontier || !guard->owned_cnt ||
               !guard->q->vp_ref_cnt))
    return;

  afl_state_t        *afl = guard->afl;
  struct queue_entry *q = guard->q;
  u64                 owner_cost = vp_entry_cost(q);
  u32                 slots = (u32)vp_frontier_site_span(afl);

  s32 last_site = -1;
  u8  site_touched = 0;
  for (u32 i = 0; i < guard->owned_cnt; ++i) {

    size_t idx = guard->owned_idx[i];
    u32    site = (u32)(idx / slots);
    /* vp_trim_guard_init() populates owned_idx in site-ascending order.
       If this invariant changes, fall back to full owner-cost refresh. */
    if (unlikely(last_site >= 0 && site < (u32)last_site)) {

      vp_trim_refresh_owner_cost(afl, q);
      return;

    }

    if ((s32)site != last_site && last_site >= 0) {

      if (site_touched) { vp_refresh_site_winner(afl, (u32)last_site); }
      site_touched = 0;

    }

    vp_frontier_entry_t *entry = &afl->vp_frontier[idx];
    if (entry->owner == q && entry->dist < VP_DIST_UNSOLVED &&
        entry->cost != owner_cost) {

      entry->cost = owner_cost;
      site_touched = 1;

    }

    last_site = (s32)site;

  }

  if (last_site >= 0 && site_touched) {

    vp_refresh_site_winner(afl, (u32)last_site);

  }

}

void vp_trim_guard_destroy(vp_trim_guard_t *guard) {

  if (!guard) return;
  vp_trim_guard_after_exec(guard);
  vp_trim_guard_destroy_req(guard);

}

void vp_trim_refresh_owner_cost(afl_state_t *afl, struct queue_entry *q) {

  if (unlikely(!afl || !q || !afl->vp_frontier || !q->vp_ref_cnt)) return;

  u64 owner_cost = vp_entry_cost(q);
  u32 refs_left = q->vp_ref_cnt;
  u16 slots = (u16)vp_frontier_site_span(afl);

  for (u32 site = 0; site < CMP_MAP_W && refs_left; ++site) {

    size_t base = vp_site_base(afl, site);
    u8     site_touched = 0;
    for (u16 rel = 0; rel < slots && refs_left; ++rel) {

      vp_frontier_entry_t *entry = &afl->vp_frontier[base + rel];
      if (entry->owner != q || entry->dist >= VP_DIST_UNSOLVED) continue;

      if (entry->cost != owner_cost) {

        entry->cost = owner_cost;
        site_touched = 1;

      }

      --refs_left;

    }

    if (site_touched) { vp_refresh_site_winner(afl, site); }

  }

}

/* Fast VP-interest probe used before queue admission.
   Admission is based on distance-only progress; cost tie-breaks are applied
   later in vp_frontier_apply() after calibration provides real exec_us. */
u8 vp_frontier_would_improve(afl_state_t *afl) {

  if (unlikely(!afl->vp_frontier)) return 0;

  vp_map_t *vp = afl->shm.vp_map;
  if (unlikely(!vp || !vp->enabled)) return 0;
  u16                    max_slot_count = (u16)afl->value_profile_slots;
  u16                    active_mask = vp_active_slot_mask(max_slot_count);
  vp_runtime_site_iter_t it;
  vp_runtime_site_iter_init(&it, vp);
  u32        k;
  vp_site_t *site;
  while (vp_runtime_site_iter_next(&it, &k, &site)) {

    vp_site_candidate_t candidates[VP_MAX_SLOTS];
    u32                 cand_count = vp_collect_runtime_site_candidates(
        site, active_mask, candidates, max_slot_count);

    for (u32 i = 0; i < cand_count; ++i) {

      vp_frontier_runtime_slot_ctx_t ctx;
      vp_frontier_runtime_slot_ctx_init(afl, k, candidates[i].slot_rel, 0,
                                        &ctx);
      if (vp_frontier_runtime_slot_would_improve_ctx(
              &ctx, candidates[i].dist, candidates[i].is_protected))
        return 1;

    }

  }

  return 0;

}

/* Apply L1 runtime-SHM candidates to the VP frontier using caller-provided
   cost (used as tie-breaker at equal distance). */
static inline u8 vp_apply_runtime_frontier(afl_state_t        *afl,
                                           struct queue_entry *q, u64 cost) {

  vp_map_t *vp = afl->shm.vp_map;
  if (unlikely(!vp || !vp->enabled)) return 0;

  u8                     improved = 0;
  u16                    max_slot_count = (u16)afl->value_profile_slots;
  u16                    active_mask = vp_active_slot_mask(max_slot_count);
  vp_runtime_site_iter_t it;
  vp_runtime_site_iter_init(&it, vp);
  u32        k;
  vp_site_t *site;
  while (vp_runtime_site_iter_next(&it, &k, &site)) {

    vp_site_candidate_t candidates[VP_MAX_SLOTS];
    u32                 cand_count = vp_collect_runtime_site_candidates(
        site, active_mask, candidates, max_slot_count);

    if (vp_apply_runtime_site_candidates(afl, q, k, candidates, cand_count,
                                         cost)) {

      improved = 1;

    }

  }

  return improved;

}

void vp_frontier_apply_with_cost(afl_state_t *afl, struct queue_entry *q,
                                 u64 cost) {

  if (unlikely(!q || !afl->vp_frontier)) return;

  u8 improved = vp_apply_runtime_frontier(afl, q, cost);

  if (q->vp_only && !q->vp_ref_cnt && !q->vp_last_ref_cycle) {

    q->vp_last_ref_cycle = afl->queue_cycle;

  }

  if (improved) afl->score_changed = 1;
  vp_maybe_disable_entry(afl, q);

}

void vp_frontier_apply(afl_state_t *afl, struct queue_entry *q) {

  vp_frontier_apply_with_cost(afl, q, vp_entry_cost(q));

}

/* Apply deferred disable checks for VP-only queue entries at queue-cycle
   boundaries. */
void vp_apply_delayed_evictions(afl_state_t *afl) {

  if (!afl->value_profile_mode) return;
  u8 needs_retry = 0;

  for (u32 i = 0; i < afl->queued_items; ++i) {

    struct queue_entry *q = afl->queue_buf[i];
    if (!q) continue;

    if (!q->disabled && q->vp_only && !q->has_new_cov && !q->vp_ref_cnt &&
        q->vp_last_ref_cycle && afl->queue_cycle <= q->vp_last_ref_cycle) {

      needs_retry = 1;
      continue;

    }

    vp_maybe_disable_entry(afl, q);

  }

  if (needs_retry) { afl->score_changed = 1; }

}

/* Collect runtime VP signal for one concrete input. */
u8 vp_collect_signal_for_input(afl_state_t *afl, u8 *mem, u32 len) {

  if (unlikely(!afl->value_profile_active)) return 0;

  void *exec_mem = mem;
  u32   exec_len = write_to_testcase(afl, &exec_mem, len, 0);
  if (!exec_len) return 0;

  u8 fault = fuzz_run_target(afl, &afl->fsrv, afl->fsrv.exec_tmout);
  if (unlikely(fault == FSRV_RUN_ERROR)) {

    FATAL("Unable to execute target application");

  }

  if (fault != afl->crash_mode && fault != FSRV_RUN_NOBITS) return 0;

  return afl->shm.vp_map && afl->shm.vp_map->enabled;

}

/* Replay queue entries once VP activates in stagnation mode so the frontier
   is immediately based on existing inputs too. */
static void vp_replay_queue(afl_state_t *afl) {

  u32 start = afl->value_profile_replay_idx;
  u32 end = afl->queued_items;
  /* TODO: This can replay many entries in one call and pause the main loop on
     large queues. Consider a per-call batch/time budget, or at least log the
     pending replay size when activation starts. */
  if (start > end) start = end;
  if (start == end) {

    afl->value_profile_replay_idx = end;
    return;

  }

  u32 i = start;
  for (; i < end; ++i) {

    if (afl->stop_soon) break;

    struct queue_entry *q = afl->queue_buf[i];
    if (unlikely(!q || q->disabled || !q->len)) continue;

    u8 *mem = queue_testcase_get(afl, q);
    if (!vp_collect_signal_for_input(afl, mem, q->len)) continue;
    vp_frontier_apply_with_cost(afl, q, vp_entry_cost(q));

  }

  afl->value_profile_replay_idx = i;

}

/* Check stagnation and activate/deactivate value profiling. */

void vp_update_activation(afl_state_t *afl) {

  if (afl->value_profile_mode != 2) return;

  u64 cur = get_cur_time();
  /* Stagnation mode is edge-coverage based, not queue-growth based. */
  u64 no_find_ms = (afl->last_cov_find_time == 0)
                       ? (cur - afl->start_time)
                       : (cur - afl->last_cov_find_time);

  u8 should = (no_find_ms >= (u64)afl->value_profile_stagnation_secs * 1000);

  if (should && !afl->value_profile_active) {

    afl->value_profile_active = 1;
    afl->value_profile_enabled_cycle = afl->queue_cycle;
    vp_replay_queue(afl);
    afl->score_changed = 1;
    OKF("Stagnation (%llu s), enabling value profiling.",
        (unsigned long long)(no_find_ms / 1000));

  } else if (!should && afl->value_profile_active) {

    /* Keep VP on for one full queue cycle after activation to avoid
       immediate on/off flapping on transient coverage recoveries. */
    if (afl->queue_cycle <= afl->value_profile_enabled_cycle) return;

    afl->value_profile_active = 0;
    afl->value_profile_enabled_cycle = 0;
    afl->value_profile_replay_idx = afl->queued_items;
    afl->score_changed = 1;
    OKF("New edge coverage found, disabling value profiling.");

  }

}

