#include <stdint.h>
#include <string.h>

#include "../include/value-profile.h"

extern vp_map_t *__afl_vp_map;
void __valueprofile_hook4(uint32_t arg1, uint32_t arg2, uint8_t attr);

static vp_map_t vp_local;

static void begin_exec(void) {

  vp_local.enabled = 1;
  ++vp_local.exec_id;
  if (!vp_local.exec_id) ++vp_local.exec_id;
  vp_local.control_len = 0;
  vp_local.control_drops = 0;

}

__attribute__((noinline)) static void run_once(uint32_t observed) {

  __valueprofile_hook4(observed, 0, 0);

}

int main(void) {

  memset(&vp_local, 0, sizeof(vp_local));
  __afl_vp_map = &vp_local;

  /* First unsolved hit initializes the two home slots for metric tags 0 and 1.
   */
  begin_exec();
  run_once(0x01010101U);
  if (vp_local.control_len != 1) return 1;
  u16        site = vp_local.control[0];
  vp_site_t *site_state = &vp_local.site[site];
  if ((site_state->valid_mask & 0x3U) != 0x3U) return 2;
  if (site_state->valid_mask & ~0x3U) return 3;

  /* Regression check: repeating the same non-improving observation must not
     spill into overflow slots. Before the fix, this filled slots 2/3. */
  begin_exec();
  run_once(0x01010101U);
  if (vp_local.control_len != 0) return 4;
  site_state = &vp_local.site[site];
  if (site_state->valid_mask & ~0x3U) return 5;

  /* Improvement to solved must still update the two home slots. */
  begin_exec();
  run_once(0x00000000U);
  if (vp_local.control_len != 1) return 6;
  site_state = &vp_local.site[site];
  if (site_state->slots[0].best_dist != 0 ||
      site_state->slots[1].best_dist != 0)
    return 7;

  return 0;

}

