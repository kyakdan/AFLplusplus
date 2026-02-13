/*
 * Shared library used by GCC plugin PC Guard regression tests.
 * The function below must be instrumented and initialized via
 * __sanitizer_cov_trace_pc_guard_init when linked at startup.
 */

#include <stdint.h>

volatile int dso_sink;

int pcguard_dso_fn(const uint8_t *buf, int len) {

  if (len > 0 && buf[0] == 'A') {

    dso_sink = 1;
    return 1;

  }

  dso_sink = 0;
  return 0;

}
