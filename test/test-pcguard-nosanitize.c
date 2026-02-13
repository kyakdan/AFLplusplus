/*
 * Regression test fixture for __attribute__((no_sanitize_coverage)).
 * The GCC plugin should not insert PC Guard instrumentation into the
 * excluded function when the attribute is supported by the compiler.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#if defined(__has_attribute)
  #if __has_attribute(no_sanitize_coverage)
    #define HAS_NO_SANITIZE_COVERAGE 1
    #define NO_SANITIZE_COVERAGE __attribute__((no_sanitize_coverage))
  #else
    #define HAS_NO_SANITIZE_COVERAGE 0
    #define NO_SANITIZE_COVERAGE
  #endif
#else
  #define HAS_NO_SANITIZE_COVERAGE 0
  #define NO_SANITIZE_COVERAGE
#endif

#define NOINLINE __attribute__((noinline))

volatile int nosancov_sink;

NO_SANITIZE_COVERAGE NOINLINE int pcguard_nosancov_excluded(int x) {

  if (x == 7) {

    nosancov_sink = 7;
    return 1;

  }

  nosancov_sink = x;
  return 0;

}

NOINLINE int pcguard_nosancov_included(int x) {

  if (x == 9) {

    nosancov_sink = 9;
    return 1;

  }

  nosancov_sink = x + 1;
  return 0;

}

int main(int argc, char **argv) {

  if (argc > 1 && argv[1][0] == 'q') {

    printf("%d\n", HAS_NO_SANITIZE_COVERAGE);
    return 0;

  }

  int x = (argc > 1) ? atoi(argv[1]) : 0;
  (void)pcguard_nosancov_excluded(x);
  (void)pcguard_nosancov_included(x);
  return 0;

}
