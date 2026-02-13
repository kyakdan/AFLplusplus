/*
 * Main executable for GCC plugin PC Guard DSO regression tests.
 * It links against test-pcguard-dso-lib.c at startup.
 */

#include <stdint.h>
#include <stdlib.h>

extern int pcguard_dso_fn(const uint8_t *buf, int len);

volatile int main_sink;

int main(int argc, char **argv) {

  uint8_t in = 'B';

  if (argc > 1 && argv[1][0] == 'A') {

    in = 'A';
    main_sink = 1;

  } else {

    main_sink = 2;

  }

  (void)pcguard_dso_fn(&in, 1);
  return EXIT_SUCCESS;

}
