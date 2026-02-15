/*
 * Fixture for sub-block compare handling:
 * - compares used as control decisions should be skipped
 * - compares used only as values should still be instrumented
 */

#include <stdint.h>

volatile int decision_use_sink;

__attribute__((noinline)) int pcguard_decision_use(int a, int b) {

  if (a < b) return 1;
  return 0;

}

__attribute__((noinline)) int pcguard_non_decision_use(int a, int b) {

  int c = (a < b);
  decision_use_sink = c;
  return c;

}

int main(int argc, char **argv) {

  (void)argv;
  decision_use_sink += pcguard_decision_use(argc, argc + 1);
  decision_use_sink += pcguard_non_decision_use(argc, argc + 1);
  return decision_use_sink & 1;

}
