#include <unistd.h>

volatile int subatomic_sink;
volatile int subatomic_g0 = 0;
volatile int subatomic_g1 = 0;

int main(void) {

  unsigned char in[2] = {0};
  if (read(0, in, sizeof(in)) != (ssize_t)sizeof(in)) return 0;

  int expected0 = (int)(in[0] & 1);
  int desired0 = 7;
  int ok = __atomic_compare_exchange_n((int *)&subatomic_g0, &expected0,
                                       desired0, 0, __ATOMIC_SEQ_CST,
                                       __ATOMIC_SEQ_CST);

  int expected1 = (int)(in[1] & 1);
  int old = __sync_val_compare_and_swap((int *)&subatomic_g1, expected1, 11);

  /* Keep values live without introducing control-flow branches. */
  subatomic_sink = ok + old + expected0 + expected1;
  return 0;

}
