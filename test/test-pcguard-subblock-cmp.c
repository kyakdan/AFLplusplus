#include <unistd.h>

volatile int subcmp_sink;

int main(void) {

  unsigned char in[2] = {0};
  if (read(0, in, sizeof(in)) != (ssize_t)sizeof(in)) return 0;

  int lt = (in[0] < in[1]);
  int eq = (in[0] == in[1]);

  /* Keep compare results live without introducing new control flow. */
  subcmp_sink = lt + eq;
  return 0;

}
