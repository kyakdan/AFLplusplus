#ifndef TEST_PCGUARD_COMDAT_H
#define TEST_PCGUARD_COMDAT_H

template <typename T>
__attribute__((noinline)) int pcguard_comdat_template(T x) {

  volatile int y = (int)x;
  if (y == 12345) { return 1; }
  return 0;

}

#endif
