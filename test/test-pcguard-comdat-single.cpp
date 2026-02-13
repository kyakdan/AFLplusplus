#include "test-pcguard-comdat.h"

int pcguard_comdat_one(int x) {

  return pcguard_comdat_template(x);

}

int main(int argc, char **) {

  return pcguard_comdat_one(argc);

}
