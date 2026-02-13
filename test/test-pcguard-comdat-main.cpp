int pcguard_comdat_one(int);
int pcguard_comdat_two(int);

int main(int argc, char **) {

  return pcguard_comdat_one(argc) + pcguard_comdat_two(argc + 1);

}
