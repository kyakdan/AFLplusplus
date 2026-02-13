/*
 * Fixture for static initialization helper handling in GCC PC Guard mode.
 * The compiler-generated helper function should not receive instrumentation.
 */

volatile int static_init_sink;

struct static_init_fixture {

  static_init_fixture() {

    static_init_sink = 7;

  }

};

static static_init_fixture global_fixture;

int main() {

  return static_init_sink == 7 ? 0 : 1;

}
