/*
 * Persistent mode fuzz test for GCC PC Guard implementation.
 * Triggers abort() when specific code paths are reached.
 *
 * Compile: afl-gcc-fast -o test-pcguard-persistent test-pcguard-persistent.c
 * Run: afl-fuzz -i input -o output -- ./test-pcguard-persistent
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>

__AFL_FUZZ_INIT();

/* Linker-provided section bounds */
#if defined(__APPLE__) && defined(__MACH__)
extern uint32_t sancov_guards_start
    __asm("section$start$__DATA$__sancov_guards");
extern uint32_t sancov_guards_stop
    __asm("section$end$__DATA$__sancov_guards");
#define SANCOV_START (&sancov_guards_start)
#define SANCOV_STOP (&sancov_guards_stop)
#else
extern uint32_t __start___sancov_guards;
extern uint32_t __stop___sancov_guards;
#define SANCOV_START (&__start___sancov_guards)
#define SANCOV_STOP (&__stop___sancov_guards)
#endif

volatile int sink;

/* Test 1: Simple magic value check */
void test_magic(uint8_t *buf, int len) {
    if (len >= 4) {
        if (buf[0] == 'F' && buf[1] == 'U' && buf[2] == 'Z' && buf[3] == 'Z') {
            abort();  /* Found magic: FUZZ */
        }
    }
}

/* Test 2: Critical edge with nested conditions */
void test_critical_edge(uint8_t *buf, int len) {
    if (len >= 3) {
        int x = buf[0];
        int y = buf[1];
        int z = buf[2];

        /* Diamond pattern - critical edges */
        int result;
        if (x > 128) {
            result = 1;
        } else {
            result = 2;
        }

        if (y > 128) {
            result += 10;
        } else {
            result += 20;
        }

        /* Crash requires specific path through both diamonds */
        if (result == 11 && z == 0x42) {
            abort();  /* x>128, y>128, z==0x42 */
        }
    }
}

/* Test 3: Loop with early exit - tests edge splitting */
void test_loop(uint8_t *buf, int len) {
    if (len >= 2) {
        int target = buf[0];
        int count = buf[1] % 16;
        int found = 0;

        for (int i = 0; i < count; i++) {
            if (i == target) {
                found = 1;
                break;  /* Critical edge: loop exit */
            }
            sink = i;
        }

        if (found && target == 7 && count == 10) {
            abort();  /* Specific loop path */
        }
    }
}

/* Test 4: Switch statement coverage */
void test_switch(uint8_t *buf, int len) {
    if (len >= 2) {
        int selector = buf[0] % 5;
        int check = buf[1];

        int result;
        switch (selector) {
            case 0: result = 100; break;
            case 1: result = 200; break;
            case 2: result = 300; break;
            case 3: result = 400; break;
            default: result = 500; break;
        }

        if (result == 300 && check == 0xAB) {
            abort();  /* selector==2 && check==0xAB */
        }
    }
}

/* Test 5: Deep nesting */
void test_nested(uint8_t *buf, int len) {
    if (len >= 4) {
        if (buf[0] > 100) {
            if (buf[1] > 100) {
                if (buf[2] > 100) {
                    if (buf[3] == 0xFF) {
                        abort();  /* All conditions met */
                    }
                }
            }
        }
    }
}

/* Verify guards are initialized.
   With default AFL_INST_RATIO=100 every guard must be non-zero.
   When AFL_INST_RATIO < 100 the runtime may legitimately set some
   guards to 0 (mapped to coverage[0]), so accept those.  */
int verify_guards(void) {
    uint32_t *start = SANCOV_START;
    uint32_t *stop = SANCOV_STOP;
    int       allow_zero = 0;
    long      total = (long)(stop - start);
    long      nonzero = 0;
    char     *ratio_str = getenv("AFL_INST_RATIO");

    if (ratio_str) {
        char *endptr = NULL;
        long  ratio = strtol(ratio_str, &endptr, 10);
        if (endptr != ratio_str && *endptr == '\0' && ratio > 0 && ratio < 100) {
            allow_zero = 1;
        }
    }

    for (uint32_t *p = start; p < stop; p++) {
        if (*p != 0) nonzero++;
    }

    if (!allow_zero && nonzero != total) {
        fprintf(stderr,
                "ERROR: Only %ld/%ld guards initialized (AFL_INST_RATIO unset or >=100)\n",
                nonzero, total);
        return 1;
    }

    if (nonzero == 0) {
        fprintf(stderr, "ERROR: No guards initialized at all!\n");
        return 1;
    }

    fprintf(stderr, "[+] %ld/%ld guards initialized\n", nonzero, total);
    return 0;
}

int main(void) {
    if (verify_guards() != 0) {
        return 1;
    }

#ifdef __AFL_HAVE_MANUAL_CONTROL
    __AFL_INIT();
#endif

    uint8_t *buf = __AFL_FUZZ_TESTCASE_BUF;

    while (__AFL_LOOP(10000)) {
        int len = __AFL_FUZZ_TESTCASE_LEN;
        if (len < 1) continue;

        test_magic(buf, len);
        test_critical_edge(buf, len);
        test_loop(buf, len);
        test_switch(buf, len);
        test_nested(buf, len);
    }

    return 0;
}
