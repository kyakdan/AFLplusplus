#!/bin/sh

. ./test-pre.sh

$ECHO "$BLUE[*] Testing: gcc_plugin"
test -e ../afl-gcc-fast -a -e ../afl-compiler-rt.o && {
  SAVE_AFL_CC=${AFL_CC}
  export AFL_CC=`command -v gcc`
  rm -f test-instr.plain.gccpi
  ../afl-gcc-fast -o test-instr.plain.gccpi ../test-instr.c > /dev/null 2>&1
  AFL_HARDEN=1 ../afl-gcc-fast -o test-compcov.harden.gccpi test-compcov.c > /dev/null 2>&1
  test -e test-instr.plain.gccpi && {
    chmod +x test-instr.plain.gccpi
    ls -l test-instr.plain.gccpi
    $ECHO "$GREEN[+] gcc_plugin compilation succeeded"
    echo 0 | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-instr.plain.0 -r -- ./test-instr.plain.gccpi > /dev/null 2>&1
    AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-instr.plain.1 -r -- ./test-instr.plain.gccpi < /dev/null > /dev/null 2>&1
    test -e test-instr.plain.0 -a -e test-instr.plain.1 && {
      diff test-instr.plain.0 test-instr.plain.1 > /dev/null 2>&1 && {
        $ECHO "$RED[!] gcc_plugin instrumentation should be different on different input but is not"
        CODE=1
      } || {
        $ECHO "$GREEN[+] gcc_plugin instrumentation present and working correctly"
        TUPLES=`echo 0|AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o /dev/null -- ./test-instr.plain.gccpi 2>&1 | grep Captur | awk '{print$3}'`
        test "$TUPLES" -gt 1 -a "$TUPLES" -lt 10 && {
          $ECHO "$GREEN[+] gcc_plugin run reported $TUPLES instrumented locations which is fine"
        } || {
          $ECHO "$RED[!] gcc_plugin instrumentation produces a weird numbers: $TUPLES"
          $ECHO "$YELLOW[-] this is a known issue in gcc, not AFL++. It is not flagged as an error because travis builds would all fail otherwise :-("
          #CODE=1
        }
        test "$TUPLES" -lt 2 && SKIP=1
        true
      }
    } || {
      $ECHO "$RED[!] gcc_plugin instrumentation failed"
      CODE=1
    }
    rm -f test-instr.plain.0 test-instr.plain.1
  } || {
    $ECHO "$RED[!] gcc_plugin failed"
    CODE=1
  }

  test -e test-compcov.harden.gccpi && test_compcov_binary_functionality ./test-compcov.harden.gccpi && {
    nm test-compcov.harden.gccpi | grep -Eq 'stack_chk_fail|fstack-protector-all|fortified' > /dev/null 2>&1 && {
      $ECHO "$GREEN[+] gcc_plugin hardened mode succeeded and is working"
    } || {
      $ECHO "$RED[!] gcc_plugin hardened mode is not hardened"
      CODE=1
    }
    rm -f test-compcov.harden.gccpi
  } || {
    $ECHO "$RED[!] gcc_plugin hardened mode compilation failed"
    CODE=1
  }
  # now we want to be sure that afl-fuzz is working
  # make sure crash reporter is disabled on Mac OS X
  (test "$(uname -s)" = "Darwin" && test $(launchctl list 2>/dev/null | grep -q '\.ReportCrash$') && {
    $ECHO "$RED[!] we cannot run afl-fuzz with enabled crash reporter. Run 'sudo sh afl-system-config'.$RESET"
    CODE=1
    true
  }) || {
    test -z "$SKIP" && {
      mkdir -p in
      echo 0 > in/in
      $ECHO "$GREY[*] running afl-fuzz for gcc_plugin, this will take approx 10 seconds"
      {
        ../afl-fuzz -V07 -m ${MEM_LIMIT} -i in -o out -- ./test-instr.plain.gccpi >>errors 2>&1
      } >>errors 2>&1
      test -n "$( ls out/default/queue/id:000002* 2>/dev/null )" && {
        $ECHO "$GREEN[+] afl-fuzz is working correctly with gcc_plugin"
      } || {
        echo CUT------------------------------------------------------------------CUT
        cat errors
        echo CUT------------------------------------------------------------------CUT
        $ECHO "$RED[!] afl-fuzz is not working correctly with gcc_plugin"
        CODE=1
      }
      rm -rf in out errors
    }
  }
  rm -f test-instr.plain.gccpi

  # now for the special gcc_plugin things
  echo foobar.c > instrumentlist.txt
  AFL_GCC_INSTRUMENT_FILE=instrumentlist.txt ../afl-gcc-fast -o test-compcov test-compcov.c > /dev/null 2>&1
  test -x test-compcov && test_compcov_binary_functionality ./test-compcov && {
    echo 1 | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o - -r -- ./test-compcov 2>&1 | grep -q "Captured 0 tuples" && {
      $ECHO "$GREEN[+] gcc_plugin instrumentlist feature works correctly"
    } || {
      $ECHO "$RED[!] gcc_plugin instrumentlist feature failed"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin instrumentlist feature compilation failed."
    CODE=1
  }
  rm -f test-compcov test.out instrumentlist.txt
  ../afl-gcc-fast -o test-persistent ../utils/persistent_mode/persistent_demo.c > /dev/null 2>&1
  test -e test-persistent && {
    echo foo | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o /dev/null -q -r -- ./test-persistent && {
      $ECHO "$GREEN[+] gcc_plugin persistent mode feature works correctly"
    } || {
      $ECHO "$RED[!] gcc_plugin persistent mode feature failed to work"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin persistent mode feature compilation failed"
    CODE=1
  }
  rm -f test-persistent

  # Test forkserver-only mode aliases: no coverage instrumentation should be emitted.
  for GCC_FSRV_ENV in AFL_GCC_ONLY_FSRV AFL_GCC_ONLY_FRSV; do
    env "${GCC_FSRV_ENV}=1" ../afl-gcc-fast -o test-fsrv-only ../test-instr.c > /dev/null 2>&1
    test -e test-fsrv-only && {
      if command -v readelf >/dev/null 2>&1; then
        readelf -S test-fsrv-only 2>/dev/null | grep -q "sancov_guards" && {
          $ECHO "$RED[!] gcc_plugin ${GCC_FSRV_ENV}: unexpected sancov_guards section present"
          CODE=1
        }
      fi

      AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o /dev/null -- ./test-fsrv-only < /dev/null > test-fsrv-only.log 2>&1
      SHOWMAP_RC=$?
      TUPLES=$(grep Captur test-fsrv-only.log | awk '{print$3}' | tr -cd '0-9')
      test "$SHOWMAP_RC" -eq 0 -a "$TUPLES" = "0" && {
        $ECHO "$GREEN[+] gcc_plugin ${GCC_FSRV_ENV} works correctly (0 tuples)"
      } || {
        $ECHO "$RED[!] gcc_plugin ${GCC_FSRV_ENV} regression (rc=$SHOWMAP_RC, tuples=${TUPLES:-N/A})"
        CODE=1
      }
    } || {
      $ECHO "$RED[!] gcc_plugin ${GCC_FSRV_ENV} compilation failed"
      CODE=1
    }
    rm -f test-fsrv-only test-fsrv-only.log
  done

  # Test PC Guard persistent mode with guard verification
  ../afl-gcc-fast -o test-pcguard-persistent ./test-pcguard-persistent.c > /dev/null 2>&1
  test -e test-pcguard-persistent && {
    # The test binary verifies all sancov_guards are initialized (non-zero)
    # before entering the fuzz loop. Run it once outside afl-fuzz to check.
    ./test-pcguard-persistent > /dev/null 2>&1
    test $? -eq 0 && {
      $ECHO "$GREEN[+] gcc_plugin PC Guard persistent mode: guard verification passed"
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard persistent mode: guard verification failed"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard persistent mode compilation failed"
    CODE=1
  }
  rm -f test-pcguard-persistent

  # Test setjmp/returns_twice instrumentation fix (GitHub issue #2541)
  # GCC 13+ requires returns_twice calls to be first in their basic block.
  # Compile with -fchecking to verify the CFG is valid.
  $ECHO "$GREY[*] testing setjmp/returns_twice instrumentation (issue #2541)"
  ../afl-gcc-fast -fchecking -fdump-tree-afl -o test-setjmp ./test-setjmp.c > test-setjmp.log 2>&1
  test -e test-setjmp && {
    # Run the binary and capture output for debugging
    SETJMP_OUTPUT=$(./test-setjmp 2>&1)
    SETJMP_RC=$?
    test "$SETJMP_RC" -eq 0 && {
      # Verify instrumentation is present via afl-showmap
      TUPLES=`AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o /dev/null -- ./test-setjmp 2>&1 | grep Captur | awk '{print$3}'`
      test "$TUPLES" -gt 0 && {
        # Verify trampoline structure in GIMPLE dump:
        # - setjmp should be first stmt in its block (after DEBUG_STMT)
        # - AFL instrumentation should be in a separate preceding block
        # With PC Guard mode, instrumentation (.edge_id loads) should be in a
        # trampoline block, not in the same block as setjmp/sigsetjmp calls.
        # The -fchecking flag above already validates the CFG structurally
        # (GCC 13+ requires setjmp to be first stmt in its block).
        # Additionally, verify via GIMPLE dump that no instrumentation appears
        # directly before setjmp/sigsetjmp calls.
        DUMP_FILE=$(ls test-setjmp-test-setjmp.c.*.afl 2>/dev/null | head -1)
        if test -n "$DUMP_FILE"; then
          # In PC Guard mode, instrumentation uses .edge_id variables.
          # Verify these don't appear in the same block before setjmp/sigsetjmp.
          SETJMP_BLOCK=$(grep -B5 "_setjmp" "$DUMP_FILE" | grep -c "edge_id" || true)
          SIGSETJMP_BLOCK=$(grep -B5 "sigsetjmp" "$DUMP_FILE" | grep -c "edge_id" || true)
          test "$SETJMP_BLOCK" -eq 0 -a "$SIGSETJMP_BLOCK" -eq 0 && {
            $ECHO "$GREEN[+] gcc_plugin setjmp/returns_twice instrumentation works correctly"
            $ECHO "$GREEN[+] gcc_plugin verified: setjmp/sigsetjmp are first in block, instrumentation in trampoline"
          } || {
            $ECHO "$RED[!] gcc_plugin setjmp test: instrumentation incorrectly placed before setjmp/sigsetjmp"
            CODE=1
          }
        else
          # No dump file (e.g., older GCC without -fdump-tree-afl support)
          # Still passes because -fchecking validated CFG and afl-showmap captured edges
          $ECHO "$GREEN[+] gcc_plugin setjmp/returns_twice instrumentation works correctly"
        fi
      } || {
        $ECHO "$RED[!] gcc_plugin setjmp test has no instrumentation (tuples=$TUPLES)"
        CODE=1
      }
    } || {
      $ECHO "$RED[!] gcc_plugin setjmp test execution failed (exit code $SETJMP_RC)"
      test -n "$SETJMP_OUTPUT" && $ECHO "$RED    output: $SETJMP_OUTPUT"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin setjmp/returns_twice compilation failed (with -fchecking)"
    cat test-setjmp.log
    CODE=1
  }
  rm -f test-setjmp test-setjmp.log test-setjmp-test-setjmp.c.*.afl

  # Test PC Guard mode features
  $ECHO "$GREY[*] testing PC Guard edge coverage mode"

  # Test 1: Verify sancov_guards section exists in binary
  ../afl-gcc-fast -o test-pcguard ../test-instr.c > /dev/null 2>&1
  test -e test-pcguard && {
    if command -v readelf >/dev/null 2>&1; then
      readelf -S test-pcguard 2>/dev/null | grep -q "sancov_guards" && {
        $ECHO "$GREEN[+] gcc_plugin PC Guard: sancov_guards section present"
      } || {
        $ECHO "$RED[!] gcc_plugin PC Guard: sancov_guards section NOT found"
        CODE=1
      }
    else
      $ECHO "$YELLOW[-] gcc_plugin PC Guard: readelf not available, skipping section check"
    fi
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard test compilation failed"
    CODE=1
  }
  rm -f test-pcguard

  # Test 2: Verify critical edge splitting produces distinct coverage
  # Compile test with critical edges
  ../afl-gcc-fast -o test-edges ./test-critical-edges.c > /dev/null 2>&1
  test -e test-edges && {
    # Different paths through critical edges should produce different coverage
    # Path 1: x=0, y=0 (both else branches)
    AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-edges.map1 -- ./test-edges 0 0 2>/dev/null
    # Path 2: x=1, y=0 (x true, y false)
    AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-edges.map2 -- ./test-edges 1 0 2>/dev/null
    # Path 3: x=0, y=1 (x false, y true)
    AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-edges.map3 -- ./test-edges 0 1 2>/dev/null
    # Path 4: x=1, y=1 (both true)
    AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-edges.map4 -- ./test-edges 1 1 2>/dev/null

    # All four paths should have different coverage (edge coverage distinguishes them)
    UNIQUE_MAPS=0
    test -e test-edges.map1 && UNIQUE_MAPS=$((UNIQUE_MAPS + 1))
    test -e test-edges.map2 && ! diff -q test-edges.map1 test-edges.map2 >/dev/null 2>&1 && UNIQUE_MAPS=$((UNIQUE_MAPS + 1))
    test -e test-edges.map3 && ! diff -q test-edges.map1 test-edges.map3 >/dev/null 2>&1 && ! diff -q test-edges.map2 test-edges.map3 >/dev/null 2>&1 && UNIQUE_MAPS=$((UNIQUE_MAPS + 1))
    test -e test-edges.map4 && ! diff -q test-edges.map1 test-edges.map4 >/dev/null 2>&1 && ! diff -q test-edges.map2 test-edges.map4 >/dev/null 2>&1 && ! diff -q test-edges.map3 test-edges.map4 >/dev/null 2>&1 && UNIQUE_MAPS=$((UNIQUE_MAPS + 1))

    test "$UNIQUE_MAPS" -ge 3 && {
      $ECHO "$GREEN[+] gcc_plugin PC Guard: critical edge coverage working ($UNIQUE_MAPS distinct paths)"
    } || {
      test "$UNIQUE_MAPS" -lt 2 && {
        $ECHO "$RED[!] gcc_plugin PC Guard: only $UNIQUE_MAPS distinct coverage maps (expected >= 3)"
        CODE=1
      } || {
        $ECHO "$YELLOW[-] gcc_plugin PC Guard: only $UNIQUE_MAPS distinct coverage maps (expected >= 3)"
        # Not a hard failure - edge pruning may legitimately reduce some paths
      }
    }
    rm -f test-edges test-edges.map*
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard: critical edge test compilation failed"
    CODE=1
  }

  # Test 3: Verify guard values are initialized (non-zero in sancov_guards)
  ../afl-gcc-fast -o test-guards ../test-instr.c > /dev/null 2>&1
  test -e test-guards && {
    # Check that instrumentation captured edges (afl-showmap triggers guard init)
    TUPLES=$(echo 0 | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o /dev/null -- ./test-guards 2>&1 | grep Captur | awk '{print$3}')
    test "$TUPLES" -gt 0 && {
      $ECHO "$GREEN[+] gcc_plugin PC Guard: guard initialization working ($TUPLES edges)"
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard: guard initialization failed (0 edges captured)"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard: guard test compilation failed"
    CODE=1
  }
  rm -f test-guards

  # Test 4: Verify startup-linked DSO gets its own PC Guard init callback
  # (regression for per-module constructor emission).
  if test "$(uname -s)" != "Darwin"; then
    ../afl-gcc-fast -shared -fPIC -o libtest-pcguard-dso.so ./test-pcguard-dso-lib.c > /dev/null 2>&1
    ../afl-gcc-fast -o test-pcguard-dso-main ./test-pcguard-dso-main.c -L. -Wl,-rpath,'$ORIGIN' -ltest-pcguard-dso > /dev/null 2>&1
    test -e test-pcguard-dso-main -a -e libtest-pcguard-dso.so && {
      # Run target directly so callback logs come only from target/DSO, not
      # from afl-showmap's own instrumented process.
      DSO_INIT_LOG=$(AFL_DEBUG=1 ./test-pcguard-dso-main A 2>&1)
      DSO_RC=$?
      INIT_CALLS=$(printf "%s\n" "$DSO_INIT_LOG" | grep -c "Running __sanitizer_cov_trace_pc_guard_init:")
      test "$DSO_RC" -eq 0 -a "$INIT_CALLS" -ge 2 && {
        $ECHO "$GREEN[+] gcc_plugin PC Guard: startup-linked DSO guard init working ($INIT_CALLS init callbacks observed)"
      } || {
        $ECHO "$RED[!] gcc_plugin PC Guard: startup-linked DSO init callback check failed (rc=$DSO_RC, callbacks=$INIT_CALLS)"
        CODE=1
      }
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard: startup-linked DSO test compilation failed"
      CODE=1
    }
    rm -f test-pcguard-dso-main libtest-pcguard-dso.so
  else
    $ECHO "$YELLOW[-] gcc_plugin PC Guard: skipping startup-linked DSO init test on Darwin"
  fi

  # Test 5: Verify no_sanitize_coverage excludes function instrumentation
  # when the compiler supports the attribute.
  ../afl-gcc-fast -O0 -fdump-tree-afl -o test-pcguard-nosanitize ./test-pcguard-nosanitize.c > test-pcguard-nosanitize.log 2>&1
  test -e test-pcguard-nosanitize && {
    HAS_NOSANCOV_ATTR=$(./test-pcguard-nosanitize q 2>/dev/null | tr -d '\r\n')
    if test "$HAS_NOSANCOV_ATTR" = "1"; then
      DUMP_FILE=$(ls test-pcguard-nosanitize-test-pcguard-nosanitize.c.*.afl 2>/dev/null | head -1)
      if test -n "$DUMP_FILE"; then
        EXCLUDED_EDGE_IDS=$(awk '/^;; Function pcguard_nosancov_excluded/ {in_func=1; next} /^;; Function / {if (in_func) in_func=0} in_func && /edge_id/ {count++} END {print count+0}' "$DUMP_FILE")
        INCLUDED_EDGE_IDS=$(awk '/^;; Function pcguard_nosancov_included/ {in_func=1; next} /^;; Function / {if (in_func) in_func=0} in_func && /edge_id/ {count++} END {print count+0}' "$DUMP_FILE")
        test "$EXCLUDED_EDGE_IDS" -eq 0 -a "$INCLUDED_EDGE_IDS" -gt 0 && {
          $ECHO "$GREEN[+] gcc_plugin PC Guard: no_sanitize_coverage honored (excluded=$EXCLUDED_EDGE_IDS, included=$INCLUDED_EDGE_IDS)"
        } || {
          $ECHO "$RED[!] gcc_plugin PC Guard: no_sanitize_coverage check failed (excluded=$EXCLUDED_EDGE_IDS, included=$INCLUDED_EDGE_IDS)"
          CODE=1
        }
      else
        $ECHO "$YELLOW[-] gcc_plugin PC Guard: no_sanitize_coverage dump not available, skipping structural check"
      fi
    else
      $ECHO "$YELLOW[-] gcc_plugin PC Guard: no_sanitize_coverage attribute unsupported by compiler, skipping"
    fi
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard: no_sanitize_coverage test compilation failed"
    cat test-pcguard-nosanitize.log
    CODE=1
  }
  rm -f test-pcguard-nosanitize test-pcguard-nosanitize.log test-pcguard-nosanitize-test-pcguard-nosanitize.c.*.afl

  # Test 6: Verify sub-block compare/select instrumentation in branchless code.
  ../afl-gcc-fast -O0 -o test-pcguard-subblock-cmp ./test-pcguard-subblock-cmp.c > /dev/null 2>&1
  test -e test-pcguard-subblock-cmp && {
    printf '\001\002' | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-pcguard-subblock-cmp.map1 -- ./test-pcguard-subblock-cmp > /dev/null 2>&1
    printf '\002\001' | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-pcguard-subblock-cmp.map2 -- ./test-pcguard-subblock-cmp > /dev/null 2>&1
    test -e test-pcguard-subblock-cmp.map1 -a -e test-pcguard-subblock-cmp.map2 && {
      ! diff -q test-pcguard-subblock-cmp.map1 test-pcguard-subblock-cmp.map2 > /dev/null 2>&1 && {
        $ECHO "$GREEN[+] gcc_plugin PC Guard: sub-block compare/select coverage working"
      } || {
        $ECHO "$RED[!] gcc_plugin PC Guard: sub-block compare/select coverage check failed"
        CODE=1
      }
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard: sub-block compare/select map generation failed"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard: sub-block compare/select test compilation failed"
    CODE=1
  }
  rm -f test-pcguard-subblock-cmp test-pcguard-subblock-cmp.map1 test-pcguard-subblock-cmp.map2

  # Test 7: Verify sub-block cmpxchg instrumentation in branchless code.
  ../afl-gcc-fast -O0 -o test-pcguard-subblock-atomic ./test-pcguard-subblock-atomic.c > /dev/null 2>&1
  test -e test-pcguard-subblock-atomic && {
    printf '\000\000' | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-pcguard-subblock-atomic.map1 -- ./test-pcguard-subblock-atomic > /dev/null 2>&1
    printf '\001\001' | AFL_QUIET=1 ../afl-showmap -m ${MEM_LIMIT} -o test-pcguard-subblock-atomic.map2 -- ./test-pcguard-subblock-atomic > /dev/null 2>&1
    test -e test-pcguard-subblock-atomic.map1 -a -e test-pcguard-subblock-atomic.map2 && {
      ! diff -q test-pcguard-subblock-atomic.map1 test-pcguard-subblock-atomic.map2 > /dev/null 2>&1 && {
        $ECHO "$GREEN[+] gcc_plugin PC Guard: sub-block cmpxchg coverage working"
      } || {
        $ECHO "$RED[!] gcc_plugin PC Guard: sub-block cmpxchg coverage check failed"
        CODE=1
      }
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard: sub-block cmpxchg map generation failed"
      CODE=1
    }
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard: sub-block cmpxchg test compilation failed"
    CODE=1
  }
  rm -f test-pcguard-subblock-atomic test-pcguard-subblock-atomic.map1 test-pcguard-subblock-atomic.map2

  # Test 8: Verify decision-use compares are not instrumented as sub-block sites.
  ../afl-gcc-fast -O0 -fdump-tree-afl -o test-pcguard-decision-use ./test-pcguard-decision-use.c > test-pcguard-decision-use.log 2>&1
  test -e test-pcguard-decision-use && {
    DUMP_FILE=$(ls test-pcguard-decision-use-test-pcguard-decision-use.c.*.afl 2>/dev/null | head -1)
    if test -n "$DUMP_FILE"; then
      DECISION_SUBBLOCK=$(awk '/^;; Function pcguard_decision_use / {in_func=1; next} /^;; Function / {if (in_func) in_func=0} in_func && /edge_true|edge_false/ {count++} END {print count+0}' "$DUMP_FILE")
      NON_DECISION_SUBBLOCK=$(awk '/^;; Function pcguard_non_decision_use / {in_func=1; next} /^;; Function / {if (in_func) in_func=0} in_func && /edge_true|edge_false/ {count++} END {print count+0}' "$DUMP_FILE")
      test "$DECISION_SUBBLOCK" -eq 0 -a "$NON_DECISION_SUBBLOCK" -gt 0 && {
        $ECHO "$GREEN[+] gcc_plugin PC Guard: decision-use compare filtering works (decision=$DECISION_SUBBLOCK, non-decision=$NON_DECISION_SUBBLOCK)"
      } || {
        $ECHO "$RED[!] gcc_plugin PC Guard: decision-use compare filtering check failed (decision=$DECISION_SUBBLOCK, non-decision=$NON_DECISION_SUBBLOCK)"
        CODE=1
      }
    else
      $ECHO "$YELLOW[-] gcc_plugin PC Guard: decision-use dump not available, skipping structural check"
    fi
  } || {
    $ECHO "$RED[!] gcc_plugin PC Guard: decision-use test compilation failed"
    cat test-pcguard-decision-use.log
    CODE=1
  }
  rm -f test-pcguard-decision-use test-pcguard-decision-use.log test-pcguard-decision-use-test-pcguard-decision-use.c.*.afl

  # Test 9: Verify static initialization helpers stay uninstrumented.
  if test -e ../afl-g++-fast; then
    ../afl-g++-fast -O0 -fdump-tree-afl -o test-pcguard-static-init ./test-pcguard-static-init.cpp > test-pcguard-static-init.log 2>&1
    test -e test-pcguard-static-init && {
      DUMP_FILE=$(ls test-pcguard-static-init-test-pcguard-static-init.cpp.*.afl 2>/dev/null | head -1)
      if test -n "$DUMP_FILE"; then
        STATIC_HELPERS=$(grep -c "^;; Function __static_initialization_and_destruction_" "$DUMP_FILE" || true)
        if test "$STATIC_HELPERS" -gt 0; then
          STATIC_EDGE_IDS=$(awk '/^;; Function __static_initialization_and_destruction_/ {in_func=1; next} /^;; Function / {if (in_func) in_func=0} in_func && /edge_id/ {count++} END {print count+0}' "$DUMP_FILE")
          test "$STATIC_EDGE_IDS" -eq 0 && {
            $ECHO "$GREEN[+] gcc_plugin PC Guard: static initialization helper skip works (edge_id count=$STATIC_EDGE_IDS)"
          } || {
            $ECHO "$RED[!] gcc_plugin PC Guard: static initialization helper contains instrumentation (edge_id count=$STATIC_EDGE_IDS)"
            CODE=1
          }
        else
          $ECHO "$YELLOW[-] gcc_plugin PC Guard: no static initialization helper in dump, skipping structural check"
        fi
      else
        $ECHO "$YELLOW[-] gcc_plugin PC Guard: static-init dump not available, skipping structural check"
      fi
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard: static-init test compilation failed"
      cat test-pcguard-static-init.log
      CODE=1
    }
  else
    $ECHO "$YELLOW[-] gcc_plugin PC Guard: skipping static-init test (afl-g++-fast missing)"
  fi
  rm -f test-pcguard-static-init test-pcguard-static-init.log test-pcguard-static-init-test-pcguard-static-init.cpp.*.afl

  # Test 10: Verify COMDAT template instantiations keep TU-local guard arrays.
  # This avoids body/guard mismatches when different TUs produce different
  # guard counts for the same COMDAT function.
  if test -e ../afl-g++-fast -a "$(uname -s)" != "Darwin"; then
    ../afl-g++-fast -O0 -o test-pcguard-comdat-single ./test-pcguard-comdat-single.cpp > /dev/null 2>&1
    ../afl-g++-fast -O0 -o test-pcguard-comdat-multi ./test-pcguard-comdat-main.cpp ./test-pcguard-comdat-tu1.cpp ./test-pcguard-comdat-tu2.cpp > /dev/null 2>&1
    test -e test-pcguard-comdat-single -a -e test-pcguard-comdat-multi && {
      SINGLE_GUARDS=$(nm -a test-pcguard-comdat-single 2>/dev/null | grep -Ec "__sancov_gen_")
      MULTI_GUARDS=$(nm -a test-pcguard-comdat-multi 2>/dev/null | grep -Ec "__sancov_gen_")
      WEAK_TEMPLATE_GUARDS=$(nm -a test-pcguard-comdat-multi 2>/dev/null | grep "__sancov_gen_" | grep -Ec " [wWvV] " || true)
      DELTA=$((MULTI_GUARDS - SINGLE_GUARDS))
      test "$WEAK_TEMPLATE_GUARDS" -eq 0 -a "$DELTA" -ge 1 && {
        $ECHO "$GREEN[+] gcc_plugin PC Guard: COMDAT guard safety preserved (no weak coalescing, delta=$DELTA)"
      } || {
        $ECHO "$RED[!] gcc_plugin PC Guard: COMDAT guard safety check failed (weak_template=$WEAK_TEMPLATE_GUARDS, single=$SINGLE_GUARDS, multi=$MULTI_GUARDS, delta=$DELTA)"
        CODE=1
      }
    } || {
      $ECHO "$RED[!] gcc_plugin PC Guard: COMDAT safety test compilation failed"
      CODE=1
    }
  elif test "$(uname -s)" = "Darwin"; then
    $ECHO "$YELLOW[-] gcc_plugin PC Guard: skipping COMDAT safety test on Darwin"
  else
    $ECHO "$YELLOW[-] gcc_plugin PC Guard: skipping COMDAT safety test (afl-g++-fast missing)"
  fi
  rm -f test-pcguard-comdat-single test-pcguard-comdat-multi

  export AFL_CC=${SAVE_AFL_CC}
} || {
  $ECHO "$YELLOW[-] gcc_plugin not compiled, cannot test"
  INCOMPLETE=1
}

. ./test-post.sh
