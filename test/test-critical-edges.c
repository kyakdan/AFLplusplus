/*
 * Test program with critical edges for GCC plugin PC Guard testing.
 * A critical edge is an edge from a block with multiple successors
 * to a block with multiple predecessors.
 *
 * This program has multiple critical edges that should be split
 * by the PC Guard instrumentation for true edge coverage.
 */

#include <stdio.h>
#include <stdlib.h>

volatile int sink;

int main(int argc, char **argv) {
    int x = 0;
    int y = 0;

    /* Read input to control branches */
    if (argc > 1) {
        x = atoi(argv[1]);
    }
    if (argc > 2) {
        y = atoi(argv[2]);
    }

    /*
     * Critical edge example 1:
     * Both branches of the first if lead to the same second if.
     * Edge: (if x > 0 == false) -> (if y > 0) is critical
     * Edge: (if x > 0 == true)  -> (if y > 0) is critical
     */
    if (x > 0) {
        sink = 1;
    } else {
        sink = 2;
    }

    if (y > 0) {
        sink = 3;
    }

    /*
     * Critical edge example 2:
     * Switch statement - the switch block has multiple successors and the
     * merge point after the switch has multiple predecessors, creating
     * critical edges from each case to the merge point.
     */
    int result;
    switch (x) {
        case 0:  result = 10; break;
        case 1:  result = 20; break;
        case 2:  result = 30; break;
        default: result = 40; break;
    }
    sink = result;  /* Merge point with multiple predecessors */

    /*
     * Critical edge example 3:
     * Loop with multiple exits
     */
    for (int i = 0; i < 5; i++) {
        if (x == i) {
            break;  /* Edge to after-loop from inside is critical */
        }
        sink = i;
    }
    /* After loop - has preds from: loop exit condition, break */

    return sink;
}
