/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* Test harness for libshrincs.

   Runs SHA-256 KATs (including NIST CAVS vectors from test/sha256/vectors/) and WOTS+C
   self-consistency / tamper checks.  WOTS+C has no upstream RFC test vectors, so there is
   no cross-check against a reference implementation -- correctness rests on the VST proof
   (`make prove`); these tests guard the compiled binary against regressions and feed the
   sanitizer / ctgrind gates realistic inputs.

   Section drivers live in test/sha256/sha256.c and test/wots/wots.c; shared helpers in
   test/common.c. */

#include "wots.h"

#include <stdio.h>

/* Section drivers, defined in their respective TUs. */
int run_sha256_tests(void);
int run_wots_tests(void);

int main(void)
{
    (void)printf("libshrincs (WOTS+C, SHA-256)\n");

    int failures = 0;
    failures += run_sha256_tests();
    failures += run_wots_tests();

    if (failures) {
        (void)printf("%d test(s) FAILED\n", failures);
        return 1;
    }
    (void)printf("all tests passed\n");
    return 0;
}
