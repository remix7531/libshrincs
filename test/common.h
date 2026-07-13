/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#ifndef SHRINCS_WOTS_TEST_COMMON_H
#define SHRINCS_WOTS_TEST_COMMON_H

#include "wots.h"

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

enum test_status { T_OK, T_FAIL, T_SKIP, T_ERROR };

const char *status_str(enum test_status s);

/* CSPRNG: getrandom(2) with EINTR retry; /dev/urandom fallback. */
int fill_random(uint8_t *buf, size_t n);
int read_exact(FILE *f, void *buf, size_t n);
void unpack_addr(shrincs_wots_addr addr, const uint8_t bytes[22]);
void zero_addr(shrincs_wots_addr addr);

/* RUN(T): invoke T, print "T ... <status>", bump local `failures` on T_FAIL / T_ERROR.
   Caller must have an `int failures` in scope. */
#define RUN(T)                                                \
    do {                                                      \
        enum test_status _s = T();                            \
        (void)printf("  %-28s ... %s\n", #T, status_str(_s)); \
        if (_s == T_FAIL || _s == T_ERROR) {                  \
            failures++;                                       \
        }                                                     \
    } while (0)

#endif
