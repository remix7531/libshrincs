/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* The build defines _DEFAULT_SOURCE (for getrandom(2) and getline(3)) so
   every test TU sees the same feature-test gates. */

#include "common.h"

#include <errno.h>
#include <stdio.h>
#include <sys/random.h>
#include <unistd.h>

const char *status_str(enum test_status s)
{
    switch (s) {
        case T_OK:
            return "ok";
        case T_FAIL:
            return "FAIL";
        case T_SKIP:
            return "SKIP";
        case T_ERROR:
            return "ERROR";
    }
    return "?";
}

int fill_random(uint8_t *buf, size_t n)
{
    size_t off = 0;
    while (off < n) {
        ssize_t r = getrandom(buf + off, n - off, 0);
        if (r < 0) {
            if (errno == EINTR) {
                continue;
            }
            if (errno == ENOSYS) {
                break;
            }
            return -1;
        }
        if (r == 0) {
            break;
        } /* shouldn't happen on urandom; fall back */
        off += (size_t)r;
    }
    if (off == n) {
        return 0;
    }
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) {
        return -1;
    }
    int rc = fread(buf + off, 1, n - off, f) == (n - off) ? 0 : -1;
    (void)fclose(f);
    return rc;
}

int read_exact(FILE *f, void *buf, size_t n)
{
    return fread(buf, 1, n, f) == n ? 0 : -1;
}
