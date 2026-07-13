/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#include "common.h"
#include "sha256.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- SHA-256 KATs ---------- */

static enum test_status test_sha256_empty(void)
{
    static const uint8_t e[32] = {0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4,
                                  0xc8, 0x99, 0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b,
                                  0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55};
    uint8_t got[32];
    shrincs_sha256(got, (const uint8_t *)"", 0);
    return memcmp(got, e, 32) == 0 ? T_OK : T_FAIL;
}

static enum test_status test_sha256_abc(void)
{
    static const uint8_t e[32] = {0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40,
                                  0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17,
                                  0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad};
    uint8_t got[32];
    shrincs_sha256(got, (const uint8_t *)"abc", 3);
    return memcmp(got, e, 32) == 0 ? T_OK : T_FAIL;
}

/* ---------- NIST CAVS .rsp parser ---------- */

static int hex_nibble(unsigned char c)
{
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    if (c >= 'a' && c <= 'f') {
        return 10 + (c - 'a');
    }
    if (c >= 'A' && c <= 'F') {
        return 10 + (c - 'A');
    }
    return -1;
}

/* Decode `n` bytes of hex from `src` into `dst`. Returns -1 on any non-hex char
   (catches truncated CAVS lines). */
static int hex_decode(const char *src, uint8_t *dst, size_t n)
{
    for (size_t i = 0; i < n; i++) {
        int hi = hex_nibble((unsigned char)src[2 * i]);
        int lo = hex_nibble((unsigned char)src[(2 * i) + 1]);
        if (hi < 0 || lo < 0) {
            return -1;
        }
        dst[i] = (uint8_t)((hi << 4) | lo);
    }
    return 0;
}

/* Parse a NIST CAVS .rsp file and run every Len/Msg/MD triple through shrincs_sha256.
   Returns the number of vectors checked via *out, and:
     -1 = parse error / digest mismatch
      0 = file not present
      1 = all vectors checked. */
static int run_sha256_cavs(const char *path, int *out)
{
    *out = 0;
    FILE *f = fopen(path, "r");
    if (!f) {
        return 0;
    }

    char *line = NULL;
    size_t line_cap = 0;
    uint8_t *msg = NULL;
    size_t msg_cap = 0;
    size_t cur_len = 0;
    int rc = 1;
    int count = 0;

    ssize_t n;
    while ((n = getline(&line, &line_cap, f)) > 0) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '[') {
            continue;
        }
        if (strncmp(line, "Len = ", 6) == 0) {
            char *end = NULL;
            unsigned long bits = strtoul(line + 6, &end, 10);
            if (end == line + 6 || (*end != '\0' && *end != '\n' && *end != '\r')) {
                rc = -1;
                break;
            }
            cur_len = bits / 8;
            if (cur_len > msg_cap) {
                uint8_t *p = realloc(msg, cur_len);
                if (!p) {
                    rc = -1;
                    break;
                }
                msg = p;
                msg_cap = cur_len;
            }
        } else if (strncmp(line, "Msg = ", 6) == 0) {
            if (cur_len && hex_decode(line + 6, msg, cur_len)) {
                rc = -1;
                break;
            }
        } else if (strncmp(line, "MD = ", 5) == 0) {
            uint8_t expected[32];
            if (hex_decode(line + 5, expected, 32)) {
                rc = -1;
                break;
            }
            uint8_t got[32];
            shrincs_sha256(got, msg, cur_len);
            if (memcmp(got, expected, 32) != 0) {
                rc = -1;
                break;
            }
            count++;
        }
    }
    free(msg);
    free(line);
    (void)fclose(f);
    *out = count;
    return rc;
}

int run_sha256_tests(void)
{
    int failures = 0;
    (void)printf("sha256\n");
    RUN(test_sha256_empty);
    RUN(test_sha256_abc);

    static const struct {
        const char *name;
        const char *path;
    } cavs[] = {
        {"test_sha256_cavs_short", "test/sha256/vectors/SHA256ShortMsg.rsp"},
        {"test_sha256_cavs_long", "test/sha256/vectors/SHA256LongMsg.rsp"},
    };
    for (size_t i = 0; i < sizeof cavs / sizeof cavs[0]; i++) {
        int kat_n = 0;
        int rc = run_sha256_cavs(cavs[i].path, &kat_n);
        if (rc == 0) {
            (void)printf("  %-28s ... SKIP (file not present)\n", cavs[i].name);
        } else if (rc == 1 && kat_n > 0) {
            (void)printf("  %-28s ... ok (%d vectors)\n", cavs[i].name, kat_n);
        } else {
            (void)printf("  %-28s ... FAIL (after %d ok)\n", cavs[i].name, kat_n);
            failures++;
        }
    }
    return failures;
}
