/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#include "util.h"

void *shrincs_memcpy(void *dst, const void *src, size_t n)
{
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    for (size_t i = 0; i < n; i++) {
        d[i] = s[i];
    }
    return dst;
}

void *shrincs_memset(void *dst, int byte, size_t n)
{
    uint8_t *d = (uint8_t *)dst;
    uint8_t b = (uint8_t)byte;
    for (size_t i = 0; i < n; i++) {
        d[i] = b;
    }
    return dst;
}

int shrincs_ct_memcmp(const uint8_t *a, const uint8_t *b, size_t n)
{
    uint8_t diff = 0;
    for (size_t i = 0; i < n; i++) {
        diff |= (uint8_t)(a[i] ^ b[i]);
    }
    return diff;
}

void shrincs_panic(void)
{
#ifndef __COMPCERT__
    __builtin_trap();
#endif
    for (;;) {}
}
