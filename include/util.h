/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#ifndef SHRINCS_UTIL_H
#define SHRINCS_UTIL_H

#include <stddef.h>
#include <stdint.h>

/* Byte copy. In-tree replacement for libc memcpy, so VST can discharge it from a real proof
   body. Buffers must not overlap. */
void *shrincs_memcpy(void *dst, const void *src, size_t n);

/* Byte fill. In-tree replacement for libc memset, so VST can discharge it from a real proof body. */
void *shrincs_memset(void *dst, int byte, size_t n);

/* Byte compare. Returns 0 iff equal. Used by shrincs_wots_verify, whose inputs are public;
   no constant-time guarantee is implied. */
int shrincs_ct_memcmp(const uint8_t *a, const uint8_t *b, size_t n);

/* Trap on contract violation. Triggered by SHRINCS_ASSERT; does not return. Uses __builtin_trap
   (defined-behavior abort on GCC, Clang and CompCert) with a trailing infinite loop as a
   fallback if the compiler ever fails to mark it noreturn. Unreachable from VST-proven code:
   the only SHRINCS_ASSERT sites are in sha256.c, whose body is axiomatized (body_sha256),
   not proved against; shrincs_panic's own funspec carries PROP(False), so no proven body
   can reach a call to it. */
void shrincs_panic(void);

#ifndef SHRINCS_CHECKS
#define SHRINCS_CHECKS 1
#endif

#if SHRINCS_CHECKS
#define SHRINCS_ASSERT(cond) \
    do {                     \
        if (!(cond))         \
            shrincs_panic(); \
    } while (0)
#else
#define SHRINCS_ASSERT(cond) ((void)0)
#endif

#endif
