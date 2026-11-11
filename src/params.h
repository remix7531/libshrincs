/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* The scheme parameters, derived constants and ADRS type flags of the reference,
   shrincs-bip/impl/shrincs.py, under the reference's names. Internal to the library, and kept
   in one header so every scheme source reads the same definitions. */

#ifndef SHRINCS_PARAMS_H
#define SHRINCS_PARAMS_H

#define N 16 /* hash output = sha256(...)[:16] */

/* The reference's WOTS+C parameters and derived constants. */
#define WOTS_C_CHAIN_BITS   4
#define WOTS_C_CHAIN_COUNT  32    /* ceildiv(128, WOTS_C_CHAIN_BITS) */
#define WOTS_C_CHAIN_MAX    15    /* 2**WOTS_C_CHAIN_BITS - 1: the index of a chain tip */
#define WOTS_C_CONSTANT_SUM 240   /* ceildiv(WOTS_C_CHAIN_COUNT * WOTS_C_CHAIN_MAX, 2) */
#define COUNTER_BYTES       2     /* 16-bit grinding counter */
#define COUNTER_COUNT       65536 /* 2**16: grinding tries range(2**16) */

/* ADRS type flags. */
#define SF_WOTS_C_HASH  16
#define SF_WOTS_C_PK    17
#define SF_WOTS_C_PRF   21
#define SF_WOTS_C_GRIND 22

#endif
