/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#ifndef SHRINCS_SHA256_H
#define SHRINCS_SHA256_H

#include <stddef.h>
#include <stdint.h>

#define SHRINCS_SHA256_DIGEST_BYTES 32
#define SHRINCS_SHA256_BLOCK_BYTES  64

/* One-shot SHA-256 (FIPS 180-4).
     out:   non-NULL, >= 32 writable bytes
     in:    non-NULL or inlen == 0
     inlen: <= SIZE_MAX / 8 */
void shrincs_sha256(uint8_t out[SHRINCS_SHA256_DIGEST_BYTES], const uint8_t *in, size_t inlen);

#endif
