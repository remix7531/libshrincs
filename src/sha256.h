/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *
 * Public API of sha256.c: SHA-256 (FIPS 180-4), one-shot.
 *
 * One entry point, a pure function of its input:
 *
 *   shrincs_sha256(out, in, inlen)   the FIPS 180-4 digest
 *
 * NO STREAMING API. There is no context struct, no init/update/final,
 * and no internal buffering: the caller presents the whole message at
 * once. That is a deliberate restriction -- the streaming state and
 * its invariants are the bulk of the verification cost, and nothing
 * in this project needs them.
 */

#ifndef SHRINCS_SHA256_H
#define SHRINCS_SHA256_H

#include <stddef.h>
#include <stdint.h>

#define SHRINCS_SHA256_DIGEST_BYTES 32
#define SHRINCS_SHA256_BLOCK_BYTES  64

/* The SHA-256 digest of `in[0..inlen)`, written to `out[0..32)`.
 *
 * `out` must point to 32 writable bytes and MUST NOT OVERLAP `in`;
 * that is what the two `restrict` qualifiers say, and the funspec
 * (proof/sha256.v's spec_sha256) says the same thing via
 * the separating conjunction between its two `data_at` clauses in SEP.
 *
 * `in` must be a valid pointer even when `inlen` is 0 (it is never
 * dereferenced in that case, but the funspec's precondition still
 * asks for a 0-length array at a real address, not for NULL).
 *
 * `inlen` is bounded by 2^61 - 1 (the precondition of
 * spec_sha256), so that the message length in BITS fits the
 * 64-bit length field FIPS 180-4 SS 5.1.1 appends. The bound is far
 * beyond any address space; it is stated because the funspec must say
 * what the C actually guarantees. */
void shrincs_sha256(uint8_t out[restrict 32], const uint8_t *restrict in, size_t inlen);

#endif
