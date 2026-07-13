/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* SHA-256 (FIPS 180-4).  The message schedule uses a 16-word ring buffer indexed
   (t-k) mod 16.

   Treated as admitted in the VST proof: the funspec is
   proof/vst/contract/trusted.v's sha256_spec, assumed via
   Axiom body_sha256 in proof/vst/contract/gprog.v. */

#include "sha256.h"
#include "util.h"

#define BLOCK SHRINCS_SHA256_BLOCK_BYTES

/* FIPS 180-4 §5.3.3 initial hash value. */
static const uint32_t H256_IV[8] = {
    0x6a09e667U,
    0xbb67ae85U,
    0x3c6ef372U,
    0xa54ff53aU,
    0x510e527fU,
    0x9b05688cU,
    0x1f83d9abU,
    0x5be0cd19U,
};

/* FIPS 180-4 §4.2.2 round constants. */
static const uint32_t K256[64] = {
    0x428a2f98U, 0x71374491U, 0xb5c0fbcfU, 0xe9b5dba5U, 0x3956c25bU, 0x59f111f1U, 0x923f82a4U, 0xab1c5ed5U,
    0xd807aa98U, 0x12835b01U, 0x243185beU, 0x550c7dc3U, 0x72be5d74U, 0x80deb1feU, 0x9bdc06a7U, 0xc19bf174U,
    0xe49b69c1U, 0xefbe4786U, 0x0fc19dc6U, 0x240ca1ccU, 0x2de92c6fU, 0x4a7484aaU, 0x5cb0a9dcU, 0x76f988daU,
    0x983e5152U, 0xa831c66dU, 0xb00327c8U, 0xbf597fc7U, 0xc6e00bf3U, 0xd5a79147U, 0x06ca6351U, 0x14292967U,
    0x27b70a85U, 0x2e1b2138U, 0x4d2c6dfcU, 0x53380d13U, 0x650a7354U, 0x766a0abbU, 0x81c2c92eU, 0x92722c85U,
    0xa2bfe8a1U, 0xa81a664bU, 0xc24b8b70U, 0xc76c51a3U, 0xd192e819U, 0xd6990624U, 0xf40e3585U, 0x106aa070U,
    0x19a4c116U, 0x1e376c08U, 0x2748774cU, 0x34b0bcb5U, 0x391c0cb3U, 0x4ed8aa4aU, 0x5b9cca4fU, 0x682e6ff3U,
    0x748f82eeU, 0x78a5636fU, 0x84c87814U, 0x8cc70208U, 0x90befffaU, 0xa4506cebU, 0xbef9a3f7U, 0xc67178f2U,
};

static inline uint32_t rotr(uint32_t x, unsigned n)
{
    return (x >> n) | (x << (32 - n));
}

static inline void to_u32s(uint32_t out[16], const uint8_t block[BLOCK])
{
    for (unsigned i = 0; i < 16; i++) {
        out[i] = ((uint32_t)block[(4 * i) + 0] << 24) | ((uint32_t)block[(4 * i) + 1] << 16) |
                 ((uint32_t)block[(4 * i) + 2] << 8) | ((uint32_t)block[(4 * i) + 3]);
    }
}

/* FIPS 180-4 §6.2.2: process one 64-byte block. */
static void shrincs_compress_block(uint32_t state[8], const uint8_t block[BLOCK])
{
    uint32_t W[16];
    to_u32s(W, block);

    uint32_t a = state[0];
    uint32_t b = state[1];
    uint32_t c = state[2];
    uint32_t d = state[3];
    uint32_t e = state[4];
    uint32_t f = state[5];
    uint32_t g = state[6];
    uint32_t h = state[7];

    for (unsigned t = 0; t < 64; t++) {
        uint32_t w_t;
        if (t < 16) {
            w_t = W[t];
        } else {
            uint32_t w15 = W[(t - 15) % 16];
            uint32_t w2 = W[(t - 2) % 16];
            uint32_t s0 = rotr(w15, 7) ^ rotr(w15, 18) ^ (w15 >> 3);
            uint32_t s1 = rotr(w2, 17) ^ rotr(w2, 19) ^ (w2 >> 10);
            w_t = W[(t - 16) % 16] + s0 + W[(t - 7) % 16] + s1;
            W[t % 16] = w_t;
        }

        uint32_t S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        uint32_t ch = (e & f) ^ (~e & g);
        uint32_t T1 = h + S1 + ch + K256[t] + w_t;

        uint32_t S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        uint32_t mj = (a & b) ^ (a & c) ^ (b & c);
        uint32_t T2 = S0 + mj;

        h = g;
        g = f;
        f = e;
        e = d + T1;
        d = c;
        c = b;
        b = a;
        a = T1 + T2;
    }

    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
    state[4] += e;
    state[5] += f;
    state[6] += g;
    state[7] += h;
}

static void shrincs_compress_blocks(uint32_t state[8], const uint8_t *blocks, size_t n)
{
    for (size_t i = 0; i < n; i++) {
        shrincs_compress_block(state, blocks + (i * BLOCK));
    }
}

void shrincs_sha256(uint8_t out[SHRINCS_SHA256_DIGEST_BYTES], const uint8_t *in, size_t inlen)
{
    SHRINCS_ASSERT(out != (void *)0);
    SHRINCS_ASSERT(in != (void *)0 || inlen == 0);
    SHRINCS_ASSERT(inlen <= ((size_t)-1) / 8);

    uint32_t state[8];
    shrincs_memcpy(state, H256_IV, sizeof state);

    size_t full = inlen / BLOCK;
    shrincs_compress_blocks(state, in, full);

    /* FIPS 180-4 §5.1.1 padding: 0x80, zeros, 64-bit BE bit-length. */
    size_t rem = inlen % BLOCK;
    uint8_t tail[2 * BLOCK];
    shrincs_memset(tail, 0, sizeof tail);
    shrincs_memcpy(tail, in + (full * BLOCK), rem);
    tail[rem] = 0x80;

    size_t end = (rem < 56) ? BLOCK : 2 * BLOCK;
    uint64_t bitlen = (uint64_t)inlen * 8U;
    for (unsigned i = 0; i < 8; i++) {
        tail[end - 1 - i] = (uint8_t)(bitlen >> (8 * i));
    }
    shrincs_compress_blocks(state, tail, end / BLOCK);

    for (unsigned i = 0; i < 8; i++) {
        out[(4 * i) + 0] = (uint8_t)(state[i] >> 24);
        out[(4 * i) + 1] = (uint8_t)(state[i] >> 16);
        out[(4 * i) + 2] = (uint8_t)(state[i] >> 8);
        out[(4 * i) + 3] = (uint8_t)(state[i]);
    }
}
