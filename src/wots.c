/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* WOTS+C (grinding / constant-sum Winternitz) for the SHRINCS stateful leaf, n = 16, w = 16,
   chain_count = 32. Reference spec: shrincs-bip/impl/shrincs.py. Public API in wots.h, threat
   model in SECURITY.md. */

#include "wots.h"
#include "sha256.h"
#include "util.h"
#include "thash.h"

/* SHRINCS WOTS+C parameters. */
#define N                         16  /* hash output = sha256(...)[:16] */
#define W                         16  /* Winternitz radix */
#define CHAIN_COUNT               32  /* number of hash chains (= digits) */
#define SHRINCS_WOTS_CONSTANT_SUM 240 /* floor(CHAIN_COUNT * (W-1) / 2): constant digit sum */
#define COUNTER_BYTES             2   /* 16-bit grinding counter */
#define PKSEED_PAD                48  /* pk_seed || zeros(48) = one SHA-256 block (64) */
#define GRIND_PREFIX              10  /* shrincs_wots_h_grind hashes ADRS[0..10): height+index+type */
#define GRIND_PAD                 4   /* zeros between the digest and the counter */

/* ADRS type bytes (SHRINCS §"ADRS type flags"). */
#define SF_SHRINCS_WOTS_HASH  16
#define SF_SHRINCS_WOTS_PK    17
#define SF_SHRINCS_WOTS_PRF   21
#define SF_SHRINCS_WOTS_GRIND 22

/* ADRS byte offsets. */
#define ADRS_TYPE     9
#define ADRS_RESERVED 10
#define ADRS_CHAIN    14
#define ADRS_HASH     18

/* Concatenated chain tips fed to T_sf (as an enum constant so the
   product is not an int-multiplication widened into an array size). */
enum { ENDS_BYTES = CHAIN_COUNT * N }; /* 32 * 16 = 512 */

_Static_assert(SHRINCS_WOTS_PK_BYTES == N, "pk == n");
_Static_assert(SHRINCS_WOTS_SIG_BYTES == COUNTER_BYTES + (CHAIN_COUNT * N), "sig == counter + chain_count*n");
_Static_assert(SHRINCS_WOTS_ADDR_BYTES == SHRINCS_THASH_ADDR_BYTES, "one 22-byte ADRS format across the scheme");

/* WOTS+C public-key compression: the tweakable hash over the CHAIN_COUNT
   chain tips. A thin wrapper over the shared shrincs_thash at message
   length ENDS_BYTES. Reads addr; does not mutate it. */
static void shrincs_wots_t_sf(uint8_t out[N],
                              const uint8_t pk_seed[N],
                              const uint8_t addr[SHRINCS_WOTS_ADDR_BYTES],
                              const uint8_t ends[ENDS_BYTES])
{
    shrincs_thash(out, pk_seed, addr, ends, ENDS_BYTES);
}

/* H_grind(pk_seed, ADRS, msg, counter) =
     SHA256(pk_seed || zeros(48) || ADRS[0..10) || msg || zeros(4)
            || toByte(counter,2))[:16].
   Reads addr[0..10) (height + index + type); the caller sets the type
   byte.  Does not mutate addr. */
static void shrincs_wots_h_grind(uint8_t out[N],
                                 const uint8_t msg[SHRINCS_WOTS_MSG_BYTES],
                                 uint32_t counter,
                                 const uint8_t pk_seed[N],
                                 const uint8_t addr[SHRINCS_WOTS_ADDR_BYTES])
{
    uint8_t buf[N + PKSEED_PAD + GRIND_PREFIX + SHRINCS_WOTS_MSG_BYTES + GRIND_PAD +
                COUNTER_BYTES]; /* 16+48+10+32+4+2 = 112 */
    uint8_t hash[SHRINCS_SHA256_DIGEST_BYTES];
    unsigned off = 0;
    shrincs_memcpy(buf + off, pk_seed, N);
    off += N;
    shrincs_memset(buf + off, 0, PKSEED_PAD);
    off += PKSEED_PAD;
    shrincs_memcpy(buf + off, addr, GRIND_PREFIX);
    off += GRIND_PREFIX;
    shrincs_memcpy(buf + off, msg, SHRINCS_WOTS_MSG_BYTES);
    off += SHRINCS_WOTS_MSG_BYTES;
    shrincs_memset(buf + off, 0, GRIND_PAD);
    off += GRIND_PAD;
    buf[off + 0] = (uint8_t)(counter >> 8);
    buf[off + 1] = (uint8_t)(counter);
    shrincs_sha256(hash, buf, sizeof buf);
    shrincs_memcpy(out, hash, N);
}

/* sk_i = PRF(pk_seed, sk_seed, ADRS) with the ADRS typed for the WOTS+C PRF, chain index i,
   zero reserved + hash index. Sets addr[9..22). */
static void shrincs_wots_derive_sk(uint8_t out[N],
                                   unsigned chain_i,
                                   const uint8_t sk_seed[N],
                                   const uint8_t pk_seed[N],
                                   uint8_t addr[SHRINCS_WOTS_ADDR_BYTES])
{
    addr[ADRS_TYPE] = SF_SHRINCS_WOTS_PRF;
    shrincs_adrs_put32(addr, ADRS_RESERVED, 0);
    shrincs_adrs_put32(addr, ADRS_CHAIN, (uint32_t)chain_i);
    shrincs_adrs_put32(addr, ADRS_HASH, 0);
    shrincs_thash(out, pk_seed, addr, sk_seed, N);
}

/* WOTS+C hash chain: F iterated `steps` times from index `start`. The caller sets
   addr[ADRS_TYPE] and the chain index first; this writes the hash index addr[18..22) on
   each step. */
static void shrincs_wots_chain_iter(
    uint8_t node[N], unsigned start, unsigned steps, const uint8_t pk_seed[N], uint8_t addr[SHRINCS_WOTS_ADDR_BYTES])
{
    for (unsigned j = 0; j < steps; j++) {
        uint8_t in[N];
        shrincs_adrs_put32(addr, ADRS_HASH, (uint32_t)(start + j));
        shrincs_memcpy(in, node, N);
        shrincs_thash(node, pk_seed, addr, in, N);
    }
}

/* Per-chain kernel shared by pubkey_gen and signing: derive the chain secret sk_i
   (PRF-typed ADRS), re-type the ADRS to the WOTS+C hash, then run its hash chain `steps`
   steps from index 0. Sets addr[9..22). */
static void shrincs_wots_chain_from_seed(uint8_t node[N],
                                         unsigned chain_i,
                                         unsigned steps,
                                         const uint8_t sk_seed[N],
                                         const uint8_t pk_seed[N],
                                         uint8_t addr[SHRINCS_WOTS_ADDR_BYTES])
{
    shrincs_wots_derive_sk(node, chain_i, sk_seed, pk_seed, addr);
    addr[ADRS_TYPE] = SF_SHRINCS_WOTS_HASH;
    shrincs_wots_chain_iter(node, 0, steps, pk_seed, addr);
}

/* Write the CHAIN_COUNT base-16 digits of H_grind(...,counter) (MSB-first nibbles of the
   16-byte grind output) and return their sum (<= CHAIN_COUNT * (W-1) = 480). Sets
   addr[ADRS_TYPE] = grind. */
static unsigned shrincs_wots_map_digest(uint8_t digits[CHAIN_COUNT],
                                        const uint8_t msg[SHRINCS_WOTS_MSG_BYTES],
                                        uint32_t counter,
                                        const uint8_t pk_seed[N],
                                        uint8_t addr[SHRINCS_WOTS_ADDR_BYTES])
{
    uint8_t hg[N];
    addr[ADRS_TYPE] = SF_SHRINCS_WOTS_GRIND;
    shrincs_wots_h_grind(hg, msg, counter, pk_seed, addr);
    for (unsigned i = 0; i < N; i++) {
        digits[(2 * i) + 0] = (uint8_t)(hg[i] >> 4);
        digits[(2 * i) + 1] = (uint8_t)(hg[i] & 0x0f);
    }
    unsigned sum = 0;
    for (unsigned i = 0; i < CHAIN_COUNT; i++) {
        sum += digits[i];
    }
    return sum;
}

/* Grind for the SMALLEST counter < 2^16 whose digits sum to SHRINCS_WOTS_CONSTANT_SUM. On
   success writes the digits and *counter_out and returns 0; returns 1 on exhaustion
   (negligible probability). counter is a uint64 so the bound is an exact 2^16 with no
   wraparound. */
static int shrincs_wots_grind_to_constant_sum(uint8_t digits[CHAIN_COUNT],
                                              uint32_t *counter_out,
                                              const uint8_t msg[SHRINCS_WOTS_MSG_BYTES],
                                              const uint8_t pk_seed[N],
                                              uint8_t addr[SHRINCS_WOTS_ADDR_BYTES])
{
    uint64_t counter = 0;
    while (counter < ((uint64_t)1 << 16)) {
        if (shrincs_wots_map_digest(digits, msg, (uint32_t)counter, pk_seed, addr) == SHRINCS_WOTS_CONSTANT_SUM) {
            *counter_out = (uint32_t)counter;
            return 0;
        }
        counter++;
    }
    return 1;
}

void shrincs_wots_pubkey_gen(uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                             const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                             const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                             uint8_t addr[static restrict 22])
{
    uint8_t ends[ENDS_BYTES];
    for (unsigned i = 0; i < CHAIN_COUNT; i++) {
        uint8_t *tip = ends + ((size_t)i * N);
        shrincs_wots_chain_from_seed(tip, i, W - 1, sk_seed, pk_seed, addr);
    }
    addr[ADRS_TYPE] = SF_SHRINCS_WOTS_PK;
    shrincs_adrs_put32(addr, ADRS_CHAIN, 0);
    shrincs_adrs_put32(addr, ADRS_HASH, 0);
    shrincs_wots_t_sf(pk, pk_seed, addr, ends);
}

int shrincs_wots_sign(uint8_t sig[static restrict SHRINCS_WOTS_SIG_BYTES],
                      const uint8_t msg[static restrict SHRINCS_WOTS_MSG_BYTES],
                      const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                      const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                      uint8_t addr[static restrict 22])
{
    uint8_t digits[CHAIN_COUNT];
    uint32_t counter;
    if (shrincs_wots_grind_to_constant_sum(digits, &counter, msg, pk_seed, addr) != 0) {
        return SHRINCS_WOTS_SIGN_FAILED;
    }
    /* 2-byte big-endian counter is prepended; the chains follow from byte 2. */
    sig[0] = (uint8_t)(counter >> 8);
    sig[1] = (uint8_t)(counter);
    for (unsigned i = 0; i < CHAIN_COUNT; i++) {
        uint8_t *chain = sig + COUNTER_BYTES + ((size_t)i * N);
        shrincs_wots_chain_from_seed(chain, i, digits[i], sk_seed, pk_seed, addr);
    }
    return SHRINCS_WOTS_OK;
}

int shrincs_wots_pubkey_from_sig(uint8_t pk_cand[static restrict SHRINCS_WOTS_PK_BYTES],
                                 const uint8_t sig[static restrict SHRINCS_WOTS_SIG_BYTES],
                                 const uint8_t msg[static restrict SHRINCS_WOTS_MSG_BYTES],
                                 const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                                 uint8_t addr[static restrict 22])
{
    uint8_t digits[CHAIN_COUNT];
    /* 2-byte big-endian counter is at the head of sig; chains follow from byte 2. */
    uint32_t counter = ((uint32_t)sig[0] << 8) | ((uint32_t)sig[1]);
    /* Constant-sum gate: reject unless the digest at counter sums to the target. */
    if (shrincs_wots_map_digest(digits, msg, counter, pk_seed, addr) != SHRINCS_WOTS_CONSTANT_SUM) {
        return SHRINCS_WOTS_VERIFY_FAILED;
    }
    uint8_t ends[ENDS_BYTES];
    /* Copy all CHAIN_COUNT raw tips out of the signature in one shot, then
       complete each chain in place -- the loop never touches sig again. */
    shrincs_memcpy(ends, sig + COUNTER_BYTES, ENDS_BYTES);
    addr[ADRS_TYPE] = SF_SHRINCS_WOTS_HASH;
    shrincs_adrs_put32(addr, ADRS_RESERVED, 0);
    for (unsigned i = 0; i < CHAIN_COUNT; i++) {
        uint8_t *tip = ends + ((size_t)i * N);
        shrincs_adrs_put32(addr, ADRS_CHAIN, (uint32_t)i);
        shrincs_wots_chain_iter(tip, digits[i], (W - 1) - digits[i], pk_seed, addr);
    }
    addr[ADRS_TYPE] = SF_SHRINCS_WOTS_PK;
    shrincs_adrs_put32(addr, ADRS_CHAIN, 0);
    shrincs_adrs_put32(addr, ADRS_HASH, 0);
    shrincs_wots_t_sf(pk_cand, pk_seed, addr, ends);
    return SHRINCS_WOTS_OK;
}

int shrincs_wots_verify(const uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                        const uint8_t sig[static restrict SHRINCS_WOTS_SIG_BYTES],
                        const uint8_t msg[static restrict SHRINCS_WOTS_MSG_BYTES],
                        const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                        uint8_t addr[static restrict 22])
{
    uint8_t pk_cand[SHRINCS_WOTS_PK_BYTES];
    if (shrincs_wots_pubkey_from_sig(pk_cand, sig, msg, pk_seed, addr) != SHRINCS_WOTS_OK) {
        return SHRINCS_WOTS_VERIFY_FAILED;
    }
    return (shrincs_ct_memcmp(pk_cand, pk, SHRINCS_WOTS_PK_BYTES) == 0) ? SHRINCS_WOTS_OK : SHRINCS_WOTS_VERIFY_FAILED;
}
