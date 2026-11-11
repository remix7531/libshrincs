/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* WOTS+C (grinding / constant-sum Winternitz) for the SHRINCS stateful leaf, n = 16, w = 16,
   chain_count = 32. Reference spec: shrincs-bip/impl/shrincs.py, whose function and constant
   names the code below keeps. Public API in shrincs.h. */

#include "shrincs.h"
#include "sha256.h"
#include "util.h"
#include "thash.h"
#include "params.h"

/* Enum constants, so each product and each offset is one integer constant
   and not an int expression widened into an array size or a pointer sum. */
enum {
    WOTS_C_CHAINS_SIZE = WOTS_C_CHAIN_COUNT * N, /* 32 * 16 = 512 */

    /* The H_grind preimage:
         pk_seed(16) || zeros(48) || ADRS[0..10) || digest(32) || zeros(4) || counter(2). */
    GRIND_ADRS_PREFIX = 10, /* height + index + type */
    GRIND_PAD = 4,
    GRIND_AT_PAD = N,                                          /* 16 */
    GRIND_AT_ADRS = GRIND_AT_PAD + SHRINCS_THASH_PKSEED_PAD,   /* 64 */
    GRIND_AT_DIGEST = GRIND_AT_ADRS + GRIND_ADRS_PREFIX,       /* 74 */
    GRIND_AT_ZEROS = GRIND_AT_DIGEST + SHRINCS_WOTS_MSG_BYTES, /* 106 */
    GRIND_AT_COUNTER = GRIND_AT_ZEROS + GRIND_PAD,             /* 110 */
    GRIND_BYTES = GRIND_AT_COUNTER + COUNTER_BYTES             /* 112 */
};

_Static_assert(SHRINCS_WOTS_PK_BYTES == N, "pk == n");
_Static_assert(SHRINCS_WOTS_SK_SEED_BYTES == N, "sk_seed == n");
_Static_assert(SHRINCS_WOTS_PK_SEED_BYTES == N, "pk_seed == n");
_Static_assert(SHRINCS_THASH_OUT_BYTES == N, "one hash length across the scheme");
_Static_assert(SHRINCS_WOTS_SIG_BYTES == COUNTER_BYTES + WOTS_C_CHAINS_SIZE, "sig == counter + chain_count*n");
_Static_assert(WOTS_C_CHAINS_SIZE <= SHRINCS_THASH_MAX_MSG, "T_sf's message fits the tweakable hash");

/* T_sf(pk_seed, WotsCPk(node_height, node_index), M_l): the public-key
   compression, the tweakable hash over the WOTS_C_CHAIN_COUNT chain tips. */
static void shrincs_wots_c_t_sf(uint8_t out[N],
                                const uint8_t pk_seed[N],
                                uint8_t node_height,
                                uint64_t node_index,
                                const uint8_t M_l[WOTS_C_CHAINS_SIZE])
{
    uint8_t addr[SHRINCS_THASH_ADDR_BYTES];
    shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_PK, 0, 0, 0);
    shrincs_thash(out, pk_seed, addr, M_l, WOTS_C_CHAINS_SIZE);
}

/* F(pk_seed, WotsCHash(node_height, node_index, chain_index, hash_index),
   M_1): one step of a hash chain. */
static void shrincs_wots_c_f(uint8_t out[N],
                             const uint8_t pk_seed[N],
                             uint8_t node_height,
                             uint64_t node_index,
                             uint32_t chain_index,
                             uint32_t hash_index,
                             const uint8_t M_1[N])
{
    uint8_t addr[SHRINCS_THASH_ADDR_BYTES];
    shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_HASH, 0, chain_index, hash_index);
    shrincs_thash(out, pk_seed, addr, M_1, N);
}

/* H_grind(pk_seed, WotsCGrind(node_height, node_index), digest, counter) =
     SHA256(pk_seed || zeros(48) || ADRS[0..10) || digest || zeros(4)
            || counter.to_bytes(2))[:16].
   counter is below 2**16. */
static void shrincs_wots_c_h_grind(uint8_t out[N],
                                   const uint8_t pk_seed[N],
                                   uint8_t node_height,
                                   uint64_t node_index,
                                   const uint8_t digest[SHRINCS_WOTS_MSG_BYTES],
                                   uint32_t counter)
{
    uint8_t addr[SHRINCS_THASH_ADDR_BYTES];
    uint8_t buf[GRIND_BYTES];
    uint8_t hash[SHRINCS_SHA256_DIGEST_BYTES];
    shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_GRIND, 0, 0, 0);
    shrincs_memcpy(buf, pk_seed, N);
    shrincs_memset(buf + GRIND_AT_PAD, 0, SHRINCS_THASH_PKSEED_PAD);
    shrincs_memcpy(buf + GRIND_AT_ADRS, addr, GRIND_ADRS_PREFIX);
    shrincs_memcpy(buf + GRIND_AT_DIGEST, digest, SHRINCS_WOTS_MSG_BYTES);
    shrincs_memset(buf + GRIND_AT_ZEROS, 0, GRIND_PAD);
    buf[GRIND_AT_COUNTER] = (uint8_t)(counter >> 8);
    buf[GRIND_AT_COUNTER + 1] = (uint8_t)(counter);
    shrincs_sha256(hash, buf, GRIND_BYTES);
    shrincs_memcpy(out, hash, N);
}

/* PRF(pk_seed, sk_seed, WotsCPrf(node_height, node_index, tree_balanced,
   tree_depth, chain_index)): the secret start of one chain. */
static void shrincs_wots_c_prf(uint8_t out[N],
                               const uint8_t pk_seed[N],
                               const uint8_t sk_seed[N],
                               uint8_t node_height,
                               uint64_t node_index,
                               bool tree_balanced,
                               uint8_t tree_depth,
                               uint32_t chain_index)
{
    uint8_t addr[SHRINCS_THASH_ADDR_BYTES];
    /* WotsCPrf.to_bytes: word1 = int(tree_balanced) * 2**24 + tree_depth * 2**16. */
    uint32_t word1 = ((uint32_t)tree_balanced << 24) + ((uint32_t)tree_depth << 16);
    shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_PRF, word1, chain_index, 0);
    shrincs_thash(out, pk_seed, addr, sk_seed, N);
}

/* wots_c_chain_iter: iterates the hash chain in place from index start to
   index stop, one F per step, each step tweaked by
   WotsCHash(node_height, node_index, chain_index, j).
   Requires start <= stop <= WOTS_C_CHAIN_MAX. */
static void shrincs_wots_c_chain_iter(uint8_t node[N],
                                      uint32_t start,
                                      uint32_t stop,
                                      const uint8_t pk_seed[N],
                                      uint8_t node_height,
                                      uint64_t node_index,
                                      uint32_t chain_index)
{
    for (uint32_t j = start; j < stop; j++) {
        uint8_t previous[N];
        shrincs_memcpy(previous, node, N);
        shrincs_wots_c_f(node, pk_seed, node_height, node_index, chain_index, j, previous);
    }
}

/* base_2b(x, WOTS_C_CHAIN_BITS, WOTS_C_CHAIN_COUNT) for the N-byte x: the
   base-16 digits of x, so each byte gives its high nibble and then its low
   nibble. */
static void shrincs_wots_c_base_2b(uint8_t indexes[WOTS_C_CHAIN_COUNT], const uint8_t x[N])
{
    for (uint32_t i = 0; i < N; i++) {
        indexes[(2 * i) + 0] = (uint8_t)(x[i] >> 4);
        indexes[(2 * i) + 1] = (uint8_t)(x[i] & 0x0f);
    }
}

/* wots_c_map_digest: writes the WOTS_C_CHAIN_COUNT indexes that H_grind
   maps the digest to at counter. Returns 1 if they sum to
   WOTS_C_CONSTANT_SUM and 0 otherwise, where the reference returns the
   indexes or None. counter is below 2**16. */
static int shrincs_wots_c_map_digest(uint8_t indexes[WOTS_C_CHAIN_COUNT],
                                     const uint8_t pk_seed[N],
                                     const uint8_t message_digest[SHRINCS_WOTS_MSG_BYTES],
                                     uint8_t node_height,
                                     uint64_t node_index,
                                     uint32_t counter)
{
    uint8_t hashed[N];
    shrincs_wots_c_h_grind(hashed, pk_seed, node_height, node_index, message_digest, counter);
    shrincs_wots_c_base_2b(indexes, hashed);
    uint32_t sum = 0;
    for (uint32_t i = 0; i < WOTS_C_CHAIN_COUNT; i++) {
        sum += indexes[i];
    }
    if (sum != WOTS_C_CONSTANT_SUM) {
        return 0;
    }
    return 1;
}

/* wots_c_grind_to_constant_sum: grinds for the smallest counter below 2**16
   whose indexes sum to WOTS_C_CONSTANT_SUM. Returns that counter and leaves
   its indexes written, or returns -1 on exhaustion (negligible probability),
   where the reference returns None. */
static int shrincs_wots_c_grind_to_constant_sum(uint8_t indexes[WOTS_C_CHAIN_COUNT],
                                                const uint8_t pk_seed[N],
                                                const uint8_t message_digest[SHRINCS_WOTS_MSG_BYTES],
                                                uint8_t node_height,
                                                uint64_t node_index)
{
    for (uint32_t i = 0; i < COUNTER_COUNT; i++) {
        if (shrincs_wots_c_map_digest(indexes, pk_seed, message_digest, node_height, node_index, i) != 0) {
            return (int)i;
        }
    }
    return -1;
}

void shrincs_wots_c_pubkey_gen(uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                               const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                               const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                               uint8_t node_height,
                               uint64_t node_index,
                               bool tree_balanced,
                               uint8_t tree_depth)
{
    uint8_t wots_pk[WOTS_C_CHAINS_SIZE];
    for (uint32_t i = 0; i < WOTS_C_CHAIN_COUNT; i++) {
        uint8_t *tip = wots_pk + ((size_t)i * N);
        shrincs_wots_c_prf(tip, pk_seed, sk_seed, node_height, node_index, tree_balanced, tree_depth, i);
        shrincs_wots_c_chain_iter(tip, 0, WOTS_C_CHAIN_MAX, pk_seed, node_height, node_index, i);
    }
    shrincs_wots_c_t_sf(pk, pk_seed, node_height, node_index, wots_pk);
}

int shrincs_wots_c_sign(uint8_t signature[static restrict SHRINCS_WOTS_SIG_BYTES],
                        const uint8_t message_digest[static restrict SHRINCS_WOTS_MSG_BYTES],
                        const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                        const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                        uint8_t node_height,
                        uint64_t node_index,
                        bool tree_balanced,
                        uint8_t tree_depth)
{
    uint8_t indexes[WOTS_C_CHAIN_COUNT];
    int grinded = shrincs_wots_c_grind_to_constant_sum(indexes, pk_seed, message_digest, node_height, node_index);
    if (grinded < 0) {
        return SHRINCS_SIGN_FAILED;
    }
    /* counter.to_bytes(2) is prepended; the chains follow from byte 2. */
    uint32_t counter = (uint32_t)grinded;
    signature[0] = (uint8_t)(counter >> 8);
    signature[1] = (uint8_t)(counter);
    for (uint32_t i = 0; i < WOTS_C_CHAIN_COUNT; i++) {
        uint8_t *chain = signature + COUNTER_BYTES + ((size_t)i * N);
        shrincs_wots_c_prf(chain, pk_seed, sk_seed, node_height, node_index, tree_balanced, tree_depth, i);
        shrincs_wots_c_chain_iter(chain, 0, indexes[i], pk_seed, node_height, node_index, i);
    }
    return SHRINCS_OK;
}

int shrincs_wots_c_pubkey_from_sig(uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                                   const uint8_t signature[static restrict SHRINCS_WOTS_SIG_BYTES],
                                   const uint8_t message_digest[static restrict SHRINCS_WOTS_MSG_BYTES],
                                   const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                                   uint8_t node_height,
                                   uint64_t node_index)
{
    uint8_t indexes[WOTS_C_CHAIN_COUNT];
    uint8_t wots_pk[WOTS_C_CHAINS_SIZE];
    /* int.from_bytes(signature[0:2]) */
    uint32_t counter = ((uint32_t)signature[0] << 8) + (uint32_t)signature[1];
    /* Constant-sum gate: reject unless the digest at counter sums to the target. */
    if (shrincs_wots_c_map_digest(indexes, pk_seed, message_digest, node_height, node_index, counter) == 0) {
        return SHRINCS_VERIFY_FAILED;
    }
    for (uint32_t i = 0; i < WOTS_C_CHAIN_COUNT; i++) {
        uint8_t *tip = wots_pk + ((size_t)i * N);
        shrincs_memcpy(tip, signature + COUNTER_BYTES + ((size_t)i * N), N);
        shrincs_wots_c_chain_iter(tip, indexes[i], WOTS_C_CHAIN_MAX, pk_seed, node_height, node_index, i);
    }
    shrincs_wots_c_t_sf(pk, pk_seed, node_height, node_index, wots_pk);
    return SHRINCS_OK;
}
