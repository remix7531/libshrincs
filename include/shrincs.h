/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#ifndef SHRINCS_H
#define SHRINCS_H

#include <stdbool.h>
#include <stdint.h>

/* WOTS+C (grinding / constant-sum Winternitz) as used for the SHRINCS stateful (FXMSS) leaf:
   n = 16, w = 16, chain_count = 32.  Instead of a Winternitz checksum, signing grinds a 16-bit
   counter until the 32-byte message digest maps to chain_count base-w digits whose sum equals a
   fixed target (240 = floor(32 * 15 / 2)); the counter is prepended to the signature.  Every
   tweakable hash is SHA-256 truncated to 16 bytes over pk_seed || zeros(48) || ADRS || M.

   The three functions below are wots_c_pubkey_gen, wots_c_sign and wots_c_pubkey_from_sig of
   shrincs-bip/impl/shrincs.py, with the result as the first parameter and the reference's
   parameters after it, in the reference's order and under the reference's names.

   WOTS+C is a one-time signature scheme: every (sk_seed, pk_seed, node_height, node_index)
   tuple may shrincs_wots_c_sign at most one message. */

#define SHRINCS_WOTS_SK_SEED_BYTES 16
#define SHRINCS_WOTS_PK_SEED_BYTES 16
#define SHRINCS_WOTS_MSG_BYTES     32  /* message digest (H_msg_sf output) */
#define SHRINCS_WOTS_PK_BYTES      16  /* T_sf hash of the chain tips (= n) */
#define SHRINCS_WOTS_SIG_BYTES     514 /* 2-byte counter + chain_count * n = 2 + 32*16 */

enum shrincs_status {
    SHRINCS_OK = 0,
    SHRINCS_VERIFY_FAILED = -1, /* the reference's None from wots_c_pubkey_from_sig */
    SHRINCS_SIGN_FAILED = -2,   /* grinding exhausted 2^16 counters (negligible) */
};

/* Common preconditions for all three functions:
     - all pointers non-NULL (C99 [static N] notation makes this a UB-on-violation contract the
       compiler can exploit),
     - each buffer is at least N elements as declared,
     - input/output buffers do not overlap (restrict).
   node_height and node_index locate the WOTS+C leaf in the FXMSS tree. tree_balanced and
   tree_depth describe that tree and enter the secret-key derivation only. */

/* WOTS+C public-key generation: iterate every chain to its last index, then T_sf-compress
   the 32 tips to a single 16-byte public key. */
void shrincs_wots_c_pubkey_gen(uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                               const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                               const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                               uint8_t node_height,
                               uint64_t node_index,
                               bool tree_balanced,
                               uint8_t tree_depth);

/* WOTS+C signing: grind for the smallest constant-sum counter, then iterate each chain secret
   up to its index; the 16-bit counter is prepended to the signature.  Returns SHRINCS_OK,
   or SHRINCS_SIGN_FAILED if grinding is exhausted, in which case signature is
   unspecified. */
int shrincs_wots_c_sign(uint8_t signature[static restrict SHRINCS_WOTS_SIG_BYTES],
                        const uint8_t message_digest[static restrict SHRINCS_WOTS_MSG_BYTES],
                        const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                        const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                        uint8_t node_height,
                        uint64_t node_index,
                        bool tree_balanced,
                        uint8_t tree_depth);

/* WOTS+C public key from a signature.  Reads the counter from the head of signature, returns
   SHRINCS_VERIFY_FAILED unless the digest is constant-sum, else completes the chains and
   T_sf-compresses to the 16-byte public key the signature commits to and returns
   SHRINCS_OK.  The caller compares pk with the expected public key.  On
   SHRINCS_VERIFY_FAILED pk is unspecified. */
int shrincs_wots_c_pubkey_from_sig(uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                                   const uint8_t signature[static restrict SHRINCS_WOTS_SIG_BYTES],
                                   const uint8_t message_digest[static restrict SHRINCS_WOTS_MSG_BYTES],
                                   const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                                   uint8_t node_height,
                                   uint64_t node_index);

#endif
