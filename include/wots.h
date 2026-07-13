/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#ifndef SHRINCS_WOTS_H
#define SHRINCS_WOTS_H

#include <stdint.h>

/* WOTS+C (grinding / constant-sum Winternitz) as used for the SHRINCS stateful (FXMSS) leaf:
   n = 16, w = 16, chain_count = 32.  Instead of a Winternitz checksum, signing grinds a 16-bit
   counter until the 32-byte message digest maps to chain_count base-w digits whose sum equals a
   fixed target (240 = floor(32 * 15 / 2)); the counter is prepended to the signature.  Every
   tweakable hash is SHA-256 truncated to 16 bytes over pk_seed || zeros(48) || ADRS || M.  See
   SECURITY.md for the threat model and shrincs-bip/impl/shrincs.py for the reference spec.

   WOTS+C is a one-time signature scheme: every (sk_seed, pk_seed, addr) triple may
   shrincs_wots_sign at most one message. */

#define SHRINCS_WOTS_SK_SEED_BYTES 16
#define SHRINCS_WOTS_PK_SEED_BYTES 16
#define SHRINCS_WOTS_MSG_BYTES     32  /* message digest (H_msg_sf output) */
#define SHRINCS_WOTS_PK_BYTES      16  /* T_sf hash of the chain tips (= n) */
#define SHRINCS_WOTS_SIG_BYTES     514 /* 2-byte counter + chain_count * n = 2 + 32*16 */
#define SHRINCS_WOTS_ADDR_BYTES    22  /* serialized ADRS length */

/* WOTS+C address (SHRINCS), 22 bytes:
     [0]       height
     [1 .. 9)  index      (big-endian)
     [9]       type byte
     [10 .. 14) reserved  (zero)
     [14 .. 18) chain index (big-endian)
     [18 .. 22) hash index  (big-endian)
   Callers prefill bytes [0 .. 9) (height + index); the WOTS+C algorithms
   set the type byte and clobber bytes [9 .. 22).

   Spelled as a raw [static restrict SHRINCS_WOTS_ADDR_BYTES] in the
   function signatures (rather than via this typedef) so the size +
   non-null + no-alias guarantees actually bind to the parameter. */
typedef uint8_t shrincs_wots_addr[SHRINCS_WOTS_ADDR_BYTES];

enum shrincs_wots_result {
    SHRINCS_WOTS_OK = 0,
    SHRINCS_WOTS_VERIFY_FAILED = -1,
    SHRINCS_WOTS_SIGN_FAILED = -2, /* grinding exhausted 2^16 counters (negligible) */
};

/* Common preconditions for all four functions:
     - all pointers non-NULL (C99 [static N] notation makes this a UB-on-violation contract the
       compiler can exploit),
     - each buffer is at least N elements as declared,
     - input/output buffers do not overlap (restrict),
     - addr's bytes [9..22) are clobbered. */

/* WOTS+C public-key generation: shrincs_wots_chain_iter every chain to w-1, then T_sf-compress
   the 32 tips to a single 16-byte public key. */
void shrincs_wots_pubkey_gen(uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                             const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                             const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                             uint8_t addr[static restrict SHRINCS_WOTS_ADDR_BYTES]);

/* WOTS+C signing: grind for a constant-sum counter, then shrincs_wots_chain_iter each secret
   up to its digit; the 16-bit counter is prepended to sig.  Returns SHRINCS_WOTS_OK, or
   SHRINCS_WOTS_SIGN_FAILED if grinding is exhausted. */
int shrincs_wots_sign(uint8_t sig[static restrict SHRINCS_WOTS_SIG_BYTES],
                      const uint8_t msg[static restrict SHRINCS_WOTS_MSG_BYTES],
                      const uint8_t sk_seed[static restrict SHRINCS_WOTS_SK_SEED_BYTES],
                      const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                      uint8_t addr[static restrict SHRINCS_WOTS_ADDR_BYTES]);

/* WOTS+C candidate public key from a signature.  Reads the counter from the head of sig,
   rejects (SHRINCS_WOTS_VERIFY_FAILED) unless the digest is constant-sum, else completes the
   chains and T_sf-compresses to a 16-byte candidate.  Prefer shrincs_wots_verify for
   verification. */
int shrincs_wots_pubkey_from_sig(uint8_t pk_cand[static restrict SHRINCS_WOTS_PK_BYTES],
                                 const uint8_t sig[static restrict SHRINCS_WOTS_SIG_BYTES],
                                 const uint8_t msg[static restrict SHRINCS_WOTS_MSG_BYTES],
                                 const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                                 uint8_t addr[static restrict SHRINCS_WOTS_ADDR_BYTES]);

/* WOTS+C signature verification (compares 16 bytes).
   Returns SHRINCS_WOTS_OK or SHRINCS_WOTS_VERIFY_FAILED. */
int shrincs_wots_verify(const uint8_t pk[static restrict SHRINCS_WOTS_PK_BYTES],
                        const uint8_t sig[static restrict SHRINCS_WOTS_SIG_BYTES],
                        const uint8_t msg[static restrict SHRINCS_WOTS_MSG_BYTES],
                        const uint8_t pk_seed[static restrict SHRINCS_WOTS_PK_SEED_BYTES],
                        uint8_t addr[static restrict SHRINCS_WOTS_ADDR_BYTES]);

#endif
