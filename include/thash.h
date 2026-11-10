/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* The SHRINCS tweakable hash: the one keyed-hash primitive every SHRINCS
   node type (WOTS+C chains and pk-compression, and -- once they land --
   the XMSS/FORS tree hashes) instantiates, plus the address serializer
   it consumes. Kept in its own translation unit so future scheme sources
   share it. */

#ifndef SHRINCS_THASH_H
#define SHRINCS_THASH_H

#include <stddef.h>
#include <stdint.h>

#define SHRINCS_THASH_OUT_BYTES  16 /* truncated SHA-256 output = sha256(...)[:16] */
#define SHRINCS_THASH_ADDR_BYTES 22 /* the 22-byte ADRS domain separator */
#define SHRINCS_THASH_PKSEED_PAD 48 /* pk_seed || zeros(48) fills one SHA-256 block (64) */

/* Message-length cap for the fixed-size internal buffer. Sized for the
   current WOTS+C tower (T_sf hashes CHAIN_COUNT*n = 32*16 = 512 tip
   bytes -- the largest message today). Bump this one constant as full
   SHRINCS adds larger messages (or switch to a streaming SHA-256). */
#define SHRINCS_THASH_MAX_MSG 512

/* Address.pack of the reference:
     addr := height(1) || index(8) || address_type(1) || word1(4) || word2(4) || word3(4),
   every field big-endian. Each address class of the reference is one call
   with its type flag and its payload words. */
void shrincs_adrs_pack(uint8_t addr[SHRINCS_THASH_ADDR_BYTES],
                       uint8_t height,
                       uint64_t index,
                       uint8_t address_type,
                       uint32_t word1,
                       uint32_t word2,
                       uint32_t word3);

/* The SHRINCS tweakable hash:
     out := SHA256(pk_seed || zeros(48) || addr || msg[:msglen])[:16].
   Reads addr and msg; does not mutate them. [out] must not alias [msg].
   Requires msglen <= SHRINCS_THASH_MAX_MSG. */
void shrincs_thash(uint8_t out[SHRINCS_THASH_OUT_BYTES],
                   const uint8_t pk_seed[SHRINCS_THASH_OUT_BYTES],
                   const uint8_t addr[SHRINCS_THASH_ADDR_BYTES],
                   const uint8_t *msg,
                   size_t msglen);

#endif
