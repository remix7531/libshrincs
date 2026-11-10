/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* The SHRINCS tweakable hash and its address serializer. Reference spec:
   shrincs-bip/impl/shrincs.py. Shared across all SHRINCS node types. */

#include "thash.h"
#include "sha256.h"
#include "util.h"

void shrincs_adrs_pack(uint8_t addr[SHRINCS_THASH_ADDR_BYTES],
                       uint8_t height,
                       uint64_t index,
                       uint8_t address_type,
                       uint32_t word1,
                       uint32_t word2,
                       uint32_t word3)
{
    addr[0] = height;
    addr[1] = (uint8_t)(index >> 56);
    addr[2] = (uint8_t)(index >> 48);
    addr[3] = (uint8_t)(index >> 40);
    addr[4] = (uint8_t)(index >> 32);
    addr[5] = (uint8_t)(index >> 24);
    addr[6] = (uint8_t)(index >> 16);
    addr[7] = (uint8_t)(index >> 8);
    addr[8] = (uint8_t)(index);
    addr[9] = address_type;
    addr[10] = (uint8_t)(word1 >> 24);
    addr[11] = (uint8_t)(word1 >> 16);
    addr[12] = (uint8_t)(word1 >> 8);
    addr[13] = (uint8_t)(word1);
    addr[14] = (uint8_t)(word2 >> 24);
    addr[15] = (uint8_t)(word2 >> 16);
    addr[16] = (uint8_t)(word2 >> 8);
    addr[17] = (uint8_t)(word2);
    addr[18] = (uint8_t)(word3 >> 24);
    addr[19] = (uint8_t)(word3 >> 16);
    addr[20] = (uint8_t)(word3 >> 8);
    addr[21] = (uint8_t)(word3);
}

/* The preimage pk_seed(16) || zeros(48) || addr(22) || msg(msglen). Enum
   constants, so each offset is one integer constant in a pointer sum. */
enum {
    THASH_AT_PAD = SHRINCS_THASH_OUT_BYTES,                  /* 16 */
    THASH_AT_ADDR = THASH_AT_PAD + SHRINCS_THASH_PKSEED_PAD, /* 64 */
    THASH_AT_MSG = THASH_AT_ADDR + SHRINCS_THASH_ADDR_BYTES, /* 86 */
    THASH_BUF_BYTES = THASH_AT_MSG + SHRINCS_THASH_MAX_MSG   /* 598 */
};

/* out := SHA256(pk_seed || zeros(48) || addr || msg[:msglen])[:16].
   Generalizes the fixed-16-byte chain hash to any message length so one
   primitive serves F (msglen = n), the PRF (msglen = n), the WOTS+C
   public-key compression T_sf (msglen = chain_count*n), and the future
   tree hashes. The preimage is assembled left to right in one fixed
   max-size buffer and exactly its 86+msglen bytes are hashed, so the
   bytes past the message are never read. */
void shrincs_thash(uint8_t out[SHRINCS_THASH_OUT_BYTES],
                   const uint8_t pk_seed[SHRINCS_THASH_OUT_BYTES],
                   const uint8_t addr[SHRINCS_THASH_ADDR_BYTES],
                   const uint8_t *msg,
                   size_t msglen)
{
    uint8_t buf[THASH_BUF_BYTES];
    uint8_t hash[SHRINCS_SHA256_DIGEST_BYTES];
    shrincs_memcpy(buf, pk_seed, SHRINCS_THASH_OUT_BYTES);
    shrincs_memset(buf + THASH_AT_PAD, 0, SHRINCS_THASH_PKSEED_PAD);
    shrincs_memcpy(buf + THASH_AT_ADDR, addr, SHRINCS_THASH_ADDR_BYTES);
    shrincs_memcpy(buf + THASH_AT_MSG, msg, msglen);
    shrincs_sha256(hash, buf, THASH_AT_MSG + msglen);
    shrincs_memcpy(out, hash, SHRINCS_THASH_OUT_BYTES);
}
