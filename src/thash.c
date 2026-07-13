/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* The SHRINCS tweakable hash and its ADRS field writer. Reference spec:
   shrincs-bip/impl/shrincs.py. Shared across all SHRINCS node types. */

#include "thash.h"
#include "sha256.h"
#include "util.h"

void shrincs_adrs_put32(uint8_t addr[SHRINCS_THASH_ADDR_BYTES], unsigned off, uint32_t v)
{
    addr[off + 0] = (uint8_t)(v >> 24);
    addr[off + 1] = (uint8_t)(v >> 16);
    addr[off + 2] = (uint8_t)(v >> 8);
    addr[off + 3] = (uint8_t)(v);
}

/* out := SHA256(pk_seed || zeros(48) || addr || msg[:msglen])[:16].
   Generalizes the fixed-16-byte chain hash to any message length so one
   primitive serves F (msglen = n), the PRF (msglen = n), the WOTS+C
   public-key compression T_sf (msglen = chain_count*n), and the future
   tree hashes. A single fixed max-size buffer (zeroed, prefix + message
   filled, exactly prefix+msglen bytes hashed) keeps the layout simple
   and constant-shaped -- deliberately trading the always-max stack
   footprint for a foundation that generalizes. */
void shrincs_thash(uint8_t out[SHRINCS_THASH_OUT_BYTES],
                   const uint8_t pk_seed[SHRINCS_THASH_OUT_BYTES],
                   const uint8_t addr[SHRINCS_THASH_ADDR_BYTES],
                   const uint8_t *msg,
                   size_t msglen)
{
    uint8_t buf[SHRINCS_THASH_OUT_BYTES + SHRINCS_THASH_PKSEED_PAD + SHRINCS_THASH_ADDR_BYTES +
                SHRINCS_THASH_MAX_MSG]; /* 16+48+22+512 = 598 */
    uint8_t hash[SHRINCS_SHA256_DIGEST_BYTES];
    size_t prefix = SHRINCS_THASH_OUT_BYTES + SHRINCS_THASH_PKSEED_PAD + SHRINCS_THASH_ADDR_BYTES; /* 86 */
    shrincs_memset(buf, 0, sizeof buf);
    shrincs_memcpy(buf, pk_seed, SHRINCS_THASH_OUT_BYTES);
    /* buf[16 .. 64) stays zero: the pk_seed pad. */
    shrincs_memcpy(buf + SHRINCS_THASH_OUT_BYTES + SHRINCS_THASH_PKSEED_PAD, addr, SHRINCS_THASH_ADDR_BYTES);
    shrincs_memcpy(buf + prefix, msg, msglen);
    shrincs_sha256(hash, buf, prefix + msglen);
    shrincs_memcpy(out, hash, SHRINCS_THASH_OUT_BYTES);
}
