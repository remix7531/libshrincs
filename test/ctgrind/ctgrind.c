/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

/* Constant-time check for the secret-consuming WOTS+C entry points
   (shrincs_wots_pubkey_gen and shrincs_wots_sign) via the ctgrind technique
   (https://github.com/agl/ctgrind). These are the only API functions that read
   sk_seed; pk_from_sig and shrincs_wots_verify see only public inputs.

   Note: shrincs_wots_sign's grinding loop trip-count depends on msg, but msg is
   public (left defined below), so this does not leak sk_seed.

   sk_seed is initialized to a real value, then marked "undefined" for valgrind's
   memcheck. Any branch or memory address computed from those bytes will trip a
   "Conditional jump or move depends on uninitialised value" error, which
   --error-exitcode=1 promotes to a non-zero exit. */

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <memcheck.h>

#include "wots.h"

int main(void)
{
    uint8_t sk_seed[SHRINCS_WOTS_SK_SEED_BYTES];
    uint8_t pk_seed[SHRINCS_WOTS_PK_SEED_BYTES];
    uint8_t msg[SHRINCS_WOTS_MSG_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    shrincs_wots_addr addr;

    memset(pk_seed, 0xA5, sizeof pk_seed);
    memset(msg, 0x5A, sizeof msg);
    memset(sk_seed, 0x42, sizeof sk_seed);

    VALGRIND_MAKE_MEM_UNDEFINED(sk_seed, sizeof sk_seed);

    /* shrincs_wots_pubkey_gen reads sk_seed. */
    memset(addr, 0, sizeof addr);
    shrincs_wots_pubkey_gen(pk, sk_seed, pk_seed, addr);

    /* shrincs_wots_sign reads sk_seed. */
    memset(addr, 0, sizeof addr);
    shrincs_wots_sign(sig, msg, sk_seed, pk_seed, addr);

    /* Outputs are secret-derived; mark them defined so the sink below
       doesn't itself trigger a use-of-uninit report. */
    VALGRIND_MAKE_MEM_DEFINED(pk, sizeof pk);
    VALGRIND_MAKE_MEM_DEFINED(sig, sizeof sig);

    /* Keep the calls from being optimized away. */
    volatile uint8_t sink = 0;
    for (size_t i = 0; i < sizeof pk; i++)
        sink ^= pk[i];
    for (size_t i = 0; i < sizeof sig; i++)
        sink ^= sig[i];
    (void)sink;

    return 0;
}
