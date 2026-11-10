/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 */

#include "common.h"
#include "sha256.h"
#include "wots.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ---------- Self-consistency ----------

   WOTS+C has no upstream RFC test vectors (the grinding counter is a scheme variant), so
   verification is self-referential: shrincs_wots_sign, then check that pk_from_sig /
   shrincs_wots_verify accept. Signing can in principle fail (SHRINCS_WOTS_SIGN_FAILED) if
   2^16 counters are exhausted without hitting the constant digit-sum; that is negligible,
   so treating it as T_ERROR flags a broken shrincs_wots_grind_to_constant_sum rather than
   a spurious FAIL. */

static enum test_status test_wots_self_roundtrip(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    const uint8_t *sk_seed = input + 0;
    const uint8_t *pk_seed = input + 32;
    const uint8_t *msg = input + 64;

    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, sk_seed, pk_seed, a0);
    if (shrincs_wots_sign(sig, msg, sk_seed, pk_seed, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    return shrincs_wots_verify(pk, sig, msg, pk_seed, a2) == SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

/* All-zero msg: an extreme digit distribution the shrincs_wots_grind_to_constant_sum must still
   push to the constant target sum. */
static enum test_status test_wots_msg_all_zero(void)
{
    uint8_t sk_seed[SHRINCS_WOTS_SK_SEED_BYTES];
    uint8_t pk_seed[SHRINCS_WOTS_PK_SEED_BYTES];
    uint8_t msg[SHRINCS_WOTS_MSG_BYTES] = {0};
    if (fill_random(sk_seed, SHRINCS_WOTS_SK_SEED_BYTES) || fill_random(pk_seed, SHRINCS_WOTS_PK_SEED_BYTES)) {
        return T_ERROR;
    }
    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    zero_addr(a0);
    zero_addr(a1);
    zero_addr(a2);
    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, sk_seed, pk_seed, a0);
    if (shrincs_wots_sign(sig, msg, sk_seed, pk_seed, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    return shrincs_wots_verify(pk, sig, msg, pk_seed, a2) == SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

/* All-0xff msg: the opposite extreme distribution. */
static enum test_status test_wots_msg_all_ff(void)
{
    uint8_t sk_seed[SHRINCS_WOTS_SK_SEED_BYTES];
    uint8_t pk_seed[SHRINCS_WOTS_PK_SEED_BYTES];
    uint8_t msg[SHRINCS_WOTS_MSG_BYTES];
    memset(msg, 0xff, SHRINCS_WOTS_MSG_BYTES);
    if (fill_random(sk_seed, SHRINCS_WOTS_SK_SEED_BYTES) || fill_random(pk_seed, SHRINCS_WOTS_PK_SEED_BYTES)) {
        return T_ERROR;
    }
    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    zero_addr(a0);
    zero_addr(a1);
    zero_addr(a2);
    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, sk_seed, pk_seed, a0);
    if (shrincs_wots_sign(sig, msg, sk_seed, pk_seed, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    return shrincs_wots_verify(pk, sig, msg, pk_seed, a2) == SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

/* Signing is deterministic (shrincs_wots_grind_to_constant_sum picks the least valid
   counter), so two signatures over the same (key, msg) -- counter tail included -- must
   be byte-identical. */
static enum test_status test_wots_addr_reuse(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    const uint8_t *sk_seed = input + 0;
    const uint8_t *pk_seed = input + 32;
    const uint8_t *msg = input + 64;

    shrincs_wots_addr a;
    shrincs_wots_addr b;
    unpack_addr(a, input + 96);
    unpack_addr(b, input + 96);

    uint8_t sig_a[SHRINCS_WOTS_SIG_BYTES];
    uint8_t sig_b[SHRINCS_WOTS_SIG_BYTES];
    if (shrincs_wots_sign(sig_a, msg, sk_seed, pk_seed, a) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    if (shrincs_wots_sign(sig_b, msg, sk_seed, pk_seed, b) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    return memcmp(sig_a, sig_b, SHRINCS_WOTS_SIG_BYTES) == 0 ? T_OK : T_FAIL;
}

/* ---------- Tamper checks ---------- */

static enum test_status test_wots_tamper_sig(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, input + 0, input + 32, a0);
    if (shrincs_wots_sign(sig, input + 64, input + 0, input + 32, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    sig[300] ^= 0x10; /* a chain byte (sig is 514 = 2 + 32*16) */
    return shrincs_wots_verify(pk, sig, input + 64, input + 32, a2) != SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

/* Flip a byte in the 2-byte grinding-counter head (sig[0..2)):
   the recomputed digest no longer matches, so shrincs_wots_verify must reject. */
static enum test_status test_wots_tamper_counter(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, input + 0, input + 32, a0);
    if (shrincs_wots_sign(sig, input + 64, input + 0, input + 32, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    sig[0] ^= 0x01; /* first counter byte (prepended) */
    return shrincs_wots_verify(pk, sig, input + 64, input + 32, a2) != SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_tamper_pk(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, input + 0, input + 32, a0);
    if (shrincs_wots_sign(sig, input + 64, input + 0, input + 32, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    pk[0] ^= 0x01;
    return shrincs_wots_verify(pk, sig, input + 64, input + 32, a2) != SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_tamper_pk_seed(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, input + 0, input + 32, a0);
    if (shrincs_wots_sign(sig, input + 64, input + 0, input + 32, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    uint8_t bad_pk_seed[SHRINCS_WOTS_PK_SEED_BYTES];
    memcpy(bad_pk_seed, input + 32, SHRINCS_WOTS_PK_SEED_BYTES);
    bad_pk_seed[7] ^= 0x80;
    return shrincs_wots_verify(pk, sig, input + 64, bad_pk_seed, a2) != SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_wrong_addr(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    shrincs_wots_addr a_sign;
    shrincs_wots_addr a_ver;
    shrincs_wots_addr a_pk;
    unpack_addr(a_sign, input + 96);
    unpack_addr(a_pk, input + 96);
    unpack_addr(a_ver, input + 96);
    a_ver[4] ^= 1; /* flip an index (prefix) byte so the ADRS differs */

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, input + 0, input + 32, a_pk);
    if (shrincs_wots_sign(sig, input + 64, input + 0, input + 32, a_sign) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    return shrincs_wots_verify(pk, sig, input + 64, input + 32, a_ver) != SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_tamper_msg(void)
{
    uint8_t input[128];
    if (fill_random(input, sizeof input)) {
        return T_ERROR;
    }
    const uint8_t *sk_seed = input + 0;
    const uint8_t *pk_seed = input + 32;
    uint8_t *msg = input + 64;

    shrincs_wots_addr a0;
    shrincs_wots_addr a1;
    shrincs_wots_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig[SHRINCS_WOTS_SIG_BYTES];
    shrincs_wots_pubkey_gen(pk, sk_seed, pk_seed, a0);
    if (shrincs_wots_sign(sig, msg, sk_seed, pk_seed, a1) != SHRINCS_WOTS_OK) {
        return T_ERROR;
    }
    msg[0] ^= 0x01;
    return shrincs_wots_verify(pk, sig, msg, pk_seed, a2) != SHRINCS_WOTS_OK ? T_OK : T_FAIL;
}

/* ---------- WOTS+C known-answer tests (cross-check vs shrincs.py) ----------

   test/wots/vectors/wotsc.kat contains outputs from the reference implementation
   shrincs-bip/impl/shrincs.py. Each case fixes an input and records the
   reference counter / digits / h_grind / sig / pk; we run the compiled shrincs_wots_* and
   byte-compare, catching any divergence from the authoritative construction (hash layout,
   ADRS layout, chain order, counter framing). */

#define KAT_GRIND_TYPE 22 /* SF_SHRINCS_WOTS_GRIND (mirrors src/wots.c) */

static int kat_hex_nibble(unsigned char c)
{
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    if (c >= 'a' && c <= 'f') {
        return 10 + (c - 'a');
    }
    if (c >= 'A' && c <= 'F') {
        return 10 + (c - 'A');
    }
    return -1;
}

static int kat_hex_decode(const char *src, uint8_t *dst, size_t n)
{
    for (size_t i = 0; i < n; i++) {
        int hi = kat_hex_nibble((unsigned char)src[2 * i]);
        int lo = kat_hex_nibble((unsigned char)src[(2 * i) + 1]);
        if (hi < 0 || lo < 0) {
            return -1;
        }
        dst[i] = (uint8_t)((hi << 4) | lo);
    }
    return 0;
}

/* Return the value part of a "key = value" line, or NULL if key doesn't match. */
static const char *kat_field(const char *line, const char *key)
{
    size_t k = strlen(key);
    return strncmp(line, key, k) == 0 ? line + k : NULL;
}

/* Independent recomputation of H_grind(pk_seed, ADRS, msg, counter) =
   SHA256(pk_seed || zeros(48) || ADRS[0..10) with grind type byte || msg || zeros(4) ||
   counter_be2)[:16]. A second oracle for the hash layout, separate from the
   shrincs_wots_sign pipeline. */
static void kat_recompute_h_grind(
    uint8_t out[16], const uint8_t pk_seed[16], const uint8_t adrs[22], const uint8_t msg[32], unsigned long counter)
{
    uint8_t pre[16 + 48 + 10 + 32 + 4 + 2]; /* 112 */
    uint8_t full[32];
    size_t o = 0;
    memcpy(pre + o, pk_seed, 16);
    o += 16;
    memset(pre + o, 0, 48);
    o += 48;
    memcpy(pre + o, adrs, 10);
    pre[o + 9] = KAT_GRIND_TYPE;
    o += 10;
    memcpy(pre + o, msg, 32);
    o += 32;
    memset(pre + o, 0, 4);
    o += 4;
    pre[o + 0] = (uint8_t)(counter >> 8);
    pre[o + 1] = (uint8_t)(counter);
    shrincs_sha256(full, pre, sizeof pre);
    memcpy(out, full, 16);
}

/* Run one parsed case through the compiled code; 0 = all match,
   -1 = mismatch (with a localizing message on stderr). */
static int kat_check_case(int idx,
                          const uint8_t sk_seed[16],
                          const uint8_t pk_seed[16],
                          const uint8_t adrs[22],
                          const uint8_t msg[32],
                          unsigned long counter,
                          const uint8_t digits[32],
                          const uint8_t h_grind[16],
                          const uint8_t sig_exp[SHRINCS_WOTS_SIG_BYTES],
                          const uint8_t pk_exp[SHRINCS_WOTS_PK_BYTES])
{
    shrincs_wots_addr a;
    uint8_t pk_got[SHRINCS_WOTS_PK_BYTES];
    uint8_t sig_got[SHRINCS_WOTS_SIG_BYTES];

    memcpy(a, adrs, 22);
    shrincs_wots_pubkey_gen(pk_got, sk_seed, pk_seed, a);
    if (memcmp(pk_got, pk_exp, SHRINCS_WOTS_PK_BYTES) != 0) {
        (void)fprintf(stderr, "  kat[%d]: pubkey_gen pk mismatch\n", idx);
        return -1;
    }
    memcpy(a, adrs, 22);
    if (shrincs_wots_sign(sig_got, msg, sk_seed, pk_seed, a) != SHRINCS_WOTS_OK) {
        (void)fprintf(stderr, "  kat[%d]: sign returned failure\n", idx);
        return -1;
    }
    if (memcmp(sig_got, sig_exp, SHRINCS_WOTS_SIG_BYTES) != 0) {
        (void)fprintf(stderr, "  kat[%d]: sig mismatch\n", idx);
        return -1;
    }
    if ((((unsigned long)sig_got[0] << 8) | sig_got[1]) != counter) {
        (void)fprintf(stderr, "  kat[%d]: counter head mismatch\n", idx);
        return -1;
    }
    memcpy(a, adrs, 22);
    if (shrincs_wots_verify(pk_exp, sig_exp, msg, pk_seed, a) != SHRINCS_WOTS_OK) {
        (void)fprintf(stderr, "  kat[%d]: verify rejected reference sig\n", idx);
        return -1;
    }
    uint8_t hg[16];
    kat_recompute_h_grind(hg, pk_seed, adrs, msg, counter);
    if (memcmp(hg, h_grind, 16) != 0) {
        (void)fprintf(stderr, "  kat[%d]: h_grind mismatch\n", idx);
        return -1;
    }
    unsigned sum = 0;
    for (size_t i = 0; i < 16; i++) {
        if (digits[2 * i] != (h_grind[i] >> 4) || digits[(2 * i) + 1] != (h_grind[i] & 0x0f)) {
            (void)fprintf(stderr, "  kat[%d]: digits != nibbles(h_grind)\n", idx);
            return -1;
        }
    }
    for (size_t i = 0; i < 32; i++) {
        sum += digits[i];
    }
    if (sum != 240) {
        (void)fprintf(stderr, "  kat[%d]: digit sum %u != 240\n", idx, sum);
        return -1;
    }
    return 0;
}

/* Parse test/wots/vectors/wotsc.kat and check every case. Reports the number of cases
   via *out, and returns: -1 parse/mismatch, 0 file absent, 1 ok. */
static int run_wots_kat(const char *path, int *out)
{
    *out = 0;
    FILE *f = fopen(path, "r");
    if (!f) {
        return 0;
    }

    uint8_t sk_seed[16];
    uint8_t pk_seed[16];
    uint8_t adrs[22];
    uint8_t msg[32];
    uint8_t digits[32];
    uint8_t h_grind[16];
    uint8_t sig_exp[SHRINCS_WOTS_SIG_BYTES];
    uint8_t pk_exp[SHRINCS_WOTS_PK_BYTES];
    unsigned long counter = 0;

    char *line = NULL;
    size_t cap = 0;
    int rc = 1;
    int n = 0;
    const char *v;
    ssize_t r;
    while ((r = getline(&line, &cap, f)) > 0) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '[') {
            continue;
        }
        v = kat_field(line, "sk_seed = ");
        if (v) {
            if (kat_hex_decode(v, sk_seed, 16)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "pk_seed = ");
        if (v) {
            if (kat_hex_decode(v, pk_seed, 16)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "adrs = ");
        if (v) {
            if (kat_hex_decode(v, adrs, 22)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "msg = ");
        if (v) {
            if (kat_hex_decode(v, msg, 32)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "counter = ");
        if (v) {
            char *end = NULL;
            counter = strtoul(v, &end, 10);
            if (end == v) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "digits = ");
        if (v) {
            if (kat_hex_decode(v, digits, 32)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "h_grind = ");
        if (v) {
            if (kat_hex_decode(v, h_grind, 16)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "sig = ");
        if (v) {
            if (kat_hex_decode(v, sig_exp, SHRINCS_WOTS_SIG_BYTES)) {
                rc = -1;
                break;
            }
            continue;
        }
        v = kat_field(line, "pk = ");
        if (v) {
            if (kat_hex_decode(v, pk_exp, SHRINCS_WOTS_PK_BYTES)) {
                rc = -1;
                break;
            }
            if (kat_check_case(n, sk_seed, pk_seed, adrs, msg, counter, digits, h_grind, sig_exp, pk_exp)) {
                rc = -1;
                break;
            }
            n++;
            continue;
        }
    }
    free(line);
    (void)fclose(f);
    *out = n;
    return rc;
}

int run_wots_tests(void)
{
    int failures = 0;
    (void)printf("wots+c (grinding / constant-sum Winternitz)\n");
    RUN(test_wots_self_roundtrip);
    RUN(test_wots_msg_all_zero);
    RUN(test_wots_msg_all_ff);
    RUN(test_wots_addr_reuse);
    RUN(test_wots_tamper_msg);
    RUN(test_wots_tamper_sig);
    RUN(test_wots_tamper_counter);
    RUN(test_wots_tamper_pk);
    RUN(test_wots_tamper_pk_seed);
    RUN(test_wots_wrong_addr);

    int kat_n = 0;
    int kat_rc = run_wots_kat("test/wots/vectors/wotsc.kat", &kat_n);
    if (kat_rc == 0) {
        (void)printf("  %-28s ... SKIP (file not present)\n", "test_wots_kat_shrincs");
    } else if (kat_rc == 1 && kat_n > 0) {
        (void)printf("  %-28s ... ok (%d vectors)\n", "test_wots_kat_shrincs", kat_n);
    } else {
        (void)printf("  %-28s ... FAIL (after %d ok)\n", "test_wots_kat_shrincs", kat_n);
        failures++;
    }
    return failures;
}
