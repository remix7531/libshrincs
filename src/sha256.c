/* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *
 * SHA-256, FIPS 180-4. Written to be VERIFIED, not to be clever: the
 * structure below is a statement-for-equation transcription of the
 * standard, and the Rocq definition of SHA-256 in this repository is
 * the same transcription. Section references in the comments are to
 * FIPS 180-4.
 *
 * proof/internal/vst/sha256/verif/ proves each function against the
 * FIPS definition in proof/sha256.v. proof/internal/vst/sha256/vsu.v
 * packages the proofs as a Verified Software Unit with no imports.
 * proof/internal/vst/link.v links it with the other units to establish
 * the public WOTS+C contracts.
 *
 * WHAT IS DELIBERATELY NOT HERE, and why
 *
 *   - No streaming state. One-shot only (see sha256.h).
 *   - No libc. The byte moves are explicit fixed-bound `for` loops,
 *     not memcpy/memset. VST has no funspec for those unless you
 *     assume one, and an assumed funspec is exactly what this
 *     project's audit gate exists to keep out.
 *   - No __builtin_read32_reversed / bswap intrinsics. load_be32 and
 *     store_be32 are portable shift/or, which is also the form
 *     compilers recognise and fold back into a single bswap.
 *   - No volatile, and no memory-erasure builtin. clightgen lowers
 *     those to Sbuiltin, which VST 2.16 cannot symbolically execute.
 *   - No file-scope tables. A `static const` array is a Clight global,
 *     and a caller must own whatever the callee reads, so it would
 *     reach into the precondition of every proved caller. K and H^(0)
 *     are locals instead, which keeps shrincs_sha256's contract a
 *     function of its bytes alone.
 *
 * WHERE SPEED IS TRADED FOR PROVABILITY, on purpose
 *
 *   - The 64 rounds are ONE loop, not 64 unrolled rounds. Unrolled,
 *     the a..h rotation is resolved at compile time and the proof is
 *     64 straight-line steps; looped, the proof is one induction
 *     against the specification's fold.
 *
 * The message schedule trades the OTHER way, deliberately: it is a
 * sixteen-word sliding window W[t % 16], not a full W[64]. That saves
 * 192 bytes of stack, and it is the one
 * place where this file accepts a harder proof to get a better
 * implementation -- the invariant must say the array holds the
 * sixteen most recent schedule words rather than a prefix. Splitting
 * step 3 of SS 6.2.2 into two loops is what keeps that relation out of
 * rounds 0..15 entirely. See the note above sha256_compress_words.
 *
 * The six logical functions of SS 4.1.2 are `static inline` rather
 * than macros so that each has its own funspec and is proved once
 * against its FIPS equation; clightgen keeps them as functions (it
 * runs before CompCert's inliner), so the proof structure is
 * unaffected and both gcc and ccomp still inline them.
 */

#include <stddef.h>
#include <stdint.h>

#include "sha256.h"

/* ================================================================== */
/* The standard's two constant tables, each written once. Macros, not
 * `static const` arrays (see the head of this file): a macro expands to
 * a braced initialiser, so each use is an ordinary local array and
 * clightgen emits straight-line assignments -- no hidden global, and no
 * builtin memcpy, which VST cannot symbolically execute. */

/* SS 4.2.2: the sixty-four round constants K[0..63], the first
 * thirty-two bits of the fractional parts of the cube roots of the
 * first sixty-four primes. */
#define SHA256_K_INIT                                                                                        \
    {0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u, 0x3956c25bu, 0x59f111f1u, 0x923f82a4u, 0xab1c5ed5u, \
     0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u, 0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u, \
     0xe49b69c1u, 0xefbe4786u, 0x0fc19dc6u, 0x240ca1ccu, 0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau, \
     0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u, 0xc6e00bf3u, 0xd5a79147u, 0x06ca6351u, 0x14292967u, \
     0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u, 0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u, \
     0xa2bfe8a1u, 0xa81a664bu, 0xc24b8b70u, 0xc76c51a3u, 0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u, \
     0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u, 0x391c0cb3u, 0x4ed8aa4au, 0x5b9cca4fu, 0x682e6ff3u, \
     0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u, 0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u}

/* SS 5.3.3: the initial hash value H^(0), the first thirty-two bits of
 * the fractional parts of the square roots of the first eight primes. */
#define SHA256_H0_INIT \
    {0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au, 0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u}

/* ================================================================== */
/* SS 3.2 (3),(4): the two word operations SHA-256 uses.
 *
 * ROTR is spelled the way SS 3.2 (4) defines it -- a shift, a shift
 * and an OR -- and not via a rotate intrinsic, so that the C and the
 * Rocq definition (Shrincs.sha256.ROTR) are the same expression.
 *
 * ROTR and SHR are macros so their shift and OR expressions remain
 * visible in the Clight bodies of the six logical functions below.
 *
 * Nothing is lost on the proof side: ROTR and SHR are named
 * definitions in the model, and one bridge lemma each relates the
 * CompCert shift/or expression to them, so the six proofs below still
 * reason about ROTR rather than about raw bits.
 *
 * PRECONDITION, on both: 0 < n < 32. FIPS 180-4 SS 3.2 (4) allows
 * n = 0, but `x << (32 - 0)` would be a shift by the full width,
 * which C leaves undefined; every one of the twelve uses below passes
 * a literal in 2..25. */

#define SHR(n, x)  ((x) >> (n))
#define ROTR(n, x) (((x) >> (n)) | ((x) << (32 - (n))))

/* ================================================================== */
/* SS 4.1.2: the six logical functions, one per FIPS equation. */

/* (4.2)  Ch(x, y, z) = (x AND y) XOR (NOT x AND z) */
static inline uint32_t Ch(uint32_t x, uint32_t y, uint32_t z)
{
    return (x & y) ^ (~x & z);
}

/* (4.3)  Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) */
static inline uint32_t Maj(uint32_t x, uint32_t y, uint32_t z)
{
    return (x & y) ^ (x & z) ^ (y & z);
}

/* (4.4)  Sigma0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x) */
static inline uint32_t Sigma0(uint32_t x)
{
    return ROTR(2, x) ^ ROTR(13, x) ^ ROTR(22, x);
}

/* (4.5)  Sigma1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x) */
static inline uint32_t Sigma1(uint32_t x)
{
    return ROTR(6, x) ^ ROTR(11, x) ^ ROTR(25, x);
}

/* (4.6)  sigma0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x) */
static inline uint32_t sigma0(uint32_t x)
{
    return ROTR(7, x) ^ ROTR(18, x) ^ SHR(3, x);
}

/* (4.7)  sigma1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x) */
static inline uint32_t sigma1(uint32_t x)
{
    return ROTR(17, x) ^ ROTR(19, x) ^ SHR(10, x);
}

/* ================================================================== */
/* SS 3.1 (2): words are big-endian on the wire. These two are the
 * only place byte order is decided. */

/* The 32-bit big-endian word at p[0..4). */
static inline uint32_t load_be32(const uint8_t *p)
{
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | ((uint32_t)p[3]);
}

/* Write x to p[0..4), most significant byte first. */
static inline void store_be32(uint8_t *p, uint32_t x)
{
    p[0] = (uint8_t)(x >> 24);
    p[1] = (uint8_t)(x >> 16);
    p[2] = (uint8_t)(x >> 8);
    p[3] = (uint8_t)(x);
}

/* ================================================================== */
/* SS 5.2.1: parse one 512-bit block into sixteen 32-bit words. */

static void sha256_parse(uint32_t M[restrict 16], const uint8_t *restrict block)
{
    uint32_t t;

    for (t = 0; t < 16; t++) {
        /* t < 16, so the uint32_t product cannot wrap; the implicit widening
           is exact, so no cast is spelled. */
        /* NOLINTNEXTLINE(bugprone-implicit-widening-of-multiplication-result) */
        M[t] = load_be32(block + (4 * t));
    }
}

/* ================================================================== */
/* SS 6.2.2 for ONE already-parsed block, updating the eight-word
 * chaining value H in place.
 *
 * RustCrypto sha2's `compress_u32(state, block: [u32; 16])`, function
 * for function and loop for loop, including the sliding window.
 *
 * THE SLIDING WINDOW. SS 6.2.2 step 1 describes a sixty-four-word
 * message schedule {W_t}, but round t reads only W_{t-2}, W_{t-7},
 * W_{t-15} and W_{t-16}, so sixteen words always suffice: W[t % 16]
 * holds W_t, and computing W_t overwrites W_{t-16}, which nothing
 * needs again. That also lets the schedule be computed inside the
 * round loop rather than before it, which is what the single loop
 * below does.
 *
 * 192 bytes of stack saved, and the
 * proof gets harder in a specific way: the loop invariant can no
 * longer say "W[t] is the t-th schedule word" pointwise. It has to
 * say that the sixteen live slots hold the sixteen most recent
 * schedule words -- a relation between the array and a WINDOW of the
 * specification. (fips-180-4-lean needs the same relation and calls
 * it MatchAfter.) Splitting step 3 in two keeps that relation out of
 * the first sixteen rounds, where the array is still untouched, so
 * only the second loop carries it.
 *
 * K IS A PARAMETER because this is the per-BLOCK function: declared
 * here it would be re-initialised for every 64-byte block, and the
 * callers pay it once per call instead. This keeps sixty-four stores
 * out of the longest proof in the development.
 *
 * The four numbered steps in the comments are the standard's own. */

static void
sha256_compress_words(uint32_t H[restrict 8], const uint32_t M[restrict 16], const uint32_t sha256_K[restrict 64])
{
    uint32_t W[16];
    uint32_t a;
    uint32_t b;
    uint32_t c;
    uint32_t d;
    uint32_t e;
    uint32_t f;
    uint32_t g;
    uint32_t h;
    uint32_t T1;
    uint32_t T2;
    uint32_t w;
    uint32_t t;

    /* Step 1, first sixteen words: W_t = M_t. The rest of the
     * schedule is produced one word at a time inside step 3. */
    for (t = 0; t < 16; t++) {
        W[t] = M[t];
    }

    /* Step 2. Initialise the eight working variables with H^(i-1). */
    a = H[0];
    b = H[1];
    c = H[2];
    d = H[3];
    e = H[4];
    f = H[5];
    g = H[6];
    h = H[7];

    /* Step 3, rounds 0 to 15. The schedule words for these rounds are
     * the block itself, already in W, so nothing is produced here. */
    for (t = 0; t < 16; t++) {
        T1 = h + Sigma1(e) + Ch(e, f, g) + sha256_K[t] + W[t];
        T2 = Sigma0(a) + Maj(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + T1;
        d = c;
        c = b;
        b = a;
        a = T1 + T2;
    }

    /* Step 3, rounds 16 to 63. Each round first produces its own
     * schedule word by SS 6.2.2 step 1's recurrence
     *   W_t = sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) + W_{t-16}
     * and stores it over W_{t-16}, which no later round reads. All
     * four subtractions are safe: t >= 16 throughout. The W_{t-16}
     * slot IS the destination slot, (t - 16) % 16 == t % 16, so the
     * read below happens before the write that retires it.
     *
     * Separate loops avoid a per-round `if (t < 16)` branch and keep
     * schedule generation confined to these later rounds. */
    for (t = 16; t < 64; t++) {
        w = sigma1(W[(t - 2) % 16]) + W[(t - 7) % 16] + sigma0(W[(t - 15) % 16]) + W[(t - 16) % 16];
        W[t % 16] = w;
        T1 = h + Sigma1(e) + Ch(e, f, g) + sha256_K[t] + w;
        T2 = Sigma0(a) + Maj(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + T1;
        d = c;
        c = b;
        b = a;
        a = T1 + T2;
    }

    /* Step 4. Compute the i-th intermediate hash value H^(i). */
    H[0] = a + H[0];
    H[1] = b + H[1];
    H[2] = c + H[2];
    H[3] = d + H[3];
    H[4] = e + H[4];
    H[5] = f + H[5];
    H[6] = g + H[6];
    H[7] = h + H[7];
}

/* ================================================================== */
/* SS 6.2.2 applied to `nblocks` consecutive 64-byte blocks, advancing
 * `state` in place. RustCrypto sha2's `compress(state, blocks)`,
 * function for function, as sha256_compress_words above is its
 * `compress_u32(state, block)`.
 *
 * Internal: the public header offers exactly one function, and this
 * is not it. It exists because shrincs_sha256() drives two runs of
 * blocks -- the message proper and the padded tail -- and they should
 * be one piece of code proved once. That is also why K is a parameter
 * here rather than a local: shrincs_sha256() would otherwise initialise
 * it once per run instead of once per call. Only the one EXPORTED
 * function owns the table; everything internal receives it. */

static void sha256_compress_blocks(uint32_t state[restrict 8],
                                   const uint8_t *restrict blocks,
                                   size_t nblocks,
                                   const uint32_t sha256_K[restrict 64])
{
    uint32_t M[16];
    size_t i;

    for (i = 0; i < nblocks; i++) {
        sha256_parse(M, blocks + (i * 64));
        sha256_compress_words(state, M, sha256_K);
    }
}

/* ================================================================== */
/* SS 6.2: SHA-256 of an arbitrary-length message.
 *
 * The whole blocks of `in` are compressed in place, straight out of
 * the caller's buffer. Only the remainder -- fewer than 64 bytes --
 * is copied, into the local `tail`, together with the padding of
 * SS 5.1.1. `tail` is a plain local and not a static: a function-local
 * static becomes a Clight global, which this translation unit's VSU
 * would then have to own. */

void shrincs_sha256(uint8_t out[restrict 32], const uint8_t *restrict in, size_t inlen)
{
    uint32_t H[8] = SHA256_H0_INIT;              /* SS 5.3.3 */
    const uint32_t sha256_K[64] = SHA256_K_INIT; /* SS 4.2.2 */
    uint8_t tail[128];
    size_t nblocks; /* whole 64-byte blocks of `in`                  */
    size_t rem;     /* inlen mod 64: what is left for the tail       */
    size_t ntail;   /* padded tail blocks, 1 or 2                    */
    size_t tlen;    /* padded tail length in bytes, 64 or 128        */
    size_t i;

    nblocks = inlen / 64;
    rem = inlen % 64;

    /* SS 6.2.2 applied to each whole block of the message proper. */
    sha256_compress_blocks(H, in, nblocks, sha256_K);

    /* SS 5.1.1. Append the bit "1" (the byte 0x80, since the message
     * is a whole number of bytes), then k zero bits, then the 64-bit
     * big-endian message length in BITS. k is the smallest solution
     * of `8*inlen + 1 + k = 448 (mod 512)`, which for a byte-aligned
     * message is exactly what "zero-fill to the last eight bytes of
     * the last block" computes -- one block if the remainder leaves
     * room for the 0x80 and the length field (rem < 56), two if not.
     *
     * The whole 128-byte buffer is zeroed with a constant trip count
     * rather than only the part in use: the extra stores are noise
     * next to a compression round, and a fixed bound keeps the loop
     * invariant free of the rem/tlen case split. */
    for (i = 0; i < 128; i++) {
        tail[i] = 0;
    }
    for (i = 0; i < rem; i++) {
        tail[i] = in[(nblocks * 64) + i];
    }
    tail[rem] = 0x80;

    if (rem < 56) {
        tlen = 64;
        ntail = 1;
    } else {
        tlen = 128;
        ntail = 2;
    }

    /* The message length in bits is 8*inlen, which needs 64 bits;
     * it is stored as its two 32-bit halves rather than through a
     * 64-bit store, so that store_be32 is the only writer of
     * multi-byte values in this file. inlen < 2^61 (sha256.h) is what
     * makes `inlen >> 29` the exact high half. */
    store_be32(tail + tlen - 8, (uint32_t)(inlen >> 29));
    store_be32(tail + tlen - 4, (uint32_t)inlen << 3);

    sha256_compress_blocks(H, tail, ntail, sha256_K);

    /* SS 6.2.2: the digest is H_0 || H_1 || ... || H_7, big-endian. */
    for (i = 0; i < 8; i++) {
        store_be32(out + (4 * i), H[i]);
    }
}
