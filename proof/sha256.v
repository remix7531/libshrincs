(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Model.sha256_spec: SHA-256, FIPS 180-4

    Read against FIPS 180-4 in its section order:

      SS 3   notation and word operations
      SS 4   the six logical functions and the constants K
      SS 5   padding, parsing, the initial hash value
      SS 6   the schedule, the compression, SHA-256 itself

    Every definition carries its equation number and the standard's
    own sentence sits immediately above it, so the Rocq reads as the
    continuation of the prose.

    WHAT IS AND IS NOT HERE. Definitions, the one lemma that discharges
    the only place this development specialises the standard
    ([padbits_spec]), and known-answer tests. Nothing else. Every
    derived fact the machine-checked proofs need -- sizes, prefix
    forms of the schedule and the round fold, the single-block
    shortcut -- lives in Vst.sha256.clone and NOT here, so
    that this file stays a document.

    [Vst.sha256.clone] keeps a private copy for derived proof facts.
    [Vst.sha256.sync] checks each definition against this file in the
    kernel. The known-answer tests therefore pin both spellings.

    ONE EXPORTED FUNCTION. SS 6 below ends with [sha256], FIPS 180-4 in
    full: no preprocessing shortcuts, so no length-field special case
    to worry about. src/sha256.c exports exactly this one.

    [Model.sha256] wraps these bytes for the shared model. The
    hash-game assumptions in [Sec.axioms] concern that concrete hash.

    SCOPE TRAPS, all three silent, all three documented at length in
    Model.bytes: [Z] arrives via [BinInt] and never [ZArith]; nat
    annotations are [%nat] and never [%N]; hex literals need [Z_scope]
    opened BY NAME, because in this import context [%Z] is mathcomp's
    [int_scope]. *)

(* floyd FIRST -- the import-order trap this repository documents: the
   two notation stacks clash unless floyd is established before the
   mathcomp surface. [words] Exports it, together with [w256] and the
   |->32 notations the contracts at the foot of this file are written
   in. *)
From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.clight Require Import sha256.

From Shrincs.internal.common Require Import bytes.

From HB Require Import structures.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope Z_scope.

(* ================================================================= *)
(** ** SS 3. Notation and conventions

    "For the secure hash algorithms, the size of the message block --
    m bits -- depends on the algorithm. For SHA-1, SHA-224 and
    SHA-256, each message block has 512 bits, which are represented as
    a sequence of sixteen 32-bit words."

    The word type is mathcomp-word's [word U32], via SSProve's jasmin
    shim. That is the same word type the SSProve games use, which is
    why the security half of this repository and the C half can talk
    about one object rather than two that are claimed equal. *)

Abbreviation w32 := (word U32).

Definition w32_0 : w32 := wrepr U32 0.

(** *** SS 3.2 (1): bitwise logical operations

    Transliterated so that the definitions in SS 4 below are the FIPS
    equations with the glyphs replaced: [.&] is AND, [.|] is OR, [.^]
    is XOR, [~.] is NOT.

    These live in their own scope, opened locally here and nowhere
    else. The VST side loads floyd, whose notation levels are easy to
    collide with; a scope that is never open outside this file cannot
    collide with anything. *)

Declare Scope sha_scope.
Delimit Scope sha_scope with sha.

Notation "x .& y" := (wand x y) (at level 40, left associativity) : sha_scope.
Notation "x .| y" := (wor x y) (at level 50, left associativity) : sha_scope.
Notation "x .^ y" := (wxor x y) (at level 45, left associativity) : sha_scope.
Notation "~. x" := (wnot x) (at level 35, right associativity) : sha_scope.

Local Open Scope sha_scope.

(** SS 3.2 (2), addition modulo 2^w, is the ring addition on
    [word U32]. It is written [(_ + _)%R] throughout and is
    deliberately NOT given a notation of its own: it is the one
    operation a reader might mistake for integer addition, so it
    stays visibly different. *)

(** *** SS 3.2 (3): the right shift operation

    "The right shift operation SHR^n(x), where x is a w-bit word and n
    is an integer with 0 <= n < w, is defined by SHR^n(x) = x >> n." *)

Definition SHR (n : Z) (x : w32) : w32 := wshr x n.

(** *** SS 3.2 (4): the rotate right operation

    "The rotate right (circular right shift) operation ROTR^n(x),
    where x is a w-bit word and n is an integer with 0 <= n < w, is
    defined by ROTR^n(x) = (x >> n) OR (x << w - n)."

    Written as the standard writes it -- a shift, a shift and an OR --
    and not as the library's rotation primitive. The two agree, and
    [ROTR_wror] says so; but the definition a reader checks against
    the document should be the document's. src/sha256.c spells it the
    same way, for the same reason. *)

Definition ROTR (n : Z) (x : w32) : w32 := (SHR n x) .| (wshl x (32 - n)).

Lemma ROTR_wror (n : Z) (x : w32) : 0 <= n < 32 -> ROTR n x = wror x n.
Proof.
move=> Hn.
rewrite /ROTR /SHR /wror.
have Hb : wsize_bits U32 = 32 by [].
rewrite Hb (Z.mod_small _ _ Hn).
reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 4. Functions and constants *)

(** *** SS 4.1.2: SHA-224 and SHA-256 functions

    "SHA-224 and SHA-256 both use six logical functions, where each
    function operates on 32-bit words, which are represented as x, y
    and z. The result of each function is a new 32-bit word." *)

(** (4.2)  Ch(x, y, z) = (x AND y) XOR (NOT x AND z) *)
Definition Ch (x y z : w32) : w32 := (x .& y) .^ ((~. x) .& z).

(** (4.3)  Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) *)
Definition Maj (x y z : w32) : w32 := (x .& y) .^ (x .& z) .^ (y .& z).

(** (4.4)  Sigma_0^{256}(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x) *)
Definition Sigma0 (x : w32) : w32 := ROTR 2 x .^ ROTR 13 x .^ ROTR 22 x.

(** (4.5)  Sigma_1^{256}(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x) *)
Definition Sigma1 (x : w32) : w32 := ROTR 6 x .^ ROTR 11 x .^ ROTR 25 x.

(** (4.6)  sigma_0^{256}(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x) *)
Definition sigma0 (x : w32) : w32 := ROTR 7 x .^ ROTR 18 x .^ SHR 3 x.

(** (4.7)  sigma_1^{256}(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x) *)
Definition sigma1 (x : w32) : w32 := ROTR 17 x .^ ROTR 19 x .^ SHR 10 x.

(** *** SS 4.2.2: SHA-224 and SHA-256 constants

    "SHA-224 and SHA-256 use the same sequence of sixty-four constant
    32-bit words, K_0^{256}, K_1^{256}, ..., K_63^{256}. These words
    represent the first thirty-two bits of the fractional parts of the
    cube roots of the first sixty-four prime numbers. In hex, these
    constant words are (from left to right)" *)

Definition K_Z : seq Z :=
  [:: 0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5;
      0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
      0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3;
      0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
      0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc;
      0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
      0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7;
      0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
      0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13;
      0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
      0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3;
      0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
      0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5;
      0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
      0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208;
      0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2 ].

Definition K : seq w32 := [seq wrepr U32 z | z <- K_Z].

(* ================================================================= *)
(** ** SS 5. Preprocessing

    ONE DELIBERATE SPECIALISATION, and the only one in this file.
    FIPS 180-4 defines SHA-256 on a message of any number of BITS;
    this development defines it on a whole number of BYTES. That is
    what the C can hash and what the WOTS+C model consumes.

    The specialisation is not asserted, it is DISCHARGED: [padzeros]
    is a closed form in bytes, and [padbits_spec] proves that the bit
    count it produces is exactly SS 5.1.1's k. A reader checking this
    section against the standard checks [padbits_spec]. *)

(** The message length in bytes. *)
Definition msglen (msg : seq Z) : Z := Z.of_nat (size msg).

(** *** SS 5.1.1: padding the message

    "Suppose that the length of the message, M, is l bits. Append the
    bit 1 to the end of the message, followed by k zero bits, where k
    is the smallest, non-negative solution to the equation
    l + 1 + k = 448 mod 512. Then append the 64-bit block that is
    equal to the number l expressed using a binary representation."

    For a message of n BYTES, l = 8n; the appended 1 bit together with
    the seven zero bits that follow it is the byte 0x80, and the rest
    of the zero bits are [padzeros n] whole zero bytes. *)

Definition padzeros (n : Z) : Z := (55 - n) mod 64.

(** FIPS's k itself, in bits. The seven is the tail of the 0x80 byte. *)
Definition padbits (n : Z) : Z := 8 * padzeros n + 7.

Lemma padzeros_range (n : Z) : 0 <= padzeros n < 64.
Proof. apply: Z.mod_pos_bound; lia. Qed.

(** THE FAITHFULNESS STATEMENT. [padbits n] is the k of SS 5.1.1: a
    non-negative solution of the congruence, and the smallest one.
    This is what makes the byte-level definition above a
    specialisation of the standard rather than a variant of it. *)

Lemma padbits_spec (n : Z) :
  0 <= n ->
  (* a non-negative solution ... *)
  0 <= padbits n
  /\ (8 * n + 1 + padbits n) mod 512 = 448
  (* ... and no non-negative solution is smaller. *)
  /\ (forall k, 0 <= k -> (8 * n + 1 + k) mod 512 = 448 -> padbits n <= k).
Proof.
move=> Hn.
have Hr := padzeros_range n.
have Hk : 0 <= padbits n < 512 by rewrite /padbits; lia.
(* The congruence. Both sides are eight times something, so divide the
   modulus through and the message length cancels against the padding. *)
have Hmod : (8 * n + 1 + padbits n) mod 512 = 448.
{ rewrite /padbits /padzeros.
  have -> : 8 * n + 1 + (8 * ((55 - n) mod 64) + 7)
          = 8 * ((55 - n) mod 64 + (n + 1)) by lia.
  have -> : 512 = 8 * 64 by [].
  rewrite Z.mul_mod_distr_l //.
  rewrite Z.add_mod_idemp_l //.
  have -> : 55 - n + (n + 1) = 56 by lia.
  by []. }
split; [ lia | split; [ exact: Hmod | ] ].
(* Minimality. Any other solution is congruent to this one modulo 512,
   and this one is the representative in [0, 512), so nothing
   non-negative can be smaller. *)
move=> k Hk0 Hks.
have Hda := Z.div_mod (8 * n + 1 + k) 512 ltac:(lia).
have Hdb := Z.div_mod (8 * n + 1 + padbits n) 512 ltac:(lia).
rewrite Hks in Hda.
rewrite Hmod in Hdb.
lia.
Qed.

(** The 64-bit big-endian encoding of the message length in bits --
    SS 5.1.1's "64-bit block equal to the number l". Rendered by the
    codec in Model.bytes, shared with the C contracts. *)
Definition len_bytes (n : Z) : seq Z := bytes_of_word U64 (wrepr U64 (8 * n)).

(** SS 5.1.1 assembled: message, the 0x80 byte, the zero bytes, the
    length. *)
Definition pad (msg : seq Z) : seq Z :=
  msg ++ [:: 128] ++ nseq (Z.to_nat (padzeros (msglen msg))) 0 ++ len_bytes (msglen msg).

(** *** SS 5.2.1: parsing the message

    "the message and its padding are parsed into N 512-bit blocks,
    M^(1), M^(2), ..., M^(N). Since the 512 bits of the input block
    may be expressed as sixteen 32-bit words, the first 32 bits of
    message block i are denoted M_0^(i), the next 32 bits are
    M_1^(i), and so on up to M_15^(i)."

    Index-based rather than by successive chunking, so that "the t-th
    word of the i-th block" is a term.

    NAME: [parse_blocks] and not [parse]. A bare [parse] is shadowed
    by mathcomp's [ssralg.parse] and [rat.parse] -- the numeral
    parsers -- which import after this file everywhere downstream and
    win silently; the symptom is an "expected type Number.number"
    error at the use site, nowhere near the cause. *)

Definition parse_block (blk : seq Z) : seq w32 :=
  [seq word_of_bytes U32 (take 4 (drop (4 * i) blk)) | i <- iota 0 16].

Definition nblocks (padded : seq Z) : nat := (size padded %/ 64)%nat.

Definition parse_blocks (padded : seq Z) : seq (seq w32) :=
  [seq parse_block (take 64 (drop (64 * i) padded)) | i <- iota 0 (nblocks padded)].

(** *** SS 5.3.3: setting the initial hash value H^(0)

    "For SHA-256, the initial hash value, H^(0), shall consist of the
    following eight 32-bit words, in hex" -- obtained by taking the
    first thirty-two bits of the fractional parts of the square roots
    of the first eight prime numbers. *)

Definition H0_Z : seq Z :=
  [:: 0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a;
      0x510e527f; 0x9b05688c; 0x1f83d9ab; 0x5be0cd19 ].

Definition H0 : seq w32 := [seq wrepr U32 z | z <- H0_Z].

(* ================================================================= *)
(** ** SS 6.2. SHA-256 hash computation *)

(** *** SS 6.2.2 step 1: the message schedule

    "Prepare the message schedule, {W_t}:

         W_t =  M_t^(i)                                     0 <= t <= 15
         W_t =  sigma_1^{256}(W_{t-2}) + W_{t-7}
                 + sigma_0^{256}(W_{t-15}) + W_{t-16}       16 <= t <= 63"

    The first sixteen words ARE the block, so the schedule starts as
    the block and grows: [sched_step] appends the next word, reading
    the four back-references off the end at exactly the offsets the
    standard names. [size W] is the index t being computed. *)

Definition sched_step (W : seq w32) : seq w32 :=
  let t := size W in
  rcons W (sigma1 (nth w32_0 W (t - 2))
           + nth w32_0 W (t - 7)
           + sigma0 (nth w32_0 W (t - 15))
           + nth w32_0 W (t - 16))%R.

Definition schedule (M : seq w32) : seq w32 := iter 48 sched_step M.

(** *** SS 6.2.2 steps 2 and 3: the working variables and the rounds

    "Initialize the eight working variables, a, b, c, d, e, f, g and
    h, with the (i-1)st hash value" and then, "for t = 0 to 63:

         T_1 = h + Sigma_1^{256}(e) + Ch(e,f,g) + K_t^{256} + W_t
         T_2 = Sigma_0^{256}(a) + Maj(a,b,c)
         h = g;  g = f;  f = e;  e = d + T_1;
         d = c;  c = b;  b = a;  a = T_1 + T_2"

    Eight named components rather than an eight-element list, for the
    same reason src/sha256.c uses eight named locals: the rotation is
    then a renaming and not an index shift. *)

Definition state := (w32 * w32 * w32 * w32 * w32 * w32 * w32 * w32)%type.

Definition round (st : state) (kw : w32 * w32) : state :=
  let: (a, b, c, d, e, f, g, h) := st in
  let: (Kt, Wt) := kw in
  let T1 := (h + Sigma1 e + Ch e f g + Kt + Wt)%R in
  let T2 := (Sigma0 a + Maj a b c)%R in
  ((T1 + T2)%R, a, b, c, (d + T1)%R, e, f, g).

Definition state_of (H : seq w32) : state :=
  (nth w32_0 H 0, nth w32_0 H 1, nth w32_0 H 2, nth w32_0 H 3,
   nth w32_0 H 4, nth w32_0 H 5, nth w32_0 H 6, nth w32_0 H 7).

Definition list_of_state (st : state) : seq w32 :=
  let: (a, b, c, d, e, f, g, h) := st in [:: a; b; c; d; e; f; g; h].

Definition rounds (H M : seq w32) : state :=
  foldl round (state_of H) (zip K (schedule M)).

(** *** SS 6.2.2 step 4: the intermediate hash value

    "Compute the ith intermediate hash value H^(i):
         H_0^(i) = a + H_0^(i-1)   ...   H_7^(i) = h + H_7^(i-1)"

    Steps 1 to 4 together are THE COMPRESSION FUNCTION: a chaining
    value and one 512-bit block in, the next chaining value out. It is
    named after what it takes, sixteen already-parsed words, because
    there is a second spelling of the same function just below that
    takes bytes.

    RustCrypto's sha2 crate splits it at exactly the same seam --
    [compress_words] here is its [compress_u32(state, block: [u32;16])]
    and [compress_blocks] is its [compress(state, blocks: &[[u8;64]])].
    src/sha256.c has the same two functions under the same two names. *)

Definition compress_words (H : seq w32) (M : seq w32) : seq w32 :=
  [seq (x.1 + x.2)%R | x <- zip (list_of_state (rounds H M)) H].

(** The same function driven over a run of consecutive 64-byte blocks,
    parsing each (SS 5.2.1) on the way in. NO PREPROCESSING: this does
    not pad, does not append a length, and does not care where the
    bytes came from. *)

Definition compress_blocks (H : seq w32) (bs : seq Z) : seq w32 :=
  foldl compress_words H (parse_blocks bs).

(** *** The digest: eight words, big-endian

    "the resulting 256-bit message digest of the message, M, is
         H_0^(N) || H_1^(N) || ... || H_7^(N)."

    The digest renderer is shared by the byte and word views. *)

Definition digest_bytes (Hs : seq w32) : seq Z :=
  flatten [seq bytes_of_word U32 w | w <- Hs].

Definition digest_of (Hs : seq w32) : word U256 := word_of_bytes U256 (digest_bytes Hs).

(* ================================================================= *)
(** ** SS 6.2: SHA-256

    Preprocessing (SS 5), then the compression function over the
    result, then the digest. Three lines, and the one function
    src/sha256.c exports (as [shrincs_sha256]).

    The C exports only the complete digest. *)

Definition sha256_words (msg : seq Z) : seq w32 := compress_blocks H0 (pad msg).

(** The digest as the thirty-two bytes the C stores out. *)
Definition sha256_bytes (msg : seq Z) : seq Z := digest_bytes (sha256_words msg).

(** The digest as one 256-bit word, used by the C contract. *)
Definition sha256 (msg : seq Z) : word U256 := digest_of (sha256_words msg).

(* ================================================================= *)
(** ** Known-answer tests

    A transcription can be faithful in every visible way and still
    have a typo in it. These are the check: each digest below was
    produced by sha256sum(1) and python3 hashlib, and each lemma is
    closed inside the logic by [vm_compute] -- so they pin the
    DEFINITIONS above, not an extracted program. Via
    Vst.sha256.sync they pin the VST side's clone too.

    THE LENGTHS ARE CHOSEN, NOT ARBITRARY. SS 5.1.1's padding has one
    case split -- a message whose last partial block leaves room for
    the 0x80 byte and the eight length bytes pads to one more block,
    otherwise to two -- and src/sha256.c has the matching branch. The
    vectors sit on both sides of it and on the block boundary itself:

      0, 3        no whole blocks, and the empty message
      55          the largest remainder that still pads to ONE block
      56          the smallest that needs TWO
      63, 64, 65  either side of the block boundary
      119, 120    the same boundary one block up
      128, 200    several whole blocks *)

(** The test message of n bytes is 0, 1, 2, ..., n-1. *)
Definition ramp (n : nat) : seq Z := [seq Z.of_nat i | i <- iota 0 n].

(** The empty message. *)
Lemma sha256_kat_0 :
  sha256 (ramp 0)
  = wrepr U256 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
Proof. vm_compute. reflexivity. Qed.

(** The ASCII string "abc" -- FIPS 180-4's own worked example
    (SS 5.1.1 and appendix B.1). *)
Lemma sha256_kat_abc :
  sha256 [:: 0x61; 0x62; 0x63 ]
  = wrepr U256 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
Proof. vm_compute. reflexivity. Qed.

(** The largest message whose padding still fits one block. *)
Lemma sha256_kat_55 :
  sha256 (ramp 55)
  = wrepr U256 0x463eb28e72f82e0a96c0a4cc53690c571281131f672aa229e0d45ae59b598b59.
Proof. vm_compute. reflexivity. Qed.

(** The smallest that needs a second padding block. *)
Lemma sha256_kat_56 :
  sha256 (ramp 56)
  = wrepr U256 0xda2ae4d6b36748f2a318f23e7ab1dfdf45acdc9d049bd80e59de82a60895f562.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_kat_63 :
  sha256 (ramp 63)
  = wrepr U256 0x29af2686fd53374a36b0846694cc342177e428d1647515f078784d69cdb9e488.
Proof. vm_compute. reflexivity. Qed.

(** Exactly one block, so the padding is a whole extra block. *)
Lemma sha256_kat_64 :
  sha256 (ramp 64)
  = wrepr U256 0xfdeab9acf3710362bd2658cdc9a29e8f9c757fcf9811603a8c447cd1d9151108.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_kat_65 :
  sha256 (ramp 65)
  = wrepr U256 0x4bfd2c8b6f1eec7a2afeb48b934ee4b2694182027e6d0fc075074f2fabb31781.
Proof. vm_compute. reflexivity. Qed.

(** The 55/56 boundary one block up. *)
Lemma sha256_kat_119 :
  sha256 (ramp 119)
  = wrepr U256 0xda18797ed7c3a777f0847f429724a2d8cd5138e6ed2895c3fa1a6d39d18f7ec6.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_kat_120 :
  sha256 (ramp 120)
  = wrepr U256 0xf52b23db1fbb6ded89ef42a23ce0c8922c45f25c50b568a93bf1c075420bbb7c.
Proof. vm_compute. reflexivity. Qed.

(** Several whole blocks. *)
Lemma sha256_kat_128 :
  sha256 (ramp 128)
  = wrepr U256 0x471fb943aa23c511f6f72f8d1652d9c880cfa392ad80503120547703e56a2be5.
Proof. vm_compute. reflexivity. Qed.

Lemma sha256_kat_200 :
  sha256 (ramp 200)
  = wrepr U256 0x1901da1c9f699b48f6b2636e65cbf73abf99d0441ef67f5c540a42f7051dec6f.
Proof. vm_compute. reflexivity. Qed.

Local Close Scope sha_scope.

(* ==================================================================== *)
(** ** 7. The C contract: what src/sha256.c promises

    One VST funspec for the function src/sha256.c exports,
    [shrincs_sha256]. Each
    postcondition names a function defined ABOVE in this file, so what
    the C is asserted to compute is the transcription of FIPS 180-4 a
    reader has just read, not a second description of it.

    Reading key (notations from Vst.repr.words): [p |->32[sh] w] is
    "the thirty-two bytes at p, with permission sh, are the big-endian
    bytes of the word w"; [|->_32] is the same footprint with arbitrary
    content. The [;] between SEP clauses is a SEPARATING conjunction,
    so each contract already says the caller's buffers do not overlap
    -- the formal counterpart of the [restrict] in include/sha256.h,
    which CompCert drops during elaboration.

    NOTHING ELSE IS IN THEM. No [gv : globals] and no resource for the
    round constants: K and H^(0) are function locals in the C precisely
    so that this contract is a function of its bytes alone. See
    Vst.sha256.tables.

    THAT src/sha256.c SATISFIES IT is Vst.sha256.correct, whose
    [sha256_c_correct] packages the twelve semax_body proofs of
    Vst.sha256.verif as one verified component exporting exactly
    this one. It cannot be stated here: it needs the component, the
    component is proved against Vst.sha256.clone, and the gate
    tying the clone to this file (Vst.sha256.sync) is itself
    downstream of this file. *)

Local Open Scope Z_scope.
Local Open Scope logic.

(** SS 6.2 in general. [inlen < 2^61] is what makes the message length
    in BITS fit the sixty-four-bit field SS 5.1.1 appends;
    include/sha256.h states the same bound in the same words. *)
Definition spec_sha256 : AST.ident * funspec :=
  DECLARE _shrincs_sha256
  WITH msg : list byte, out_ptr : Values.val, in_ptr : Values.val,
       sh_in : share, sh_out : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sh_in; writable_share sh_out;
          0 <= Zlength msg < two_p 61)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr (Zlength msg)))
    SEP (data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
         out_ptr |->_32[sh_out])
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
         out_ptr |->32[sh_out] (sha256 (List.map Byte.unsigned msg))).

Local Close Scope logic.

Local Close Scope Z_scope.
