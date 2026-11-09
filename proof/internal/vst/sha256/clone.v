(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.sha256.clone: the VST side's private copy of the spec

    A PRIVATE CLONE of Model.sha256_spec, plus every derived fact the
    machine-checked proofs need and a reviewer does not.

    WHY A CLONE AND NOT AN IMPORT. Model.sha256_spec is one of the files
    a reviewer reads, and it earns that by containing nothing but
    definitions, one faithfulness lemma and known-answer tests. The
    moment the body proofs under verif/ start needing sizes, prefix
    forms and step lemmas, those accumulate wherever the definitions
    live. Keeping the definitions in two places, with the compiler
    checking they agree, is what stops that: the machinery lands HERE
    and Model.sha256_spec stays a document.

    HOW DRIFT IS CAUGHT. Vst.sha256.sync states, definition
    by definition, that the spelling below and the spelling in
    Model.sha256_spec are the SAME TERM, each by [reflexivity] -- so the
    kernel checks it and a divergence is a build failure, not a silent
    fork. That also transfers Model.sha256_spec's known-answer tests to this
    copy: the vectors pin one spelling, [reflexivity] pins the other
    to it.

    NOTHING HERE IS REVIEWER-FACING. Read Model.sha256_spec instead.

    THE DERIVED MACHINERY, and why each piece exists: a C `for` loop
    invariant has to name the value after i iterations, so the
    schedule and the round fold each get an "upto n" form with a step
    lemma ([schedule_uptoS], [nth_schedule_upto_last], [roundsS]). *)

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

Lemma padzeros_range (n : Z) : 0 <= padzeros n < 64.
Proof.
apply Z.mod_pos_bound.
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

    Both exported functions end this way, so it is named once. *)

Definition digest_bytes (Hs : seq w32) : seq Z :=
  flatten [seq bytes_of_word U32 w | w <- Hs].

Definition digest_of (Hs : seq w32) : word U256 := word_of_bytes U256 (digest_bytes Hs).

(* ================================================================= *)
(** ** SS 6.2: SHA-256

    Preprocessing (SS 5), then the compression function over the
    result, then the digest. Three lines, and the one function
    src/sha256.c exports. *)

Definition sha256_words (msg : seq Z) : seq w32 := compress_blocks H0 (pad msg).

(** The digest as the thirty-two bytes the C stores out. *)
Definition sha256_bytes (msg : seq Z) : seq Z := digest_bytes (sha256_words msg).

(** The digest as one 256-bit word, used by the C contract. *)
Definition sha256 (msg : seq Z) : word U256 := digest_of (sha256_words msg).

(* ================================================================= *)
(** ** Derived machinery: sizes

    Every loop bound in src/sha256.c is one of these. *)

Lemma K_size : size K = 64%nat.
Proof.
rewrite size_map.
reflexivity.
Qed.

Lemma H0_size : size H0 = 8%nat.
Proof.
rewrite size_map.
reflexivity.
Qed.

Lemma len_bytes_size (n : Z) : size (len_bytes n) = 8%nat.
Proof. apply bytes_of_word_size. Qed.

Lemma parse_block_size (blk : seq Z) : size (parse_block blk) = 16%nat.
Proof.
rewrite size_map.
rewrite size_iota.
reflexivity.
Qed.

Lemma parse_blocks_size (padded : seq Z) : size (parse_blocks padded) = nblocks padded.
Proof.
rewrite size_map.
rewrite size_iota.
reflexivity.
Qed.

Lemma list_of_state_size (st : state) : size (list_of_state st) = 8%nat.
Proof.
destruct st as [[[[[[[a b] c] d] e] f] g] h].
reflexivity.
Qed.

Lemma compress_words_size (H M : seq w32) : size H = 8%nat -> size (compress_words H M) = 8%nat.
Proof.
intros HH.
unfold compress_words.
rewrite size_map.
rewrite size_zip.
rewrite list_of_state_size.
rewrite HH.
rewrite minnn.
reflexivity.
Qed.

(** SS 6.2.2 step 4, indexed: [compress_words] is a [map] over a
    [zip], and a loop that stores its eight entries one at a time
    needs the entries and not the fold. *)
Lemma nth_compress_words (Hs Ms : seq w32) (k : nat) :
  (k < 8)%nat -> size Hs = 8%nat ->
  nth w32_0 (compress_words Hs Ms) k
  = (nth w32_0 (list_of_state (rounds Hs Ms)) k + nth w32_0 Hs k)%R.
Proof.
intros Hk H8.
(* the map runs over a zip of two eight-element lists, so index [k] is
   in range and the pair at [k] is the pair of the two entries *)
assert (Hsz : size (zip (list_of_state (rounds Hs Ms)) Hs) = 8%nat).
{ rewrite size_zip.
  rewrite list_of_state_size.
  rewrite H8.
  rewrite minnn.
  reflexivity. }
unfold compress_words.
rewrite (nth_map (w32_0, w32_0)).
- rewrite Hsz.
  exact Hk.
- rewrite nth_zip.
  + rewrite list_of_state_size.
    rewrite H8.
    reflexivity.
  + reflexivity.
Qed.

(** [compress_words] preserves the eight-word state, so the fold over
    any run of blocks does too. Every loop that advances the chaining
    value one block at a time needs this to re-establish the callee's
    PREcondition. *)
Lemma foldl_compress_words_size (Hst : seq w32) (L : seq (seq w32)) :
  size Hst = 8%nat -> size (foldl compress_words Hst L) = 8%nat.
Proof.
revert Hst.
induction L as [|M L IH].
- (* no blocks: the chaining value comes back untouched *)
  intros Hst HH.
  exact HH.
- (* one block consumed, and the callee restores the eight words *)
  intros Hst HH.
  simpl.
  apply IH.
  apply compress_words_size.
  exact HH.
Qed.

(* ================================================================= *)
(** ** Derived machinery: the digest as bytes

    [digest_bytes] is the flattening the C's eight [store_be32] calls
    perform. Its length and its range are what let [word_of_bytes]
    invert it, and both proofs are one induction on the word list. *)

Lemma digest_bytes_cons (w : w32) (Hs : seq w32) :
  digest_bytes (w :: Hs) = bytes_of_word U32 w ++ digest_bytes Hs.
Proof. reflexivity. Qed.

Lemma digest_bytes_size (Hs : seq w32) : size (digest_bytes Hs) = (4 * size Hs)%nat.
Proof.
induction Hs as [|w Hs IH].
- (* no words: no bytes *)
  reflexivity.
- (* one more word contributes its four bytes *)
  rewrite digest_bytes_cons.
  rewrite size_cat.
  rewrite bytes_of_word_size.
  rewrite IH.
  rewrite mulnS.
  reflexivity.
Qed.

Lemma digest_bytes_range (Hs : seq w32) (b : Z) :
  b \in digest_bytes Hs -> 0 <= b < 256.
Proof.
induction Hs as [|w Hs IH].
- (* no words: the byte list is empty, so there is nothing to bound *)
  intros Hb.
  discriminate Hb.
- rewrite digest_bytes_cons.
  rewrite mem_cat.
  intros Hb.
  destruct (elimT orP Hb) as [Hin | Hin].
  + (* the byte is one of the four the leading word contributes *)
    destruct (elimT mapP Hin) as [j _ Hval].
    rewrite Hval.
    apply byte_of_word_range.
  + (* the byte comes from the remaining words *)
    apply IH.
    exact Hin.
Qed.

(** SS 5.1.1's closing claim: "the length of the padded message should
    now be a multiple of 512 bits", i.e. of 64 bytes. *)

Lemma pad_size (msg : seq Z) :
  Z.of_nat (size (pad msg)) = msglen msg + 9 + padzeros (msglen msg).
Proof.
unfold pad.
rewrite !size_cat.
rewrite size_nseq.
rewrite len_bytes_size.
simpl.
unfold msglen.
(* [rewrite <- !plusE] turns mathcomp's [addn] into Stdlib's [Nat.add]:
   [lia]'s preprocessing has instances for the latter and none for the
   former, so without it the goal is opaque to it. *)
rewrite <- !plusE.
pose proof (padzeros_range (Z.of_nat (size msg))) as Hr.
lia.
Qed.

Lemma pad_size_mod (msg : seq Z) : Z.of_nat (size (pad msg)) mod 64 = 0.
Proof.
rewrite pad_size.
unfold padzeros.
unfold msglen.
set n := Z.of_nat (size msg).
(* reassociate so that the [mod 64] sits leftmost, where
   [Z.add_mod_idemp_l] can absorb it *)
assert (Hcomm : n + 9 + (55 - n) mod 64 = (55 - n) mod 64 + (n + 9)).
{ lia. }
rewrite Hcomm.
rewrite (Z.add_mod_idemp_l _ _ 64 ltac:(lia)).
(* message, 0x80 byte, zero fill and length add up to whole blocks *)
assert (Hsum : 55 - n + (n + 9) = 64).
{ lia. }
rewrite Hsum.
reflexivity.
Qed.

(* ================================================================= *)
(** ** Derived machinery: the schedule as a growing prefix

    src/sha256.c fills W[0..64) with one `for` loop, so its invariant
    has to name the schedule after i extension steps. [schedule] is
    [schedule_upto _ 48]; the three lemmas below are, in order, the
    loop's step, the value it stores, and the fact that earlier
    entries do not move.

    This is what the full uint32_t W[64] array buys over the usual
    sixteen-word ring buffer: the invariant is an equality between the
    array and a prefix of [schedule], not a sliding-window relation. *)

(** The schedule after [n] extension steps: W_0 .. W_(15+n).

    An ABBREVIATION and not a Definition, deliberately. As a Definition,
    [schedule M = schedule_upto M 48] is true but its [reflexivity]
    asks conversion to unfold [iter] forty-eight times through
    [sched_step] -- each layer carrying [rcons], [nth] and two
    [sigma]s -- and the proof does not come back. As an abbreviation the
    two are the SAME TERM and nothing has to be converted at all. *)

Abbreviation schedule_upto M n := (iter n sched_step M).

Lemma schedule_upto0 (M : seq w32) : schedule_upto M 0 = M.
Proof. reflexivity. Qed.

Lemma schedule_uptoS (M : seq w32) (n : nat) :
  schedule_upto M n.+1 = sched_step (schedule_upto M n).
Proof.
rewrite iterS.
reflexivity.
Qed.

Lemma sched_step_size (W : seq w32) : size (sched_step W) = (size W).+1.
Proof.
unfold sched_step.
rewrite size_rcons.
reflexivity.
Qed.

Lemma schedule_upto_size (M : seq w32) (n : nat) :
  size (schedule_upto M n) = (size M + n)%nat.
Proof.
induction n as [|n IH].
- (* no extension steps: the schedule is still the block *)
  rewrite schedule_upto0.
  rewrite addn0.
  reflexivity.
- (* each step appends exactly one word *)
  rewrite schedule_uptoS.
  rewrite sched_step_size.
  rewrite IH.
  rewrite addnS.
  reflexivity.
Qed.

Lemma schedule_size (M : seq w32) : size M = 16%nat -> size (schedule M) = 64%nat.
Proof.
intros HM.
unfold schedule.
rewrite schedule_upto_size.
rewrite HM.
reflexivity.
Qed.

Lemma nth_schedule_uptoS (M : seq w32) (n t : nat) :
  (t < size (schedule_upto M n))%nat ->
  nth w32_0 (schedule_upto M n.+1) t = nth w32_0 (schedule_upto M n) t.
Proof.
intros Ht.
rewrite schedule_uptoS.
unfold sched_step.
rewrite nth_rcons.
(* [t] is below the old size, so [nth] reads the old entry *)
rewrite Ht.
reflexivity.
Qed.

(** Extension never disturbs a word already produced, at any distance.
    THE SLIDING WINDOW NEEDS THIS and the full-array version did not:
    src/sha256.c keeps only sixteen live schedule words, so its loop
    invariant is stated against [schedule_upto M n] for the current n
    while the funspec speaks of the whole [schedule M]. These two move
    between the two. *)

Lemma nth_schedule_upto_add (M : seq w32) (n k u : nat) :
  size M = 16%nat -> (u < 16 + n)%nat ->
  nth w32_0 (schedule_upto M (n + k)) u = nth w32_0 (schedule_upto M n) u.
Proof.
intros HM Hu.
induction k as [|k IH].
- (* no further steps *)
  rewrite addn0.
  reflexivity.
- (* index [u] is still inside the schedule after [n + k] steps, so the
     (n+k+1)-st step leaves it alone *)
  assert (Hlt : (u < size (schedule_upto M (n + k)))%nat).
  { rewrite schedule_upto_size.
    rewrite HM.
    apply (leq_trans Hu).
    rewrite leq_add2l.
    apply leq_addr. }
  rewrite addnS.
  rewrite (nth_schedule_uptoS M (n + k) u Hlt).
  exact IH.
Qed.

Lemma nth_schedule_prefix (M : seq w32) (n u : nat) :
  size M = 16%nat -> (n <= 48)%nat -> (u < 16 + n)%nat ->
  nth w32_0 (schedule M) u = nth w32_0 (schedule_upto M n) u.
Proof.
intros HM Hn Hu.
unfold schedule.
(* split the forty-eight steps as [n] steps plus the rest *)
rewrite <- (subnKC Hn).
apply nth_schedule_upto_add.
- exact HM.
- exact Hu.
Qed.

(** The word the n-th extension step produces, at its own index, with
    the four back-references at the offsets SS 6.2.2 names. *)
Lemma nth_schedule_upto_last (M : seq w32) (n : nat) :
  size M = 16%nat ->
  nth w32_0 (schedule_upto M n.+1) (16 + n)%nat
  = (sigma1 (nth w32_0 (schedule_upto M n) (14 + n))
     + nth w32_0 (schedule_upto M n) (9 + n)
     + sigma0 (nth w32_0 (schedule_upto M n) (1 + n))
     + nth w32_0 (schedule_upto M n) n)%R.
Proof.
intros HM.
(* after [n] steps the schedule holds W_0 .. W_(15+n) *)
assert (Hs : size (schedule_upto M n) = (16 + n)%nat).
{ rewrite schedule_upto_size.
  rewrite HM.
  reflexivity. }
rewrite schedule_uptoS.
unfold sched_step.
rewrite <- cats1.
rewrite nth_cat.
rewrite Hs.
(* index 16+n is past the old schedule, so it is the appended word *)
rewrite ltnn.
rewrite subnn.
simpl.
(* the four back-references, at the offsets SS 6.2.2 names. [rewrite <-
   !plusE] / [<- !minusE] turn mathcomp's [addn] and [subn] into
   Stdlib's, which is the only arithmetic [lia] has instances for. *)
assert (E2 : (16 + n - 2 = 14 + n)%nat).
{ rewrite <- !plusE.
  rewrite <- !minusE.
  lia. }
assert (E7 : (16 + n - 7 = 9 + n)%nat).
{ rewrite <- !plusE.
  rewrite <- !minusE.
  lia. }
assert (E15 : (16 + n - 15 = 1 + n)%nat).
{ rewrite <- !plusE.
  rewrite <- !minusE.
  lia. }
assert (E16 : (16 + n - 16 = n)%nat).
{ rewrite <- !plusE.
  rewrite <- !minusE.
  lia. }
rewrite E2.
rewrite E7.
rewrite E15.
rewrite E16.
reflexivity.
Qed.

(** SS 6.2.2 step 1 over the whole schedule. [nth_schedule_upto_last]
    produces the recurrence with three different [schedule_upto]
    prefixes in it; a loop invariant that names [schedule M] and
    nothing else needs those prefixes eliminated, which is what
    [nth_schedule_prefix] does. The result is the recurrence in the
    shape the standard writes it. *)
Lemma nth_schedule_rec (M : seq w32) (n : nat) :
  size M = 16%nat -> (n < 48)%nat ->
  nth w32_0 (schedule M) (16 + n)
  = (sigma1 (nth w32_0 (schedule M) (14 + n))
     + nth w32_0 (schedule M) (9 + n)
     + sigma0 (nth w32_0 (schedule M) (1 + n))
     + nth w32_0 (schedule M) n)%R.
Proof.
intros HM Hn.
assert (Hn48 : (n <= 48)%nat).
{ apply ltnW.
  exact Hn. }
(* The five index bounds the prefix lemma needs. [apply (introT ltP)]
   turns mathcomp's BOOLEAN [<] into the Peano one: this build has no
   mczify, so [lia] cannot see the boolean comparison at all.
   [rewrite <- !plusE] then turns [addn] into Stdlib's [Nat.add], which
   is the addition [lia]'s preprocessing has instances for. *)
assert (L16 : (16 + n < 16 + n.+1)%nat).
{ apply (introT ltP).
  rewrite <- !plusE.
  lia. }
assert (L14 : (14 + n < 16 + n)%nat).
{ apply (introT ltP).
  rewrite <- !plusE.
  lia. }
assert (L9 : (9 + n < 16 + n)%nat).
{ apply (introT ltP).
  rewrite <- !plusE.
  lia. }
assert (L1 : (1 + n < 16 + n)%nat).
{ apply (introT ltP).
  rewrite <- !plusE.
  lia. }
assert (L0 : (n < 16 + n)%nat).
{ apply (introT ltP).
  rewrite <- !plusE.
  lia. }
rewrite (nth_schedule_prefix M n.+1 (16 + n) HM Hn L16).
rewrite (nth_schedule_upto_last M n HM).
(* put the four back-references back in terms of the whole schedule *)
rewrite <- (nth_schedule_prefix M n (14 + n) HM Hn48 L14).
rewrite <- (nth_schedule_prefix M n (9 + n) HM Hn48 L9).
rewrite <- (nth_schedule_prefix M n (1 + n) HM Hn48 L1).
rewrite <- (nth_schedule_prefix M n n HM Hn48 L0).
reflexivity.
Qed.

(* ================================================================= *)
(** ** Derived machinery: the rounds as a growing prefix

    Same story for the sixty-four rounds: [rounds] is
    [rounds_upto _ _ 64], and [roundsS] is what the round loop's
    invariant steps along. *)

(** The state after [n] of the sixty-four rounds. An abbreviation for the
    same reason as [schedule_upto]. *)

Abbreviation rounds_upto H M n := (foldl round (state_of H) (take n (zip K (schedule M)))).

Lemma rounds_uptoE (H M : seq w32) :
  size M = 16%nat -> rounds H M = rounds_upto H M 64.
Proof.
intros HM.
(* the zip is exactly the sixty-four (K_t, W_t) pairs *)
assert (Hz : size (zip K (schedule M)) = 64%nat).
{ rewrite size_zip.
  rewrite K_size.
  rewrite (schedule_size M HM).
  rewrite minnn.
  reflexivity. }
unfold rounds.
(* The [take] is discharged from [Hz] explicitly. Left to a general
   closer, the side goal [size (zip K (schedule M)) <= 64] goes to
   [done], which tries to COMPUTE [schedule M] -- forty-eight [rcons]
   steps on an abstract list -- and does not come back. *)
assert (Htake : take 64 (zip K (schedule M)) = zip K (schedule M)).
{ apply take_oversize.
  rewrite Hz.
  apply leqnn. }
rewrite Htake.
reflexivity.
Qed.

Lemma rounds_upto0 (H M : seq w32) : rounds_upto H M 0 = state_of H.
Proof.
rewrite take0.
reflexivity.
Qed.

Lemma roundsS (H M : seq w32) (n : nat) :
  (n < 64)%nat -> size M = 16%nat ->
  rounds_upto H M n.+1
  = round (rounds_upto H M n) (nth w32_0 K n, nth w32_0 (schedule M) n).
Proof.
intros Hn HM.
pose proof K_size as HK.
pose proof (schedule_size M HM) as HS.
(* [foldl] on a singleton is definitional, but reaching it with [simpl]
   would also unfold [schedule M] into its forty-eight iterations and
   the goal never comes back. Named instead. *)
assert (foldl1 : forall (a : state) (x : w32 * w32), foldl round a [:: x] = round a x).
{ intros a x.
  reflexivity. }
(* round [n] exists, so the (n+1)-st prefix is the n-th plus one pair *)
assert (Hlt : (n < size (zip K (schedule M)))%nat).
{ rewrite size_zip.
  rewrite HK.
  rewrite HS.
  rewrite minnn.
  exact Hn. }
rewrite (take_nth (w32_0, w32_0) Hlt).
rewrite <- cats1.
rewrite foldl_cat.
rewrite foldl1.
rewrite nth_zip.
- (* the two zipped lists are the same length *)
  rewrite HK.
  rewrite HS.
  reflexivity.
- reflexivity.
Qed.

Local Close Scope sha_scope.
