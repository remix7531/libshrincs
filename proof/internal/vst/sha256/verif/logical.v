(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_logical: proofs of body_Ch, body_Maj, body_Sigma0,
      body_Sigma1, body_sigma0 and body_sigma1

    SIX semax_body PROOFS IN ONE FILE, a deliberate exception to this
    project's one-per-file rule (proof/STYLE.md), and the reason is
    build time rather than taste: each of these bodies is a single
    [return] statement and its proof is four lines, while the fixed
    cost of any verif/ file is one load of the floyd + mathcomp +
    SSProve stack. Six files would pay that load six times over
    for twenty-four lines of proof. What the one-per-file rule buys is
    build PARALLELISM, and that is worth its fixed cost only where a
    file's own checking time dominates its load time -- which is
    [sha256_compress_words], not these.

    WHAT THESE PROVE. That the C's bit expressions are the equations
    of FIPS 180-4 SS 4.1.2 -- (4.2) through (4.7), one lemma each.
    They are also the first real use of Vst.sha256.bridge,
    and they are its justification: each proof is [forward], then
    [entailer!], then a rewrite chain that pushes [w32_of_int] through
    the CompCert expression to the leaves, where [w32_of_intK] cancels
    it. No bit-level reasoning appears here at all; it is all in the
    bridge, proved once.

    IMPORT DISCIPLINE, narrower here than in the sibling verif files.
    Not one of these six proofs mentions mathcomp's [seq] vocabulary,
    so the file takes [ssralg] and [word.word] alone rather than the
    full [boot order algebra word_ssrZ word] surface. That
    matters for readability: under the wide surface ssreflect's
    [rewrite] shadows the stdlib one and [rewrite L by tac] is a
    syntax error, so the side conditions of [w32_of_int_ROTR] have to
    be discharged by an ssreflect [//]. Narrowed, they are ordinary
    [by lia]. The narrow import still supplies [word U32], the word
    operations and their lemmas. Widening it back would break every
    [by lia] below with a parse error rather than a proof failure. *)

From Vst.repr Require Import words.
From Vst.sha256 Require Import bridge.
From Vst.sha256 Require Import contract.
From Vst.sha256 Require Import clone.
From Vst.clight Require Import sha256.

From mathcomp Require Import ssralg word.word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

(** (4.2)  Ch(x, y, z) = (x AND y) XOR (NOT x AND z) *)
Lemma body_Ch : semax_body Vprog_sha Gprog_sha f_Ch spec_Ch.
Proof.
start_function.
(* return (x & y) ^ (~x & z); *)
forward.
entailer!.
unfold clone.Ch.
(* Push w32_of_int through the C expression, leaf by leaf. *)
rewrite <- w32_of_int_not.
rewrite <- !w32_of_int_and.
rewrite <- w32_of_int_xor.
rewrite w32_of_intK.
reflexivity.
Qed.

(** (4.3)  Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) *)
Lemma body_Maj : semax_body Vprog_sha Gprog_sha f_Maj spec_Maj.
Proof.
start_function.
(* return (x & y) ^ (x & z) ^ (y & z); *)
forward.
entailer!.
unfold clone.Maj.
rewrite <- !w32_of_int_and.
rewrite <- !w32_of_int_xor.
rewrite w32_of_intK.
reflexivity.
Qed.

(** (4.4)  Sigma_0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)

    The C writes each rotation as SS 3.2 (4) defines it, and clightgen
    keeps the [32 - n] unevaluated, so the goal matches
    [w32_of_int_ROTR] literally at each of the three amounts. *)
Lemma body_Sigma0 : semax_body Vprog_sha Gprog_sha f_Sigma0 spec_Sigma0.
Proof.
start_function.
(* return ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22); *)
forward.
entailer!.
unfold clone.Sigma0.
(* Each rotation in turn; the side condition is 0 < n < 32. *)
rewrite <- (w32_of_int_ROTR x 2) by lia.
rewrite <- (w32_of_int_ROTR x 13) by lia.
rewrite <- (w32_of_int_ROTR x 22) by lia.
rewrite <- !w32_of_int_xor.
rewrite w32_of_intK.
reflexivity.
Qed.

(** (4.5)  Sigma_1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x) *)
Lemma body_Sigma1 : semax_body Vprog_sha Gprog_sha f_Sigma1 spec_Sigma1.
Proof.
start_function.
(* return ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25); *)
forward.
entailer!.
unfold clone.Sigma1.
rewrite <- (w32_of_int_ROTR x 6) by lia.
rewrite <- (w32_of_int_ROTR x 11) by lia.
rewrite <- (w32_of_int_ROTR x 25) by lia.
rewrite <- !w32_of_int_xor.
rewrite w32_of_intK.
reflexivity.
Qed.

(** (4.6)  sigma_0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x) *)
Lemma body_sigma0 : semax_body Vprog_sha Gprog_sha f_sigma0 spec_sigma0.
Proof.
start_function.
(* return ROTR(x, 7) ^ ROTR(x, 18) ^ (x >> 3); *)
forward.
entailer!.
unfold clone.sigma0.
rewrite <- (w32_of_int_ROTR x 7) by lia.
rewrite <- (w32_of_int_ROTR x 18) by lia.
(* SS 3.2 (3): the third term is SHR, not the ROTR of SS 3.2 (4).
   Nothing wraps around, so the side condition is the wider
   0 <= n < 32 and the bridge lemma is w32_of_int_shru. *)
rewrite <- (w32_of_int_shru x 3) by lia.
rewrite <- !w32_of_int_xor.
rewrite w32_of_intK.
reflexivity.
Qed.

(** (4.7)  sigma_1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x) *)
Lemma body_sigma1 : semax_body Vprog_sha Gprog_sha f_sigma1 spec_sigma1.
Proof.
start_function.
(* return ROTR(x, 17) ^ ROTR(x, 19) ^ (x >> 10); *)
forward.
entailer!.
unfold clone.sigma1.
rewrite <- (w32_of_int_ROTR x 17) by lia.
rewrite <- (w32_of_int_ROTR x 19) by lia.
rewrite <- (w32_of_int_shru x 10) by lia.
rewrite <- !w32_of_int_xor.
rewrite w32_of_intK.
reflexivity.
Qed.
