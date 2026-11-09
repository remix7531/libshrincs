(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_load_be32: proof of body_load_be32

    SS 3.1 (2): the four bytes at [p] read as one big-endian 32-bit
    word. Together with store_be32 this is the only place in
    src/sha256.c where byte order is decided, and the funspec states
    it against the shared [word_of_bytes] codec in [Model.bytes].

    THE SHAPE. Four loads, one [return], and then a single arithmetic
    identity: CompCert's shift-or tower and [word_of_bytes]' [foldl]
    build the same number. [int_be32_word_of_bytes] below is that
    identity, and it is pure [Z] -- no separation logic -- so it is
    stated and proved before the body.

    NO BIT-INDEX CASE SPLIT IS NEEDED. Both sides are built from
    [Z.lor] and [Z.shiftl] alone, and [Z.shiftl_lor] plus
    [Z.shiftl_shiftl] rewrite the [foldl]'s left-nested
    shift-by-8-then-or into the tower's shift-by-24/16/8-then-or. The
    byte bounds are used only where [Int.unsigned (Int.repr z) = z] is
    needed, never for disjointness of the four fields. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import bridge.
From Shrincs.internal.vst.sha256 Require Import contract.
From Shrincs.internal.vst.sha256 Require Import clone.
From Shrincs.internal.vst.support Require Import settings.
From Shrincs.clight Require Import sha256.

(* The mathcomp surface is deliberately narrow: [ssralg] for the ring
   structure, [word.word] for [word U32] and its lemmas. The full
   surface replaces stdlib's [rewrite] with ssreflect's, and the
   proofs below use stdlib's [rewrite ... by tac]. Nothing in this
   file needs mathcomp's [seq] vocabulary, so narrowing costs it
   nothing. *)
From mathcomp Require Import ssralg word.word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

(* ================================================================= *)
(** ** The arithmetic the C performs

    The C expression [(p0 << 24) | (p1 << 16) | (p2 << 8) | p3] read
    as a [word U32]. The four hypotheses are the byte ranges; they are
    what makes each [Int.repr] on the left transparent to
    [Int.unsigned], and nothing else. *)

Lemma int_be32_word_of_bytes (z0 z1 z2 z3 : Z) :
  0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 -> 0 <= z3 < 256 ->
  Int.or (Int.or (Int.or (Int.shl (Int.repr z0) (Int.repr 24))
                         (Int.shl (Int.repr z1) (Int.repr 16)))
                 (Int.shl (Int.repr z2) (Int.repr 8)))
         (Int.repr z3)
  = int_of_w32 (word_of_bytes U32 (z0 :: z1 :: z2 :: z3 :: nil)).
Proof.
intros Hz0 Hz1 Hz2 Hz3.
(* mathcomp-word reduces modulo [wbase U32] and [Int.repr] modulo
   [Int.modulus]; [wbase_U32] says those are the same number, so the
   inner reduction is invisible to the outer one *)
assert (Hwrepr : forall z : Z, wunsigned (wrepr U32 z) = z mod Int.modulus).
{ intros z.
  rewrite <- wbase_U32.
  apply wunsigned_repr. }

(* both sides become [Int.repr] of a Z built from [Z.lor]/[Z.shiftl] *)
unfold Int.shl.
rewrite !Int.unsigned_repr by rep_lia.
rewrite !or_repr.
unfold int_of_w32, word_of_bytes.
rewrite Hwrepr.
rewrite Int_repr_mod.
f_equal.
(* the [foldl] over a four-element list, written out *)
simpl.
(* left-nested shift-by-8 towers are shift-by-24/16/8 towers *)
rewrite !Z.shiftl_lor.
rewrite !Z.shiftl_shiftl by lia.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The body proof *)

Lemma body_load_be32 : semax_body Vprog_sha Gprog_sha f_load_be32 spec_load_be32.
Proof.
start_function.
rename H into Hlen.

(* ===== Stage 1: give the four bytes names ===== *)
(* [Zlength bs = 4] rules out every other list shape, so the five
   impossible branches close on the length alone. *)
destruct bs as [| b0 [| b1 [| b2 [| b3 [| b4 bs']]]]].
1-4: rewrite ?Zlength_cons, ?Zlength_nil in Hlen; rep_lia.
2: rewrite ?Zlength_cons in Hlen; rep_lia.
clear Hlen.

(* ===== Stage 2: walk the C ===== *)
(* [forward] reads each element with [Znth], and only sees a [Vubyte]
   there once the [map] is gone. *)
change (ListDef.map Vubyte (b0 :: b1 :: b2 :: b3 :: nil))
  with (Vubyte b0 :: Vubyte b1 :: Vubyte b2 :: Vubyte b3 :: nil).

forward.                        (* t'1 = p[0] *)
{ entailer!.
  rep_lia. }
forward.                        (* t'2 = p[1] *)
{ entailer!.
  rep_lia. }
forward.                        (* t'3 = p[2] *)
{ entailer!.
  rep_lia. }
forward.                        (* t'4 = p[3] *)
{ entailer!.
  rep_lia. }
forward.                        (* return (t'1<<24)|(t'2<<16)|(t'3<<8)|t'4 *)

(* ===== Stage 3: the returned value against the funspec's word ===== *)
entailer!.
change (Znth 0 (Vubyte b0 :: Vubyte b1 :: Vubyte b2 :: Vubyte b3 :: nil))
  with (Vubyte b0).
change (Znth 1 (Vubyte b0 :: Vubyte b1 :: Vubyte b2 :: Vubyte b3 :: nil))
  with (Vubyte b1).
change (Znth 2 (Vubyte b0 :: Vubyte b1 :: Vubyte b2 :: Vubyte b3 :: nil))
  with (Vubyte b2).
change (Znth 3 (Vubyte b0 :: Vubyte b1 :: Vubyte b2 :: Vubyte b3 :: nil))
  with (Vubyte b3).
(* the C's [sem_or]/[sem_shift_ii]/[sem_cast_i2i] on concrete [Vint]s;
   Vst.settings is what keeps this from diverging *)
simpl.
f_equal.
apply int_be32_word_of_bytes.
all: rep_lia.
Qed.
