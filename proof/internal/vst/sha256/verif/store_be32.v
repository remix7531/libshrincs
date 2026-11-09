(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_store_be32: Proof of body_store_be32

    SS 3.1 (2) in the writing direction: [x] stored to [p[0..4)],
    most significant byte first, stated against [bytes_of_word U32].

    ONE TRAP BAKED IN BEFORE THE FIRST [forward]. A byte store
    [p[i] = (uint8_t)(x >> k)] into a [tarray tuchar] makes [forward]
    DIVERGE -- a Rocq [Timeout], not a failure -- once [k >= 24],
    because value evaluation [simpl]-unfolds [Int.Z_mod_modulus] and
    [Z.shiftr] and the term explodes. Shrincs.internal.vst.support.settings sets the
    two [Arguments ... : simpl never] that prevent it and is imported
    below for exactly that reason. store_be32's first line is
    p[0] = x >> 24, so it fires immediately.

    The same trap bites again AFTER the [forward] chain, in the
    arithmetic: an unrestricted [simpl] on the
    [List.map (fun z => Vubyte (Byte.repr z))] over the four extracted
    bytes unfolds [Byte.repr] onto the [Z.land] terms and hangs.
    [cbn [List.map]] -- delta restricted to the one constant that has
    to move -- does the same job and returns at once. That is why
    [store_be32_bytes_eq] reduces the map that way and never with
    [simpl].

    THE ARITHMETIC. After the four stores VST holds the four values
    [Int.zero_ext 8 (Int.zero_ext 8 (Int.shru x (Int.repr k)))] and
    the funspec asks for [bytes_of_word U32 (w32_of_int x)], i.e.
    [Z.land (Z.shiftr (Int.unsigned x) k) 255] wrapped in
    [Vubyte o Byte.repr]. The five lemmas below bridge these
    representations using [Z.shiftr] and [Z.land]. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import bridge.
From Shrincs.internal.vst.sha256 Require Import contract.
From Shrincs.internal.vst.support Require Import settings.
From Shrincs.internal.vst.sha256 Require Import clone.
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
(** ** The byte-extraction arithmetic

    Pure [Z] and [Int] facts used by the byte stores. *)

(** clightgen emits the [(uint8_t)] cast twice -- once for the
    assignment's implicit conversion and once for the explicit cast --
    so every stored value arrives with [Int.zero_ext 8] applied
    twice. *)
Lemma zero_ext_8_idem (v : Int.int) :
  Int.zero_ext 8 (Int.zero_ext 8 v) = Int.zero_ext 8 v.
Proof.
apply Int.zero_ext_idem.
lia.
Qed.

(** An 8-bit truncation IS the low byte: the C-side [Int] value and
    the model-side [Z.land _ 255] are the same [val]. This is
    libshrincs' [zero_ext_8_byte] restated over [Z.land] rather than
    over a range hypothesis. *)
Lemma zero_ext_8_Vubyte (v : Int.int) :
  Vint (Int.zero_ext 8 v) = Vubyte (Byte.repr (Z.land (Int.unsigned v) 255)).
Proof.
unfold Vubyte, Int.zero_ext.
f_equal.
f_equal.
rewrite Byte.unsigned_repr_eq.
rewrite Zbits.Zzero_ext_mod by lia.
change 255 with (Z.ones 8).
rewrite Z.land_ones by lia.
change (two_p 8) with 256.
change (2 ^ 8) with 256.
change Byte.modulus with 256.
now rewrite Zmod_mod.
Qed.

(** [Int.shru] by an in-range amount loses nothing to the [Int.repr]
    it is defined by, because a right shift only shrinks the value.
    This is libshrincs' [div_mod256_mod2pow32] in shift form. *)
Lemma int_unsigned_shru_eq (x : Int.int) (k : Z) :
  0 <= k < 32 -> Int.unsigned (Int.shru x (Int.repr k)) = Z.shiftr (Int.unsigned x) k.
Proof.
intros Hk.
pose proof (Int.unsigned_range x) as Hrange.
change Int.modulus with 4294967296 in Hrange.
assert (Hpow : 1 <= 2 ^ k).
{ change 1 with (2 ^ 0).
  apply Z.pow_le_mono_r; lia. }
assert (Hk32 : 0 <= k <= Int.max_unsigned) by rep_lia.
(* the shifted value still fits in 32 bits, so neither [Int.repr]
   inside [Int.shru] wraps *)
assert (Hshift : 0 <= Z.shiftr (Int.unsigned x) k <= Int.max_unsigned).
{ rewrite Z.shiftr_div_pow2 by lia.
  change Int.max_unsigned with 4294967295.
  assert (Hlo : 0 <= Int.unsigned x / 2 ^ k)
    by (apply Z.div_pos; lia).
  assert (Hhi : Int.unsigned x / 2 ^ k <= Int.unsigned x)
    by (apply Z.div_le_upper_bound; nia).
  lia. }
unfold Int.shru.
rewrite (Int.unsigned_repr _ Hk32).
now rewrite (Int.unsigned_repr _ Hshift).
Qed.

(** The whole bridge, in the shape the final entailment needs: the
    four values the C stores are the funspec's byte list. *)
Lemma store_be32_bytes_eq (x : Int.int) :
  List.map (fun z : Z => Vubyte (Byte.repr z)) (bytes_of_word U32 (w32_of_int x))
  = [Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru x (Int.repr 24))));
     Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru x (Int.repr 16))));
     Vint (Int.zero_ext 8 (Int.zero_ext 8 (Int.shru x (Int.repr 8))));
     Vint (Int.zero_ext 8 (Int.zero_ext 8 x))].
Proof.
rewrite bytes_of_word_U32_eq.
rewrite wunsigned_w32_of_int.
rewrite !zero_ext_8_idem.
(* delta restricted to List.map: a bare simpl unfolds Byte.repr and hangs *)
cbn [List.map].
rewrite !zero_ext_8_Vubyte.
rewrite (int_unsigned_shru_eq x 24) by lia.
rewrite (int_unsigned_shru_eq x 16) by lia.
rewrite (int_unsigned_shru_eq x 8) by lia.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The body proof *)

Lemma body_store_be32 : semax_body Vprog_sha Gprog_sha f_store_be32 spec_store_be32.
Proof.
start_function.
(* p[0] = (uint8_t)(x >> 24) *)
forward.
(* p[1] = (uint8_t)(x >> 16) *)
forward.
(* p[2] = (uint8_t)(x >> 8) *)
forward.
(* p[3] = (uint8_t)x *)
forward.

(* The two data_at's differ only in their value list: VST holds the
   four stores as an upd_Znth chain over default_val, the funspec
   holds bytes_of_word. list_solve reconciles the chain; the
   arithmetic is store_be32_bytes_eq. *)
entailer!.
apply derives_refl'.
f_equal.
rewrite store_be32_bytes_eq.
list_solve.
Qed.
