(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.arith_xor: [Int.xor] / [Int.or] byte facts.

    [Int.xor] / [Int.or] equal-zero characterizations and [uint8_t] range
    preservation, plus [zero_ext 8] on an in-range [int]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.data_at.
From Vst Require Import theory.pure.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Int xor/or byte facts.

    Zero-tests and 8-bit range closure for [Int.xor] / [Int.or], plus
    the [Int.zero_ext 8] fixed-point fact; used by the constant-time
    byte-compare ([body_shrincs_ct_memcmp]) and byte stores. *)

(** Two ints are equal iff their XOR is zero. *)
Lemma int_xor_eq_zero_iff (a b : int) :
  Int.xor a b = Int.zero <-> a = b.
Proof.
  split; intro H.
  - apply Int.same_bits_eq; intros i Hi.
    pose proof (Int.bits_xor a b i Hi) as Hbit.
    assert (Hz : Int.testbit (Int.xor a b) i = false).
    { rewrite H. apply Int.bits_zero. }
    rewrite Hbit in Hz.
    destruct (Int.testbit a i), (Int.testbit b i); simpl in Hz; congruence.
  - subst. apply Int.xor_idem.
Qed.

(** Bitwise OR is zero iff each operand is zero. *)
Lemma int_or_eq_zero_iff (a b : int) :
  Int.or a b = Int.zero <-> a = Int.zero /\ b = Int.zero.
Proof.
  split.
  - intro H. split; apply Int.same_bits_eq; intros i Hi.
    + pose proof (Int.bits_or a b i Hi) as Hbit.
      assert (Hz : Int.testbit (Int.or a b) i = false).
      { rewrite H. apply Int.bits_zero. }
      rewrite Hbit in Hz. rewrite Int.bits_zero.
      destruct (Int.testbit a i); simpl in Hz; congruence.
    + pose proof (Int.bits_or a b i Hi) as Hbit.
      assert (Hz : Int.testbit (Int.or a b) i = false).
      { rewrite H. apply Int.bits_zero. }
      rewrite Hbit in Hz. rewrite Int.bits_zero.
      destruct (Int.testbit a i), (Int.testbit b i); simpl in Hz; congruence.
  - intros [Ha Hb]. subst. apply Int.or_zero.
Qed.

(** If [a, b] both fit in 8 bits then so does [Int.xor a b]. *)
Lemma int_xor_byte_bound (a b : int) :
  0 <= Int.unsigned a < 256 ->
  0 <= Int.unsigned b < 256 ->
  0 <= Int.unsigned (Int.xor a b) < 256.
Proof.
  intros Ha Hb.
  unfold Int.xor.
  rewrite Int.unsigned_repr_eq.
  assert (Hnn : 0 <= Z.lxor (Int.unsigned a) (Int.unsigned b))
    by (apply Z.lxor_nonneg; lia).
  assert (Ha8 : Z.log2 (Int.unsigned a) < 8).
  { destruct (Z.eq_dec (Int.unsigned a) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hb8 : Z.log2 (Int.unsigned b) < 8).
  { destruct (Z.eq_dec (Int.unsigned b) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hub : Z.lxor (Int.unsigned a) (Int.unsigned b) < 256).
  { destruct (Z.eq_dec (Z.lxor (Int.unsigned a) (Int.unsigned b)) 0) as [E|E].
    { rewrite E. lia. }
    change 256 with (2 ^ 8).
    apply Z.log2_lt_pow2; [lia| ].
    apply (Z.le_lt_trans _ (Z.max (Z.log2 (Int.unsigned a)) (Z.log2 (Int.unsigned b))) _).
    { apply Z.log2_lxor; lia. }
    apply Z.max_lub_lt; lia. }
  rewrite Z.mod_small by (change Int.modulus with 4294967296; lia).
  lia.
Qed.

(** If [a, b] both fit in 8 bits then so does [Int.or a b]. *)
Lemma int_or_byte_bound (a b : int) :
  0 <= Int.unsigned a < 256 ->
  0 <= Int.unsigned b < 256 ->
  0 <= Int.unsigned (Int.or a b) < 256.
Proof.
  intros Ha Hb.
  unfold Int.or.
  rewrite Int.unsigned_repr_eq.
  assert (Hnn : 0 <= Z.lor (Int.unsigned a) (Int.unsigned b))
    by (apply Z.lor_nonneg; lia).
  assert (Ha8 : Z.log2 (Int.unsigned a) < 8).
  { destruct (Z.eq_dec (Int.unsigned a) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hb8 : Z.log2 (Int.unsigned b) < 8).
  { destruct (Z.eq_dec (Int.unsigned b) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hub : Z.lor (Int.unsigned a) (Int.unsigned b) < 256).
  { destruct (Z.eq_dec (Z.lor (Int.unsigned a) (Int.unsigned b)) 0) as [E|E].
    { rewrite E. lia. }
    change 256 with (2 ^ 8).
    apply Z.log2_lt_pow2; [lia| ].
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; lia. }
  rewrite Z.mod_small by (change Int.modulus with 4294967296; lia).
  lia.
Qed.

(** Byte-bounded ints are fixed points of [Int.zero_ext 8]. *)
Lemma zero_ext_8_byte (x : int) :
  0 <= Int.unsigned x < 256 ->
  Int.zero_ext 8 x = x.
Proof.
  intros H. apply zero_ext_inrange.
  change (two_p 8) with 256. lia.
Qed.

