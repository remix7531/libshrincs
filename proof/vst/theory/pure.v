(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * theory.pure: VST-free pure-Z / Gallina arithmetic lemmas.

    The tier-1 math layer: lemmas whose statement and proof mention no
    VST/Floyd machinery (no [Int], [Vint], [Vubyte], [val], [data_at],
    [reptype], [mpred], [Ptrofs], [force_val]) and use only [lia] /
    [induction] / [cbn] / stdlib [Z.*] rewrites.

    These were factored out of [contract.lemmas.arith] so they can live
    below the separation-logic layer. [contract.lemmas.arith] imports
    this file for the [to_byte] shape, [div_mod256_mod2pow32],
    [Z_testbit_above_8], [Zland_15_mod16] and [list_sum_le_bound] facts
    it builds its VST bridges on top of. *)

From Stdlib Require Import List ZArith Lia.

From Vst Require Import model.wots.

Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** [to_byte] -- lengths. *)

Lemma to_byte_length : forall y x,
  length (to_byte x y) = y.
Proof.
  induction y; intros; cbn; [reflexivity|].
  rewrite length_app, IHy. cbn. lia.
Qed.

Lemma to_byte_Zlength : forall x y,
  Zlength (to_byte x y) = Z.of_nat y.
Proof. intros. rewrite Zlength_correct, to_byte_length. reflexivity. Qed.

Lemma byte_mod256_0 : byte_mod256 0 = zero_byte.
Proof. apply byte_eq. reflexivity. Qed.

Lemma to_byte_0_zeros : forall y,
  to_byte 0 y = repeat zero_byte y.
Proof.
  induction y; [reflexivity|].
  cbn [to_byte].
  change (0 / 256) with 0.
  rewrite IHy, byte_mod256_0, <- repeat_cons.
  reflexivity.
Qed.

Lemma to_byte_small : forall (x : Z) (y : nat),
  0 <= x < 256 -> (0 < y)%nat ->
  to_byte x y = repeat zero_byte (Nat.pred y) ++ [byte_mod256 x].
Proof.
  intros x y Hx Hy.
  destruct y; [lia|].
  cbn [to_byte Nat.pred].
  assert (Hdiv : x / 256 = 0) by (apply Zdiv_small; lia).
  rewrite Hdiv, to_byte_0_zeros.
  reflexivity.
Qed.

(** [firstn (S n) l = firstn n l ++ [nth n l d]] when [n < length l]. *)
Lemma firstn_S_snoc : forall [A : Type] n (l : list A) d,
  (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n; intros [|x xs] d Hn; cbn in *; try lia.
  - reflexivity.
  - rewrite (IHn xs d) by lia. reflexivity.
Qed.

(* ================================================================= *)
(** ** [to_byte x 4] as four big-endian byte shifts of a 32-bit word. *)

Lemma to_byte_4_eq : forall x,
  to_byte x 4 = [byte_mod256 (x / 2^24);
                byte_mod256 (x / 2^16);
                byte_mod256 (x / 2^8);
                byte_mod256 x].
Proof.
  intros.
  cbn [to_byte app].
  rewrite !Zdiv_Zdiv by lia.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** 2-byte big-endian counter encode / decode (WOTS+C prepended
    16-bit grinding counter). *)

(** [to_byte x 2] as two big-endian byte shifts. *)
Lemma to_byte_2_eq : forall x,
  to_byte x 2 = [byte_mod256 (x / 2 ^ 8); byte_mod256 x].
Proof.
  intros.
  cbn [to_byte app].
  change (2 ^ 8) with 256.
  reflexivity.
Qed.

(** Big-endian recomposition: a 16-bit value from its two to_byte bytes
    (decode direction; companion to [to_byte_2_eq]). *)
Lemma word_be_recompose_2 : forall counter,
  0 <= counter < 2 ^ 16 ->
  (counter / 2 ^ 8 mod 256) * 2 ^ 8 + counter mod 256 = counter.
Proof.
  intros counter H.
  change (2 ^ 8) with 256 in *. change (2 ^ 16) with 65536 in H.
  assert (H8 : counter / 256 mod 256 = counter / 256)
    by (apply Z.mod_small; split;
        [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite H8.
  pose proof (Z.div_mod counter 256 ltac:(lia)).
  lia.
Qed.

(* ================================================================= *)
(** ** Byte-extraction arithmetic (support for the [zero_ext] bridges
    in [contract.lemmas.arith]). *)

(** Extracting one of the four big-endian bytes of a 32-bit word.
    Key arithmetic identity used in the byte-extraction proof.
    For [k <= 24], the top 32-[k] bits of [v / 2^k] contribute only
    multiples of 256, hence vanish mod 256. *)
Lemma div_mod256_mod2pow32 : forall v k,
  (k = 0 \/ k = 8 \/ k = 16 \/ k = 24) ->
  (v mod 2^32) / 2^k mod 256 = v / 2^k mod 256.
Proof.
  intros v k Hk.

  assert (Hfact : exists m, 2^32 = 2^k * m /\ (256 | m) /\ 0 < 2^k).
  { destruct Hk as [Hc|[Hc|[Hc|Hc]]]; subst k.
    - exists 4294967296.
      split; [reflexivity | split; [exists 16777216; reflexivity | lia]].
    - exists 16777216.
      split; [reflexivity | split; [exists 65536;    reflexivity | lia]].
    - exists 65536.
      split; [reflexivity | split; [exists 256;      reflexivity | lia]].
    - exists 256.
      split; [reflexivity | split; [exists 1;        reflexivity | lia]]. }

  destruct Hfact as [m [H32 [[c Hc] Hk0]]].

  set (q := v / 2^32).
  set (r := v mod 2^32).
  replace v with (2^32 * q + r) by (unfold q, r; symmetry; apply Z.div_mod; lia).
  rewrite H32.
  replace (2^k * m * q + r) with (((c * q) * 256) * 2^k + r) by (rewrite Hc; ring).
  rewrite Z.div_add_l by lia.
  rewrite <- Z.add_mod_idemp_l by lia.
  rewrite Z.mod_mul by lia.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** [to_byte] ignores bits above its byte width: a fixed-width
    serialization reads only the low bytes of its argument, so two
    values congruent below that width serialize to the same bytes. *)

(** Two values congruent mod 256 have the same [byte_mod256]. *)
Lemma byte_mod256_congr : forall a b, a mod 256 = b mod 256 -> byte_mod256 a = byte_mod256 b.
Proof.
  intros a b H. apply byte_eq. unfold byte_val, byte_mod256.
  rewrite !machine.Byte.unsigned_repr_eq, byte_modulus. exact H.
Qed.

(** [to_byte _ 4] depends only on the low 32 bits. *)
Lemma to_byte_mod2pow32 : forall v, to_byte (v mod 2 ^ 32) 4 = to_byte v 4.
Proof.
  intros v.
  assert (Hk0 : (v mod 2 ^ 32) mod 256 = v mod 256).
  { pose proof (div_mod256_mod2pow32 v 0 ltac:(tauto)) as H.
    change (2 ^ 0) with 1 in H. rewrite !Z.div_1_r in H. exact H. }
  rewrite !to_byte_4_eq.
  do 3 (apply f_equal2; [apply byte_mod256_congr; apply div_mod256_mod2pow32; tauto|]).
  apply f_equal2; [apply byte_mod256_congr; exact Hk0 | reflexivity].
Qed.

(** Bit [i >= 8] of any value [< 256] is zero. *)
Lemma Z_testbit_above_8 : forall x i,
  0 <= x < 256 -> 8 <= i -> Z.testbit x i = false.
Proof.
  intros x i Hx Hi.
  apply Z.bits_above_log2; [lia|].
  destruct (Z.eq_dec x 0) as [->|Hne]; [simpl; lia|].
  assert (Z.log2 x < 8) by (apply Z.log2_lt_pow2; [lia | change (2^8) with 256; lia]).
  lia.
Qed.

(** [Z.land x 15 = x mod 16] for nonnegative [x]. *)
Lemma Zland_15_mod16 : forall x : Z, 0 <= x -> Z.land x 15 = x mod 16.
Proof.
  intros x Hx.
  change 15 with (Z.ones 4).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** [list_sum] bound (constant-sum gate support). *)

Lemma list_sum_le_bound : forall (l : list nat) (b : nat),
  Forall (fun x => (x <= b)%nat) l -> (list_sum l <= length l * b)%nat.
Proof.
  induction l as [|x xs IH]; intros b Hall; simpl.
  - lia.
  - inversion Hall as [|? ? Hx Hxs]; subst.
    specialize (IH b Hxs).
    lia.
Qed.
