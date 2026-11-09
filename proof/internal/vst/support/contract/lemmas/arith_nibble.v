(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.arith_nibble: nibble extraction and base-16 digit facts.

    [nibble_f] and the [flat_map nibble_f] digit bookkeeping (length, the
    per-nibble [<= 15] bound) that [body_shrincs_wots_map_digest] uses, plus the
    [digest_of] / [digits_to_vals] length lemmas and the digit-sum bound for
    the constant-sum gate. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.data_at.
From Vst Require Import theory.pure.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Nibble extraction (for [body_expand_digits]). *)

(** For a byte [0 <= x < 256]:
    - [Int.shr] by 4 equals [x / 16].
    - [Int.and] with 15 equals [x mod 16].
    The [zero_ext 8 (zero_ext 8 _)] wrapper is what Clight produces for
    [(uint8_t)(x >> 4)] / [(uint8_t)(x & 0xf)]. *)
Lemma nibble_hi : forall x : Z, 0 <= x < 256 ->
  Int.zero_ext 8 (Int.zero_ext 8
    (Int.shr (Int.repr x) (Int.repr 4))) = Int.repr (x / 16).
Proof.
  intros x Hx.

  assert (Hs : Int.signed (Int.repr x) = x)
    by (apply Int.signed_repr; rep_lia).
  unfold Int.shr.
  rewrite Hs.
  change (Int.unsigned (Int.repr 4)) with 4.
  rewrite Int.zero_ext_idem by lia.

  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite !Int.testbit_repr by (try destruct (zlt i 8); lia).
  destruct (zlt i 8).
  - rewrite Z.shiftr_div_pow2 by lia.
    change (2^4) with 16.
    reflexivity.
  - symmetry.
    apply Z_testbit_above_8; [|lia].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma Int_and_15 : forall x,
  Int.and (Int.repr x) (Int.repr 15) = Int.repr (Z.land x 15).
Proof.
  intros x.
  apply Int.same_bits_eq.
  intros j Hj.
  rewrite Int.bits_and by lia.
  rewrite !Int.testbit_repr by lia.
  rewrite Z.land_spec.
  reflexivity.
Qed.

Lemma nibble_lo : forall x : Z, 0 <= x < 256 ->
  Int.zero_ext 8 (Int.zero_ext 8
    (Int.and (Int.repr x) (Int.repr 15))) = Int.repr (x mod 16).
Proof.
  intros x Hx.

  rewrite Int.zero_ext_idem by lia.
  rewrite Int_and_15, Zland_15_mod16 by lia.

  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite !Int.testbit_repr by lia.
  assert (Hmod : 0 <= x mod 16 < 16) by (apply Z.mod_pos_bound; lia).
  destruct (zlt i 8); [reflexivity|].

  symmetry.
  apply Z_testbit_above_8; [lia | lia].
Qed.

(* ================================================================= *)
(** ** Nibble-store reductions (for the digit-expansion stores).

    Clight lowers [digits[..] = (uint8_t)(hg[i] >> 4)] and
    [digits[..] = (uint8_t)(hg[i] & 0x0f)] to a [sem_cast_i2i] over a
    [sem_shift_ii] / [sem_and].  These two lemmas collapse those into
    the abstract nibbles [b / 16] and [b mod 16] (via [nibble_hi] /
    [nibble_lo] above), so the store re-establishes the
    [nibble_step_shape] invariant. *)

Lemma digest_store_hi : forall z : Z,
  force_val
    (sem_cast_i2i I8 Unsigned
       (force_val
          (sem_shift_ii
             (fun (sg : signedness) (n1 n2 : int) =>
                match sg with
                | Signed => Int.shr n1 n2
                | Unsigned => Int.shru n1 n2
                end)
             Signed (Vubyte (Byte.repr z)) (Vint (Int.repr 4)))))
  = Vint (Int.repr (Byte.unsigned (Byte.repr z) / 16)).
Proof.
  intros z.
  unfold Vubyte.
  cbn [force_val sem_cast_i2i sem_shift_ii cast_int_int].
  f_equal.
  rewrite <- (Int.zero_ext_idem 8) by lia.
  apply nibble_hi.
  rep_lia.
Qed.

Lemma digest_store_lo : forall z : Z,
  force_val
    (sem_cast_i2i I8 Unsigned
       (force_val
          (sem_and tuchar tint (Vubyte (Byte.repr z)) (Vint (Int.repr 15)))))
  = Vint (Int.repr (Byte.unsigned (Byte.repr z) mod 16)).
Proof.
  intros z.
  unfold Vubyte, sem_and.
  simpl.
  f_equal.
  rewrite <- (Int.zero_ext_idem 8) by lia.
  apply nibble_lo.
  rep_lia.
Qed.

(** The nibble-extraction function. *)
Definition nibble_f (b : byte) : list nat :=
  [Z.to_nat (b / 16); Z.to_nat (b mod 16)].

Lemma length_flat_map_nibble_f : forall l : list byte,
  length (flat_map nibble_f l) = (length l * 2)%nat.
Proof.
  induction l as [|x xs IH]; [reflexivity|]. 
  simpl.
  rewrite IH. 
  lia.
Qed.

Lemma Zlength_flat_map_nibble_f : forall l : block,
  Zlength (flat_map nibble_f l) = Zlength l * 2.
Proof.
  intros. 
  rewrite !Zlength_correct. 
  rewrite length_flat_map_nibble_f.
  lia.
Qed.

(** For [Zlength msg = 16] (the [H_grind] output), the full [base_2b msg 32]
    is the un-truncated [flat_map] since it has exactly 32 entries. *)
Lemma base_2b_full_16 : forall msg : block,
  Zlength msg = 16 -> base_2b msg 32 = flat_map nibble_f msg.
Proof.
  intros msg HlM.
  unfold base_2b.
  pose proof (length_flat_map_nibble_f msg) as Hlen.
  rewrite Zlength_correct in HlM.
  assert (Hn : length msg = 16%nat) by lia.
  rewrite Hn in Hlen.
  apply firstn_all2.
  lia.
Qed.

Lemma flat_map_nibble_f_sublist_step :
  forall (msg : block) (i : Z),
    0 <= i < Zlength msg ->
    flat_map nibble_f (sublist 0 (i+1) msg) =
    flat_map nibble_f (sublist 0 i msg) ++ nibble_f (Znth i msg).
Proof.
  intros msg i Hi.
  rewrite (sublist_split 0 i (i+1)) by lia.
  rewrite <- flat_map_app.
  rewrite (sublist_one i (i+1) msg) by lia.
  reflexivity.
Qed.

(** Shape step using [flat_map nibble_f (sublist 0 i msg)]. *)
Lemma nibble_step_shape :
  forall (msg : block) (i : Z),
    0 <= i < 16 -> Zlength msg = 16 ->
    let b := Byte.unsigned (Byte.repr (Znth i msg)) in
    upd_Znth (2 * i + 1)
      (upd_Znth (2 * i)
        (digits_to_vals (flat_map nibble_f (sublist 0 i msg))
          ++ Zrepeat Vundef (32 - 2*i))
        (Vint (Int.repr (b / 16))))
      (Vint (Int.repr (b mod 16)))
    = digits_to_vals (flat_map nibble_f (sublist 0 (i+1) msg))
      ++ Zrepeat Vundef (32 - 2*(i+1)).
Proof.
  intros msg i Hi HlM b.

  assert (Hbyte : byte_val (Znth i msg) = b).
  { subst b.
    rewrite Byte.unsigned_repr; [reflexivity|].
    pose proof (byte_val_range (Znth i msg)).
    rep_lia. }
  assert (Hb_rng : 0 <= b < 256)
    by (subst b; pose proof (Byte.unsigned_range
                  (Byte.repr (Znth i msg))); rep_lia).

  rewrite flat_map_nibble_f_sublist_step by lia.
  set (D := digits_to_vals (flat_map nibble_f (sublist 0 i msg))).
  assert (HDlen : Zlength D = 2 * i).
  { subst D.
    rewrite Zlength_digits_to_vals, Zlength_flat_map_nibble_f.
    rewrite Zlength_sublist by lia.
    lia. }

  unfold digits_to_vals.
  rewrite map_app.
  fold digits_to_vals.
  fold D.
  change (map (fun d : nat => Vubyte (Byte.repr (Z.of_nat d)))
          (flat_map nibble_f (sublist 0 i msg))) with D.
  unfold nibble_f.
  rewrite Hbyte.
  simpl map.
  change (let (q, _) := Z.div_eucl b 16 in q) with (b / 16).

  assert (Hdiv : 0 <= b / 16 < 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hmod : 0 <= b mod 16 < 256)
    by (pose proof (Z.mod_pos_bound b 16 ltac:(lia)); lia).
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).

  assert (Hvb : forall x, 0 <= x < 256 ->
    Vubyte (Byte.repr x) = Vint (Int.repr x)).
  { intros x Hx. 
    unfold Vubyte.
    do 2 f_equal.
    rewrite Byte.unsigned_repr by rep_lia.
    reflexivity. }

  rewrite (Hvb _ Hdiv), (Hvb _ Hmod).

  list_solve.
Qed.

(* ================================================================= *)
(** ** [flat_map nibble_f] digit facts (length + per-nibble [<= 15] bound).

    Support the [digest_of] length/bound lemmas just below (and thereby
    the constant-sum gate); the digest is [base_2b] over the [H_grind]
    output, i.e. the full [flat_map nibble_f]. *)

Lemma Zlength_flat_map_nibble_f_16 : forall msg,
  Zlength msg = 16 -> Zlength (flat_map nibble_f msg) = 32.
Proof.
  intros. rewrite Zlength_flat_map_nibble_f. lia.
Qed.

(** Every element of [flat_map nibble_f msg] is <= 15 ([byte]'s range
    is intrinsic now, so this needs no hypothesis on [msg]). *)
Lemma Forall_flat_map_nibble_f_le_15 : forall msg : block,
  Forall (fun n => (n <= 15)%nat) (flat_map nibble_f msg).
Proof.
  intros msg.
  induction msg as [|b rest IH]; simpl.
  - constructor.
  - pose proof (byte_val_range b) as Hb.
    constructor; [|constructor].
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by (apply Z.div_pos; lia).
      assert (Hle : b / 16 <= 255 / 16).
      { apply Z.div_le_mono; lia. }
      change (255 / 16) with 15 in Hle.
      assumption.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).
      assert (0 <= b mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      lia.
    + apply IH.
Qed.

Lemma nibble_le_15 : forall (msg : block) (k : Z),
  Zlength msg = 16 ->
  0 <= k < 32 ->
  (Znth k (flat_map nibble_f msg) <= 15)%nat.
Proof.
  intros msg k HlM Hk.
  pose proof (Forall_flat_map_nibble_f_le_15 msg) as HF.
  rewrite Forall_Znth in HF.
  apply HF.
  rewrite Zlength_flat_map_nibble_f_16; lia.
Qed.

(* ================================================================= *)
(** ** [digest_of] / [digits_to_vals] lengths.

    The grinding digest is [base_2b] over the 16-byte truncated [H_grind]
    output, so it has exactly [len = 32] nibbles and equals the full
    flat_map (of the grind-typed address). *)

Lemma H_grind_Zlength : forall pk_seed a m counter,
  Zlength (H_grind pk_seed a m counter) = 16.
Proof.
  intros. unfold H_grind, trunc16.
  rewrite Zlength_correct, length_firstn, length_sha256'. reflexivity.
Qed.

Lemma digest_of_flat_map : forall pk_seed a m counter,
  digest_of pk_seed a m counter
  = flat_map nibble_f (H_grind pk_seed (shrincs_wots_grind_adrs a) m counter).
Proof.
  intros. unfold digest_of.
  change (Z.of_nat len) with 32.
  apply base_2b_full_16. apply H_grind_Zlength.
Qed.

Lemma digest_of_Zlength : forall pk_seed a m counter,
  Zlength (digest_of pk_seed a m counter) = 32.
Proof.
  intros. rewrite digest_of_flat_map.
  apply Zlength_flat_map_nibble_f_16. apply H_grind_Zlength.
Qed.

Lemma nth_digest_le_15 : forall pk_seed a m counter k,
  0 <= k < 32 ->
  (Znth k (digest_of pk_seed a m counter) <= 15)%nat.
Proof.
  intros pk_seed a m counter k Hk.
  rewrite digest_of_flat_map.
  apply nibble_le_15; [apply H_grind_Zlength | exact Hk].
Qed.

(** *** Digit-sum bound (constant-sum gate).

    Bound the digit sum so the C [== 240] test can be reflected back
    into the model's [good_counter] (a [Nat.eqb] on the sum).  All pure
    [Z]/[nat]; no separation logic, no [find_counter] reduction. *)

Lemma digest_sum_bound : forall pk_seed a m counter,
  (list_sum (digest_of pk_seed a m counter) <= 480)%nat.
Proof.
  intros pk_seed a m counter.
  rewrite digest_of_flat_map.
  pose proof (Forall_flat_map_nibble_f_le_15
                (H_grind pk_seed (shrincs_wots_grind_adrs a) m counter)) as HF.
  pose proof (list_sum_le_bound _ 15 HF) as Hle.
  assert (Hlen : length (H_grind pk_seed (shrincs_wots_grind_adrs a) m counter) = 16%nat).
  { pose proof (H_grind_Zlength pk_seed (shrincs_wots_grind_adrs a) m counter) as HZ.
    rewrite Zlength_correct in HZ. lia. }
  rewrite length_flat_map_nibble_f, Hlen in Hle.
  lia.
Qed.

(** Reflect the C's [sum == 240] test back into the model: the digit sum
    is bounded by 480 ([digest_sum_bound]), so the [Int.repr] equality the
    guard leaves is injective.  Shared by the constant-sum gates in
    [body_shrincs_wots_grind_to_constant_sum] and
    [body_shrincs_wots_pubkey_from_sig]. *)
Lemma digest_sum_repr_240 : forall pk_seed a m counter,
  Int.repr (Z.of_nat (list_sum (digest_of pk_seed a m counter))) = Int.repr 240 ->
  Z.of_nat (list_sum (digest_of pk_seed a m counter)) = 240.
Proof.
  intros pk_seed a m counter H.
  pose proof (digest_sum_bound pk_seed a m counter) as Hb.
  apply repr_inj_unsigned; [ rep_lia | rep_lia | exact H ].
Qed.

