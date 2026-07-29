(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.arith_nibble: nibble extraction and base-16 digit facts.

    Two layers.  Below: the Clight-level nibble bridges ([nibble_hi] /
    [nibble_lo] and the two store reductions) that
    [body_shrincs_wots_map_digest] needs to read [hg[i] >> 4] and
    [hg[i] & 0x0f] as [b / 16] and [b mod 16].  Above: the digit-vector
    facts the WOTS+C bodies consume.

    The digit vector is the port's [digest_of], whose byte-wise nibble
    split ([digest_of_nib]) and range/length facts are already proved in
    [Model.theory.shrincs] -- the port's generic [base_2b] never has to
    be unfolded here.  This file only restates that shape at VST's
    [Zlength] / [Znth] / [upd_Znth] and bounds the digit sum for the
    constant-sum gate.  The digits are [Z] (the spec's ints are [Z]
    throughout -- model/PORTING.md), so no [Z.of_nat] appears. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.data_at.
From Vst Require Import theory.pure.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** Nibble extraction (for [body_shrincs_wots_map_digest]). *)

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

(* ================================================================= *)
(** ** The port's nibble split [nib], at VST's indexing.

    [Model.theory.shrincs.nib x j] is the pair of nibbles of byte [j] of
    [x], read through the spec's own [index]; the digit vector is
    [flat_map (nib hg) (range 0 16)] ([digest_of_nib]).  What the C loop
    needs on top of that: the [range] step it advances by, the [Znth]
    form of one [nib], the prefix length, and the store shape those
    three assemble into. *)

Lemma flat_map_nib_step : forall (x : block) (i : Z), 0 <= i ->
  flat_map (nib x) (shrincs.range 0 (i + 1))
  = flat_map (nib x) (shrincs.range 0 i) ++ nib x i.
Proof.
  intros x i Hi.
  unfold shrincs.range.
  replace (Z.to_nat (i + 1 - 0)) with (S (Z.to_nat (i - 0))) by lia.
  rewrite seq_S, map_app.
  (* [flat_map_app] is VST's, stated right-to-left *)
  rewrite <- flat_map_app.
  cbn [map flat_map].
  rewrite app_nil_r.
  f_equal.
  f_equal.
  lia.
Qed.

(** The spec reads a byte with [index] (0 out of range); VST reads it
    with [Znth] (the [Inhabitant_byte] default is the same [zero_byte]),
    so in range the two agree. *)
Lemma nib_Znth : forall (x : block) (i : Z), 0 <= i ->
  nib x i = [Znth i x / 16; Znth i x mod 16].
Proof.
  intros x i Hi.
  unfold nib, shrincs.index, Znth.
  destruct (Z_lt_dec i 0); [lia|].
  rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

Lemma length_flat_map_nib : forall (x : block) (l : list Z),
  length (flat_map (nib x) l) = (2 * length l)%nat.
Proof.
  intros x.
  induction l as [|j l IH]; [reflexivity|].
  cbn [flat_map length].
  rewrite length_app, IH.
  unfold nib.
  cbn [length].
  lia.
Qed.

Lemma Zlength_flat_map_nib : forall (x : block) (i : Z), 0 <= i ->
  Zlength (flat_map (nib x) (shrincs.range 0 i)) = 2 * i.
Proof.
  intros x i Hi.
  rewrite Zlength_correct, length_flat_map_nib, length_range.
  lia.
Qed.

(** One step of the digit-expansion loop: storing the two nibbles of
    byte [i] over the two [Vundef] cells at [2i] / [2i+1] extends the
    [flat_map (nib msg)] prefix by one index. *)
Lemma nibble_step_shape :
  forall (msg : block) (i : Z),
    0 <= i < 16 -> Zlength msg = 16 ->
    let b := Byte.unsigned (Byte.repr (Znth i msg)) in
    upd_Znth (2 * i + 1)
      (upd_Znth (2 * i)
        (digits_to_vals (flat_map (nib msg) (shrincs.range 0 i))
          ++ Zrepeat Vundef (32 - 2*i))
        (Vint (Int.repr (b / 16))))
      (Vint (Int.repr (b mod 16)))
    = digits_to_vals (flat_map (nib msg) (shrincs.range 0 (i+1)))
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

  rewrite flat_map_nib_step, nib_Znth by lia.
  set (D := digits_to_vals (flat_map (nib msg) (shrincs.range 0 i))).
  assert (HDlen : Zlength D = 2 * i)
    by (subst D; rewrite Zlength_digits_to_vals, Zlength_flat_map_nib; lia).

  unfold digits_to_vals.
  rewrite map_app.
  cbn [map].
  rewrite Hbyte.
  change (map (fun d : Z => Vubyte (Byte.repr d))
            (flat_map (nib msg) (shrincs.range 0 i))) with D.

  assert (Hdiv : 0 <= b / 16 < 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hmod : 0 <= b mod 16 < 256)
    by (pose proof (Z.mod_pos_bound b 16 ltac:(lia)); lia).

  (* the two stores are [Vint]s; the invariant carries [Vubyte]s *)
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
(** ** [digest_of] at VST's [Zlength] / [Znth].

    The grinding digest is [base_2b] at [b = 4] over the 16-byte
    [H_grind] output, so it has exactly [len = 32] nibbles.  The C keys
    it on the DEPENDENT grind address; the port keys it on that
    address's anchor, and [adrs_bytes_grind] is the bridge. *)

Lemma H_grind_Zlength : forall pk_seed A m counter,
  Zlength (shrincs.H_grind pk_seed A m counter) = 16.
Proof.
  intros. rewrite Zlength_correct, length_H_grind. reflexivity.
Qed.

Lemma digest_of_flat_map : forall pk_seed (a : adrs) m counter,
  digest_of pk_seed (anchor_nh a) (anchor_ni a) m counter
  = flat_map
      (nib (shrincs.H_grind pk_seed (adrs_bytes (shrincs_wots_grind_adrs a)) m counter))
      (shrincs.range 0 16).
Proof.
  intros. rewrite digest_of_nib, adrs_bytes_grind. reflexivity.
Qed.

Lemma digest_of_Zlength : forall pk_seed nh ni m counter,
  Zlength (digest_of pk_seed nh ni m counter) = 32.
Proof.
  intros. rewrite Zlength_correct, length_digest_of. reflexivity.
Qed.

(** Every digit is a base-16 digit -- unconditional in [k], since the
    port's [index_int] reads 0 out of range. *)
Lemma nth_digest_le_15 : forall pk_seed nh ni m counter k,
  0 <= k ->
  0 <= Znth k (digest_of pk_seed nh ni m counter) <= 15.
Proof.
  intros pk_seed nh ni m counter k Hk.
  rewrite Znth_index_int by lia.
  apply index_int_digest_of_range.
Qed.

(** *** Digit-sum bound (constant-sum gate).

    Bound the digit sum so the C [== 240] test can be reflected back
    into the model's [good_counter] (via [good_counter_Z_iff]).  All
    pure [Z]; no separation logic, no [find_counter] reduction. *)

Lemma digest_sum_bound : forall pk_seed nh ni m counter,
  0 <= shrincs.sum_list (digest_of pk_seed nh ni m counter) <= 480.
Proof.
  intros pk_seed nh ni m counter.
  assert (HF : Forall (fun d => 0 <= d <= 15) (digest_of pk_seed nh ni m counter))
    by (apply Forall_forall; intros d Hd;
        exact (digest_of_In_range _ _ _ _ _ _ Hd)).
  pose proof (sum_list_le_bound _ 15 ltac:(lia) HF) as Hle.
  rewrite length_digest_of in Hle.
  lia.
Qed.

(** Reflect the C's [sum == 240] test back into the model: the digit sum
    is bounded by 480 ([digest_sum_bound]), so the [Int.repr] equality the
    guard leaves is injective.  Shared by the constant-sum gates in
    [body_shrincs_wots_grind_to_constant_sum] and
    [body_shrincs_wots_pubkey_from_sig]. *)
Lemma digest_sum_repr_240 : forall pk_seed nh ni m counter,
  Int.repr (shrincs.sum_list (digest_of pk_seed nh ni m counter)) = Int.repr 240 ->
  shrincs.sum_list (digest_of pk_seed nh ni m counter) = 240.
Proof.
  intros pk_seed nh ni m counter H.
  pose proof (digest_sum_bound pk_seed nh ni m counter) as Hb.
  apply repr_inj_unsigned; [ rep_lia | rep_lia | exact H ].
Qed.
