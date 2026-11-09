(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.theory.address: facts about [model.address]'s definitions.

    Kept separate from [model.address] itself: that file is "the
    shape of an ADRS," this one is "facts about it." *)

From Shrincs.internal.common Require Export address.
From Stdlib Require Import ZArith Lia List.
Import ListNotations.
#[local] Open Scope Z_scope.

(** These facts hold for ANY instantiation of [address.adrs]'s two
    bounds, so we keep them generic: a section over [cc]/[pb] with a
    [Local Abbreviation] rebinding the bare [adrs] to [address.adrs cc pb].
    (None of them needs the positivity hypotheses -- they don't build a
    zero default.) *)
Section AddrFacts.
Variables cc pb : nat.
Local Abbreviation adrs := (address.adrs cc pb).

(** [shrincs_wots_grind_adrs] rebuilds the grind address from the
    anchor, so applying it twice is the same as once (the second
    application reads back the same anchor it just wrote). *)
Lemma shrincs_wots_grind_adrs_idem : forall a : adrs,
  shrincs_wots_grind_adrs (shrincs_wots_grind_adrs a) = shrincs_wots_grind_adrs a.
Proof.
  intros a. unfold shrincs_wots_grind_adrs, adrs_nh, adrs_ni. reflexivity.
Qed.

(** Two addresses with different [adrs_type] values are never equal
    -- a single generic fact, applied at whichever pair of type
    constants a consumer needs (e.g. [SF_SHRINCS_WOTS_HASH <>
    SF_SHRINCS_WOTS_PK] is immediate by [discriminate]/[lia] on the
    literal numerals). *)
Lemma adrs_type_neq_neq : forall a1 a2 : adrs,
  adrs_type a1 <> adrs_type a2 -> a1 <> a2.
Proof.
  intros a1 a2 Hneq Heq. congruence.
Qed.

(** The WOTS+C fin-anchor projections are FAITHFUL: their [fin_val] is
    exactly the flat [Z] anchor projection, on every arm (the stateless
    layer/tree share the anchor's ordinal via [ly_nh] / the [fin (2^64)]
    type).  The C-refinement's [adrs_to_raw] fold lemmas rewrite the
    smart-constructor anchor ([adrs_nh]/[adrs_ni]) back to the wire
    projection with these. *)
Lemma adrs_nh_tag_z : forall a : adrs, fin_val (adrs_nh a) = adrs_anchor_tag_z a.
Proof. intros a; destruct a; reflexivity. Qed.

Lemma adrs_ni_idx_z : forall a : adrs, fin_val (adrs_ni a) = adrs_anchor_idx_z a.
Proof. intros a; destruct a; reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** ** [adrs_bytes] is injective: distinct ADRS values serialize to
    distinct 22-byte strings.

    This is the domain-separation fact the hypertree layers (XMSS /
    FORS) will need -- "distinct node => distinct ADRS bytes" -- exactly
    as the WOTS+C leaf needed [addressing.chain_tweak_inj].  The type
    byte ([adrs_type], at wire offset 9) is distinct across all twelve
    constructors, so it recovers the arm; the five remaining [Z]
    projections then recover each [fin] field via [fin_val] injectivity.

    The WOTS+C chain / position words occupy 4 wire bytes each, so
    recovering them needs their bounds to fit: [cc], [pb <= 2 ^ 32]
    (both hold at the spec numbers 32 / 15).  Every stateless field
    bound is a literal below [2 ^ 32], so those arms need no side
    condition.  The [to_byte] / byte serialization facts here are the
    model-side counterparts of [Vst.theory.pure]'s (the model may not
    import the VST tree). *)

(** [to_byte x y] is a [y]-byte string. *)
Lemma to_byte_len : forall y x, length (to_byte x y) = y.
Proof.
  induction y as [|y' IH]; intros x; simpl; [reflexivity|].
  rewrite length_app, IH; simpl; lia.
Qed.

(** The low byte of a [to_byte] step: [byte_mod256] agrees mod 256. *)
Lemma byte_mod256_mod : forall x y, byte_mod256 x = byte_mod256 y -> Z.modulo x 256 = Z.modulo y 256.
Proof.
  intros x y H. apply (f_equal byte_val) in H.
  unfold byte_val, byte_mod256 in H.
  rewrite !machine.Byte.unsigned_repr_eq, byte_modulus in H. exact H.
Qed.

(** [to_byte _ n] is injective on values that fit in [n] bytes. *)
Lemma to_byte_inj : forall n x y,
  0 <= x < 2 ^ (8 * Z.of_nat n) ->
  0 <= y < 2 ^ (8 * Z.of_nat n) ->
  to_byte x n = to_byte y n -> x = y.
Proof.
  induction n as [|n' IH]; intros x y Hx Hy H.
  - simpl in Hx, Hy. lia.
  - simpl in H. apply app_inj_tail in H. destruct H as [Hpre Hlast].
    apply byte_mod256_mod in Hlast.
    assert (Hpow : 2 ^ (8 * Z.of_nat (S n')) = 256 * 2 ^ (8 * Z.of_nat n')).
    { rewrite Nat2Z.inj_succ.
      replace (8 * Z.succ (Z.of_nat n')) with (8 + 8 * Z.of_nat n') by lia.
      rewrite Z.pow_add_r by lia. replace (2 ^ 8) with 256 by reflexivity. reflexivity. }
    rewrite Hpow in Hx, Hy.
    assert (Hpos : 0 < 2 ^ (8 * Z.of_nat n')) by (apply Z.pow_pos_nonneg; lia).
    assert (Hxd : 0 <= x / 256 < 2 ^ (8 * Z.of_nat n')).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (Hyd : 0 <= y / 256 < 2 ^ (8 * Z.of_nat n')).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    specialize (IH _ _ Hxd Hyd Hpre).
    pose proof (Z.div_mod x 256 ltac:(lia)) as Dx.
    pose proof (Z.div_mod y 256 ltac:(lia)) as Dy.
    lia.
Qed.

Lemma to_byte_inj_1 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> to_byte x 1 = to_byte y 1 -> x = y.
Proof. intros x y Hx Hy H. apply (to_byte_inj 1 x y); [ change (2 ^ (8 * Z.of_nat 1)) with 256; lia | change (2 ^ (8 * Z.of_nat 1)) with 256; lia | exact H ]. Qed.

Lemma to_byte_inj_8 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> to_byte x 8 = to_byte y 8 -> x = y.
Proof. intros x y Hx Hy H. apply (to_byte_inj 8 x y); [ change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia | change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia | exact H ]. Qed.

Lemma to_byte_inj_4 : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> to_byte x 4 = to_byte y 4 -> x = y.
Proof. intros x y Hx Hy H. apply (to_byte_inj 4 x y); [ change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia | change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia | exact H ]. Qed.

(** A concatenation splits at a matching length boundary. *)
Lemma app_split_len : forall (l1 l2 r1 r2 : list byte),
  length l1 = length l2 -> l1 ++ r1 = l2 ++ r2 -> l1 = l2 /\ r1 = r2.
Proof.
  induction l1 as [|x l1' IH]; intros l2 r1 r2 Hlen Happ.
  - destruct l2; simpl in *; [split; [reflexivity | exact Happ] | discriminate].
  - destruct l2 as [|y l2']; simpl in *; [discriminate|].
    injection Happ as Hxy Happ'. injection Hlen as Hlen'.
    specialize (IH l2' r1 r2 Hlen' Happ'). destruct IH as [Hl Hr].
    split; [rewrite Hxy, Hl; reflexivity | exact Hr].
Qed.

(** The six wire [Z] projections are each in their byte-width's range. *)
Lemma tag_z_range : forall a : adrs, 0 <= adrs_anchor_tag_z a < 256.
Proof.
  intros a; destruct a; simpl;
    match goal with |- context[fin_val ?f] => pose proof (fin_range f) end;
    try (unfold hypertree_layers in * ); lia.
Qed.

Lemma idx_z_range : forall a : adrs, 0 <= adrs_anchor_idx_z a < 2 ^ 64.
Proof. intros a; destruct a; simpl; apply fin_range. Qed.

Lemma pa_range : forall a : adrs, 0 <= payload_a_z a < 2 ^ 32.
Proof.
  intros a; destruct a; simpl;
    try (match goal with |- context[fin_val ?f] => pose proof (fin_range f) end);
    change (2 ^ 32) with 4294967296; try (unfold sub_leaves in * ); lia.
Qed.

Lemma pb_range : forall a : adrs, Z.of_nat cc <= 2 ^ 32 -> 0 <= payload_b_z a < 2 ^ 32.
Proof.
  intros a Hcc; destruct a; simpl;
    try (match goal with |- context[fin_val ?f] => pose proof (fin_range f) end);
    change (2 ^ 32) with 4294967296 in *;
    try (unfold len_tw in * ); try (unfold h_xmss in * ); try (unfold h_fors in * ); lia.
Qed.

Lemma pc_range : forall a : adrs, Z.of_nat pb <= 2 ^ 32 -> 0 <= payload_c_z a < 2 ^ 32.
Proof.
  intros a Hpbb; destruct a; simpl;
    try (match goal with |- context[fin_val ?f] => pose proof (fin_range f) end);
    change (2 ^ 32) with 4294967296 in *;
    try (unfold w_tw_pred in * ); try (unfold sub_leaves in * ); try (unfold fors_idx in * ); lia.
Qed.

(** The six wire projections determine the address: the type byte fixes
    the constructor, the rest recover each field. *)
Lemma adrs_proj_inj : forall a b : adrs,
  adrs_anchor_tag_z a = adrs_anchor_tag_z b ->
  adrs_anchor_idx_z a = adrs_anchor_idx_z b ->
  adrs_type a = adrs_type b ->
  payload_a_z a = payload_a_z b ->
  payload_b_z a = payload_b_z b ->
  payload_c_z a = payload_c_z b ->
  a = b.
Proof.
  intros a b Htag Hidx Hnt Hpa Hpb Hpc.
  destruct a; destruct b; simpl in *;
    try (exfalso; apply (f_equal byte_val) in Hnt; vm_compute in Hnt; discriminate);
    f_equal; apply fin_val_inj; assumption.
Qed.

(** Headline: [adrs_bytes] is injective (chain / position words fitting
    in 4 bytes, i.e. [cc], [pb <= 2 ^ 32]). *)
Lemma adrs_bytes_inj : forall a b : adrs,
  Z.of_nat cc <= 2 ^ 32 -> Z.of_nat pb <= 2 ^ 32 ->
  adrs_bytes a = adrs_bytes b -> a = b.
Proof.
  intros a b Hcc Hpbb H. unfold adrs_bytes in H.
  apply app_split_len in H; [| rewrite !to_byte_len; reflexivity]. destruct H as [E1 H].
  apply app_split_len in H; [| rewrite !to_byte_len; reflexivity]. destruct H as [E2 H].
  apply app_split_len in H; [| rewrite !to_byte_len; reflexivity]. destruct H as [E3 H].
  apply app_split_len in H; [| rewrite !to_byte_len; reflexivity]. destruct H as [E4 H].
  apply app_split_len in H; [| rewrite !to_byte_len; reflexivity]. destruct H as [E5 E6].
  apply to_byte_inj_1 in E1; [| apply tag_z_range | apply tag_z_range].
  apply to_byte_inj_8 in E2; [| apply idx_z_range | apply idx_z_range].
  apply to_byte_inj_1 in E3; [| apply byte_val_range | apply byte_val_range].
  apply byte_eq in E3.
  apply to_byte_inj_4 in E4; [| apply pa_range | apply pa_range].
  apply to_byte_inj_4 in E5; [| apply pb_range; exact Hcc | apply pb_range; exact Hcc].
  apply to_byte_inj_4 in E6; [| apply pc_range; exact Hpbb | apply pc_range; exact Hpbb].
  apply adrs_proj_inj; assumption.
Qed.

End AddrFacts.
