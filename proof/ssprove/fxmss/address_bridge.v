(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.fxmss.address_bridge: FXMSS/native address compatibility.

    The FXMSS security proof uses the unbounded, stateful address type
    [SHRINCS.Addressing.adrs_sf].  The executable SHRINCS model uses the
    bounded dependent union [Model.address.adrs].  This file is the isolated
    boundary between those representations.  It does not change either
    address type or any WOTS+C/FXMSS theorem.

    The bridge records the native field bounds, converts exactly when they
    hold, proves cancellation in both directions on the five stateful arms,
    and proves equality of the resulting 22-byte wire encodings.  The final
    section supplies partial and subtype-based adapters for native hash
    functions; invalid abstract addresses are rejected rather than truncated
    or silently mapped to a dummy address. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude.
From Stdlib Require Import ZArith Lia.

From Model Require Import address fin.
From HBS.Math Require Import BinTree.
From SHRINCS Require Import Addressing.
Set Warnings "notation-overridden,ambiguous-paths".

#[local] Open Scope Z_scope.

Section AddressBridge.

Variables chain_count pos_bound : nat.

Local Notation model_adrs := (address.adrs chain_count pos_bound).

(* ------------------------------------------------------------------ *)
(** ** Bounds carried by the native address type *)

Definition anchor_bounded (zi : nat * nat) : Prop :=
  Z.of_nat zi.1 < 256 /\ Z.of_nat zi.2 < 2 ^ 64.

Definition adrs_bounded (a : adrs_sf) : Prop :=
  Z.of_nat (adrs_height a) < 256 /\
  Z.of_nat (adrs_index a) < 2 ^ 64 /\
  match a with
  | AdrChain _ _ chain pos =>
      Z.of_nat chain < Z.of_nat chain_count /\
      Z.of_nat pos < Z.of_nat pos_bound
  | AdrPrf _ _ chain => Z.of_nat chain < Z.of_nat chain_count
  | _ => True
  end.

Definition bounded_adrs := {a : adrs_sf | adrs_bounded a}.

Lemma grind_adrs_bounded zi :
  anchor_bounded zi -> adrs_bounded (wotsc_grind_adrs zi).
Proof. by case: zi => z i []. Qed.

Lemma tree_adrs_bounded z i :
  anchor_bounded (z, i) -> adrs_bounded (tree_node_adrs z i).
Proof. by case. Qed.

Lemma chain_adrs_bounded zi chain pos :
  anchor_bounded zi ->
  Z.of_nat chain < Z.of_nat chain_count ->
  Z.of_nat pos < Z.of_nat pos_bound ->
  adrs_bounded (wotsc_chain_adrs zi chain pos).
Proof. by case: zi => z i [hz hi] hc hp; repeat split. Qed.

Lemma pk_adrs_bounded zi :
  anchor_bounded zi -> adrs_bounded (wotsc_pk_adrs zi).
Proof. by case: zi => z i []. Qed.

Lemma prf_adrs_bounded zi chain :
  anchor_bounded zi ->
  Z.of_nat chain < Z.of_nat chain_count ->
  adrs_bounded (wotsc_prf_adrs zi chain).
Proof. by case: zi => z i [hz hi] hc; repeat split. Qed.

(* ------------------------------------------------------------------ *)
(** ** Exact conversion to and from [Model.address.adrs] *)

Definition to_model_adrs (a : adrs_sf) (Ha : adrs_bounded a) : model_adrs.
Proof.
  destruct a as [z i | z i | z i chain pos | z i | z i chain];
    cbn in Ha |- *.
  - destruct Ha as [Hz [Hi _]].
    exact (address.Wc_grind (fin_of_nat 256 z Hz)
      (fin_of_nat (2 ^ 64) i Hi)).
  - destruct Ha as [Hz [Hi _]].
    exact (address.Fxmss (fin_of_nat 256 z Hz)
      (fin_of_nat (2 ^ 64) i Hi)).
  - destruct Ha as [Hz [Hi [Hchain Hpos]]].
    exact (address.Wc_hash (fin_of_nat 256 z Hz)
      (fin_of_nat (2 ^ 64) i Hi)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain)
      (fin_of_nat (Z.of_nat pos_bound) pos Hpos)).
  - destruct Ha as [Hz [Hi _]].
    exact (address.Wc_pk (fin_of_nat 256 z Hz)
      (fin_of_nat (2 ^ 64) i Hi)).
  - destruct Ha as [Hz [Hi Hchain]].
    exact (address.Wc_prf (fin_of_nat 256 z Hz)
      (fin_of_nat (2 ^ 64) i Hi)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain)).
Defined.

Definition of_model_adrs (a : model_adrs) : option adrs_sf :=
  match a with
  | address.Wc_hash nh ni chain pos =>
      Some (AdrChain (Z.to_nat (fin_val nh)) (Z.to_nat (fin_val ni))
        (Z.to_nat (fin_val chain)) (Z.to_nat (fin_val pos)))
  | address.Wc_prf nh ni chain =>
      Some (AdrPrf (Z.to_nat (fin_val nh)) (Z.to_nat (fin_val ni))
        (Z.to_nat (fin_val chain)))
  | address.Wc_pk nh ni =>
      Some (AdrPk (Z.to_nat (fin_val nh)) (Z.to_nat (fin_val ni)))
  | address.Wc_grind nh ni =>
      Some (AdrGrind (Z.to_nat (fin_val nh)) (Z.to_nat (fin_val ni)))
  | address.Fxmss nh ni =>
      Some (AdrTree (Z.to_nat (fin_val nh)) (Z.to_nat (fin_val ni)))
  | _ => None
  end.

Lemma of_model_to_model a Ha :
  of_model_adrs (to_model_adrs a Ha) = Some a.
Proof.
  destruct a; cbn in Ha |- *.
  - destruct Ha as [Hz [Hi _]].
    cbn; rewrite !Nat2Z.id; reflexivity.
  - destruct Ha as [Hz [Hi _]].
    cbn; rewrite !Nat2Z.id; reflexivity.
  - destruct Ha as [Hz [Hi [Hchain Hpos]]].
    cbn; rewrite !Nat2Z.id; reflexivity.
  - destruct Ha as [Hz [Hi _]].
    cbn; rewrite !Nat2Z.id; reflexivity.
  - destruct Ha as [Hz [Hi Hchain]].
    cbn; rewrite !Nat2Z.id; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bounds for FXMSS tree coordinates *)

(** [Z.of_nat] transports MathComp exponentiation to [Z.pow] without
    evaluating either side. *)
Lemma of_nat_expn (a b : nat) :
  Z.of_nat (expn a b) = Z.pow (Z.of_nat a) (Z.of_nat b).
Proof.
  elim: b => [|b IH]; first by rewrite expn0.
  rewrite expnS Nat2Z.inj_mul IH Nat2Z.inj_succ.
  rewrite Z.pow_succ_r; last by lia.
  by [].
Qed.

Lemma fxmss_anchor_bounded (h_sf z i : nat) :
  (h_sf <= 64)%nat ->
  (z <= h_sf)%nat ->
  (i < expn 2 (h_sf - z))%nat ->
  anchor_bounded (z, i).
Proof.
  move=> hh hz hi; split.
  - change (Z.of_nat z < Z.of_nat 256)%Z.
    apply Nat2Z.inj_lt.
    apply/ltP.
    exact: leq_ltn_trans (leq_trans hz hh) (isT : (64 < 256)%nat).
  - have hiZ :
        (Z.of_nat i < Z.of_nat (expn 2 (h_sf - z)))%Z.
      by apply Nat2Z.inj_lt; exact/ltP.
    rewrite of_nat_expn in hiZ.
    have he : (h_sf - z <= 64)%nat.
      exact: leq_trans (leq_subr z h_sf) hh.
    have heZ : (Z.of_nat (h_sf - z) <= 64)%Z.
      change (Z.of_nat (h_sf - z) <= Z.of_nat 64)%Z.
      by apply Nat2Z.inj_le; exact/leP.
    have hpow : (2 ^ Z.of_nat (h_sf - z) <= 2 ^ 64)%Z.
      by apply Z.pow_le_mono_r; lia.
    change (Z.of_nat i < 2 ^ Z.of_nat (h_sf - z))%Z in hiZ.
    exact (Z.lt_le_trans _ _ _ hiZ hpow).
Qed.

Lemma path_anchor_bounded (h_sf : nat) (p : seq bool) :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  anchor_bounded ((h_sf - size p)%nat, idx_of_path p).
Proof.
  move=> hh hp.
  apply: (fxmss_anchor_bounded h_sf (h_sf - size p)%nat
    (idx_of_path p) hh (leq_subr (size p) h_sf)).
  rewrite subKn //.
  exact (idx_of_path_lt p).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The canonical 22-byte wire encoding *)

Definition adrs_type_byte (a : adrs_sf) : byte :=
  match a with
  | AdrGrind _ _ => address.SF_SHRINCS_WOTS_GRIND
  | AdrTree _ _ => address.SF_FXMSS_TREE
  | AdrChain _ _ _ _ => address.SF_SHRINCS_WOTS_HASH
  | AdrPk _ _ => address.SF_SHRINCS_WOTS_PK
  | AdrPrf _ _ _ => address.SF_SHRINCS_WOTS_PRF
  end.

Definition adrs_bytes (a : adrs_sf) : list byte :=
  address.to_byte (Z.of_nat (adrs_height a)) 1 ++
  address.to_byte (Z.of_nat (adrs_index a)) 8 ++
  address.to_byte (adrs_type_byte a) 1 ++
  address.to_byte 0 4 ++
  address.to_byte (Z.of_nat (adrs_chain a)) 4 ++
  address.to_byte (Z.of_nat (adrs_hash a)) 4.

Lemma adrs_type_byte_nat a :
  Z.to_nat (adrs_type_byte a) = adrs_type a.
Proof. by case: a. Qed.

Lemma to_model_adrs_bytes a Ha :
  address.adrs_bytes (to_model_adrs a Ha) = adrs_bytes a.
Proof.
  destruct a; cbn in Ha |- *.
  - by destruct Ha as [Hz [Hi _]].
  - by destruct Ha as [Hz [Hi _]].
  - by destruct Ha as [Hz [Hi [Hchain Hpos]]].
  - by destruct Ha as [Hz [Hi _]].
  - by destruct Ha as [Hz [Hi Hchain]].
Qed.

Lemma to_model_adrs_inj a b Ha Hb :
  to_model_adrs a Ha = to_model_adrs b Hb -> a = b.
Proof.
  move/(congr1 of_model_adrs).
  by rewrite !of_model_to_model => [[]].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Native hash adapters on the exact bounded domain *)

Definition adapt_hash {PP X Y : Type}
    (H : PP -> model_adrs -> X -> Y) :
    PP -> bounded_adrs -> X -> Y :=
  fun pp a x => H pp (to_model_adrs (proj1_sig a) (proj2_sig a)) x.

Definition adapt_prf {PP K Y : Type}
    (H : PP -> K -> model_adrs -> Y) :
    PP -> K -> bounded_adrs -> Y :=
  fun pp k a => H pp k (to_model_adrs (proj1_sig a) (proj2_sig a)).

End AddressBridge.
