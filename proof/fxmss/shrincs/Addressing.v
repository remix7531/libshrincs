(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * SHRINCS.Addressing: native addresses for the FXMSS proof.

    This module is a compatibility facade over the library's canonical
    dependent address type.  It deliberately defines no second address
    representation: [adrs_sf] is [Model.address.adrs], and [adrs_sf_ch],
    [encode_adrs], and [decode_adrs] are the exact finite encoding from
    [Sec.addressing].

    The copied FXMSS development presents address components as [nat]s.  The
    smart constructors below therefore totalize their boundary: representable
    components are placed exactly in the corresponding [fin] fields, while an
    out-of-range component is represented by zero in the same address class.
    Every injectivity lemma states the range hypotheses under which this
    boundary is exact.  In particular, no component is truncated or reduced
    modulo its field bound. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude.
From Sec Require addressing.
From Model Require Import address fin.
From HBS.Math Require Import BinTree.
From Stdlib Require Import ZArith Lia.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Native type and exact finite encoding *)

Definition adrs_sf (chain_count w : nat) : Type :=
  address.adrs chain_count w.-1.

Definition adrs_sf_ch (chain_count w : nat) : choice_type :=
  addressing.adrs_sf_ch chain_count w.

Definition encode_adrs {chain_count w}
    (a : adrs_sf chain_count w) : adrs_sf_ch chain_count w :=
  addressing.encode_adrs chain_count w a.

Definition decode_adrs {chain_count w}
    (t : adrs_sf_ch chain_count w) : adrs_sf chain_count w :=
  addressing.decode_adrs chain_count w t.

Lemma encode_adrsK chain_count w :
  @cancel (adrs_sf_ch chain_count w) (adrs_sf chain_count w)
    encode_adrs decode_adrs.
Proof. exact: addressing.encode_adrsK. Qed.

Lemma decode_adrsK chain_count w :
  @cancel (adrs_sf chain_count w) (adrs_sf_ch chain_count w)
    decode_adrs encode_adrs.
Proof. by move=> t; apply: fto_otf. Qed.

Lemma encode_adrs_inj chain_count w :
  @injective (adrs_sf_ch chain_count w) (adrs_sf chain_count w)
    encode_adrs.
Proof. exact: addressing.encode_adrs_inj. Qed.

Arguments encode_adrs {chain_count w} _.
Arguments decode_adrs {chain_count w} _.

(* ------------------------------------------------------------------ *)
(** ** Field bounds and exact-or-zero placement *)

Definition anchor_bounded (zi : nat * nat) : Prop :=
  (Z.of_nat zi.1 < 256)%Z /\ (Z.of_nat zi.2 < 2 ^ 64)%Z.

Definition component_bounded (bound n : nat) : Prop :=
  (Z.of_nat n < Z.of_nat bound)%Z.

Lemma component_bounded_lt bound n :
  (n < bound)%nat -> component_bounded bound n.
Proof.
move=> Hn; rewrite /component_bounded.
apply Nat2Z.inj_lt.
exact/ltP.
Qed.

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

(** Coordinates admitted by an FXMSS verifier fit the native one-byte
    height and eight-byte index fields when [h_sf <= 64]. *)
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
- have hiZ : (Z.of_nat i < Z.of_nat (expn 2 (h_sf - z)))%Z.
    by apply Nat2Z.inj_lt; exact/ltP.
  rewrite of_nat_expn in hiZ.
  have he : (h_sf - z <= 64)%nat :=
    leq_trans (leq_subr z h_sf) hh.
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
exact: idx_of_path_lt.
Qed.

Definition fin_zero (bound : Z) (Hbound : (0 < bound)%Z) : fin bound :=
  fin_of_nat bound 0 Hbound.

Definition fin_of_nat_or_zero (bound : Z) (Hbound : (0 < bound)%Z)
    (n : nat) : fin bound :=
  match Z_lt_dec (Z.of_nat n) bound with
  | left Hn => fin_of_nat bound n Hn
  | right _ => fin_zero bound Hbound
  end.

Lemma fin_of_nat_or_zeroE bound Hbound n
    (Hn : (Z.of_nat n < bound)%Z) :
  fin_of_nat_or_zero bound Hbound n = fin_of_nat bound n Hn.
Proof.
rewrite /fin_of_nat_or_zero; case: Z_lt_dec => [Hn'|Hn']; last by lia.
by apply: fin_val_inj; rewrite !fin_val_of_nat.
Qed.

Lemma byte_bound_pos : (0 < 256)%Z.
Proof. lia. Qed.

Lemma index_bound_pos : (0 < 2 ^ 64)%Z.
Proof. by apply: Z.pow_pos_nonneg; lia. Qed.

Definition anchor_height (z : nat) : fin 256 :=
  fin_of_nat_or_zero 256 byte_bound_pos z.

Definition anchor_index (i : nat) : fin (2 ^ 64) :=
  fin_of_nat_or_zero (2 ^ 64) index_bound_pos i.

Lemma anchor_heightE z (Hz : (Z.of_nat z < 256)%Z) :
  anchor_height z = fin_of_nat 256 z Hz.
Proof. exact: fin_of_nat_or_zeroE. Qed.

Lemma anchor_indexE i (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  anchor_index i = fin_of_nat (2 ^ 64) i Hi.
Proof. exact: fin_of_nat_or_zeroE. Qed.

(* ------------------------------------------------------------------ *)
(** ** Stateful smart constructors *)

Definition wotsc_grind_adrs {chain_count w} (zi : nat * nat) :
    adrs_sf chain_count w :=
  address.Wc_grind (anchor_height zi.1) (anchor_index zi.2).

Definition tree_node_adrs {chain_count w} (z i : nat) :
    adrs_sf chain_count w :=
  address.Fxmss (anchor_height z) (anchor_index i).

Definition wotsc_pk_adrs {chain_count w} (zi : nat * nat) :
    adrs_sf chain_count w :=
  address.Wc_pk (anchor_height zi.1) (anchor_index zi.2).

Definition wotsc_prf_adrs {chain_count w} (zi : nat * nat) (chain : nat) :
    adrs_sf chain_count w :=
  match Z_lt_dec 0 (Z.of_nat chain_count) with
  | left Hcount =>
      address.Wc_prf (anchor_height zi.1) (anchor_index zi.2)
        (fin_of_nat_or_zero (Z.of_nat chain_count) Hcount chain)
  | right _ => wotsc_pk_adrs zi
  end.

Definition wotsc_chain_adrs {chain_count w} (zi : nat * nat)
    (chain pos : nat) : adrs_sf chain_count w :=
  match Z_lt_dec 0 (Z.of_nat chain_count),
        Z_lt_dec 0 (Z.of_nat w.-1) with
  | left Hcount, left Hpos =>
      address.Wc_hash (anchor_height zi.1) (anchor_index zi.2)
        (fin_of_nat_or_zero (Z.of_nat chain_count) Hcount chain)
        (fin_of_nat_or_zero (Z.of_nat w.-1) Hpos pos)
  | _, _ => wotsc_pk_adrs zi
  end.

Arguments wotsc_grind_adrs {chain_count w} _.
Arguments tree_node_adrs {chain_count w} _ _.
Arguments wotsc_chain_adrs {chain_count w} _ _ _.
Arguments wotsc_pk_adrs {chain_count w} _.
Arguments wotsc_prf_adrs {chain_count w} _ _.

(* Constructor-style compatibility names used by a few copied proofs. *)
Notation AdrGrind := wotsc_grind_adrs.
Notation AdrTree := tree_node_adrs.
Notation AdrChain := wotsc_chain_adrs.
Notation AdrPk := wotsc_pk_adrs.
Notation AdrPrf := wotsc_prf_adrs.

(* ------------------------------------------------------------------ *)
(** ** Native projections *)

Definition adrs_type {chain_count w} (a : adrs_sf chain_count w) : nat :=
  Z.to_nat (address.adrs_type a).

Definition adrs_height {chain_count w} (a : adrs_sf chain_count w) : nat :=
  Z.to_nat (address.adrs_anchor_tag_z a).

Definition adrs_index {chain_count w} (a : adrs_sf chain_count w) : nat :=
  Z.to_nat (address.adrs_anchor_idx_z a).

Definition adrs_chain {chain_count w} (a : adrs_sf chain_count w) : nat :=
  Z.to_nat (address.payload_b_z a).

Definition adrs_hash {chain_count w} (a : adrs_sf chain_count w) : nat :=
  Z.to_nat (address.payload_c_z a).

Definition adrs_keypair {chain_count w}
    (a : adrs_sf chain_count w) : nat * nat :=
  (adrs_height a, adrs_index a).

Definition TY_WOTS_HASH_SF : nat :=
  Z.to_nat address.SF_SHRINCS_WOTS_HASH.
Definition TY_WOTS_PK_SF : nat :=
  Z.to_nat address.SF_SHRINCS_WOTS_PK.
Definition TY_TREE_SF : nat :=
  Z.to_nat address.SF_FXMSS_TREE.
Definition TY_WOTS_PRF_SF : nat :=
  Z.to_nat address.SF_SHRINCS_WOTS_PRF.
Definition TY_WOTS_GRIND_SF : nat :=
  Z.to_nat address.SF_SHRINCS_WOTS_GRIND.

Lemma wotsc_prf_adrs_chain chain_count w zi chain :
  component_bounded chain_count chain ->
  @adrs_chain chain_count w (wotsc_prf_adrs zi chain) = chain.
Proof.
move=> Hchain.
have Hchain' := Hchain.
rewrite /component_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /adrs_chain /wotsc_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain) /=.
exact: Nat2Z.id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Exactness and injectivity on representable inputs *)

Lemma wotsc_pk_adrs_keypair chain_count w zi :
  anchor_bounded zi ->
  @adrs_keypair chain_count w (wotsc_pk_adrs zi) = zi.
Proof.
case: zi => z i [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /wotsc_pk_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma wotsc_grind_adrs_keypair chain_count w zi :
  anchor_bounded zi ->
  @adrs_keypair chain_count w (wotsc_grind_adrs zi) = zi.
Proof.
case: zi => z i [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /wotsc_grind_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma tree_node_adrs_keypair chain_count w z i :
  anchor_bounded (z, i) ->
  @adrs_keypair chain_count w (tree_node_adrs z i) = (z, i).
Proof.
move=> [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /tree_node_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma AdrGrind_inj chain_count w z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  @AdrGrind chain_count w (z, i) = AdrGrind (z', i') ->
  z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 (@adrs_keypair chain_count w) H).
rewrite (wotsc_grind_adrs_keypair chain_count w (z, i) Hz)
  (wotsc_grind_adrs_keypair chain_count w (z', i') Hz').
by case.
Qed.

Lemma AdrTree_inj chain_count w z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  @AdrTree chain_count w z i = AdrTree z' i' ->
  z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 (@adrs_keypair chain_count w) H).
rewrite (tree_node_adrs_keypair chain_count w z i Hz)
  (tree_node_adrs_keypair chain_count w z' i' Hz').
by case.
Qed.

Lemma AdrPk_inj chain_count w z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  @AdrPk chain_count w (z, i) = AdrPk (z', i') ->
  z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 (@adrs_keypair chain_count w) H).
rewrite (wotsc_pk_adrs_keypair chain_count w (z, i) Hz)
  (wotsc_pk_adrs_keypair chain_count w (z', i') Hz').
by case.
Qed.

Lemma wotsc_chain_adrsE chain_count w zi chain pos
    (Hzi : anchor_bounded zi)
    (Hchain : component_bounded chain_count chain)
    (Hpos : component_bounded w.-1 pos) :
  @wotsc_chain_adrs chain_count w zi chain pos =
    address.Wc_hash
      (fin_of_nat 256 zi.1 Hzi.1)
      (fin_of_nat (2 ^ 64) zi.2 Hzi.2)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain)
      (fin_of_nat (Z.of_nat w.-1) pos Hpos).
Proof.
have Hchain' := Hchain.
have Hpos' := Hpos.
rewrite /component_bounded in Hchain' Hpos'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
have Hpos0 : (0 < Z.of_nat w.-1)%Z.
  have := Nat2Z.is_nonneg pos; lia.
rewrite /wotsc_chain_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
case: Z_lt_dec => [Hpos0'|Hpos0']; last by lia.
rewrite (anchor_heightE _ Hzi.1) (anchor_indexE _ Hzi.2).
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain)
  (fin_of_nat_or_zeroE _ _ _ Hpos).
congr (address.Wc_hash _ _ _ _); apply: fin_val_inj;
  by rewrite !fin_val_of_nat.
Qed.

Lemma AdrChain_inj chain_count w z i c p z' i' c' p' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  component_bounded chain_count c ->
  component_bounded w.-1 p ->
  component_bounded chain_count c' ->
  component_bounded w.-1 p' ->
  @AdrChain chain_count w (z, i) c p = AdrChain (z', i') c' p' ->
  [/\ z = z', i = i', c = c' & p = p'].
Proof.
move=> Hz Hz' Hc Hp Hc' Hp' H.
rewrite (wotsc_chain_adrsE chain_count w (z, i) c p Hz Hc Hp)
  (wotsc_chain_adrsE chain_count w (z', i') c' p' Hz' Hc' Hp') in H.
injection H => Hpf Hcf Hif Hzf.
by split; apply: Nat2Z.inj.
Qed.

Lemma wotsc_prf_adrsE chain_count w zi chain
    (Hzi : anchor_bounded zi)
    (Hchain : component_bounded chain_count chain) :
  @wotsc_prf_adrs chain_count w zi chain =
    address.Wc_prf
      (fin_of_nat 256 zi.1 Hzi.1)
      (fin_of_nat (2 ^ 64) zi.2 Hzi.2)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain).
Proof.
have Hchain' := Hchain.
rewrite /component_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /wotsc_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (anchor_heightE _ Hzi.1) (anchor_indexE _ Hzi.2).
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain).
congr (address.Wc_prf _ _ _); apply: fin_val_inj;
  by rewrite !fin_val_of_nat.
Qed.

Lemma AdrPrf_inj chain_count w z i c z' i' c' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  component_bounded chain_count c ->
  component_bounded chain_count c' ->
  @AdrPrf chain_count w (z, i) c = AdrPrf (z', i') c' ->
  [/\ z = z', i = i' & c = c'].
Proof.
move=> Hz Hz' Hc Hc' H.
rewrite (wotsc_prf_adrsE chain_count w (z, i) c Hz Hc)
  (wotsc_prf_adrsE chain_count w (z', i') c' Hz' Hc') in H.
injection H => Hcf Hif Hzf.
by split; apply: Nat2Z.inj.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pairwise disjoint stateful classes *)

Lemma adrs_grind_neq_tree chain_count w zi z i :
  @wotsc_grind_adrs chain_count w zi <> tree_node_adrs z i.
Proof. by []. Qed.

Lemma adrs_grind_neq_pk chain_count w zi zi' :
  @wotsc_grind_adrs chain_count w zi <> wotsc_pk_adrs zi'.
Proof. by []. Qed.

Lemma adrs_tree_neq_pk chain_count w z i zi :
  @tree_node_adrs chain_count w z i <> wotsc_pk_adrs zi.
Proof. by []. Qed.

Arguments adrs_type {chain_count w} _.
Arguments adrs_height {chain_count w} _.
Arguments adrs_index {chain_count w} _.
Arguments adrs_chain {chain_count w} _.
Arguments adrs_hash {chain_count w} _.
Arguments adrs_keypair {chain_count w} _.
