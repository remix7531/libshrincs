(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.addressing

    This module is a compatibility facade over the library's canonical
    dependent address type.  It deliberately defines no second address
    representation: [adrs_sf] is [Model.address.adrs], and [adrs_sf_ch],
    [encode_adrs], and [decode_adrs] are the exact finite encoding from
    [Sec.addressing].

    The copied shrincs_fxmss_scheme development presents address components as [nat]s.  The
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
From HBS.math Require Import bin_tree.
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

(** Decidable form of [anchor_bounded]'s index half, for use inside the
    scheme's boolean well-formedness and verifier predicates. *)
Definition index_bounded (i : nat) : bool := (Z.of_nat i <? 2 ^ 64)%Z.

Lemma index_boundedP i : index_bounded i -> (Z.of_nat i < 2 ^ 64)%Z.
Proof. by move/Z.ltb_lt. Qed.

Lemma index_boundedI i : (Z.of_nat i < 2 ^ 64)%Z -> index_bounded i.
Proof. by move/Z.ltb_lt. Qed.

(** Downward closure, stated on [nat] so callers never have to bring
    [2 ^ 64] into a MathComp goal (where it would be a unary numeral). *)
Lemma index_bounded_leq (i j : nat) :
  (i <= j)%nat -> index_bounded j -> index_bounded i.
Proof.
move=> hij /Z.ltb_lt hj; apply/Z.ltb_lt.
have : (Z.of_nat i <= Z.of_nat j)%Z by apply/Nat2Z.inj_le/leP.
lia.
Qed.

Lemma component_bounded_lt bound n :
  (n < bound)%nat -> component_bounded bound n.
Proof.
move=> Hn; rewrite /component_bounded.
apply Nat2Z.inj_lt.
exact/ltP.
Qed.

(** Coordinates admitted by an shrincs_fxmss_scheme verifier fit the native one-byte
    height and eight-byte index fields.  The height is bounded by the
    declared tree height, itself a byte (shrincs.py: [FXMSS_HEIGHT =
    255]); the index is bounded directly, which is what the spec's
    verifier check [leaf_index < 2 ** min(64, leaf_depth)]
    (shrincs.py, [fxmss_pubkey_from_sig]) supplies.  Note the index
    bound is NOT implied by the height bound: at [h_sf = 255] a
    position 200 levels below the root has an index far beyond the
    eight-byte field. *)
Lemma shrincs_fxmss_anchor_bounded (h_sf z i : nat) :
  (h_sf <= 255)%nat ->
  (z <= h_sf)%nat ->
  (Z.of_nat i < 2 ^ 64)%Z ->
  anchor_bounded (z, i).
Proof.
move=> hh hz hi; split; last exact: hi.
change (Z.of_nat z < Z.of_nat 256)%Z.
apply Nat2Z.inj_lt.
apply/ltP.
exact: leq_ltn_trans (leq_trans hz hh) (isT : (255 < 256)%nat).
Qed.

Lemma shrincs_fxmss_path_anchor_bounded (h_sf : nat) (p : seq bool) :
  (h_sf <= 255)%nat ->
  (size p <= h_sf)%nat ->
  (Z.of_nat (idx_of_path p) < 2 ^ 64)%Z ->
  anchor_bounded ((h_sf - size p)%nat, idx_of_path p).
Proof.
move=> hh hp.
exact: (shrincs_fxmss_anchor_bounded h_sf _ _ hh (leq_subr (size p) h_sf)).
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

Definition shrincs_fxmss_wots_grind_adrs {chain_count w} (zi : nat * nat) :
    adrs_sf chain_count w :=
  address.Wc_grind (anchor_height zi.1) (anchor_index zi.2).

Definition shrincs_fxmss_tree_node_adrs {chain_count w} (z i : nat) :
    adrs_sf chain_count w :=
  address.Fxmss (anchor_height z) (anchor_index i).

Definition shrincs_fxmss_wots_pk_adrs {chain_count w} (zi : nat * nat) :
    adrs_sf chain_count w :=
  address.Wc_pk (anchor_height zi.1) (anchor_index zi.2).

Definition shrincs_fxmss_wots_prf_adrs {chain_count w} (zi : nat * nat) (chain : nat) :
    adrs_sf chain_count w :=
  match Z_lt_dec 0 (Z.of_nat chain_count) with
  | left Hcount =>
      address.Wc_prf (anchor_height zi.1) (anchor_index zi.2)
        (fin_of_nat_or_zero (Z.of_nat chain_count) Hcount chain)
  | right _ => shrincs_fxmss_wots_pk_adrs zi
  end.

Definition shrincs_fxmss_wots_chain_adrs {chain_count w} (zi : nat * nat)
    (chain pos : nat) : adrs_sf chain_count w :=
  match Z_lt_dec 0 (Z.of_nat chain_count),
        Z_lt_dec 0 (Z.of_nat w.-1) with
  | left Hcount, left Hpos =>
      address.Wc_hash (anchor_height zi.1) (anchor_index zi.2)
        (fin_of_nat_or_zero (Z.of_nat chain_count) Hcount chain)
        (fin_of_nat_or_zero (Z.of_nat w.-1) Hpos pos)
  | _, _ => shrincs_fxmss_wots_pk_adrs zi
  end.

Arguments shrincs_fxmss_wots_grind_adrs {chain_count w} _.
Arguments shrincs_fxmss_tree_node_adrs {chain_count w} _ _.
Arguments shrincs_fxmss_wots_chain_adrs {chain_count w} _ _ _.
Arguments shrincs_fxmss_wots_pk_adrs {chain_count w} _.
Arguments shrincs_fxmss_wots_prf_adrs {chain_count w} _ _.

(* Constructor-style compatibility names used by a few copied proofs. *)
Notation shrincs_fxmss_adr_grind := shrincs_fxmss_wots_grind_adrs.
Notation shrincs_fxmss_adr_tree := shrincs_fxmss_tree_node_adrs.
Notation shrincs_fxmss_adr_chain := shrincs_fxmss_wots_chain_adrs.
Notation shrincs_fxmss_adr_pk := shrincs_fxmss_wots_pk_adrs.
Notation shrincs_fxmss_adr_prf := shrincs_fxmss_wots_prf_adrs.

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

Lemma shrincs_fxmss_wots_prf_adrs_chain chain_count w zi chain :
  component_bounded chain_count chain ->
  @adrs_chain chain_count w (shrincs_fxmss_wots_prf_adrs zi chain) = chain.
Proof.
move=> Hchain.
have Hchain' := Hchain.
rewrite /component_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /adrs_chain /shrincs_fxmss_wots_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain) /=.
exact: Nat2Z.id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Exactness and injectivity on representable inputs *)

Lemma shrincs_fxmss_wots_pk_adrs_keypair chain_count w zi :
  anchor_bounded zi ->
  @adrs_keypair chain_count w (shrincs_fxmss_wots_pk_adrs zi) = zi.
Proof.
case: zi => z i [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /shrincs_fxmss_wots_pk_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma shrincs_fxmss_wots_grind_adrs_keypair chain_count w zi :
  anchor_bounded zi ->
  @adrs_keypair chain_count w (shrincs_fxmss_wots_grind_adrs zi) = zi.
Proof.
case: zi => z i [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /shrincs_fxmss_wots_grind_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma shrincs_fxmss_tree_node_adrs_keypair chain_count w z i :
  anchor_bounded (z, i) ->
  @adrs_keypair chain_count w (shrincs_fxmss_tree_node_adrs z i) = (z, i).
Proof.
move=> [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /shrincs_fxmss_tree_node_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma shrincs_fxmss_wots_grind_adrs_inj chain_count w z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  @shrincs_fxmss_adr_grind chain_count w (z, i) = shrincs_fxmss_adr_grind (z', i') ->
  z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 (@adrs_keypair chain_count w) H).
rewrite (shrincs_fxmss_wots_grind_adrs_keypair chain_count w (z, i) Hz)
  (shrincs_fxmss_wots_grind_adrs_keypair chain_count w (z', i') Hz').
by case.
Qed.

Lemma shrincs_fxmss_tree_node_adrs_inj chain_count w z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  @shrincs_fxmss_adr_tree chain_count w z i = shrincs_fxmss_adr_tree z' i' ->
  z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 (@adrs_keypair chain_count w) H).
rewrite (shrincs_fxmss_tree_node_adrs_keypair chain_count w z i Hz)
  (shrincs_fxmss_tree_node_adrs_keypair chain_count w z' i' Hz').
by case.
Qed.

Lemma shrincs_fxmss_wots_pk_adrs_inj chain_count w z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  @shrincs_fxmss_adr_pk chain_count w (z, i) = shrincs_fxmss_adr_pk (z', i') ->
  z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 (@adrs_keypair chain_count w) H).
rewrite (shrincs_fxmss_wots_pk_adrs_keypair chain_count w (z, i) Hz)
  (shrincs_fxmss_wots_pk_adrs_keypair chain_count w (z', i') Hz').
by case.
Qed.

Lemma shrincs_fxmss_wots_chain_adrsE chain_count w zi chain pos
    (Hzi : anchor_bounded zi)
    (Hchain : component_bounded chain_count chain)
    (Hpos : component_bounded w.-1 pos) :
  @shrincs_fxmss_wots_chain_adrs chain_count w zi chain pos =
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
rewrite /shrincs_fxmss_wots_chain_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
case: Z_lt_dec => [Hpos0'|Hpos0']; last by lia.
rewrite (anchor_heightE _ Hzi.1) (anchor_indexE _ Hzi.2).
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain)
  (fin_of_nat_or_zeroE _ _ _ Hpos).
congr (address.Wc_hash _ _ _ _); apply: fin_val_inj;
  by rewrite !fin_val_of_nat.
Qed.

Lemma shrincs_fxmss_wots_chain_adrs_inj chain_count w z i c p z' i' c' p' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  component_bounded chain_count c ->
  component_bounded w.-1 p ->
  component_bounded chain_count c' ->
  component_bounded w.-1 p' ->
  @shrincs_fxmss_adr_chain chain_count w (z, i) c p = shrincs_fxmss_adr_chain (z', i') c' p' ->
  [/\ z = z', i = i', c = c' & p = p'].
Proof.
move=> Hz Hz' Hc Hp Hc' Hp' H.
rewrite (shrincs_fxmss_wots_chain_adrsE chain_count w (z, i) c p Hz Hc Hp)
  (shrincs_fxmss_wots_chain_adrsE chain_count w (z', i') c' p' Hz' Hc' Hp') in H.
injection H => Hpf Hcf Hif Hzf.
by split; apply: Nat2Z.inj.
Qed.

Lemma shrincs_fxmss_wots_prf_adrsE chain_count w zi chain
    (Hzi : anchor_bounded zi)
    (Hchain : component_bounded chain_count chain) :
  @shrincs_fxmss_wots_prf_adrs chain_count w zi chain =
    address.Wc_prf
      (fin_of_nat 256 zi.1 Hzi.1)
      (fin_of_nat (2 ^ 64) zi.2 Hzi.2)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain).
Proof.
have Hchain' := Hchain.
rewrite /component_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /shrincs_fxmss_wots_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (anchor_heightE _ Hzi.1) (anchor_indexE _ Hzi.2).
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain).
congr (address.Wc_prf _ _ _); apply: fin_val_inj;
  by rewrite !fin_val_of_nat.
Qed.

Lemma shrincs_fxmss_wots_prf_adrs_inj chain_count w z i c z' i' c' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  component_bounded chain_count c ->
  component_bounded chain_count c' ->
  @shrincs_fxmss_adr_prf chain_count w (z, i) c = shrincs_fxmss_adr_prf (z', i') c' ->
  [/\ z = z', i = i' & c = c'].
Proof.
move=> Hz Hz' Hc Hc' H.
rewrite (shrincs_fxmss_wots_prf_adrsE chain_count w (z, i) c Hz Hc)
  (shrincs_fxmss_wots_prf_adrsE chain_count w (z', i') c' Hz' Hc') in H.
injection H => Hcf Hif Hzf.
by split; apply: Nat2Z.inj.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pairwise disjoint stateful classes *)

Lemma shrincs_fxmss_adrs_grind_neq_tree chain_count w zi z i :
  @shrincs_fxmss_wots_grind_adrs chain_count w zi <> shrincs_fxmss_tree_node_adrs z i.
Proof. by []. Qed.

Lemma shrincs_fxmss_adrs_grind_neq_pk chain_count w zi zi' :
  @shrincs_fxmss_wots_grind_adrs chain_count w zi <> shrincs_fxmss_wots_pk_adrs zi'.
Proof. by []. Qed.

Lemma shrincs_fxmss_adrs_tree_neq_pk chain_count w z i zi :
  @shrincs_fxmss_tree_node_adrs chain_count w z i <> shrincs_fxmss_wots_pk_adrs zi.
Proof. by []. Qed.

Arguments adrs_type {chain_count w} _.
Arguments adrs_height {chain_count w} _.
Arguments adrs_index {chain_count w} _.
Arguments adrs_chain {chain_count w} _.
Arguments adrs_hash {chain_count w} _.
Arguments adrs_keypair {chain_count w} _.
