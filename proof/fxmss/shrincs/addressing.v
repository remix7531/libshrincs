(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.addressing

    A thin re-export of [Sec.addressing] -- THE one address facade over
    [Model.address] -- under the names the copied shrincs_fxmss_scheme
    development uses.  This module defines no second address
    representation and no second smart constructor: [adrs_sf] is
    [Model.address.adrs], the encoding is [Sec.addressing]'s exact
    finite encoding, and every [shrincs_fxmss_*_adrs] name below is an
    abbreviation for the corresponding facade constructor.

    The facade presents address components as [nat]s and totalizes that
    boundary exact-or-zero: a representable component is placed exactly
    in the corresponding [fin] field, an out-of-range one is represented
    by zero in the same address class.  Every injectivity lemma states
    the range hypotheses under which the boundary is exact.  In
    particular, no component is truncated or reduced modulo its field
    bound.

    What genuinely lives here is the FXMSS-specific arithmetic: the
    coordinates an shrincs_fxmss_scheme verifier admits fit the native
    one-byte height and eight-byte index fields
    ([shrincs_fxmss_anchor_bounded], [shrincs_fxmss_path_anchor_bounded]). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude.
From Sec Require addressing.
From Model Require Import address fin.
From Sec.lib Require Import math.bin_tree.
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
(** ** Field bounds and exact-or-zero placement (facade re-exports) *)

Notation field_bounded := addressing.field_bounded.
Notation anchor_bounded := addressing.anchor_bounded.
Notation component_bounded := addressing.component_bounded.
Notation component_bounded_lt := addressing.component_bounded_lt.

Notation fin_zero := addressing.fin_zero.
Notation fin_of_nat_or_zero := addressing.fin_of_nat_or_zero.
Notation fin_of_nat_or_zeroE := addressing.fin_of_nat_or_zeroE.

Notation byte_bound_pos := addressing.byte_bound_pos.
Notation index_bound_pos := addressing.index_bound_pos.

Notation anchor_height := addressing.anchor_height.
Notation anchor_index := addressing.anchor_index.
Notation anchor_heightE := addressing.anchor_heightE.
Notation anchor_indexE := addressing.anchor_indexE.

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

(* ------------------------------------------------------------------ *)
(** ** Stateful smart constructors (facade re-exports) *)

Notation shrincs_fxmss_wots_grind_adrs := addressing.wc_grind_adrs.
Notation shrincs_fxmss_tree_node_adrs := addressing.fxmss_tree_adrs.
Notation shrincs_fxmss_wots_pk_adrs := addressing.wc_pk_adrs.
Notation shrincs_fxmss_wots_prf_adrs := addressing.wc_prf_adrs.
Notation shrincs_fxmss_wots_chain_adrs := addressing.wc_hash_adrs.

(* Constructor-style compatibility names used by a few copied proofs. *)
Notation shrincs_fxmss_adr_grind := addressing.wc_grind_adrs.
Notation shrincs_fxmss_adr_tree := addressing.fxmss_tree_adrs.
Notation shrincs_fxmss_adr_chain := addressing.wc_hash_adrs.
Notation shrincs_fxmss_adr_pk := addressing.wc_pk_adrs.
Notation shrincs_fxmss_adr_prf := addressing.wc_prf_adrs.

(* ------------------------------------------------------------------ *)
(** ** Native projections (facade re-exports) *)

Notation adrs_type := addressing.adrs_type.
Notation adrs_height := addressing.adrs_height.
Notation adrs_index := addressing.adrs_index.
Notation adrs_chain := addressing.adrs_chain.
Notation adrs_hash := addressing.adrs_hash.
Notation adrs_keypair := addressing.adrs_keypair.

Notation TY_WOTS_HASH_SF := addressing.TY_WOTS_HASH_SF.
Notation TY_WOTS_PK_SF := addressing.TY_WOTS_PK_SF.
Notation TY_TREE_SF := addressing.TY_TREE_SF.
Notation TY_WOTS_PRF_SF := addressing.TY_WOTS_PRF_SF.
Notation TY_WOTS_GRIND_SF := addressing.TY_WOTS_GRIND_SF.

(* ------------------------------------------------------------------ *)
(** ** Exactness and injectivity on representable inputs (facade
    re-exports) *)

Notation shrincs_fxmss_wots_prf_adrs_chain := addressing.wc_prf_adrs_chain.
Notation shrincs_fxmss_wots_pk_adrs_keypair := addressing.wc_pk_adrs_keypair.
Notation shrincs_fxmss_wots_grind_adrs_keypair := addressing.wc_grind_adrs_keypair.
Notation shrincs_fxmss_tree_node_adrs_keypair := addressing.fxmss_tree_adrs_keypair.
Notation shrincs_fxmss_wots_grind_adrs_inj := addressing.wc_grind_adrs_inj.
Notation shrincs_fxmss_tree_node_adrs_inj := addressing.fxmss_tree_adrs_inj.
Notation shrincs_fxmss_wots_pk_adrs_inj := addressing.wc_pk_adrs_inj.
Notation shrincs_fxmss_wots_chain_adrsE := addressing.wc_hash_adrsE.
Notation shrincs_fxmss_wots_chain_adrs_inj := addressing.wc_hash_adrs_inj.
Notation shrincs_fxmss_wots_prf_adrsE := addressing.wc_prf_adrsE.
Notation shrincs_fxmss_wots_prf_adrs_inj := addressing.wc_prf_adrs_inj.

(* ------------------------------------------------------------------ *)
(** ** Pairwise disjoint stateful classes (facade re-exports) *)

Notation shrincs_fxmss_adrs_grind_neq_tree := addressing.wc_grind_adrs_neq_fxmss_tree.
Notation shrincs_fxmss_adrs_grind_neq_pk := addressing.wc_grind_adrs_neq_wc_pk.
Notation shrincs_fxmss_adrs_tree_neq_pk := addressing.fxmss_tree_adrs_neq_wc_pk.
