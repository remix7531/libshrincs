(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.fxmss.scheme_bridge: native bounds for FXMSS addresses.

    This file specializes [Sec.fxmss.address_bridge]'s field bounds to
    coordinates that the abstract FXMSS scheme actually constructs or accepts.
    A declared tree height [h_sf <= 64] makes every node height fit the native
    one-byte field and every path-derived node index fit the native eight-byte
    field.  The WOTS+C chain and position fields retain their exact library
    bounds; callers supply the range facts already proved by the WOTS+C folds.

    These are compatibility lemmas only.  The FXMSS scheme, games, assumptions,
    and security theorem remain unchanged. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude.
From Sec.fxmss Require Import address_bridge.
From Stdlib Require Import ZArith.

From SHRINCS.FXMSS Require Import Scheme.
Set Warnings "notation-overridden,ambiguous-paths".

(* ------------------------------------------------------------------ *)
(** ** Scheme and verification coordinates *)

Lemma pos_id_bounded h_sf p :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  anchor_bounded (pos_id h_sf p).
Proof. exact: path_anchor_bounded.
Qed.

Lemma sign_path_bounded h_sf sp q :
  (h_sf <= 64)%nat ->
  (q < size (leaf_paths (shape_of h_sf sp)))%nat ->
  anchor_bounded (pos_id h_sf (sign_path h_sf sp q)).
Proof.
  move=> hh hq.
  apply: pos_id_bounded hh.
  exact: sign_path_size.
Qed.

Lemma verify_anchor_bounded h_sf z i :
  (h_sf <= 64)%nat ->
  (z <= h_sf)%nat ->
  (i < expn 2 (h_sf - z))%nat ->
  anchor_bounded (z, i).
Proof. exact: fxmss_anchor_bounded.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Addresses reached by the FXMSS scheme *)

Section SchemeAddresses.

Variables chain_count w : nat.

Local Notation pos_bound := (w.-1).

Lemma path_tree_adrs_bounded h_sf p :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  adrs_bounded chain_count pos_bound
    (tree_node_adrs (h_sf - size p) (idx_of_path p)).
Proof.
  move=> hh hp.
  apply: tree_adrs_bounded.
  exact: path_anchor_bounded.
Qed.

Lemma path_grind_adrs_bounded h_sf p :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  adrs_bounded chain_count pos_bound
    (wotsc_grind_adrs (pos_id h_sf p)).
Proof.
  move=> hh hp.
  apply: grind_adrs_bounded.
  exact: pos_id_bounded.
Qed.

Lemma path_pk_adrs_bounded h_sf p :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  adrs_bounded chain_count pos_bound
    (wotsc_pk_adrs (pos_id h_sf p)).
Proof.
  move=> hh hp.
  apply: pk_adrs_bounded.
  exact: pos_id_bounded.
Qed.

Lemma path_prf_adrs_bounded h_sf p chain :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  (chain < chain_count)%nat ->
  adrs_bounded chain_count pos_bound
    (wotsc_prf_adrs (pos_id h_sf p) chain).
Proof.
  move=> hh hp Hchain.
  apply: prf_adrs_bounded.
  - exact: pos_id_bounded.
  - apply Nat2Z.inj_lt.
    exact/ltP.
Qed.

Lemma path_chain_adrs_bounded h_sf p chain pos :
  (h_sf <= 64)%nat ->
  (size p <= h_sf)%nat ->
  (chain < chain_count)%nat ->
  (pos < pos_bound)%nat ->
  adrs_bounded chain_count pos_bound
    (wotsc_chain_adrs (pos_id h_sf p) chain pos).
Proof.
  move=> hh hp Hchain Hpos.
  apply: chain_adrs_bounded.
  - exact: pos_id_bounded.
  - apply Nat2Z.inj_lt.
    exact/ltP.
  - apply Nat2Z.inj_lt.
    exact/ltP.
Qed.

End SchemeAddresses.
