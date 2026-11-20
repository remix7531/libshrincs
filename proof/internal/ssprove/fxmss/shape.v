(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.shape

    The two legal BIP structures and their sequential leaf schedule.
    Unbalanced trees descend left and issue right siblings before the last
    left leaf. Coordinates are (height,index), both retained in tweaks and
    random-oracle separators. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.fxmss Require Import params.
From Shrincs Require Import spec schemes.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_structure_legal (b : bool) (d : nat) : bool :=
  (0 < d) && (d <= if b then 64 else 255).

Definition shrincs_fxmss_leaf_count (b : bool) (d : nat) : nat :=
  if b then 2 ^ d else d.+1.

Definition shrincs_fxmss_select_leaf (b : bool) (d q : nat) :
    option shrincs_fxmss_coord :=
  if shrincs_fxmss_structure_legal b d &&
       (q < shrincs_fxmss_leaf_count b d) then
    if b then Some (uint U8 (255 - d), uint U64 q)
    else if q == d then Some (uint U8 (255 - d), uint U64 0)
         else Some (uint U8 (254 - q), uint U64 1)
  else None.

Definition shrincs_fxmss_leaf_at (b : bool) (d : UInt8) (a : shrincs_fxmss_coord) : bool
  :=
  (255 - Z.to_nat (wunsigned a.1) == Z.to_nat (wunsigned d)) ||
  (~~ b && (a.2 == uint U64 1)).

Lemma shrincs_fxmss_legal_depth b d :
  shrincs_fxmss_structure_legal b d -> d <= 255.
Proof.
rewrite /shrincs_fxmss_structure_legal.
case: b => /andP[_ hd] //.
exact: leq_trans hd (isT : 64 <= 255).
Qed.

Lemma shrincs_fxmss_legal_positive b d :
  shrincs_fxmss_structure_legal b d -> 0 < d.
Proof. by move/andP=> []. Qed.

Lemma shrincs_fxmss_balanced_depth d :
  shrincs_fxmss_structure_legal true d -> d <= 64.
Proof. by move/andP=> []. Qed.

Lemma shrincs_fxmss_select_leaf_none b d q :
  ~~ (shrincs_fxmss_structure_legal b d &&
      (q < shrincs_fxmss_leaf_count b d)) ->
  shrincs_fxmss_select_leaf b d q = None.
Proof. by rewrite /shrincs_fxmss_select_leaf => /negbTE ->. Qed.

Lemma shrincs_fxmss_select_leaf_some b d q a :
  shrincs_fxmss_select_leaf b d q = Some a ->
  shrincs_fxmss_structure_legal b d /\ q < shrincs_fxmss_leaf_count b d.
Proof.
rewrite /shrincs_fxmss_select_leaf.
by case: ifP => [/andP[hb hq]|] // _.
Qed.

Lemma shrincs_fxmss_select_balanced d q :
  shrincs_fxmss_structure_legal true d -> q < 2 ^ d ->
  shrincs_fxmss_select_leaf true d q =
    Some (uint U8 (255 - d), uint U64 q).
Proof. by move=> hd hq; rewrite /shrincs_fxmss_select_leaf hd /= hq. Qed.

Lemma shrincs_fxmss_select_unbalanced_last d :
  shrincs_fxmss_structure_legal false d ->
  shrincs_fxmss_select_leaf false d d =
    Some (uint U8 (255 - d), uint U64 0).
Proof. by move=> hd; rewrite /shrincs_fxmss_select_leaf hd /= ltnSn eqxx. Qed.

Lemma shrincs_fxmss_select_unbalanced_right d q :
  shrincs_fxmss_structure_legal false d -> q < d ->
  shrincs_fxmss_select_leaf false d q =
    Some (uint U8 (254 - q), uint U64 1).
Proof.
move=> hd hq.
rewrite /shrincs_fxmss_select_leaf hd /= (ltn_trans hq (ltnSn d)).
by rewrite (ltn_eqF hq).
Qed.

Lemma shrincs_fxmss_leaf_count_bound b d :
  shrincs_fxmss_structure_legal b d ->
  shrincs_fxmss_leaf_count b d <= 2 ^ 64.
Proof.
case: b => /andP[_ hd].
- by rewrite /shrincs_fxmss_leaf_count leq_exp2l.
- rewrite /shrincs_fxmss_leaf_count.
  apply: (@leq_trans (2 ^ 8) d.+1 (2 ^ 64)).
  + exact: hd.
  + by rewrite leq_exp2l.
Qed.
