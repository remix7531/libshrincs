(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.lossless

    Unit mass of admitted oracle executions, including lazy sampling.
    Protocol assertions are discharged by explicit state side conditions. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp Require Import reals.
From mathcomp.experimental_reals Require Import distr realsum.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma dweight_dlet_one (A B : choiceType) (mu : distr R A)
    (f : A -> distr R B) :
  dweight mu = 1%R ->
  (forall x, dweight (f x) = 1%R) ->
  dweight (dlet f mu) = 1%R.
Proof.
move=> hmu hf.
rewrite pr_dlet.
under eq_exp do rewrite hf.
by rewrite exp_cst hmu GRing.mulr1.
Qed.

Lemma lossless_dist_bind (A B : choice_type) (d : dist A)
    (f : A -> raw_code B) (h : heap) :
  LosslessCode d ->
  (forall x, dweight (Pr_code (f x) h) = 1%R) ->
  dweight (Pr_code (x ← d ;; f x) h) = 1%R.
Proof.
move=> hd hf.
rewrite Pr_code_fst.
apply: dweight_dlet_one hf.
by rewrite pr_predT; exact: hd.
Qed.
