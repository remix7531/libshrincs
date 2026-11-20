(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.sample_seq

    Coverage guard for the sampler micro-test package.
    This package is not a real/ideal pair and has no protocol checks;
    its constant bool-indexed lift is identical in both branches, even
    for a failing sampler. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common toolkit.sample_seq.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma sample_seq_test_no_setup (d : dist 'nat) (answer : bool) :
  AdvOf (fun _ : bool => SampleSeqTest.test_pkg d)
    (guard_calls (SampleSeqTest.TEST, ('unit, 'list ('nat))) tt 1 answer) = 0%R.
Proof. apply: guard_adv_oracle_eq. reflexivity. Qed.
