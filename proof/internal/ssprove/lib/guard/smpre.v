(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.smpre

    Protocol-abort regression guards for the public smpre experiment.
    Fixed calls ignore replies; initialized-heap checks exercise exhausted
    budgets and closed phases directly, without stopping at an earlier call. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation smpre.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Lemma smpre_query_no_setup (x : th_T T) (answer : bool) :
  AdvOf (SMPRE_game T target_class p)
    (guard_calls (PQUERY, (th_T T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smpre_query_over_budget (x : th_T T) (answer : bool) :
  AdvOf (SMPRE_game T target_class p)
    (guard_calls (PQUERY, (th_T T, th_N T)) x p.+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smpre_reveal_no_setup (x : 'unit) (answer : bool) :
  AdvOf (SMPRE_game T target_class p)
    (guard_calls (PGETPP, ('unit, th_PP T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smpre_eval_no_setup (x : th_T T × th_M T) (answer : bool) :
  AdvOf (SMPRE_game T target_class p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smpre_check_no_setup (x : 'nat × th_M T) (answer : bool) :
  AdvOf (SMPRE_game T target_class p)
    (guard_calls (PCHECK, ('nat × th_M T, 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [j m].
by rewrite !Pr_code_get /=.
Qed.

Lemma smpre_query_phase_abort (b : bool) (t : th_T T) (h : heap) :
  get_heap h pre_rev_loc = true ->
  Pr_code (resolve (SMPRE_game T target_class p b)
    (PQUERY, (th_T T, th_N T)) t) h = Pr_code fail h.
Proof.
move=> hrev.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /=.
Qed.

Lemma smpre_query_budget_abort (b : bool) (t : th_T T) (h : heap) :
  get_heap h pre_rev_loc = false ->
  (p <= size (get_heap h (pre_tws_loc T)))%N ->
  Pr_code (resolve (SMPRE_game T target_class p b)
    (PQUERY, (th_T T, th_N T)) t) h = Pr_code fail h.
Proof.
move=> hrev hbudget.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /= Pr_code_get ltnNge hbudget /=.
Qed.

Lemma smpre_query_after_reveal_phase_abort (t : th_T T)
    (answer : bool) :
  AdvOf (SMPRE_game T target_class p)
    (guard_then (PGETPP, ('unit, th_PP T)) tt
      (PQUERY, (th_T T, th_N T)) t erefl answer) = 0%R.
Proof.
apply: guard_then_adv_eq.
simplify_linking.
reflexivity.
Qed.

End Guards.
