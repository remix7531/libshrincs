(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.smtcr

    Protocol-abort regression guards for the public smtcr experiment.
    Fixed calls ignore replies; initialized-heap checks exercise exhausted
    budgets and closed phases directly, without stopping at an earlier call. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation smtcr.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Lemma smtcr_query_no_setup (x : th_T T × th_M T) (answer : bool) :
  AdvOf (SMTCR_game T target_class p)
    (guard_calls (TQUERY, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smtcr_query_over_budget (x : th_T T × th_M T) (answer : bool) :
  AdvOf (SMTCR_game T target_class p)
    (guard_calls (TQUERY, (th_T T × th_M T, th_N T)) x p.+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smtcr_reveal_no_setup (x : 'unit) (answer : bool) :
  AdvOf (SMTCR_game T target_class p)
    (guard_calls (GETPP, ('unit, th_PP T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smtcr_eval_no_setup (x : th_T T × th_M T) (answer : bool) :
  AdvOf (SMTCR_game T target_class p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma smtcr_check_no_setup (x : 'nat × th_M T) (answer : bool) :
  AdvOf (SMTCR_game T target_class p)
    (guard_calls (CHECK, ('nat × th_M T, 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [j m].
by rewrite !Pr_code_get /=.
Qed.

Lemma smtcr_query_phase_abort (b : bool) (t : th_T T) (m : th_M T) (h : heap) :
  get_heap h tcr_rev_loc = true ->
  Pr_code (resolve (SMTCR_game T target_class p b)
    (TQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h.
Proof.
move=> hrev.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /=.
Qed.

Lemma smtcr_query_budget_abort (b : bool) (t : th_T T) (m : th_M T) (h : heap) :
  get_heap h tcr_rev_loc = false ->
  (p <= size (get_heap h (tcr_tws_loc T)))%N ->
  Pr_code (resolve (SMTCR_game T target_class p b)
    (TQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h.
Proof.
move=> hrev hbudget.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /= Pr_code_get ltnNge hbudget /=.
Qed.

Lemma smtcr_query_after_reveal_phase_abort (t : th_T T) (m : th_M T)
    (answer : bool) :
  AdvOf (SMTCR_game T target_class p)
    (guard_then (GETPP, ('unit, th_PP T)) tt
      (TQUERY, (th_T T × th_M T, th_N T)) (t, m) erefl answer) = 0%R.
Proof.
apply: guard_then_adv_eq.
simplify_linking.
reflexivity.
Qed.

End Guards.
