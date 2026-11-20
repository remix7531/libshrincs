(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.tcrx

    Fixed-call regression guards for protocol aborts. The target oracle is
    independent of the bit, including failures. CHECK refuses unrevealed
    state on both bits. Repeated target calls may abort before the budget. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation tcrx.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat).

Lemma tcrx_query_no_setup (x : th_T T × th_M T) (answer : bool) :
  AdvOf (TCRX_game T target_class partner p)
    (guard_calls (XQUERY, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma tcrx_query_over_budget (x : th_T T × th_M T) (answer : bool) :
  AdvOf (TCRX_game T target_class partner p)
    (guard_calls (XQUERY, (th_T T × th_M T, th_N T)) x p.+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma tcrx_check_no_setup (x : 'nat × (th_T T × th_M T)) (answer : bool) :
  AdvOf (TCRX_game T target_class partner p)
    (guard_calls (XCHECK, ('nat × (th_T T × th_M T), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [j [t m]].
by rewrite !Pr_code_get /=.
Qed.

Lemma tcrx_reveal_no_setup (answer : bool) :
  AdvOf (TCRX_game T target_class partner p)
    (guard_calls (XGETPP, ('unit, th_PP T)) tt 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma tcrx_eval_no_setup (x : th_T T × th_M T) (answer : bool) :
  AdvOf (TCRX_game T target_class partner p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma tcrx_query_phase_abort (b : bool) (t : th_T T) (m : th_M T) (h : heap) :
  get_heap h tcrx_rev_loc = true ->
  Pr_code (resolve (TCRX_game T target_class partner p b)
    (XQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h.
Proof.
move=> hrev.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /=.
Qed.

Lemma tcrx_query_budget_abort (b : bool) (t : th_T T) (m : th_M T) (h : heap) :
  get_heap h tcrx_rev_loc = false ->
  (p <= size (get_heap h (tcrx_tws_loc T)))%N ->
  Pr_code (resolve (TCRX_game T target_class partner p b)
    (XQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h.
Proof.
move=> hrev hbudget.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /= Pr_code_get ltnNge hbudget /=.
Qed.

Lemma tcrx_query_after_reveal_phase_abort (t : th_T T) (m : th_M T)
    (answer : bool) :
  AdvOf (TCRX_game T target_class partner p)
    (guard_then (XGETPP, ('unit, th_PP T)) tt
      (XQUERY, (th_T T × th_M T, th_N T)) (t, m) erefl answer) = 0%R.
Proof.
apply: guard_then_adv_eq.
simplify_linking.
reflexivity.
Qed.

End Guards.
