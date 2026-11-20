(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.public

    Protocol-abort guards for the concrete public games in schemes.v.
    These instantiate the generic guards without a hash-security premise. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude guard.common guard.stcrp_option guard.tcrx guard.smtcr.
From Shrincs Require Import games schemes.

Import PackageNotation stcrp_option tcrx smtcr.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (p : nat).

Lemma fxmss_grind_query_no_setup (x : th_T (shrincs_thf) × (bytes 32)) (answer :
  bool) :
  AdvOf (fxmss_grind_game p)
    (guard_calls (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) x 1 answer) = 0%R.
Proof. exact: stcrp_option_query_no_setup. Qed.

Lemma fxmss_grind_query_over_budget (x : th_T (shrincs_thf) × (bytes 32))
  (answer : bool) :
  AdvOf (fxmss_grind_game p)
    (guard_calls (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) x p.+1 answer) = 0%R.
Proof. exact: stcrp_option_query_over_budget. Qed.

Lemma fxmss_grind_check_no_setup (x : 'nat × ((bytes 32) × 'nat)) (answer :
  bool) :
  AdvOf (fxmss_grind_game p)
    (guard_calls (SCHECK, ('nat × ((bytes 32) × 'nat), 'bool)) x 1 answer) = 0%R.
Proof. exact: stcrp_option_check_no_setup. Qed.

Lemma fxmss_grind_reveal_no_setup (answer : bool) :
  AdvOf (fxmss_grind_game p)
    (guard_calls (SGETPP, ('unit, th_PP (shrincs_thf))) tt 1 answer) = 0%R.
Proof. exact: stcrp_option_reveal_no_setup. Qed.

Lemma fxmss_grind_eval_no_setup (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_grind_game p)
    (guard_calls (EVAL, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R.
Proof. exact: stcrp_option_eval_no_setup. Qed.

Lemma fxmss_grind_query_phase_abort (b : bool) (t : th_T (shrincs_thf)) (m :
  (bytes 32)) (h : heap) :
  get_heap h stcr_option_rev_loc = true ->
  Pr_code (resolve (fxmss_grind_game p b)
    (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) (t, m)) h = Pr_code fail h.
Proof. exact: stcrp_option_query_phase_abort. Qed.

Lemma fxmss_grind_query_budget_abort (b : bool) (t : th_T (shrincs_thf)) (m :
  (bytes 32)) (h : heap) :
  get_heap h stcr_option_rev_loc = false ->
  (p <= size (get_heap h (stcr_option_tws_loc (shrincs_thf))))%N ->
  Pr_code (resolve (fxmss_grind_game p b)
    (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) (t, m)) h = Pr_code fail h.
Proof. exact: stcrp_option_query_budget_abort. Qed.

Lemma fxmss_grind_query_after_reveal_phase_abort (t : th_T (shrincs_thf)) (m :
  (bytes 32))
    (answer : bool) :
  AdvOf (fxmss_grind_game p)
    (guard_then (SGETPP, ('unit, th_PP (shrincs_thf))) tt
      (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) (t, m) erefl answer) = 0%R.
Proof. exact: stcrp_option_query_after_reveal_phase_abort. Qed.

Lemma fxmss_tcrx_query_no_setup (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_tcrx_game p)
    (guard_calls (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R.
Proof. exact: tcrx_query_no_setup. Qed.

Lemma fxmss_tcrx_query_over_budget (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_tcrx_game p)
    (guard_calls (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x p.+1 answer) = 0%R.
Proof. exact: tcrx_query_over_budget. Qed.

Lemma fxmss_tcrx_check_no_setup (x : 'nat × (th_T (shrincs_thf) × th_M
  (shrincs_thf))) (answer : bool) :
  AdvOf (fxmss_tcrx_game p)
    (guard_calls (XCHECK, ('nat × (th_T (shrincs_thf) × th_M (shrincs_thf)), 'bool)) x 1 answer) = 0%R.
Proof. exact: tcrx_check_no_setup. Qed.

Lemma fxmss_tcrx_reveal_no_setup (answer : bool) :
  AdvOf (fxmss_tcrx_game p)
    (guard_calls (XGETPP, ('unit, th_PP (shrincs_thf))) tt 1 answer) = 0%R.
Proof. exact: tcrx_reveal_no_setup. Qed.

Lemma fxmss_tcrx_eval_no_setup (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_tcrx_game p)
    (guard_calls (EVAL, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R.
Proof. exact: tcrx_eval_no_setup. Qed.

Lemma fxmss_tcrx_query_phase_abort (b : bool) (t : th_T (shrincs_thf)) (m : th_M
  (shrincs_thf)) (h : heap) :
  get_heap h tcrx_rev_loc = true ->
  Pr_code (resolve (fxmss_tcrx_game p b)
    (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h.
Proof. exact: tcrx_query_phase_abort. Qed.

Lemma fxmss_tcrx_query_budget_abort (b : bool) (t : th_T (shrincs_thf)) (m :
  th_M (shrincs_thf)) (h : heap) :
  get_heap h tcrx_rev_loc = false ->
  (p <= size (get_heap h (tcrx_tws_loc (shrincs_thf))))%N ->
  Pr_code (resolve (fxmss_tcrx_game p b)
    (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h.
Proof. exact: tcrx_query_budget_abort. Qed.

Lemma fxmss_tcrx_query_after_reveal_phase_abort (t : th_T (shrincs_thf)) (m :
  th_M (shrincs_thf))
    (answer : bool) :
  AdvOf (fxmss_tcrx_game p)
    (guard_then (XGETPP, ('unit, th_PP (shrincs_thf))) tt
      (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m) erefl answer) = 0%R.
Proof. exact: tcrx_query_after_reveal_phase_abort. Qed.

Lemma fxmss_tree_query_no_setup (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_tree_game p)
    (guard_calls (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R.
Proof. exact: smtcr_query_no_setup. Qed.

Lemma fxmss_tree_query_over_budget (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_tree_game p)
    (guard_calls (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x p.+1 answer) = 0%R.
Proof. exact: smtcr_query_over_budget. Qed.

Lemma fxmss_tree_reveal_no_setup (x : 'unit) (answer : bool) :
  AdvOf (fxmss_tree_game p)
    (guard_calls (GETPP, ('unit, th_PP (shrincs_thf))) x 1 answer) = 0%R.
Proof. exact: smtcr_reveal_no_setup. Qed.

Lemma fxmss_tree_eval_no_setup (x : th_T (shrincs_thf) × th_M (shrincs_thf))
  (answer : bool) :
  AdvOf (fxmss_tree_game p)
    (guard_calls (EVAL, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R.
Proof. exact: smtcr_eval_no_setup. Qed.

Lemma fxmss_tree_check_no_setup (x : 'nat × th_M (shrincs_thf)) (answer : bool)
  :
  AdvOf (fxmss_tree_game p)
    (guard_calls (CHECK, ('nat × th_M (shrincs_thf), 'bool)) x 1 answer) = 0%R.
Proof. exact: smtcr_check_no_setup. Qed.

Lemma fxmss_tree_query_phase_abort (b : bool) (t : th_T (shrincs_thf)) (m : th_M
  (shrincs_thf)) (h : heap) :
  get_heap h tcr_rev_loc = true ->
  Pr_code (resolve (fxmss_tree_game p b)
    (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h.
Proof. exact: smtcr_query_phase_abort. Qed.

Lemma fxmss_tree_query_budget_abort (b : bool) (t : th_T (shrincs_thf)) (m :
  th_M (shrincs_thf)) (h : heap) :
  get_heap h tcr_rev_loc = false ->
  (p <= size (get_heap h (tcr_tws_loc (shrincs_thf))))%N ->
  Pr_code (resolve (fxmss_tree_game p b)
    (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h.
Proof. exact: smtcr_query_budget_abort. Qed.

Lemma fxmss_tree_query_after_reveal_phase_abort (t : th_T (shrincs_thf)) (m :
  th_M (shrincs_thf))
    (answer : bool) :
  AdvOf (fxmss_tree_game p)
    (guard_then (GETPP, ('unit, th_PP (shrincs_thf))) tt
      (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m) erefl answer) = 0%R.
Proof. exact: smtcr_query_after_reveal_phase_abort. Qed.

End Guards.
