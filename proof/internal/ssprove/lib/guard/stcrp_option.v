(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.stcrp_option

    Fixed-call regression guards for protocol aborts. The target oracle is
    independent of the bit, including failures. SCHECK refuses unrevealed
    state on both bits. Repeated target calls may abort before the budget. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat).

Lemma stcrp_option_query_no_setup (x : th_T T × Mb) (answer : bool) :
  AdvOf (STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma stcrp_option_query_over_budget (x : th_T T × Mb) (answer : bool) :
  AdvOf (STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) x p.+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma stcrp_option_check_no_setup (x : 'nat × (Mb × 'nat)) (answer : bool) :
  AdvOf (STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SCHECK, ('nat × (Mb × 'nat), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [j [m ctr]].
by rewrite !Pr_code_get /=.
Qed.

Lemma stcrp_option_reveal_no_setup (answer : bool) :
  AdvOf (STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SGETPP, ('unit, th_PP T)) tt 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma stcrp_option_eval_no_setup (x : th_T T × th_M T) (answer : bool) :
  AdvOf (STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma stcrp_option_query_phase_abort (b : bool) (t : th_T T) (m : Mb) (h : heap) :
  get_heap h stcr_option_rev_loc = true ->
  Pr_code (resolve (STCRP_option_game T target_class Mb enc prp cap p b)
    (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) (t, m)) h = Pr_code fail h.
Proof.
move=> hrev.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /=.
Qed.

Lemma stcrp_option_query_budget_abort (b : bool) (t : th_T T) (m : Mb) (h : heap) :
  get_heap h stcr_option_rev_loc = false ->
  (p <= size (get_heap h (stcr_option_tws_loc T)))%N ->
  Pr_code (resolve (STCRP_option_game T target_class Mb enc prp cap p b)
    (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) (t, m)) h = Pr_code fail h.
Proof.
move=> hrev hbudget.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /= Pr_code_get ltnNge hbudget /=.
Qed.

Lemma stcrp_option_query_after_reveal_phase_abort (t : th_T T) (m : Mb)
    (answer : bool) :
  AdvOf (STCRP_option_game T target_class Mb enc prp cap p)
    (guard_then (SGETPP, ('unit, th_PP T)) tt
      (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) (t, m) erefl answer) = 0%R.
Proof.
apply: guard_then_adv_eq.
simplify_linking.
reflexivity.
Qed.

End Guards.
