(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.smud

    Protocol-abort guards for [SMUD_game].
    UGETPP ends the target phase; no setup is needed before UQUERY. A single
    query uses the losslessness laws supplied by the caller.
    The repeated-query guard is unconditional: a duplicate tweak aborts at call two. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation smud.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Restoring the bind spine after a state read lets the semantic bind
   lemmas match; reduction under the raw-code coercion unfolds that spine. *)
Local Ltac fold_pr_bind :=
  match goal with
  | |- context [Pr_code (?f ?A ?B ?c ?k) ?h] =>
    change (Pr_code (f A B c k) h) with (Pr_code (bind c k) h)
  end.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool).

Lemma smud_uquery_no_setup
    (hdpp : LosslessCode (th_dPP T))
    (hdm : LosslessCode (th_dM T))
    (hdn : LosslessCode (th_dN T))
    (p : nat) (t : th_T T) (answer : bool) :
  AdvOf (SMUD_game T target_class p)
    (guard_calls (UQUERY, (th_T T, th_N T)) t 1 answer) = 0%R.
Proof.
apply: guard_adv_fst_eq.
simplify_linking.
case hclass: (target_class t) => //=.
rewrite !Pr_code_get /=.
case: p => [|p] //=.
rewrite !Pr_code_put Pr_code_get /= !bind_assoc.
change (dfst (Pr_code
  (bind (pp ← th_dPP T ;; #put ud_pp_loc T := Some pp ;;
         x ← th_dM T ;; ret (th_eval T pp t x)) (fun _ => ret answer))
  (set_heap empty_heap (ud_tws_loc T) [:: t])) =
  dfst (Pr_code (bind (y ← th_dN T ;; ret y) (fun _ => ret answer))
    (set_heap empty_heap (ud_tws_loc T) [:: t]))).
rewrite !bind_assoc.
rewrite (Pr_code_fst (prog_valid (th_dPP T)))
  (Pr_code_fst (prog_valid (th_dN T))) !dfst_dlet_commut.
under eq_dlet.
- (* The real branch integrates a lossless message sample. *)
  move=> pp.
  rewrite Pr_code_put.
  fold_pr_bind.
  rewrite bind_assoc (Pr_code_fst (prog_valid (th_dM T))) dfst_dlet_commut.
  under eq_dlet do rewrite Pr_code_ret dmarginE dlet_unit_ext /=.
  rewrite (Pr_fstC hdm).
  over.
under [RHS]eq_dlet do rewrite Pr_code_ret dmarginE dlet_unit_ext /=.
by rewrite (Pr_fstC hdpp) (Pr_fstC hdn).
Qed.

Lemma smud_uquery_repeated_abort (p : nat) (t : th_T T) (answer : bool) :
  AdvOf (SMUD_game T target_class p)
    (guard_calls (UQUERY, (th_T T, th_N T)) t p.+1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
case hclass: (target_class t).
2: {
  rewrite /guard_repeat -/guard_repeat.
  simplify_linking.
  by rewrite hclass /= !Pr_code_sample !dlet_null_ext.
}
case: p => [|p].
- (* Zero budget: no sampling occurs in either branch. *)
  simplify_linking.
  by rewrite hclass /= !Pr_code_get /=.
- (* Positive budget: the duplicate tweak forces both tails to fail. *)
  rewrite /guard_repeat -/guard_repeat.
  simplify_linking.
  rewrite hclass /= !Pr_code_get /= !Pr_code_put Pr_code_get /= !bind_assoc.
  match goal with
  | |- Pr_code (?f ?A ?B ?c ?k) ?h =
       Pr_code (?g ?A' ?B' ?c' ?k') ?h' =>
    change (Pr_code (bind c k) h = Pr_code (bind c' k') h')
  end.
  rewrite !bind_assoc.
  rewrite (Pr_code_fst (prog_valid (th_dPP T)))
    (Pr_code_fst (prog_valid (th_dN T))).
  under eq_dlet.
  + move=> pp.
    rewrite Pr_code_put.
    fold_pr_bind.
    rewrite bind_assoc (Pr_code_fst (prog_valid (th_dM T))).
    under eq_dlet do rewrite Pr_code_get !get_set_heap_neq //=
      Pr_code_get get_set_heap_neq // get_set_heap_eq /= in_cons eqxx /=.
    under eq_dlet.
    * move=> x.
      case: (1 < p.+1)%N => /=;
        rewrite Pr_code_sample dlet_null_ext; over.
    over.
  under [RHS]eq_dlet.
  + (* The ideal branch aborts on the duplicate target. *)
    move=> y.
    rewrite Pr_code_get get_set_heap_neq //= Pr_code_get
      get_set_heap_eq /= in_cons eqxx /=.
    case: (1 < p.+1)%N => /=;
      rewrite Pr_code_sample dlet_null_ext; over.
  apply distr_ext => z.
  by rewrite !dletC dnullE !GRing.mulr0.
Qed.

Lemma smud_query_phase_abort (b : bool) (p : nat) (t : th_T T) (h : heap) :
  get_heap h ud_rev_loc = true ->
  Pr_code (resolve (SMUD_game T target_class p b)
    (UQUERY, (th_T T, th_N T)) t) h = Pr_code fail h.
Proof.
move=> hrev.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /=.
Qed.

Lemma smud_query_budget_abort (b : bool) (p : nat) (t : th_T T) (h : heap) :
  get_heap h ud_rev_loc = false ->
  (p <= size (get_heap h (ud_tws_loc T)))%N ->
  Pr_code (resolve (SMUD_game T target_class p b)
    (UQUERY, (th_T T, th_N T)) t) h = Pr_code fail h.
Proof.
move=> hrev hbudget.
simplify_linking.
case: (target_class t) => //=.
by rewrite Pr_code_get hrev /= Pr_code_get ltnNge hbudget /=.
Qed.

Lemma smud_query_after_reveal_phase_abort (p : nat) (t : th_T T)
    (answer : bool) :
  AdvOf (SMUD_game T target_class p)
    (guard_then (UGETPP, ('unit, th_PP T)) tt
      (UQUERY, (th_T T, th_N T)) t erefl answer) = 0%R.
Proof.
apply: guard_then_adv_eq.
simplify_linking.
rewrite !Pr_code_get /= !bind_assoc.
rewrite !(Pr_code_fst (prog_valid (th_dPP T))).
under eq_dlet.
- move=> pp.
  rewrite !Pr_code_put.
  case: (target_class t) => /=.
  + rewrite Pr_code_get get_set_heap_eq /= Pr_code_sample dlet_null_ext.
    over.
  + rewrite Pr_code_sample dlet_null_ext.
    over.
under [RHS]eq_dlet.
- move=> pp.
  rewrite !Pr_code_put.
  case: (target_class t) => /=.
  + rewrite Pr_code_get get_set_heap_eq /= Pr_code_sample dlet_null_ext.
    over.
  + rewrite Pr_code_sample dlet_null_ext.
    over.
reflexivity.
Qed.

End Guards.
