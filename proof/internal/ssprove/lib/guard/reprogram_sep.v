(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.reprogram_sep

    Guards for leaf-separated reprogramming.
    Without reprogramming, every QUERY charges the counter. REPRO permits
    at most one call per separator: two calls with the same suffix exceed
    that limit. Both checks precede the bit. Only the single-call REPRO
    guard needs losslessness of the extra output sampler. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common
  toolkit.ro_plus toolkit.reprogram_sep.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SepGuards.
Context (Pfx X R I : choice_type) (sep : X -> I)
  (dPfx : dist Pfx) (dR : dist R) (qh : nat).

Lemma ro_sep_query_no_setup (x : Pfx × X) (answer : bool) :
  AdvOf (RO_repro_sep Pfx X R I sep dPfx dR qh)
    (guard_calls (QUERY, (Pfx × X, R)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma ro_sep_query_over_budget (x : Pfx × X) (answer : bool) :
  AdvOf (RO_repro_sep Pfx X R I sep dPfx dR qh)
    (guard_calls (QUERY, (Pfx × X, R)) x qh.+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma ro_sep_repro_no_setup (x : X) (answer : bool) :
  LosslessCode dR ->
  AdvOf (RO_repro_sep Pfx X R I sep dPfx dR qh)
    (guard_calls (REPRO, (X, Pfx)) x 1 answer) = 0%R.
Proof.
move=> hr; apply: guard_adv_fst_eq.
simplify_linking.
rewrite !Pr_code_get /= !Pr_code_put !bind_assoc
  (Pr_code_fst (prog_valid dPfx)) (Pr_code_fst (prog_valid dPfx))
  !dfst_dlet_commut.
apply eq_dlet => r.
rewrite Pr_code_get.
match goal with
| |- context [Pr_code (?f ?A ?B ?c ?k) ?h] =>
  change (Pr_code (f A B c k) h) with (Pr_code (bind c k) h) end.
rewrite bind_assoc (Pr_code_fst (prog_valid dR)) dfst_dlet_commut.
under eq_dlet do rewrite Pr_code_put Pr_code_ret dmarginE dlet_unit_ext /=.
by rewrite (Pr_fstC hr) Pr_code_ret dmarginE dlet_unit_ext.
Qed.

Lemma ro_sep_repro_over_budget (x : X) (answer : bool) :
  AdvOf (RO_repro_sep Pfx X R I sep dPfx dR qh)
    (guard_calls (REPRO, (X, Pfx)) x 2 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
rewrite !Pr_code_get /= !Pr_code_put !bind_assoc
  (Pr_code_fst (prog_valid dPfx)) (Pr_code_fst (prog_valid dPfx)).
under eq_dlet.
- (* The repeated query aborts for each sampled prefix. *)
  move=> r; rewrite Pr_code_get.
  match goal with
  | |- context [Pr_code (?f ?A ?B ?c ?k) ?h] =>
    change (Pr_code (f A B c k) h) with (Pr_code (bind c k) h) end.
  rewrite bind_assoc (Pr_code_fst (prog_valid dR)).
  under eq_dlet do rewrite Pr_code_put Pr_code_get get_set_heap_neq //
    get_set_heap_eq /= in_cons eqxx /= Pr_code_sample dlet_null_ext.
  over.
under [RHS]eq_dlet do rewrite Pr_code_get get_set_heap_eq /=
  in_cons eqxx /= Pr_code_sample dlet_null_ext.
apply distr_ext => z.
by rewrite !dletC dnullE !GRing.mulr0.
Qed.

End SepGuards.
