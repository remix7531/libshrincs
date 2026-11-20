(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.prf

    Protocol-abort guards for [PRF_game].
    There is no setup call. One successful query uses the losslessness
    laws supplied by the caller. With fixed arguments the second query fails
    freshness, regardless of the remaining budget. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation prf.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (K : khf).

Lemma prf_fquery_no_setup
    (hdk : LosslessCode (kh_dK K))
    (hdn : LosslessCode (kh_dN K))
    (q : nat) (m : kh_M K) (answer : bool) :
  AdvOf (PRF_game K q)
    (guard_calls (FQUERY, (kh_M K, kh_N K)) m 1 answer) = 0%R.
Proof.
apply: guard_adv_fst_eq.
simplify_linking.
rewrite !Pr_code_get /=.
case: q => [|q] //=.
rewrite !Pr_code_put Pr_code_get /= !bind_assoc.
rewrite (Pr_code_fst (prog_valid (kh_dK K)))
  (Pr_code_fst (prog_valid (kh_dN K))) !dfst_dlet_commut.
under eq_dlet do rewrite Pr_code_put Pr_code_ret dmarginE dlet_unit_ext.
under [RHS]eq_dlet do rewrite Pr_code_ret dmarginE dlet_unit_ext.
by rewrite /= (Pr_fstC hdk) (Pr_fstC hdn).
Qed.

Lemma prf_fquery_repeated_abort (q : nat) (m : kh_M K) (answer : bool) :
  AdvOf (PRF_game K q)
    (guard_calls (FQUERY, (kh_M K, kh_N K)) m q.+1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
case: q => [|q].
- (* Zero budget: the first call aborts in both branches. *)
  simplify_linking.
  by rewrite !Pr_code_get /=.
- (* Positive budget: the second fixed query is a duplicate. *)
  rewrite /guard_repeat -/guard_repeat.
  simplify_linking.
  rewrite !Pr_code_get /= !Pr_code_put Pr_code_get /= !bind_assoc.
  rewrite (Pr_code_fst (prog_valid (kh_dK K)))
    (Pr_code_fst (prog_valid (kh_dN K))).
  under eq_dlet do rewrite Pr_code_put Pr_code_get get_set_heap_neq //
    get_set_heap_eq /= in_cons eqxx /=.
  under [RHS]eq_dlet do rewrite Pr_code_get get_set_heap_eq /= in_cons eqxx /=.
  case: (1 < q.+1)%N => /=;
    under eq_dlet do rewrite Pr_code_sample dlet_null_ext;
    under [RHS]eq_dlet do rewrite Pr_code_sample dlet_null_ext;
    apply distr_ext => z;
    by rewrite !dletC !dnullE !GRing.mulr0.
Qed.

Lemma prf_query_budget_abort (q : nat) (b : bool)
    (m : kh_M K) (h : heap) :
  (q <= size (get_heap h (prf_qs_loc K)))%N ->
  Pr_code (resolve (PRF_game K q b)
    (FQUERY, (kh_M K, kh_N K)) m) h = Pr_code fail h.
Proof.
move=> hbudget.
simplify_linking.
by rewrite Pr_code_get ltnNge hbudget /=.
Qed.

End Guards.
