(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.ro_plus

    Guards for the random oracle with reprogramming, defined in ro_plus
    and reused by reprogram.
    QUERY is bit-independent. REPRO checks its counter before the bit;
    its single-call guard needs only the extra output sampler to be
    lossless. The common prefix sampler may fail. Counter exhaustion
    needs neither premise. The concrete test instance discharges dR. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common toolkit.ro_plus.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section ROGuards.
Context (Pfx X R : choice_type) (dPfx : dist Pfx) (dR : dist R) (qh qp : nat).

Lemma guard_resolve_repro (b : bool) (x : X) :
  resolve (RO_repro Pfx X R dPfx dR qh qp b) (REPRO, (X, Pfx)) x =
  (rc ← get ro_rcnt_loc ;;
   #assert (rc < qp)%N ;;
   #put ro_rcnt_loc := rc.+1 ;;
   r ← dPfx ;;
   if b then
     m ← get (ro_map_loc Pfx X R) ;;
     y ← dR ;;
     #put (ro_map_loc Pfx X R) := setm m (r, x) y ;;
     ret r
   else ret r).
Proof.
simplify_linking.
reflexivity.
Qed.

Lemma ro_repro_exhausted (b : bool) (x : X) (answer : bool) (n : nat) (h : heap) :
  (qp <= get_heap h ro_rcnt_loc + n)%N ->
  Pr_code (code_link (guard_repeat (REPRO, (X, Pfx)) x n.+1 answer)
    (RO_repro Pfx X R dPfx dR qh qp b)) h = dnull.
Proof.
elim: n h => [|n hrec] h hq.
- (* The next call is rejected. *)
  change (Pr_code (bind
    (resolve (RO_repro Pfx X R dPfx dR qh qp b) (REPRO, (X, Pfx)) x)
    (fun _ => ret answer)) h = dnull).
  rewrite guard_resolve_repro Pr_code_get.
  have -> : (get_heap h ro_rcnt_loc < qp)%N = false.
  { by apply/negbTE; rewrite -leqNgt; move: hq; rewrite addn0. }
  by rewrite /= Pr_code_sample dlet_null_ext.
- (* Successful calls leave fewer calls until the shared abort. *)
  change (Pr_code (bind
    (resolve (RO_repro Pfx X R dPfx dR qh qp b) (REPRO, (X, Pfx)) x)
    (fun _ => code_link (guard_repeat (REPRO, (X, Pfx)) x n.+1 answer)
      (RO_repro Pfx X R dPfx dR qh qp b))) h = dnull).
  rewrite guard_resolve_repro Pr_code_get.
  case hc: (get_heap h ro_rcnt_loc < qp)%N => /=;
    last by rewrite Pr_code_sample dlet_null_ext.
  rewrite Pr_code_put.
  match goal with
  | |- Pr_code (?f ?A ?B ?c ?k) ?h = _ =>
    change (Pr_code (bind c k) h = dnull)
  end.
  rewrite bind_assoc (Pr_code_fst (prog_valid dPfx)).
  case: b hrec => hrec.
  + (* Reprogramming also samples and updates the map. *)
    under eq_dlet.
    * move=> r; rewrite Pr_code_get.
      match goal with |- context [Pr_code (?f ?A ?B ?c ?k) ?h] =>
        change (Pr_code (f A B c k) h) with (Pr_code (bind c k) h) end.
      rewrite bind_assoc (Pr_code_fst (prog_valid dR)).
      under eq_dlet.
      -- move=> y; rewrite Pr_code_put.
         rewrite hrec; first by rewrite get_set_heap_neq //
            get_set_heap_eq addSn -addnS.
         over.
      over.
    apply distr_ext => z.
    by rewrite !dletC dnullE !GRing.mulr0.
  + under eq_dlet.
    * move=> r; rewrite hrec; first by rewrite get_set_heap_eq addSn -addnS.
      over.
    apply distr_ext => z.
    by rewrite dletC dnullE GRing.mulr0.
Qed.

Lemma ro_repro_over_budget (x : X) (answer : bool) :
  AdvOf (RO_repro Pfx X R dPfx dR qh qp)
    (guard_calls (REPRO, (X, Pfx)) x qp.+1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
by rewrite !ro_repro_exhausted //= add0n.
Qed.

Lemma ro_query_no_setup (x : Pfx × X) (answer : bool) :
  AdvOf (RO_repro Pfx X R dPfx dR qh qp)
    (guard_calls (QUERY, (Pfx × X, R)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma ro_query_over_budget (x : Pfx × X) (answer : bool) :
  AdvOf (RO_repro Pfx X R dPfx dR qh qp)
    (guard_calls (QUERY, (Pfx × X, R)) x qh.+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma ro_repro_no_setup (x : X) (answer : bool) :
  LosslessCode dR ->
  AdvOf (RO_repro Pfx X R dPfx dR qh qp)
    (guard_calls (REPRO, (X, Pfx)) x 1 answer) = 0%R.
Proof.
move=> hr.
apply: guard_adv_fst_eq.
simplify_linking.
rewrite !Pr_code_get /=.
case: qp => [|p] //=.
rewrite !Pr_code_put !bind_assoc (Pr_code_fst (prog_valid dPfx))
  (Pr_code_fst (prog_valid dPfx)) !dfst_dlet_commut.
apply eq_dlet => r.
rewrite Pr_code_get.
match goal with
| |- context [Pr_code (?f ?A ?B ?c ?k) ?h] =>
  change (Pr_code (f A B c k) h) with (Pr_code (bind c k) h) end.
rewrite bind_assoc (Pr_code_fst (prog_valid dR)) dfst_dlet_commut.
under eq_dlet do rewrite Pr_code_put Pr_code_ret dmarginE dlet_unit_ext /=.
by rewrite (Pr_fstC hr) Pr_code_ret dmarginE dlet_unit_ext.
Qed.

End ROGuards.

Lemma ro_test_query_no_setup (x : chFin 3 × 'nat) (answer : bool) :
  AdvOf ROPlusTest.test_game
    (guard_calls (QUERY, (chFin 3 × 'nat, 'bool)) x 1 answer) = 0%R.
Proof. exact: ro_query_no_setup. Qed.

Lemma ro_test_query_over_budget (x : chFin 3 × 'nat) (answer : bool) :
  AdvOf ROPlusTest.test_game
    (guard_calls (QUERY, (chFin 3 × 'nat, 'bool)) x 6 answer) = 0%R.
Proof. exact: ro_query_over_budget. Qed.

Lemma ro_test_repro_no_setup (x : nat) (answer : bool) :
  AdvOf ROPlusTest.test_game
    (guard_calls (REPRO, ('nat, chFin 3)) x 1 answer) = 0%R.
Proof. apply: ro_repro_no_setup. Qed.

Lemma ro_test_repro_over_budget (x : nat) (answer : bool) :
  AdvOf ROPlusTest.test_game
    (guard_calls (REPRO, ('nat, chFin 3)) x 2 answer) = 0%R.
Proof. exact: ro_repro_over_budget. Qed.
