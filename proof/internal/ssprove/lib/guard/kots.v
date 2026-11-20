(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.kots

    Protocol-abort guards for [KOTS_game]. All calls use fixed
    arguments and ignore the reply. The setup/commit call has a one-call budget;
    two attempts exercise that budget, including refusal paths. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.

Import PackageNotation kots.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (S : sig_scheme).

Lemma kots_vc_commit_no_setup (sp : SParam S) (m : Msg S) (answer : bool) :
  AdvOf (KOTS_vc_game S)
    (guard_calls (COMMIT, (SParam S × Msg S, Pk S × 'option (Sig S))) (sp, m) 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma kots_vc_commit_over_budget (sp : SParam S) (m : Msg S) (answer : bool) :
  AdvOf (KOTS_vc_game S)
    (guard_calls (COMMIT, (SParam S × Msg S, Pk S × 'option (Sig S))) (sp, m) 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma kots_vc_kforge_no_setup (m : Msg S) (sig : Sig S)
    (answer : bool) :
  AdvOf (KOTS_vc_game S)
    (guard_calls (KFORGE, (Msg S × Sig S, 'bool))
      (m, sig) 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /=.
Qed.

Lemma kots_vc_commit_phase_abort (b : bool) (sp : SParam S)
    (m : Msg S) (pk : Pk S) (h : heap) :
  get_heap h (kots_pk_loc S) = Some pk ->
  Pr_code (resolve (KOTS_vc_game S b)
    (COMMIT, (SParam S × Msg S, Pk S × 'option (Sig S))) (sp, m)) h =
    Pr_code fail h.
Proof.
move=> hpk.
simplify_linking.
by rewrite Pr_code_get hpk /=.
Qed.

End Guards.
