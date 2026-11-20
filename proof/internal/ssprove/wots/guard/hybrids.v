(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.wots.guard.hybrids

    Protocol-abort guards for the existing WOTS+C hybrids. Intermediate
    games are compared to the ideal uniform-chain game, whose commit
    body agrees and whose forgery check has the same initial abort. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.wots Require Import params scheme games
  hop.intermediates hop.prf hop.ud.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (P : wc_params).

Lemma sampledkey_commit_no_setup
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_sampledkey P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sampledkey_commit_over_budget
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_sampledkey P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sampledkey_forge_no_setup
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_sampledkey P)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

Lemma uniformchains_commit_no_setup
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_uniformchains P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma uniformchains_commit_over_budget
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_uniformchains P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma uniformchains_forge_no_setup
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_uniformchains P)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

Lemma keyed_commit_no_setup (K : choice_type) (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P)
    (dK : dist K)
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_keyed P K PRF dK)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma keyed_commit_over_budget (K : choice_type) (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P)
    (dK : dist K)
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_keyed P K PRF dK)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma keyed_forge_no_setup (K : choice_type) (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P)
    (dK : dist K)
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (G_forge_keyed P K PRF dK)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

Lemma ud_hybrid_forge_no_setup (s : nat)
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf (HGw P s)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

Lemma grind_commit_no_setup
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_grind P else G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma grind_commit_over_budget
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_grind P else G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma grind_forge_no_setup
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_grind P else G_forge_uniformchains P false))
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

Lemma compress_commit_no_setup
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_compress P else G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma compress_commit_over_budget
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_compress P else G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma compress_forge_no_setup
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_compress P else G_forge_uniformchains P false))
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

Lemma chain_commit_no_setup
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_chain P else G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma chain_commit_over_budget
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_chain P else G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma chain_forge_no_setup
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool) :
  AdvOf ((fun b => if b then G_post_chain P else G_forge_uniformchains P false))
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [m sig].
by rewrite !Pr_code_get /=.
Qed.

End Guards.
