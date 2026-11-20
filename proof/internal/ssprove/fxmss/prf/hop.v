(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.hop

    The real and ideal simulations give the exact chain-start and message-
    randomizer PRF hops. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.prf_memo toolkit.hop_tactics.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance prf.inputs prf.reduction prf.keys_ideal prf.keys_real
  prf.message_memo prf.message_ideal prf.message_real.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF hop *)

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma R_prf_ideal (Q : shrincs_fxmss_resources) (bit : bool) :
  perfect I_forge (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)
    (R_prf Q bit ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false).
Proof.
rewrite /R_prf.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ prf_ideal_inv).
-
  change (Invariant (loc (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)) (unionm
    (unionm (loc
    (R_prf_memo Q
    bit)) (loc (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q))))
      (loc (prf.PRF_game
    shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false))) prf_ideal_inv).
  rewrite -unionmA.
  exact: prf_ideal_inv_invariant.
-
  intros id S T arg has.
  fmap_invert has.
  +
    exact: R_prf_ideal_gen.
  +
    exact: R_prf_ideal_sign.
  +
    exact: R_prf_ideal_hash.
  +
    exact: R_prf_ideal_forge.
Qed.

Lemma R_prf_real (Q : shrincs_fxmss_resources) (bit : bool) :
  perfect I_forge (G_forge_keyed shrincs_fxmss_sha256 Q bit)
    (R_prf Q bit ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true).
Proof.
rewrite /R_prf.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ prf_real_inv).
-
  change (Invariant (loc (G_forge_keyed shrincs_fxmss_sha256 Q bit)) (unionm (unionm
    (loc
    (R_prf_memo Q
    bit)) (loc (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q))))
      (loc (prf.PRF_game
    shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true))) prf_real_inv).
  rewrite -unionmA.
  exact: prf_real_inv_invariant.
-
  intros id S T arg has.
  fmap_invert has.
  +
    exact: R_prf_real_gen.
  +
    exact: R_prf_real_sign.
  +
    exact: R_prf_real_hash.
  +
    exact: R_prf_real_forge.
Qed.

Lemma prf_key_advantage (Q : shrincs_fxmss_resources) (bit : bool) (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_forge_keyed shrincs_fxmss_sha256 Q bit) (G_forge_sampledkey
    shrincs_fxmss_sha256 Q bit) A =
  Adv (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_leaf_capacity Q *
    wots_c_chain_count).+1 true)
      (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_leaf_capacity Q *
        wots_c_chain_count).+1 false)
      (A ∘ R_prf Q bit).
Proof.
rewrite (Adv_perfect_l (R_prf_real Q bit)) (Adv_perfect_r (R_prf_ideal Q bit)).
by rewrite Adv_reduction.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Message PRF hop *)

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma R_prf_msg_ideal (Q : shrincs_fxmss_resources) (bit : bool) :
  perfect I_forge (G_forge_randomized shrincs_fxmss_sha256 Q bit)
    (R_prf_msg Q bit ∘ prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q)
      false).
Proof.
rewrite /R_prf_msg.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ prf_msg_ideal_inv).
-
  change (Invariant (loc (G_forge_randomized shrincs_fxmss_sha256 Q bit)) (unionm
    (unionm (loc
    (R_prf_msg_memo Q
    bit)) (loc (prf_memo.R_prf_memo shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg
      Q)))) (loc (prf.PRF_game
    shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) false))) prf_msg_ideal_inv).
  rewrite -unionmA.
  exact: prf_msg_ideal_inv_invariant.
-
  intros id S T arg has.
  fmap_invert has.
  +
    exact: R_prf_msg_ideal_gen.
  +
    exact: R_prf_msg_ideal_sign.
  +
    exact: R_prf_msg_ideal_hash.
  +
    exact: R_prf_msg_ideal_forge.
Qed.

Lemma R_prf_msg_real (Q : shrincs_fxmss_resources) (bit : bool) :
  perfect I_forge (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)
    (R_prf_msg Q bit ∘ prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q)
      true).
Proof.
rewrite /R_prf_msg.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ prf_msg_real_inv).
-
  change (Invariant (loc (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)) (unionm
    (unionm (loc
    (R_prf_msg_memo Q
    bit)) (loc (prf_memo.R_prf_memo shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg
      Q)))) (loc (prf.PRF_game
    shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) true))) prf_msg_real_inv).
  rewrite -unionmA.
  exact: prf_msg_real_inv_invariant.
-
  intros id S T arg has.
  fmap_invert has.
  +
    exact: R_prf_msg_real_gen.
  +
    exact: R_prf_msg_real_sign.
  +
    exact: R_prf_msg_real_hash.
  +
    exact: R_prf_msg_real_forge.
Qed.

Lemma prf_msg_advantage (Q : shrincs_fxmss_resources) (bit : bool) (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (G_forge_randomized
    shrincs_fxmss_sha256 Q bit) A =
  Adv (prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_sign_budget Q).+1 true)
      (prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_sign_budget Q).+1 false)
      (A ∘ R_prf_msg Q bit).
Proof.
rewrite (Adv_perfect_l (R_prf_msg_real Q bit)) (Adv_perfect_r (R_prf_msg_ideal Q
  bit)).
by rewrite Adv_reduction.
Qed.
