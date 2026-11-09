(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.bound.chain_tcr

    The chain target-collision game-hop equality, peeled out of
    [Shrincs.internal.ssprove.theorem] for parallel type-checking (see
    [Shrincs.internal.ssprove.bound.grind]).

    States that the [G_post_compress -> G_post_chain] advantage equals the SM-TCR
    advantage of the chain-TCR reduction [R_chain_tcr] (ChainHop's
    [R_chain_tcr_real] / [R_chain_tcr_ideal]). *)

From Shrincs.internal.ssprove.lib Require Import prelude games.smtcr sig.scheme sig.kots.
From Shrincs.internal.ssprove.lib Require Import chain.core.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import params scheme games analysis
  hop.compress hop.chain_tcr.
From mathcomp Require Import reals.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section ThmChainTCR.

Context (P : wc_params).
Context (A : nom_package).
(* [Adv_perfect_l/r] resolve the adversary's [ValidPackage] by typeclass
   inference; it must be in scope here as it was in the Theorem section. *)
Context (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A).

(** [G_post_compress ~ G_post_chain] is the chain-TCR reduction's perfect hop. *)
Lemma ctcr_hop_eq :
  Adv (intermediates.G_post_compress P) (intermediates.G_post_chain P) A
    = AdvOf (SMTCR_game (thf_chain P) (coll_chain P) (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P).
Proof.
rewrite (Adv_perfect_l (R_chain_tcr_real P)).
rewrite (Adv_perfect_r (R_chain_tcr_ideal P)).
by rewrite Adv_reduction.
Qed.

End ThmChainTCR.
