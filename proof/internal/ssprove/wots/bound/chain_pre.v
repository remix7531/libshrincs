(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.bound.chain_pre

    The chain-preimage game-hop equality, peeled out of [Shrincs.internal.ssprove.wots.theorem]
    for parallel type-checking (see [Shrincs.internal.ssprove.wots.bound.grind]).

    States that the [G_post_chain -> G_forge_uniformchains false] advantage
    equals the SM-PRE advantage of the chain-preimage reduction
    [R_chain_pre] (ChainHop's [R_chain_pre_real] / [R_chain_pre_ideal]). *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.wots Require Import params scheme games analysis
  hop.chain_pre.
From mathcomp Require Import reals.


Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section ThmChainPRE.

Context (P : wc_params).
Context (A : nom_package).
(* [Adv_perfect_l/r] resolve the adversary's [ValidPackage] by typeclass
   inference; it must be in scope here as it was in the Theorem section. *)
Context (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A).

(** [G_post_chain ~ G_forge_uniformchains false] is the chain-preimage reduction's perfect hop. *)
Lemma cpre_hop_eq :
  Adv (intermediates.G_post_chain P) (G_forge_uniformchains P false) A
    = AdvOf (SMPRE_game (thf_hash P) (wcp_chain_class P) (wcp_chain_count P)) (A ∘ R_chain_pre P).
Proof.
rewrite (Adv_perfect_l (R_chain_pre_real P)).
rewrite (Adv_perfect_r (R_chain_pre_ideal P)).
by rewrite Adv_reduction.
Qed.

End ThmChainPRE.
