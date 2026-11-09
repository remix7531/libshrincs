(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.bound.prf

    The PRF game-hop equality, in its own file like the other
    per-hop advantage bounds (Shrincs.internal.ssprove.bound.grind), so it type-checks
    in parallel with them.

    States that the [G_forge_keyed -> G_forge_sampledkey] advantage (at either KOTS bit b)
    equals the PRF advantage of the derivation reduction [R_prf]
    (hop.prf's [R_prf_real] / [R_prf_ideal]). *)

From Shrincs.internal.ssprove.lib Require Import prelude games.thf games.prf sig.scheme sig.kots.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import params scheme games hop.prf.
From mathcomp Require Import reals.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section ThmPrf.

Context (P : wc_params).
Context (K : choice_type).
Context (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P).
Context (dK : dist K).
Context (A : nom_package).
(* [Adv_perfect_l/r] resolve the adversary's [ValidPackage] by typeclass
   inference; it must be in scope here as it was in the Theorem section. *)
Context (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A).

(** [G_forge_keyed ~ G_forge_sampledkey] is the derivation reduction's perfect hop (at either
    KOTS bit). *)
Lemma prf_hop_eq (b : bool) :
  Adv (G_forge_keyed P K PRF dK b) (G_forge_sampledkey P b) A
    = AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK b).
Proof.
rewrite (Adv_perfect_l (R_prf_real P K PRF dK b)).
rewrite (Adv_perfect_r (R_prf_ideal P K PRF dK b)).
by rewrite Adv_reduction.
Qed.

End ThmPrf.
