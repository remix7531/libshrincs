(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.bound.grind

    The grinding game-hop equality, peeled out of [Shrincs.internal.ssprove.wots.theorem] so it
    type-checks in parallel with the other hop-equalities (the final
    assembly's [Adv_perfect_l/r] rewrites over the full game terms are
    the build's long pole; separate files enable parallel builds).

    States that the [G_forge_uniformchains true -> G_post_grind] advantage
    equals the STCRP advantage of the grinding reduction [R_grind]
    (GrindHop's [R_grind_real] / [R_grind_ideal]). *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.wots Require Import params scheme games analysis
  hop.grind.
From mathcomp Require Import reals.


Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section ThmGrind.

Context (P : wc_params).
Context (A : nom_package).
(* [Adv_perfect_l/r] resolve the adversary's [ValidPackage] by typeclass
   inference; it must be in scope here as it was in the Theorem section. *)
Context (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A).

(** [G_forge_uniformchains true ~ G_post_grind] is the grinding reduction's perfect hop. *)
Lemma grind_hop_eq :
  Adv (G_forge_uniformchains P true) (intermediates.G_post_grind P) A
    = AdvOf (STCRP_game (thf_hash P) (wcp_grind_class P) (wcp_M P) (grind_enc P) (grind_prp P) (wcp_c_max P) 1)
            (A ∘ R_grind P).
Proof.
rewrite (Adv_perfect_l (R_grind_real P)).
rewrite (Adv_perfect_r (R_grind_ideal P)).
by rewrite Adv_reduction.
Qed.

End ThmGrind.
