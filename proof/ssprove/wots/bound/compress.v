(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.bound.compress

    The compression game-hop equality, peeled out of [Sec.theorem]
    for parallel type-checking (see [Sec.bound.grind] for the
    rationale).

    States that the [G_post_grind -> G_post_compress] advantage equals the SM-TCR
    advantage of the compression reduction [R_compress] (CompressHop's
    [R_compress_real] / [R_compress_ideal]). *)

From Sec.lib Require Import prelude games.smtcr sig.scheme sig.kots.
From Sec Require Import addressing.
From Sec.wots Require Import params scheme games analysis
  hop.grind hop.compress.
From mathcomp Require Import reals.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section ThmCompress.

Context (P : wc_params).
Context (A : nom_package).
(* [Adv_perfect_l/r] resolve the adversary's [ValidPackage] by typeclass
   inference; it must be in scope here as it was in the Theorem section. *)
Context (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A).

(** [G_post_grind ~ G_post_compress] is the compression reduction's perfect hop. *)
Lemma compress_hop_eq :
  Adv (intermediates.G_post_grind P) (intermediates.G_post_compress P) A
    = AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P).
Proof.
rewrite (Adv_perfect_l (R_compress_real P)).
rewrite (Adv_perfect_r (R_compress_ideal P)).
by rewrite Adv_reduction.
Qed.

End ThmCompress.
