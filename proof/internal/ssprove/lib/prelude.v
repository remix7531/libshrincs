(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.lib.prelude

    Common imports, notations and settings for the library
    (hash-based signatures in SSProve).

    Every file with SSProve content starts with [From Shrincs.internal.ssprove.lib Require
    Import prelude.]; pure-math files import only the
    MathComp prefix and must not depend on SSProve.

    This file doubles as a smoke test: it checks that the SSProve
    classic layer (AdvantageE, triangle inequality) and the nominal
    layer (Adv, Pr', perfect, hybrid machinery) are available from the
    devshell-installed ssprove package. *)

From mathcomp Require Export boot order algebra.

From Stdlib Require Export Utf8.
From extructures Require Export ord fset fmap.

From Equations Require Export Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve.Crypt Require Export NominalPrelude TotalProbability HybridArgument.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Smoke checks: fail at compile time if the expected SSProve surface
   moved. *)
(* Referenced silently (no [Check] output): nominal advantage, success
   probability, perfect indistinguishability, game-hop chaining, classic-layer
   advantage.  Fails here if any moved. *)
Local Definition _ssprove_surface :=
  (@Adv, @Pr', @perfect, @Adv_triangle, @AdvantageE).

(** An adversary valid against the middle interface [M], composed with
    a reduction [R : package I M], is a valid adversary against [I] --
    [valid_sep_link_weak] at the reduction's own bundled validity.
    The discharge lemma for validity-scoped hardness assumptions
    (Shrincs.games): each application site is one
    [valid_adv_link VA _]. *)
Lemma valid_adv_link {I M : Interface} {A : nom_package} {R : package I M}
    (VA : ValidPackage (loc A) M A_export A) :
  ValidPackage (loc (A ∘ R)%sep) I A_export (A ∘ R)%sep.
Proof.
eapply valid_sep_link_weak.
- exact: VA.
- exact: (pack_valid R).
- exact: fsubmapxx.
Qed.
