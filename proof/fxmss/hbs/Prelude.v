(** * HBS.Prelude

    Common imports, notations and settings for the HBS library
    (hash-based signatures in SSProve).

    Every HBS file with SSProve content starts with [From HBS Require
    Import Prelude.]; pure-math files under HBS.Math import only the
    MathComp prefix and must not depend on SSProve.

    This file doubles as the P0 smoke test: it checks that the SSProve
    classic layer (AdvantageE, triangle inequality) and the nominal
    layer (Adv, Pr', perfect, hybrid machinery) are available from the
    devshell-installed ssprove package. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Export all_ssreflect all_algebra.
Set Warnings "notation-overridden,ambiguous-paths".
Unset SsrOldRewriteGoalsOrder. (* remove the line when requiring MathComp >= 2.6 *)

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
Check @Adv.           (* nominal advantage *)
Check @Pr'.           (* nominal success probability *)
Check @perfect.       (* perfect indistinguishability *)
Check @Adv_triangle.  (* game-hop chaining *)
Check @AdvantageE.    (* classic-layer advantage *)
