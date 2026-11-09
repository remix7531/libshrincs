(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * wots.model.wots: re-export shim for the shared model.

    Re-exports the pure WOTS+C model from [proof/internal/common/wots.v] --
    definitions, supporting lemmas ([model.theory.wots],
    [model.theory.address]), and notation -- so every [From wots
    Require Import/Export model.wots.] line in this tree keeps
    resolving.

    [PRF]'s argument order is [pk_seed -> ADRS -> sk_seed], matching
    [F] / [T_sf] / [H_grind]. *)

From Shrincs.internal.common Require Export wots theory.address theory.wots.
