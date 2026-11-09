(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.helpers: aggregates the internal helper funspec modules.

    Re-exports the in-tree libc alternatives ([contract.helpers_libc]), the
    shared tweakable-hash funspecs ([contract.helpers_thash], backing
    [src/thash.c]) and the WOTS+C step funspecs ([contract.helpers_wots],
    backing [src/wots.c]) -- one module per C translation unit, so each
    reads independently; every funspec is unchanged.  [contract.gprog]
    partitions these same funspecs into [Gprog_libc] / [Gprog_thash] /
    [Gprog_wots] and assembles the full program [Gprog]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Export contract.helpers_libc.
From Shrincs.internal.vst.support Require Export contract.helpers_thash.
From Shrincs.internal.vst.support Require Export contract.helpers_wots.
