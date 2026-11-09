(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas: aggregator for the focused bridge modules.

    Historical single-file entry point. Actual lemmas live in the
    [contract.lemmas.*] modules; this file just re-exports them so
    downstream code keeps working with
    [From Vst Require Import contract.lemmas.]. *)

From Shrincs.internal.vst.support Require Export theory.pure.
From Shrincs.internal.vst.support Require Export contract.lemmas.data_at.
From Shrincs.internal.vst.support Require Export tactics.slot.
From Shrincs.internal.vst.support Require Export contract.lemmas.cancel_hints.
From Shrincs.internal.vst.support Require Export contract.lemmas.byte_ok.
From Shrincs.internal.vst.support Require Export contract.lemmas.lengths.
From Shrincs.internal.vst.support Require Export contract.lemmas.arith.
From Shrincs.internal.vst.support Require Export tactics.adrs_store.
From Shrincs.internal.vst.support Require Export contract.lemmas.chain_blocks.
From Shrincs.internal.vst.support Require Export contract.lemmas.shrincs_wots_verify.
