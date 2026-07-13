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

From Vst Require Export theory.pure.
From Vst Require Export contract.lemmas.data_at.
From Vst Require Export tactics.slot.
From Vst Require Export contract.lemmas.cancel_hints.
From Vst Require Export contract.lemmas.byte_ok.
From Vst Require Export contract.lemmas.lengths.
From Vst Require Export contract.lemmas.arith.
From Vst Require Export tactics.adrs_store.
From Vst Require Export contract.lemmas.chain_blocks.
From Vst Require Export contract.lemmas.shrincs_wots_verify.
