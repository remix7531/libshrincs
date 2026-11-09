(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Assumption audit of the public bodies and linked C component.

    The linked component covers every translation unit and discharges
    their imports. Its assumption cone must stay within the VST library
    baseline in assumptions/allowed.txt. *)

From Shrincs.internal.vst.wots Require Import body_shrincs_wots_pubkey_gen.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_sign.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_pubkey_from_sig.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_verify.
From Shrincs.internal.vst Require Import link.
From Shrincs.internal.vst.sha256 Require Import correct.

Set Printing Width 4000.

Print Assumptions body_shrincs_wots_pubkey_gen.
Print Assumptions body_shrincs_wots_sign.
Print Assumptions body_shrincs_wots_pubkey_from_sig.
Print Assumptions body_shrincs_wots_verify.
Print Assumptions link.shrincs_c_vsu.
Print Assumptions sha256_c_correct.
