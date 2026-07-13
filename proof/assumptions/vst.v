(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Assumption audit (vst tree)

    [Print Assumptions] for the vst-side proved surface: the 4 public API
    body proofs and the aggregate [all_bodies]
    (proof/vst/verif/all_bodies.v) that conjoins all 18 [semax_body]
    facts (17 proved + [body_sha256]).  assumptions/check.sh's vst gate 3
    compiles this file, strips the CompCert/VST "Fetching opaque proofs
    from disk" progress lines (NOT assumptions -- see the KNOWN TRAP note
    in check.sh's header), extracts the axiom names from what remains,
    and diffs them against the `[vst]` section of
    assumptions/allowed.txt: the build fails if any theorem here
    depends on an axiom outside that frozen baseline (the classical
    CompCert/Flocq stack plus the 2 named trust anchors
    [SHA256]/[body_sha256]; the [machine.v] Module-Type fields
    [wordsize]/[wordsize_not_zero] are discharged at instantiation and
    never appear in a cone -- they are covered by check.sh's model
    gate 2 source scan instead).

    Siblings: assumptions/model.v (the shared pure-model surface,
    including [Model.correct.wots.wots_correct], diffed against `[model]`) and
    assumptions/ssprove.v (the Sec headline theorems, diffed
    against `[ssprove]`): same structure (baseline probe, then the
    headline theorems, widest printing), same exclusion from the default
    build (see _RocqProject's trailing comment) so this
    ~axiom-fetch-heavy compile only runs when the audit gate asks for
    it. *)

From Vst Require Import verif.body_shrincs_wots_pubkey_gen.
From Vst Require Import verif.body_shrincs_wots_sign.
From Vst Require Import verif.body_shrincs_wots_pubkey_from_sig.
From Vst Require Import verif.body_shrincs_wots_verify.
From Vst Require Import verif.all_bodies.

Set Printing Width 4000.

(* The 4 public API C body proofs, individually -- each a
   [semax_body Vprog Gprog f_<fn> <fn>_spec] against the VST/CompCert
   program logic, hence pulling in the classical CompCert/Flocq baseline
   plus the 2 trust anchors ([SHA256]/[body_sha256]). *)
Print Assumptions body_shrincs_wots_pubkey_gen.
Print Assumptions body_shrincs_wots_sign.
Print Assumptions body_shrincs_wots_pubkey_from_sig.
Print Assumptions body_shrincs_wots_verify.

(* The aggregate: all 18 conjuncts (17 proved [semax_body]s + the
   [body_sha256] axiom) in one theorem, so this single probe covers the
   WHOLE proved VST surface -- see all_bodies.v's header for why an
   enumeration aggregate is used here instead of one [semax_prog] link
   step (VSU over a single TU would re-axiomatize the proved cross-TU
   externals). *)
Print Assumptions all_bodies.
