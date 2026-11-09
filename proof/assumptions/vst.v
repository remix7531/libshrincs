(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Assumption audit (vst tree)

    [Print Assumptions] for the vst-side proved surface: the 4 public API
    body proofs and the aggregate [all_bodies]
    (proof/internal/vst/all_bodies.v) that conjoins all 18 [semax_body]
    facts -- all 18 PROVED, [body_sha256] included (it is a Lemma in
    contract/gprog.v now, from src/sha256.c's own VST body proof).
    The [sha256_c_correct] component probe additionally covers every
    private SHA-256 helper body.
    assumptions/check.sh's vst gate 3 compiles this file, strips the
    CompCert/VST "Fetching opaque proofs from disk" progress lines (NOT
    assumptions -- see the KNOWN TRAP note in check.sh's header),
    extracts the axiom names from what remains, and diffs them against
    the `[vst]` section of assumptions/allowed.txt: the build fails if
    any theorem here depends on an axiom outside that frozen baseline --
    which is now the classical CompCert/Flocq stack and NOTHING ELSE, no
    named anchor of this repository's own. (The [machine.v] Module-Type
    fields [wordsize]/[wordsize_not_zero] are discharged at
    instantiation and never appear in a cone -- they are covered by
    check.sh's model gate 2 source scan instead.)

    Siblings: assumptions/model.v (the shared pure-model surface,
    including [Shrincs.internal.common.correct.wots.wots_correct], diffed against `[model]`) and
    assumptions/ssprove.v (the Sec headline theorems, diffed
    against `[ssprove]`): same structure (baseline probe, then the
    headline theorems, widest printing), same exclusion from the default
    build (see _RocqProject's trailing comment) so this
    ~axiom-fetch-heavy compile only runs when the audit gate asks for
    it. *)

From Shrincs.internal.vst.wots Require Import body_shrincs_wots_pubkey_gen.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_sign.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_pubkey_from_sig.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_verify.
From Shrincs.internal.vst Require Import all_bodies.
From Shrincs.internal.vst.sha256 Require Import correct.

Set Printing Width 4000.

(* The 4 public API C body proofs, individually -- each a
   [semax_body Vprog Gprog f_<fn> <fn>_spec] against the VST/CompCert
   program logic, hence pulling in the classical CompCert/Flocq baseline
   -- and, since [Parameter SHA256] and [Axiom body_sha256] are both
   gone, nothing else. *)
Print Assumptions body_shrincs_wots_pubkey_gen.
Print Assumptions body_shrincs_wots_sign.
Print Assumptions body_shrincs_wots_pubkey_from_sig.
Print Assumptions body_shrincs_wots_verify.

(* The aggregate covers the WOTS+C body proofs and the exported SHA-256
   body transferred to their context.
   See all_bodies.v's header for why an
   enumeration aggregate is used here instead of one [semax_prog] link
   step (VSU over a single TU would re-axiomatize the proved cross-TU
   externals). *)
Print Assumptions all_bodies.

(* The component proof also checks every private SHA-256 helper body. *)
Print Assumptions sha256_c_correct.
