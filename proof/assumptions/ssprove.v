(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Assumption audit (ssprove tree)

    [Print Assumptions] for the Sec headline theorems and the games<->model
    bridge, plus a baseline probe.  assumptions/check.sh's ssprove gate 3
    compiles this file, extracts the axiom names, and diffs them against
    the `[ssprove]` section of assumptions/allowed.txt: the build
    fails if any theorem here depends on an axiom outside the classical
    baseline PLUS the 6 named hash-game assumptions from
    Sec.axioms.

    [shrincs_wots_secure]/[shrincs_wots_secure_ideal_sk]/
    [shrincs_wots_secure_shrincs] are unconditional over their abstract
    F/T_sf/H_grind/PRF Context: none of the hash assumptions (PRF, SM-TCR,
    SM-PRE, SM-UD, STCRP) is an axiom for THEM -- each is an explicit
    [AdvOf] term in their statement, never assumed.  Only
    [shrincs_wots_secure_sha256] (Sec.axioms's connection of
    the abstract theorem to the concrete truncated-SHA256 construction)
    depends on the 6 hash-game axioms, by design -- this file's job is
    to confirm they're the ONLY axioms it depends on beyond the
    classical baseline (no undeclared hash assumption sneaking in
    through a different route).

    Siblings: assumptions/model.v (the shared pure-model surface,
    including the combinatorial core these reductions rest on, diffed
    against `[model]`) and assumptions/vst.v (the VST body proofs,
    diffed against `[vst]`).  All three are excluded from the default
    build (see _RocqProject's trailing comment); `make audit` / check.sh
    recompiles them standalone. *)

From Sec.lib Require Import prelude.

Set Printing Width 4000.

(* Baseline probe: the nominal-layer triangle inequality exercises the
   real-number/probability stack and thus SSProve's classical axioms. *)
Print Assumptions Adv_triangle.

(* Pure spec-contract bridge (Sec.bridge): Model.wots's byte
   nibble-splitting vs this repo's LSB-first digits_w. *)
Require Import Sec.bridge.
Print Assumptions Sec.bridge.base_2b_digits_w.
Print Assumptions Sec.bridge.digest_of_bridge.

(* The headline result: one-time (known-message) security of keyed
   WOTS+C (chain starts PRF-derived), and its ideal-key stepping
   theorem. *)
Require Import Sec.wots.theorem.
Print Assumptions Sec.wots.theorem.shrincs_wots_secure.
Print Assumptions Sec.wots.theorem.shrincs_wots_secure_ideal_sk.

(* The same two headlines, restated over the STANDARD known-message
   valid-commit notion KOTS_vc_game (Sec.lib.sig.kots), via the
   unconditional perfect links in Sec.wots.kots_link -- must depend on
   exactly the same axiom cone as the two probes above. *)
Print Assumptions Sec.wots.theorem.shrincs_wots_secure_kots.
Print Assumptions Sec.wots.theorem.shrincs_wots_secure_kots_ideal_sk.

(* The headline at the spec's parameters (w = 16, chain_count = 32,
   constant_sum = 240, c_max = 2^16, 16-byte values): the side
   conditions are discharged, so the bound is non-vacuous. *)
Require Import Sec.wots.instantiation.
Print Assumptions Sec.wots.instantiation.shrincs_wots_secure_shrincs.

(* The concrete truncated-SHA256 construction, unconditional modulo
   the 6 named hash-game axioms (Sec.axioms). *)
Require Import Sec.axioms.
Print Assumptions Sec.axioms.shrincs_wots_secure_sha256.

(* Same corollary, over KOTS_vc_game -- must depend on exactly the
   classical baseline plus the same 6 named hash-game axioms. *)
Print Assumptions Sec.axioms.shrincs_wots_secure_kots_sha256.

(* The games<->model machine link (Sec.wots.model_bridge): the headline
   functional-correspondence lemmas -- keyed pubkey, grinding counter,
   verification, and signing -- proving the games scheme computes the
   same thing as the model of record, Model.shrincs (the port of the
   normative Python spec), at the concrete truncated-SHA256
   instantiation.  These are PURE equalities, NOT security claims:
   their cones must stay within the classical baseline plus
   sha256.SHA256 (the SHA-256 function), and must NOT touch any of the
   6 hash-game axioms -- the correspondence is unconditional. *)
Require Import Sec.wots.model_bridge.
Print Assumptions Sec.wots.model_bridge.pubkey_gen_modelE.
Print Assumptions Sec.wots.model_bridge.find_counter_modelE.
Print Assumptions Sec.wots.model_bridge.verify_modelE.
Print Assumptions Sec.wots.model_bridge.sign_modelE.
