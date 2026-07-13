(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Assumption audit (model tree)

    [Print Assumptions] for the shared pure-model surface: the ground-truth
    correctness theorem [Model.correct.wots.wots_correct] and the pure
    combinatorial core (chain extraction, target-sum/checksum encoding)
    that both proof trees' reductions rest on.  assumptions/check.sh's
    model gate 3 compiles this file, extracts the axiom names, and diffs
    them against the `[model]` section of
    assumptions/allowed.txt: the build fails if any theorem
    here depends on an axiom outside that frozen baseline (expected: only
    [sha256.SHA256] -- the model is a Stdlib-only development
    parameterized by the SHA-256 function, so no classical axioms should
    appear).

    The model tree is the shared trust ROOT: both the ssprove security
    proof and the vst C-refinement proof state their claims against it,
    so its cone is audited first and must stay minimal.

    Siblings: assumptions/ssprove.v (the Sec headline theorems, diffed
    against `[ssprove]`) and assumptions/vst.v (the VST body proofs,
    diffed against `[vst]`).  All three are excluded from the default
    build (see _RocqProject's trailing comment); `make audit` / check.sh
    recompiles them standalone. *)

From Model Require Import math.chain math.encoding correct.wots.

Set Printing Width 4000.

(* Pure combinatorial core used by the chain reductions. *)
Print Assumptions chain.chain_extractP.        (* chain collision / preimage extraction *)
Print Assumptions encoding.eq_sumn_exists_lt.  (* WOTS+C target-sum lemma *)
Print Assumptions encoding.checksum_exists_lt. (* checksum domination (proves EC's two_encodings axiom) *)

(* The Stdlib-only ground-truth correctness theorem: [shrincs_wots_verify]
   accepts any signature [shrincs_wots_sign] produces against the matching
   [shrincs_wots_pubkey_gen]. Depends on nothing but the model itself --
   no VST, no CompCert, no classical axioms expected here. *)
Print Assumptions Model.correct.wots.wots_correct.
