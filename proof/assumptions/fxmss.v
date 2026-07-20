(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Assumption audit for FXMSS

    [Print Assumptions] for the headline EU-CMA theorem in [proof/fxmss]
    (logical name [SHRINCS.fxmss]; see [fxmss/README.md]).

    [shrincs_fxmss_secure] is admit-free and unconditional over its abstract
    F/T_l/H_grind/H_tree/PRF Context: none of the hash assumptions is an axiom
    FOR IT -- each per-primitive term (PRF, reprogramming, digest, grind, the
    leaf/tree SM-TCR, TCRX) is an explicit advantage/[AdvOf] term in the bound,
    never assumed.  Its axiom cone must therefore stay within the
    classical/SSProve baseline already listed in the `[ssprove]` section of
    assumptions/allowed.txt (propositional/functional extensionality,
    indefinite description, strict-Prop proof irrelevance, the real-number
    carrier, and mathcomp-analysis's realsum.__admitted__interchange_psum) --
    with NO new axiom, parameter, or trust anchor.

    Like assumptions/{model,ssprove,vst}.v, this probe is excluded from the
    default build (not in _RocqProject) and compiled by `make audit` / check.sh
    gate 3.  FXMSS is checked against the existing `[ssprove]` baseline, so no
    `[fxmss]` allowlist section or additional trust anchor is needed.  To review
    the cone manually, compile this file standalone against the project's -Q
    maps, e.g. from proof/:
      rocq c $(rocq makefile -f _RocqProject -o /dev/null; echo) assumptions/fxmss.v
    or simply `coqc` with the four `-Q` maps from _RocqProject. *)

From SHRINCS Require Import fxmss.theorem.

Set Printing Width 4000.

Print Assumptions SHRINCS.fxmss.theorem.shrincs_fxmss_secure.
