(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * verif.all_bodies: the LINKING SURROGATE aggregate theorem.

    [Gprog] (contract/gprog.v) bundles 18 funspecs sourced from THREE
    separately-clightgen'd translation units: [src/wots.c]
    (clight/wots.v -- 15 internal functions: the 4 libc shims, the 7
    WOTS+C-specific step functions, and the 4 public entry points), the
    shared tweakable-hash TU [src/thash.c] (clight/thash.v -- 2 functions,
    [shrincs_adrs_put32]/[shrincs_thash]), and [src/sha256.c]
    (clight/sha256.v -- 1 function, [shrincs_sha256], deliberately NOT
    proved: [body_sha256] is the one [Axiom], in contract/gprog.v).  Each
    of the 17 non-axiomatized funspecs is discharged by its own
    [semax_body Vprog Gprog f_<fn> <fn>_spec] lemma, one per
    [proof/vst/verif/body_*.v] file.

    This file conjoins all 18 into ONE theorem, [all_bodies], so a single
    [Print Assumptions all_bodies] (see proof/assumptions/vst.v)
    audits the WHOLE proved surface in one probe instead of 17 separate
    ones that could silently miss a body if the verif/ directory listing
    ever drifts from [_RocqProject] or [Gprog].  [gprog_covered] is the
    tie-back that makes such drift compile-time-visible: it proves
    [map fst Gprog] is EXACTLY these 18 idents, in this order, by
    [reflexivity] -- so a funspec added to (or removed from) [Gprog]
    without a matching change here fails the build, rather than silently
    shrinking what the audit gate covers.

    TU note (verified, not papered over): [Vprog]/[Gprog] are built in
    contract/public.v over [clight.wots]'s composite environment
    ([CompSpecs]/[Vprog] via [make_compspecs prog]/[mk_varspecs prog] with
    [prog] = [clight.wots.prog]).  The two thash-TU body lemmas
    ([body_shrincs_thash], [body_shrincs_adrs_put32]) state their
    [semax_body] against that SAME [Vprog]/[Gprog] but need [clight.thash]
    imported (below) for their [f_shrincs_thash]/[f_shrincs_adrs_put32]
    function values, which [Gprog]'s own import chain does not pull in
    (only [contract.helpers_thash]'s funspecs, not [clight.thash]'s
    function bodies).  This is not a mismatch: [clightgen -normalize]
    string-keys every identifier ([$"shrincs_thash"] etc.), so the SAME
    ident is used across all three separately-generated TUs, and
    [semax_body] itself only needs [f_<fn>] and the funspec's [DECLARE]
    ident to agree -- not that both come from one [prog]. This is the same
    pattern contract/trusted.v already relies on ([_shrincs_sha256]
    resolves identically whether reached via [clight.sha256] or
    transitively via [clight.wots]). The one visible consequence: several
    idents below ([_shrincs_thash], [_shrincs_adrs_put32],
    [_shrincs_memcpy], [_shrincs_memset], [_shrincs_sha256]) are declared
    in more than one of the three clight files now in scope; Rocq resolves
    the bare name to whichever declaration was imported last (no
    ambiguity error), and since every declaration of a given ident reduces
    to the identical string-keyed value, [gprog_covered]'s [reflexivity]
    goes through regardless of which one is picked.

    WHY NOT VSU / [semax_prog]: [wots.c] calls [shrincs_thash] /
    [shrincs_adrs_put32] (defined in [thash.c]) and [shrincs_memcpy] /
    [shrincs_memset] / [shrincs_sha256] (also cross-TU) as External
    functions.  A plain [semax_prog] over any ONE TU's Clight AST would
    have to re-axiomatize every cross-TU callee's funspec as an assumed
    "External" spec -- silently reintroducing exactly the trust surface
    this repo has kept down to just [SHA256] + [body_sha256] (see
    contract/trusted.v's header).  The enumeration aggregate below is a
    deliberate substitute for that missing link step: every conjunct is
    an already-proved [semax_body] (or the one named axiom), so
    [all_bodies] adds no new trust -- it just packages the existing 17
    Qed's (+ 1 axiom) into one theorem for the audit gate to probe. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import clight.thash.

From Vst Require Import verif.body_shrincs_memset.
From Vst Require Import verif.body_shrincs_memcpy.
From Vst Require Import verif.body_shrincs_ct_memcmp.
From Vst Require Import verif.body_shrincs_panic.
From Vst Require Import verif.body_shrincs_adrs_put32.
From Vst Require Import verif.body_shrincs_thash.
From Vst Require Import verif.body_shrincs_wots_t_sf.
From Vst Require Import verif.body_shrincs_wots_h_grind.
From Vst Require Import verif.body_shrincs_wots_derive_sk.
From Vst Require Import verif.body_shrincs_wots_chain_iter.
From Vst Require Import verif.body_shrincs_wots_chain_from_seed.
From Vst Require Import verif.body_shrincs_wots_map_digest.
From Vst Require Import verif.body_shrincs_wots_grind_to_constant_sum.
From Vst Require Import verif.body_shrincs_wots_pubkey_gen.
From Vst Require Import verif.body_shrincs_wots_sign.
From Vst Require Import verif.body_shrincs_wots_pubkey_from_sig.
From Vst Require Import verif.body_shrincs_wots_verify.

(* ================================================================= *)
(** ** Completeness: [Gprog] has exactly these 18 idents, in this order.
    A funspec silently added to (or dropped from) [Gprog] without a
    matching edit here breaks this [reflexivity] -- so the audit gate
    below can never silently shrink. *)
Lemma gprog_covered : map fst Gprog =
  [ _shrincs_sha256;
    _shrincs_memset; _shrincs_memcpy; _shrincs_ct_memcmp; _shrincs_panic;
    _shrincs_adrs_put32; _shrincs_thash;
    _shrincs_wots_t_sf; _shrincs_wots_h_grind; _shrincs_wots_derive_sk;
    _shrincs_wots_chain_iter; _shrincs_wots_chain_from_seed;
    _shrincs_wots_map_digest; _shrincs_wots_grind_to_constant_sum;
    _shrincs_wots_pubkey_gen; _shrincs_wots_sign;
    _shrincs_wots_pubkey_from_sig; _shrincs_wots_verify ].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** The aggregate: all 18 conjuncts, grouped by translation unit
    (mirroring [Gprog]'s own [Gprog_libc]/[Gprog_thash]/[Gprog_wots]
    partition in contract/gprog.v). Every conjunct is discharged by
    [exact] on an already-[Qed]'d lemma (or the one named [Axiom]) --
    this theorem proves nothing new. *)
Theorem all_bodies :
  (* src/sha256.c -- axiomatized, not proved here (contract/gprog.v). *)
  semax_body Vprog Gprog f_shrincs_sha256 sha256_spec /\
  (* src/wots.c -- libc shims. *)
  semax_body Vprog Gprog f_shrincs_memset shrincs_memset_spec /\
  semax_body Vprog Gprog f_shrincs_memcpy shrincs_memcpy_spec /\
  semax_body Vprog Gprog f_shrincs_ct_memcmp shrincs_ct_memcmp_spec /\
  semax_body Vprog Gprog f_shrincs_panic shrincs_panic_spec /\
  (* src/thash.c -- shared tweakable-hash TU. *)
  semax_body Vprog Gprog f_shrincs_adrs_put32 shrincs_adrs_put32_spec /\
  semax_body Vprog Gprog f_shrincs_thash shrincs_thash_spec /\
  (* src/wots.c -- WOTS+C-specific internal step functions. *)
  semax_body Vprog Gprog f_shrincs_wots_t_sf shrincs_wots_t_sf_spec /\
  semax_body Vprog Gprog f_shrincs_wots_h_grind shrincs_wots_h_grind_spec /\
  semax_body Vprog Gprog f_shrincs_wots_derive_sk shrincs_wots_derive_sk_spec /\
  semax_body Vprog Gprog f_shrincs_wots_chain_iter shrincs_wots_chain_iter_spec /\
  semax_body Vprog Gprog f_shrincs_wots_chain_from_seed shrincs_wots_chain_from_seed_spec /\
  semax_body Vprog Gprog f_shrincs_wots_map_digest shrincs_wots_map_digest_spec /\
  semax_body Vprog Gprog f_shrincs_wots_grind_to_constant_sum shrincs_wots_grind_to_constant_sum_spec /\
  (* src/wots.c -- public API. *)
  semax_body Vprog Gprog f_shrincs_wots_pubkey_gen shrincs_wots_pubkey_gen_spec /\
  semax_body Vprog Gprog f_shrincs_wots_sign shrincs_wots_sign_spec /\
  semax_body Vprog Gprog f_shrincs_wots_pubkey_from_sig shrincs_wots_pubkey_from_sig_spec /\
  semax_body Vprog Gprog f_shrincs_wots_verify shrincs_wots_verify_spec.
(* NOT [repeat split.]: [semax_body] itself unfolds to a multi-way [/\]
   (funsig-agreement / no-duplicate-vars / var-sizes / callconv side
   conditions, plus the actual [semax] judgment as the last conjunct), so
   [repeat split] does not stop at these 18 top-level conjuncts -- it keeps
   unfolding EACH [semax_body ...] leaf into its own internal pieces too,
   desynchronizing a flat list of 18 bulleted [exact body_<fn>]'s from the
   actual (much longer) goal list; the symptom is a confusing
   "has type semax_body ... while it is expected to have type
   forall Espec : OracleKind, ..." on the FIRST bullet, because that
   bullet's goal is already a fragment of [body_sha256]'s statement, not
   the whole thing. Building the proof term directly with nested [conj]
   splits only the 18 conjuncts written in THIS theorem's statement,
   without descending into any [semax_body]'s own definition. *)
Proof.
  exact
  (conj body_sha256
    (conj body_shrincs_memset
      (conj body_shrincs_memcpy
        (conj body_shrincs_ct_memcmp
          (conj body_shrincs_panic
            (conj body_shrincs_adrs_put32
              (conj body_shrincs_thash
                (conj body_shrincs_wots_t_sf
                  (conj body_shrincs_wots_h_grind
                    (conj body_shrincs_wots_derive_sk
                      (conj body_shrincs_wots_chain_iter
                        (conj body_shrincs_wots_chain_from_seed
                          (conj body_shrincs_wots_map_digest
                            (conj body_shrincs_wots_grind_to_constant_sum
                              (conj body_shrincs_wots_pubkey_gen
                                (conj body_shrincs_wots_sign
                                  (conj body_shrincs_wots_pubkey_from_sig
                                    body_shrincs_wots_verify))))))))))))))))).
Qed.
