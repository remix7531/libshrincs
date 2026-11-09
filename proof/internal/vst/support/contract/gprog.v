(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.gprog: one proof context per translation unit.

    Combines [contract.trusted] (the SHA-256 contract -- the sha256
    translation unit's own, see that file's header) with
    [contract.helpers] (the internal step funspecs proved in
    [proof/internal/vst]) and [contract.public] (the public API specs),
    and cuts the result into ONE [Gprog] PER C SOURCE FILE.

    THE CUT IS THE COMPONENT STRUCTURE, not a convenience. libshrincs is
    four translation units -- [src/util.c], [src/sha256.c],
    [src/thash.c], [src/wots.c] -- and each is verified as its own VSU
    ([internal/vst/*/component.v], [internal/vst/sha256/vsu.v]) before [internal/vst/link.v] joins them.
    VST's [mkVSU] puts every body-proof obligation of a unit in the
    context [Imports ++ G]: the funspecs the unit ASSUMES about the
    functions it calls but does not define, followed by the funspecs of
    the functions it DOES define. So each [Gprog_<tu>] below is spelled
    exactly that way, and each body proof states its
    [semax_body] against its own unit's -- which is what lets [mkVSU]
    accept the body proof unchanged.

    WHAT A UNIT MAY IMPORT is a DAG with no cycles, and reading the
    three [Imports_*] lists top to bottom is reading it:
    [util] imports nothing; [sha256] imports nothing (its own
    [Gprog_sha] lives in [Shrincs.internal.vst.sha256.contract]); [thash] imports
    the two shims and the hash; [wots] imports three shims, the hash and
    thash.c's two. No unit imports a function of a unit downstream of
    it, so [internal/vst/link.v] can discharge every import by linking, and the
    linked whole imports nothing.

    THE PUBLIC ENTRY POINTS ARE IN [G_wots], not in a segment of their
    own: [src/wots.c] defines all eleven of the functions it names --
    the seven [static] step functions AND the four public ones -- so all
    eleven are that unit's [G]. Which four are the INTERFACE is said by
    [Shrincs.internal.vst.wots.component]'s Exports slot, not here. *)

From VST Require Export floyd.proofauto.

From Shrincs.internal.vst.support Require Export contract.trusted contract.public contract.helpers.

Open Scope Z_scope.

(* ================================================================= *)
(** ** [src/util.c] -- the in-tree libc alternatives.

    The leaf of the DAG: [util.c] calls nothing, so its Imports are
    [nil] and its context is its own four funspecs. *)

Definition G_util : funspecs :=
  [ shrincs_memset_spec;
    shrincs_memcpy_spec;
    shrincs_ct_memcmp_spec;
    shrincs_panic_spec ].

Definition Gprog_util : funspecs := G_util.

(* ================================================================= *)
(** ** [src/thash.c] -- the shared tweakable hash.

    [shrincs_thash] calls [shrincs_memset], [shrincs_memcpy] and
    [shrincs_sha256] (src/thash.c:40-46); [shrincs_adrs_put32] calls
    nothing. *)

Definition Imports_thash : funspecs :=
  [ shrincs_memset_spec;
    shrincs_memcpy_spec;
    sha256_spec ].

Definition G_thash : funspecs :=
  [ shrincs_adrs_put32_spec;
    shrincs_thash_spec ].

Definition Gprog_thash : funspecs := Imports_thash ++ G_thash.

(* ================================================================= *)
(** ** [src/wots.c] -- WOTS+C.

    Six imports: three of [util.c]'s four shims ([shrincs_panic] is not
    among them -- no [SHRINCS_ASSERT] site is left in the C, so the
    symbol does not even appear in this unit's AST), [shrincs_sha256]
    (called directly from [shrincs_wots_h_grind], not only through
    [shrincs_thash]) and both of [thash.c]'s functions. *)

Definition Imports_wots : funspecs :=
  [ shrincs_memset_spec;
    shrincs_memcpy_spec;
    shrincs_ct_memcmp_spec;
    sha256_spec;
    shrincs_adrs_put32_spec;
    shrincs_thash_spec ].

(** All eleven functions [src/wots.c] defines: the seven [static] step
    functions, then the four public entry points. *)
Definition G_wots : funspecs :=
  [ shrincs_wots_t_sf_spec;
    shrincs_wots_h_grind_spec;
    shrincs_wots_derive_sk_spec;
    shrincs_wots_chain_iter_spec;
    shrincs_wots_chain_from_seed_spec;
    shrincs_wots_map_digest_spec;
    shrincs_wots_grind_to_constant_sum_spec;
    shrincs_wots_pubkey_gen_spec;
    shrincs_wots_sign_spec;
    shrincs_wots_pubkey_from_sig_spec;
    shrincs_wots_verify_spec ].

Definition Gprog_wots : funspecs := Imports_wots ++ G_wots.
