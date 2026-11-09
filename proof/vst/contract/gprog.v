(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.gprog: the full [Gprog] funspec bundle.
    Combines [contract.trusted] (the SHA-256 contract)
    with [contract.helpers] (internal WOTS+ specs proved in [proof/vst/verif])
    and [contract.public] (the public API specs).

    The internal helpers are partitioned into [Gprog_libc] / [Gprog_thash] /
    [Gprog_wots], one segment per C translation unit ([include/util.h]'s
    libc shims, the shared tweakable-hash TU [src/thash.c], and the
    WOTS+C-specific TU [src/wots.c]).  The partition changes nothing
    semantically -- [find_id] is order-insensitive for the distinct names
    here -- but keeps the segments reusable on their own: the planned FXMSS
    driver can assemble its own [Gprog] as [Gprog_libc ++ Gprog_thash ++
    ...] without dragging in the WOTS-specific [Gprog_wots]. *)

From VST Require Export floyd.proofauto.
From Vst Require Export contract.trusted contract.public contract.helpers.

Open Scope Z_scope.

(** ** Per-translation-unit funspec segments. *)

(** [include/util.h]'s in-tree libc alternatives. *)
Definition Gprog_libc : funspecs :=
  [ shrincs_memset_spec;
    shrincs_memcpy_spec;
    shrincs_ct_memcmp_spec;
    shrincs_panic_spec ].

(** The shared tweakable-hash TU, [src/thash.c]. *)
Definition Gprog_thash : funspecs :=
  [ shrincs_adrs_put32_spec;
    shrincs_thash_spec ].

(** The WOTS+C-specific internal step functions, [src/wots.c]. *)
Definition Gprog_wots : funspecs :=
  [ shrincs_wots_t_sf_spec;
    shrincs_wots_h_grind_spec;
    shrincs_wots_derive_sk_spec;
    shrincs_wots_chain_iter_spec;
    shrincs_wots_chain_from_seed_spec;
    shrincs_wots_map_digest_spec;
    shrincs_wots_grind_to_constant_sum_spec ].

(** Full program funspec bundle -- sha256, libc, thash, wots helpers, then
    public API. *)
Definition Gprog : funspecs :=
  sha256_spec ::
  Gprog_libc ++ Gprog_thash ++ Gprog_wots ++
  [ shrincs_wots_pubkey_gen_spec;
    shrincs_wots_sign_spec;
    shrincs_wots_pubkey_from_sig_spec;
    shrincs_wots_verify_spec ].

(** [body_sha256] is not verified here -- by design. [src/sha256.c] is a
    direct FIPS 180-4 port verified elsewhere, so we axiomatise the C
    function via [sha256_spec] rather than proving the body against our
    own model of SHA-256. The trusted surface is exactly this axiom plus
    the [SHA256] parameter in [model.wots] (the length/range guarantees
    once carried separately by [SHA256_length]/[SHA256_byte_ok] are now
    intrinsic to the [byte]/[vec] types, so those lemmas no longer
    exist). *)
Axiom body_sha256 : semax_body Vprog Gprog f_shrincs_sha256 sha256_spec.
