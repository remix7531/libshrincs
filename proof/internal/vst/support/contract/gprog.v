(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.gprog: the full [Gprog] funspec bundle.
    Combines [contract.trusted] (the SHA-256 contract -- the sha256
    translation unit's own, see that file's header) with
    [contract.helpers] (internal WOTS+ specs proved in [proof/internal/vst])
    and [contract.public] (the public API specs).

    The internal helpers are partitioned into [Gprog_sha] / [Gprog_libc] /
    [Gprog_thash] / [Gprog_wots], one segment per C translation unit
    ([src/sha256.c], [include/util.h]'s libc shims, the shared
    tweakable-hash TU [src/thash.c], and the WOTS+C-specific TU
    [src/wots.c]).  The partition changes nothing semantically --
    [find_id] is order-insensitive for the distinct names here -- but
    keeps the segments reusable on their own: the planned FXMSS driver
    can assemble its own [Gprog] as [Gprog_libc ++ Gprog_thash ++ ...]
    without dragging in the WOTS-specific [Gprog_wots].

    [Gprog_sha] IS [Shrincs.internal.vst.sha256.contract]'s, verbatim -- all
    twelve funspecs of [src/sha256.c], not just the one
    [shrincs_sha256] a caller can name. The eleven private ones are
    here for a single reason: [body_sha256] below moves the sha256
    unit's own body proof into THIS proof context, and a context can
    only grow ([tycontext_sub]), so every funspec that proof was done
    against has to be present. They are unreachable from [src/wots.c]
    (all eleven are [static] in the C -- see
    [Shrincs.internal.vst.sha256.vsu]'s [sha256_public_idents]), so no
    [forward_call] anywhere in [proof/internal/vst] can resolve to one. *)

From VST Require Export floyd.proofauto.

(** [Import]/[Require]-only, and before the [Export]s: the sha256
    unit's funspec bundle and its body proof are needed to STATE and
    PROVE [body_sha256] below, and reach no further. (The body proof's
    own name is [body_sha256] too, hence the qualified reference.) *)
From Shrincs.internal.vst.sha256 Require Import contract.
From Shrincs.internal.vst.sha256.verif Require sha256.

From Shrincs.internal.vst.support Require Export contract.trusted contract.public contract.helpers.

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
  Gprog_sha ++ Gprog_libc ++ Gprog_thash ++ Gprog_wots ++
  [ shrincs_wots_pubkey_gen_spec;
    shrincs_wots_sign_spec;
    shrincs_wots_pubkey_from_sig_spec;
    shrincs_wots_verify_spec ].

(* ================================================================= *)
(** ** [src/sha256.c]'s body proof, moved into this context.

    [Shrincs.internal.vst.sha256.verif.sha256]'s [body_sha256] proves
    [shrincs_sha256] against [spec_sha256] in the sha256 unit's OWN
    proof context ([Vprog_sha]/[Gprog_sha]). The only step needed here
    is context subsumption: [Gprog] extends [Gprog_sha] on the left, so
    every funspec the body proof could call resolves to the same
    funspec it was proved against, and [Vprog_sha] and [Vprog] are both
    empty (neither translation unit has a global). Nothing about
    SHA-256 is assumed: this is the C body proof, re-stated. *)

Lemma tycontext_sub_sha256 :
  tycontext_sub (func_tycontext f_shrincs_sha256 Vprog_sha Gprog_sha nil)
                (func_tycontext f_shrincs_sha256 Vprog Gprog nil).
Proof.
unfold Gprog.
apply tycontext_sub_Gprog_app1.
- apply compute_list_norepet_e. reflexivity.
- apply compute_list_norepet_e. reflexivity.
Qed.

Lemma body_sha256 : semax_body Vprog Gprog f_shrincs_sha256 sha256_spec.
Proof.
apply (semax_body_subsumption _ Vprog_sha Vprog Gprog_sha Gprog _ _
         Shrincs.internal.vst.sha256.verif.sha256.body_sha256 tycontext_sub_sha256).
Qed.
