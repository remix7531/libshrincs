(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.link: the four components linked, importing nothing

    libshrincs' C is four translation units and four Verified Software
    Units: [Shrincs.internal.vst.util.component] ([src/util.c], imports nothing),
    [Shrincs.internal.vst.sha256.vsu] ([src/sha256.c], imports nothing),
    [Shrincs.internal.vst.thash.component] ([src/thash.c], imports three) and
    [Shrincs.internal.vst.wots.component] ([src/wots.c], imports six). This file joins
    them and packages the result. The Imports slot of what comes out is
    [nil]: nothing is assumed about any function the program calls,
    because the linked program defines them all.

    THAT nil IS THE WHOLE CONTENT OF THE FILE. Every cross-unit callee
    -- the three libc shims, SHA-256, the tweakable hash and its ADRS
    writer -- appears in exactly one unit as [Gfun (Internal _)] with a
    [semax_body] behind it, and in the units that call it as
    [Gfun (External _)] with a funspec assumed. [linkVSUs] subtracts
    one side's Exports from the other's Imports; nine subtractions
    later there is nothing left to assume.

    THE LINK IS CHEAP, and the reason is a decision in the C rather
    than a trick here: all four translation units have an EMPTY
    composite environment (no [struct] crosses -- or exists at -- a
    unit boundary), so their compspecs are the same object and the
    cross-unit [data_at] reconciliation that normally dominates
    [linkVSUs] does not arise. [Shrincs.internal.vst.sha256.vsu]'s
    [compspecs_agree] says so by [reflexivity].

    EVERY IMPORT DISCHARGE IS [funspec_sub_refl], not a subsumption
    step, and that is by construction: an importing unit and the
    exporting unit name the SAME funspec definition -- [Gprog_thash]'s
    [shrincs_memcpy_spec] IS [G_util]'s (contract.helpers_libc holds the
    one copy), and [Imports_wots]'s [sha256_spec] IS
    [Shrincs.internal.vst.sha256.contract]'s [spec_sha256] (contract.trusted
    defines it as that term). A specialised import would be a different
    funspec and each discharge would need a [funspec_sub] proof in
    place of the [reflexivity].

    THE INIT PREDICATE IS [emp]. No translation unit has a global, so
    the linked unit claims no part of the initial memory. [linkVSUs]
    hands back the components' predicates side by side, so three links
    produce [((emp * emp) * emp) * emp]; [VSU_ext] collapses that. *)

From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.internal.vst.util Require Import component.
From Shrincs.internal.vst.thash Require Import component.
From Shrincs.internal.vst.wots Require Import component.
From Shrincs.internal.vst.sha256 Require Import vsu.
From VST.floyd Require Import VSU.

(** For [_shrincs_panic]: [src/wots.c] has no [SHRINCS_ASSERT] site, so
    the symbol appears in no AST but [util.c]'s. *)
From Shrincs.clight Require Import util.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope logic.

(* ================================================================= *)
(** ** The link, one unit at a time

    In dependency order, so each step's Imports are already among the
    accumulated Exports: the two import-free units first, then the
    tweakable hash, then WOTS+C. *)

(** [src/util.c] + [src/sha256.c]. Neither imports anything, so this
    step discharges nothing -- it exists to put the five contracts the
    two upper units need into one Exports slot. *)
Definition UtilSha256VSU := ltac:(linkVSUs UtilVSU Sha256VSU).

(** ... + [src/thash.c]. Discharges [Imports_thash]: [shrincs_memset]
    and [shrincs_memcpy] against the util unit, [shrincs_sha256]
    against the sha256 unit. *)
Definition HashesVSU := ltac:(linkVSUs UtilSha256VSU ThashVSU).

(** ... + [src/wots.c]. Discharges [Imports_wots], all six. Imports
    come out [nil]. *)
Definition LinkedVSU := ltac:(linkVSUs HashesVSU WotsVSU).

(** The linked Clight program: all four C sources as one module,
    derived from the four ASTs clightgen produces on every build. *)
Definition shrincs_QP : QP.program Clight.function := VSU_prog LinkedVSU.

(* ================================================================= *)
(** ** The import-free whole

    Exports are the four contracts [include/wots.h] declares -- the
    WOTS+C key generation, signing, public-key recovery and
    verification -- and NOTHING ELSE. The seven other verified
    functions are privatised here: they are still verified and still
    exported by their own units, which is where a client wanting one of
    them looks, but THIS object is the WOTS+C claim, and a hash
    contract in its Exports slot would be a promise about a different
    interface. *)

(** The idents privatised at this boundary: [util.c]'s four shims,
    SHA-256, and [thash.c]'s two. Every one is verified; none is part
    of the library's interface. *)
Definition shrincs_private_idents : list ident :=
  [ _shrincs_memset; _shrincs_memcpy; _shrincs_ct_memcmp; _shrincs_panic;
    _shrincs_sha256; _shrincs_adrs_put32; _shrincs_thash ].

Theorem shrincs_c_vsu :
  @VSU NullExtension.Espec nil nil shrincs_QP
       (* parenthesised: an [@]-application argument is parsed at level 0,
          where the multi-element list notation is not available *)
       ([ shrincs_wots_pubkey_gen_spec;
          shrincs_wots_sign_spec;
          shrincs_wots_pubkey_from_sig_spec;
          shrincs_wots_verify_spec ])
       emp.
Proof.
apply (VSU_ext (privatizeExports LinkedVSU shrincs_private_idents)).
(* every component claims nothing, and [emp * emp] is [emp] *)
extensionality gv.
rewrite !sepcon_emp.
reflexivity.
Qed.

(* ================================================================= *)
(** ** Reviewability: what a reader can check by inspection *)

(** (a) The exported contracts are the four public entry points, and
    they are [Shrincs.internal.vst.wots.component]'s interface unchanged -- the link
    weakened nothing. *)
Lemma shrincs_exports_idents :
  map fst wots_ASI
  = [_shrincs_wots_pubkey_gen; _shrincs_wots_sign;
     _shrincs_wots_pubkey_from_sig; _shrincs_wots_verify].
Proof. reflexivity. Qed.

(** (b) [privatizeExports] removed exactly the seven above and kept
    exactly the four: the filter, computed. *)
Lemma shrincs_privatize_exact :
  privatize_ids shrincs_private_idents (VSU_Exports LinkedVSU) = wots_ASI.
Proof. reflexivity. Qed.

(** (c) The linked program defines twenty-nine functions -- [util.c]'s
    four, [sha256.c]'s twelve, [thash.c]'s two and [wots.c]'s eleven --
    and every one of them has a [semax_body] behind it, because
    [Component]'s [Comp_G_justified] carries an [SF] obligation per
    internal function and [linkVSUs] cannot produce this object without
    all of them.

    THIS IS THE DRIFT GUARD. A function added to any of the four C
    sources and left unverified does not shrink what the audit covers:
    it makes this count wrong, and -- because [mkVSU]'s [Comp_G_dom]
    demands that a unit's spec list be EXACTLY its AST's internal
    functions -- it stops that unit's component from being built at
    all. *)
Lemma shrincs_internal_count :
  Datatypes.length (internalFunctions shrincs_QP) = 29%nat.
Proof. reflexivity. Qed.
