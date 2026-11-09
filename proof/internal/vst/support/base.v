(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.base: the root of the VST tier

    THE FILE EVERY OTHER vst/ FILE IMPORTS FIRST, and the reason it
    must be first is the import-order trap: floyd's notations and the
    mathcomp surface clash unless floyd arrives first, so anything
    needing both Imports this file before [mathcomp]. It carries the
    three things that have to be established before any of that:
    floyd itself, the [compspecs] the whole tier elaborates against,
    and the name-hygiene note explaining what the merged stack shadows.

    ONE THING THIS FILE IS NOT: free of [wots.c]. It Exports
    Vst.clight.wots, because [CompSpecs] has to be built from some
    program and all three Clight programs (sha256.c, thash.c, wots.c)
    have the same empty composite environment:
    Vst.sha256.vsu's [compspecs_agree] says so by [reflexivity].
    The SHA-256 proofs and [Vst.contract.repr] both export this
    instance, so contracts and callers use the same constant.

    [Vst.repr] supplies the
    mathcomp-seq to stdlib-list dictionary in [repr.seqlist], the
    32-byte word codec, the [tarray tuchar] surgery and the funspec
    notations in [repr.words]. *)

From VST Require Export floyd.proofauto.
From Vst Require Export clight.wots.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Model Require Export bytes.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

(* ================================================================= *)
(** ** Name hygiene under the merged import stack

    Three Stdlib names are shadowed by the mathcomp surface and are
    therefore spelled qualified throughout this file:

    - [val]  -- mathcomp's [eqtype.val] (the subtype projection) hides
      CompCert's [Values.val]. Spelled [Values.val].
    - [map]  -- mathcomp's [seq.map] hides [List.map]. The two are
      extensionally the same function but NOT the same constant, and
      every VST list lemma ([Zlength_map], [Znth_map], [sublist_map],
      ...) is stated about [List.map]. Spelled [List.map] in the
      definitions.
    - [nth]  -- mathcomp's [seq.nth] hides [List.nth] (and takes its
      arguments in a different order). [nth_seq_list] is the bridge.
    - [int]  -- mathcomp's [ssrint.int] hides CompCert's machine
      integers. Spelled [Int.int].

    None of this reaches the notations at the bottom of the file, so
    the funspec surface is unaffected. *)
