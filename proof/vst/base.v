(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.base: shared VST imports and composite environment.

    Floyd must be imported before the MathComp surface because their
    notations otherwise clash. All three Clight programs have the same
    empty composite environment. Contracts share the instance built
    from the WOTS+C program. *)

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
