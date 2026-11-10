(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.util.component: src/util.c as a Verified Software Unit

    The three body proofs of [proof/internal/vst/util/body_shrincs_{memset,
    memcpy,panic}.v], assembled into ONE object:

        VSU  Externs=nil  Imports=nil  util_QP
             Exports=util_ASI  InitPred=emp

    IMPORTS ARE nil, AND THAT IS THE POINT OF THE FILE EXISTING.
    [src/util.c] is the in-tree replacement for the two libc
    functions the rest of libshrincs needs, written in C precisely so
    that nothing in the library is assumed rather than proved. It calls
    nothing, so it is the leaf of the link DAG and the one unit whose
    import-freedom is a fact about the C rather than a result of
    linking.

    THE INTERFACE IS ALL THREE. Unlike [src/sha256.c] and [src/wots.c],
    [util.c] has no [static]: every function it defines is part of its
    interface, so [util_ASI] is [G_util] and there is nothing to
    privatise here. What makes the shims invisible to a CLIENT of the
    library is [Shrincs.internal.vst.link]'s [privatizeExports], one level up.

    [shrincs_panic] IS EXPORTED THOUGH NOTHING CALLS IT: its funspec
    (contract.helpers.helpers_libc) has [PROP (False)] as its precondition, so
    the export is a promise no caller can cash. No [SHRINCS_ASSERT]
    site is left in [src/], which is why [_shrincs_panic] does not even
    appear in the wots or thash ASTs -- this unit is where the symbol
    lives.

    THE INIT PREDICATE IS [emp]: [util.c] has no globals, so the unit
    claims no part of the initial memory. *)

From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.internal.vst.util Require Import body_shrincs_memset.
From Shrincs.internal.vst.util Require Import body_shrincs_memcpy.
From Shrincs.internal.vst.util Require Import body_shrincs_panic.
From VST.floyd Require Import VSU.

(** LAST, so the bare [prog] below is [util.c]'s and not the [wots.c]
    one [contract.gprog] re-exports through [support.base]. *)
From Shrincs.clight Require Import util.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope logic.

(* ================================================================= *)
(** ** The unit and its interface *)

(** The Clight AST of [src/util.c] in VSU's "quick program" form.
    [QPprog] normalises against the AMBIENT compspecs, [Shrincs.internal.vst.support.base]'s;
    all four of libshrincs' translation units have an EMPTY composite
    environment, so that is the same object as this unit's own --
    [Shrincs.internal.vst.sha256.vsu]'s [compspecs_agree] states the fact by
    [reflexivity] and it is what keeps the cross-unit [data_at]
    reconciliation out of [Shrincs.internal.vst.link]. *)
Definition util_QP : QP.program Clight.function := ltac:(QPprog prog).

(** Everything [util.c] defines, since [util.c] hides nothing. *)
Definition util_ASI : funspecs := G_util.

(* ================================================================= *)
(** ** The component *)

Definition UtilVSU :
  @VSU NullExtension.Espec nil nil util_QP util_ASI emp.
Proof.
mkVSU prog G_util.
+ solve_SF_internal body_shrincs_memset.
+ solve_SF_internal body_shrincs_memcpy.
+ solve_SF_internal body_shrincs_panic.
Qed.

(* ================================================================= *)
(** ** Reviewability: what a reader can check by inspection *)

(** (a) The interface is the three shims. *)
Lemma util_ASI_idents :
  map fst util_ASI
  = [_shrincs_memset; _shrincs_memcpy; _shrincs_panic].
Proof. reflexivity. Qed.

(** (b) The C agrees that all three are public: [util.c] has no [static],
    so the AST's own [public_idents] contains every function this unit's
    spec list names. Nothing is private here. *)
Lemma util_public_idents :
  List.filter (fun i => id_in_list i (map fst util_ASI)) public_idents
  = [_shrincs_panic; _shrincs_memset; _shrincs_memcpy].
Proof. reflexivity. Qed.

(** (c) The unit's proof context is LITERALLY the [Gprog] the three body
    proofs were done against: [mkVSU] justifies each body in
    [Imports ++ G], and here [Imports] is [nil]. *)
Lemma util_context_is_Gprog : nil ++ G_util = Gprog_util.
Proof. reflexivity. Qed.
