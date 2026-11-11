(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.thash.component: src/thash.c as a Verified Software Unit

    The two body proofs of [proof/internal/vst/thash/body_shrincs_thash.v] and
    [body_shrincs_adrs_pack.v], assembled into ONE object:

        VSU  Externs=nil  Imports=Imports_thash  thash_QP
             Exports=thash_ASI  InitPred=emp

    THREE IMPORTS, AND EACH IS A CALL IN THE C. [shrincs_thash] fills
    its 598-byte staging buffer from the left: [pk_seed] with
    [shrincs_memcpy], the 48 zero bytes with [shrincs_memset], [addr]
    and [msg] with two more [shrincs_memcpy]s. It hashes the result
    with [shrincs_sha256] and copies the leading 16 bytes out with a
    fourth [shrincs_memcpy]. All
    three callees are defined in OTHER translation units, so this
    unit's AST has them as [Gfun (External _)] and a VSU over that AST
    can only IMPORT their contracts. [Shrincs.internal.vst.link] discharges all
    three by linking against [Shrincs.internal.vst.util.component]'s and
    [Shrincs.internal.vst.sha256.vsu]'s components.

    THE INTERFACE IS BOTH FUNCTIONS. [src/thash.h] declares
    [shrincs_thash] and [shrincs_adrs_pack] alike, and neither is
    [static] in the C: this is the SHARED tweakable-hash layer, kept in
    its own translation unit so the coming FXMSS/FORS sources link
    against the same verified object rather than re-deriving it. Which
    of the two a CLIENT of libshrincs can see is decided one level up,
    by [Shrincs.internal.vst.link]'s [privatizeExports].

    THE INIT PREDICATE IS [emp]: [thash.c] has no globals -- the
    staging buffer is a function local -- so the unit claims no part of
    the initial memory. *)

From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.internal.vst.thash Require Import body_shrincs_adrs_pack.
From Shrincs.internal.vst.thash Require Import body_shrincs_thash.
From VST.floyd Require Import VSU.

(** LAST, so the bare [prog] below is [thash.c]'s and not the [wots.c]
    one [contract.gprog] re-exports through [support.base]. *)
From Shrincs.clight Require Import thash.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope logic.

(* ================================================================= *)
(** ** The unit and its interface *)

(** The Clight AST of [src/thash.c] in VSU's "quick program" form; see
    [Shrincs.internal.vst.util.component]'s note on why normalising against the
    ambient compspecs is sound for every unit here. *)
Definition thash_QP : QP.program Clight.function := ltac:(QPprog prog).

(** Both functions [src/thash.h] declares. *)
Definition thash_ASI : funspecs := G_thash.

(* ================================================================= *)
(** ** The component *)

Definition ThashVSU :
  @VSU NullExtension.Espec nil Imports_thash thash_QP thash_ASI emp.
Proof.
mkVSU prog G_thash.
+ solve_SF_internal body_shrincs_adrs_pack.
+ solve_SF_internal body_shrincs_thash.
Qed.

(* ================================================================= *)
(** ** Reviewability: what a reader can check by inspection *)

(** (a) The interface is the tweakable hash and its address serializer. *)
Lemma thash_ASI_idents :
  map fst thash_ASI = [_shrincs_adrs_pack; _shrincs_thash].
Proof. reflexivity. Qed.

(** (b) What the unit assumes: three contracts, for the three functions
    [src/thash.c] calls and does not define. *)
Lemma thash_imports_idents :
  map fst Imports_thash
  = [_shrincs_memset; _shrincs_memcpy; _shrincs_sha256].
Proof. reflexivity. Qed.

(** (c) The C agrees: of the two functions [src/thash.c] defines, the
    AST marks both public -- so "interface" here is not a choice this
    proof made, it is what the translation unit already says. *)
Lemma thash_public_idents :
  List.filter (fun i => id_in_list i (map fst thash_ASI)) public_idents
  = [_shrincs_thash; _shrincs_adrs_pack].
Proof. reflexivity. Qed.

(** (d) The unit's proof context is LITERALLY the [Gprog] the two body
    proofs were done against. *)
Lemma thash_context_is_Gprog : Imports_thash ++ G_thash = Gprog_thash.
Proof. reflexivity. Qed.
