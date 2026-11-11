(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_vsu: src/sha256.c as a Verified Software Unit

    The twelve [semax_body] proofs of this directory, assembled into
    ONE object: the sha256 translation unit is a verified component
    that imports nothing, claims no globals, and exports exactly the
    one function src/sha256.h declares.

        VSU  Externs=nil  Imports=nil  sha256_QP
             Exports=[spec_sha256]  InitPred=emp

    THE INTERFACE IS ONE FUNCTION. [sha256_ASI] lists [sha256] and
    nothing else, so the other eleven -- the six logical functions of
    SS 4.1.2, the two byte-order primitives, [sha256_parse],
    [sha256_compress_words] and [sha256_compress_blocks] -- are private
    to the unit: proved, carried in the component's internal spec list,
    and invisible to a client. That is the VSU-level counterpart of
    their [static] in the C, and [sha256_public_idents] below checks
    the two statements agree by [reflexivity] against the AST's own
    [public_idents].

    Imports are [nil] because src/sha256.c calls only its own helpers.

    THE INIT PREDICATE IS [emp], and it is why the exported contract is
    a function of its bytes alone. src/sha256.c has NO globals: K
    (SS 4.2.2) and H^(0) (SS 5.3.3) are function locals, so the
    component claims no part of the initial memory and no client has to
    carry the round constants of a hash. Shrincs.internal.vst.sha256.tables
    has the argument for writing the C that way and what it cost.

    WHAT THE PROOF COSTS. Nothing: [mkVSU] discharges every
    module-level obligation (no duplicate identifiers, externs really
    external, [G]'s domain is exactly the AST's internal functions,
    the exports are subsumed, and -- since the unit has no globals --
    the init predicate too) automatically, and the twelve [SF]
    obligations are one [solve_SF_internal] each against a body proof
    that already exists. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import bridge clone.
From Shrincs.internal.vst.sha256 Require Import tables contract.
From Shrincs.clight Require Import sha256.
From Shrincs.internal.vst.sha256.verif Require Import
  logical load_be32 store_be32 parse compress_words compress_blocks sha256.
From VST.floyd Require Import VSU.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.
Local Open Scope logic.

(* ================================================================= *)
(** ** The unit and its interface *)

(** The Clight AST of src/sha256.c in VSU's "quick program" form.
    [QPprog] normalises against the AMBIENT compspecs, which is
    Shrincs.internal.vst.support.base's, built from wots.c. All four Clight programs have an
    empty composite environment, so the
    compspecs are the same object. [compspecs_agree] below says so
    by [reflexivity]. It is also what makes the cross-unit [data_at]
    reconciliation that would normally dominate [linkVSUs] not arise
    at all. *)
Definition sha256_QP : QP.program Clight.function := ltac:(QPprog prog).

(** The interface: exactly the one function src/sha256.h
    declares. Everything else src/sha256.c defines is private. *)
Definition sha256_ASI : funspecs := [ spec_sha256 ].

(** The component's internal spec list -- all twelve. The eleven
    that are not in [sha256_ASI] are exactly the private ones. *)
Definition sha256_internal_specs : funspecs := Gprog_sha.

(* ================================================================= *)
(** ** The component *)

Definition Sha256VSU :
  @VSU NullExtension.Espec nil nil sha256_QP sha256_ASI emp.
Proof.
mkVSU prog sha256_internal_specs.
+ solve_SF_internal body_Ch.
+ solve_SF_internal body_Maj.
+ solve_SF_internal body_Sigma0.
+ solve_SF_internal body_Sigma1.
+ solve_SF_internal body_sigma0.
+ solve_SF_internal body_sigma1.
+ solve_SF_internal body_load_be32.
+ solve_SF_internal body_store_be32.
+ solve_SF_internal body_sha256_parse.
+ solve_SF_internal body_sha256_compress_words.
+ solve_SF_internal body_sha256_compress_blocks.
+ solve_SF_internal body_sha256.
Qed.

(* ================================================================= *)
(** ** Reviewability: what a reader can check by inspection

    Three [reflexivity] facts. Together they say the object above
    speaks about the right symbols, exports one of them, and agrees
    with the C about which one. *)

(** (a) The interface is [sha256]. *)
Lemma sha256_ASI_idents : map fst sha256_ASI = [_shrincs_sha256].
Proof. reflexivity. Qed.

(** (b) The eleven the interface does NOT name, listed. These are the
    functions a client of the unit cannot call and cannot see a
    contract for. *)
Lemma sha256_private_idents :
  List.filter (fun i => negb (id_in_list i (map fst sha256_ASI)))
              (map fst sha256_internal_specs)
  = [ _Ch; _Maj; _Sigma0; _Sigma1; _sigma0; _sigma1;
      _load_be32; _store_be32; _sha256_parse;
      _sha256_compress_words; _sha256_compress_blocks ].
Proof. reflexivity. Qed.

(** (c) The C agrees. Of the twelve functions src/sha256.c defines,
    the AST marks exactly one as public -- the other eleven are
    [static]. So "private" here is not a choice this proof made about
    what to export; it is what the translation unit already says. *)
Lemma sha256_public_idents :
  List.filter (fun i => id_in_list i (map fst sha256_internal_specs)) public_idents
  = [_shrincs_sha256].
Proof. reflexivity. Qed.

(** (d) The ambient compspecs is the sha256 unit's own. All four
    Clight programs have an empty composite environment,
    so the [CompSpecs] the twelve body proofs were done against --
    Shrincs.internal.vst.support.base's, built from wots.c -- IS the one sha256.c
    determines. This is what makes [QPprog prog] above legitimate and
    what removes the cross-unit [data_at] reconciliation from the
    link. *)
Definition CompSpecsSha : compspecs.
Proof. make_compspecs clight.sha256.prog. Defined.

Lemma compspecs_agree : CompSpecs = CompSpecsSha.
Proof. reflexivity. Qed.
