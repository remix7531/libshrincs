(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.sha256.correct: src/sha256.c satisfies the contract of Model.sha256_spec

    The twelve semax_body proofs of Vst.sha256.verif are stated
    over the CLONE, Vst.sha256.clone, and packaged by
    Vst.sha256.vsu as a component exporting the clone's spelling of
    the one contract. Model.sha256_spec, a reviewer-facing file,
    spells the same
    contract over its own definitions. This file is the one step
    between, and it is the only reason the reviewer-facing contract is
    not decoration.

    IT COULD NOT BE STATED IN Model.sha256_spec ITSELF, and the reason is an
    ordering fact rather than a choice: the step needs Vst.sha256.sync,
    the gate asserting clone = original, and that gate mentions
    Model.sha256_spec, so it is downstream of it. The component is downstream
    again. So the claim lands here, one file after both.

    The exported interface contains only the complete SHA-256 digest. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import contract vsu sync.
From Shrincs.internal.vst.sha256 Require clone.
Require Shrincs.sha256.
From VST.floyd Require Import VSU.

Set Bullet Behavior "Strict Subproofs".

(** The reviewer's spelling of the interface. *)
Module Spec := Shrincs.sha256.

(** The component's Exports slot, read at Model.sha256_spec's definition.
    [sync_sha256] is the whole content: the two files' funspecs are
    written identically, so once the hash names agree the lists are the
    same term. *)
Lemma sha256_ASI_canonical :
  sha256_ASI = [ Spec.spec_sha256 ].
Proof.
unfold sha256_ASI, contract.spec_sha256, Spec.spec_sha256.
rewrite sync_sha256.
reflexivity.
Qed.

(** src/sha256.c is a verified component that assumes nothing, claims
    no global state, and provides exactly the one contract of
    Model.sha256_spec -- SS 6.2 in general. *)
Theorem sha256_c_correct :
  @VSU NullExtension.Espec nil nil sha256_QP
       [ Spec.spec_sha256 ] emp.
Proof.
rewrite <- sha256_ASI_canonical.
exact Sha256VSU.
Qed.
