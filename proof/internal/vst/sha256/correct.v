(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.sha256.correct: the public SHA-256 contract

    The body proofs use the private SHA clone. Synchronization rewrites
    its digest to the canonical definition, so the verified component
    exports exactly the contract of Shrincs.contracts. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import contract vsu sync.
From Shrincs.internal.vst.sha256 Require clone.
Require Shrincs.sha256 Shrincs.contracts.
From VST.floyd Require Import VSU.

Set Bullet Behavior "Strict Subproofs".

(** The reviewer's spelling of the interface. *)
Module Spec := Shrincs.contracts.

(** The component's Exports slot, read at the public contract.
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
    no global state, and provides the public complete-digest contract. *)
Theorem sha256_c_correct :
  @VSU NullExtension.Espec nil nil sha256_QP
       [ Spec.spec_sha256 ] emp.
Proof.
rewrite <- sha256_ASI_canonical.
exact Sha256VSU.
Qed.
