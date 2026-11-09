(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_panic: VST body proof for [shrincs_panic].

    The funspec has a [PROP(False)] precondition (panic is only invoked
    on unreachable error paths), so the body proof is vacuous: any
    caller able to establish the precondition has already derived
    [False] and the body can be anything. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.

Open Scope Z_scope.

Lemma body_shrincs_panic :
  semax_body Vprog Gprog f_shrincs_panic shrincs_panic_spec.
Proof.
  start_function.
  contradiction.
Qed.
