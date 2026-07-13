(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.sha256: SHA-256, abstracted as a Parameter.

    SHA-256 itself is left abstract; external tooling instantiates it
    (VST's trusted funspec bridges it to the C implementation; a
    future SSProve-side concrete-hash-game axiom set, per
    proof/ssprove/axioms.v, would bridge it to the security
    proof). Its type states the two properties every consumer needs
    intrinsically, rather than as separate axioms: the output is
    exactly [hash_bytes = 32] bytes ([Vec.t]), and the input is at
    most [sha256_max_input_len] bytes ([BList.t]) -- SHA-256's real
    limit, 2^64 - 1 *bits*, i.e. [(2^64 - 1) / 8 = 2^61 - 1] bytes
    (the message length is padded into a 64-bit field). [Z]'s binary
    representation makes this literal cheap to reason about with
    [lia]; a [nat] this large would not be (see [model.bounded]'s
    header comment).

    No hash call in this repo comes remotely close to that bound --
    [model.wots]'s [thash]/[H_grind] wrap the real [SHA256] behind a
    clip to [sha256_max_input_len] ([bounded.BList.clip]) so every
    caller can keep passing a plain [list byte] without threading a
    length invariant through the whole model; the clip only exists to
    satisfy [SHA256]'s type -- it never actually truncates anything a
    real WOTS+C call produces.

    Generic, not scheme-specific -- reusable by any future SHRINCS
    scheme model that hashes with SHA-256, mirroring the
    src/sha256.c / src/wots.c split at the C-source level. *)

From Stdlib Require Import List ZArith.
From Model Require Export address bounded.
#[local] Open Scope Z_scope.

Definition block : Type := list byte.

Definition hash_bytes : Z := 32.

Definition sha256_max_input_len : Z := 2 ^ 61 - 1.

Parameter SHA256 : BList.t byte sha256_max_input_len -> Vec.t byte hash_bytes.
