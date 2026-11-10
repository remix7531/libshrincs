(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.trusted: the SHA-256 contract the callers import

    [sha256_spec] is the SHA-256 unit's exported contract. [sha256_spec_canonical] pins it to [Shrincs.contracts.spec_sha256], so the thash and wots imports describe the canonical FIPS 180-4 definition. [Shrincs.internal.vst.link] discharges those imports against the verified SHA-256 component.

    The two callers, [shrincs_thash] and [shrincs_wots_c_h_grind], hold their preimage as bytes of the specification. [contract.buffer] restates this contract in that vocabulary. *)

From VST Require Export floyd.proofauto.
From Shrincs.internal.vst.sha256 Require Import contract.
From Shrincs.internal.vst.sha256 Require sync.
Require Shrincs.sha256 Shrincs.contracts.

Open Scope Z_scope.

(** [sha256(out, in, inlen)]: writes the 32-byte digest of [in] to [out]. Not restated here: it IS the sha256 unit's exported contract, so there is exactly one funspec for [shrincs_sha256] in the repository and no second description of it to keep in sync. *)
Definition sha256_spec : ident * funspec := Shrincs.internal.vst.sha256.contract.spec_sha256.

(** ... and it is the reviewer-facing one, by [reflexivity] once the clone's hash name is rewritten to the canonical one. Same content as [Shrincs.internal.vst.sha256.correct]'s [sha256_ASI_canonical], restated here because THIS is the funspec [Gprog] hands to every caller. *)
Lemma sha256_spec_canonical : sha256_spec = Shrincs.contracts.spec_sha256.
Proof.
unfold sha256_spec, Shrincs.internal.vst.sha256.contract.spec_sha256,
       Shrincs.contracts.spec_sha256.
rewrite Shrincs.internal.vst.sha256.sync.sync_sha256.
reflexivity.
Qed.
