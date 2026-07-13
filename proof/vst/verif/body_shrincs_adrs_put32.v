(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_adrs_put32: VST body proof for [shrincs_adrs_put32].

    Four big-endian byte stores at [addr[off..off+4)] realise the raw
    [sublist] splice in [shrincs_adrs_put32_spec]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import clight.thash.
Import ListNotations.

Open Scope Z_scope.

Lemma body_shrincs_adrs_put32 : semax_body Vprog Gprog f_shrincs_adrs_put32 shrincs_adrs_put32_spec.
Proof.
  Local Opaque to_byte.
  start_function.
  assert (Hcv : Zlength (block_to_vals content) = 22)
    by (rewrite block_to_vals_length; assumption).
  (* Four big-endian byte stores. *)
  forward. forward. forward. forward.
  entailer!!.
  (* Collapse the cast+store double zero_ext, then normalise every stored
     byte to [Vubyte (Byte.repr (v / 2^k mod 256))]. *)
  rewrite !Int.zero_ext_idem by lia.
  rewrite (zero_ext_shru_byte v 24) by auto.
  rewrite (zero_ext_shru_byte v 16) by auto.
  rewrite (zero_ext_shru_byte v 8) by auto.
  rewrite zero_ext_byte.
  (* RHS: expose the four splice bytes in the same [v / 2^k] form. *)
  rewrite to_byte_4_eq.
  apply derives_refl'; f_equal.
  unfold block_to_vals.
  rewrite !map_app.
  list_solve.
Qed.
