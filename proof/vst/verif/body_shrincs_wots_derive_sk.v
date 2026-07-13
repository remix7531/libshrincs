(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_derive_sk: VST body proof for [shrincs_wots_derive_sk]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
Import ListNotations.
Open Scope Z_scope.

(* The wire-view fold of the four in-place stores ([prf_raw_stores]) is
   shared -- see [contract.lemmas.chain_blocks]. *)

Local Opaque to_byte.

(** Preimage assembly for [shrincs_wots_derive_sk]: type the ADRS, splice
    reserved/chain/hash via three [shrincs_adrs_put32] calls on the
    wire view, then [shrincs_thash] the result -- a non-aliased
    [PRF] call giving [shrincs_wots_derive_sk chain_i sk_seed pk_seed a]
    and leaving [addr] holding [shrincs_wots_prf_adrs a chain_i]. *)
Lemma body_shrincs_wots_derive_sk : semax_body Vprog Gprog f_shrincs_wots_derive_sk shrincs_wots_derive_sk_spec.
Proof.
  start_function.

  (* ===== addr[ADRS_TYPE] = SF_SHRINCS_WOTS_PRF (21), over the wire view ===== *)
  store_type_byte.

  (* ===== shrincs_adrs_put32(addr, ADRS_RESERVED=10, 0) ===== *)
  forward_call (a_ptr, 10, 0, radrs_bytes (rset_type (adrs_to_raw a) 21), sh_a).
  rewrite shrincs_adrs_put32_reserved.

  (* ===== shrincs_adrs_put32(addr, ADRS_CHAIN=14, chain_i) ===== *)
  forward_call (a_ptr, 14, chain_i,
                radrs_bytes (rset_payload_a (rset_type (adrs_to_raw a) 21) 0), sh_a).
  rewrite shrincs_adrs_put32_chain.

  (* ===== shrincs_adrs_put32(addr, ADRS_HASH=18, 0) ===== *)
  forward_call (a_ptr, 18, 0,
                radrs_bytes (rset_payload_b (rset_payload_a (rset_type (adrs_to_raw a) 21) 0) chain_i),
                sh_a).
  rewrite shrincs_adrs_put32_hash.

  (* Fold the wire view back to the union PRF address. *)
  rewrite (prf_raw_stores a chain_i) by rep_lia.
  rewrite radrs_bytes_to_raw.

  (* ===== shrincs_thash(out, pk_seed, addr, sk_seed, N) -- [PRF] reads
     [sk_seed] directly as the message and writes the derived chain secret
     to the uninitialised [out]. *)
  unfold n_bytes in *. change (Z.of_nat n) with 16 in *.
  forward_call (out_ptr, ps_ptr, a_ptr, ss_ptr, 16,
                shrincs_wots_prf_adrs a (to_chain32 (Z.to_nat chain_i)),
                pk_seed, sk_seed, sh_o, sh_ps, sh_a, sh_ss).

  (* ===== Postcondition ===== *)
  unfold shrincs_wots_derive_sk, PRF.
  entailer!!.
Qed.
