(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_chain_from_seed: VST body proof for [shrincs_wots_chain_from_seed].

    The per-chain kernel [shrincs_wots_derive_sk(node,i,..); addr[9]=HASH;
    shrincs_wots_chain_iter(node,0,steps,..)].  After [shrincs_wots_derive_sk] the ADRS is
    [shrincs_wots_prf_adrs a i]; the type-byte store retypes it to
    [shrincs_wots_hash_adrs a i] (the two constructors differ only in the type
    byte, [set_type_byte_prf_hash]); the chain then runs [steps] steps from
    index 0. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.

Open Scope Z_scope.

Lemma body_shrincs_wots_chain_from_seed :
  semax_body Vprog Gprog f_shrincs_wots_chain_from_seed shrincs_wots_chain_from_seed_spec.
Proof.
  start_function.

  (* ===== shrincs_wots_derive_sk(node, chain_i, sk_seed, pk_seed, addr) ===== *)
  forward_call (node_ptr, ss_ptr, ps_ptr, a_ptr,
                chain_i, sk_seed, pk_seed, a,
                sh_n, sh_ss, sh_ps, sh_a).
  (* node := derive_sk sk_seed pk_seed (anchor_nh a) (anchor_ni a) chain_i;
     addr := shrincs_wots_prf_adrs a (to_chain32 (Z.to_nat chain_i)). *)

  (* ===== addr[ADRS_TYPE] = SF_SHRINCS_WOTS_HASH (16) ===== *)
  (* [store_type_byte] exposes the wire view and folds the type-byte store
     into [rset_type (adrs_to_raw (shrincs_wots_prf_adrs a i)) 16]; then
     collapse that into [adrs_to_raw (shrincs_wots_hash_adrs a i)] -- the two
     differ only in the type byte ([set_type_byte_prf_hash], with
     [byte_val SF_SHRINCS_WOTS_HASH] convertible to 16) -- and fold the wire
     view back to [adrs_to_vals]. *)
  store_type_byte.
  rewrite set_type_byte_prf_hash.
  rewrite <- adrs_to_vals_raw.

  (* ===== shrincs_wots_chain_iter(node, 0, steps, pk_seed, addr) ===== *)
  forward_call (node_ptr, ps_ptr, a_ptr,
                0, steps,
                derive_sk sk_seed pk_seed (anchor_nh a) (anchor_ni a) chain_i,
                pk_seed, shrincs_wots_hash_adrs w_pred_pos a (to_chain32 (Z.to_nat chain_i)),
                sh_n, sh_ps, sh_a).
  { (* step bound + secret / seed lengths + the hash-address precondition
       ([shrincs_wots_hash_adrs a i] is a [Wc_hash] by construction) *)
    change (Z.of_nat w_pred) with 15 in *.
    repeat split; try rep_lia; try assumption; try apply derive_sk_Zlength;
      try (apply adrs_hash_is_Wc_hash; reflexivity). }

  (* ===== Postcondition: [shrincs_wots_chain_iter] reports its chain at the
     address it was handed, so re-key it onto the base address [a] -- the
     hash constructor keeps [a]'s anchor ([shrincs_wots_hash_adrs_struct_eq])
     and stores [chain_i] in the word [chain_of] reads back. *)
  assert (Hci : chain_of (shrincs_wots_hash_adrs w_pred_pos a
                            (to_chain32 (Z.to_nat chain_i))) = chain_i).
  { cbn [shrincs_wots_hash_adrs payload_b_z].
    apply to_chain32_val.
    lia. }
  destruct (shrincs_wots_hash_adrs_struct_eq a (to_chain32 (Z.to_nat chain_i)))
    as (Hnh & Hni).
  rewrite Hci, Hnh, Hni.
  change (Z.to_nat 0) with 0%nat.
  entailer!!.
Qed.
