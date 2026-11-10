(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_f: VST body proof for [shrincs_wots_c_f].

    Packs the [WotsCHash] address and hashes the node with the shared
    [shrincs_thash], which is [F] at that address. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_wots_c_f :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_f shrincs_wots_c_f_spec.
Proof.
  start_function.

  (* shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_HASH, 0, chain_index, hash_index) *)
  forward_call (v_addr, node_height, node_index, SF_WOTS_C_HASH,
                uint U32 0, chain_index, hash_index, Tsh).

  (* shrincs_thash(out, pk_seed, addr, M_1, N) *)
  forward_call (out_ptr, ps_ptr, v_addr, m_ptr, 16,
                pk_seed,
                pack node_height node_index SF_WOTS_C_HASH (uint U32 0) chain_index hash_index,
                tval M_1, sh_o, sh_ps, Tsh, sh_m).
  { exact (Zlength_tuple 16 M_1). }

  rewrite F_th.
  entailer!.
Qed.
