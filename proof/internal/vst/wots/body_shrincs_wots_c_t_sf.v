(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_t_sf: VST body proof for [shrincs_wots_c_t_sf].

    Packs the [WotsCPk] address and hashes the chain tips with the
    shared [shrincs_thash], which is [T_sf] at that address. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_wots_c_t_sf :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_t_sf shrincs_wots_c_t_sf_spec.
Proof.
  start_function.

  (* shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_PK, 0, 0, 0) *)
  forward_call (v_addr, node_height, node_index, SF_WOTS_C_PK,
                uint U32 0, uint U32 0, uint U32 0, Tsh).

  (* shrincs_thash(out, pk_seed, addr, M_l, WOTS_C_CHAINS_SIZE) *)
  forward_call (out_ptr, ps_ptr, v_addr, m_ptr, 512,
                pk_seed,
                pack node_height node_index SF_WOTS_C_PK (uint U32 0) (uint U32 0) (uint U32 0),
                tval M_l, sh_o, sh_ps, Tsh, sh_m).
  { exact (Zlength_tuple _ M_l). }

  rewrite T_sf_th.
  entailer!.
Qed.
