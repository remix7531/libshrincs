(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_prf: VST body proof for [shrincs_wots_c_prf].

    Packs the [WotsCPrf] address, whose first payload word carries the
    shape of the tree, and hashes the secret seed with the shared
    [shrincs_thash], which is [PRF] at that address. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_wots_c_prf :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_prf shrincs_wots_c_prf_spec.
Proof.
  start_function.

  (* word1 = ((uint32_t)tree_balanced << 24) + ((uint32_t)tree_depth << 16) *)
  forward.
  rewrite prf_word1.

  (* shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_PRF, word1, chain_index, 0) *)
  forward_call (v_addr, node_height, node_index, SF_WOTS_C_PRF,
                wrepr U32 (Z.b2z tree_balanced * 2 ^ 24 + wunsigned tree_depth * 2 ^ 16),
                chain_index, uint U32 0, Tsh).

  (* shrincs_thash(out, pk_seed, addr, sk_seed, N) *)
  forward_call (out_ptr, ps_ptr, v_addr, ss_ptr, 16,
                pk_seed,
                pack node_height node_index SF_WOTS_C_PRF
                  (wrepr U32 (Z.b2z tree_balanced * 2 ^ 24 + wunsigned tree_depth * 2 ^ 16))
                  chain_index (uint U32 0),
                tval sk_seed, sh_o, sh_ps, Tsh, sh_ss).
  { exact (Zlength_tuple 16 sk_seed). }

  rewrite PRF_th.
  entailer!.
Qed.
