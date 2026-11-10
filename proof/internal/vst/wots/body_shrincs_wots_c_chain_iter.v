(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_chain_iter: VST body proof for [shrincs_wots_c_chain_iter].

    The C loop [for (j = start; j < stop; j++)] copies the node aside and
    overwrites it with [F] at hash index [j]. The loop invariant at [j]
    says [node] holds the reference's chain from [start] to [j], and one
    turn is [wots_c_chain_iter_step]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog contract.buffer theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_wots_c_chain_iter :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_chain_iter shrincs_wots_c_chain_iter_spec.
Proof.
  start_function.
  rename H into Hstart.
  rename H0 into Hstop.
  assert_PROP (isptr v_previous) as Pprevious by entailer!.
  assert_PROP (isptr node_ptr) as Pnode by entailer!.

  forward_for_simple_bound stop
    (EX j : Z,
      PROP (start <= j)
      LOCAL (lvar _previous (tarray tuchar 16) v_previous;
             temp _node node_ptr;
             temp _stop (Vint (Int.repr stop));
             temp _pk_seed ps_ptr;
             temp _node_height (Vint (Int.repr (wunsigned node_height)));
             temp _node_index (Vlong (Int64.repr (wunsigned node_index)));
             temp _chain_index (Vint (Int.repr (wunsigned chain_index))))
      SEP (data_at sh_n (tarray tuchar 16)
             (vals (wots_c_chain_iter node (Z.to_nat start) (Z.to_nat j) pk_seed
                      node_height node_index chain_index)) node_ptr;
           data_at_ Tsh (tarray tuchar 16) v_previous;
           data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr)).
  - (* j = start: the chain from [start] to [start] is the node itself *)
    forward.
    Exists start.
    rewrite wots_c_chain_iter_nil.
    entailer!.
  - (* one turn, at hash index [i] *)
    rename H into Hi.
    Intros.
    rename H into Hsi.
    set (current := wots_c_chain_iter node (Z.to_nat start) (Z.to_nat i) pk_seed
                      node_height node_index chain_index).

    (* memcpy(previous, node, N) *)
    rewrite (data_at__filled Tsh 16 v_previous).
    forward_call memcpy_fill_sub
      (Tsh, sh_n, v_previous, node_ptr, v_previous, node_ptr, 16, 16, 0, 0, 16,
       @nil UInt8, tval current, tval current).
    { bytes_side_conditions. }
    change (cat nil (tval current)) with (tval current).
    rewrite (filled_full Tsh 16 current v_previous) by exact (Zlength_tuple 16 current).

    (* shrincs_wots_c_f(node, pk_seed, node_height, node_index, chain_index, j, previous):
       the node is overwritten, so its old content is given up first *)
    sep_apply (data_at_data_at_ sh_n (tarray tuchar 16) (vals current) node_ptr).
    assert (Hrepr : Int.repr i = Int.repr (wunsigned (uint U32 (Z.to_nat i))))
      by (rewrite wunsigned_uint_u32 by rep_lia; reflexivity).
    rewrite Hrepr.
    forward_call (node_ptr, ps_ptr, v_previous, pk_seed, node_height, node_index,
                  chain_index, uint U32 (Z.to_nat i), current, sh_n, sh_ps, Tsh).
    rewrite <- Hrepr.

    (* the invariant at [i + 1] *)
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite (wots_c_chain_iter_step pk_seed node_height node_index chain_index node
               (start := Z.to_nat start) (j := Z.to_nat i))
      by (apply (introT leP); lia).
    fold current.
    entailer!.
  - (* j = stop *)
    entailer!.
Qed.
