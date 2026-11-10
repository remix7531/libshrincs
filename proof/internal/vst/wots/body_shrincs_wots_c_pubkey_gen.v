(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_pubkey_gen: VST body proof for [shrincs_wots_c_pubkey_gen].

    The loop fills the local [wots_pk] one chain tip at a time: turn [i]
    derives the secret start of chain [i] into the next sixteen bytes and
    iterates it there to its tip. [wots_pk] is a [filled] buffer whose
    written part after [i] turns is the first [i] tips. After the loop it
    is the reference's concatenation, and one [T_sf] gives the key. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog contract.buffer theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Set Default Timeout 100.

Lemma body_shrincs_wots_c_pubkey_gen :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_pubkey_gen shrincs_wots_c_pubkey_gen_spec.
Proof.
  start_function.
  open_rep.
  set (tip := fun i : nat =>
         tval (chain_from_seed sk_seed pk_seed node_height node_index tree_balanced
                 tree_depth 15 i)).
  assert (Htip : forall i : nat, Zlength (tip i) = 16) by (intros i; exact (Zlength_tuple 16 _)).
  assert_PROP (isptr v_wots_pk) as Pwots_pk by entailer!.
  rewrite (data_at__filled Tsh 512 v_wots_pk).
  assert_PROP (field_compatible (tarray tuchar 512) [] v_wots_pk) as FC
    by (unfold filled; entailer!).

  forward_for_simple_bound 32
    (EX i : Z,
      PROP ()
      LOCAL (lvar _wots_pk (tarray tuchar 512) v_wots_pk;
             temp _pk pk_ptr; temp _sk_seed sk_seed_ptr; temp _pk_seed pk_seed_ptr;
             temp _node_height (Vint (Int.repr (wunsigned node_height)));
             temp _node_index (Vlong (Int64.repr (wunsigned node_index)));
             temp _tree_balanced (Vint (Int.repr (Z.b2z tree_balanced)));
             temp _tree_depth (Vint (Int.repr (wunsigned tree_depth))))
      SEP (filled Tsh 512 (blocks tip (Z.to_nat i)) v_wots_pk;
           data_at_ sh_pk (tarray tuchar 16) pk_ptr;
           data_at sh_sk_seed (tarray tuchar 16) (vals sk_seed) sk_seed_ptr;
           data_at sh_pk_seed (tarray tuchar 16) (vals pk_seed) pk_seed_ptr)).
  - (* no tip yet *)
    entailer!.
  - rename H into Hi.
    assert (Hdone : Zlength (blocks tip (Z.to_nat i)) = 16 * i)
      by (apply Zlength_blocks; [exact Htip | lia]).
    (* tip = wots_pk + i * N *)
    forward.
    rewrite (block_pointer_array v_wots_pk 512 i Pwots_pk) by rep_lia.
    (* the next sixteen bytes of [wots_pk], as an array of their own *)
    rewrite (filled_split Tsh 512 (blocks tip (Z.to_nat i)) v_wots_pk (16 * i) 16 Hdone
               ltac:(lia) ltac:(lia) FC).
    Intros.
    assert (Hrepr : Int.repr i = Int.repr (wunsigned (uint U32 (Z.to_nat i))))
      by (rewrite wunsigned_uint_u32 by rep_lia; reflexivity).
    rewrite Hrepr.

    (* shrincs_wots_c_prf(tip, pk_seed, sk_seed, node_height, node_index, tree_balanced,
                          tree_depth, i) *)
    forward_call (offset_val (16 * i) v_wots_pk, pk_seed_ptr, sk_seed_ptr, pk_seed, sk_seed,
                  node_height, node_index, tree_balanced, tree_depth,
                  uint U32 (Z.to_nat i), Tsh, sh_pk_seed, sh_sk_seed).

    (* shrincs_wots_c_chain_iter(tip, 0, WOTS_C_CHAIN_MAX, pk_seed, node_height, node_index, i) *)
    forward_call (offset_val (16 * i) v_wots_pk, pk_seed_ptr,
                  PRF pk_seed sk_seed
                    (WotsCPrf node_height node_index tree_balanced tree_depth
                       (uint U32 (Z.to_nat i))),
                  0, 15, pk_seed, node_height, node_index, uint U32 (Z.to_nat i),
                  Tsh, sh_pk_seed).
    rewrite <- Hrepr.

    (* the written block goes back: [wots_pk] now holds [i + 1] tips *)
    change (Z.to_nat 0) with 0%nat.
    change (Z.to_nat 15) with 15%nat.
    change (vals (wots_c_chain_iter
                    (PRF pk_seed sk_seed
                       (WotsCPrf node_height node_index tree_balanced tree_depth
                          (uint U32 (Z.to_nat i))))
                    0 15 pk_seed node_height node_index (uint U32 (Z.to_nat i))))
      with (vals (tip (Z.to_nat i))).
    rewrite (blocks_step tip i) by lia.
    rewrite <- (filled_join Tsh 512 (blocks tip (Z.to_nat i)) (tip (Z.to_nat i)) v_wots_pk
                  (16 * i) 16 Hdone (Htip _) ltac:(lia) FC).
    entailer!.
  - (* all thirty-two tips: [wots_pk] is the reference's concatenation *)
    rewrite (filled_full Tsh 512 (blocks tip (Z.to_nat 32)) v_wots_pk)
      by (rewrite Zlength_blocks by (first [exact Htip | lia]); reflexivity).
    change (Z.to_nat 32) with 32%nat.
    unfold tip.
    rewrite <- tval_pubkey_gen_tips.
    (* From here the tips are an opaque tuple with one recorded fact, so that no
       tactic unfolds the thirty-two chains. *)
    pose proof (wots_c_pubkey_gen_eq sk_seed pk_seed node_height node_index tree_balanced
                  tree_depth) as Hkey.
    set (tips := pubkey_gen_tips sk_seed pk_seed node_height node_index tree_balanced
                   tree_depth) in Hkey |- *.
    clearbody tips.
    clear tip Htip.

    (* shrincs_wots_c_t_sf(pk, pk_seed, node_height, node_index, wots_pk) *)
    forward_call (pk_ptr, pk_seed_ptr, v_wots_pk, pk_seed, node_height, node_index, tips,
                  sh_pk, sh_pk_seed, Tsh).
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 512) (vals tips) v_wots_pk).
    rewrite <- Hkey.
    Exists (wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth).
    open_rep.
    entailer!.
Qed.
