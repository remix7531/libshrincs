(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_sign: VST body proof for [shrincs_wots_c_sign].

    The signature buffer carries the two counter bytes followed by the
    completed signing chains. The grinding result supplies the bounds on
    every chain length. Exhaustion leaves the output content unspecified. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog contract.buffer theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Set Default Timeout 100.

Lemma body_shrincs_wots_c_sign :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_sign shrincs_wots_c_sign_spec.
Proof.
  start_function.
  open_rep.
  forward_call (v_indexes, pk_seed_ptr, message_digest_ptr, pk_seed, message_digest,
                node_height, node_index, Tsh, sh_pk_seed, sh_message_digest).
  destruct (wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index)
    as [[counter indexes]|] eqn:Hgrind.
  - pose proof (wunsigned_u16_range counter) as Hcounter.
    pose proof (@wots_c_sign_some sk_seed pk_seed node_height node_index tree_balanced
                  tree_depth message_digest counter indexes Hgrind) as Hsign.
    pose proof (@wots_c_grind_indexes pk_seed message_digest node_height node_index
                  counter indexes Hgrind) as Hindexes.
    assert (Hlen : Zlength indexes = 32).
    { rewrite Hindexes.
      apply Zlength_base_2b. }
    assert (Hle : forall j : nat, Z.of_nat (nth 0%nat indexes j) <= 15).
    { intros j.
      rewrite Hindexes.
      apply nth_indexes_Z_le. }
    forward_if.
    + rep_lia.
    + clear H.
      forward.
      rewrite (data_at__filled sh_signature 514 signature_ptr).
      unfold filled.
      forward.
      forward.
      rewrite counter_hi_byte.
      rewrite counter_lo_byte.
      set (b0 := wrepr U8 (wunsigned counter / 256 ^ 1)).
      set (b1 := wrepr U8 (wunsigned counter / 256 ^ 0)).
      rewrite (filled_upd 514 (@nil UInt8) b0 0) by (first [reflexivity | lia]).
      rewrite (filled_upd 514 (rcons (@nil UInt8) b0) b1 1)
        by (rewrite ?Zlength_rcons; first [reflexivity | lia]).
      change (rcons (rcons (@nil UInt8) b0) b1)
        with (tval (int_to_bytes counter 2)).
      fold (filled sh_signature 514 (int_to_bytes counter 2) signature_ptr).
      set (chain := fun j : nat =>
             tval (chain_from_seed sk_seed pk_seed node_height node_index tree_balanced
                     tree_depth (nth 0%nat indexes j) j)).
      assert (Hchain : forall j : nat, Zlength (chain j) = 16)
        by (intros j; exact (Zlength_tuple 16 _)).
      assert_PROP (isptr signature_ptr) as Psignature by (unfold filled; entailer!).
      assert_PROP (field_compatible (tarray tuchar 514) [] signature_ptr) as FC
        by (unfold filled; entailer!).
      assert (Hprefix_pointer :
                eval_binop Oadd (tptr tuchar) tint signature_ptr (Vint (Int.repr 2))
                = offset_val 2 signature_ptr).
      { destruct signature_ptr; try contradiction; reflexivity. }

      forward_for_simple_bound 32
        (EX i : Z,
          PROP ()
          LOCAL (lvar _indexes (tarray tuchar 32) v_indexes;
                 temp _signature signature_ptr; temp _message_digest message_digest_ptr;
                 temp _sk_seed sk_seed_ptr; temp _pk_seed pk_seed_ptr;
                 temp _node_height (Vint (Int.repr (wunsigned node_height)));
                 temp _node_index (Vlong (Int64.repr (wunsigned node_index)));
                 temp _tree_balanced (Vint (Int.repr (Z.b2z tree_balanced)));
                 temp _tree_depth (Vint (Int.repr (wunsigned tree_depth))))
          SEP (filled sh_signature 514
                 (cat (tval (int_to_bytes counter 2)) (blocks chain (Z.to_nat i)))
                 signature_ptr;
               data_at Tsh (tarray tuchar 32) (index_vals indexes) v_indexes;
               data_at sh_message_digest (tarray tuchar 32) (vals message_digest) message_digest_ptr;
               data_at sh_sk_seed (tarray tuchar 16) (vals sk_seed) sk_seed_ptr;
               data_at sh_pk_seed (tarray tuchar 16) (vals pk_seed) pk_seed_ptr)).
      * change (Z.to_nat 0) with 0%nat.
        rewrite blocks0.
        rewrite cats0.
        entailer!.
      * rename H into Hi.
        assert (Hdone : Zlength (cat (tval (int_to_bytes counter 2))
                                     (blocks chain (Z.to_nat i))) = 2 + 16 * i).
        { rewrite Zlength_cat, Zlength_tuple.
          rewrite Zlength_blocks by (first [exact Hchain | lia]).
          reflexivity. }
        forward.
        rewrite Hprefix_pointer.
        rewrite (block_pointer_ptr (offset_val 2 signature_ptr) i)
          by (first [destruct signature_ptr; exact Psignature | rep_lia]).
        rewrite offset_offset_val.
        replace (16 * i + 2) with (2 + 16 * i) by lia.
        rewrite (filled_split sh_signature 514
                   (cat (tval (int_to_bytes counter 2)) (blocks chain (Z.to_nat i)))
                   signature_ptr (2 + 16 * i) 16 Hdone ltac:(lia) ltac:(lia) FC).
        Intros.
        assert (Hrepr : Int.repr i = Int.repr (wunsigned (uint U32 (Z.to_nat i))))
          by (rewrite wunsigned_uint_u32 by rep_lia; reflexivity).
        rewrite Hrepr.
        forward_call (offset_val (2 + 16 * i) signature_ptr, pk_seed_ptr, sk_seed_ptr,
                      pk_seed, sk_seed, node_height, node_index, tree_balanced, tree_depth,
                      uint U32 (Z.to_nat i), sh_signature, sh_pk_seed, sh_sk_seed).
        rewrite <- Hrepr.
        forward.
        { entailer!.
          apply tc_val_Znth_index_vals; [lia | apply Hle]. }
        rewrite Znth_index_vals by lia.
        rewrite Hrepr.
        forward_call (offset_val (2 + 16 * i) signature_ptr, pk_seed_ptr,
                      PRF pk_seed sk_seed
                        (WotsCPrf node_height node_index tree_balanced tree_depth
                           (uint U32 (Z.to_nat i))),
                      0, Z.of_nat (nth 0%nat indexes (Z.to_nat i)), pk_seed,
                      node_height, node_index, uint U32 (Z.to_nat i),
                      sh_signature, sh_pk_seed).
        rewrite <- Hrepr.
        rewrite Nat2Z.id.
        change (Z.to_nat 0) with 0%nat.
        change (vals (wots_c_chain_iter
                        (PRF pk_seed sk_seed
                           (WotsCPrf node_height node_index tree_balanced tree_depth
                              (uint U32 (Z.to_nat i))))
                        0 (nth 0%nat indexes (Z.to_nat i)) pk_seed node_height node_index
                        (uint U32 (Z.to_nat i))))
          with (vals (chain (Z.to_nat i))).
        rewrite (blocks_step chain i) by lia.
        rewrite catA.
        rewrite <- (filled_join sh_signature 514
                      (cat (tval (int_to_bytes counter 2)) (blocks chain (Z.to_nat i)))
                      (chain (Z.to_nat i)) signature_ptr (2 + 16 * i) 16
                      Hdone (Hchain _) ltac:(lia) FC).
        entailer!.
      * rewrite (filled_full sh_signature 514
                   (cat (tval (int_to_bytes counter 2)) (blocks chain (Z.to_nat 32)))
                   signature_ptr).
        2: { rewrite Zlength_cat, Zlength_tuple.
             rewrite Zlength_blocks by (first [exact Hchain | lia]).
             reflexivity. }
        change (Z.to_nat 32) with 32%nat.
        unfold chain.
        rewrite <- tval_signature_of.
        forward.
        Exists (wots_c_sign message_digest sk_seed pk_seed node_height node_index
                  tree_balanced tree_depth) 0.
        rewrite Hsign.
        open_rep.
        entailer!.
  - forward_if.
    + forward.
      Exists (wots_c_sign message_digest sk_seed pk_seed node_height node_index
                tree_balanced tree_depth) (-2).
      rewrite (@wots_c_sign_none sk_seed pk_seed node_height node_index tree_balanced
                 tree_depth message_digest Hgrind).
      open_rep.
      entailer!.
    + contradiction.
Qed.
