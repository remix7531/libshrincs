(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_pubkey_from_sig: VST body proof for public key recovery.

    The signature stays read-only while the local buffer collects the
    completed chains. Digest rejection leaves the public key unspecified. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog contract.buffer theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Set Default Timeout 100.

Local Lemma signature_counter_unsigned (signature : Bytes (2 + WOTS_C_CHAINS_SIZE)) :
  wunsigned (int_from_bytes U16 (slice signature 0 2))
  = wunsigned (nth (uint U8 0) signature 0) * 256
    + wunsigned (nth (uint U8 0) signature 1).
Proof.
  change (int_from_bytes U16 (slice signature 0 2))
    with (int_from_bytes U16
            [:: nth (uint U8 0) signature 0; nth (uint U8 0) signature 1]).
  rewrite int_from_bytes_2.
  apply wunsigned_repr_small.
  change (wbase U16) with 65536.
  pose proof (wunsigned_u8_range (nth (uint U8 0) signature 0)) as Hfirst.
  pose proof (wunsigned_u8_range (nth (uint U8 0) signature 1)) as Hsecond.
  lia.
Qed.

Lemma body_shrincs_wots_c_pubkey_from_sig :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_pubkey_from_sig
    shrincs_wots_c_pubkey_from_sig_spec.
Proof.
  start_function.
  open_rep.
  assert_PROP (isptr signature_ptr) as Psignature by entailer!.
  assert_PROP (isptr v_wots_pk) as Pwots_pk by entailer!.
  forward.
  { entailer!.
    apply tc_val_Znth_vals.
    rewrite Zlength_tuple.
    change (Z.of_nat (2 + WOTS_C_CHAINS_SIZE)) with 514.
    lia. }
  rewrite Znth_vals by (rewrite Zlength_tuple; change (Z.of_nat (2 + WOTS_C_CHAINS_SIZE)) with 514; lia).
  rewrite Znth_seq_nth by lia.
  forward.
  { entailer!.
    apply tc_val_Znth_vals.
    rewrite Zlength_tuple.
    change (Z.of_nat (2 + WOTS_C_CHAINS_SIZE)) with 514.
    lia. }
  rewrite Znth_vals by (rewrite Zlength_tuple; change (Z.of_nat (2 + WOTS_C_CHAINS_SIZE)) with 514; lia).
  rewrite Znth_seq_nth by lia.
  forward.
  rewrite shl_repr by (pose proof (wunsigned_u8_range (nth (uint U8 0) signature 0)); lia).
  rewrite add_repr.
  change (2 ^ 8) with 256.
  rewrite <- signature_counter_unsigned.
  set (counter := int_from_bytes U16 (slice signature 0 2)).
  forward_call (v_indexes, pk_seed_ptr, message_digest_ptr, pk_seed, message_digest,
                node_height, node_index, counter, Tsh, sh_pk_seed, sh_message_digest).
  destruct (wots_c_map_digest pk_seed message_digest node_height node_index counter)
    as [indexes|] eqn:Hmap.
  - forward_if.
    + discriminate.
    + pose proof (@wots_c_map_digest_indexes pk_seed message_digest node_height node_index
                    counter indexes Hmap) as Hindexes.
      assert (Hlen : Zlength indexes = 32).
      { rewrite Hindexes.
        apply Zlength_base_2b. }
      assert (Hle : forall j : nat, Z.of_nat (nth 0%nat indexes j) <= 15).
      { intros j.
        rewrite Hindexes.
        apply nth_indexes_Z_le. }
      pose proof (@wots_c_pubkey_from_sig_some pk_seed node_height node_index signature
                    message_digest indexes Hmap) as Hrecover.
      set (tip := fun j : nat =>
             tval (chain_from_sig pk_seed node_height node_index signature indexes j)).
      assert (Htip : forall j : nat, Zlength (tip j) = 16)
        by (intros j; exact (Zlength_tuple 16 _)).
      rewrite (data_at__filled Tsh 512 v_wots_pk).
      assert_PROP (field_compatible (tarray tuchar 512) [] v_wots_pk) as FC
        by (unfold filled; entailer!).

      forward_for_simple_bound 32
        (EX i : Z,
          PROP ()
          LOCAL (lvar _indexes (tarray tuchar 32) v_indexes;
                 lvar _wots_pk (tarray tuchar 512) v_wots_pk;
                 temp _pk pk_ptr; temp _signature signature_ptr;
                 temp _message_digest message_digest_ptr; temp _pk_seed pk_seed_ptr;
                 temp _node_height (Vint (Int.repr (wunsigned node_height)));
                 temp _node_index (Vlong (Int64.repr (wunsigned node_index))))
          SEP (filled Tsh 512 (blocks tip (Z.to_nat i)) v_wots_pk;
               data_at Tsh (tarray tuchar 32) (index_vals indexes) v_indexes;
               data_at_ sh_pk (tarray tuchar 16) pk_ptr;
               data_at sh_signature (tarray tuchar 514) (vals signature) signature_ptr;
               data_at sh_message_digest (tarray tuchar 32) (vals message_digest) message_digest_ptr;
               data_at sh_pk_seed (tarray tuchar 16) (vals pk_seed) pk_seed_ptr)).
      * entailer!.
      * rename H into Hi.
        assert (Hdone : Zlength (blocks tip (Z.to_nat i)) = 16 * i)
          by (apply Zlength_blocks; [exact Htip | lia]).
        forward.
        rewrite (block_pointer_array v_wots_pk 512 i Pwots_pk) by rep_lia.
        rewrite (filled_split Tsh 512 (blocks tip (Z.to_nat i)) v_wots_pk (16 * i) 16
                   Hdone ltac:(lia) ltac:(lia) FC).
        Intros.
        rewrite (data_at__filled Tsh 16 (offset_val (16 * i) v_wots_pk)).
        assert (Hslice : sublist (2 + 16 * i) (2 + 16 * i + 16) (tval signature)
                        = tval (slice signature (2 + Z.to_nat i * 16) 16)).
        { rewrite sublist_slice.
          - replace (Z.to_nat (2 + 16 * i)) with (2 + Z.to_nat i * 16)%nat
              by (rewrite <- plusE, <- multE; lia).
            replace (Z.to_nat (2 + 16 * i + 16 - (2 + 16 * i))) with 16%nat by lia.
            reflexivity.
          - lia.
          - rewrite Zlength_tuple.
            change (Z.of_nat (2 + WOTS_C_CHAINS_SIZE)) with 514.
            lia. }
        forward_call memcpy_fill_sub
          (Tsh, sh_signature, offset_val (16 * i) v_wots_pk, signature_ptr,
           offset_val (16 * i) v_wots_pk, offset_val (2 + 16 * i) signature_ptr,
           16, 514, 0, 2 + 16 * i, 16, @nil UInt8, tval signature,
           tval (slice signature (2 + Z.to_nat i * 16) 16)).
        { entailer!.
          replace (i * 16) with (16 * i) by lia.
          destruct signature_ptr; try contradiction.
          destruct v_wots_pk; try contradiction.
          reflexivity. }
        { repeat split; try assumption; try (rewrite ?Zlength_tuple; reflexivity); lia. }
        change (cat nil (tval (slice signature (2 + Z.to_nat i * 16) 16)))
          with (tval (slice signature (2 + Z.to_nat i * 16) 16)).
        rewrite (filled_full Tsh 16 (slice signature (2 + Z.to_nat i * 16) 16)
                   (offset_val (16 * i) v_wots_pk)) by exact (Zlength_tuple 16 _).
        forward.
        { entailer!.
          apply tc_val_Znth_index_vals; [lia | apply Hle]. }
        rewrite Znth_index_vals by lia.
        assert (Hrepr : Int.repr i = Int.repr (wunsigned (uint U32 (Z.to_nat i))))
          by (rewrite wunsigned_uint_u32 by rep_lia; reflexivity).
        rewrite Hrepr.
        forward_call (offset_val (16 * i) v_wots_pk, pk_seed_ptr,
                      slice signature (2 + Z.to_nat i * 16) 16,
                      Z.of_nat (nth 0%nat indexes (Z.to_nat i)), 15, pk_seed,
                      node_height, node_index, uint U32 (Z.to_nat i), Tsh, sh_pk_seed).
        { repeat split; try lia.
          apply Hle. }
        rewrite <- Hrepr.
        rewrite Nat2Z.id.
        change (Z.to_nat 15) with 15%nat.
        change (vals (wots_c_chain_iter (slice signature (2 + Z.to_nat i * 16) 16)
                        (nth 0%nat indexes (Z.to_nat i)) 15 pk_seed node_height node_index
                        (uint U32 (Z.to_nat i))))
          with (vals (tip (Z.to_nat i))).
        rewrite (blocks_step tip i) by lia.
        rewrite <- (filled_join Tsh 512 (blocks tip (Z.to_nat i)) (tip (Z.to_nat i))
                      v_wots_pk (16 * i) 16 Hdone (Htip _) ltac:(lia) FC).
        entailer!.
      * rewrite (filled_full Tsh 512 (blocks tip (Z.to_nat 32)) v_wots_pk)
          by (rewrite Zlength_blocks by (first [exact Htip | lia]); reflexivity).
        change (Z.to_nat 32) with 32%nat.
        unfold tip.
        rewrite <- tval_recovered_tips.
        set (tips := recovered_tips pk_seed node_height node_index signature indexes)
          in Hrecover |- *.
        clearbody tips.
        clear tip Htip.
        forward_call (pk_ptr, pk_seed_ptr, v_wots_pk, pk_seed, node_height, node_index,
                      tips, sh_pk, sh_pk_seed, Tsh).
        sep_apply (data_at_data_at_ Tsh (tarray tuchar 512) (vals tips) v_wots_pk).
        forward.
        Exists (wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index) 0.
        rewrite Hrecover.
        open_rep.
        entailer!.
  - forward_if.
    + forward.
      Exists (wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index) (-1).
      rewrite (@wots_c_pubkey_from_sig_none pk_seed node_height node_index signature
                 message_digest Hmap).
      open_rep.
      entailer!.
    + contradiction.
Qed.
