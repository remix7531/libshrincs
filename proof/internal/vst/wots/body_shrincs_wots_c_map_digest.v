(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_map_digest: VST body proof for [shrincs_wots_c_map_digest].

    Hashes the digest at the counter into the local [hashed], splits it
    into the thirty-two indexes, sums them in a loop and compares the sum
    with the constant. The loop invariant carries the sum of the first
    [j] indexes. [wots_c_map_digest_some] and [wots_c_map_digest_none]
    turn the comparison into the reference's result.

    Once the two calls are done the indexes are an opaque list with four
    recorded facts. The loop must not see how they are computed: floyd
    would evaluate [take] on them, which forces the whole digit
    conversion. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Lemma body_shrincs_wots_c_map_digest :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_map_digest shrincs_wots_c_map_digest_spec.
Proof.
  start_function.

  (* shrincs_wots_c_h_grind(hashed, pk_seed, node_height, node_index, message_digest, counter) *)
  forward_call (v_hashed, ps_ptr, m_ptr, pk_seed, node_height, node_index,
                message_digest, counter, Tsh, sh_ps, sh_m).

  (* shrincs_wots_c_base_2b(indexes, hashed) *)
  forward_call (i_ptr, v_hashed,
                H_grind pk_seed (WotsCGrind node_height node_index) message_digest counter,
                sh_i, Tsh).

  (* ===== The indexes, from here on a list with these facts ===== *)
  change (base_2b (H_grind pk_seed (WotsCGrind node_height node_index) message_digest counter)
            WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT)
    with (digest_indexes pk_seed message_digest node_height node_index counter).
  pose proof (@sumn_digest_indexes_le pk_seed message_digest node_height node_index counter)
    as Hsum.
  pose proof (@wots_c_map_digest_some pk_seed message_digest node_height node_index counter)
    as Hsome.
  pose proof (@wots_c_map_digest_none pk_seed message_digest node_height node_index counter)
    as Hnone.
  assert (Hlen : Zlength (digest_indexes pk_seed message_digest node_height node_index counter)
                 = 32)
    by (exact (Zlength_base_2b _ _ _)).
  assert (Hle : forall m : nat,
            Z.of_nat (nth 0%nat
                        (digest_indexes pk_seed message_digest node_height node_index counter)
                        m) <= 15)
    by (intros m; apply nth_indexes_Z_le).
  set (indexes := digest_indexes pk_seed message_digest node_height node_index counter)
    in Hsum, Hsome, Hnone, Hlen, Hle |- *.
  clearbody indexes.

  (* sum = 0 *)
  forward.
  forward_for_simple_bound 32
    (EX j : Z,
      PROP ()
      LOCAL (temp _sum (Vint (Int.repr (Z.of_nat (sumn (take (Z.to_nat j) indexes)))));
             lvar _hashed (tarray tuchar 16) v_hashed;
             temp _indexes i_ptr)
      SEP (data_at sh_i (tarray tuchar 32) (index_vals indexes) i_ptr;
           data_at Tsh (tarray tuchar 16)
             (vals (H_grind pk_seed (WotsCGrind node_height node_index) message_digest
                      counter)) v_hashed;
           data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
           data_at sh_m (tarray tuchar 32) (vals message_digest) m_ptr)).
  - change (Z.to_nat 0) with 0%nat.
    rewrite take0.
    entailer!.
  - rename H into Hj.
    (* t = indexes[i] *)
    forward.
    { entailer!.
      apply tc_val_Znth_index_vals.
      - lia.
      - apply Hle. }
    rewrite Znth_index_vals by lia.
    (* sum += t *)
    forward.
    rewrite add_repr.
    rewrite <- sumn_take_Z by lia.
    entailer!.
  - rewrite (take_all_Z indexes 32 Hlen).
    forward_if.
    + (* the sum is not the constant: the reference returns None *)
      forward.
      rewrite (Hnone H).
      entailer!.
    + (* the sum is the constant: the reference returns the indexes *)
      forward.
      rewrite (Hsome H).
      entailer!.
Qed.
