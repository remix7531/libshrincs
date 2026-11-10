(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_thash: VST body proof for the general [shrincs_thash].

    Assembles the SHA-256 preimage
    [pk_seed(16) || zeros(48) || ADRS(22) || msg(msglen)] from the left
    in a 598-byte scratch [buf], hashes its [86 + msglen] bytes and copies
    the first 16 bytes of the digest to [out], which is [th pk_seed adrs msg].

    [buf] is a [filled] buffer throughout ([contract.buffer]): each of the
    four writes appends to it, and the hash reads what is written. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog contract.buffer theory.values.
From Shrincs.internal.vst Require Import shape.
From Shrincs.clight Require Import thash.
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_thash : semax_body Vprog Gprog_thash f_shrincs_thash shrincs_thash_spec.
Proof.
  start_function.
  rename H into Hmsg.
  rename H0 into Hbound.
  assert (Hmsglen : 0 <= msglen) by (rewrite <- Hmsg; apply Zlength_nonneg).
  (* The pointer facts let [forward_call] see that a buffer's own pointer
     is its offset 0. *)
  assert_PROP (isptr v_buf) as Pbuf by entailer!.
  assert_PROP (isptr ps_ptr) as Pps by entailer!.
  assert_PROP (isptr a_ptr) as Pa by entailer!.
  assert_PROP (isptr m_ptr) as Pm by entailer!.
  assert_PROP (isptr out_ptr) as Pout by entailer!.
  assert_PROP (isptr v_hash) as Phash by entailer!.
  rewrite (data_at__filled Tsh 598 v_buf).

  (* memcpy(buf, pk_seed, 16) *)
  forward_call memcpy_fill_sub
    (Tsh, sh_ps, v_buf, ps_ptr, v_buf, ps_ptr, 598, 16, 0, 0, 16,
     @nil UInt8, tval pk_seed, tval pk_seed).
  { split.
    - exact (Zlength_tuple 16 pk_seed).
    - apply sublist_tuple.
      reflexivity. }
  change (cat nil (tval pk_seed)) with (tval pk_seed).

  (* memset(buf + 16, 0, 48) *)
  forward_call memset_fill_sub
    (Tsh, v_buf, offset_val 16 v_buf, 598, 16, 48, tval pk_seed, tval (zeros 48)).
  { exact (Zlength_tuple 16 pk_seed). }

  (* memcpy(buf + 64, addr, 22) *)
  forward_call memcpy_fill_sub
    (Tsh, sh_a, v_buf, a_ptr, offset_val 64 v_buf, a_ptr, 598, 22, 64, 0, 22,
     cat (tval pk_seed) (tval (zeros 48)), tval adrs, tval adrs).
  { split3.
    - bytes_length.
    - exact (Zlength_tuple 22 adrs).
    - apply sublist_tuple.
      reflexivity. }

  (* memcpy(buf + 86, msg, msglen) *)
  forward_call memcpy_fill_sub
    (Tsh, sh_m, v_buf, m_ptr, offset_val 86 v_buf, m_ptr, 598, msglen, 86, 0, msglen,
     cat (cat (tval pk_seed) (tval (zeros 48))) (tval adrs), msg, msg).
  { split.
    - bytes_length.
    - apply sublist_same.
      + reflexivity.
      + symmetry.
        exact Hmsg. }

  (* sha256(hash, buf, 86 + msglen), over the preimage in the specification's bracketing *)
  rewrite <- !catA.
  forward_call sha256_fill_sub
    (v_hash, v_buf, 598, 86 + msglen,
     cat (tval pk_seed) (cat (tval (zeros 48)) (cat (tval adrs) msg)), Tsh, Tsh).
  { bytes_length. }

  (* memcpy(out, hash, 16): the digest truncated to its first 16 bytes *)
  rewrite (data_at__filled sh_o 16 out_ptr).
  forward_call memcpy_fill_sub
    (sh_o, Tsh, out_ptr, v_hash, out_ptr, v_hash, 16, 32, 0, 0, 16,
     @nil UInt8,
     tval (sha256 (cat (tval pk_seed) (cat (tval (zeros 48)) (cat (tval adrs) msg)))),
     tval (th pk_seed adrs msg)).
  { split.
    - exact (Zlength_tuple 32 _).
    - apply (sublist_slice _ 0 16).
      + lia.
      + rewrite Zlength_tuple.
        rep_lia. }

  (* ===== Postcondition: [out] is full, and the two locals go back to the stack ===== *)
  change (cat nil (tval (th pk_seed adrs msg))) with (tval (th pk_seed adrs msg)).
  rewrite (filled_full sh_o 16 (th pk_seed adrs msg) out_ptr) by exact (Zlength_tuple 16 _).
  sep_apply (filled_data_at_ Tsh 598
               (cat (tval pk_seed) (cat (tval (zeros 48)) (cat (tval adrs) msg))) v_buf).
  entailer!.
Qed.
