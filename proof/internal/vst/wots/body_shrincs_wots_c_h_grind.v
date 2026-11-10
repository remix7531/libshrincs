(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_h_grind: VST body proof for [shrincs_wots_c_h_grind].

    Packs the [WotsCGrind] address, then assembles the [H_grind] SHA-256
    preimage from the left in the 112-byte stack buffer [buf]:

      [0,16) pk_seed | [16,64) zeros | [64,74) addr[0,10)
      | [74,106) digest | [106,110) zeros | [110,112) counter (BE),

    five appends through [shrincs_memcpy] and [shrincs_memset] and two
    byte stores. It hashes the buffer and copies the first 16 bytes of
    the digest to [out]. [H_grind_preimage] says that this is [H_grind]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog contract.buffer theory.values.
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_wots_c_h_grind :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_h_grind shrincs_wots_c_h_grind_spec.
Proof.
  start_function.
  (* The pointer facts let [forward_call] see that a buffer's own pointer
     is its offset 0. *)
  assert_PROP (isptr v_buf) as Pbuf by entailer!.
  assert_PROP (isptr v_addr) as Paddr by entailer!.
  assert_PROP (isptr v_hash) as Phash by entailer!.
  assert_PROP (isptr ps_ptr) as Pps by entailer!.
  assert_PROP (isptr d_ptr) as Pd by entailer!.
  assert_PROP (isptr out_ptr) as Pout by entailer!.

  (* shrincs_adrs_pack(addr, node_height, node_index, SF_WOTS_C_GRIND, 0, 0, 0) *)
  forward_call (v_addr, node_height, node_index, SF_WOTS_C_GRIND,
                uint U32 0, uint U32 0, uint U32 0, Tsh).
  set (adrs := pack node_height node_index SF_WOTS_C_GRIND (uint U32 0) (uint U32 0) (uint U32 0)).
  rewrite (data_at__filled Tsh 112 v_buf).

  (* memcpy(buf, pk_seed, N) *)
  forward_call memcpy_fill_sub
    (Tsh, sh_ps, v_buf, ps_ptr, v_buf, ps_ptr, 112, 16, 0, 0, 16,
     @nil UInt8, tval pk_seed, tval pk_seed).
  { bytes_side_conditions. }
  change (cat nil (tval pk_seed)) with (tval pk_seed).

  (* memset(buf + GRIND_AT_PAD, 0, 48) *)
  forward_call memset_fill_sub
    (Tsh, v_buf, offset_val 16 v_buf, 112, 16, 48, tval pk_seed, tval (zeros 48)).
  { bytes_side_conditions. }

  (* memcpy(buf + GRIND_AT_ADRS, addr, GRIND_ADRS_PREFIX): height, index and type *)
  forward_call memcpy_fill_sub
    (Tsh, Tsh, v_buf, v_addr, offset_val 64 v_buf, v_addr, 112, 22, 64, 0, 10,
     cat (tval pk_seed) (tval (zeros 48)), tval adrs, tval (slice adrs 0 10)).
  { bytes_side_conditions. }

  (* memcpy(buf + GRIND_AT_DIGEST, digest, 32) *)
  forward_call memcpy_fill_sub
    (Tsh, sh_d, v_buf, d_ptr, offset_val 74 v_buf, d_ptr, 112, 32, 74, 0, 32,
     cat (cat (tval pk_seed) (tval (zeros 48))) (tval (slice adrs 0 10)),
     tval digest, tval digest).
  { bytes_side_conditions. }

  (* memset(buf + GRIND_AT_ZEROS, 0, GRIND_PAD) *)
  forward_call memset_fill_sub
    (Tsh, v_buf, offset_val 106 v_buf, 112, 106, 4,
     cat (cat (cat (tval pk_seed) (tval (zeros 48))) (tval (slice adrs 0 10))) (tval digest),
     tval (zeros 4)).
  { bytes_side_conditions. }

  (* ===== The two bytes of the counter, stored one after the other ===== *)
  set (written := cat (cat (cat (cat (tval pk_seed) (tval (zeros 48)))
                                (tval (slice adrs 0 10))) (tval digest)) (tval (zeros 4))).
  assert (Hwritten : Zlength written = 110) by (unfold written; bytes_length).
  unfold filled.
  (* buf[GRIND_AT_COUNTER] = (uint8_t)(counter >> 8) *)
  forward.
  (* buf[GRIND_AT_COUNTER + 1] = (uint8_t)(counter) *)
  forward.
  rewrite counter_hi_byte.
  rewrite counter_lo_byte.
  set (b0 := wrepr U8 (wunsigned counter / 256 ^ 1)).
  set (b1 := wrepr U8 (wunsigned counter / 256 ^ 0)).
  rewrite (filled_upd 112 written b0 110) by (first [exact Hwritten | lia]).
  rewrite (filled_upd 112 (rcons written b0) b1 (110 + 1)) by (rewrite ?Zlength_rcons; lia).
  fold (filled Tsh 112 (rcons (rcons written b0) b1) v_buf).

  (* shrincs_sha256(hash, buf, GRIND_BYTES) *)
  forward_call sha256_fill_sub
    (v_hash, v_buf, 112, 112, rcons (rcons written b0) b1, Tsh, Tsh).
  { bytes_side_conditions. }

  (* memcpy(out, hash, N): the digest truncated to its first 16 bytes *)
  rewrite (data_at__filled sh_o 16 out_ptr).
  forward_call memcpy_fill_sub
    (sh_o, Tsh, out_ptr, v_hash, out_ptr, v_hash, 16, 32, 0, 0, 16,
     @nil UInt8,
     tval (sha256 (rcons (rcons written b0) b1)),
     tval (H_grind pk_seed (WotsCGrind node_height node_index) digest counter)).
  { rewrite H_grind_preimage.
    bytes_side_conditions. }

  (* ===== Postcondition: [out] is full, and the three locals go back to the stack ===== *)
  change (cat nil (tval (H_grind pk_seed (WotsCGrind node_height node_index) digest counter)))
    with (tval (H_grind pk_seed (WotsCGrind node_height node_index) digest counter)).
  rewrite (filled_full sh_o 16
             (H_grind pk_seed (WotsCGrind node_height node_index) digest counter) out_ptr)
    by exact (Zlength_tuple 16 _).
  sep_apply (filled_data_at_ Tsh 112 (rcons (rcons written b0) b1) v_buf).
  entailer!.
Qed.
