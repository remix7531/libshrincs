(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_h_grind: VST body proof for [shrincs_wots_h_grind].

    Assembles the [H_grind] SHA-256 preimage in the 112-byte stack
    buffer [buf], laid out as

      [0,16) pk_seed | [16,64) zeros | [64,74) addr[0,10)
      | [74,106) msg | [106,110) zeros | [110,112) counter (BE),

    one region per stage (a memcpy/memset/byte-store each), re-gathers
    the six slices, hashes the buffer, and copies the 16-byte
    truncation of the digest to [out]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.
Import ListNotations.
Open Scope Z_scope.

Local Opaque to_byte.

Lemma body_shrincs_wots_h_grind : semax_body Vprog Gprog_wots f_shrincs_wots_h_grind shrincs_wots_h_grind_spec.
Proof.
  start_function.
  rename H into Hcntbnd.
  rename H0 into Hmsglen.
  rename H1 into Hpslen.
  change n_bytes with 16 in *.
  change msg_bytes with 32 in *.

  (* ===== Stage 1: buf[0,16) <- pk_seed (memcpy) ===== *)
  (* off = 0 *)
  forward.
  (* Split buf[112] -> [0,16) ++ [16,112). *)
  assert_PROP (field_compatible (Tarray tuchar 112 noattr) nil v_buf) as FC
    by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Tsh 112 16 v_buf) by (auto; lia).
  Intros.
  rewrite (data_at__memory_block Tsh (Tarray tuchar 16 noattr) v_buf).
  Intros.
  rename H into FCbuf16.
  change (sizeof (Tarray tuchar 16 noattr)) with 16.
  rewrite (block_to_vals_eq_Vint pk_seed).
  (* memcpy(buf + 0, pk_seed, N) *)
  forward_call (sh_ps, Tsh, v_buf, ps_ptr, 16, block_ints pk_seed).

  (* ===== Stage 2: buf[16,64) <- zeros (memset) ===== *)
  (* off = 16 *)
  forward.
  (* Split the tail [16,112) -> [16,64) ++ [64,112). *)
  set (p16 := field_address0 (Tarray tuchar 112 noattr) (SUB 16) v_buf).
  assert_PROP (field_compatible (Tarray tuchar 96 noattr) nil p16) as FC2
    by (replace 96 with (112 - 16) by lia; entailer!).
  rewrite (split2_data_at__Tarray_tuchar Tsh 96 48 p16) by (auto; lia).
  Intros.
  rewrite (data_at__memory_block Tsh (Tarray tuchar 48 noattr) p16).
  Intros.
  change (sizeof (Tarray tuchar 48 noattr)) with 48.
  (* memset(buf + 16, 0, PKSEED_PAD) *)
  forward_call (Tsh, p16, 48, Int.repr 0).
  { entailer!.
    unfold p16.
    rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
    reflexivity. }

  (* ===== Stage 3: buf[64,74) <- addr[0,10) (memcpy) ===== *)
  (* off = 64 *)
  forward.
  (* Split the tail [64,112) -> [64,74) ++ [74,112). *)
  set (p64 := field_address0 (Tarray tuchar 96 noattr) (SUB 48) p16).
  assert_PROP (field_compatible (Tarray tuchar 48 noattr) nil p64) as FC3
    by (replace 48 with (96 - 48) by lia; entailer!).
  rewrite (split2_data_at__Tarray_tuchar Tsh 48 10 p64) by (auto; lia).
  Intros.
  rewrite (data_at__memory_block Tsh (Tarray tuchar 10 noattr) p64).
  Intros.
  change (sizeof (Tarray tuchar 10 noattr)) with 10.
  (* Split the 22-byte addr source into [0,10) ++ [10,22). *)
  pose proof (Zlength_adrs_to_vals a) as Hla.
  assert (Hl1 : Zlength (sublist 0 10 (adrs_to_vals a)) = 10)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hl2 : Zlength (sublist 10 22 (adrs_to_vals a)) = 22 - 10)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hsrc10 : sublist 0 10 (adrs_to_vals a)
                   = map Vint (block_ints (firstn 10 (adrs_bytes a)))).
  { rewrite <- block_to_vals_eq_Vint.
    unfold adrs_to_vals.
    rewrite <- block_to_vals_sublist, sublist_adrs_bytes_10.
    reflexivity. }
  assert (Hadr_split : adrs_to_vals a
                       = sublist 0 10 (adrs_to_vals a) ++ sublist 10 22 (adrs_to_vals a)).
  { rewrite <- (sublist_split 0 10 22 (adrs_to_vals a)) by lia.
    symmetry.
    apply sublist_same; lia. }
  rewrite Hadr_split.
  rewrite (split2_data_at_Tarray_app 10 22 sh_a tuchar
             (sublist 0 10 (adrs_to_vals a)) (sublist 10 22 (adrs_to_vals a)) a_ptr Hl1 Hl2).
  rewrite Hsrc10.
  clear Hla Hadr_split.
  (* memcpy(buf + 64, addr, GRIND_PREFIX) *)
  forward_call (sh_a, Tsh, p64, a_ptr, 10, block_ints (firstn 10 (adrs_bytes a))).
  { entailer!.
    unfold p64, p16.
    rewrite !field_address0_offset by (apply arr_field_compatible0; [eassumption | lia]).
    rewrite !offset_offset_val.
    reflexivity. }
  cancel.

  (* ===== Stage 4: buf[74,106) <- msg (memcpy) ===== *)
  (* off = 74 *)
  forward.
  (* Split the tail [74,112) -> [74,106) ++ [106,112). *)
  set (p74 := field_address0 (Tarray tuchar 48 noattr) (SUB 10) p64).
  assert_PROP (field_compatible (Tarray tuchar 38 noattr) nil p74) as FC4
    by (replace 38 with (48 - 10) by lia; entailer!).
  rewrite (split2_data_at__Tarray_tuchar Tsh 38 32 p74) by (auto; lia).
  Intros.
  rewrite (data_at__memory_block Tsh (Tarray tuchar 32 noattr) p74).
  Intros.
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  rewrite (block_to_vals_eq_Vint msg).
  (* memcpy(buf + 74, msg, SHRINCS_WOTS_MSG_BYTES) *)
  forward_call (sh_m, Tsh, p74, m_ptr, 32, block_ints msg).
  { entailer!.
    unfold p74, p64, p16.
    rewrite !field_address0_offset by (apply arr_field_compatible0; [eassumption | lia]).
    rewrite !offset_offset_val.
    reflexivity. }

  (* ===== Stage 5: buf[106,110) <- zeros (memset) ===== *)
  (* off = 106 *)
  forward.
  (* Split the tail [106,112) -> [106,110) ++ [110,112). *)
  set (p106 := field_address0 (Tarray tuchar 38 noattr) (SUB 32) p74).
  assert_PROP (field_compatible (Tarray tuchar 6 noattr) nil p106) as FC5
    by (replace 6 with (38 - 32) by lia; entailer!).
  rewrite (split2_data_at__Tarray_tuchar Tsh 6 4 p106) by (auto; lia).
  Intros.
  rewrite (data_at__memory_block Tsh (Tarray tuchar 4 noattr) p106).
  Intros.
  change (sizeof (Tarray tuchar 4 noattr)) with 4.
  (* memset(buf + 106, 0, GRIND_PAD) *)
  forward_call (Tsh, p106, 4, Int.repr 0).
  { entailer!.
    unfold p106, p74, p64, p16.
    rewrite !field_address0_offset by (apply arr_field_compatible0; [eassumption | lia]).
    rewrite !offset_offset_val.
    reflexivity. }

  (* off = 110 *)
  forward.

  (* ===== Stage 6: re-gather the six slices back into buf[112] ===== *)
  set (X1 := map Vint (block_ints pk_seed)).
  set (Z2 := repeat (Vint (Int.repr 0)) (Z.to_nat 48)).
  set (X3 := map Vint (block_ints (firstn 10 (adrs_bytes a)))).
  set (X4 := map Vint (block_ints msg)).
  set (Z5 := repeat (Vint (Int.repr 0)) (Z.to_nat 4)).
  rewrite (data_at__tarray Tsh tuchar (6 - 4)).
  set (U := Zrepeat (default_val tuchar) (6 - 4)).
  (* Slice lengths, feeding the [split2_data_at_Tarray_app] re-folds. *)
  assert (HlX1 : Zlength X1 = 16)
    by (unfold X1; rewrite Zlength_map, Zlength_block_ints; lia).
  assert (HlZ2 : Zlength Z2 = 48)
    by (unfold Z2; rewrite Zlength_repeat; lia).
  assert (HlX3 : Zlength X3 = 10)
    by (unfold X3; rewrite <- Hsrc10; exact Hl1).
  assert (HlX4 : Zlength X4 = 32)
    by (unfold X4; rewrite Zlength_map, Zlength_block_ints; lia).
  assert (HlZ5 : Zlength Z5 = 4)
    by (unfold Z5; rewrite Zlength_repeat; lia).
  assert (HlU : Zlength U = 6 - 4)
    by (unfold U; rewrite Zlength_Zrepeat; lia).
  assert (Hl_Z5U : Zlength (Z5 ++ U) = 38 - 32)
    by (unfold U; rewrite Zlength_app, HlZ5, Zlength_Zrepeat; lia).
  assert (Hl_X4Z5U : Zlength (X4 ++ Z5 ++ U) = 48 - 10)
    by (rewrite Zlength_app, HlX4, Hl_Z5U; lia).
  assert (Hl_X3X4Z5U : Zlength (X3 ++ X4 ++ Z5 ++ U) = 96 - 48)
    by (rewrite Zlength_app, HlX3, Hl_X4Z5U; lia).
  assert (Hl_Z2X3X4Z5U : Zlength (Z2 ++ X3 ++ X4 ++ Z5 ++ U) = 112 - 16)
    by (rewrite Zlength_app, HlZ2, Hl_X3X4Z5U; lia).

  (* [106,110) with [110,112) -> buf[106,112) at p106 *)
  gather_SEP (data_at Tsh (tarray tuchar 4) _ p106)
             (data_at Tsh (tarray tuchar (6 - 4)) _
                (field_address0 (Tarray tuchar 6 noattr) (SUB 4) p106)).
  change (Tarray tuchar 6 noattr) with (tarray tuchar 6).
  rewrite <- (split2_data_at_Tarray_app 4 6 Tsh tuchar Z5 U p106 HlZ5 HlU).
  (* [74,106) with [106,112) -> buf[74,112) at p74 *)
  gather_SEP (data_at Tsh (tarray tuchar 32) _ p74)
             (data_at Tsh (tarray tuchar 6) _ p106).
  unfold p106.
  change (Tarray tuchar 38 noattr) with (tarray tuchar 38).
  change (tarray tuchar 6) with (tarray tuchar (38 - 32)).
  rewrite <- (split2_data_at_Tarray_app 32 38 Tsh tuchar X4 (Z5 ++ U) p74 HlX4 Hl_Z5U).
  (* [64,74) with [74,112) -> buf[64,112) at p64 *)
  gather_SEP (data_at Tsh (tarray tuchar 10) _ p64)
             (data_at Tsh (tarray tuchar 38) _ p74).
  unfold p74.
  change (Tarray tuchar 48 noattr) with (tarray tuchar 48).
  change (tarray tuchar 38) with (tarray tuchar (48 - 10)).
  rewrite <- (split2_data_at_Tarray_app 10 48 Tsh tuchar X3 (X4 ++ Z5 ++ U) p64 HlX3 Hl_X4Z5U).
  (* [16,64) with [64,112) -> buf[16,112) at p16 *)
  gather_SEP (data_at Tsh (tarray tuchar 48) _ p16)
             (data_at Tsh (tarray tuchar 48) _ p64).
  unfold p64.
  change (Tarray tuchar 96 noattr) with (tarray tuchar 96).
  rewrite <- (split2_data_at_Tarray_app 48 96 Tsh tuchar Z2 (X3 ++ X4 ++ Z5 ++ U) p16
                HlZ2 Hl_X3X4Z5U).
  (* [0,16) with [16,112) -> buf[112] at v_buf *)
  gather_SEP (data_at Tsh (tarray tuchar 16) _ v_buf)
             (data_at Tsh (tarray tuchar 96) _ p16).
  unfold p16.
  change (Tarray tuchar 112 noattr) with (tarray tuchar 112).
  change (tarray tuchar 96) with (tarray tuchar (112 - 16)).
  rewrite <- (split2_data_at_Tarray_app 16 112 Tsh tuchar X1 (Z2 ++ X3 ++ X4 ++ Z5 ++ U) v_buf
                HlX1 Hl_Z2X3X4Z5U).
  (* The slice pointers, their [field_compatible]s and the app-length
     facts are dead once the buffer is whole again. *)
  clear dependent p106.
  clear dependent p74.
  clear dependent p64.
  clear dependent p16.
  clear FC FCbuf16.
  clear HlU Hl_Z5U Hl_X4Z5U Hl_X3X4Z5U Hl_Z2X3X4Z5U.

  (* ===== Stage 7: buf[110,112) <- big-endian counter (two stores) ===== *)
  (* buf[110] = (uint8_t)(counter >> 8) *)
  forward.
  (* buf[111] = (uint8_t)(counter) *)
  forward.

  (* ===== Stage 8: fold buf into block_to_vals of the SHA-256 preimage ===== *)
  rewrite !Int.zero_ext_idem by lia.
  change (16 + (48 + (10 + (32 + (4 + 1))))) with 111.
  change (16 + (48 + (10 + (32 + 4)))) with 110.
  pose proof (counter_bytes_eq' counter ltac:(lia)) as Hcnt.
  (* The two stores replace exactly the two Vundef tail cells. *)
  assert (Hstruct : forall d0 d1 : val,
            upd_Znth 111 (upd_Znth 110 (X1 ++ Z2 ++ X3 ++ X4 ++ Z5 ++ U) d0) d1
            = X1 ++ Z2 ++ X3 ++ X4 ++ Z5 ++ [d0; d1]).
  { intros d0 d1. unfold U. list_solve. }
  rewrite Hstruct.
  (* Fold each chunk to block_to_vals of its preimage component. *)
  assert (Heq : X1 ++ Z2 ++ X3 ++ X4 ++ Z5 ++
                [Vint (Int.zero_ext 8 (Int.shru (Int.repr counter) (Int.repr 8)));
                 Vint (Int.zero_ext 8 (Int.repr counter))]
              = block_to_vals
                  (pk_seed ++ zeros 48 ++ firstn 10 (adrs_bytes a)
                   ++ msg ++ zeros 4 ++ to_byte counter 2)).
  { rewrite !block_to_vals_app.
    rewrite <- Hcnt.
    unfold X1, Z2, X3, X4, Z5.
    rewrite <- !block_to_vals_eq_Vint.
    rewrite !zeros_to_vals.
    reflexivity. }
  rewrite Heq.
  clear Hcnt Hstruct Heq HlX1 HlZ2 HlX3 HlX4 HlZ5 Z2 Z5 U.

  (* ===== Stage 9: sha256(hash, buf, sizeof buf) ===== *)
  forward_call sha256_block_spec_sub (v_hash, v_buf, 112,
                pk_seed ++ zeros 48 ++ firstn 10 (adrs_bytes a)
                ++ msg ++ zeros 4 ++ to_byte counter 2,
                Tsh, Tsh).
  { rewrite !Zlength_app.
    rewrite <- sublist_adrs_bytes_10.
    rewrite Zlength_sublist by (rewrite ?Zlength_adrs_bytes; lia).
    unfold zeros.
    rewrite <- !to_byte_0_zeros.
    rewrite !to_byte_Zlength.
    unfold sha256_max_input_len.
    lia. }

  (* ===== Stage 10: memcpy(out, hash, N) -- truncate the digest ===== *)
  set (sha := sha256' (pk_seed ++ zeros 48 ++ firstn 10 (adrs_bytes a)
                      ++ msg ++ zeros 4 ++ to_byte counter 2)).
  (* Split the 32-byte digest into [0,16) ++ [16,32). *)
  assert (Hlsha : Zlength (block_to_vals sha) = 32)
    by (unfold sha; rewrite block_to_vals_length, SHA256_Zlength; reflexivity).
  assert (Hh1 : Zlength (sublist 0 16 (block_to_vals sha)) = 16)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hh2 : Zlength (sublist 16 32 (block_to_vals sha)) = 32 - 16)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hhsrc : sublist 0 16 (block_to_vals sha) = block_to_vals (firstn 16 sha))
    by (rewrite <- block_to_vals_sublist, sublist_firstn; reflexivity).
  assert (Hhsplit : block_to_vals sha
                    = sublist 0 16 (block_to_vals sha) ++ sublist 16 32 (block_to_vals sha)).
  { rewrite <- (sublist_split 0 16 32 (block_to_vals sha)) by lia.
    symmetry.
    apply sublist_same; lia. }
  rewrite Hhsplit.
  rewrite (split2_data_at_Tarray_app 16 32 Tsh tuchar
             (sublist 0 16 (block_to_vals sha)) (sublist 16 32 (block_to_vals sha)) v_hash Hh1 Hh2).
  rewrite Hhsrc.
  rewrite (block_to_vals_eq_Vint (firstn 16 sha)).
  rewrite (data_at__memory_block sh_o (tarray tuchar 16) out_ptr).
  Intros.
  change (sizeof (tarray tuchar 16)) with 16.
  (* memcpy(out, hash, N) *)
  forward_call (Tsh, sh_o, out_ptr, v_hash, 16, block_ints (firstn 16 sha)).

  (* ===== Postcondition ===== *)
  (* [out] holds the truncated digest [H_grind = trunc16 (SHA256 preimage)]. *)
  assert (Hout : H_grind pk_seed a msg counter = firstn 16 sha)
    by (unfold H_grind, trunc16, sha; reflexivity).
  subst X1 X3 X4.
  rewrite <- Hsrc10.
  rewrite <- !block_to_vals_eq_Vint.
  rewrite Hout.
  (* Re-gather the read-only [addr] back to its 22-byte form. *)
  gather_SEP (data_at sh_a (tarray tuchar 10) _ a_ptr)
             (data_at sh_a (tarray tuchar (22 - 10)) _
                (field_address0 (tarray tuchar 22) (SUB 10) a_ptr)).
  rewrite <- (split2_data_at_Tarray_app 10 22 sh_a tuchar
                (sublist 0 10 (adrs_to_vals a)) (sublist 10 22 (adrs_to_vals a)) a_ptr Hl1 Hl2).
  entailer!.
  (* Re-gather the two halves of [hash] for the stack frame. *)
  assert_PROP (field_compatible (tarray tuchar 32) nil v_hash) as FCv by entailer!.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (block_to_vals (firstn 16 sha)) v_hash).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar (32 - 16))
               (sublist 16 32 (block_to_vals sha))
               (field_address0 (tarray tuchar 32) (SUB 16) v_hash)).
  rewrite (split2_data_at__Tarray_tuchar Tsh 32 16 v_hash) by (auto; lia).
  cancel.
  (* Fold the split [addr] slices back to [adrs_to_vals a]. *)
  rewrite sublist_rejoin by (rewrite ?Zlength_adrs_to_vals; lia).
  rewrite sublist_same by (rewrite ?Zlength_adrs_to_vals; lia).
  apply derives_refl.
Qed.
