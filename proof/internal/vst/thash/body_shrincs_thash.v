(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_thash: VST body proof for the general [shrincs_thash].

    Zeros a 598-byte scratch [buf], then assembles the SHA-256 preimage
    [pk_seed(16) || zeros(48) || ADRS(22) || msg(msglen)] into
    [buf[0 .. 86+msglen)] (three [memcpy]s, the [16,64) gap left zero by
    the [memset]), hashes [buf[0 .. 86+msglen)] and copies the first 16
    bytes to [out] -- i.e. [out := thash pk_seed A msg].  [msg] is a
    separate readable buffer (no aliasing with [out]). *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.
From Shrincs.clight Require Import thash.
Import ListNotations.
Open Scope Z_scope.

Lemma body_shrincs_thash : semax_body Vprog Gprog_thash f_shrincs_thash shrincs_thash_spec.
Proof.
  start_function.
  rename H into Hpslen.
  rename H0 into Hmsglen.
  rename H1 into Hmsgbnd.
  unfold n_bytes in *.
  change (Z.of_nat n) with 16 in *.

  (* ===== [prefix := 86]; [memset(buf, 0, 598)] zeros the scratch buffer ===== *)
  forward.
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 598 noattr) v_buf).
  change (sizeof (Tarray tuchar 598 noattr)) with 598.
  forward_call (Tsh, v_buf, 598, Int.repr 0).

  (* ===== Carve the zeroed buffer into the four preimage regions + tail =====
     [0,16) pk_seed | [16,64) zeros(48) | [64,86) ADRS | [86,86+msglen) msg |
     [86+msglen,598) unused zero tail.  The [16,64) gap stays zero (the
     [memset]); the other three regions get overwritten by [memcpy].  The
     [repeat] splits are the shared [repeat_Vint0_Zsplit]
     ([contract.lemmas.data_at]). *)
  assert (Hdecomp : repeat (Vint (Int.repr 0)) (Z.to_nat 598)
    = repeat (Vint (Int.repr 0)) (Z.to_nat 16) ++ repeat (Vint (Int.repr 0)) (Z.to_nat 48)
      ++ repeat (Vint (Int.repr 0)) (Z.to_nat 22) ++ repeat (Vint (Int.repr 0)) (Z.to_nat msglen)
      ++ repeat (Vint (Int.repr 0)) (Z.to_nat (512 - msglen))).
  { replace 598 with (16 + (48 + (22 + (msglen + (512 - msglen))))) by lia.
    rewrite !repeat_Vint0_Zsplit by lia.
    reflexivity. }
  rewrite Hdecomp.
  clear Hdecomp.
  set (R0 := repeat (Vint (Int.repr 0)) (Z.to_nat 16)).
  set (R1 := repeat (Vint (Int.repr 0)) (Z.to_nat 48)).
  set (R2 := repeat (Vint (Int.repr 0)) (Z.to_nat 22)).
  set (R3 := repeat (Vint (Int.repr 0)) (Z.to_nat msglen)).
  set (R4 := repeat (Vint (Int.repr 0)) (Z.to_nat (512 - msglen))).
  assert (HR0 : Zlength R0 = 16) by (apply Zlength_repeat; lia).
  assert (HR1 : Zlength R1 = 48) by (apply Zlength_repeat; lia).
  assert (HR2 : Zlength R2 = 22) by (apply Zlength_repeat; lia).
  assert (HR3 : Zlength R3 = msglen) by (apply Zlength_repeat; lia).
  assert (HR4 : Zlength R4 = 512 - msglen) by (apply Zlength_repeat; lia).

  (* ===== Split off [0,16); memcpy(buf, pk_seed, 16) =====
     The field-compatibility facts ([FCbuf]/[FC16]/..) are recorded for the
     full sub-arrays so [field_address0_offset] can resolve the nested
     [memcpy] destination pointers. *)
  assert_PROP (field_compatible (tarray tuchar 598) nil v_buf) as FCbuf by entailer!.
  assert (Ht1 : Zlength (R1++R2++R3++R4) = 598 - 16) by (rewrite !Zlength_app, HR1, HR2, HR3, HR4; lia).
  rewrite (split2_data_at_Tarray_app 16 598 Tsh tuchar R0 (R1++R2++R3++R4) v_buf HR0 Ht1).
  change (598 - 16) with 582.
  set (p16 := field_address0 (tarray tuchar 598) (SUB 16) v_buf).
  assert_PROP (field_compatible (tarray tuchar 582) nil p16) as FC16 by entailer!.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) R0 v_buf).
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 16 noattr) v_buf).
  change (sizeof (Tarray tuchar 16 noattr)) with 16.
  rewrite (block_to_vals_eq_Vint pk_seed).
  forward_call (sh_ps, Tsh, v_buf, ps_ptr, 16, block_ints pk_seed).

  (* ===== Split off [16,64) (zeros) and [64,86); memcpy(buf+64, addr, 22) ===== *)
  assert (Ht2 : Zlength (R2++R3++R4) = 582 - 48) by (rewrite !Zlength_app, HR2, HR3, HR4; lia).
  rewrite (split2_data_at_Tarray_app 48 582 Tsh tuchar R1 (R2++R3++R4) p16 HR1 Ht2).
  change (582 - 48) with 534.
  set (p64 := field_address0 (tarray tuchar 582) (SUB 48) p16).
  assert_PROP (field_compatible (tarray tuchar 534) nil p64) as FC64 by entailer!.
  assert (Ht3 : Zlength (R3++R4) = 534 - 22) by (rewrite !Zlength_app, HR3, HR4; lia).
  rewrite (split2_data_at_Tarray_app 22 534 Tsh tuchar R2 (R3++R4) p64 HR2 Ht3).
  change (534 - 22) with 512.
  set (p86 := field_address0 (tarray tuchar 534) (SUB 22) p64).
  assert_PROP (field_compatible (tarray tuchar 512) nil p86) as FC86 by entailer!.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 22) R2 p64).
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 22 noattr) p64).
  change (sizeof (Tarray tuchar 22 noattr)) with 22.
  unfold t_addr, adrs_to_vals.
  rewrite (block_to_vals_eq_Vint (adrs_bytes A)).
  forward_call (sh_a, Tsh, p64, a_ptr, 22, block_ints (adrs_bytes A)).
  { entailer!.
    unfold p64, p16.
    rewrite !field_address0_offset by auto with field_compatible.
    destruct v_buf; try contradiction.
    simpl.
    rewrite Ptrofs.add_assoc.
    reflexivity. }

  (* ===== Split off [86,86+msglen); memcpy(buf+86, msg, msglen) ===== *)
  rewrite (split2_data_at_Tarray_app msglen 512 Tsh tuchar R3 R4 p86 HR3 HR4).
  set (ptail := field_address0 (tarray tuchar 512) (SUB msglen) p86).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar msglen) R3 p86).
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar msglen noattr) p86).
  replace (sizeof (Tarray tuchar msglen noattr)) with msglen by (simpl; lia).
  rewrite (block_to_vals_eq_Vint msg).
  forward_call (sh_m, Tsh, p86, m_ptr, msglen, block_ints msg).
  { entailer!.
    unfold p86, p64, p16.
    rewrite !field_address0_offset by auto with field_compatible.
    destruct v_buf; try contradiction.
    simpl.
    rewrite !Ptrofs.add_assoc.
    reflexivity. }

  (* ===== Re-gather the whole 598-byte buffer (reusing the original split
     sizes so the [field_address0] pointers line up) ===== *)
  assert (Hpkv : Zlength (map Vint (block_ints pk_seed)) = 16)
    by (rewrite Zlength_map, Zlength_block_ints; exact Hpslen).
  assert (Hadrv : Zlength (map Vint (block_ints (adrs_bytes A))) = 22)
    by (rewrite Zlength_map, Zlength_block_ints, Zlength_adrs_bytes; reflexivity).
  assert (Hmsgv : Zlength (map Vint (block_ints msg)) = msglen)
    by (rewrite Zlength_map, Zlength_block_ints; exact Hmsglen).
  gather_SEP (data_at Tsh (tarray tuchar msglen) (map Vint (block_ints msg)) p86)
             (data_at Tsh (tarray tuchar (512 - msglen)) R4 ptail).
  unfold ptail.
  rewrite <- (split2_data_at_Tarray_app msglen 512 Tsh tuchar
               (map Vint (block_ints msg)) R4 p86 Hmsgv HR4).
  assert (Hrest2 : Zlength (map Vint (block_ints msg) ++ R4) = 534 - 22)
    by (rewrite Zlength_app, Hmsgv, HR4; lia).
  gather_SEP (data_at Tsh (tarray tuchar 22) _ p64) (data_at Tsh (tarray tuchar 512) _ p86).
  unfold p86.
  rewrite <- (split2_data_at_Tarray_app 22 534 Tsh tuchar
               (map Vint (block_ints (adrs_bytes A))) (map Vint (block_ints msg) ++ R4) p64 Hadrv Hrest2).
  assert (Hrest3 : Zlength (map Vint (block_ints (adrs_bytes A)) ++ map Vint (block_ints msg) ++ R4) = 582 - 48)
    by (rewrite !Zlength_app, Hadrv, Hmsgv, HR4; lia).
  gather_SEP (data_at Tsh (tarray tuchar 48) _ p16) (data_at Tsh (tarray tuchar 534) _ p64).
  unfold p64.
  rewrite <- (split2_data_at_Tarray_app 48 582 Tsh tuchar R1
               (map Vint (block_ints (adrs_bytes A)) ++ map Vint (block_ints msg) ++ R4) p16 HR1 Hrest3).
  assert (Hrest4 : Zlength (R1 ++ map Vint (block_ints (adrs_bytes A)) ++ map Vint (block_ints msg) ++ R4) = 598 - 16)
    by (rewrite !Zlength_app, HR1, Hadrv, Hmsgv, HR4; lia).
  gather_SEP (data_at Tsh (tarray tuchar 16) _ v_buf) (data_at Tsh (tarray tuchar 582) _ p16).
  unfold p16.
  rewrite <- (split2_data_at_Tarray_app 16 598 Tsh tuchar (map Vint (block_ints pk_seed))
               (R1 ++ map Vint (block_ints (adrs_bytes A)) ++ map Vint (block_ints msg) ++ R4) v_buf Hpkv Hrest4).
  clear Hpkv Hadrv Hmsgv Hrest2 Hrest3 Hrest4 Ht1 Ht2 Ht3 HR0 HR1 HR2 HR3 FC16 FC64 FC86.

  (* ===== Fold buf[0..86+msglen) to [block_to_vals] of the SHA-256 preimage,
     leaving the zero tail [R4] behind ([change reptype -> val] because the
     [split] lemmas typed the wire content at [reptype tuchar]). ===== *)
  set (Preim := pk_seed ++ zeros 48 ++ adrs_bytes A ++ msg).
  assert (Hpre : map Vint (block_ints pk_seed) ++ R1 ++ map Vint (block_ints (adrs_bytes A)) ++ map Vint (block_ints msg)
               = block_to_vals Preim).
  { unfold Preim.
    rewrite !block_to_vals_app.
    rewrite <- (block_to_vals_eq_Vint pk_seed).
    rewrite <- (block_to_vals_eq_Vint (adrs_bytes A)).
    rewrite <- (block_to_vals_eq_Vint msg).
    unfold R1.
    change (Z.to_nat 48) with 48%nat.
    rewrite (zeros_to_vals 48).
    reflexivity. }
  assert (Hcontent : map Vint (block_ints pk_seed) ++ R1 ++ map Vint (block_ints (adrs_bytes A)) ++ map Vint (block_ints msg) ++ R4
                   = block_to_vals Preim ++ R4).
  { rewrite <- Hpre.
    rewrite <- !app_assoc.
    reflexivity. }
  change (reptype tuchar) with val in *.
  rewrite Hcontent.
  assert (Hz48 : Zlength (zeros 48) = 48) by (unfold zeros; rewrite Zlength_correct, repeat_length; reflexivity).
  assert (HpreLen : Zlength (block_to_vals Preim) = 86 + msglen).
  { rewrite block_to_vals_length.
    unfold Preim.
    rewrite !Zlength_app, Zlength_adrs_bytes, Hz48, Hpslen, Hmsglen.
    lia. }
  assert (HR4' : Zlength R4 = 598 - (86 + msglen)) by (rewrite HR4; lia).

  (* ===== [sha256(hash, buf, 86+msglen)] over the assembled preimage ===== *)
  rewrite (split2_data_at_Tarray_app (86+msglen) 598 Tsh tuchar (block_to_vals Preim) R4 v_buf HpreLen HR4').
  forward_call sha256_block_spec_sub (v_hash, v_buf, 86 + msglen, Preim, Tsh, Tsh).
  { cancel. }
  { split; [rewrite <- block_to_vals_length; exact HpreLen | unfold sha256_max_input_len; lia]. }

  (* ===== Split hash[32] at 16; truncating memcpy(out, hash, 16) ===== *)
  assert_PROP (field_compatible (Tarray tuchar 32 noattr) nil v_hash) as FCh by entailer!.
  assert (HlV : Zlength (block_to_vals (sha256' Preim)) = 32) by (rewrite block_to_vals_length, SHA256_Zlength; reflexivity).
  assert (Hs1 : Zlength (sublist 0 16 (block_to_vals (sha256' Preim))) = 16) by (rewrite Zlength_sublist by lia; lia).
  assert (Hs2 : Zlength (sublist 16 32 (block_to_vals (sha256' Preim))) = 32 - 16) by (rewrite Zlength_sublist by lia; lia).
  assert (Hsplit : block_to_vals (sha256' Preim) = sublist 0 16 (block_to_vals (sha256' Preim)) ++ sublist 16 32 (block_to_vals (sha256' Preim)))
    by list_solve.
  rewrite Hsplit.
  rewrite (split2_data_at_Tarray_app 16 32 Tsh tuchar (sublist 0 16 (block_to_vals (sha256' Preim))) (sublist 16 32 (block_to_vals (sha256' Preim))) v_hash Hs1 Hs2).
  rewrite <- (block_to_vals_sublist 0 16 (sha256' Preim)).
  rewrite (block_to_vals_eq_Vint (sublist 0 16 (sha256' Preim))).
  sep_apply (data_at__memory_block_cancel sh_o (Tarray tuchar 16 noattr) out_ptr).
  change (sizeof (Tarray tuchar 16 noattr)) with 16.
  forward_call (Tsh, sh_o, out_ptr, v_hash, 16, block_ints (sublist 0 16 (sha256' Preim))).

  (* ===== Postcondition: fold [out] to [thash], the reads back to their
     inputs, and re-merge the stack locals ([hash]/[buf]). ===== *)
  assert (Hthash : sublist 0 16 (sha256' Preim) = thash pk_seed A msg)
    by (unfold Preim, thash, trunc16; rewrite sublist_firstn; reflexivity).
  rewrite <- (block_to_vals_eq_Vint (sublist 0 16 (sha256' Preim))).
  rewrite Hthash.
  rewrite <- (block_to_vals_eq_Vint pk_seed).
  rewrite <- (block_to_vals_eq_Vint msg).
  unfold adrs_to_vals, t_addr.
  rewrite <- (block_to_vals_eq_Vint (adrs_bytes A)).
  entailer!.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (block_to_vals (thash pk_seed A msg)) v_hash).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar (32 - 16)) (sublist 16 32 (block_to_vals (sha256' Preim))) (field_address0 (tarray tuchar 32) (SUB 16) v_hash)).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar (86 + Zlength msg)) (block_to_vals Preim) v_buf).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar (598 - (86 + Zlength msg))) R4 (field_address0 (tarray tuchar 598) (SUB (86 + Zlength msg)) v_buf)).
  unfold tarray.
  rewrite (split2_data_at__Tarray_tuchar Tsh 32 16 v_hash ltac:(lia) Pv_hash FCh).
  rewrite (split2_data_at__Tarray_tuchar Tsh 598 (86 + Zlength msg) v_buf ltac:(lia) Pv_buf FCbuf).
  cancel.
Qed.
