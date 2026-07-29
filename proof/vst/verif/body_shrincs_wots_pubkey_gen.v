(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_pubkey_gen: VST body proof for [shrincs_wots_pubkey_gen]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import model.wots.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* Keep the port's hash and the 32-fold chain folded: the closing [cancel]'s
   "close by conversion" would otherwise delta-unfold the whole chain map at
   [Qed] (every tactic runs fast; only [Qed] blows up). *)
Local Opaque to_byte derive_sk wc_chain shrincs.T_sf.

Lemma body_shrincs_wots_pubkey_gen : semax_body Vprog Gprog f_shrincs_wots_pubkey_gen shrincs_wots_pubkey_gen_spec.
Proof.
  start_function.
  change pk_bytes with 16.
  change seed_bytes with 16.
  forward_for_simple_bound 32
    (EX i : Z, EX b : adrs,
      PROP (adrs_struct_eq b a; 0 < i -> payload_a_z b = 0)
      LOCAL (temp _pk pk_ptr; temp _sk_seed sk_ptr;
             temp _pk_seed ps_ptr; temp _addr a_ptr;
             lvar _ends (tarray tuchar 512) v_ends)
      SEP (data_at Tsh (tarray tuchar 512)
             (blocks_to_vals (map (pkgen_block sk_seed pk_seed a)
                                  (seq 0 (Z.to_nat i)))
              ++ Zrepeat Vundef (512 - 16 * i)) v_ends;
           data_at_ sh_pk (tarray tuchar 16) pk_ptr;
           data_at sh_sk (tarray tuchar 16) (block_to_vals sk_seed) sk_ptr;
           data_at sh_ps (tarray tuchar 16) (block_to_vals pk_seed) ps_ptr;
           data_at sh_a t_addr (adrs_to_vals b) a_ptr)).
  - (* loop entry: the caller's address [a] is trivially prefix-equal to itself *)
    Exists a.
    entailer!!.
    apply adrs_struct_eq_refl.
  - (* loop body *)
    assert_PROP (field_compatible (tarray tuchar 512) nil v_ends
                 /\ Zlength (block_to_vals sk_seed) = 16
                 /\ Zlength (block_to_vals pk_seed) = 16)
      as Hpure by entailer!.
    destruct Hpure as [Hfc_ends [Hlss Hlps]].
    rewrite block_to_vals_length in Hlss, Hlps.

    (* _tip = ends + i*16 *)
    forward.

    (* Split ends into FILLED (16*i) | MID (16) | TAIL (512-16*(i+1)) *)
    set (FILLED := blocks_to_vals
                     (map (pkgen_block sk_seed pk_seed a)
                          (seq 0 (Z.to_nat i)))).
    assert (HlFILLED : Zlength FILLED = 16 * i).
    { subst FILLED.
      rewrite Zlength_blocks_to_vals_map_seq
        by (intros k; apply pkgen_block_Zlength).
      lia. }
    erewrite (split2_data_at_Tarray_app (16*i) 512 Tsh tuchar
                FILLED (Zrepeat Vundef (512 - 16*i)))
      by (try exact HlFILLED; split_sc).
    replace (512 - 16*i) with (16 + (512 - 16*(i+1))) by lia.
    rewrite <- Zrepeat_app by lia.
    erewrite (split2_data_at_Tarray_app 16 _ Tsh tuchar
                (Zrepeat Vundef 16) (Zrepeat Vundef (512 - 16*(i+1))))
      by split_sc.
    set (pMID := field_address0 (tarray tuchar 512) (SUB (16*i)) v_ends).
    Intros.

    (* Convert MID slot to data_at_ *)
    replace (Zrepeat (A:=val) Vundef 16)
      with (default_val (tarray tuchar 16)) by reflexivity.
    rewrite <- data_at__eq.

    (* shrincs_wots_chain_from_seed(ends + i*16, i, W - 1, sk_seed, pk_seed, addr) --
       derive_sk + hash-retype + the chain in one call.  The step count is passed
       as [Z.of_nat w_pred] rather than the literal 15, so the POST lands on
       [pkgen_block]'s own step count with no re-normalisation. *)
    forward_call (pMID, sk_ptr, ps_ptr, a_ptr,
                  i, Z.of_nat w_pred, sk_seed, pk_seed, b,
                  Tsh, sh_sk, sh_ps, sh_a).
    { (* PARAMS slot address *)
      solve_slot_addr_pure pMID Hfc_ends. }
    change n_bytes with 16.

    (* Rewrite the chain result to [pkgen_block sk pk a i]. *)
    rewrite Nat2Z.id.
    rewrite (iter_eq_pkgen_block sk_seed pk_seed a b i H0 ltac:(lia)).

    (* The threaded address after this iteration is structurally equal to a. *)
    Exists (chain_addr_post (shrincs_wots_hash_adrs w_pred_pos b (to_chain32 (Z.to_nat i))) 0%nat w_pred).

    (* Arithmetic helpers for the merge rewrites. *)
    replace (16 + (512 - 16 * (i + 1)) - 16) with (512 - 16 * i - 16) by lia.
    replace (16 + (512 - 16 * (i + 1))) with (512 - 16 * i) by lia.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.

    assert (Hlpkgen :
      Zlength (block_to_vals
        (pkgen_block sk_seed pk_seed a (Z.to_nat i))) = 16).
    { rewrite block_to_vals_length, pkgen_block_Zlength.
      reflexivity. }

    (* Merge MID + TAIL: slot @ pMID ++ tail = suffix @ pMID *)
    gather_SEP
      (data_at Tsh (tarray tuchar 16)
         (block_to_vals (pkgen_block sk_seed pk_seed a (Z.to_nat i))) pMID)
      (data_at Tsh (tarray tuchar (512 - 16 * i - 16)) _ _).
    erewrite <- (split2_data_at_Tarray_app 16 (512 - 16 * i)
                   Tsh tuchar
                   (block_to_vals
                     (pkgen_block sk_seed pk_seed a (Z.to_nat i)))
                   (Zrepeat Vundef (512 - 16 * (i + 1)))
                   pMID Hlpkgen)
      by (rewrite Zlength_Zrepeat; lia).

    (* Merge FILLED + suffix: FILLED @ v_ends ++ suffix = full array *)
    unfold pMID.
    gather_SEP
      (data_at Tsh (tarray tuchar (16 * i)) FILLED v_ends)
      (data_at Tsh (tarray tuchar (512 - 16 * i)) _ _).
    erewrite <- (split2_data_at_Tarray_app (16 * i) 512 Tsh tuchar
                   FILLED
                   (block_to_vals
                     (pkgen_block sk_seed pk_seed a (Z.to_nat i))
                    ++ Zrepeat Vundef (512 - 16 * (i + 1)))
                   v_ends HlFILLED)
      by (rewrite Zlength_app, block_to_vals_length,
          pkgen_block_Zlength, Zlength_Zrepeat; rep_lia).

    (* Fold LHS to the invariant's named form, then close. *)
    subst FILLED.
    rewrite app_assoc, <- blocks_to_vals_seq_S.
    entailer!!.

    (* Re-establish the [adrs_struct_eq] invariant for the threaded address:
       [chain_addr_post] and [shrincs_wots_hash_adrs] both preserve the prefix,
       so transit through them back to [b], then [b] to [a] via [H0]. *)
    apply adrs_struct_eq_trans with (shrincs_wots_hash_adrs w_pred_pos b (to_chain32 (Z.to_nat i))).
    apply chain_addr_post_struct_eq.
    apply adrs_struct_eq_trans with b.
    apply shrincs_wots_hash_adrs_struct_eq.
    exact H0.

  (* ===== after the loop: PK-type the address, then T_sf-compress ===== *)
  - Intros b.
    match goal with H : adrs_struct_eq b a |- _ => rename H into Hstruct end.
    match goal with H : 0 < 32 -> _ |- _ => rename H into Hres0 end.
    assert (Hres : payload_a_z b = 0) by (apply Hres0; lia).

    (* addr[ADRS_TYPE] = SF_SHRINCS_WOTS_PK (17), over the wire ([radrs])
       view of [addr]. *)
    store_type_byte.

    (* shrincs_adrs_put32(addr, ADRS_CHAIN=14, 0); shrincs_adrs_put32(addr, ADRS_HASH=18, 0) *)
    store_pk_words a_ptr sh_a b.

    (* Fold the three stores into the wire view of [shrincs_wots_pk_adrs a],
       then bridge the wire bytes back to [adrs_to_vals]. *)
    change 17 with (byte_val SF_SHRINCS_WOTS_PK).
    rewrite (pkaddr_final_eq b a Hstruct Hres).
    rewrite radrs_bytes_to_raw.
    change (block_to_vals (adrs_bytes (shrincs_wots_pk_adrs a)))
      with (adrs_to_vals (shrincs_wots_pk_adrs a)).

    (* Collapse the ends buffer to [block_to_vals (concat (chain_tips ...))]. *)
    change (Z.to_nat 32) with len.
    replace (512 - 16 * 32) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.
    rewrite <- chain_tips_map.

    (* Retype the ends buffer to the shape [shrincs_wots_t_sf] expects: fuse
       [blocks_to_vals ... = block_to_vals (concat ...)], and re-express the
       array bounds 512 and 16 as the funspec's [Z.of_nat (len * n)] and
       [n_bytes]. *)
    change (blocks_to_vals (chain_tips sk_seed pk_seed (anchor_nh a) (anchor_ni a)))
      with (block_to_vals (concat (chain_tips sk_seed pk_seed (anchor_nh a) (anchor_ni a)))).
    change 512 with (Z.of_nat (len * n)).
    change 16 with n_bytes.

    (* shrincs_wots_t_sf(pk, pk_seed, addr, ends) -- the final T_sf compression. *)
    assert_PROP (Zlength (block_to_vals pk_seed) = 16) as Hlps by entailer!.
    rewrite block_to_vals_length in Hlps.
    forward_call (pk_ptr, ps_ptr, a_ptr, v_ends,
                  shrincs_wots_pk_adrs a, pk_seed,
                  concat (chain_tips sk_seed pk_seed (anchor_nh a) (anchor_ni a)),
                  sh_pk, sh_ps, sh_a, Tsh).
    { (* ends length *)
      apply Zlength_concat_chain_tips. }

    (* Postcondition: section 5's reassembly, spent ONCE -- the port's
       [wots_c_pubkey_gen] at [adrs_bytes a] IS the T_sf of the concatenated
       per-chain tips the loop just built. *)
    rewrite adrs_bytes_pk, adrs_bytes_mk_adrs, wots_c_pubkey_gen_tips.
    unfold shrincs.concat.
    entailer!!.
Qed.
