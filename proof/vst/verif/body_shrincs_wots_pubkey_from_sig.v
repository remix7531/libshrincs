(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_pubkey_from_sig: VST body proof for [shrincs_wots_pubkey_from_sig]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import model.wots.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* The address-stepping helpers this body leans on ([wc_set_chain] and its
   struct-eq/type/raw lemmas, [adrs_hash_is_Wc_hash], [complete_block_from_ai],
   [hash0_raw], [pkaddr_final_17]) are shared -- see
   [contract.lemmas.chain_blocks]; [chain_addr_post_hash_type] /
   [chain_addr_post_pa0] live beside [chain_addr_post] in
   [contract.helpers_wots]; the array/digest bridges
   ([Zlength_blocks_to_vals_fixed], [Znth_digits_to_vals]) live in
   [contract.lemmas.data_at], and the digest-sum reflection
   ([digest_sum_repr_240]) in [contract.lemmas.arith_nibble]. *)

(* Keep the heavy chain/digest/hash definitions folded during the closing
   cancels' "close by conversion": otherwise the [Qed] kernel check
   delta-unfolds the 32-chain [complete_block] / [wc_chain] map, the
   grinding digest and [T_sf], and diverges. *)
Opaque complete_block wc_chain shrincs.T_sf shrincs.sha256 digest_of
       shrincs.H_grind shrincs.base_2b.

Lemma body_shrincs_wots_pubkey_from_sig :
  semax_body Vprog Gprog f_shrincs_wots_pubkey_from_sig shrincs_wots_pubkey_from_sig_spec.
Proof.
  start_function.

  (* ===== The POST, reassembled once =====
     [Model.theory.shrincs] section 5.6 splits the port's whole verifier
     front end, at the spec's flat signature layout, into the counter's
     constant-sum gate and the [T_sf] of the completed chains -- which is
     exactly what the gate and the loop below build.  Every hypothesis it
     needs is already in the funspec PROP; the model side counts blocks
     with [length] where the funspec bounds them with [Zlength]. *)
  assert (Hends : shrincs.wots_c_pubkey_from_sig
                    (shrincs.to_bytes counter 2 ++ shrincs.concat sig) msg pk_seed
                    (adrs_bytes a)
                  = if good_counter pk_seed (anchor_nh a) (anchor_ni a) msg counter
                    then Some (shrincs.T_sf pk_seed (wc_pk_adrs (anchor_nh a) (anchor_ni a))
                                 (concat (complete_ends msg sig counter pk_seed
                                            (anchor_nh a) (anchor_ni a))))
                    else None).
  { rewrite adrs_bytes_mk_adrs.
    apply wots_c_pubkey_from_sig_ends.
    - assumption.
    - assumption.
    - match goal with Hf : Forall (fun b => Zlength b = n_bytes) sig |- _ =>
        rewrite Forall_forall in Hf;
        intros b Hb;
        specialize (Hf b Hb);
        rewrite Zlength_correct, n_bytes_eq in Hf
      end.
      lia. }

  (* ===== Reassemble the 2-byte big-endian counter from sig[0..2) =====
     [start_function] already reduces [block_to_vals (to_bytes counter 2)] to
     the two concrete head cells, so the loads read them directly. *)

  (* sig[0] *)
  forward.
  all: try close_tc_byte_cons.
  rewrite Znth_0_cons.
  (* sig[1] *)
  forward.
  all: try close_tc_byte_cons.
  rewrite Znth_pos_cons by lia.
  rewrite Znth_0_cons.
  (* counter = (uint32_t)sig[0] << 8 | (uint32_t)sig[1] *)
  forward.
  match goal with |- context [temp _counter (Vint ?E)] => assert (Hcounter : E = Int.repr counter) end.
  { rewrite !byte.byte_modulus.
    rewrite !Byte.unsigned_repr
      by (match goal with |- 0 <= ?x mod ?y <= _ => pose proof (Z.mod_pos_bound x y ltac:(lia)) end; rep_lia).
    rewrite bytes_be_to_halfword by (apply Z.mod_pos_bound; lia).
    f_equal.
    change (let (q, _) := Z.div_eucl counter 256 in q) with (counter / 256).
    assert (E1 : counter / 256 = counter / 2 ^ 8) by reflexivity.
    rewrite E1.
    apply word_be_recompose_2. assumption. }
  rewrite Hcounter.
  clear Hcounter.
  deadvars!.

  (* ===== shrincs_wots_map_digest(digits, msg, counter, pk_seed, addr) ===== *)
  forward_call (v_digits, msg_ptr, counter, ps_ptr, a_ptr, msg, pk_seed, a, Tsh, sh_m, sh_ps, sh_a).

  (* ===== Constant-sum gate: reject unless the digest sums to 240 ===== *)
  forward_if.
  - (* sum <> 240: return -1; the port's recovery returns [None] *)
    assert (Hgc : good_counter pk_seed (anchor_nh a) (anchor_ni a) msg counter = false).
    { apply not_true_is_false.
      intro Hg.
      apply good_counter_Z_iff in Hg.
      match goal with Hs : Int.repr _ <> Int.repr _ |- _ => apply Hs end.
      f_equal.
      exact Hg. }
    assert (Hnone : shrincs.wots_c_pubkey_from_sig
                      (shrincs.to_bytes counter 2 ++ shrincs.concat sig) msg pk_seed
                      (adrs_bytes a) = None)
      by (rewrite Hends, Hgc; reflexivity).
    forward.
    (* Both POST conjuncts are keyed on the port's accept/reject: the
       [None] arm leaves pk uninitialised and the address grind-typed,
       which is what the loop-free reject path holds.  [setoid_rewrite]
       (not [rewrite]) because [start_function] has already computed the
       counter prefix inside the port's flat signature argument. *)
    setoid_rewrite Hnone.
    setoid_rewrite Hgc.
    entailer!!.
  - (* sum = 240: completion loop, then T_sf compress, return 0 *)
    assert (Hsum : shrincs.sum_list
                     (digest_of pk_seed (anchor_nh a) (anchor_ni a) msg counter) = 240).
    { apply digest_sum_repr_240.
      match goal with Hs : Int.repr _ = Int.repr 240 |- _ => exact Hs end. }
    assert (Hgc : good_counter pk_seed (anchor_nh a) (anchor_ni a) msg counter = true)
      by (apply good_counter_Z_iff; exact Hsum).
    assert (Hsome : shrincs.wots_c_pubkey_from_sig
                      (shrincs.to_bytes counter 2 ++ shrincs.concat sig) msg pk_seed
                      (adrs_bytes a)
                    = Some (shrincs.T_sf pk_seed (wc_pk_adrs (anchor_nh a) (anchor_ni a))
                              (concat (complete_ends msg sig counter pk_seed
                                         (anchor_nh a) (anchor_ni a)))))
      by (rewrite Hends, Hgc; reflexivity).
    (* ===== shrincs_memcpy(ends, sig + 2, 512): copy all CHAIN_COUNT raw tips
       out of the signature in one shot; the loop below never reads sig. ===== *)
    change sig_bytes with 514.
    (* [Hfc_sig] is never used by name but feeds [auto with field_compatible]
       in the memcpy side block's [field_address0_offset] rewrite. *)
    assert_PROP (field_compatible (tarray tuchar 514) nil sig_ptr)
      as Hfc_sig by entailer!.
    assert (Hlen32 : length sig = 32%nat)
      by (match goal with Hs : length sig = len |- _ => rewrite Hs; reflexivity end).
    assert (HFsig : Forall (fun b => Zlength b = n_bytes) sig)
      by (match goal with Hf : Forall (fun b => Zlength b = n_bytes) sig |- _ => exact Hf end).
    assert (Hlctr : Zlength (block_to_vals (to_byte counter 2)) = 2)
      by (rewrite block_to_vals_length, to_byte_Zlength; reflexivity).
    assert (Hlsig512 : Zlength (blocks_to_vals sig) = 512).
    { rewrite Zlength_blocks_to_vals_fixed by exact HFsig.
      rewrite Hlen32. change n_bytes with 16. lia. }
    (* split sig into the 2-byte counter head | the 512-byte chain region *)
    erewrite (split2_data_at_Tarray_app 2 514 sh_sig tuchar
                (block_to_vals (to_byte counter 2)) (blocks_to_vals sig))
      by (first [exact Hlctr | exact Hlsig512]).
    set (sSRC := field_address0 (tarray tuchar 514) (SUB 2) sig_ptr).
    Intros.
    sep_apply (data_at__memory_block_cancel Tsh (tarray tuchar 512) v_ends).
    change (sizeof (tarray tuchar 512)) with 512.
    rewrite (blocks_to_vals_eq_Vint sig).
    forward_call (sh_sig, Tsh, v_ends, sSRC, 512, block_ints (concat sig)).
    { entailer!!.
      unfold sSRC.
      rewrite field_address0_offset by auto with field_compatible.
      simpl. reflexivity. }
    rewrite <- (blocks_to_vals_eq_Vint sig).
    (* re-merge sig back to the whole array (untouched from here on) *)
    unfold sSRC.
    gather_SEP
      (data_at sh_sig (tarray tuchar 2) (block_to_vals (to_byte counter 2)) sig_ptr)
      (data_at sh_sig (tarray tuchar 512) (blocks_to_vals sig)
         (field_address0 (tarray tuchar 514) (SUB 2) sig_ptr)).
    erewrite <- (split2_data_at_Tarray_app 2 514 sh_sig tuchar
                   (block_to_vals (to_byte counter 2)) (blocks_to_vals sig)
                   sig_ptr Hlctr Hlsig512).
    clear Hfc_sig Hlctr Hlsig512 sSRC.
    (* addr[ADRS_TYPE] = SF_SHRINCS_WOTS_HASH (16): grind type byte 22 overwritten;
       the wire view becomes [rset_type (adrs_to_raw (grind a)) 16]. *)
    store_type_byte.
    (* shrincs_adrs_put32(addr, ADRS_RESERVED=10, 0): reserved word -> 0 *)
    forward_call (a_ptr, 10, 0,
                  radrs_bytes (rset_type (adrs_to_raw (shrincs_wots_grind_adrs a)) 16), sh_a).
    rewrite shrincs_adrs_put32_reserved.
    (* fold the wire view to [shrincs_wots_hash_adrs a (to_chain32 0)] for the loop entry *)
    rewrite hash0_raw.
    rewrite radrs_bytes_to_raw.
    (* ===== Completion loop: fill ends[i*N .. i*N+N) with complete_block i ===== *)
    forward_for_simple_bound 32
      (EX i : Z, EX ai : adrs,
        PROP (adrs_struct_eq ai a;
              adrs_type ai = SF_SHRINCS_WOTS_HASH; payload_a_z ai = 0)
        LOCAL (temp _counter (Vint (Int.repr counter));
               lvar _ends (tarray tuchar 512) v_ends;
               lvar _digits (tarray tuchar 32) v_digits; temp _pk_cand pk_ptr;
               temp _sig sig_ptr; temp _msg msg_ptr; temp _pk_seed ps_ptr;
               temp _addr a_ptr)
        SEP (data_at Tsh (tarray tuchar 512)
               (blocks_to_vals
                  (map (complete_block sig
                          (digest_of pk_seed (anchor_nh a) (anchor_ni a) msg counter)
                          pk_seed a)
                       (seq 0 (Z.to_nat i)))
                ++ blocks_to_vals (skipn (Z.to_nat i) sig)) v_ends;
             data_at Tsh (tarray tuchar (Z.of_nat len))
               (digits_to_vals
                  (digest_of pk_seed (anchor_nh a) (anchor_ni a) msg counter)) v_digits;
             data_at sh_m (tarray tuchar msg_bytes) (block_to_vals msg) msg_ptr;
             data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
             data_at sh_a t_addr (adrs_to_vals ai) a_ptr;
             data_at_ sh_pk (tarray tuchar pk_bytes) pk_ptr;
             data_at sh_sig (tarray tuchar sig_bytes)
               (block_to_vals (to_byte counter 2) ++ blocks_to_vals sig) sig_ptr)).
    + (* loop entry: after the bulk memcpy [ends] holds [blocks_to_vals sig],
         i.e. zero completed blocks followed by all 32 raw tips. *)
      Exists (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 0)).
      change (Z.to_nat 0) with 0%nat.
      simpl seq.
      simpl map.
      change (blocks_to_vals nil) with (@nil val).
      change (skipn 0%nat sig) with sig.
      rewrite app_nil_l.
      entailer!!.
      apply shrincs_wots_hash_adrs_struct_eq.
    + (* loop body *)
      Intros.
      match goal with H : adrs_struct_eq ai a |- _ => rename H into Hse end.
      match goal with H : adrs_type ai = SF_SHRINCS_WOTS_HASH |- _ => rename H into Htype end.
      match goal with H : payload_a_z ai = 0 |- _ => rename H into Hpa end.
      (* [Hfc_ends] is never used by name but feeds [auto with field_compatible]
         in the chain_iter side block's [field_address0_offset] rewrite. *)
      assert_PROP (field_compatible (tarray tuchar 512) nil v_ends) as Hfc_ends by entailer!.
      assert (Hilen : 0 <= i < Z.of_nat len) by (rewrite len_eq_Z; lia).
      set (DS := digest_of pk_seed (anchor_nh a) (anchor_ni a) msg counter) in *.
      set (FILLED := blocks_to_vals (map (complete_block sig DS pk_seed a) (seq 0 (Z.to_nat i)))).
      (* A completed end is [n] bytes only because its LAUNCH block is: at
         digit 15 the chain runs zero steps, and the port's [index_block]
         defaults to the EMPTY block out of range. *)
      assert (Hcb : forall j : nat, (j < 32)%nat ->
                      Zlength (complete_block sig DS pk_seed a j) = n_bytes).
      { intros j Hj.
        apply complete_block_Zlength.
        apply index_block_Zlength; [ rewrite Hlen32; lia | exact HFsig ]. }
      assert (HlFILLED : Zlength FILLED = 16 * i).
      { subst FILLED.
        rewrite Zlength_blocks_to_vals_fixed
          by (apply Forall_map, Forall_forall; intros j Hj;
              apply in_seq in Hj; apply Hcb; lia).
        rewrite length_map, length_seq.
        change n_bytes with 16.
        lia. }
      (* Peel raw tip [i] off the skipn-tail at the port's own default, so
         the peeled block IS [index_block sig i]; the loop completes it in place. *)
      rewrite (blocks_to_vals_skipn_hd sig (Z.to_nat i) (@nil byte))
        by (rewrite Hlen32; lia).
      change (nth (Z.to_nat i) sig (@nil byte)) with (index_block sig i).
      assert (HlMID : Zlength (block_to_vals (index_block sig i)) = 16).
      { rewrite block_to_vals_length. change 16 with n_bytes.
        apply index_block_Zlength; [ rewrite Hlen32; lia | exact HFsig ]. }
      assert (HlTAIL : Zlength (blocks_to_vals (skipn (S (Z.to_nat i)) sig)) = 512 - 16 * (i + 1)).
      { rewrite Zlength_blocks_to_vals_fixed.
        - rewrite length_skipn, Hlen32. change n_bytes with 16. lia.
        - apply Forall_skipn. exact HFsig. }
      assert (HlMT : Zlength (block_to_vals (index_block sig i)
                       ++ blocks_to_vals (skipn (S (Z.to_nat i)) sig)) = 512 - 16 * i).
      { rewrite Zlength_app, HlMID, HlTAIL. lia. }
      (* split ends: FILLED (16*i) | MID = raw tip i (16) | TAIL = raw skipn(S i) *)
      erewrite (split2_data_at_Tarray_app (16*i) 512 Tsh tuchar FILLED
                  (block_to_vals (index_block sig i)
                     ++ blocks_to_vals (skipn (S (Z.to_nat i)) sig)))
        by (first [exact HlFILLED | exact HlMT]).
      erewrite (split2_data_at_Tarray_app 16 (512 - 16*i) Tsh tuchar
                  (block_to_vals (index_block sig i))
                  (blocks_to_vals (skipn (S (Z.to_nat i)) sig))).
      2: exact HlMID.
      2:{ rewrite Zlength_blocks_to_vals_fixed by (apply Forall_skipn; exact HFsig).
          rewrite length_skipn, Hlen32. change n_bytes with 16. lia. }
      set (pMID := field_address0 (tarray tuchar 512) (SUB (16*i)) v_ends).
      Intros.
      (* _tip = ends + i*16 *)
      forward.
      (* fold the addr buffer to its raw wire view *)
      unfold t_addr.
      rewrite adrs_to_vals_raw.
      (* ===== shrincs_adrs_put32(addr, ADRS_CHAIN=14, i): set chain word to i ===== *)
      forward_call (a_ptr, 14, i, radrs_bytes (adrs_to_raw ai), sh_a).
      rewrite shrincs_adrs_put32_chain.
      (* ===== _t'2 = digits[i]; _t'3 = digits[i] ===== *)
      pose proof (digest_of_Zlength pk_seed (anchor_nh a) (anchor_ni a) msg counter) as Hdl.
      change (digest_of pk_seed (anchor_nh a) (anchor_ni a) msg counter) with DS in Hdl.
      pose proof (index_int_digest_of_range pk_seed (anchor_nh a) (anchor_ni a) msg counter i)
        as Hrng.
      change (digest_of pk_seed (anchor_nh a) (anchor_ni a) msg counter) with DS in Hrng.
      forward.
      close_tc_byte_digit.
      forward.
      (* digit-value bridge: the C's [digits[i]] IS the port's [index_int DS i] *)
      assert (Hd : Znth i (digits_to_vals DS) = Vint (Int.repr (shrincs.index_int DS i))).
      { rewrite <- Znth_index_int by lia.
        apply Znth_digits_to_vals.
        - rewrite Hdl. lia.
        - rewrite Znth_index_int by lia. lia. }
      setoid_rewrite Hd.
      (* fold the addr buffer to the launch union [wc_set_chain ai i] *)
      rewrite <- (wc_set_chain_raw ai i Htype ltac:(lia)).
      rewrite radrs_bytes_to_raw.
      (* ===== shrincs_wots_chain_iter(tip, digits[i], W-1-digits[i], pk_seed, addr) ===== *)
      forward_call (pMID, ps_ptr, a_ptr,
                    shrincs.index_int DS i,
                    15 - shrincs.index_int DS i,
                    index_block sig i, pk_seed,
                    wc_set_chain ai (Z.to_nat i),
                    Tsh, sh_ps, sh_a).
      { entailer!!.
        unfold pMID.
        rewrite field_address0_offset by auto with field_compatible.
        simpl.
        rewrite !Z.add_0_l, !Z.mul_1_l.
        rewrite (Z.mul_comm i 16).
        reflexivity. }
      { change (Z.of_nat w_pred) with 15.
        repeat split; try rep_lia; try assumption;
          try (change 16 with n_bytes; apply index_block_Zlength;
               [ rewrite Hlen32; lia | exact HFsig ]);
          try (apply adrs_hash_is_Wc_hash; apply wc_set_chain_type; exact Htype). }
      (* ===== invariant preservation at i+1 ===== *)
      clear Hd Hdl HlMID HlTAIL HlMT.
      (* the C counts steps from the literal [w - 1]; the model from [w_pred] *)
      replace (15 - shrincs.index_int DS i)
        with (Z.of_nat w_pred - shrincs.index_int DS i) by reflexivity.
      (* fold the run chain into the model [complete_block sig DS pk_seed a i] *)
      rewrite (complete_block_from_ai sig DS pk_seed ai a i Hse Htype Hilen).
      (* supply the residual address and its structural facts *)
      set (ai' := chain_addr_post (wc_set_chain ai (Z.to_nat i))
                    (Z.to_nat (shrincs.index_int DS i))
                    (Z.to_nat (Z.of_nat w_pred - shrincs.index_int DS i))).
      assert (Hai'se : adrs_struct_eq ai' a).
      { subst ai'.
        eapply adrs_struct_eq_trans; [apply chain_addr_post_struct_eq |].
        eapply adrs_struct_eq_trans; [apply wc_set_chain_struct_eq | exact Hse]. }
      assert (Hai'ty : adrs_type ai' = SF_SHRINCS_WOTS_HASH).
      { subst ai'. apply chain_addr_post_hash_type. apply wc_set_chain_type. exact Htype. }
      assert (Hai'pa : payload_a_z ai' = 0).
      { subst ai'. apply chain_addr_post_pa0. apply wc_set_chain_type. exact Htype. }
      Exists ai'.
      (* merge MID(completed) + TAIL into the suffix at pMID, then FILLED +
         suffix into the whole [ends]; sig stays whole (a passive frame). *)
      assert (HlpkMID : Zlength (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i))) = 16).
      { rewrite block_to_vals_length. change 16 with n_bytes.
        apply Hcb. lia. }
      change n_bytes with 16.
      gather_SEP
        (data_at Tsh (tarray tuchar 16)
           (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i))) pMID)
        (data_at Tsh (tarray tuchar (512 - 16 * i - 16)) _ _).
      erewrite <- (split2_data_at_Tarray_app 16 (512 - 16 * i) Tsh tuchar
                     (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i)))
                     (blocks_to_vals (skipn (S (Z.to_nat i)) sig)) pMID HlpkMID)
        by (rewrite Zlength_blocks_to_vals_fixed by (apply Forall_skipn; exact HFsig);
            rewrite length_skipn, Hlen32; change n_bytes with 16; lia).
      unfold pMID.
      gather_SEP
        (data_at Tsh (tarray tuchar (16 * i)) FILLED v_ends)
        (data_at Tsh (tarray tuchar (512 - 16 * i)) _ _).
      erewrite <- (split2_data_at_Tarray_app (16 * i) 512 Tsh tuchar FILLED
                     (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i))
                      ++ blocks_to_vals (skipn (S (Z.to_nat i)) sig)) v_ends HlFILLED)
        by (rewrite Zlength_app, HlpkMID,
              Zlength_blocks_to_vals_fixed by (apply Forall_skipn; exact HFsig);
            rewrite length_skipn, Hlen32; change n_bytes with 16; lia).
      (* fold the merged [ends] content to the invariant at i+1 *)
      subst FILLED.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite blocks_to_vals_seq_S.
      rewrite <- app_assoc.
      entailer!!.
    + (* loop exit: i = 32, ends fully filled *)
      Intros ai.
      match goal with
      | Hse : adrs_struct_eq ai a, Hr : payload_a_z ai = 0 |- _ =>
          rename Hse into Hai_se; rename Hr into Hai_r
      end.
      (* all 32 blocks completed: the raw skipn-tail is now empty *)
      rewrite skipn_all2 by
        (change (Z.to_nat 32) with 32%nat;
         match goal with Hs : length sig = len |- _ => rewrite Hs end;
         change len with 32%nat; lia).
      change (blocks_to_vals nil) with (@nil val).
      rewrite app_nil_r.
      (* ===== Retag addr to the PK address [shrincs_wots_pk_adrs a] ===== *)
      (* addr[ADRS_TYPE] = SF_SHRINCS_WOTS_PK (17) *)
      store_type_byte.
      (* shrincs_adrs_put32(addr, ADRS_CHAIN=14, 0); shrincs_adrs_put32(addr, ADRS_HASH=18, 0) *)
      store_pk_words a_ptr sh_a ai.
      rewrite (pkaddr_final_17 ai a Hai_se Hai_r).
      rewrite radrs_bytes_to_raw.
      (* fold ends to [block_to_vals (concat (complete_ends ...))] *)
      change (Z.to_nat 32) with len.
      rewrite <- (complete_ends_map msg sig counter pk_seed a).
      rewrite blocks_to_vals_concat.
      (* ===== shrincs_wots_t_sf(pk_cand, pk_seed, addr, ends): compress ends into pk_cand ===== *)
      forward_call (pk_ptr, ps_ptr, a_ptr, v_ends,
                    shrincs_wots_pk_adrs a, pk_seed,
                    concat (complete_ends msg sig counter pk_seed
                              (anchor_nh a) (anchor_ni a)),
                    sh_pk, sh_ps, sh_a, Tsh).
      { change n_bytes with 16. change (Z.of_nat (len * n)) with 512.
        rewrite Zlength_concat_complete_ends by assumption.
        repeat split; try assumption; try rep_lia. }
      (* the compression hashes the PK address's WIRE form, which is the
         anchored [wc_pk_adrs] section 5 states the reassembly at *)
      rewrite (adrs_bytes_pk a).
      (* ===== return SHRINCS_WOTS_OK = 0; the port's recovery returns [Some] ===== *)
      forward.
      setoid_rewrite Hsome.
      setoid_rewrite Hgc.
      entailer!!.
Qed.
