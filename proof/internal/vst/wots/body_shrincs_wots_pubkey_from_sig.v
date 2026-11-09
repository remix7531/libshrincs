(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_pubkey_from_sig: VST body proof for [shrincs_wots_pubkey_from_sig]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.
From Shrincs.internal.vst.support Require Import model.wots.

Open Scope Z_scope.

Local Abbreviation adrs := (address.adrs len w_pred).

(* The address-stepping helpers this body leans on ([wc_set_chain] and its
   struct-eq/type/raw lemmas, [adrs_hash_is_Wc_hash], the [chain_iter_c]
   position-independence family, [complete_block_from_ai], [hash0_raw],
   [pkaddr_final_17]) are shared -- see [contract.lemmas.chain_blocks];
   [chain_addr_post_hash_type] / [chain_addr_post_pa0] live beside
   [chain_addr_post] in [contract.helpers_wots]; the array/digest bridges
   ([Zlength_blocks_to_vals_map_seq], [Znth_digits_to_vals]) live in
   [contract.lemmas.data_at], and the digest-sum reflection
   ([digest_sum_repr_240]) in [contract.lemmas.arith_nibble]. *)

(* Keep the heavy chain/digest/hash definitions folded during the closing
   cancels' "close by conversion": otherwise the [Qed] kernel check
   delta-unfolds the 32-chain [complete_block]/[shrincs_wots_chain_iter] map, the
   grinding digest and [T_sf], and diverges. *)
Opaque complete_block shrincs_wots_chain_iter T_sf thash digest_of H_grind base_2b.

Lemma body_shrincs_wots_pubkey_from_sig :
  semax_body Vprog Gprog f_shrincs_wots_pubkey_from_sig shrincs_wots_pubkey_from_sig_spec.
Proof.
  start_function.

  (* ===== Reassemble the 2-byte big-endian counter from sig[0..2) =====
     [start_function] already reduces [block_to_vals (to_byte counter 2)] to
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
  - (* sum <> 240: return -1; valid_digest = false *)
    assert (Hvalid : valid_digest (digest_of pk_seed a msg counter) = false).
    { unfold valid_digest. apply Nat.eqb_neq. intro Hc.
      match goal with H : Int.repr (Z.of_nat (list_sum _)) <> Int.repr _ |- _ => apply H end.
      rewrite Hc. change constant_sum with 240%nat. reflexivity. }
    forward.
    (* POST address conjunct is [if valid_digest .. then pk_adrs else grind_adrs];
       [rewrite Hvalid] fires the [false] branch to [grind_adrs], the address the
       loop-free reject path already holds. *)
    rewrite Hvalid.
    entailer!!.
  - (* sum = 240: completion loop, then T_sf compress, return 0 *)
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
               (blocks_to_vals (map (complete_block sig (digest_of pk_seed a msg counter) pk_seed a)
                                    (seq 0 (Z.to_nat i)))
                ++ blocks_to_vals (skipn (Z.to_nat i) sig)) v_ends;
             data_at Tsh (tarray tuchar (Z.of_nat len))
               (digits_to_vals (digest_of pk_seed a msg counter)) v_digits;
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
      set (DS := digest_of pk_seed a msg counter) in *.
      set (FILLED := blocks_to_vals (map (complete_block sig DS pk_seed a) (seq 0 (Z.to_nat i)))).
      assert (HlFILLED : Zlength FILLED = 16 * i).
      { subst FILLED.
        rewrite Zlength_blocks_to_vals_map_seq
          by (intros k; apply complete_block_Zlength, nth_block_Zlength_default, HFsig).
        lia. }
      (* Peel raw tip [i] off the skipn-tail; the loop reads/completes it in place. *)
      rewrite (blocks_to_vals_skipn_hd sig (Z.to_nat i) default) by (rewrite Hlen32; lia).
      assert (HlMID : Zlength (block_to_vals (nth (Z.to_nat i) sig default)) = 16).
      { rewrite block_to_vals_length. change 16 with n_bytes.
        apply nth_block_Zlength_default. assumption. }
      assert (HlTAIL : Zlength (blocks_to_vals (skipn (S (Z.to_nat i)) sig)) = 512 - 16 * (i + 1)).
      { rewrite Zlength_blocks_to_vals_fixed.
        - rewrite length_skipn, Hlen32. change n_bytes with 16. lia.
        - apply Forall_skipn. assumption. }
      assert (HlMT : Zlength (block_to_vals (nth (Z.to_nat i) sig default)
                       ++ blocks_to_vals (skipn (S (Z.to_nat i)) sig)) = 512 - 16 * i).
      { rewrite Zlength_app, HlMID, HlTAIL. lia. }
      (* split ends: FILLED (16*i) | MID = raw tip i (16) | TAIL = raw skipn(S i) *)
      erewrite (split2_data_at_Tarray_app (16*i) 512 Tsh tuchar FILLED
                  (block_to_vals (nth (Z.to_nat i) sig default)
                     ++ blocks_to_vals (skipn (S (Z.to_nat i)) sig)))
        by (first [exact HlFILLED | exact HlMT]).
      erewrite (split2_data_at_Tarray_app 16 (512 - 16*i) Tsh tuchar
                  (block_to_vals (nth (Z.to_nat i) sig default))
                  (blocks_to_vals (skipn (S (Z.to_nat i)) sig))).
      2: exact HlMID.
      2:{ rewrite Zlength_blocks_to_vals_fixed by (apply Forall_skipn; assumption).
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
      pose proof (digest_of_Zlength pk_seed a msg counter) as Hdl.
      change (digest_of pk_seed a msg counter) with DS in Hdl.
      forward.
      close_tc_byte_digit.
      forward.
      (* digit-value bridge: Znth i digits = Vint (Int.repr (Z.of_nat (nth i DS 0))) *)
      assert (Hb : Znth i DS = nth (Z.to_nat i) DS 0%nat).
      { unfold Znth. destruct (Z_lt_dec i 0); [lia|].
        apply nth_indep. rewrite Zlength_correct in Hdl. lia. }
      pose proof (nth_digest_le_15 pk_seed a msg counter i ltac:(lia)) as Hle.
      change (digest_of pk_seed a msg counter) with DS in Hle.
      rewrite Hb in Hle.
      assert (Hd : Znth i (digits_to_vals DS) =
                   Vint (Int.repr (Z.of_nat (nth (Z.to_nat i) DS 0%nat))))
        by (apply Znth_digits_to_vals; [rewrite Hdl | ]; lia).
      setoid_rewrite Hd.
      (* fold the addr buffer to the launch union [wc_set_chain ai i] *)
      rewrite <- (wc_set_chain_raw ai i Htype ltac:(lia)).
      rewrite radrs_bytes_to_raw.
      (* ===== shrincs_wots_chain_iter(tip, digits[i], W-1-digits[i], pk_seed, addr) ===== *)
      forward_call (pMID, ps_ptr, a_ptr,
                    Z.of_nat (nth (Z.to_nat i) DS 0%nat),
                    15 - Z.of_nat (nth (Z.to_nat i) DS 0%nat),
                    nth (Z.to_nat i) sig default, pk_seed,
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
          try (change 16 with n_bytes; apply nth_block_Zlength_default; assumption);
          try (apply adrs_hash_is_Wc_hash; apply wc_set_chain_type; exact Htype). }
      (* ===== invariant preservation at i+1 ===== *)
      clear Hb Hd Hdl Hle HlMID HlTAIL HlMT.
      rewrite Nat2Z.id.
      assert (Hs2 : Z.to_nat (15 - Z.of_nat (nth (Z.to_nat i) DS 0%nat))
                    = (w_pred - nth (Z.to_nat i) DS 0%nat)%nat).
      { change w_pred with 15%nat. rewrite Z2Nat.inj_sub by lia. rewrite Nat2Z.id. reflexivity. }
      rewrite Hs2.
      (* fold the run chain into the model [complete_block sig DS pk_seed a i] *)
      rewrite (complete_block_from_ai sig DS pk_seed ai a i Hse Htype).
      (* supply the residual address and its structural facts *)
      set (ai' := chain_addr_post (wc_set_chain ai (Z.to_nat i))
                    (nth (Z.to_nat i) DS 0%nat) (w_pred - nth (Z.to_nat i) DS 0%nat)).
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
        apply complete_block_Zlength. apply nth_block_Zlength_default. assumption. }
      change n_bytes with 16.
      gather_SEP
        (data_at Tsh (tarray tuchar 16)
           (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i))) pMID)
        (data_at Tsh (tarray tuchar (512 - 16 * i - 16)) _ _).
      erewrite <- (split2_data_at_Tarray_app 16 (512 - 16 * i) Tsh tuchar
                     (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i)))
                     (blocks_to_vals (skipn (S (Z.to_nat i)) sig)) pMID HlpkMID)
        by (rewrite Zlength_blocks_to_vals_fixed by (apply Forall_skipn; assumption);
            rewrite length_skipn, Hlen32; change n_bytes with 16; lia).
      unfold pMID.
      gather_SEP
        (data_at Tsh (tarray tuchar (16 * i)) FILLED v_ends)
        (data_at Tsh (tarray tuchar (512 - 16 * i)) _ _).
      erewrite <- (split2_data_at_Tarray_app (16 * i) 512 Tsh tuchar FILLED
                     (block_to_vals (complete_block sig DS pk_seed a (Z.to_nat i))
                      ++ blocks_to_vals (skipn (S (Z.to_nat i)) sig)) v_ends HlFILLED)
        by (rewrite Zlength_app, HlpkMID,
              Zlength_blocks_to_vals_fixed by (apply Forall_skipn; assumption);
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
                    concat (complete_ends msg sig counter pk_seed a),
                    sh_pk, sh_ps, sh_a, Tsh).
      { change n_bytes with 16. change (Z.of_nat (len * n)) with 512.
        rewrite Zlength_concat_complete_ends by assumption.
        repeat split; try assumption; try rep_lia. }
      (* ===== return SHRINCS_WOTS_OK = 0; valid_digest = true ===== *)
      assert (HsumZ : Z.of_nat (list_sum (digest_of pk_seed a msg counter)) = 240).
      { apply digest_sum_repr_240.
        match goal with H : Int.repr (Z.of_nat (list_sum _)) = Int.repr 240 |- _ => exact H end. }
      assert (Hvalid : valid_digest (digest_of pk_seed a msg counter) = true).
      { unfold valid_digest. apply Nat.eqb_eq. apply Nat2Z.inj.
        change (Z.of_nat constant_sum) with 240. exact HsumZ. }
      forward.
      (* POST address conjunct is [if valid_digest .. then pk_adrs else grind_adrs];
         [rewrite Hvalid] fires the [true] branch to [pk_adrs], the address the
         completion loop established. *)
      rewrite Hvalid.
      unfold shrincs_wots_pubkey_from_sig.
      entailer!!.
Qed.
