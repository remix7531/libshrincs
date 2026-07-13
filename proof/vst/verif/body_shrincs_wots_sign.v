(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_sign: VST body proof for [shrincs_wots_sign]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import model.wots.
Import ListNotations.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* Shared lemmas this proof leans on: the invariant re-typing bridge
   [chain_addr_post_struct_eq] lives in [contract.helpers]; the per-slot
   address/derive congruences [shrincs_wots_hash_adrs_congr] and [shrincs_wots_derive_sk_congr]
   (used to re-key [shrincs_wots_chain_from_seed]'s result off the residual address [ai]
   back onto the base [a]) live in [contract.lemmas.chain_blocks]. *)

(* Keep the heavy chain/grind definitions folded during the closing [cancel]'s
   "close by conversion": otherwise the [Qed] kernel check delta-unfolds the
   32-chain [sign_chains]/[sign_block]/[shrincs_wots_derive_sk]/[shrincs_wots_chain_iter] map and the
   [find_counter] fuel, and diverges (every tactic runs fast; only [Qed] blows
   up). *)
Local Opaque find_counter find_from sign_block sign_chains shrincs_wots_derive_sk
       shrincs_wots_chain_iter thash F PRF T_sf digest_of H_grind base_2b to_byte.

Lemma body_shrincs_wots_sign : semax_body Vprog Gprog f_shrincs_wots_sign shrincs_wots_sign_spec.
Proof.
  (* WOTS+C shrincs_wots_sign, 2-byte-prepended counter refactor.  The C writes the
     2-byte big-endian counter to sig[0..2) BEFORE the chain loop, so the loop
     invariant SEP carries [block_to_vals (to_byte counter 2)] as a FIXED prefix
     with chain writes at [SUB (2 + 16*i)].  [find_counter] is kept symbolic
     (destructed in the GOAL) so the kernel never WHNF-reduces its 2^16 fuel. *)
  start_function.
  rename H into Hmsglen.
  rename H0 into Hpslen.
  rename H1 into Hsklen.

  (* ===== shrincs_wots_grind_to_constant_sum(digits, &counter, msg, pk_seed, addr) ===== *)
  forward_call (v_digits, v_counter, msg_ptr, ps_ptr, a_ptr,
                msg, pk_seed, a, Tsh, Tsh, sh_m, sh_ps, sh_a).

  (* Case-split on the winning counter.  [remember] abstracts [find_counter]
     to a VARIABLE [fc] first, so the case-split's [match] is on [fc], not on
     the reducible [find_counter ...] application. *)
  remember (find_counter pk_seed a msg) as fc eqn:E.
  destruct fc as [counter|].

  - (* ===== Some counter: grinding succeeded, sign the digits ===== *)
    symmetry in E.   (* E : find_counter pk_seed a msg = Some counter *)
    forward_if.
    { (* unreachable: shrincs_wots_grind_to_constant_sum returned 0 (success), so 0 <> 0 is false *)
      discriminate. }
    (* Discard the [_t'1 <> 0] guard so the loop-body's [adrs_struct_eq]
       invariant hypothesis lands as [H]. *)
    clear H.

    pose proof (find_counter_lt _ _ _ _ E) as Hcounter.
    unfold c_max in Hcounter.
    change sig_bytes with 514.
    Intros.

    (* ===== sig[0..2) = big-endian counter (written BEFORE the loop) ===== *)
    (* _t'4 = counter; sig[0] = (uint8_t)(counter >> 8) *)
    forward.
    forward.
    (* _t'3 = counter; sig[1] = (uint8_t)counter *)
    forward.
    forward.

    (* Fold the two stored counter bytes into the fixed prefix
       [block_to_vals (to_byte counter 2)]. *)
    rewrite !Int.zero_ext_idem by lia.
    assert (Hstruct : forall c0 c1 : val,
              upd_Znth 1 (upd_Znth 0 (default_val (tarray tuchar 514)) c0) c1
              = [c0; c1] ++ Zrepeat Vundef 512).
    { intros c0 c1. list_solve. }
    rewrite Hstruct.
    rewrite (counter_bytes_eq' counter Hcounter).

    (* Chain loop: fill sig[2..514) with the len signing chains, keeping the
       2-byte counter prefix fixed. *)
    forward_for_simple_bound 32
      (EX i : Z, EX ai : adrs,
        PROP (adrs_struct_eq ai a)
        LOCAL (lvar _counter tuint v_counter; lvar _digits (tarray tuchar 32) v_digits;
               temp _sig sig_ptr; temp _msg msg_ptr; temp _sk_seed sk_ptr;
               temp _pk_seed ps_ptr; temp _addr a_ptr)
        SEP (data_at sh_sig (tarray tuchar 514)
               (block_to_vals (to_byte counter 2)
                ++ blocks_to_vals (map (sign_block sk_seed pk_seed a
                                          (digest_of pk_seed a msg counter))
                                       (seq 0 (Z.to_nat i)))
                ++ Zrepeat Vundef (512 - 16 * i)) sig_ptr;
             data_at Tsh (tarray tuchar 32)
               (digits_to_vals (digest_of pk_seed a msg counter)) v_digits;
             data_at Tsh tuint (Vint (Int.repr counter)) v_counter;
             data_at sh_m (tarray tuchar msg_bytes) (block_to_vals msg) msg_ptr;
             data_at sh_sk (tarray tuchar seed_bytes) (block_to_vals sk_seed) sk_ptr;
             data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
             data_at sh_a t_addr (adrs_to_vals ai) a_ptr)).

    + (* ----- loop entry: [addr] is grind-typed after the grinding call, so
         enter with [ai := shrincs_wots_grind_adrs a] (struct-eq to [a]). ----- *)
      Exists (shrincs_wots_grind_adrs a).
      entailer!.
      apply shrincs_wots_grind_adrs_struct_eq.

    + (* ----- loop body ----- *)
      Intros.
      match goal with H : adrs_struct_eq _ _ |- _ => rename H into Hae end.
      assert_PROP (field_compatible (tarray tuchar 514) nil sig_ptr
                   /\ Zlength (block_to_vals sk_seed) = n_bytes
                   /\ Zlength (block_to_vals pk_seed) = n_bytes)
        as Hpure by entailer!.
      destruct Hpure as [Hfc_sig [Hlss Hlps]].
      rewrite block_to_vals_length in Hlss, Hlps.

      (* Split sig into PREFIX (2 + 16*i) | MID (16) | TAIL. *)
      set (FILLED := blocks_to_vals
                       (map (sign_block sk_seed pk_seed a
                               (digest_of pk_seed a msg counter))
                            (seq 0 (Z.to_nat i)))).
      assert (HlFILLED : Zlength FILLED = 16 * i).
      { subst FILLED.
        rewrite Zlength_blocks_to_vals_map_seq
          by (intros k; apply sign_block_Zlength).
        lia. }
      assert (HlPREF : Zlength (block_to_vals (to_byte counter 2) ++ FILLED) = 2 + 16 * i).
      { rewrite Zlength_app, block_to_vals_length, to_byte_Zlength, HlFILLED. lia. }
      (* group [counter prefix ++ FILLED] as the fixed head before slot i *)
      rewrite (app_assoc (block_to_vals (to_byte counter 2)) FILLED).
      erewrite (split2_data_at_Tarray_app (2 + 16*i) 514 sh_sig tuchar
                  (block_to_vals (to_byte counter 2) ++ FILLED)
                  (Zrepeat Vundef (512 - 16*i)))
        by (first [exact HlPREF |
                   (rewrite Zlength_Zrepeat; lia) | split_sc]).
      replace (512 - 16*i) with (16 + (512 - 16*(i+1))) by lia.
      rewrite <- Zrepeat_app by lia.
      erewrite (split2_data_at_Tarray_app 16 _ sh_sig tuchar
                  (Zrepeat Vundef 16) (Zrepeat Vundef (512 - 16*(i+1))))
        by split_sc.
      set (pSUFF := field_address0 (tarray tuchar 514) (SUB (2 + 16*i)) sig_ptr).
      Intros.

      (* Convert MID slot to data_at_. *)
      replace (Zrepeat (A:=val) Vundef 16)
        with (default_val (tarray tuchar 16)) by reflexivity.
      rewrite <- data_at__eq.

      (* _chain = sig + 2 + i*N (the per-slot base pointer) *)
      forward.

      (* ===== _t'2 = digits[i] (the chain-length argument to shrincs_wots_chain_from_seed) ===== *)
      pose proof (digest_of_Zlength pk_seed a msg counter) as Hdl.
      forward.
      { close_tc_byte_digit. }

      (* Facts about digit i: value bridge + [<= w_pred] bound. *)
      assert (HZn : Znth i (digest_of pk_seed a msg counter)
                    = nth (Z.to_nat i) (digest_of pk_seed a msg counter) 0%nat)
        by (rewrite <- nth_Znth by (rewrite Hdl; lia); reflexivity).
      assert (Hd15 : (nth (Z.to_nat i) (digest_of pk_seed a msg counter) 0%nat <= 15)%nat)
        by (rewrite <- HZn; apply nth_digest_le_15; lia).
      assert (Ht6 : Znth i (digits_to_vals (digest_of pk_seed a msg counter))
                    = Vint (Int.repr
                        (Z.of_nat (nth (Z.to_nat i) (digest_of pk_seed a msg counter) 0%nat))))
        by (apply Znth_digits_to_vals; [rewrite Hdl | ]; lia).
      setoid_rewrite Ht6.

      (* ===== shrincs_wots_chain_from_seed(chain, i, digits[i], sk_seed, pk_seed, addr) --
         shrincs_wots_derive_sk + hash-retype + shrincs_wots_chain_iter in one call. ===== *)
      forward_call (pSUFF, sk_ptr, ps_ptr, a_ptr,
                    i, Z.of_nat (nth (Z.to_nat i) (digest_of pk_seed a msg counter) 0%nat),
                    sk_seed, pk_seed, ai,
                    sh_sig, sh_sk, sh_ps, sh_a).
      { (* PARAMS slot address: a pure equality, no SEP facts needed. *)
        solve_slot_addr_pure pSUFF Hfc_sig. }
      { (* chain index + step bound + seed lengths *)
        change (Z.of_nat w_pred) with 15. change (Z.of_nat len) with 32.
        repeat split; try rep_lia; try assumption. }

      (* Fold shrincs_wots_chain_from_seed's result (over the residual address [ai],
         struct-eq to [a]) back to the base-[a] [sign_block] via the shared
         [iter_eq_sign_block]; the residual [shrincs_wots_hash_adrs] inside
         [chain_addr_post] re-keys onto [a] via the congruence.  Under the
         union-ADRS API the chain index is a [fin 32] ([to_chain32 (Z.to_nat i)]). *)
      rewrite Nat2Z.id.
      rewrite (iter_eq_sign_block sk_seed pk_seed a ai
                 (digest_of pk_seed a msg counter) (Z.to_nat i) Hae).
      rewrite (shrincs_wots_hash_adrs_congr ai a (to_chain32 (Z.to_nat i)) Hae).
      replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia.

      change n_bytes with 16.

      assert (Hlsign :
        Zlength (block_to_vals
          (sign_block sk_seed pk_seed a
             (digest_of pk_seed a msg counter) (Z.to_nat i))) = 16).
      { rewrite block_to_vals_length, sign_block_Zlength.
        reflexivity. }
      assert (HlTAIL : Zlength (Zrepeat (A:=val) Vundef (512 - 16 * (i + 1)))
                       = 514 - (2 + 16 * i) - 16).
      { rewrite Zlength_Zrepeat; lia. }

      (* Merge MID slot + TAIL into the suffix at pSUFF. *)
      gather_SEP
        (data_at sh_sig (tarray tuchar 16)
           (block_to_vals (sign_block sk_seed pk_seed a
              (digest_of pk_seed a msg counter) (Z.to_nat i))) pSUFF)
        (data_at sh_sig (tarray tuchar (514 - (2 + 16 * i) - 16)) _ _).
      erewrite <- (split2_data_at_Tarray_app 16 (514 - (2 + 16 * i))
                     sh_sig tuchar
                     (block_to_vals (sign_block sk_seed pk_seed a
                        (digest_of pk_seed a msg counter) (Z.to_nat i)))
                     (Zrepeat Vundef (512 - 16 * (i + 1)))
                     pSUFF Hlsign HlTAIL).

      (* Merge PREFIX ++ FILLED + suffix into the full array. *)
      unfold pSUFF.
      gather_SEP
        (data_at sh_sig (tarray tuchar (2 + 16 * i))
           (block_to_vals (to_byte counter 2) ++ FILLED) sig_ptr)
        (data_at sh_sig (tarray tuchar (514 - (2 + 16 * i))) _ _).
      Exists (chain_addr_post (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 (Z.to_nat i))) 0
                (nth (Z.to_nat i) (digest_of pk_seed a msg counter) 0%nat)).
      entailer!!.
      { (* invariant: new address is still struct-eq to [a] *)
        eapply adrs_struct_eq_trans;
          [apply chain_addr_post_struct_eq | apply shrincs_wots_hash_adrs_struct_eq]. }
      assert (HlSUF : Zlength (block_to_vals (sign_block sk_seed pk_seed a
                        (digest_of pk_seed a msg counter) (Z.to_nat i))
                      ++ Zrepeat (A:=val) Vundef (512 - 16 * (i + 1)))
                      = 514 - (2 + 16 * i)).
      { rewrite Zlength_app, block_to_vals_length, sign_block_Zlength.
        rewrite Zlength_Zrepeat by lia.
        change n_bytes with 16.
        lia. }
      erewrite <- (split2_data_at_Tarray_app (2 + 16 * i) 514 sh_sig tuchar
                     (block_to_vals (to_byte counter 2) ++ FILLED)
                     (block_to_vals (sign_block sk_seed pk_seed a
                        (digest_of pk_seed a msg counter) (Z.to_nat i))
                      ++ Zrepeat Vundef (512 - 16 * (i + 1)))
                     sig_ptr HlPREF HlSUF).
      apply derives_refl'.
      f_equal.
      subst FILLED.
      rewrite <- (app_assoc (block_to_vals (to_byte counter 2))).
      f_equal.
      rewrite blocks_to_vals_seq_S, <- app_assoc.
      reflexivity.

    + (* ----- after the loop: return SHRINCS_WOTS_OK ----- *)
      Intros ai.
      change (Z.to_nat 32) with 32%nat.
      change (512 - 16 * 32) with 0.
      rewrite Zrepeat_0, app_nil_r.

      (* return SHRINCS_WOTS_OK *)
      forward.

      Exists ai.
      assert (Hsign : shrincs_wots_sign msg sk_seed pk_seed a
                      = Some (sign_chains msg sk_seed pk_seed a counter, counter))
        by (unfold shrincs_wots_sign; rewrite E; reflexivity).
      rewrite Hsign.
      change sig_bytes with 514.
      rewrite sign_chains_map.
      change len with 32%nat.
      (* v_digits / v_counter are dead: drop their computed contents BEFORE the
         closing [entailer!], so [cancel] does not grind them against the
         stackframe [data_at_] default_val. *)
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 32)
                   (digits_to_vals (digest_of pk_seed a msg counter)) v_digits).
      sep_apply (data_at_data_at_ Tsh tuint (Vint (Int.repr counter)) v_counter).
      entailer!.

  - (* ===== None: grinding failed, return SHRINCS_WOTS_SIGN_FAILED ===== *)
    symmetry in E.   (* E : find_counter pk_seed a msg = None *)
    forward_if.
    + (* return -2.  The grinding call left [addr] grind-typed, so answer the
         postcondition existential with [shrincs_wots_grind_adrs a]. *)
      forward.
      Exists (shrincs_wots_grind_adrs a).
      assert (Hsign : shrincs_wots_sign msg sk_seed pk_seed a = None)
        by (unfold shrincs_wots_sign; rewrite E; reflexivity).
      rewrite Hsign.
      entailer!.
    + (* unreachable: shrincs_wots_grind_to_constant_sum returned 1 (failure) here, so
         guard-false (1 = 0) never happens *)
      discriminate.
Qed.
