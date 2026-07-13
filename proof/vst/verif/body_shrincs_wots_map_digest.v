(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_map_digest: VST body proof for [shrincs_wots_map_digest]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import model.wots.
Import ListNotations.

Open Scope Z_scope.

(* The nibble-store reductions [digest_store_hi] / [digest_store_lo] are
   shared -- see [contract.lemmas.arith_nibble], beside [nibble_hi] /
   [nibble_lo]. *)

(* ================================================================= *)
(** ** The grind-address fold (closed by the clean-anchor precondition).

    The model grind address is
    [shrincs_wots_grind_adrs a := Wc_grind (adrs_nh a) (adrs_ni a)],
    whose three payload words are ZERO ([payload_a_z]/[payload_b_z]/
    [payload_c_z] of a [Wc_grind] all fall into the [_ => 0] arm).  So
    [adrs_bytes (shrincs_wots_grind_adrs a)] ends in
    [to_byte 0 4 ++ to_byte 0 4 ++ to_byte 0 4].

    The C ([src/wots.c] and the generated Clight agree) writes ONLY the
    type byte -- [addr[ADRS_TYPE] = SF_SHRINCS_WOTS_GRIND] -- and does
    NOT touch the payload bytes 10..21.  So after the store the buffer
    is [radrs_bytes (rset_type (adrs_to_raw a) 22)], which KEEPS a's
    original payload words
    [to_byte (payload_a_z a) 4 ++ to_byte (payload_b_z a) 4 ++ to_byte (payload_c_z a) 4].

    The gap this once opened (a nonzero-payload [a] would make the two
    byte lists differ) is now closed at the spec boundary:
    [shrincs_wots_map_digest_spec] carries the clean-anchor precondition
    [payload_a_z a = 0 /\ payload_b_z a = 0 /\ payload_c_z a = 0], which
    the caller [body_shrincs_wots_grind_to_constant_sum] discharges.
    Under those three hyps both byte lists carry zero payload words, so
    the fold [grind_addr_stores] (shared, in
    [contract.lemmas.chain_blocks]) holds outright. *)

(* ================================================================= *)
(** ** [shrincs_wots_map_digest] body proof.

    [shrincs_wots_map_digest(digits, msg, counter, pk_seed, addr)] first types
    the address ([addr[9] = SF_SHRINCS_WOTS_GRIND]) then runs [shrincs_wots_h_grind] into a
    local [hg[16]], expands each byte into its two base-16 nibbles across
    [digits[32]], and returns the digit sum.  [shrincs_wots_h_grind] reads the address
    after the type store, so the digest is keyed on [shrincs_wots_grind_adrs a].

    - Phase 0 (type store): [addr[9] = 22]; switch the addr buffer to the
      wire view ([adrs_to_vals_raw]), fold the store via [upd_adrs_type]
      into [rset_type (adrs_to_raw a) 22], then fold the buffer to the
      union grind address via [grind_addr_stores] (clean-anchor PROPs)
      and [forward_call shrincs_wots_h_grind] with [shrincs_wots_grind_adrs a].
    - Phase 1 (nibble loop): [forward_for_simple_bound 16]; the invariant
      carries [digits = digits_to_vals (flat_map nibble_f (sublist 0 i hg))
      ++ Zrepeat Vundef (32 - 2*i)]; each step is [nibble_step_shape].
    - After phase 1 the whole [sublist] collapses (via [digest_of_flat_map])
      to [digits_to_vals (digest_of ...)].
    - Phase 2 (sum loop): [forward_for_simple_bound 32] with running-sum
      [temp _sum (list_sum (firstn (Z.to_nat j) (digest_of ...)))]; each step
      is [firstn_S_snoc] + [list_sum_app]; digits are <= 15 so no overflow. *)

Lemma body_shrincs_wots_map_digest : semax_body Vprog Gprog f_shrincs_wots_map_digest shrincs_wots_map_digest_spec.
Proof.
  start_function.
  (* Unpack the clean-anchor precondition into the three per-field payload
     facts [grind_addr_stores] needs to fold the type store. *)
  match goal with H : clean_anchor a |- _ => destruct H as [Hpa [Hpb Hpc]] end.

  (* ===== Phase 0: addr[ADRS_TYPE] = SF_SHRINCS_WOTS_GRIND (22) =====
     [store_type_byte] folds the direct type-byte store into
     [rset_type (adrs_to_raw a) 22]. *)
  store_type_byte.
  (* Fold the under-construction wire buffer to the union grind address
     (the clean-anchor precondition discharges the payload-zero side goals). *)
  rewrite grind_addr_stores by assumption.

  (* shrincs_wots_h_grind(hg, msg, counter, pk_seed, addr): reads the grind-typed addr,
     so [hg := block_to_vals (H_grind pk_seed (shrincs_wots_grind_adrs a) ...)] *)
  forward_call (v_hg, m_ptr, counter, ps_ptr, a_ptr, msg, pk_seed,
                shrincs_wots_grind_adrs a, Tsh, sh_m, sh_ps, sh_a).

  (* ===== Phase 1: digits[2i] = hg[i] >> 4; digits[2i+1] = hg[i] & 0x0f ===== *)
  forward_for_simple_bound 16
    (EX i : Z,
      PROP ()
      LOCAL (lvar _hg (tarray tuchar 16) v_hg; temp _digits d_ptr;
             temp _msg m_ptr; temp _counter (Vint (Int.repr counter));
             temp _pk_seed ps_ptr; temp _addr a_ptr)
      SEP (data_at Tsh (tarray tuchar n_bytes)
             (block_to_vals (H_grind pk_seed (shrincs_wots_grind_adrs a) msg counter)) v_hg;
           data_at sh_m (tarray tuchar msg_bytes) (block_to_vals msg) m_ptr;
           data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
           data_at sh_a t_addr (adrs_to_vals (shrincs_wots_grind_adrs a)) a_ptr;
           data_at sh_d (tarray tuchar 32)
             (digits_to_vals
                (flat_map nibble_f
                   (sublist 0 i (H_grind pk_seed (shrincs_wots_grind_adrs a) msg counter)))
              ++ Zrepeat Vundef (32 - 2 * i)) d_ptr)).
  - (* loop entry *)
    unfold t_addr.
    entailer!!.
  - (* loop body *)
    assert (HlHG : Zlength (H_grind pk_seed (shrincs_wots_grind_adrs a) msg counter) = 16)
      by apply H_grind_Zlength.
    (* t'3 = hg[i] *)
    forward.
    { close_tc_byte. }
    (* digits[2*i + 0] = (uint8_t)(t'3 >> 4) *)
    forward.
    (* t'2 = hg[i] (second load of the same cell; forward discharges its tc itself) *)
    forward.
    (* digits[2*i + 1] = (uint8_t)(t'2 & 0x0f) *)
    forward.
    (* re-establish the nibble invariant *)
    entailer!!.
    apply derives_refl'.
    f_equal.
    rewrite Znth_block_to_vals, digest_store_hi, digest_store_lo by lia.
    apply (nibble_step_shape (H_grind pk_seed (shrincs_wots_grind_adrs a) msg counter) i ltac:(lia)
             (H_grind_Zlength pk_seed (shrincs_wots_grind_adrs a) msg counter)).
  - (* ===== after phase 1: digits = digits_to_vals (digest_of ...) ===== *)
    pose proof (H_grind_Zlength pk_seed (shrincs_wots_grind_adrs a) msg counter) as HlHG.
    rewrite sublist_same by lia.
    change (32 - 2 * 16) with 0.
    rewrite Zrepeat_0, app_nil_r.
    rewrite <- digest_of_flat_map.
    (* sum = 0 *)
    forward.

    (* ===== Phase 2: sum += digits[i] ===== *)
    forward_for_simple_bound 32
      (EX j : Z,
        PROP ()
        LOCAL (temp _sum (Vint (Int.repr (Z.of_nat
                 (list_sum (firstn (Z.to_nat j) (digest_of pk_seed a msg counter))))));
               lvar _hg (tarray tuchar 16) v_hg; temp _digits d_ptr;
               temp _msg m_ptr; temp _counter (Vint (Int.repr counter));
               temp _pk_seed ps_ptr; temp _addr a_ptr)
        SEP (data_at Tsh (tarray tuchar n_bytes)
               (block_to_vals (H_grind pk_seed (shrincs_wots_grind_adrs a) msg counter)) v_hg;
             data_at sh_m (tarray tuchar msg_bytes) (block_to_vals msg) m_ptr;
             data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
             data_at sh_a t_addr (adrs_to_vals (shrincs_wots_grind_adrs a)) a_ptr;
             data_at sh_d (tarray tuchar 32)
               (digits_to_vals (digest_of pk_seed a msg counter)) d_ptr)).
    + (* loop entry *)
      entailer!!.
    + (* loop body *)
      pose proof (digest_of_Zlength pk_seed a msg counter) as HlDIG.
      (* t'1 = digits[i] *)
      forward.
      { close_tc_byte_digit. }
      (* sum = sum + t'1 *)
      forward.
      (* re-establish the running-sum invariant *)
      assert (Hstep :
        Z.of_nat (list_sum (firstn (Z.to_nat (i + 1)) (digest_of pk_seed a msg counter)))
        = Z.of_nat (list_sum (firstn (Z.to_nat i) (digest_of pk_seed a msg counter)))
          + Z.of_nat (Znth i (digest_of pk_seed a msg counter))).
      { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        rewrite (firstn_S_snoc (Z.to_nat i) (digest_of pk_seed a msg counter) O)
          by (rewrite <- ZtoNat_Zlength, HlDIG; lia).
        rewrite nth_Znth by lia.
        rewrite list_sum_app.
        change (list_sum (Znth i (digest_of pk_seed a msg counter) :: nil))
          with (Znth i (digest_of pk_seed a msg counter) + 0)%nat.
        lia. }
      rewrite Hstep.
      entailer!!.
      (* the loaded digit is <= 15, so [Byte.unsigned (Byte.repr d)] is [d]
         itself; [add_repr] then folds the C-side [Int.add] into the model sum *)
      unfold digits_to_vals.
      rewrite Znth_map by lia.
      unfold Vubyte.
      rewrite Byte.unsigned_repr
        by (pose proof (nth_digest_le_15 pk_seed a msg counter i ltac:(lia)); rep_lia).
      cbn [force_val both_int sem_cast_i2i cast_int_int].
      now rewrite add_repr.
    + (* ===== return: firstn 32 (digest_of ...) = digest_of ...; sum = list_sum ===== *)
      rewrite firstn_all2 by (rewrite <- ZtoNat_Zlength, digest_of_Zlength; lia).
      forward.
      entailer!!.
Qed.
