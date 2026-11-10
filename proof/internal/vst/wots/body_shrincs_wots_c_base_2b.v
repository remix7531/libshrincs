(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_base_2b: VST body proof for [shrincs_wots_c_base_2b].

    One loop turn per input byte writes its high and its low nibble.
    The invariant after [i] bytes says the first [2 * i] cells hold the
    first [2 * i] digits of the reference's [base_2b], and [nth_indexes]
    says the two nibbles of byte [i] are digits [2 * i] and [2 * i + 1]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Lemma body_shrincs_wots_c_base_2b :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_base_2b shrincs_wots_c_base_2b_spec.
Proof.
  start_function.
  set (digits := index_vals (base_2b x WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT)).
  assert (Hdigits : Zlength digits = 32).
  { unfold digits.
    rewrite Zlength_index_vals.
    rewrite Zlength_base_2b.
    reflexivity. }
  forward_for_simple_bound 16
    (EX i : Z,
      PROP ()
      LOCAL (temp _indexes i_ptr; temp _x x_ptr)
      SEP (data_at sh_i (tarray tuchar 32)
             (app (sublist 0 (2 * i) digits) (Zrepeat Vundef (32 - 2 * i))) i_ptr;
           data_at sh_x (tarray tuchar 16) (vals x) x_ptr)).
  - entailer!.
  - rename H into Hi.
    assert (Hx : Zlength (tval x) = 16) by exact (Zlength_tuple 16 x).
    (* t = x[i] *)
    forward.
    { entailer!.
      apply tc_val_Znth_vals.
      lia. }
    rewrite Znth_vals by lia.
    (* indexes[2 * i + 0] = (uint8_t)(t >> 4) *)
    forward.
    (* t = x[i] *)
    forward.
    { entailer!.
      apply tc_val_Znth_vals.
      lia. }
    rewrite Znth_vals by lia.
    (* indexes[2 * i + 1] = (uint8_t)(t & 0x0f) *)
    forward.

    (* the two cells are digits [2 * i] and [2 * i + 1] *)
    rewrite index_hi_store.
    rewrite index_lo_store.
    pose proof (Znth_index_vals_base_2b Inhabitant_val x i Hi) as Hcells.
    cbv zeta in Hcells.
    fold digits in Hcells.
    destruct Hcells as [Hhi Hlo].
    rewrite <- Hhi.
    rewrite <- Hlo.
    entailer!.
    apply derives_refl'.
    f_equal.
    list_solve.
  - (* all sixteen bytes done: the array is the digits *)
    rewrite sublist_same by lia.
    change (32 - 2 * 16) with 0.
    rewrite Zrepeat_0.
    rewrite app_nil_r.
    entailer!.
Qed.
