(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_c_grind_to_constant_sum: VST body proof for [shrincs_wots_c_grind_to_constant_sum].

    The loop tries the counters from 0 and returns at the first one the
    digest mapping accepts. The invariant at [j] says the mapping returns
    None at every counter below [j]. A hit at [j] is the reference's
    result by [wots_c_grind_some], and running out is None by
    [wots_c_grind_none].

    NOTHING HERE MAY EVALUATE THE REFERENCE. Its grinding loop ranges over
    2^16 counters and its digest mapping runs the digit conversion, so
    both are case-split on as opaque terms and rewritten with the two
    lemmas, never unfolded. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Lemma body_shrincs_wots_c_grind_to_constant_sum :
  semax_body Vprog Gprog_wots f_shrincs_wots_c_grind_to_constant_sum
    shrincs_wots_c_grind_to_constant_sum_spec.
Proof.
  start_function.
  pose proof (@wots_c_grind_some pk_seed message_digest node_height node_index) as Hfound.
  pose proof (@wots_c_grind_none pk_seed message_digest node_height node_index) as Hexhausted.

  forward_for_simple_bound 65536
    (EX j : Z,
      PROP (forall c : nat, Z.of_nat c < j ->
              wots_c_map_digest pk_seed message_digest node_height node_index (uint U16 c)
              = None)
      LOCAL (temp _indexes i_ptr; temp _pk_seed ps_ptr; temp _message_digest m_ptr;
             temp _node_height (Vint (Int.repr (wunsigned node_height)));
             temp _node_index (Vlong (Int64.repr (wunsigned node_index))))
      SEP (data_at_ sh_i (tarray tuchar 32) i_ptr;
           data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
           data_at sh_m (tarray tuchar 32) (vals message_digest) m_ptr)).
  - (* no counter is below 0 *)
    entailer!.
  - rename H into Hi.
    cbv beta.
    Intros.
    rename H into Hbelow.
    assert (Hrepr : Int.repr i = Int.repr (wunsigned (uint U16 (Z.to_nat i))))
      by (rewrite wunsigned_uint_u16 by lia; reflexivity).

    (* shrincs_wots_c_map_digest(indexes, pk_seed, message_digest, node_height, node_index, i) *)
    rewrite Hrepr.
    forward_call (i_ptr, ps_ptr, m_ptr, pk_seed, message_digest, node_height, node_index,
                  uint U16 (Z.to_nat i), sh_i, sh_ps, sh_m).
    rewrite <- Hrepr.
    destruct (wots_c_map_digest pk_seed message_digest node_height node_index
                (uint U16 (Z.to_nat i))) as [indexes|] eqn:Hmap.
    + (* the mapping accepts counter [i], the first it accepts *)
      forward_if.
      * (* return (int)i *)
        forward.
        rewrite (Hfound (Z.to_nat i) indexes).
        -- rewrite wunsigned_uint_u16 by lia.
           entailer!.
        -- rewrite Z2Nat.id by lia.
           change (2 ^ 16) with 65536.
           lia.
        -- intros c Hc.
           apply Hbelow.
           apply (elimT ltP) in Hc.
           lia.
        -- exact Hmap.
      * (* the call returned 1 *)
        discriminate.
    + (* the mapping rejects counter [i]: go on *)
      forward_if.
      * (* the call returned 0 *)
        discriminate.
      * forward.
        entailer!.
        intros c Hc.
        destruct (Z.eq_dec (Z.of_nat c) i) as [Heq|Hne].
        -- replace c with (Z.to_nat i) by lia.
           exact Hmap.
        -- apply Hbelow.
           lia.
  - (* all 2^16 counters rejected *)
    Intros.
    rename H into Hall.
    (* return -1 *)
    forward.
    rewrite Hexhausted.
    + entailer!.
    + intros c Hc.
      apply Hall.
      exact Hc.
Qed.
