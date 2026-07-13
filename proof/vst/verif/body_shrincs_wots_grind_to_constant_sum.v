(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_grind_to_constant_sum: VST body proof for [shrincs_wots_grind_to_constant_sum]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import model.wots.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* Keep the fuel-heavy definitions symbolic in the body proof: [find_counter]
   / [find_from] carry the fuel [Z.to_nat c_max = Z.to_nat (2^16)], and
   [good_counter] / [digest_of] carry [H_grind]; reducing any of them would
   force the huge nat and blow the kernel stack at [Qed]. *)
Local Opaque find_counter find_from good_counter digest_of.

(** Derive the [Z] counter bound from the [Int64] loop-guard hypothesis
    [HRE]: normalize both [Int64.unsigned (Int64.repr _)] sides ([i] by
    the invariant bound, the [c_max] literal by [vm_compute]) and
    conclude by [lia].  Used for both the in-loop [i < c_max] and the
    post-loop [i = c_max] bounds. *)
Ltac counter_guard_bound HRE :=
  unfold c_max in *;
  rewrite !Int64.unsigned_repr in HRE by rep_lia;
  vm_compute Int64.unsigned in HRE;
  lia.

Lemma body_shrincs_wots_grind_to_constant_sum : semax_body Vprog Gprog f_shrincs_wots_grind_to_constant_sum shrincs_wots_grind_to_constant_sum_spec.
Proof.
  (* The least-counter search as a [forward_while]: the invariant tracks the
     iteration [i] ([0 <= i <= c_max = 2^16]), the fact that every counter
     below [i] is bad ([good_counter ... = false]), and the mutated ADRS [A]
     (grind-typed, [shrincs_wots_grind_adrs A = shrincs_wots_grind_adrs a]; concretely
     [A = a] only before the first iteration).  The THEN branch turns
     [sum = 240] into [good_counter i = true] and bridges to
     [find_counter = Some i] via [find_counter_Some_least]; exhaustion
     ([i = c_max]) bridges to [find_counter = None] via [find_counter_None];
     either way the POST's [match find_counter ...] collapses by rewriting
     the bridge equation.

     CRITICAL: never [destruct]/[compute]/[unfold] [find_counter] -- the kernel
     would force its fuel [Z.to_nat c_max] and blow the stack.  Use ONLY the
     abstract lemmas [find_counter_Some_least] / [find_counter_None]. *)
  start_function.
  (* Unpack the clean-anchor precondition into the three per-field payload
     facts the loop invariant threads (entry instantiates [A := a]).  The
     destination names [H1]-[H3] reproduce the pre-[clean_anchor] context
     exactly, keeping the numbered references below stable. *)
  match goal with H : clean_anchor a |- _ => destruct H as [H1 [H2 H3]] end.
  (* counter = 0 *)
  forward.
  (* while (counter < (1 << 16)) -- linear search for the least good counter *)
  forward_while
    (EX i : Z, EX A : adrs,
     PROP (0 <= i <= c_max;
           shrincs_wots_grind_adrs A = shrincs_wots_grind_adrs a;
           i = 0 \/ A = shrincs_wots_grind_adrs a;
           forall c : Z, 0 <= c < i -> good_counter pk_seed a msg c = false;
           (* clean anchor threaded to [shrincs_wots_map_digest]: at entry
              [A = a] (clean by PRE), on re-entry [A = shrincs_wots_grind_adrs a]
              (clean by construction). *)
           payload_a_z A = 0; payload_b_z A = 0; payload_c_z A = 0)
     LOCAL (temp _counter (Vlong (Int64.repr i));
            temp _digits d_ptr; temp _counter_out c_ptr; temp _msg m_ptr;
            temp _pk_seed ps_ptr; temp _addr a_ptr)
     SEP (data_at_ sh_d (tarray tuchar (Z.of_nat len)) d_ptr;
          data_at_ sh_c tuint c_ptr;
          data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)     m_ptr;
          data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
          data_at sh_a  t_addr                  (adrs_to_vals A)         a_ptr))%assert.
  - (* entry: i = 0, A = a; the "no good counter below 0" premise is vacuous *)
    Exists 0 a.
    entailer!!.
    unfold c_max; lia.
  - (* the loop guard type-checks *)
    entailer!.
  - (* loop body: the true guard sharpens the invariant bound to i < c_max = 2^16 *)
    assert (Hi : i < c_max) by (counter_guard_bound HRE).
    (* Repackage the loop invariant's per-field payload facts into the single
       clean-anchor hypothesis [shrincs_wots_map_digest] now requires. *)
    assert (Hca : clean_anchor A).
    { unfold clean_anchor.
      repeat split.
      all: assumption. }
    (* sum = shrincs_wots_map_digest(digits, msg, (uint32_t)counter, pk_seed, addr) *)
    forward_call (d_ptr, m_ptr, i, ps_ptr, a_ptr,
                  msg, pk_seed, A, sh_d, sh_m, sh_ps, sh_a).
    { (* the (uint32_t)counter argument is Vint (Int.repr i) exactly, since i < 2^16 *)
      cbn.
      entailer!!.
      do 3 f_equal.
      rewrite Int64.Z_mod_modulus_eq, Zmod_small by (unfold c_max in *; rep_lia).
      reflexivity. }
    { (* shrincs_wots_map_digest's counter bound *)
      unfold c_max in Hi; lia. }
    (* the mutated buffer digits/sum are over [A]; rekey onto the original [a] *)
    rewrite (digest_of_grind_eq pk_seed A a msg i H5).
    (* if (sum == SHRINCS_WOTS_CONSTANT_SUM = 240) *)
    forward_if.
    + (* THEN: good counter found at i; store *counter_out = i and return 0 *)
      assert (Hsum : Z.of_nat (list_sum (digest_of pk_seed a msg i)) = 240)
        by (apply digest_sum_repr_240; exact H11).
      assert (Hgood : good_counter pk_seed a msg i = true)
        by (apply good_counter_Z_iff; exact Hsum).
      assert (Hfc : find_counter pk_seed a msg = Some i)
        by (apply find_counter_Some_least; [ lia | exact Hgood | exact H7 ]).
      (* *counter_out = (uint32_t)counter *)
      forward.
      (* return 0 *)
      forward.
      (* find_counter = Some i collapses the POST match without reducing find_counter *)
      rewrite Hfc.
      (* the buffer ADRS is now [shrincs_wots_grind_adrs A = shrincs_wots_grind_adrs a] *)
      rewrite H5.
      (* the stored (uint32_t)counter collapses to [i] since [i < 2^16] *)
      replace (Int64.Z_mod_modulus i) with i
        by (rewrite Int64.Z_mod_modulus_eq, Zmod_small
              by (unfold c_max in *; rep_lia); reflexivity).
      entailer!!.
    + (* ELSE: sum <> 240, so this counter is bad; continue with counter + 1 *)
      assert (Hgood : good_counter pk_seed a msg i = false)
        by (apply not_true_is_false; intros E%good_counter_Z_iff; congruence).
      (* counter++ *)
      forward.
      (* the freshly written digits are dead across iterations: weaken to
         data_at_ up front so cancel matches syntactically *)
      sep_apply (data_at_data_at_ sh_d (tarray tuchar (Z.of_nat len))
                   (digits_to_vals (digest_of pk_seed a msg i)) d_ptr).
      (* the ADRS is now [shrincs_wots_grind_adrs A]; by idempotency it is
         [shrincs_wots_grind_adrs a], so re-enter with [A := shrincs_wots_grind_adrs a] *)
      Exists (i + 1, shrincs_wots_grind_adrs a).
      rewrite H5.
      entailer!!.
      split.
      * (* the counter is still in range *)
        lia.
      * (* extend "bad below i" to "bad below i+1" via good_counter i = false *)
        intros c Hc.
        destruct (Z.eq_dec c i) as [->|Hne]; [ exact Hgood | apply H7; lia ].
  - (* after the loop: guard false and i <= c_max force i = c_max; since the
       loop ran at least once, A = shrincs_wots_grind_adrs a *)
    assert (Hic : i = c_max) by (counter_guard_bound HRE).
    assert (HA : A = shrincs_wots_grind_adrs a).
    { destruct H6 as [Hi0 | HAeq]; [ subst i; unfold c_max in Hic; lia | exact HAeq ]. }
    subst A.
    (* no good counter below c_max => find_counter = None (no find_counter reduction) *)
    assert (Hfc : find_counter pk_seed a msg = None)
      by (apply find_counter_None; rewrite <- Hic; exact H7).
    (* return 1 *)
    forward.
    rewrite Hfc.
    entailer!!.
Qed.
