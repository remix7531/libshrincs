(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_chain_iter: VST body proof for [shrincs_wots_chain_iter].

    The C loop [for (j=0; j<steps; j++)] runs, at each index [j],
    [shrincs_adrs_put32(addr, ADRS_HASH=18, start+j)] (which writes the
    position word) followed by the in-place [shrincs_thash(node,
    pk_seed, addr)] (the chain step [F]).  The loop invariant at index [j]
    says [node] holds [wc_chain pk_seed .. in_buf start j] and [addr]
    holds [chain_addr_post a start j].

    The funspec's [PROP] carries [exists nh ni chain pos, a = Wc_hash ..]:
    after [Model.address.adrs] became a dependent union, the position
    setter [set_hash_pos] is the identity on every non-[Wc_hash] arm, so
    the C's unconditional position store only refines the model on the
    hash arm (the WOTS+C chain type the caller always sets).  The body
    binds that witness and runs the loop over the [Wc_hash] address. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.

Open Scope Z_scope.

(* The [wc_chain] step law this loop leans on ([wc_chain_step], the
   [Z]-indexed form of [Model.theory.shrincs]'s [wc_chain_succ]) is
   shared -- see [contract.lemmas.chain_blocks].  Loop entry is
   [wc_chain_0] straight from the model. *)

Local Notation adrs := (address.adrs len w_pred).

(** The per-step wire/byte bridge for the loop's position store: splicing
    position [p] into the raw wire view ([adrs_to_raw]) of the carried
    address [chain_addr_post (Wc_hash ..) s k] serialises to exactly the
    union address [Wc_hash nh ni chain (to_pos15 (Z.to_nat p))].  The
    prior position (the [pos] of the [k = 0] arm, or the stepped
    [to_pos15 (s + _)] of the [k = S _] arm) drops out because
    [rset_payload_c] overwrites the one wire field in which the two
    [chain_addr_post] arms differ; the other five wire fields agree
    byte-for-byte.  File-local: this is the only body that stores a
    position over an address it has itself already stepped. *)
Lemma rset_payload_c_chain_addr_post_vals :
  forall nh ni chain pos (s k : nat) (p : Z),
    0 <= p < 15 ->
    block_to_vals
      (radrs_bytes
         (rset_payload_c
            (adrs_to_raw (chain_addr_post (Wc_hash nh ni chain pos) s k))
            p))
    = adrs_to_vals (Wc_hash nh ni chain (to_pos15 (Z.to_nat p))).
Proof.
  intros nh ni chain pos s k p Hp.
  unfold adrs_to_vals.
  f_equal.
  (* Both [chain_addr_post] arms expose a [Wc_hash] whose position field
     [rset_payload_c] overwrites, so one tactic sequence closes both. *)
  destruct k as [|k'];
    unfold chain_addr_post, set_hash_pos, adrs_to_raw, rset_payload_c,
      radrs_bytes, adrs_bytes;
    cbn [rtag ridx rtype rpa rpb rpc adrs_anchor_tag_z adrs_anchor_idx_z
         payload_a_z payload_b_z payload_c_z adrs_type];
    rewrite to_pos15_val by lia;
    rewrite Z2Nat.id by lia;
    reflexivity.
Qed.

(** The value-side counterpart: the union address the store leaves behind
    serialises to the byte address [wc_chain]'s fold hashes under at
    position [p].  The shared [adrs_bytes_hash_pos] (section 5.1b) is
    stated through the smart constructors; this loop carries the bare
    [Wc_hash] the funspec's [PROP] handed it, hence the file-local
    restatement -- and it is the only place the two meet. *)
Lemma wc_hash_adrs_Wc_hash :
  forall (nh : fin 256) (ni : fin (2 ^ 64)) (ch : fin (Z.of_nat len))
         (cp : fin (Z.of_nat w_pred)) (p : Z),
    0 <= p < 15 ->
    wc_hash_adrs (anchor_nh (Wc_hash nh ni ch cp : adrs))
                 (anchor_ni (Wc_hash nh ni ch cp : adrs))
                 (chain_of (Wc_hash nh ni ch cp : adrs)) p
    = adrs_bytes (Wc_hash nh ni ch (to_pos15 (Z.to_nat p)) : adrs).
Proof.
  intros nh ni ch cp p Hp.
  rewrite adrs_bytes_mk_adrs.
  cbn [adrs_anchor_tag_z adrs_anchor_idx_z adrs_type
       payload_a_z payload_b_z payload_c_z].
  rewrite to_pos15_val by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma body_shrincs_wots_chain_iter : semax_body Vprog Gprog f_shrincs_wots_chain_iter shrincs_wots_chain_iter_spec.
Proof.
  start_function.
  rename H into Hstart.
  rename H0 into Hsteps.
  rename H1 into Hbound.
  rename H2 into Hlen_in.
  rename H3 into Hlen_ps.
  unfold n_bytes in *.
  change (Z.of_nat n) with 16 in *.

  (* Bind the hash-address precondition [a = Wc_hash nh ni chain pos]. *)
  match goal with
  | Hh : exists _ _ _ _, a = Wc_hash _ _ _ _ |- _ =>
      destruct Hh as (nh & ni & chain & pos & ->)
  end.

  (* ===== The [for] loop, invariant at index [j].  The per-iteration scratch
     [in] stack buffer ([v_in]) is carried as a plain [data_at_]: it is
     re-filled by [memcpy] each iteration and its content never crosses the
     loop boundary. ===== *)
  forward_for_simple_bound steps
    (EX j : Z,
      PROP ()
      LOCAL (lvar _in (tarray tuchar 16) v_in;
             temp _node buf_ptr;
             temp _start (Vint (Int.repr start));
             temp _steps (Vint (Int.repr steps));
             temp _pk_seed ps_ptr;
             temp _addr a_ptr)
      SEP (data_at sh_b (tarray tuchar 16)
             (block_to_vals
                (wc_chain pk_seed
                   (anchor_nh (Wc_hash nh ni chain pos))
                   (anchor_ni (Wc_hash nh ni chain pos))
                   (chain_of (Wc_hash nh ni chain pos))
                   in_buf start j))
             buf_ptr;
           data_at_ Tsh (tarray tuchar 16) v_in;
           data_at sh_ps (tarray tuchar 16)
             (block_to_vals pk_seed) ps_ptr;
           data_at sh_a t_addr
             (adrs_to_vals
                (chain_addr_post (Wc_hash nh ni chain pos)
                   (Z.to_nat start) (Z.to_nat j)))
             a_ptr)).

  (* ===== Loop-bound side condition: [steps] representable ([<= w_pred]) ===== *)
  - unfold w_pred in Hbound.
    rep_lia.

  (* ===== Loop entry ([j = 0]): matches the precondition ===== *)
  - change (Z.to_nat 0) with 0%nat.
    rewrite wc_chain_0.
    cbn [chain_addr_post].
    entailer!!.

  (* ===== Loop body at index [i] ===== *)
  - rename H into Hi.
    assert (Hrange : 0 <= start + i < 15) by (unfold w_pred in Hbound; lia).

    (* Present the carried address over the wire (raw [radrs]) view. *)
    rewrite adrs_to_vals_raw.

    (* shrincs_adrs_put32(addr, ADRS_HASH=18, (uint32_t)(start + i)) --
       forward_call auto-discharges its side conditions (the wire view has
       [Zlength = 22] and [start + i] is representable). *)
    forward_call (a_ptr, 18, start + i,
                  radrs_bytes (adrs_to_raw
                    (chain_addr_post (Wc_hash nh ni chain pos)
                       (Z.to_nat start) (Z.to_nat i))),
                  sh_a).

    (* Fold the raw-byte splice into the position setter on the wire view. *)
    rewrite shrincs_adrs_put32_hash.

    (* The wire-view store of position [start+i] re-serialises the union
       address [Wc_hash .. (to_pos15 (start+i))] (the file-local bridge
       above); [Hrange] discharges the position-in-range side condition. *)
    rewrite rset_payload_c_chain_addr_post_vals by lia.

    (* ===== memcpy(in, node, 16): snapshot the current node into scratch [in]
       (the C reads [in] as [shrincs_thash]'s message, since [out = node]
       aliases the destination). ===== *)
    sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 16 noattr) v_in).
    change (sizeof (Tarray tuchar 16 noattr)) with 16.
    rewrite (block_to_vals_eq_Vint
               (wc_chain pk_seed
                  (anchor_nh (Wc_hash nh ni chain pos))
                  (anchor_ni (Wc_hash nh ni chain pos))
                  (chain_of (Wc_hash nh ni chain pos))
                  in_buf start i)).
    forward_call (sh_b, Tsh, v_in, buf_ptr, 16,
                  block_ints (wc_chain pk_seed
                                (anchor_nh (Wc_hash nh ni chain pos))
                                (anchor_ni (Wc_hash nh ni chain pos))
                                (chain_of (Wc_hash nh ni chain pos))
                                in_buf start i)).

    (* Retire the node's old content ([out] is overwritten by the hash) and
       restore [in]'s snapshot to [block_to_vals] form for the message SEP. *)
    sep_apply (data_at_data_at_ sh_b (tarray tuchar 16)
                 (map Vint (block_ints (wc_chain pk_seed
                    (anchor_nh (Wc_hash nh ni chain pos))
                    (anchor_ni (Wc_hash nh ni chain pos))
                    (chain_of (Wc_hash nh ni chain pos))
                    in_buf start i))) buf_ptr).
    rewrite <- (block_to_vals_eq_Vint
                 (wc_chain pk_seed
                    (anchor_nh (Wc_hash nh ni chain pos))
                    (anchor_ni (Wc_hash nh ni chain pos))
                    (chain_of (Wc_hash nh ni chain pos))
                    in_buf start i)).

    (* shrincs_thash(node, pk_seed, addr, in, 16) -- [out = node], the message
       is the snapshot in [in]. *)
    forward_call (buf_ptr, ps_ptr, a_ptr, v_in, 16,
                  Wc_hash nh ni chain (to_pos15 (Z.to_nat (start + i))),
                  pk_seed,
                  wc_chain pk_seed
                    (anchor_nh (Wc_hash nh ni chain pos))
                    (anchor_ni (Wc_hash nh ni chain pos))
                    (chain_of (Wc_hash nh ni chain pos))
                    in_buf start i,
                  sh_b, sh_ps, sh_a, Tsh).
    { (* thash PRE PROP, proved whole (seed length, message length,
         SHA-256 range): forward_call's auto-discharge of the easy
         conjuncts is context-sensitive, so do not lean on it.  Only the
         iterated node's length ([wc_chain_Zlength]) is non-trivial. *)
      split3; [exact Hlen_ps | | lia].
      apply wc_chain_Zlength.
      exact Hlen_in. }

    (* Re-establish the invariant at [j = i + 1]: one more step via
       [wc_chain_step], whose hash address is the very one the position
       store left in [addr] (the second file-local bridge); the residual
       address is [chain_addr_post]'s [S _] arm ([set_hash_pos] on the hash
       arm).  [in] is weakened back to [data_at_] for the next iteration. *)
    rewrite (wc_chain_step pk_seed
               (anchor_nh (Wc_hash nh ni chain pos))
               (anchor_ni (Wc_hash nh ni chain pos))
               (chain_of (Wc_hash nh ni chain pos))
               in_buf start i) by lia.
    rewrite wc_hash_adrs_Wc_hash by lia.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    cbn [chain_addr_post set_hash_pos].
    replace (Z.to_nat start + Z.to_nat i)%nat with (Z.to_nat (start + i)) by lia.
    entailer!!.

  (* ===== Loop exit: invariant at [j = steps] is the postcondition ===== *)
  - entailer!!.
Qed.
