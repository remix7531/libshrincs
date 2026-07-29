(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_verify: VST body proof for [shrincs_wots_verify]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
From Vst Require Import model.wots.

Open Scope Z_scope.

(* Keep the heavy chain / digest definitions folded during the closing
   [cancel]'s "close by conversion": otherwise the [Qed] kernel check
   delta-unfolds the port's 32-chain recovery loop and the grinding
   digest, and diverges.  ([to_bytes] stays TRANSPARENT: the counter
   prefix has to convert with the two concrete cells [start_function]
   computes it down to.) *)
Local Opaque shrincs.wots_c_pubkey_from_sig shrincs.T_sf shrincs.sha256
             digest_of good_counter.

Lemma body_shrincs_wots_verify : semax_body Vprog Gprog f_shrincs_wots_verify shrincs_wots_verify_spec.
Proof.
  (* WOTS+C shrincs_wots_verify.  Allocate the scratch buffer [pk_cand], recompute the
     candidate public key with [shrincs_wots_pubkey_from_sig], and (on success)
     compare it against [pk] with the constant-time [shrincs_ct_memcmp].
       - pk_from_sig recovers a candidate iff the digest at [counter] is
         constant-sum ([good_counter]); on failure shrincs_wots_verify rejects.
       - on success ct_memcmp returns 0 iff pk_cand = pk as C bytes, i.e.
         iff [block_ints pkc = block_ints pk]; the equal case yields
         [wc_verify = true], the differing case false.
     In WOTS+C both the candidate and [pk] are single [n]-byte blocks, so the
     compare is a single 16-byte block compare (no concat / block splitting). *)
  start_function.
  rename H into Hpklen.
  rename H0 into Hsiglen.
  rename H1 into Hctr.
  rename H2 into Hmsglen.
  rename H3 into Hpslen.
  rename H4 into Hsigblk.

  (* ===== The recovery, reassembled once =====
     [Model.theory.shrincs] section 5.6, at the spec's flat signature
     layout: the port recovers a candidate exactly on a good counter.
     This is the single bridge from the callee's port-level POST to the
     per-counter view both this body and the verify POST are keyed on. *)
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
    - exact Hctr.
    - exact Hsiglen.
    - rewrite Forall_forall in Hsigblk.
      intros b Hb.
      specialize (Hsigblk b Hb).
      rewrite Zlength_correct, n_bytes_eq in Hsigblk.
      lia. }

  (* pk_cand <- shrincs_wots_pubkey_from_sig(pk_cand, sig, msg, pk_seed, addr) *)
  forward_call (v_pk_cand, sig_ptr, msg_ptr, ps_ptr, a_ptr,
                sig, counter, msg, pk_seed, a,
                Tsh, sh_sig, sh_m, sh_ps, sh_a).
  (* The callee POST fixes both the recovered candidate and the residual
     address concretely, each keyed on the port's own accept/reject. *)

  (* Split on the counter's constant-sum gate = the callee's status. *)
  destruct (good_counter pk_seed (anchor_nh a) (anchor_ni a) msg counter) eqn:Hgc.

  (* ===== good counter: pk_cand holds the recovered candidate; compare against pk ===== *)
  - (* Name the candidate abstractly: the compare and the three
       [contract.lemmas.shrincs_wots_verify] links only ever need that
       recovery returned it, and that it is [n] bytes wide. *)
    assert (Hrec : exists pkc : block,
              shrincs.wots_c_pubkey_from_sig
                (shrincs.to_bytes counter 2 ++ shrincs.concat sig) msg pk_seed
                (adrs_bytes a) = Some pkc
              /\ Zlength pkc = n_bytes).
    { rewrite Hends.
      eexists.
      split; [ reflexivity | apply T_sf_Zlength ]. }
    destruct Hrec as (pkc & Hsome & Hlpkc).
    (* [setoid_rewrite] (not [rewrite]): [start_function] has already
       computed the counter prefix inside the flat signature argument. *)
    setoid_rewrite Hsome.

    (* the (_t'1 != 0) guard is dead here: _t'1 = 0 *)
    forward_if.
    { discriminate. }

    (* Expose both buffers as [map Vint (block_ints ...)] for ct_memcmp. *)
    rewrite (block_to_vals_eq_Vint pkc).
    rewrite (block_to_vals_eq_Vint pk).
    change pk_bytes with 16.

    (* shrincs_ct_memcmp(pk_cand, pk, SHRINCS_WOTS_PK_BYTES) *)
    forward_call (Tsh, sh_pk, v_pk_cand, pk_ptr, 16,
                  block_ints pkc, block_ints pk).
    { (* both buffers are 16 bytes with entries in [0, 256) *)
      repeat split.
      - rewrite Zlength_block_ints, Hlpkc.
        rep_lia.
      - rewrite Zlength_block_ints, Hpklen.
        rep_lia.
      - apply Forall_block_ints_bound.
      - apply Forall_block_ints_bound. }
    Intros vret.
    match goal with H : _ <-> _ |- _ => rename H into Hmemcmp end.

    (* Branch on the compare result: 0 iff the candidate matches pk. *)
    forward_if (
      PROP ( )
      LOCAL (temp _t'3
               (Vint (Int.repr
                        (if wc_verify pk (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                               msg pk_seed (adrs_bytes a)
                         then 0 else -1)));
             lvar _pk_cand (tarray tuchar 16) v_pk_cand; temp _pk pk_ptr;
             temp _sig sig_ptr; temp _msg msg_ptr; temp _pk_seed ps_ptr;
             temp _addr a_ptr)
      SEP (data_at Tsh (tarray tuchar 16) (map Vint (block_ints pkc)) v_pk_cand;
           data_at sh_pk (tarray tuchar 16)
             (map Vint (block_ints pk)) pk_ptr;
           data_at sh_sig (tarray tuchar sig_bytes)
             (block_to_vals (shrincs.to_bytes counter 2) ++ blocks_to_vals sig) sig_ptr;
           data_at sh_m (tarray tuchar msg_bytes) (block_to_vals msg) msg_ptr;
           data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
           (* good counter here (branch [Hgc]): the callee left the pk-typed
              address, which the [if true] in the callee POST reduces to. *)
           data_at sh_a t_addr (adrs_to_vals (shrincs_wots_pk_adrs a)) a_ptr)).

    + (* compare = 0: candidate equals pk, so the port's verifier accepts *)
      match goal with H : vret = _ |- _ => rename H into Hzero end.
      assert (Hbe : block_ints pkc = block_ints pk)
        by (apply Hmemcmp; rewrite Hzero; reflexivity).
      (* ct_memcmp only sees the blocks mod 256 ([block_ints]), but that view
         is injective on [byte] blocks (the range is intrinsic now), so the
         mod-256 equality [Hbe] recovers exact block equality, which
         [wc_verify] compares. *)
      assert (Hverify : wc_verify pk (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                          msg pk_seed (adrs_bytes a) = true)
        by (apply (pk_int_eq_implies_verify pk pkc); [ exact Hsome | exact Hbe ]).
      forward.
      rewrite Hverify.
      entailer!.

    + (* compare <> 0: candidate differs from pk, so the port's verifier rejects *)
      match goal with H : vret <> _ |- _ => rename H into Hnz end.
      assert (Hneq : block_ints pkc <> block_ints pk).
      { intro Hc.
        apply Hnz.
        apply Hmemcmp in Hc.
        rewrite Hc.
        reflexivity. }
      assert (Hverify : wc_verify pk (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                          msg pk_seed (adrs_bytes a) = false)
        by (apply (pk_int_neq_implies_verify_false pk pkc); [ exact Hsome | exact Hneq ]).
      forward.
      rewrite Hverify.
      entailer!.

    + (* join: return the computed status.  Restore [pk] to its funspec
         [block_to_vals] shape and retire the dead [pk_cand] to [data_at_],
         then [cancel] closes.  The verify POST fixes the residual address
         concretely; with [Hgc] the [if] reduces to [shrincs_wots_pk_adrs a],
         matching the invariant. *)
      forward.
      change pk_bytes with 16.
      rewrite <- (block_to_vals_eq_Vint pk).
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 16)
        (map Vint (block_ints pkc)) v_pk_cand).
      entailer!.

  (* ===== bad counter: _t'1 = -1, pk_cand untouched; reject ===== *)
  - (* [destruct] specialised [Hends] to this branch: recovery is [None]. *)
    setoid_rewrite Hends.
    forward_if.
    + (* _t'1 = -1 <> 0: return VERIFY_FAILED.  The untouched buffers match the
         postcondition verbatim, so once the return value is rewritten to the
         model's [false] case the SEP cancels and [entailer!] closes.  The
         verify POST's residual address is [shrincs_wots_grind_adrs a] here
         (the callee's [if false] branch), matching the untouched buffer. *)
      forward.
      assert (Hverify : wc_verify pk (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                          msg pk_seed (adrs_bytes a) = false)
        by (apply from_sig_None_implies_verify_false; exact Hends).
      setoid_rewrite Hverify.
      entailer!.
    + (* dead: _t'1 = -1 cannot be 0 *)
      discriminate.
Qed.
