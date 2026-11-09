(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_verify: VST body proof for [shrincs_wots_verify]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.
From Shrincs.internal.vst.support Require Import model.wots.

Open Scope Z_scope.

(* Keep the heavy chain / digest definitions folded during the closing
   [cancel]'s "close by conversion": otherwise the [Qed] kernel check
   delta-unfolds the 32-chain [shrincs_wots_pubkey_from_sig] / [shrincs_wots_chain_iter]
   map and the grinding digest, and diverges. *)
Local Opaque shrincs_wots_pubkey_from_sig digest_of valid_digest to_byte.

Lemma body_shrincs_wots_verify : semax_body Vprog Gprog f_shrincs_wots_verify shrincs_wots_verify_spec.
Proof.
  (* WOTS+C shrincs_wots_verify.  Allocate the scratch buffer [pk_cand], recompute the
     candidate public key with [shrincs_wots_pubkey_from_sig], and (on success)
     compare it against [pk] with the constant-time [shrincs_ct_memcmp].
       - pk_from_sig returns 0 iff the digest at [counter] is constant-sum
         ([valid_digest]); on failure shrincs_wots_verify rejects (digest invalid).
       - on success ct_memcmp returns 0 iff pk_cand = pk as C bytes, i.e.
         iff [block_ints (shrincs_wots_pubkey_from_sig ...) = block_ints pk];
         the equal case yields [shrincs_wots_verify = true], the differing case false.
     In WOTS+C both the candidate and [pk] are single [n]-byte blocks, so the
     compare is a single 16-byte block compare (no concat / block splitting). *)
  start_function.
  rename H into Hpklen.
  rename H0 into Hsiglen.
  rename H1 into Hctr.
  rename H2 into Hmsglen.
  rename H3 into Hpslen.
  rename H4 into Hsigblk.

  (* pk_cand <- shrincs_wots_pubkey_from_sig(pk_cand, sig, msg, pk_seed, addr) *)
  forward_call (v_pk_cand, sig_ptr, msg_ptr, ps_ptr, a_ptr,
                sig, counter, msg, pk_seed, a,
                Tsh, sh_sig, sh_m, sh_ps, sh_a).
  (* The callee POST now fixes the residual address concretely (no [EX a']):
     it is [shrincs_wots_pk_adrs a] iff the digest at [counter] is valid,
     else [shrincs_wots_grind_adrs a]. *)

  (* Split on the returned status = validity of the digest at [counter]. *)
  destruct (valid_digest (digest_of pk_seed a msg counter)) eqn:Hvd.

  (* ===== digest valid: pk_cand = shrincs_wots_pubkey_from_sig; compare against pk ===== *)
  - (* the (_t'1 != 0) guard is dead here: _t'1 = 0 *)
    forward_if.
    { discriminate. }

    (* Expose both buffers as [map Vint (block_ints ...)] for ct_memcmp. *)
    rewrite (block_to_vals_eq_Vint (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a)).
    rewrite (block_to_vals_eq_Vint pk).
    change pk_bytes with 16.

    (* shrincs_ct_memcmp(pk_cand, pk, SHRINCS_WOTS_PK_BYTES) *)
    forward_call (Tsh, sh_pk, v_pk_cand, pk_ptr, 16,
                  block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a),
                  block_ints pk).
    { (* both buffers are 16 bytes with entries in [0, 256) *)
      repeat split.
      - rewrite Zlength_block_ints.
        change (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a)
          with (T_sf pk_seed (shrincs_wots_pk_adrs a)
                  (concat (complete_ends msg sig counter pk_seed a))).
        rewrite T_sf_Zlength.
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
                        (if shrincs_wots_verify pk sig msg counter pk_seed a then 0 else -1)));
             lvar _pk_cand (tarray tuchar 16) v_pk_cand; temp _pk pk_ptr;
             temp _sig sig_ptr; temp _msg msg_ptr; temp _pk_seed ps_ptr;
             temp _addr a_ptr)
      SEP (data_at Tsh (tarray tuchar 16)
             (map Vint (block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a)))
             v_pk_cand;
           data_at sh_pk (tarray tuchar 16)
             (map Vint (block_ints pk)) pk_ptr;
           data_at sh_sig (tarray tuchar sig_bytes)
             (block_to_vals (to_byte counter 2) ++ blocks_to_vals sig) sig_ptr;
           data_at sh_m (tarray tuchar msg_bytes) (block_to_vals msg) msg_ptr;
           data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
           (* digest valid here (branch [Hvd]): the callee left the pk-typed
              address, which the [if true] in the callee POST reduces to. *)
           data_at sh_a t_addr (adrs_to_vals (shrincs_wots_pk_adrs a)) a_ptr)).

    + (* compare = 0: candidate equals pk, so shrincs_wots_verify accepts *)
      match goal with H : vret = _ |- _ => rename H into Hzero end.
      assert (Hbe : block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a)
                    = block_ints pk)
        by (apply Hmemcmp; rewrite Hzero; reflexivity).
      (* [pk_int_eq_implies_verify] needs [valid_digest = true] (Hvd).
         ct_memcmp only sees the blocks mod 256 ([block_ints]), but that view
         is injective on [byte] blocks (the range is intrinsic now), so the
         mod-256 equality [Hbe] recovers exact block equality, which
         [shrincs_wots_verify] compares. *)
      assert (Hverify : shrincs_wots_verify pk sig msg counter pk_seed a = true)
        by (apply pk_int_eq_implies_verify; [ exact Hvd | exact Hbe ]).
      forward.
      rewrite Hverify.
      entailer!.

    + (* compare <> 0: candidate differs from pk, so shrincs_wots_verify rejects *)
      match goal with H : vret <> _ |- _ => rename H into Hnz end.
      assert (Hneq : block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a)
                     <> block_ints pk).
      { intro Hc.
        apply Hnz.
        apply Hmemcmp in Hc.
        rewrite Hc.
        reflexivity. }
      assert (Hverify : shrincs_wots_verify pk sig msg counter pk_seed a = false)
        by (apply pk_int_neq_implies_verify_false; exact Hneq).
      forward.
      rewrite Hverify.
      entailer!.

    + (* join: return the computed status.  Restore [pk] to its funspec
         [block_to_vals] shape and retire the dead [pk_cand] to [data_at_],
         then [cancel] closes.  The verify POST fixes the residual address
         concretely; with [Hvd : valid_digest ... = true] the [if] reduces
         to [shrincs_wots_pk_adrs a], matching the invariant. *)
      forward.
      change pk_bytes with 16.
      rewrite <- (block_to_vals_eq_Vint pk).
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 16)
        (map Vint (block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a)))
        v_pk_cand).
      entailer!.

  (* ===== digest invalid: _t'1 = -1, pk_cand untouched; reject ===== *)
  - forward_if.
    + (* _t'1 = -1 <> 0: return VERIFY_FAILED.  The untouched buffers match the
         postcondition verbatim, so once the return value is rewritten to the
         model's [false] case the SEP cancels and [entailer!] closes.  The
         verify POST's residual address is [shrincs_wots_grind_adrs a] here
         (the callee's [if false] branch), matching the untouched buffer. *)
      forward.
      assert (Hverify : shrincs_wots_verify pk sig msg counter pk_seed a = false)
        by (unfold shrincs_wots_verify; rewrite Hvd; reflexivity).
      rewrite Hverify.
      entailer!.
    + (* dead: _t'1 = -1 cannot be 0 *)
      discriminate.
Qed.
