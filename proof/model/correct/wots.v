(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Model.correct.wots: end-to-end correctness of WOTS+C.

    [wots_c_correct] -- the spec's own verifier accepts the spec's own
    signature against the spec's own public key.

    This is now a statement about [Model.shrincs] DIRECTLY: all three
    algorithms are the port's ([wots_c_pubkey_gen], [wots_c_sign], and
    [wc_verify], which is [Model.theory.shrincs] section 5.8's name for
    the comparison shrincs.py inlines into [fxmss_pubkey_from_sig]), and
    the signature travels between them as the FLAT byte string the spec
    lays out -- a two-byte big-endian counter followed by 32 sixteen-byte
    chain values.  Nothing is re-encoded on the way, so the theorem says
    what a reader wants it to say: sign then verify, at the spec,
    succeeds.

    The one hypothesis is that grinding found a counter.  It is not
    removable and it is not a defect: [wots_c_sign] is total and returns
    the spec's documented zero block when the 2^16-counter search comes
    up empty (model/PORTING.md's assert/raise table, verdict (4)), and
    that block is not a signature.  Grinding failure has negligible
    probability but is not impossible, so the spec -- and this theorem --
    say so out loud.

    Stdlib-only, like the rest of [Model]. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Import byte shrincs theory.shrincs.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** Chain composition.

    The verifier completes a chain the signer left part-way up.  That
    the two halves compose is the whole mathematical content of WOTS
    correctness; everything else in this file is bookkeeping.

    [wc_chain] is a [fold_left] over the positions the spec visits, so
    composition is really [fold_left_app] -- but it is stated here at
    [nat] step counts, because that is what makes the induction
    structural. *)

Lemma wc_chain_add (pk_seed : bytes) (nh ni i : Z) (X : bytes) (start : Z)
      (j k : nat) :
  wc_chain pk_seed nh ni i
    (wc_chain pk_seed nh ni i X start (Z.of_nat j)) (start + Z.of_nat j) (Z.of_nat k)
  = wc_chain pk_seed nh ni i X start (Z.of_nat (j + k)).
Proof.
  induction k as [|k IH].
  - rewrite Nat.add_0_r.
    change (Z.of_nat 0) with 0.
    apply wc_chain_0.
  - rewrite wc_chain_succ, IH.
    replace (j + S k)%nat with (S (j + k)) by lia.
    rewrite wc_chain_succ.
    replace (start + Z.of_nat j + Z.of_nat k) with (start + Z.of_nat (j + k)) by lia.
    reflexivity.
Qed.

(** The same at [Z] step counts, which is the shape section 5's views
    are written in: a digit [d] and its complement [15 - d]. *)
Lemma wc_chain_split (pk_seed : bytes) (nh ni i : Z) (X : bytes) (d s : Z) :
  0 <= d -> 0 <= s ->
  wc_chain pk_seed nh ni i (wc_chain pk_seed nh ni i X 0 d) d s
  = wc_chain pk_seed nh ni i X 0 (d + s).
Proof.
  intros Hd Hs.
  rewrite <- (Z2Nat.id d Hd), <- (Z2Nat.id s Hs), <- Nat2Z.inj_add.
  rewrite <- (Z.add_0_l (Z.of_nat (Z.to_nat d))) at 2.
  apply wc_chain_add.
Qed.

(* ================================================================= *)
(** ** The verifier's completed chains ARE the signer's tips.

    Elementwise: chain [i] of the signature stops at digit [ds[i]], and
    completing it by [15 - ds[i]] more steps lands on exactly the tip
    [chain_tips] builds by running all 15 steps from the start. *)

Lemma complete_ends_sign_chains (M sk_seed pk_seed : bytes) (nh ni counter : Z) :
  complete_ends M (sign_chains M sk_seed pk_seed nh ni counter) counter pk_seed nh ni
  = chain_tips sk_seed pk_seed nh ni.
Proof.
  unfold complete_ends, chain_tips, sign_chains.
  apply map_ext_in.
  intros i Hi.
  pose proof (in_range _ _ _ Hi) as Hir.
  pose proof (index_int_digest_of_range pk_seed nh ni M counter i) as Hd.
  unfold WOTS_C_CHAIN_COUNT in Hir.
  (* the signature block at [i] is the signer's own partial chain *)
  assert (Hblk : index_block
                   (map (fun k => wc_chain pk_seed nh ni k
                                    (derive_sk sk_seed pk_seed nh ni k)
                                    0 (index_int (digest_of pk_seed nh ni M counter) k))
                        (range 0 WOTS_C_CHAIN_COUNT)) i
                 = wc_chain pk_seed nh ni i (derive_sk sk_seed pk_seed nh ni i)
                     0 (index_int (digest_of pk_seed nh ni M counter) i)).
  { unfold index_block.
    rewrite (nth_map_range _ 0 WOTS_C_CHAIN_COUNT (Z.to_nat i) [])
      by (unfold WOTS_C_CHAIN_COUNT; lia).
    rewrite Z.add_0_l, Z2Nat.id by lia.
    reflexivity. }
  rewrite Hblk, wc_chain_split by (unfold WOTS_C_CHAIN_BITS; lia).
  f_equal.
  unfold WOTS_C_CHAIN_BITS in *.
  lia.
Qed.

(* ================================================================= *)
(** ** End-to-end correctness.

    [wc_verify_ends]' three well-formedness hypotheses are discharged
    from the signature the spec itself produced: the counter is below
    2^16 because the search only ranges that far, and the 32 blocks are
    16 bytes each because every chain ends in an [F] (or, at digit 0, in
    the PRF output).  The verifier's slice arithmetic recovers chain [i]
    only when the buffer really is laid out that way, so these are not
    bookkeeping -- they are why the round trip closes. *)

Theorem wots_c_correct (M sk_seed pk_seed : bytes)
        (nh ni ty pa pb pc counter : Z) :
  find_counter pk_seed nh ni M = Some counter ->
  wc_verify (wots_c_pubkey_gen sk_seed pk_seed (mk_adrs nh ni ty pa pb pc))
            (wots_c_sign M sk_seed pk_seed (mk_adrs nh ni ty pa pb pc))
            M pk_seed (mk_adrs nh ni ty pa pb pc)
  = true.
Proof.
  intros Hfc.
  (* the flat signature: a two-byte counter followed by the 32 chains *)
  rewrite wots_c_sign_chains, Hfc.
  set (sg := sign_chains M sk_seed pk_seed nh ni counter).
  assert (Hlen : length sg = Z.to_nat WOTS_C_CHAIN_COUNT)
    by (unfold sg; rewrite length_sign_chains; reflexivity).
  assert (Hblk : forall b, In b sg -> length b = 16%nat)
    by (unfold sg; apply Forall_forall, Forall_length_sign_chains).
  rewrite (wc_verify_ends _ M sg counter pk_seed nh ni ty pa pb pc
             (find_counter_lt _ _ _ _ _ Hfc) Hlen Hblk).
  rewrite (find_counter_good _ _ _ _ _ Hfc).
  cbn [andb].
  (* both sides compress the SAME tips, so the comparison is reflexive *)
  unfold sg.
  rewrite complete_ends_sign_chains, wots_c_pubkey_gen_tips.
  unfold bytes_eqb.
  destruct (list_eq_dec byte_eq_dec _ _) as [_|Hne];
    [reflexivity | contradiction Hne; reflexivity].
Qed.
