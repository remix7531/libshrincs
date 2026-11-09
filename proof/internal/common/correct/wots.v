(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Model.correct.wots: end-to-end correctness of WOTS+C.

    [wots_correct] -- [shrincs_wots_verify] accepts any signature produced
    by [shrincs_wots_sign] against the matching [shrincs_wots_pubkey_gen].

    This is a property of the Stdlib-only ground-truth model (it consumes
    only [model.wots] and its facts), so it lives in the top-level model
    rather than in either framework's tree. *)

From Stdlib Require Import List ZArith Lia Bool Arith.Peano_dec.
From Shrincs.internal.common Require Import wots theory.wots.
Import ListNotations.
Open Scope Z_scope.

(** The dependent [chain_iter]'s step-bound argument is proof-irrelevant
    ([Peano_dec.le_unique]): the iterate does not depend on WHICH proof
    of [i + s <= w_pred] is supplied. *)
Lemma chain_iter_pirr : forall X i s pk_seed ADRS (H1 H2 : (i + s <= w_pred)%nat),
  shrincs_wots_chain_iter X i s pk_seed ADRS H1
  = shrincs_wots_chain_iter X i s pk_seed ADRS H2.
Proof. intros. f_equal. apply le_unique. Qed.

(** Chain composition (start 0, second segment length [m]): iterating [d]
    steps then [m] more from position [d] is the same as [d + m] steps.
    Threaded with the dependent step bounds -- [chain_iter_pirr] absorbs
    the [<=]-proof mismatch, [fin_val_inj] the position-proof mismatch. *)
Lemma chain_split_gen : forall m X d pk_seed ADRS
    (Hd : (0 + d <= w_pred)%nat) (Hdm : (d + m <= w_pred)%nat)
    (Hsum : (0 + (d + m) <= w_pred)%nat),
  shrincs_wots_chain_iter (shrincs_wots_chain_iter X 0 d pk_seed ADRS Hd) d m pk_seed ADRS Hdm
  = shrincs_wots_chain_iter X 0 (d + m) pk_seed ADRS Hsum.
Proof.
  induction m as [|m IH]; intros X d pk_seed ADRS Hd Hdm Hsum.
  - (* m = 0: the outer iterate is the identity; [d + 0 = d]. *)
    revert Hsum. rewrite Nat.add_0_r. intros Hsum.
    cbn [shrincs_wots_chain_iter]. apply chain_iter_pirr.
  - (* m = S m': peel the last step off both sides ([d + S m' = S (d + m')]). *)
    revert Hsum. rewrite Nat.add_succ_r. intros Hsum.
    cbn [shrincs_wots_chain_iter].
    f_equal.
    + (* the position field: both at [d + m'], proofs differ *)
      f_equal. apply fin_val_inj. reflexivity.
    + apply IH.
Qed.

(** Splitting a length-[k] chain from 0 at any [d <= k]: complete the
    [d]-step prefix by [k - d] more steps and recover the full chain. *)
Lemma chain_split : forall X d k pk_seed ADRS
    (Hd : (0 + d <= w_pred)%nat) (Hcomp : (d + (k - d) <= w_pred)%nat)
    (Hk : (0 + k <= w_pred)%nat),
  (d <= k)%nat ->
  shrincs_wots_chain_iter (shrincs_wots_chain_iter X 0 d pk_seed ADRS Hd) d (k - d) pk_seed ADRS Hcomp
  = shrincs_wots_chain_iter X 0 k pk_seed ADRS Hk.
Proof.
  intros X d k pk_seed ADRS Hd Hcomp Hk Hdk.
  assert (Heq : (d + (k - d) = k)%nat) by lia.
  assert (Hsum : (0 + (d + (k - d)) <= w_pred)%nat) by (rewrite Heq; exact Hk).
  rewrite (chain_split_gen (k - d) X d pk_seed ADRS Hd Hcomp Hsum).
  revert Hsum. rewrite Heq. intros Hsum. apply chain_iter_pirr.
Qed.

(** The verifier's chain completion recovers the honest chain tips from
    an honest signature, for any digit vector bounded by [w_pred].  Kept
    as its own lemma (digest opaque) so the kernel proof term stays
    shallow -- the [T_sf] compression is grafted on in [wots_correct]. *)
Lemma complete_ends_sign_chains_eq : forall M sk_seed pk_seed ADRS c,
  (forall i, (nth i (digest_of pk_seed ADRS M c) 0%nat <= w_pred)%nat) ->
  complete_ends M (sign_chains M sk_seed pk_seed ADRS c) c pk_seed ADRS
  = chain_tips sk_seed pk_seed ADRS.
Proof.
  intros M sk_seed pk_seed ADRS c Hb.
  unfold complete_ends, chain_tips, sign_chains. cbv zeta.
  apply for_idx_dep_ext. intros i Hi.
  rewrite (nth_for_idx_dep len _ default i Hi).
  apply chain_split. apply Hb.
Qed.

(** End-to-end correctness (conditional on grinding success): whenever
    [shrincs_wots_sign] returns a signature and counter, [shrincs_wots_verify] accepts
    it against the matching [shrincs_wots_pubkey_gen].  No [byte_ok M] hypothesis
    is needed -- the digits come from the grinding hash, not from [M]. *)
Theorem wots_correct : forall M sk_seed pk_seed ADRS sig counter,
  shrincs_wots_sign M sk_seed pk_seed ADRS = Some (sig, counter) ->
  shrincs_wots_verify (shrincs_wots_pubkey_gen sk_seed pk_seed ADRS) sig M counter pk_seed ADRS = true.
Proof.
  intros M sk_seed pk_seed ADRS sig counter Hsign.
  (* Invert [shrincs_wots_sign] via [sign_inv] -- which keeps [find_counter] in the goal,
     so the kernel never WHNF-reduces it (that would force [Z.to_nat (2^16)]). *)
  apply sign_inv in Hsign. destruct Hsign as [Hfc Hsig]. subst sig.
  assert (Hgood := find_counter_good _ _ _ _ Hfc). unfold good_counter in Hgood.
  unfold shrincs_wots_verify.
  apply andb_true_intro. split.
  - exact Hgood.
  - (* Second conjunct: [shrincs_wots_pubkey_from_sig] recovers [shrincs_wots_pubkey_gen].  Case on
       [list_eq_dec] symbolically; the equality reduces (through [T_sf]) to the
       chain-completion lemma. *)
    destruct (list_eq_dec _ _ _) as [_|Hne]; [reflexivity|].
    exfalso. apply Hne.
    unfold shrincs_wots_pubkey_from_sig, shrincs_wots_pubkey_gen.
    f_equal. f_equal.
    apply complete_ends_sign_chains_eq.
    intro i. pose proof (nth_digest_of_le_15 pk_seed ADRS M counter i).
    unfold w_pred. lia.
Qed.
