(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.theory.wots: facts about the WOTS+C model.

    Facts about [model.wots]'s definitions -- search-correctness for
    [find_counter]/[find_from], the [digest_of]/[good_counter]
    equational lemmas, and [sign_inv] -- kept separate from the model
    itself: [model.wots] is "what WOTS+C computes," this file is "why
    the computation has property X." Consumed by both the VST tree
    (model/correct/wots.v, the shrincs_wots_grind_to_constant_sum body
    proof) and the SSProve tree's model bridge. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Export wots.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** [H_grind]'s output shape.

    Unconditional: [trunc16] takes the first [n = 16] of [sha256']'s
    [hash_bytes = 32], well within range regardless of the inputs.
    (Byte-range is no longer a fact to prove here -- [byte] carries
    its own [[0, 256)] bound intrinsically; see [model.byte].) *)

Lemma length_SHA256_out : forall bl, length (Vec.to_list (SHA256 bl)) = 32%nat.
Proof.
  intros. apply Nat2Z.inj.
  rewrite (Vec.length_to_list (SHA256 bl)). unfold hash_bytes. reflexivity.
Qed.

Lemma length_sha256' : forall input, length (sha256' input) = 32%nat.
Proof. intros. unfold sha256'. apply length_SHA256_out. Qed.

(** The model hash agrees with the specification whenever clipping
    preserves its input. *)
Lemma sha256'_eq : forall input,
  Z.of_nat (length input) <= sha256_max_input_len -> sha256' input = sha256_out input.
Proof.
  intros input Hlen. unfold sha256'.
  rewrite to_list_SHA256, BList.to_list_clip by exact Hlen. reflexivity.
Qed.

Lemma H_grind_length : forall pk_seed A M counter,
  length (H_grind pk_seed A M counter) = n.
Proof.
  intros. unfold H_grind, trunc16.
  rewrite length_firstn, length_sha256'. reflexivity.
Qed.

(* ================================================================= *)
(** ** [digest_of] / [good_counter]. *)

(** [digest_of] only reaches the ADRS through [shrincs_wots_grind_adrs], so two
    addresses with the same grind form yield the same digest. *)
Lemma digest_of_grind_eq : forall pk_seed A a m c,
  shrincs_wots_grind_adrs A = shrincs_wots_grind_adrs a ->
  digest_of pk_seed A m c = digest_of pk_seed a m c.
Proof.
  intros pk_seed A a m c Heq.
  unfold digest_of.
  rewrite Heq.
  reflexivity.
Qed.

(** [good_counter] as a statement about the [Z]-valued digit sum, the form
    the C [shrincs_wots_map_digest(...) == 240] test produces. *)
Lemma good_counter_Z_iff : forall pk_seed a m i,
  good_counter pk_seed a m i = true <->
  Z.of_nat (list_sum (digest_of pk_seed a m i)) = 240.
Proof.
  intros pk_seed a m i.
  unfold good_counter, valid_digest.
  rewrite Nat.eqb_eq.
  change constant_sum with 240%nat.
  split; intro H; lia.
Qed.

(* ================================================================= *)
(** ** Search-correctness lemmas (linear-search elimination / introduction),
    consumed by [correct.v] and the VST shrincs_wots_grind_to_constant_sum body proof. *)

Lemma find_from_None_intro : forall fuel pk_seed ADRS M c,
  (forall d, c <= d < c + Z.of_nat fuel -> good_counter pk_seed ADRS M d = false) ->
  find_from pk_seed ADRS M fuel c = None.
Proof.
  induction fuel as [|f IH]; intros pk_seed ADRS M c Hbad; simpl.
  - reflexivity.
  - assert (Hc : good_counter pk_seed ADRS M c = false).
    { apply Hbad. rewrite Nat2Z.inj_succ. lia. }
    rewrite Hc. apply IH. intros d Hd. apply Hbad.
    rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma find_from_Some_good : forall fuel pk_seed ADRS M c c',
  find_from pk_seed ADRS M fuel c = Some c' ->
  good_counter pk_seed ADRS M c' = true.
Proof.
  induction fuel as [|f IH]; intros pk_seed ADRS M c c' H; simpl in H.
  - discriminate.
  - destruct (good_counter pk_seed ADRS M c) eqn:Hc.
    + injection H as <-. exact Hc.
    + eapply IH; eauto.
Qed.

Lemma find_from_Some_range : forall fuel pk_seed ADRS M c c',
  find_from pk_seed ADRS M fuel c = Some c' -> c <= c' < c + Z.of_nat fuel.
Proof.
  induction fuel as [|f IH]; intros pk_seed ADRS M c c' H; simpl in H.
  - discriminate.
  - rewrite Nat2Z.inj_succ.
    destruct (good_counter pk_seed ADRS M c) eqn:Hc.
    + injection H as <-. lia.
    + apply IH in H. lia.
Qed.

Lemma find_from_complete : forall fuel pk_seed ADRS M c i,
  c <= i < c + Z.of_nat fuel ->
  good_counter pk_seed ADRS M i = true ->
  (forall d, c <= d < i -> good_counter pk_seed ADRS M d = false) ->
  find_from pk_seed ADRS M fuel c = Some i.
Proof.
  induction fuel as [|f IH]; intros pk_seed ADRS M c i Hrange Hgood Hbad; simpl.
  - exfalso. rewrite Nat2Z.inj_0 in Hrange. lia.
  - destruct (good_counter pk_seed ADRS M c) eqn:Hc.
    + assert (Hci : c = i).
      { destruct (Z.eq_dec c i) as [e|Hne]; [exact e|].
        assert (good_counter pk_seed ADRS M c = false) by (apply Hbad; lia).
        congruence. }
      subst i. reflexivity.
    + assert (Hne : i <> c) by (intro He; subst i; congruence).
      apply IH.
      * rewrite Nat2Z.inj_succ in Hrange. lia.
      * exact Hgood.
      * intros d Hd. apply Hbad. lia.
Qed.

Lemma find_counter_good : forall pk_seed ADRS M c,
  find_counter pk_seed ADRS M = Some c -> good_counter pk_seed ADRS M c = true.
Proof. unfold find_counter; intros; eapply find_from_Some_good; eauto. Qed.

Lemma find_counter_lt : forall pk_seed ADRS M c,
  find_counter pk_seed ADRS M = Some c -> 0 <= c < c_max.
Proof.
  unfold find_counter; intros pk_seed ADRS M c H.
  apply find_from_Some_range in H.
  rewrite Z2Nat.id in H by (unfold c_max; lia). lia.
Qed.

Lemma find_counter_Some_least : forall pk_seed ADRS M i,
  0 <= i < c_max ->
  good_counter pk_seed ADRS M i = true ->
  (forall d, 0 <= d < i -> good_counter pk_seed ADRS M d = false) ->
  find_counter pk_seed ADRS M = Some i.
Proof.
  unfold find_counter; intros pk_seed ADRS M i Hi Hgood Hbad.
  apply find_from_complete; [| exact Hgood | exact Hbad].
  rewrite Z2Nat.id by (unfold c_max; lia). lia.
Qed.

Lemma find_counter_None : forall pk_seed ADRS M,
  (forall c, 0 <= c < c_max -> good_counter pk_seed ADRS M c = false) ->
  find_counter pk_seed ADRS M = None.
Proof.
  unfold find_counter; intros pk_seed ADRS M Hbad.
  apply find_from_None_intro.
  rewrite Z2Nat.id by (unfold c_max; lia).
  intros d Hd. apply Hbad. lia.
Qed.

(* ================================================================= *)
(** ** [shrincs_wots_sign] inversion. *)

(** Inversion of [shrincs_wots_sign]: a successful signature pins the counter and
    the chain signatures.  Proved with [find_counter] in the GOAL (not a
    hypothesis) so the kernel never WHNF-reduces it -- reducing
    [find_counter] would force [Z.to_nat c_max = Z.to_nat (2^16)] and
    overflow the [Qed] stack. *)
Lemma sign_inv : forall M sk_seed pk_seed ADRS sig counter,
  shrincs_wots_sign M sk_seed pk_seed ADRS = Some (sig, counter) ->
  find_counter pk_seed ADRS M = Some counter
  /\ sig = sign_chains M sk_seed pk_seed ADRS counter.
Proof.
  intros M sk_seed pk_seed ADRS sig counter.
  unfold shrincs_wots_sign.
  destruct (find_counter pk_seed ADRS M) as [c|] eqn:Hfc.
  - intro H. injection H as Hs Hc. subst. split; reflexivity.
  - intro H. discriminate.
Qed.
