(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.shrincs_wots_verify: the final link from the compiled
    16-byte compare to [wc_verify = true/false], used in
    [body_shrincs_wots_verify].

    In WOTS+C the public key and the recovered candidate are single
    [n]-byte blocks, so the verifier compares one block (no concat /
    block splitting). *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.data_at.
From Vst Require Import contract.lemmas.byte_ok.
From Vst Require Import contract.lemmas.chain_blocks.

Open Scope Z_scope.

(** [block_ints] (the flattened [shrincs_ct_memcmp] view) is injective
    ([byte]'s range is intrinsic now, so this needs no hypothesis on
    the inputs). *)
Lemma map_block_ints_inj : forall l1 l2 : list byte,
  map (fun x : byte => Int.repr (x mod 256)) l1
  = map (fun x : byte => Int.repr (x mod 256)) l2 -> l1 = l2.
Proof.
  induction l1 as [|x xs IH]; intros [|y ys] Heq;
    simpl in Heq; try discriminate; [reflexivity|].
  rewrite !byte_mod256_id in Heq.
  assert (Hhd : Int.repr x = Int.repr y)
    by (exact (f_equal (@hd _ Int.zero) Heq)).
  assert (Htl : map (fun x0 : byte => Int.repr (x0 mod 256)) xs =
                map (fun x0 : byte => Int.repr (x0 mod 256)) ys)
    by (exact (f_equal (@tl _) Heq)).
  f_equal.
  - apply (Int_repr_inj_byte x y Hhd).
  - apply (IH ys Htl).
Qed.

(** The verifier's three outcomes, at the compiled 16-byte compare.

    The port's [wc_verify] ([Model.theory.shrincs] section 5.8) is a
    view of [wots_c_pubkey_from_sig]: it recovers a candidate public key
    and compares.  So each lemma below QUANTIFIES the recovered
    candidate [pk'] and takes the recovery step as a hypothesis -- which
    is exactly the shape the body proof has in hand after its call to
    [shrincs_wots_pubkey_from_sig]. *)

(** Recovery failed (the counter's digest is not constant-sum): reject,
    without any comparison at all. *)
Lemma from_sig_None_implies_verify_false :
  forall pk sig M pk_seed ADRS,
  shrincs.wots_c_pubkey_from_sig sig M pk_seed ADRS = None ->
  wc_verify pk sig M pk_seed ADRS = false.
Proof.
  intros pk sig M pk_seed ADRS Hnone.
  unfold wc_verify.
  rewrite Hnone.
  reflexivity.
Qed.

(** A mismatch of the flattened blocks forces [wc_verify] to reject. *)
Lemma pk_int_neq_implies_verify_false :
  forall pk pk' sig M pk_seed ADRS,
  shrincs.wots_c_pubkey_from_sig sig M pk_seed ADRS = Some pk' ->
  block_ints pk' <> block_ints pk ->
  wc_verify pk sig M pk_seed ADRS = false.
Proof.
  intros pk pk' sig M pk_seed ADRS Hsome Hneq.
  unfold wc_verify, shrincs.bytes_eqb.
  rewrite Hsome.
  destruct (list_eq_dec byte_eq_dec pk' pk) as [He|Hne].
  - exfalso. apply Hneq. rewrite He. reflexivity.
  - reflexivity.
Qed.

(** A match of the flattened blocks recovers the candidate equals [pk]. *)
Lemma pk_int_eq_implies_pk : forall (pk pk' : block),
  block_ints pk' = block_ints pk -> pk' = pk.
Proof.
  intros pk pk' Heq.
  unfold block_ints in Heq.
  apply (map_block_ints_inj _ _ Heq).
Qed.

Lemma pk_int_eq_implies_verify :
  forall pk pk' sig M pk_seed ADRS,
  shrincs.wots_c_pubkey_from_sig sig M pk_seed ADRS = Some pk' ->
  block_ints pk' = block_ints pk ->
  wc_verify pk sig M pk_seed ADRS = true.
Proof.
  intros pk pk' sig M pk_seed ADRS Hsome Heq.
  unfold wc_verify, shrincs.bytes_eqb.
  rewrite Hsome, (pk_int_eq_implies_pk pk pk' Heq).
  destruct (list_eq_dec byte_eq_dec pk pk) as [_|Hne];
    [reflexivity | contradiction].
Qed.
