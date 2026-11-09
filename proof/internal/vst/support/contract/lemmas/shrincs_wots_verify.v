(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.shrincs_wots_verify: the final link from the compiled
    16-byte compare to [shrincs_wots_verify = true/false], used in
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

(** A mismatch of the flattened blocks forces [shrincs_wots_verify] to reject. *)
Lemma pk_int_neq_implies_verify_false :
  forall pk sig msg counter pk_seed a,
  block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a) <> block_ints pk ->
  shrincs_wots_verify pk sig msg counter pk_seed a = false.
Proof.
  intros pk sig msg counter pk_seed a Hneq.
  unfold shrincs_wots_verify.
  destruct (list_eq_dec byte_eq_dec
              (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a) pk) as [He|Hne].
  - exfalso. apply Hneq. rewrite He. reflexivity.
  - rewrite andb_false_r. reflexivity.
Qed.

(** A match of the flattened blocks recovers the candidate equals [pk]. *)
Lemma pk_int_eq_implies_shrincs_wots_pubkey_from_sig :
  forall pk sig msg counter pk_seed a,
  block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a) = block_ints pk ->
  shrincs_wots_pubkey_from_sig msg sig counter pk_seed a = pk.
Proof.
  intros pk sig msg counter pk_seed a Heq.
  unfold block_ints in Heq.
  apply (map_block_ints_inj _ _ Heq).
Qed.

Lemma pk_int_eq_implies_verify :
  forall pk sig msg counter pk_seed a,
  valid_digest (digest_of pk_seed a msg counter) = true ->
  block_ints (shrincs_wots_pubkey_from_sig msg sig counter pk_seed a) = block_ints pk ->
  shrincs_wots_verify pk sig msg counter pk_seed a = true.
Proof.
  intros pk sig msg counter pk_seed a Hvalid Heq.
  unfold shrincs_wots_verify.
  assert (Hpk : shrincs_wots_pubkey_from_sig msg sig counter pk_seed a = pk)
    by (apply pk_int_eq_implies_shrincs_wots_pubkey_from_sig; auto).
  rewrite Hpk, Hvalid.
  destruct (list_eq_dec byte_eq_dec pk pk) as [_|Hne];
    [reflexivity | contradiction].
Qed.
