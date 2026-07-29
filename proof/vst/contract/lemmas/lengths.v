(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.lengths: [Zlength] lemmas for the tweakable hashes,
    the chain ([wc_chain]) and [derive_sk].

    Every tweakable hash truncates SHA-256 to [n = 16] bytes.  The
    content is [Model.theory.shrincs]'s ([length_F] and friends); this
    file only restates it at VST's [Zlength], which is what [data_at]
    and [rep_lia] speak. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Lengths. *)

(** The port's [sha256] returns a [hash_bytes = 32]-byte block. *)
Lemma SHA256_Zlength : forall m, Zlength (shrincs.sha256 m) = hash_bytes.
Proof.
  intros. rewrite Zlength_correct, length_sha256. reflexivity.
Qed.

(** The four tweakable hashes truncate to [n = 16] bytes. *)

Lemma F_Zlength : forall pk_seed A M, Zlength (shrincs.F pk_seed A M) = n_bytes.
Proof. intros. rewrite Zlength_correct, length_F. reflexivity. Qed.

Lemma T_sf_Zlength : forall pk_seed A Ml, Zlength (shrincs.T_sf pk_seed A Ml) = n_bytes.
Proof. intros. rewrite Zlength_correct, length_T_sf. reflexivity. Qed.

Lemma PRF_Zlength : forall pk_seed sk_seed A,
  Zlength (shrincs.PRF pk_seed sk_seed A) = n_bytes.
Proof. intros. rewrite Zlength_correct, length_PRF. reflexivity. Qed.

Lemma H_grind_Zlength_n : forall pk_seed A M c,
  Zlength (shrincs.H_grind pk_seed A M c) = n_bytes.
Proof. intros. rewrite Zlength_correct, length_H_grind. reflexivity. Qed.

Lemma derive_sk_Zlength : forall sk pub nh ni i,
  Zlength (derive_sk sk pub nh ni i) = n_bytes.
Proof. intros. rewrite Zlength_correct, length_derive_sk. reflexivity. Qed.

(** A hash chain preserves the [n]-byte length.  Unconditional in the
    step count: a positive one ends in an [F], and a zero one is its own
    input (so the caller's [Zlength X = n_bytes] carries through).  The
    previous model's chain was a dependent [Fixpoint] and needed its
    step-bound proof threaded here; the port's is a plain [fold_left]
    over the positions the spec visits, so it does not. *)
Lemma wc_chain_Zlength : forall pk_seed nh ni i X start steps,
  Zlength X = n_bytes ->
  Zlength (wc_chain pk_seed nh ni i X start steps) = n_bytes.
Proof.
  intros pk_seed nh ni i X start steps HX.
  destruct (Z_le_gt_dec steps 0) as [Hle|Hgt].
  - (* no steps: [range start (start + steps)] is empty *)
    unfold wc_chain, shrincs.range.
    replace (Z.to_nat (start + steps - start)) with 0%nat by lia.
    cbn [seq map fold_left]. exact HX.
  - rewrite Zlength_correct, length_wc_chain by lia. reflexivity.
Qed.
