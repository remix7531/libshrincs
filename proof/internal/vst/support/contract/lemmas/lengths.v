(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.lengths: length lemmas for the tweakable hashes,
    [shrincs_wots_chain_iter] (and its C-refinement wrapper [chain_iter_c])
    and [shrincs_wots_derive_sk].

    Every tweakable hash truncates SHA-256 to [n = 16] bytes. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.public.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Lengths. *)

(** [sha256'] returns a [hash_bytes = 32]-byte block. *)
Lemma SHA256_Zlength : forall m, Zlength (sha256' m) = hash_bytes.
Proof.
  intros. rewrite Zlength_correct, length_sha256'. reflexivity.
Qed.

(** The tweakable hash truncates to [n = 16] bytes. *)
Lemma thash_Zlength : forall pk_seed A M, Zlength (thash pk_seed A M) = n_bytes.
Proof.
  intros. unfold thash, trunc16.
  rewrite Zlength_correct, length_firstn, length_sha256'. reflexivity.
Qed.

Lemma F_Zlength : forall pk_seed A M, Zlength (F pk_seed A M) = n_bytes.
Proof. intros. unfold F. apply thash_Zlength. Qed.

Lemma PRF_Zlength : forall pk_seed sk_seed A, Zlength (PRF pk_seed sk_seed A) = n_bytes.
Proof. intros. unfold PRF. apply thash_Zlength. Qed.

Lemma T_sf_Zlength : forall pk_seed A Ml, Zlength (T_sf pk_seed A Ml) = n_bytes.
Proof. intros. unfold T_sf. apply thash_Zlength. Qed.

Lemma shrincs_wots_derive_sk_Zlength : forall i sk pub a,
  Zlength (shrincs_wots_derive_sk i sk pub a) = n_bytes.
Proof. intros. unfold shrincs_wots_derive_sk. apply PRF_Zlength. Qed.

(** A hash chain preserves the [n]-byte length.  Threaded with the
    dependent [chain_iter]'s step-bound proof [H]. *)
Lemma chain_Zlength : forall X start steps pk_seed a (H : (start + steps <= w_pred)%nat),
  Zlength X = n_bytes ->
  Zlength (shrincs_wots_chain_iter X start steps pk_seed a H) = n_bytes.
Proof.
  intros X start steps pk_seed a H HX.
  destruct steps; simpl; [exact HX | apply F_Zlength].
Qed.

(** Same, for the total C-refinement wrapper [chain_iter_c] (no step-bound
    proof needed -- it is the identity out of range). *)
Lemma chain_iter_c_Zlength : forall X start steps pk_seed a,
  Zlength X = n_bytes ->
  Zlength (chain_iter_c X start steps pk_seed a) = n_bytes.
Proof.
  intros X start steps pk_seed a HX. unfold chain_iter_c.
  destruct (le_dec (start + steps) w_pred) as [H|H].
  - apply chain_Zlength, HX.
  - exact HX.
Qed.
