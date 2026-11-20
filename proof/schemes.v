(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.schemes: the experiments at the functions of Shrincs.spec

    The byte carriers and their samplers, the tweakable hash [Th] with its target classes, and the concrete WOTS+C scheme with its KOTS game. The experiments themselves are in Shrincs.games, which names no specification function. *)

From Shrincs Require Import games.
From mathcomp Require Import word_ssrZ word.
From mathcomp.experimental_reals Require Import distr.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs Require Import spec.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* The games below instantiate the experiments at the functions and byte strings of Shrincs.spec. *)

Definition bytes (n : nat) : choice_type := chTuple (chWord U8) n.

(* Every seed, hash value and message digest the games sample consists of independent uniform bytes. *)
Definition dByte : dist ('word U8) :=
  {code x ← sample uniform 256 ;; ret (uint U8 x)}.

Fixpoint sample_bytes (n : nat) : raw_code (bytes n) :=
  match n with
  | 0 => ret (nil_tuple _)
  | n'.+1 => b ← dByte ;; bs ← sample_bytes n' ;; ret (cons_tuple b bs)
  end.

Lemma sample_bytes_valid (n : nat) : ValidCode emptym emptym (sample_bytes n).
Proof.
elim: n => [|n IH] /=.
- apply valid_ret.
- apply valid_sampler => a.
  eapply valid_bind; [exact: IH | move=> bs; apply valid_ret].
Qed.

Definition dBytes (n : nat) : dist (bytes n) :=
  {code sample_bytes n #with sample_bytes_valid n}.

(* A tweak carries the six fields that Address.pack serialises: height, index, address type and three words. *)
Definition tweak : choice_type :=
  'word U8 × 'word U64 × 'word U8 × 'word U32 × 'word U32 × 'word U32.

(* The address type fixes each target class before the public seed is sampled. *)
Definition wots_c_hash_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_HASH.

Definition wots_c_pk_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_PK.

Definition wots_c_grind_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_GRIND.

(* Grinding puts the first twelve digest bytes in the tweak payload and the remaining bytes in the message. The anchor and address type stay fixed. *)
Definition grinding_tweak (t : tweak) (digest : Bytes 32) : tweak :=
  let: (height, index, address_type, word1, word2, word3) := t in
  (height, index, address_type,
   int_from_bytes U32 (slice digest 0 4),
   int_from_bytes U32 (slice digest 4 4),
   int_from_bytes U32 (slice digest 8 4)).

Definition grinding_message (digest : Bytes 32) (counter : UInt16) : seq UInt8 :=
  slice digest 12 20 ++ zeros 4 ++ int_to_bytes counter 2.

(* F, PRF and T_sf use this hash at their address fields. Grinding uses the encoded tweak and message. Every result has sixteen bytes. *)
Definition Th (pk_seed : Bytes 16) (t : tweak) (M : seq UInt8) : Bytes 16 :=
  let: (height, index, address_type, word1, word2, word3) := t in
  slice (sha256 (pk_seed ++ zeros 48 ++ pack height index address_type word1 word2 word3 ++ M)) 0 16.

(* The PRF key is the secret seed. Its input contains the public seed and the tweak. *)
Definition shrincs_prf (pk_seed : bytes 16) (t : tweak) (sk_seed : bytes 16) : bytes 16 :=
  Th pk_seed t sk_seed.

Definition wots_c_w : nat := 2 ^ WOTS_C_CHAIN_BITS.
Definition wots_c_chain_count : nat := WOTS_C_CHAIN_COUNT.
Definition wots_c_counter_max : nat := 2 ^ 16.

Lemma dByte_lossless : LosslessCode dByte.
Proof.
  rewrite /dByte.
  apply Lossless_sample.
  - exact: LosslessOp_uniform.
  - move=> x; apply Lossless_ret.
Qed.

Lemma dBytes_lossless n : LosslessCode (dBytes n).
Proof.
  rewrite /dBytes /=.
  elim: n => [|n ih].
  - apply Lossless_ret.
  - rewrite /= /dByte /=.
    apply Lossless_sample.
    + exact: LosslessOp_uniform.
    + move=> x.
      rewrite /LosslessCode (Pr_fst_bind (sample_bytes_valid n)).
      under eq_dlet do rewrite Pr_fst_ret.
      rewrite -pr_predT pr_dlet.
      under eq_exp do rewrite pr_dunit /=.
      by rewrite exp_cst pr_predT ih GRing.mulr1.
Qed.

Lemma dBytes_map_lossless n (A : choice_type)
    (f : bytes n -> A) :
  LosslessCode (x ← dBytes n ;; ret (f x)).
Proof.
  rewrite /LosslessCode (Pr_fst_bind (prog_valid (dBytes n))).
  under eq_dlet do rewrite Pr_fst_ret.
  rewrite -pr_predT pr_dlet.
  under eq_exp do rewrite pr_dunit /=.
  by rewrite exp_cst pr_predT (dBytes_lossless n) GRing.mulr1.
Qed.

(* The chain games sample hidden sixteen-byte inputs and encode them as byte sequences. Compression and grinding choose their target messages. *)
Definition shrincs_thf : thf := {|
  th_PP := bytes 16; th_T := tweak; th_M := 'list ('word U8); th_N := bytes 16;
  th_eval := Th;
  th_dPP := dBytes 16;
  th_dM := {code x ← dBytes 16 ;; ret (tval x)};
  th_dN := dBytes 16 |}.

Definition shrincs_khf_prf : khf := {|
  kh_K := bytes 16; kh_M := bytes 16 × tweak; kh_N := bytes 16;
  kh_eval := fun k pt => shrincs_prf pt.1 pt.2 k;
  kh_dK := dBytes 16; kh_dN := dBytes 16 |}.

Definition wots_c_grind_enc (t : tweak) (m : bytes 32) (c : nat)
    : tweak * seq UInt8 :=
  (grinding_tweak t m, grinding_message m (uint U16 c)).

(* This is the digit-sum test used by grinding and recovery in the specification. *)
Definition wots_c_grind_prp (g : bytes 16) : bool :=
  sumn (base_2b g WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) == WOTS_C_CONSTANT_SUM.

Section AtTheAnchor.

(* The node height and index locate the WOTS+C key. Its anchor and tree shape are fixed within the experiment and universally quantified in the theorem. *)
Context (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8).

(* The three operations are the specification entry points. Both keys carry the public seed, and signing leaves the secret key unchanged. *)
Definition wots_c_scheme : sig_scheme := {|
  Pk := bytes 16 × bytes 16;
  Sk := bytes 16 × bytes 16;
  Msg := bytes 32;
  Sig := bytes (2 + WOTS_C_CHAINS_SIZE);
  SParam := 'unit;
  keygen := fun _ => {code
    pk_seed ← dBytes 16 ;;
    sk_seed ← dBytes 16 ;;
    ret ((pk_seed, sk_seed),
         (pk_seed, wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth))};
  sign := fun sk message_digest => {code
    ret (omap (fun signature => (signature, sk))
           (wots_c_sign message_digest sk.2 sk.1 node_height node_index tree_balanced tree_depth))};
  verify := fun pk message_digest signature =>
    wots_c_pubkey_from_sig signature message_digest pk.1 node_height node_index == Some pk.2
|}.

Definition wots_c_kots_game := KOTS_vc_game wots_c_scheme.

End AtTheAnchor.
