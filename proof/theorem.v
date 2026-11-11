(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

From Shrincs Require Import contracts.
From Shrincs Require Import games.
From Shrincs.internal.vst.support Require Import base.
From Shrincs.internal.vst Require Import link.
From Shrincs.internal.vst.sha256 Require Import correct vsu.
From Shrincs.internal.ssprove Require Import instance security.
From Shrincs.internal.ssprove.wots Require Import
  hop.prf hop.ud hop.grind hop.compress hop.chain_tcr hop.chain_pre.
From VST.floyd Require Import VSU.
From Stdlib Require Import List.
From mathcomp Require Import boot order reals.
From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec.

Module Scheme := Shrincs.games.
Module Hash := Shrincs.contracts.
Module HashProof := Shrincs.internal.vst.sha256.correct.

Import ListNotations.
Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
Close Scope package_scope.
Close Scope sep_scope.

Theorem shrincs_correct_and_secure :
  (forall (message_digest : Bytes 32) (sk_seed pk_seed : Bytes 16)
          (node_height : UInt8) (node_index : UInt64)
          (tree_balanced : bool) (tree_depth : UInt8)
          (signature : Bytes (2 + WOTS_C_CHAINS_SIZE)%N),
     wots_c_sign message_digest sk_seed pk_seed node_height node_index tree_balanced tree_depth
       = Some signature ->
     wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index
       = Some (wots_c_pubkey_gen sk_seed pk_seed node_height node_index
                 tree_balanced tree_depth))
  /\
  (@VSU NullExtension.Espec nil nil shrincs_QP
     ([ contracts.shrincs_wots_c_pubkey_gen_spec;
        contracts.shrincs_wots_c_sign_spec;
        contracts.shrincs_wots_c_pubkey_from_sig_spec ]) emp)
  /\
  (forall (node_height : UInt8) (node_index : UInt64)
          (tree_balanced : bool) (tree_depth : UInt8)
          (A : nom_package),
     ValidPackage (loc A)
       (I_KOTS (Scheme.wots_c_scheme node_height node_index tree_balanced tree_depth))
       A_export A ->
     let P := wc_sha256 node_height node_index tree_balanced tree_depth in
     AdvOf (Scheme.wots_c_kots_game node_height node_index tree_balanced tree_depth) A
     <= AdvOf (PRF_game shrincs_khf_prf wots_c_chain_count)
          (A ∘ R_prf P (bytes 16) shrincs_prf (dBytes 16) true)%sep
      + \sum_(0 <= s < wots_c_w.-2)
          AdvOf (SMUD_game shrincs_thf wots_c_hash_class wots_c_chain_count)
            (A ∘ R_ud P true s)%sep
      + AdvOf (STCRP_game shrincs_thf wots_c_grind_class (bytes 32)
                 wots_c_grind_enc wots_c_grind_prp wots_c_counter_max 1)
          (A ∘ R_grind P)%sep
      + AdvOf (SMTCR_game shrincs_thf wots_c_pk_class 1)
          (A ∘ R_compress P)%sep
      + AdvOf (SMTCR_game shrincs_thf wots_c_hash_class
                 (tcr_budget wots_c_chain_count wots_c_w))
          (A ∘ R_chain_tcr P)%sep
      + AdvOf (SMPRE_game shrincs_thf wots_c_hash_class wots_c_chain_count)
          (A ∘ R_chain_pre P)%sep
      + \sum_(0 <= s < wots_c_w.-2)
          AdvOf (SMUD_game shrincs_thf wots_c_hash_class wots_c_chain_count)
            (A ∘ R_ud P false s)%sep
      + AdvOf (PRF_game shrincs_khf_prf wots_c_chain_count)
          (A ∘ R_prf P (bytes 16) shrincs_prf (dBytes 16) false)%sep).
Proof.
refine (conj _ (conj _ _)).
- intros message_digest sk_seed pk_seed node_height node_index tree_balanced tree_depth signature.
  exact (security.wots_c_verify_sign node_height node_index tree_balanced tree_depth
           message_digest sk_seed pk_seed signature).
- exact shrincs_c_vsu.
- exact security.wots_c_secure_kots.
Qed.

Theorem sha256_c_correct :
  @VSU NullExtension.Espec nil nil sha256_QP (Hash.spec_sha256 :: nil) emp.
Proof. exact HashProof.sha256_c_correct. Qed.
