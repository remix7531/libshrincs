(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.wots.component: src/wots.c as a Verified Software Unit

    The component exports exactly the three functions declared in include/shrincs.h. Every static helper has a body proof and a contract in its internal context. Its imports are the contracts of calls to the utility, SHA-256 and tweakable-hash translation units. Shrincs.internal.vst.link discharges them. *)

From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.internal.vst.wots Require Import
  body_shrincs_wots_c_t_sf body_shrincs_wots_c_f
  body_shrincs_wots_c_h_grind body_shrincs_wots_c_prf
  body_shrincs_wots_c_chain_iter body_shrincs_wots_c_base_2b
  body_shrincs_wots_c_map_digest body_shrincs_wots_c_grind_to_constant_sum
  body_shrincs_wots_c_pubkey_gen body_shrincs_wots_c_sign
  body_shrincs_wots_c_pubkey_from_sig.
From VST.floyd Require Import VSU.
From Shrincs.clight Require Import wots.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope logic.

Definition wots_QP : QP.program Clight.function := ltac:(QPprog prog).

Definition wots_ASI : funspecs :=
  [ shrincs_wots_c_pubkey_gen_spec;
    shrincs_wots_c_sign_spec;
    shrincs_wots_c_pubkey_from_sig_spec ].

Definition WotsVSU :
  @VSU NullExtension.Espec nil Imports_wots wots_QP wots_ASI emp.
Proof.
mkVSU prog G_wots.
+ solve_SF_internal body_shrincs_wots_c_t_sf.
+ solve_SF_internal body_shrincs_wots_c_f.
+ solve_SF_internal body_shrincs_wots_c_h_grind.
+ solve_SF_internal body_shrincs_wots_c_prf.
+ solve_SF_internal body_shrincs_wots_c_chain_iter.
+ solve_SF_internal body_shrincs_wots_c_base_2b.
+ solve_SF_internal body_shrincs_wots_c_map_digest.
+ solve_SF_internal body_shrincs_wots_c_grind_to_constant_sum.
+ solve_SF_internal body_shrincs_wots_c_pubkey_gen.
+ solve_SF_internal body_shrincs_wots_c_sign.
+ solve_SF_internal body_shrincs_wots_c_pubkey_from_sig.
Qed.

Lemma wots_ASI_idents :
  map fst wots_ASI
  = [_shrincs_wots_c_pubkey_gen; _shrincs_wots_c_sign;
     _shrincs_wots_c_pubkey_from_sig].
Proof. reflexivity. Qed.

Lemma wots_private_idents :
  List.filter (fun i => negb (id_in_list i (map fst wots_ASI)))
              (map fst G_wots)
  = [ _shrincs_wots_c_t_sf; _shrincs_wots_c_f; _shrincs_wots_c_h_grind;
      _shrincs_wots_c_prf; _shrincs_wots_c_chain_iter; _shrincs_wots_c_base_2b;
      _shrincs_wots_c_map_digest; _shrincs_wots_c_grind_to_constant_sum ].
Proof. reflexivity. Qed.

Lemma wots_public_idents :
  List.filter (fun i => id_in_list i (map fst G_wots)) public_idents
  = [_shrincs_wots_c_pubkey_from_sig; _shrincs_wots_c_sign;
     _shrincs_wots_c_pubkey_gen].
Proof. reflexivity. Qed.

Lemma wots_imports_idents :
  map fst Imports_wots
  = [_shrincs_memset; _shrincs_memcpy; _shrincs_sha256;
     _shrincs_adrs_pack; _shrincs_thash].
Proof. reflexivity. Qed.

Lemma wots_context_is_Gprog : Imports_wots ++ G_wots = Gprog_wots.
Proof. reflexivity. Qed.
