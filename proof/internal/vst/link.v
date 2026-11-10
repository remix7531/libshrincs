(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.link: the four components linked, importing nothing

    The utility and SHA-256 units discharge the tweakable-hash unit's imports. Together they discharge every WOTS+C import. Each importing unit names the same contract as its provider, and all composite environments are empty, so each link uses reflexive contract subsumption. The final interface exports the three WOTS+C contracts of Shrincs.contracts. *)

From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.internal.vst.util Require Import component.
From Shrincs.internal.vst.thash Require Import component.
From Shrincs.internal.vst.wots Require Import component.
From Shrincs.internal.vst.sha256 Require Import vsu.
From VST.floyd Require Import VSU.
From Shrincs.clight Require Import util.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope logic.

Definition UtilSha256VSU := ltac:(linkVSUs UtilVSU Sha256VSU).

Definition HashesVSU := ltac:(linkVSUs UtilSha256VSU ThashVSU).

Definition LinkedVSU := ltac:(linkVSUs HashesVSU WotsVSU).

Definition shrincs_QP : QP.program Clight.function := VSU_prog LinkedVSU.

Definition shrincs_private_idents : list ident :=
  [ _shrincs_memset; _shrincs_memcpy; _shrincs_panic;
    _shrincs_sha256; _shrincs_adrs_pack; _shrincs_thash ].

Definition shrincs_ASI : funspecs :=
  [ shrincs_wots_c_pubkey_gen_spec;
    shrincs_wots_c_sign_spec;
    shrincs_wots_c_pubkey_from_sig_spec ].

Theorem shrincs_c_vsu :
  @VSU NullExtension.Espec nil nil shrincs_QP
       ([ shrincs_wots_c_pubkey_gen_spec;
          shrincs_wots_c_sign_spec;
          shrincs_wots_c_pubkey_from_sig_spec ])
       emp.
Proof.
apply (VSU_ext (privatizeExports LinkedVSU shrincs_private_idents)).
extensionality gv.
rewrite !sepcon_emp.
reflexivity.
Qed.

Lemma shrincs_exports_idents :
  map fst shrincs_ASI
  = [_shrincs_wots_c_pubkey_gen; _shrincs_wots_c_sign;
     _shrincs_wots_c_pubkey_from_sig].
Proof. reflexivity. Qed.

Lemma shrincs_privatize_exact :
  privatize_ids shrincs_private_idents (VSU_Exports LinkedVSU) = shrincs_ASI.
Proof. reflexivity. Qed.

(** The component construction requires a body proof for every internal function, and this count pins the linked function inventory. *)
Lemma shrincs_internal_count :
  Datatypes.length (internalFunctions shrincs_QP) = 28%nat.
Proof. reflexivity. Qed.
