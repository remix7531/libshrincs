(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.wots.component: src/wots.c as a Verified Software Unit

    The eleven body proofs of [proof/internal/vst/wots/body_shrincs_wots_*.v],
    assembled into ONE object:

        VSU  Externs=nil  Imports=Imports_wots  wots_QP
             Exports=wots_ASI  InitPred=emp

    THE INTERFACE IS THE FOUR ENTRY POINTS [include/wots.h] declares.
    [wots_ASI] lists [shrincs_wots_pubkey_gen], [shrincs_wots_sign],
    [shrincs_wots_pubkey_from_sig] and [shrincs_wots_verify] and
    nothing else, so the seven step functions -- the chain kernel, the
    grinding loop, the digit map, the two hashes and the public-key
    compression -- are PRIVATE to the unit: proved, carried in the
    component's internal spec list, and invisible to a client. That is
    the VSU-level counterpart of their [static] in the C, and
    [wots_public_idents] below checks the two statements agree by
    [reflexivity] against the AST's own [public_idents].

    SIX IMPORTS, EACH A CROSS-UNIT CALL. Three of [util.c]'s shims
    ([shrincs_memset] and [shrincs_memcpy] inside
    [shrincs_wots_h_grind] and [shrincs_wots_pubkey_from_sig],
    [shrincs_ct_memcmp] inside [shrincs_wots_verify]);
    [shrincs_sha256] DIRECTLY, because [shrincs_wots_h_grind] builds
    its own 112-byte grinding preimage rather than going through the
    tweakable hash; and both of [thash.c]'s functions. Every one of
    them is [Gfun (External _)] in this unit's AST, which is why a VSU
    over it can only import their contracts -- and why
    [Shrincs.internal.vst.link], not this file, is where libshrincs' C stops
    assuming anything.

    THE INIT PREDICATE IS [emp]: [wots.c] has no globals -- the
    parameters are [#define]s and the chain-tip buffers are function
    locals -- so the unit claims no part of the initial memory. *)

From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_t_sf.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_h_grind.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_derive_sk.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_chain_iter.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_chain_from_seed.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_map_digest.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_grind_to_constant_sum.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_pubkey_gen.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_sign.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_pubkey_from_sig.
From Shrincs.internal.vst.wots Require Import body_shrincs_wots_verify.
From VST.floyd Require Import VSU.

(** The bare [prog] IS [wots.c]'s already ([contract.gprog] re-exports
    [Shrincs.clight.wots] through [contract.repr], which is also where
    [CompSpecs] comes from); named here so the source of the AST below
    is visible without following the export chain. *)
From Shrincs.clight Require Import wots.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope logic.

(* ================================================================= *)
(** ** The unit and its interface *)

(** The Clight AST of [src/wots.c] in VSU's "quick program" form; see
    [Shrincs.internal.vst.util.component]'s note on the ambient compspecs. *)
Definition wots_QP : QP.program Clight.function := ltac:(QPprog prog).

(** The interface: exactly the four functions [include/wots.h]
    declares. Everything else [src/wots.c] defines is private. *)
Definition wots_ASI : funspecs :=
  [ shrincs_wots_pubkey_gen_spec;
    shrincs_wots_sign_spec;
    shrincs_wots_pubkey_from_sig_spec;
    shrincs_wots_verify_spec ].

(* ================================================================= *)
(** ** The component *)

Definition WotsVSU :
  @VSU NullExtension.Espec nil Imports_wots wots_QP wots_ASI emp.
Proof.
mkVSU prog G_wots.
+ solve_SF_internal body_shrincs_wots_t_sf.
+ solve_SF_internal body_shrincs_wots_h_grind.
+ solve_SF_internal body_shrincs_wots_derive_sk.
+ solve_SF_internal body_shrincs_wots_chain_iter.
+ solve_SF_internal body_shrincs_wots_chain_from_seed.
+ solve_SF_internal body_shrincs_wots_map_digest.
+ solve_SF_internal body_shrincs_wots_grind_to_constant_sum.
+ solve_SF_internal body_shrincs_wots_pubkey_gen.
+ solve_SF_internal body_shrincs_wots_sign.
+ solve_SF_internal body_shrincs_wots_pubkey_from_sig.
+ solve_SF_internal body_shrincs_wots_verify.
Qed.

(* ================================================================= *)
(** ** Reviewability: what a reader can check by inspection *)

(** (a) The interface is the four entry points. *)
Lemma wots_ASI_idents :
  map fst wots_ASI
  = [_shrincs_wots_pubkey_gen; _shrincs_wots_sign;
     _shrincs_wots_pubkey_from_sig; _shrincs_wots_verify].
Proof. reflexivity. Qed.

(** (b) The seven the interface does NOT name, listed. These are the
    functions a client of the unit cannot call and cannot see a
    contract for. *)
Lemma wots_private_idents :
  List.filter (fun i => negb (id_in_list i (map fst wots_ASI)))
              (map fst G_wots)
  = [ _shrincs_wots_t_sf; _shrincs_wots_h_grind; _shrincs_wots_derive_sk;
      _shrincs_wots_chain_iter; _shrincs_wots_chain_from_seed;
      _shrincs_wots_map_digest; _shrincs_wots_grind_to_constant_sum ].
Proof. reflexivity. Qed.

(** (c) The C agrees. Of the eleven functions [src/wots.c] defines, the
    AST marks exactly four as public -- the other seven are [static].
    So "private" here is not a choice this proof made about what to
    export; it is what the translation unit already says. *)
Lemma wots_public_idents :
  List.filter (fun i => id_in_list i (map fst G_wots)) public_idents
  = [_shrincs_wots_verify; _shrincs_wots_pubkey_from_sig;
     _shrincs_wots_sign; _shrincs_wots_pubkey_gen].
Proof. reflexivity. Qed.

(** (d) What the unit assumes: six contracts, for the six functions
    [src/wots.c] calls and does not define. *)
Lemma wots_imports_idents :
  map fst Imports_wots
  = [_shrincs_memset; _shrincs_memcpy; _shrincs_ct_memcmp;
     _shrincs_sha256; _shrincs_adrs_put32; _shrincs_thash].
Proof. reflexivity. Qed.

(** (e) The unit's proof context is LITERALLY the [Gprog] the eleven
    body proofs were done against. *)
Lemma wots_context_is_Gprog : Imports_wots ++ G_wots = Gprog_wots.
Proof. reflexivity. Qed.
