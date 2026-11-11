(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.security: correctness and the KOTS bound of Shrincs.spec

    The two SSProve conjuncts of the public theorem, stated over the functions of Shrincs.spec. Both come from the generic model at the record [wc_sha256]: [keyed_scheme_adapter] identifies the scheme built from the three entry points of the specification with the model's keyed scheme, so its KOTS game is the game the reductions are proved against. *)

From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.wots Require Import instance.
From Shrincs.internal.ssprove.wots Require Import scheme kots_link theorem
  hop.grind hop.compress hop.chain_tcr hop.chain_pre hop.ud hop.prf.
From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp Require Import boot order reals word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Module Games := Shrincs.internal.ssprove.wots.scheme.
Module Keyed := Shrincs.internal.ssprove.wots.hop.prf.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* Two schemes over the same carriers are equal when their three operations are. *)
Lemma sig_scheme_ext (PkT SkT MsgT SigT SParamT : choice_type)
    (keygen1 keygen2 : SParamT -> dist (SkT × PkT))
    (sign1 sign2 : SkT -> MsgT -> dist ('option (SigT × SkT)))
    (verify1 verify2 : PkT -> MsgT -> SigT -> bool) :
  keygen1 = keygen2 -> sign1 = sign2 -> verify1 = verify2 ->
  Build_sig_scheme PkT SkT MsgT SigT SParamT keygen1 sign1 verify1
  = Build_sig_scheme PkT SkT MsgT SigT SParamT keygen2 sign2 verify2.
Proof. by move=> -> -> ->. Qed.

Section AtTheAnchor.

Context (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8).

Local Abbreviation P := (wc_sha256 node_height node_index tree_balanced tree_depth).
Local Abbreviation canonical_scheme :=
  (wots_c_scheme node_height node_index tree_balanced tree_depth).
Local Abbreviation model_scheme :=
  (Keyed.shrincs_wots_keyed P (bytes 16) shrincs_prf (dBytes 16)).

(* Function extensionality carries the three pointwise adapters into the record. *)
Lemma keyed_scheme_adapter : canonical_scheme = model_scheme.
Proof.
have Hpubkey : wots_c_pubkey_gen
    = fun k pp nh ni tb td =>
        Keyed.shrincs_wots_pubkey_gen (wc_sha256 nh ni tb td) (bytes 16) shrincs_prf pp k.
  do 6 (apply: functional_extensionality => ?).
  exact: pubkey_adapter.
apply: sig_scheme_ext.
- by rewrite Hpubkey.
- apply: functional_extensionality => sk.
  apply: functional_extensionality => m.
  rewrite sign_adapter.
  by case: (Games.shrincs_wots_sign _ _ _ _).
- apply: functional_extensionality => pk.
  apply: functional_extensionality => m.
  apply: functional_extensionality => sg.
  exact: verify_adapter.
Qed.

(* A signature made by wots_c_sign is accepted: wots_c_pubkey_from_sig recovers the public key of wots_c_pubkey_gen. *)
Lemma wots_c_verify_sign (message_digest : bytes 32) (sk_seed pk_seed : bytes 16)
    (signature : bytes (2 + WOTS_C_CHAINS_SIZE)) :
  wots_c_sign message_digest sk_seed pk_seed node_height node_index tree_balanced tree_depth
    = Some signature ->
  wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index
    = Some (wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth).
Proof.
rewrite sign_adapter pubkey_adapter.
set xs := Keyed.derive_sk P (bytes 16) shrincs_prf pk_seed sk_seed.
have hxs : size xs = wcp_chain_count P by rewrite /xs Keyed.size_derive_sk.
case E: (Games.shrincs_wots_sign P pk_seed xs message_digest) => [sgp|]; last by [].
move=> [<-].
apply/eqP; rewrite (verify_adapter node_height node_index tree_balanced tree_depth).
have hver := Keyed.shrincs_wots_keyed_verify_sign P (bytes 16) shrincs_prf
               pk_seed sk_seed message_digest sgp E.
(* Decoding the encoded signature gives its two parts back: the chain values have the right count and the counter is below 2^16. *)
suff -> : wcp_sig_decode P (wcp_sig_encode P sgp) = sgp by exact: hver.
move: E; rewrite /Games.shrincs_wots_sign.
case Ec: (Games.find_counter P pk_seed message_digest) => [c|]; last by [].
move=> [<-].
have hc : (c < 2 ^ 16)%N := Games.find_counter_lt P pk_seed message_digest c Ec.
have hsz : size (Games.sign_chains P pk_seed xs (Games.digest_of P pk_seed message_digest c))
           = WOTS_C_CHAIN_COUNT.
  by rewrite (Games.size_sign_chains_l P pk_seed xs _ hxs (Games.size_digest_of P _ _ _)).
have -> : wcp_sig_encode P = fun sg => sig_of sg.1 sg.2 by [].
have -> : wcp_sig_decode P = fun sg => (sig_blocks sg, sig_ctr sg) by [].
by cbn [fst snd]; rewrite (sig_blocks_of c hsz) (sig_ctr_of _ hc).
Qed.

Lemma kots_game_perfect (b : bool) :
  perfect (I_KOTS (Games.shrincs_wots_scheme P))
    (Keyed.G_forge_keyed P (bytes 16) shrincs_prf (dBytes 16) b)
    (wots_c_kots_game node_height node_index tree_balanced tree_depth b).
Proof.
rewrite /wots_c_kots_game keyed_scheme_adapter.
exact: G_forge_keyed_KOTS_vc.
Qed.

Theorem wots_c_secure_kots
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS canonical_scheme) A_export A) :
  AdvOf (wots_c_kots_game node_height node_index tree_balanced tree_depth) A
  <= AdvOf (PRF_game shrincs_khf_prf wots_c_chain_count)
       (A ∘ R_prf P (bytes 16) shrincs_prf (dBytes 16) true)
   + \sum_(0 <= s < wots_c_w.-2)
       AdvOf (SMUD_game shrincs_thf wots_c_hash_class wots_c_chain_count)
         (A ∘ R_ud P true s)
   + AdvOf (STCRP_game shrincs_thf wots_c_grind_class (bytes 32)
              wots_c_grind_enc wots_c_grind_prp wots_c_counter_max 1)
       (A ∘ R_grind P)
   + AdvOf (SMTCR_game shrincs_thf wots_c_pk_class 1)
       (A ∘ R_compress P)
   + AdvOf (SMTCR_game shrincs_thf wots_c_hash_class
              (tcr_budget wots_c_chain_count wots_c_w))
       (A ∘ R_chain_tcr P)
   + AdvOf (SMPRE_game shrincs_thf wots_c_hash_class wots_c_chain_count)
       (A ∘ R_chain_pre P)
   + \sum_(0 <= s < wots_c_w.-2)
       AdvOf (SMUD_game shrincs_thf wots_c_hash_class wots_c_chain_count)
         (A ∘ R_ud P false s)
   + AdvOf (PRF_game shrincs_khf_prf wots_c_chain_count)
       (A ∘ R_prf P (bytes 16) shrincs_prf (dBytes 16) false).
Proof.
(* The rewrite is confined to the left side: its pattern is an [Adv] of two
   games, and matching it against the hash-game terms on the right would
   compare unrelated packages by unfolding them. *)
rewrite -[X in X <= _](AdvOf_perfect kots_game_perfect).
exact: (shrincs_wots_secure P (bytes 16) shrincs_prf (dBytes 16) A VA).
Qed.

End AtTheAnchor.
