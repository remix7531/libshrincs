(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.instance

    The byte model at the literal specification hashes. The adapters identify
    its leaf and tree operations, including partial failure, with spec.v. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove Require Import hash.
From Shrincs.internal.ssprove.wots Require Import scheme instance.
From Shrincs.internal.ssprove.fxmss Require Import params scheme.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_sha256 : shrincs_fxmss_params := {|
  shrincs_fxmss_hash_eval := Th;
  shrincs_fxmss_prf_msg_eval := fun k pp a m => PRF_msg_sf k pp a.1 a.2 m;
  shrincs_fxmss_public_seed_dist := dBytes 16;
  shrincs_fxmss_secret_dist := dBytes 16;
  shrincs_fxmss_digest_dist := dBytes 32;
  shrincs_fxmss_public_seed_lossless := byte_tuple_lossless 16;
  shrincs_fxmss_secret_lossless := byte_tuple_lossless 16
|}.

Lemma shrincs_fxmss_sha256_hash_eq :
  Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_hash_function shrincs_fxmss_sha256
    = shrincs_thf.
Proof.
rewrite /shrincs_fxmss_hash_function /shrincs_thf.
f_equal; apply: boolp.Prop_irrelevance.
Qed.

Lemma shrincs_fxmss_leaf_params_sha256 a b d :
  shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a b d = wc_sha256 a.1 a.2 b d.
Proof.
rewrite /shrincs_fxmss_leaf_params /shrincs_fxmss_sha256 /wc_sha256.
reflexivity.
Qed.

Lemma shrincs_fxmss_leaf_pubkey_adapter pp k a b d :
  shrincs_fxmss_leaf_pubkey shrincs_fxmss_sha256 a b d pp
    (shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k) =
  wots_c_pubkey_gen k pp a.1 a.2 b d.
Proof.
exact: esym (pubkey_adapter a.1 a.2 b d pp k).
Qed.

Lemma shrincs_fxmss_leaf_sign_adapter pp k a b d m :
  shrincs_fxmss_leaf_sign shrincs_fxmss_sha256 a b d pp
    (shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k) m =
  wots_c_sign m k pp a.1 a.2 b d.
Proof.
exact: esym (sign_adapter a.1 a.2 b d pp k m).
Qed.

Lemma shrincs_fxmss_leaf_recover_adapter pp a b d m sg :
  shrincs_fxmss_leaf_recover shrincs_fxmss_sha256 a b d pp m sg =
  wots_c_pubkey_from_sig sg m pp a.1 a.2.
Proof.
have he root :
    (shrincs_fxmss_leaf_recover shrincs_fxmss_sha256 a b d pp m sg == Some root) =
    (wots_c_pubkey_from_sig sg m pp a.1 a.2 == Some root).
  rewrite shrincs_fxmss_leaf_recover_verify.
  exact: esym (verify_adapter a.1 a.2 b d pp root m sg).
case hleft: (shrincs_fxmss_leaf_recover _ _ _ _ _ _ _) => [x|].
- have hx := he x.
  rewrite hleft eqxx in hx.
  by apply/eqP; rewrite eq_sym -hx.
- case hright: (wots_c_pubkey_from_sig _ _ _ _ _) => [x|] //.
  have hx := he x.
  by rewrite hleft hright eqxx in hx.
Qed.

Lemma shrincs_fxmss_H_adapter pp a l r :
  shrincs_fxmss_hash_node shrincs_fxmss_sha256 pp a l r =
    H pp (FxmssTree a.1 a.2) [tuple of l ++ r].
Proof. by rewrite H_Th. Qed.

Lemma shrincs_fxmss_node_at_adapter fuel k i h pp b d :
  shrincs_fxmss_node_at shrincs_fxmss_sha256 fuel
    (shrincs_fxmss_derived_keys shrincs_fxmss_sha256 pp k b d) i h pp b d =
  fxmss_node_at fuel k i h pp b d.
Proof.
elim: fuel i h => [|fuel ih] i h //=.
rewrite /shrincs_fxmss_derived_keys shrincs_fxmss_leaf_pubkey_adapter.
case: ifP => // _.
case: ifP => // _.
case: ifP => // _.
by rewrite !ih.
Qed.

Lemma shrincs_fxmss_node_adapter k i h pp b d :
  shrincs_fxmss_node shrincs_fxmss_sha256
    (shrincs_fxmss_derived_keys shrincs_fxmss_sha256 pp k b d) i h pp b d =
  fxmss_node k i h pp b d.
Proof. exact: shrincs_fxmss_node_at_adapter. Qed.

Lemma shrincs_fxmss_sign_adapter m k i h pp b d :
  shrincs_fxmss_sign shrincs_fxmss_sha256 m
    (shrincs_fxmss_derived_keys shrincs_fxmss_sha256 pp k b d) i h pp b d =
  fxmss_sign m k i h pp b d.
Proof.
rewrite /shrincs_fxmss_sign /fxmss_sign.
rewrite /shrincs_fxmss_derived_keys shrincs_fxmss_leaf_sign_adapter.
case: ifP => // _.
case: (wots_c_sign _ _ _ _ _ _ _) => [sg|] //.
congr foldl.
apply: functional_extensionality => acc.
apply: functional_extensionality => j.
case: acc => [acc|] //=.
case: ifP => // _.
by rewrite shrincs_fxmss_node_adapter.
Qed.

Lemma shrincs_fxmss_recover_adapter i h sg m pp :
  shrincs_fxmss_recover shrincs_fxmss_sha256 i h sg m pp =
  fxmss_pubkey_from_sig i h sg m pp.
Proof.
rewrite /shrincs_fxmss_recover /fxmss_pubkey_from_sig.
by rewrite shrincs_fxmss_leaf_recover_adapter.
Qed.

Lemma shrincs_fxmss_verify_adapter pp root a sg m :
  shrincs_fxmss_verify shrincs_fxmss_sha256 pp root a sg m =
  (fxmss_pubkey_from_sig a.2 a.1 sg m pp == Some root).
Proof. by rewrite /shrincs_fxmss_verify shrincs_fxmss_recover_adapter. Qed.
