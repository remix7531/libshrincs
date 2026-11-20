(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.model.experiment_correct

    Honest signatures share the same ROM key and verify for every supplied
    digest in the stateful experiment. *)

From mathcomp Require Import boot algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  model.nodes correct model.wire bridge.keygen.

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

Local Opaque fxmss_node fxmss_node_at.

Lemma shrincs_fxmss_rom_experiment_correct :
  forall seed structure partner sk pk state ctx message md signature,
    shrincs_sf_keygen seed structure partner = Some (sk, pk) ->
    stateful_rom.sf_sign_finish fxmss_sf_scheme (sk, state) (ctx, message) md = Some signature ->
    fxmss_sf_verify_query pk (ctx, message) signature =
      fxmss_sf_sign_query (sk, state) (ctx, message) /\
    stateful_rom.sf_verify_finish fxmss_sf_scheme pk (ctx, message) signature md = true.
Proof.
move=> seed structure partner sk pk state ctx message md signature hk hs.
change (shrincs_sf_sign_with_digest message ctx sk state md = Some signature) in hs.
rewrite /shrincs_sf_sign_with_digest in hs.
case hdom: shrincs_sf_message_domain in hs; last discriminate.
case hsel: shrincs_sf_leaf_select => [[i h]|] in hs; last discriminate.
case hr: (PRF_msg_sf _ _ _ _ _) => [R|] in hs; last discriminate.
case hfs: (fxmss_sign _ _ _ _ _ _ _) => [fsig|] in hs; last discriminate.
have hd := shrincs_fxmss_spec_keygen_selected hk hsel.
have [hon hl] := shrincs_fxmss_spec_select_correct hd hsel.
have hroot := shrincs_fxmss_spec_keygen_root hk.
have [hz hi] := shrincs_fxmss_spec_leaf_bounds hd hon hl.
have hfs' := hfs.
rewrite -[h]uint_to_nat -[i]wrepr_unsigned -[nth (uint U8 0) (slice sk 64 2) 1]uint_to_nat in hfs'.
have hlen := shrincs_fxmss_spec_sign_size hd hon hl hfs'.
have [recovered [hrecover hhonest]] := shrincs_fxmss_spec_tree_correct hd hon hl hfs'.
rewrite uint_to_nat hroot in hhonest.
move: hhonest => [hroot_eq].
rewrite -hroot_eq !uint_to_nat !wrepr_unsigned in hrecover.
have hparse := @shrincs_fxmss_spec_parse_encode (BinInt.Z.to_nat (wunsigned h)) R i fsig
  signature hz hi hlen.
rewrite uint_to_nat in hparse.
have hp := hparse hs.
rewrite (shrincs_fxmss_spec_keygen_pubkey _ _ _ _ _ hk).
have [hpk [hpartner hrt]] := shrincs_fxmss_spec_pubkey_fields sk.
split.
rewrite /fxmss_sf_verify_query /fxmss_sf_sign_query.
rewrite hp hsel hr hpk hpartner hrt.
reflexivity.
change (shrincs_sf_verify_with_digest message signature ctx (shrincs_extract_pubkey sk) md = true).
by rewrite /shrincs_sf_verify_with_digest /shrincs_sf_recover_with_digest hdom hp hpk hrt hrecover eqxx.
Qed.
