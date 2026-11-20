(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.classify

    The complete forgery determines one of the four Merkle cases. The
    tree intermediate removes ordinary tree collisions while preserving
    escape, short-path and exact-anchor cases for subsequent reductions. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params scheme shape model.nodes tree.nodes games tree.forgery tree.encoding
  tree.model.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_full_case (P : shrincs_fxmss_params) (st : shrincs_fxmss_state)
  (kt : shrincs_fxmss_key_table)
    (a : shrincs_fxmss_coord) (md : bytes 32) (sg : shrincs_fxmss_bytes) :
    option (@fcase (bytes 16)) :=
  let pp := st.1.1.1 in
  let z := Z.to_nat (wunsigned a.1) in
  let i := wunsigned a.2 in
  let keys := fun c => odflt [::] (getm kt c) in
  omap (fun node =>
    extract (shrincs_fxmss_tree_node_hash P pp) [::]
      (shrincs_fxmss_value_tree P pp keys st.2.1 st.2.2)
      (shrincs_fxmss_signature_path z i) (shrincs_fxmss_signature_auth z sg) node)
    (shrincs_fxmss_leaf_recover P a false (uint U8 0) pp md
      (slice sg 0 (2 + WOTS_C_CHAINS_SIZE))).

Definition keep_no_tree_collision (P : shrincs_fxmss_params) : shrincs_fxmss_full_keep
  :=
  fun st kt a md sg =>
    match shrincs_fxmss_full_case P st kt a md sg with
    | Some (FColl _ _ _) => false
    | _ => true
    end.

Definition G_tree_free P Q := G_forge_full_signature P Q (keep_no_tree_collision P).

Lemma shrincs_fxmss_full_case_tree_collision P st kt a md sg :
  ~~ keep_no_tree_collision P st kt a md sg ->
  exists q x y, shrincs_fxmss_full_case P st kt a md sg = Some (FColl q x y).
Proof.
rewrite /keep_no_tree_collision.
case he: (shrincs_fxmss_full_case P st kt a md sg) => [fc|] //.
by case: fc he => [q x y|q x a0|q a0|] // he _; exists q, x, y.
Qed.

(** Accepted operational forgeries have the full four-case specification. *)
Lemma shrincs_fxmss_full_case_spec P st kt z i sg md :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  (z < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2
    (uint U8 z, wrepr U64 i) sg md ->
  exists node,
    [/\ shrincs_fxmss_leaf_recover P (uint U8 z, wrepr U64 i) false (uint U8 0)
          st.1.1.1 md (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node,
        shrincs_fxmss_full_case P st kt (uint U8 z, wrepr U64 i) md sg =
          Some (extract (shrincs_fxmss_tree_node_hash P st.1.1.1) [::]
            (shrincs_fxmss_value_tree P st.1.1.1 (fun c => odflt [::] (getm kt c))
              st.2.1 st.2.2)
            (shrincs_fxmss_signature_path z i) (shrincs_fxmss_signature_auth z sg) node)
              &
        extract_ok (shrincs_fxmss_tree_node_hash P st.1.1.1) [::]
          (shrincs_fxmss_value_tree P st.1.1.1 (fun c => odflt [::] (getm kt c))
            st.2.1 st.2.2)
          (shrincs_fxmss_signature_path z i) node
          (extract (shrincs_fxmss_tree_node_hash P st.1.1.1) [::]
            (shrincs_fxmss_value_tree P st.1.1.1 (fun c => odflt [::] (getm kt c))
              st.2.1 st.2.2)
            (shrincs_fxmss_signature_path z i) (shrincs_fxmss_signature_auth z sg)
              node)].
Proof.
move=> hd hz hi hroot hv.
rewrite hroot in hv.
have [node [hleaf hex]] := shrincs_fxmss_verify_merkle_extract hd hz hi hv.
exists node; split=> //.
by rewrite /shrincs_fxmss_full_case hleaf shrincs_fxmss_spec_uint8_nat //
  wunsigned_repr_small.
Qed.
