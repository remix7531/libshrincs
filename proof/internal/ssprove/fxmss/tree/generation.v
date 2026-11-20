(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.generation

    Hidden-seed generation of the legal FXMSS trees. Merkle collision witnesses
    point to the exact ordered child messages committed by hidden-seed generation,
    including off-shape forgeries. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle tree_paths.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params scheme shape model.nodes tree.model tree.encoding tree.oracles tree.nodes games
  tree.classify.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs.internal.ssprove Require Import shape.
From mathcomp Require Import word_ssrZ word.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Tree generation *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_leaf_values P pp keys b d p :=
  shrincs_fxmss_leaf_pubkey P (shrincs_fxmss_path_coord p) b (uint U8 d) pp (keys
    (shrincs_fxmss_path_coord p)).

Definition shrincs_fxmss_tree_generate P keys b d :=
  shrincs_fxmss_commit_tree
    (fun p => shrincs_fxmss_eval_leaf P (shrincs_fxmss_path_coord p) (keys
      (shrincs_fxmss_path_coord p)))
    [::] (shrincs_fxmss_tree_shape b d).

Definition shrincs_fxmss_generated_targets P pp keys b d :=
  shrincs_fxmss_commit_plan P pp (shrincs_fxmss_tree_leaf_values P pp keys b d)
    [::] (shrincs_fxmss_tree_shape b d).

Lemma shrincs_fxmss_generated_targets_fresh P pp keys b d :
  shrincs_fxmss_spec_legal_shape b d -> uniq (unzip1 (shrincs_fxmss_generated_targets P
    pp keys b d)).
Proof.
move=> /shrincs_fxmss_legal_shapeP hd.
rewrite /shrincs_fxmss_generated_targets shrincs_fxmss_commit_plan_order
  tree_postorder_root.
by rewrite map_rev rev_uniq; apply: shrincs_fxmss_tree_targets_uniq.
Qed.

Lemma shrincs_fxmss_generated_targets_budget P pp keys b d Q :
  shrincs_fxmss_spec_legal_shape b d ->
  size (shrincs_fxmss_generated_targets P pp keys b d) <= shrincs_fxmss_leaf_capacity Q
    - 1.
Proof.
move=> hd.
have ht := @shrincs_fxmss_tree_targets_budget P keys pp b d Q hd.
rewrite /shrincs_fxmss_generated_targets shrincs_fxmss_commit_plan_size
  shrincs_fxmss_tree_shape_count.
by move: ht; rewrite /shrincs_fxmss_tree_targets size_map size_internal_paths
  shrincs_fxmss_tree_shape_count.
Qed.

Lemma shrincs_fxmss_tree_generate_valid P (L : Locations) keys b d :
  ValidCode L (smtcr.I_SMTCR (shrincs_fxmss_hash_function P))
    (shrincs_fxmss_tree_generate P keys b d).
Proof.
rewrite /shrincs_fxmss_tree_generate.
by apply: (shrincs_fxmss_commit_tree_valid P L) => p.
Qed.
#[export] Existing Instance shrincs_fxmss_tree_generate_valid.

Lemma shrincs_fxmss_tree_generate_known P Q bit pp keys b d h
    (T : choiceType) (K : bytes 16 -> raw_code T) :
  shrincs_fxmss_spec_legal_shape b d ->
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h smtcr.tcr_rev_loc = false ->
  get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  Pr_code (bind
    (code_link (shrincs_fxmss_tree_generate P keys b d)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit)) K) h =
  Pr_code (K (val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d)))
    (shrincs_fxmss_commit_heap P h (shrincs_fxmss_generated_targets P pp keys b d)).
Proof.
move=> hd hp hr ht.
apply: (shrincs_fxmss_commit_tree_known P (shrincs_fxmss_leaf_capacity Q - 1) bit pp _
  (shrincs_fxmss_tree_leaf_values P pp keys b d) T) => //.
- move=> p h' K' hp'.
  exact: shrincs_fxmss_eval_leaf_known.
- rewrite ht /=.
  exact: shrincs_fxmss_generated_targets_fresh.
- rewrite ht add0n.
  exact: shrincs_fxmss_generated_targets_budget.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree plan *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_commit_value_shape P pp keys b d p rem :
  shrincs_fxmss_spec_legal_shape b d -> size p + rem = d ->
  (b = false -> idx_of_path p = 0) ->
  odflt (zeros 16)
    (shrincs_fxmss_node P keys (shrincs_fxmss_path_coord p).2 (shrincs_fxmss_path_coord
      p).1
      pp b (uint U8 d)) =
  shrincs_fxmss_commit_value P pp (shrincs_fxmss_tree_leaf_values P pp keys b d) p
    (shrincs_fxmss_tree_shape b rem).
Proof.
move=> hd hdepth hi.
have hd255 : (d <= 255)%coq_nat.
  by case: b hd hi => hd hi; simpl in hd; lia.
have hp : (size p <= 255)%coq_nat.
  move: hdepth; rewrite addnE; lia.
have hz : (255 - size p < 256)%coq_nat.
  rewrite subnE; lia.
have hfuel : rem < (255-size p).+1.
  apply/ltP.
  move: hdepth; rewrite addnE subnE; lia.
rewrite /shrincs_fxmss_node /shrincs_fxmss_path_coord shrincs_fxmss_spec_uint8_nat //.
by rewrite (@shrincs_fxmss_node_materialized P keys pp b d rem p
  (255-size p).+1 hd hdepth hi hfuel).
Qed.

Lemma shrincs_fxmss_commit_value_leaf P pp keys b d p :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_path_valid p ->
  ((size p == d) || (~~ b && (idx_of_path p == 1)))%bool ->
  odflt (zeros 16)
    (shrincs_fxmss_node P keys (shrincs_fxmss_path_coord p).2 (shrincs_fxmss_path_coord
      p).1
      pp b (uint U8 d)) = shrincs_fxmss_tree_leaf_values P pp keys b d p.
Proof.
move=> hd hp hl.
have hz : (255-size p < 256)%coq_nat by rewrite subnE; lia.
rewrite /shrincs_fxmss_node /shrincs_fxmss_path_coord shrincs_fxmss_spec_uint8_nat //.
by rewrite (@shrincs_fxmss_node_path_leaf P keys pp b d p (255-size p) hd hp hl).
Qed.

Lemma shrincs_fxmss_commit_pair_coords P pp keys b d p :
  shrincs_fxmss_spec_legal_shape b d -> size p < d ->
  (b = false -> idx_of_path p = 0) ->
  shrincs_fxmss_tree_target_pair P keys pp b d (shrincs_fxmss_path_coord p) =
  (odflt (zeros 16)
     (shrincs_fxmss_node P keys (shrincs_fxmss_path_coord (rcons p false)).2
       (shrincs_fxmss_path_coord (rcons p false)).1 pp b (uint U8 d)),
   odflt (zeros 16)
     (shrincs_fxmss_node P keys (shrincs_fxmss_path_coord (rcons p true)).2
       (shrincs_fxmss_path_coord (rcons p true)).1 pp b (uint U8 d))).
Proof.
move=> hd hp hi.
have hidx := shrincs_fxmss_path_index_bound hd (ltnW hp) hi.
rewrite !shrincs_fxmss_path_child_coord /shrincs_fxmss_tree_target_pair
  /shrincs_fxmss_honest_node.
rewrite (@shrincs_fxmss_path_index_word p hidx).
have hz : (255-size p < 256)%coq_nat by rewrite subnE; lia.
rewrite /shrincs_fxmss_path_coord shrincs_fxmss_spec_uint8_nat // subn1.
by rewrite Z.add_0_r.
Qed.

Lemma shrincs_fxmss_commit_pair_shape P pp keys b d p rem :
  shrincs_fxmss_spec_legal_shape b d -> size p + rem.+1 = d ->
  (b = false -> idx_of_path p = 0) ->
  shrincs_fxmss_tree_target_pair P keys pp b d (shrincs_fxmss_path_coord p) =
  (shrincs_fxmss_commit_value P pp (shrincs_fxmss_tree_leaf_values P pp keys b d)
     (rcons p false) (shrincs_fxmss_tree_shape b rem),
   shrincs_fxmss_commit_value P pp (shrincs_fxmss_tree_leaf_values P pp keys b d)
     (rcons p true) (if b then shrincs_fxmss_tree_shape b rem else BLeaf tt)).
Proof.
move=> hd hdepth hi.
have hp : size p < d by rewrite -hdepth addnS ltnS leq_addr.
have hdepth' (c : bool) : size (rcons p c) + rem = d.
  by rewrite size_rcons addSn -addnS.
have hleft : b = false -> idx_of_path (rcons p false) = 0.
  by move=> hb; rewrite shrincs_fxmss_path_index_rcons (hi hb).
rewrite (shrincs_fxmss_commit_pair_coords P pp keys b d p hd hp hi).
rewrite (shrincs_fxmss_commit_value_shape P pp keys b d (rcons p false) rem
  hd (hdepth' false) hleft).
case hb: b in hd hi hdepth' hp *.
- have hright : true = false -> idx_of_path (rcons p true) = 0 by [].
  by rewrite (shrincs_fxmss_commit_value_shape P pp keys true d (rcons p true) rem
    hd (hdepth' true) hright).
- have hright : idx_of_path (rcons p true) = 1.
    by rewrite shrincs_fxmss_path_index_rcons (hi erefl).
  have hvalid : shrincs_fxmss_path_valid (rcons p true).
    apply/andP; split.
    + rewrite size_rcons.
      apply: leq_trans hp _.
      by apply/leP; exact: hd.2.
    + rewrite hright.
      change (expn 2 0 < expn 2 64).
      by rewrite ltn_exp2l.
  rewrite (shrincs_fxmss_commit_value_leaf P pp keys false d (rcons p true) hd hvalid).
  + by rewrite hright eqxx /= orbT.
  + by [].
Qed.

Lemma shrincs_fxmss_commit_plan_shape P pp keys b d rem p :
  shrincs_fxmss_spec_legal_shape b d -> size p + rem = d ->
  (b = false -> idx_of_path p = 0) ->
  shrincs_fxmss_commit_plan P pp (shrincs_fxmss_tree_leaf_values P pp keys b d) p
    (shrincs_fxmss_tree_shape b rem) =
  [seq (shrincs_fxmss_tree_path_tweak q,
        shrincs_fxmss_tree_message (shrincs_fxmss_tree_target_pair P keys pp b d
          (shrincs_fxmss_path_coord q)))
    | q <- tree_postorder p (shrincs_fxmss_tree_shape b rem)].
Proof.
move=> hd.
elim: rem p => [|rem ih] p hdepth hi; first by [].
have hdepth' (c : bool) : size (rcons p c) + rem = d.
  by rewrite size_rcons addSn -addnS.
have hleft : b = false -> idx_of_path (rcons p false) = 0.
  by move=> hb; rewrite shrincs_fxmss_path_index_rcons (hi hb).
rewrite /shrincs_fxmss_tree_shape -/shrincs_fxmss_tree_shape [in
  LHS]/shrincs_fxmss_commit_plan -/shrincs_fxmss_commit_plan.
rewrite tree_postorder_node !map_cat.
rewrite -(shrincs_fxmss_commit_pair_shape P pp keys b d p rem hd hdepth hi).
rewrite (ih (rcons p false) (hdepth' false) hleft).
case hb: b in hd ih hi hdepth' hleft *; last by [].
have hright : true = false -> idx_of_path (rcons p true) = 0 by [].
by rewrite (ih (rcons p true) (hdepth' true) hright).
Qed.

Lemma shrincs_fxmss_generated_targets_eq P pp keys b d :
  shrincs_fxmss_spec_legal_shape b d ->
  shrincs_fxmss_generated_targets P pp keys b d = shrincs_fxmss_tree_committed P keys pp
    b d.
Proof.
move=> hd.
rewrite /shrincs_fxmss_generated_targets
  (shrincs_fxmss_commit_plan_shape P pp keys b d d [::] hd erefl (fun _ => erefl))
  tree_postorder_root /shrincs_fxmss_tree_committed /shrincs_fxmss_tree_targets.
by rewrite map_rev.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree witness *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_commit_plan_subtree P pp values pos t q l r :
  subtree_at (bt_posmap (fun p _ => values p) pos t) q = Some (BNode l r) ->
  (shrincs_fxmss_tree_path_tweak (pos ++ q),
   shrincs_fxmss_tree_message
     (val_bt (shrincs_fxmss_tree_node_hash P pp) (rcons (pos ++ q) false) l,
      val_bt (shrincs_fxmss_tree_node_hash P pp) (rcons (pos ++ q) true) r)) \in
    shrincs_fxmss_commit_plan P pp values pos t.
Proof.
elim: q pos t l r => [|c q ih] pos [u|tl tr] l r //=.
- case=> <- <-.
  by rewrite cats0 !mem_cat inE eqxx !orbT.
- case: c => /= hs.
  + have hm := ih (rcons pos true) tr l r hs.
    by rewrite -cat_rcons mem_cat hm.
  + have hm := ih (rcons pos false) tl l r hs.
    by rewrite -cat_rcons !mem_cat hm orbT.
Qed.

Lemma shrincs_fxmss_full_case_collision P st kt z i sg md q x y :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  (z < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2
    (uint U8 z, wrepr U64 i) sg md ->
  shrincs_fxmss_full_case P st kt (uint U8 z, wrepr U64 i) md sg = Some (FColl q x y) ->
  [/\ (shrincs_fxmss_tree_path_tweak q, shrincs_fxmss_tree_message y) \in
        shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
          st.1.1.1 st.2.1 st.2.2,
      shrincs_fxmss_tree_message x != shrincs_fxmss_tree_message y &
      th_eval (shrincs_fxmss_hash_function P) st.1.1.1 (shrincs_fxmss_tree_path_tweak q)
        (shrincs_fxmss_tree_message x) =
        th_eval (shrincs_fxmss_hash_function P) st.1.1.1 (shrincs_fxmss_tree_path_tweak
          q) (shrincs_fxmss_tree_message y)].
Proof.
move=> hd hz hi hroot hv hc.
have [node [hleaf hclass hex]] := shrincs_fxmss_full_case_spec P st kt z i sg md
  hd hz hi hroot hv.
rewrite hc in hclass.
case: hclass => he.
rewrite -he /extract_ok in hex.
case: hex => qrel [l [r [hq hs hy heq hne]]].
rewrite cat0s in hq.
subst qrel.
have hm := shrincs_fxmss_commit_plan_subtree P st.1.1.1
  (shrincs_fxmss_tree_leaf_values P st.1.1.1 (fun c => odflt [::] (getm kt c)) st.2.1
    st.2.2)
  [::] (Shrincs.internal.ssprove.fxmss.tree.encoding.shrincs_fxmss_tree_shape st.2.1
    st.2.2) q l r hs.
rewrite cat0s -hy -/(shrincs_fxmss_generated_targets _ _ _ _ _)
  (shrincs_fxmss_generated_targets_eq _ _ _ _ _ hd) in hm.
split=> //.
apply/eqP=> heq'.
exact: hne (shrincs_fxmss_tree_message_inj x y heq').
Qed.

Lemma shrincs_fxmss_full_case_collision_words P st kt a sg md q x y :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  shrincs_fxmss_full_case P st kt a md sg = Some (FColl q x y) ->
  [/\ (shrincs_fxmss_tree_path_tweak q, shrincs_fxmss_tree_message y) \in
        shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
          st.1.1.1 st.2.1 st.2.2,
      shrincs_fxmss_tree_message x != shrincs_fxmss_tree_message y &
      th_eval (shrincs_fxmss_hash_function P) st.1.1.1 (shrincs_fxmss_tree_path_tweak q)
        (shrincs_fxmss_tree_message x) =
        th_eval (shrincs_fxmss_hash_function P) st.1.1.1 (shrincs_fxmss_tree_path_tweak
          q) (shrincs_fxmss_tree_message y)].
Proof.
case: a => z i.
move=> hd hroot hv hc.
have hz : (Z.to_nat (wunsigned z) < 256)%coq_nat.
  have [hz0 hz1] := wunsigned_range z.
  change (wunsigned z < 256)%Z in hz1.
  lia.
have hi : (0 <= wunsigned i < 2^64)%Z := wunsigned_range i.
have hw := shrincs_fxmss_full_case_collision P st kt (Z.to_nat (wunsigned z))
  (wunsigned i) sg md q x y hd hz hi hroot.
rewrite uint_to_nat wrepr_unsigned in hw.
exact: hw hv hc.
Qed.
