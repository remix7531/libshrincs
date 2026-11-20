(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.model

    Every internal coordinate on either legal operational shape occurs in the
    static tree-target list. Honest target messages are the ordered values of the
    two children at each internal coordinate. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.math Require Import
  bin_tree tree_paths merkle tree_lookup fold_collision merkle_fold tree_auth_paths.
From Shrincs Require Import spec schemes games.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape model.nodes tree.encoding scheme tree.nodes model.auth.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Bool Lia.

(* ------------------------------------------------------------------ *)
(** ** Tree coverage *)

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_legal_shapeP b d :
  shrincs_fxmss_structure_legal b d <-> shrincs_fxmss_spec_legal_shape b d.
Proof.
rewrite /shrincs_fxmss_structure_legal /shrincs_fxmss_spec_legal_shape.
case: b; split.
- by move/andP=> [/ltP hp /leP hd]; split; lia.
- by move=> [hp hd]; apply/andP; split; [apply/ltP | apply/leP]; lia.
- by move/andP=> [/ltP hp /leP hd]; split; lia.
- by move=> [hp hd]; apply/andP; split; [apply/ltP | apply/leP]; lia.
Qed.

Lemma shrincs_fxmss_tree_balanced_internal d p :
  size p < d -> p \in internal_paths (shrincs_fxmss_tree_shape true d).
Proof.
elim: d p => [|d ih] [|b p] //= hp.
rewrite inE mem_cat.
apply/orP; right.
case: b.
- apply/orP; right.
  by apply/mapP; exists p; first exact: ih.
- apply/orP; left.
  by apply/mapP; exists p; first exact: ih.
Qed.

Lemma shrincs_fxmss_tree_spine_internal d k :
  k < d -> nseq k false \in internal_paths (shrincs_fxmss_tree_shape false d).
Proof.
elim: d k => [|d ih] [|k] //= hk.
rewrite cats0 inE.
apply/orP; right.
by apply/mapP; exists (nseq k false); first exact: ih.
Qed.

Lemma shrincs_fxmss_path_coord_of_idx z i :
  (z <= 255)%coq_nat -> (0 <= i < 2 ^ Z.of_nat (255-z))%Z ->
  shrincs_fxmss_path_coord (path_of_idx (255-z) (Z.to_nat i)) =
    (uint U8 z, wrepr U64 i).
Proof.
move=> hz hi.
have hir : Z.to_nat i < expn 2 (255-z).
  apply/ltP/Znat.Nat2Z.inj_lt.
  rewrite Znat.Z2Nat.id; first exact: hi.1.
  by rewrite shape.Z_of_nat_expn2; exact: hi.2.
rewrite /shrincs_fxmss_path_coord size_path_of_idx idx_of_path_of_idx //.
have hheight : 255-(255-z) = z by rewrite !subnE; lia.
rewrite hheight /uint Znat.Z2Nat.id; first exact: hi.1.
by [].
Qed.

Lemma shrincs_fxmss_tree_internal_cover b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i = false ->
  exists p,
    p \in internal_paths (shrincs_fxmss_tree_shape b d) /\
    shrincs_fxmss_tree_path_tweak p = shrincs_fxmss_tree_tweak (uint U8 z, wrepr U64 i).
Proof.
move=> hd hs hl.
have [[hz hdepth] [hi hbound]] := hs.
have hlt : 255-z < d.
  have hne : 255-z <> d.
    move=> he.
    by move: hl; rewrite /shrincs_fxmss_spec_is_leaf he eqxx.
  apply/ltP.
  rewrite subnE in hne *.
  lia.
clear hs.
case: b hd hbound hl => hd hbound hl.
- exists (path_of_idx (255-z) (Z.to_nat i)).
  split.
  + apply: shrincs_fxmss_tree_balanced_internal.
    by rewrite size_path_of_idx.
  + (* The balanced path has the requested tree tweak. *)
    have hrange : (0 <= i < 2 ^ Z.of_nat (255-z))%Z.
      split; first exact: hi.
      by rewrite subnE.
    by rewrite /shrincs_fxmss_tree_path_tweak (shrincs_fxmss_path_coord_of_idx hz
      hrange).
- (* An unbalanced internal node lies on the left spine. *)
  have hi0 : i = 0%Z.
    case: hbound => [//|[he _]].
    by move: hl; rewrite /shrincs_fxmss_spec_is_leaf he /= orbT.
  exists (nseq (255-z) false).
  split; first exact: shrincs_fxmss_tree_spine_internal.
  rewrite /shrincs_fxmss_tree_path_tweak /shrincs_fxmss_path_coord size_nseq
    idx_of_path_false hi0.
  have hheight : 255-(255-z) = z by rewrite !subnE; lia.
  by rewrite hheight.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree model *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_path_index_rcons p c :
  idx_of_path (rcons p c) = c + (idx_of_path p).*2.
Proof. by rewrite /idx_of_path rev_rcons. Qed.

Lemma shrincs_fxmss_path_index_word p :
  idx_of_path p < expn 2 64 ->
  wunsigned (shrincs_fxmss_path_coord p).2 = Z.of_nat (idx_of_path p).
Proof.
move/ltP/Znat.Nat2Z.inj_lt=> hp.
rewrite shape.Z_of_nat_expn2 in hp.
change (wunsigned (wrepr U64 (Z.of_nat (idx_of_path p))) =
  Z.of_nat (idx_of_path p)).
apply: wunsigned_repr_small.
by split; [exact: Znat.Nat2Z.is_nonneg | exact: hp].
Qed.

Lemma shrincs_fxmss_path_index_child p c :
  Z.of_nat (idx_of_path (rcons p c)) =
    (2 * Z.of_nat (idx_of_path p) + Z.of_nat c)%Z.
Proof.
rewrite shrincs_fxmss_path_index_rcons -mul2n Znat.Nat2Z.inj_add Znat.Nat2Z.inj_mul.
lia.
Qed.

Lemma shrincs_fxmss_path_index_bound b d p :
  shrincs_fxmss_spec_legal_shape b d -> size p <= d ->
  (b = false -> idx_of_path p = 0) -> idx_of_path p < expn 2 64.
Proof.
move=> hd hp hi.
case: b hd hi => hd hi.
- apply: (leq_trans (idx_of_path_lt p)).
  rewrite leq_exp2l //.
  apply: leq_trans hp _.
  by apply/leP; exact: hd.2.
- by rewrite (hi erefl) expn_gt0.
Qed.

Lemma shrincs_fxmss_path_children_bound b d p :
  shrincs_fxmss_spec_legal_shape b d -> size p < d ->
  (b = false -> idx_of_path p = 0) ->
  (2 * Z.of_nat (idx_of_path p) + 1 < 2^64)%Z.
Proof.
move=> hd hp hi.
case: b hd hi => hd hi.
- (* A balanced child index fits in 64 bits. *)
  have hsz : (size p).+1 <= 64.
    apply: leq_trans hp _.
    by apply/leP; exact: hd.2.
  have hr : idx_of_path (rcons p true) < expn 2 64.
    apply: (leq_trans (idx_of_path_lt _)).
    by rewrite leq_exp2l // size_rcons.
  move/ltP/Znat.Nat2Z.inj_lt: hr.
  by rewrite shrincs_fxmss_path_index_child shape.Z_of_nat_expn2.
- rewrite (hi erefl).
  lia.
Qed.

Definition shrincs_fxmss_subtree_value P pk keys b d p rem : bytes 16 :=
  val_bt (shrincs_fxmss_tree_node_hash P pk) p
    (bt_posmap (fun q _ => shrincs_fxmss_leaf_pubkey P (shrincs_fxmss_path_coord q) b
      (uint U8 d)
      pk (keys (shrincs_fxmss_path_coord q))) p (shrincs_fxmss_tree_shape b rem)).

Lemma shrincs_fxmss_node_path_leaf P keys pk b d p fuel :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_path_valid p ->
  ((size p == d) || (~~ b && (idx_of_path p == 1)))%bool ->
  shrincs_fxmss_node_at P fuel.+1 keys (shrincs_fxmss_path_coord p).2
    (shrincs_fxmss_path_coord p).1 pk b (uint U8 d) =
    Some (shrincs_fxmss_leaf_pubkey P (shrincs_fxmss_path_coord p) b (uint U8 d)
      pk (keys (shrincs_fxmss_path_coord p))).
Proof.
move=> hd /andP[hp hi] hl.
have hz : (255-size p < 256)%coq_nat by rewrite subnE; lia.
have hdf := shrincs_fxmss_spec_depth_bound hd.
have hir : (0 <= Z.of_nat (idx_of_path p) < 2^64)%Z.
  split; first exact: Znat.Nat2Z.is_nonneg.
  move/ltP/Znat.Nat2Z.inj_lt: hi.
  by rewrite shape.Z_of_nat_expn2.
rewrite /shrincs_fxmss_path_coord shrincs_fxmss_node_at_step //.
have hdepth : 255-(255-size p) = size p.
  move/leP: hp=> hp.
  rewrite !subnE; lia.
rewrite /shrincs_fxmss_spec_is_leaf hdepth.
have he : Z.eqb (Z.of_nat (idx_of_path p)) 1 = (idx_of_path p == 1).
  apply/idP/idP.
  - move/Z.eqb_eq=> he; apply/eqP; lia.
  - move/eqP=> ->; by [].
by rewrite he hl.
Qed.

Lemma shrincs_fxmss_path_child_coord p c :
  shrincs_fxmss_path_coord (rcons p c) =
    (uint U8 ((255-size p)-1),
     wrepr U64 (2 * Z.of_nat (idx_of_path p) + Z.of_nat c)).
Proof.
rewrite /shrincs_fxmss_path_coord size_rcons.
have hh : 255-(size p).+1 = (255-size p)-1 by rewrite !subnE; lia.
by rewrite hh /uint shrincs_fxmss_path_index_child.
Qed.

Lemma shrincs_fxmss_node_path_internal P keys pk b d p fuel :
  shrincs_fxmss_spec_legal_shape b d -> size p < d ->
  (b = false -> idx_of_path p = 0) ->
  shrincs_fxmss_node_at P fuel.+1 keys (shrincs_fxmss_path_coord p).2
    (shrincs_fxmss_path_coord p).1 pk b (uint U8 d) =
  if shrincs_fxmss_node_at P fuel keys (shrincs_fxmss_path_coord (rcons p false)).2
      (shrincs_fxmss_path_coord (rcons p false)).1 pk b (uint U8 d) is Some l then
    if shrincs_fxmss_node_at P fuel keys (shrincs_fxmss_path_coord (rcons p true)).2
        (shrincs_fxmss_path_coord (rcons p true)).1 pk b (uint U8 d) is Some r then
      Some (shrincs_fxmss_hash_node P pk (shrincs_fxmss_path_coord p) l r)
    else None
  else None.
Proof.
move=> hd hp hi.
have hd255 : (d <= 255)%coq_nat by case: b hd hi => hd hi; simpl in hd; lia.
have hp255 : (size p < 255)%coq_nat by move/ltP: hp; lia.
have hz : (255-size p < 256)%coq_nat by rewrite subnE; lia.
have hdf := shrincs_fxmss_spec_depth_bound hd.
have hidx := shrincs_fxmss_path_index_bound hd (ltnW hp) hi.
have hir : (0 <= Z.of_nat (idx_of_path p) < 2^64)%Z.
  split; first exact: Znat.Nat2Z.is_nonneg.
  move/ltP/Znat.Nat2Z.inj_lt: hidx.
  by rewrite shape.Z_of_nat_expn2.
have hchild := shrincs_fxmss_path_children_bound hd hp hi.
have hdepth : 255-(255-size p) = size p by rewrite !subnE; lia.
have hpos : 0 < 255-size p by apply/ltP; rewrite subnE; lia.
have htest : Z.ltb (2 * Z.of_nat (idx_of_path p) + 1) (2^64) = true.
  by apply/Z.ltb_lt.
rewrite !shrincs_fxmss_path_child_coord.
rewrite [in LHS]/shrincs_fxmss_path_coord shrincs_fxmss_node_at_step //
  /shrincs_fxmss_spec_is_leaf hdepth (ltn_eqF hp).
case: b hd hi => hd hi.
- by rewrite /= hp hpos htest Z.add_0_r.
- rewrite (hi erefl) /= hpos.
  have ht : (1 <? 2^64)%Z = true by vm_compute.
  rewrite ht /=.
  by rewrite /shrincs_fxmss_path_coord /uint (hi erefl).
Qed.

Lemma shrincs_fxmss_node_materialized P keys pk b d rem p fuel :
  shrincs_fxmss_spec_legal_shape b d -> size p + rem = d ->
  (b = false -> idx_of_path p = 0) -> rem < fuel ->
  shrincs_fxmss_node_at P fuel keys (shrincs_fxmss_path_coord p).2
    (shrincs_fxmss_path_coord p).1 pk b (uint U8 d) =
    Some (shrincs_fxmss_subtree_value P pk keys b d p rem).
Proof.
move=> hd.
elim: rem p fuel => [|rem ih] p [|fuel] hdepth hi hfuel //.
- have hp : size p <= d by rewrite addn0 in hdepth; rewrite hdepth.
  have hp255 : size p <= 255.
    apply: leq_trans hp _.
    apply/leP.
    by case: b hd hi => hd hi; simpl in hd; lia.
  apply shrincs_fxmss_node_path_leaf.
  + exact hd.
  + apply/andP; split; first exact: hp255.
    exact: shrincs_fxmss_path_index_bound hd hp hi.
  + by rewrite addn0 in hdepth; rewrite hdepth eqxx.
- have hp : size p < d.
    rewrite -hdepth.
    by rewrite addnS ltnS leq_addr.
  rewrite (shrincs_fxmss_node_path_internal P keys pk fuel hd hp hi).
  have hdepth' (c : bool) : size (rcons p c) + rem = d.
    by rewrite size_rcons addSn -addnS.
  have hleft : b = false -> idx_of_path (rcons p false) = 0.
    by move=> hb; rewrite shrincs_fxmss_path_index_rcons (hi hb).
  rewrite (ih (rcons p false) fuel (hdepth' false) hleft hfuel).
  case hb: b in hd hi hdepth' *.
  + have hright : true = false -> idx_of_path (rcons p true) = 0 by [].
    rewrite hb in ih.
    rewrite (ih (rcons p true) fuel (hdepth' true) hright hfuel).
    by [].
  + have hright : idx_of_path (rcons p true) = 1.
      by rewrite shrincs_fxmss_path_index_rcons (hi erefl).
    have hvalid : shrincs_fxmss_path_valid (rcons p true).
      apply/andP; split.
      * rewrite size_rcons.
        apply: leq_trans hp _.
        by apply/leP; exact: hd.2.
      * rewrite hright.
        change (expn 2 0 < expn 2 64).
        by rewrite ltn_exp2l.
    case: fuel hfuel => [|fuel] hfuel //.
    rewrite (shrincs_fxmss_node_path_leaf P keys pk fuel hd hvalid).
    * by rewrite hright eqxx /= orbT.
    * by [].
Qed.

Lemma shrincs_fxmss_root_materialized P keys pk b d :
  shrincs_fxmss_spec_legal_shape b d ->
  shrincs_fxmss_node P keys (uint U64 0) (uint U8 255) pk b (uint U8 d) =
    Some (val_bt (shrincs_fxmss_tree_node_hash P pk) [::] (shrincs_fxmss_value_tree P pk
      keys b d)).
Proof.
move=> hd.
rewrite /shrincs_fxmss_node shrincs_fxmss_spec_uint8_nat; first by [].
have hdf : d < 256 by apply/ltP; exact: shrincs_fxmss_spec_depth_bound hd.
exact: (@shrincs_fxmss_node_materialized P keys pk b d d [::] 256 hd erefl
  (fun _ => erefl) hdf).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree materialized lookup *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_materialized_lookup P keys pk b d rem pos q u :
  shrincs_fxmss_spec_legal_shape b d -> size pos + rem = d ->
  (b = false -> idx_of_path pos = 0) ->
  subtree_at (shrincs_fxmss_tree_shape b rem) q = Some u ->
  shrincs_fxmss_node P keys (shrincs_fxmss_path_coord (pos ++ q)).2
    (shrincs_fxmss_path_coord (pos ++ q)).1 pk b (uint U8 d) =
  Some (val_bt (shrincs_fxmss_tree_node_hash P pk) (pos ++ q)
    (bt_posmap (fun p _ => shrincs_fxmss_leaf_pubkey P (shrincs_fxmss_path_coord p) b
      (uint U8 d)
      pk (keys (shrincs_fxmss_path_coord p))) (pos ++ q) u)).
Proof.
move=> hd.
have hd255 : (d <= 255)%coq_nat by case: b hd => hd; simpl in hd; lia.
elim: rem pos q u => [|rem ih] pos [|c q] u hdepth hi hs.
- (* At depth zero, the empty path selects the leaf. *)
  case: hs => <-; rewrite cats0 /shrincs_fxmss_node.
  have hp : size pos <= 255 by apply/leP; rewrite addn0 in hdepth; lia.
  have hz : Z.to_nat (wunsigned (shrincs_fxmss_path_coord pos).1) = 255-size pos.
  { rewrite /shrincs_fxmss_path_coord /= shrincs_fxmss_spec_uint8_nat //; rewrite subnE;
    lia. }
  rewrite hz.
  exact: (@shrincs_fxmss_node_materialized P keys pk b d 0 pos _ hd hdepth hi (ltn0Sn
    _)).
- by [].
- (* The empty path selects the current internal subtree. *)
  case: hs => <-; rewrite cats0 /shrincs_fxmss_node.
  have hz : Z.to_nat (wunsigned (shrincs_fxmss_path_coord pos).1) = 255-size pos.
  { rewrite /shrincs_fxmss_path_coord /= shrincs_fxmss_spec_uint8_nat //; rewrite subnE;
    lia. }
  rewrite hz.
  apply: (@shrincs_fxmss_node_materialized P keys pk b d rem.+1 pos _ hd hdepth hi).
  apply/ltP; rewrite subnE addnE in hdepth *; lia.
- have hp : size pos < d by rewrite -hdepth addnS ltnS leq_addr.
  have hdepth' (side : bool) : size (rcons pos side) + rem = d.
    by rewrite size_rcons addSn -addnS.
  rewrite -cat_rcons.
  case hc: c in hs *.
  + case hb: b in hd hi hs ih *.
    * apply: ih; [exact: hdepth' | by [] | exact: hs].
    * case: q hs => [|side q] //= [<-]; rewrite cats0.
      have hright : idx_of_path (rcons pos true) = 1.
        by rewrite shrincs_fxmss_path_index_rcons (hi erefl).
      rewrite /shrincs_fxmss_node.
      apply: shrincs_fxmss_node_path_leaf hd _ _.
      -- apply/andP; split.
         ++ rewrite size_rcons; apply/leP; move/ltP: hp; lia.
         ++ rewrite hright; change (expn 2 0 < expn 2 64).
            by rewrite ltn_exp2l.
      -- by rewrite hright eqxx /= orbT.
  + apply: ih; [exact: hdepth' | | exact: hs].
    by move=> hb; rewrite shrincs_fxmss_path_index_rcons (hi hb).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree bad path *)

Import Shrincs.internal.ssprove.fxmss.scheme.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_auth_parent z i j : shrincs_fxmss_coord :=
  (uint U8 (z + j + 1), wrepr U64 (shrincs_fxmss_spec_ancestor i (j + 1))).

Definition shrincs_fxmss_auth_pair (z : nat) i (ap : seq UInt8) (node : bytes 16) j :
    bytes 16 * bytes 16 :=
  let sibling := slice ap (j * 16) 16 in
  if Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1 then (sibling, node)
  else (node, sibling).

Lemma shrincs_fxmss_auth_pair_neq z i ap ap' x y j :
  x != y -> shrincs_fxmss_auth_pair z i ap x j != shrincs_fxmss_auth_pair z i ap' y j.
Proof.
rewrite /shrincs_fxmss_auth_pair.
case: Z.eqb => hne; by rewrite xpair_eqE (negbTE hne) ?andbF.
Qed.

Lemma shrincs_fxmss_recover_step_pair P pk z i ap node j :
  shrincs_fxmss_recover_step P pk z i ap node j =
    th_eval (shrincs_fxmss_hash_function P) pk (shrincs_fxmss_tree_tweak
      (shrincs_fxmss_auth_parent z i j))
      (shrincs_fxmss_tree_message (shrincs_fxmss_auth_pair z i ap node j)).
Proof.
rewrite /shrincs_fxmss_recover_step /shrincs_fxmss_auth_pair /shrincs_fxmss_auth_parent
  /shrincs_fxmss_tree_message.
by case: Z.eqb.
Qed.

Definition shrincs_fxmss_auth_honest_pair P keys pk b d z i j : bytes 16 * bytes 16 :=
  let node := shrincs_fxmss_honest_node P keys pk b d (z+j) (shrincs_fxmss_spec_ancestor
    i j) in
  let sibling := shrincs_fxmss_honest_sibling P keys pk b d z i j in
  if Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1 then (sibling, node)
  else (node, sibling).

Lemma shrincs_fxmss_auth_pair_honest P keys pk b d z i j :
  j < 255 - z ->
  shrincs_fxmss_auth_pair z i
    (flatten [seq tval x | x <- shrincs_fxmss_honest_auth P keys pk b d z i])
    (shrincs_fxmss_honest_node P keys pk b d (z+j) (shrincs_fxmss_spec_ancestor i j)) j
      =
  shrincs_fxmss_auth_honest_pair P keys pk b d z i j.
Proof.
move=> hj.
rewrite /shrincs_fxmss_auth_pair slice_flatten_rows
  (@shrincs_fxmss_honest_auth_nth P keys pk b d z i j hj).
by [].
Qed.

Lemma shrincs_fxmss_auth_parent_shape b d z i j :
  shrincs_fxmss_spec_on_shape b d z i -> j < 255 - z ->
  shrincs_fxmss_spec_on_shape b d (z+j+1) (shrincs_fxmss_spec_ancestor i (j+1)) /\
  shrincs_fxmss_spec_is_leaf b d (z+j+1) (shrincs_fxmss_spec_ancestor i (j+1)) = false.
Proof.
move=> hs /ltP hj.
have hz : (z+j < 255)%coq_nat by rewrite subnE in hj; rewrite addnE; lia.
have ha := shrincs_fxmss_spec_on_shape_ancestor hs (Nat.lt_le_incl _ _ hz).
by rewrite !addn1 shrincs_fxmss_spec_ancestor_succ; exact:
  shrincs_fxmss_spec_on_shape_parent ha hz.
Qed.

Lemma shrincs_fxmss_bad_path_collision P keys pk b d z i ap node :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  node != shrincs_fxmss_honest_node P keys pk b d z i ->
  foldl (shrincs_fxmss_recover_step P pk z i ap) node (iota 0 (255-z)) =
    shrincs_fxmss_honest_node P keys pk b d 255 0 ->
  exists j candidate,
    [/\ j < 255-z,
        shrincs_fxmss_tree_message candidate !=
          shrincs_fxmss_tree_message (shrincs_fxmss_auth_honest_pair P keys pk b d z i
            j) &
        th_eval (shrincs_fxmss_hash_function P) pk (shrincs_fxmss_tree_tweak
          (shrincs_fxmss_auth_parent z i j))
          (shrincs_fxmss_tree_message candidate) =
        th_eval (shrincs_fxmss_hash_function P) pk (shrincs_fxmss_tree_tweak
          (shrincs_fxmss_auth_parent z i j))
          (shrincs_fxmss_tree_message (shrincs_fxmss_auth_honest_pair P keys pk b d z i
            j))].
Proof.
move=> hd hs hne hv.
have hz : z <= 255 by apply/leP; exact: hs.1.1.
have htotal : z+0+(255-z) = 255 by rewrite addn0 subnKC.
have hroot := shrincs_fxmss_recover_honest_fold P keys pk hd hs htotal.
have he : foldl (shrincs_fxmss_recover_step P pk z i ap) node (iota 0 (255-z)) =
    foldl (shrincs_fxmss_recover_step P pk z i
      (flatten [seq tval x | x <- shrincs_fxmss_honest_auth P keys pk b d z i]))
      (shrincs_fxmss_honest_node P keys pk b d z i) (iota 0 (255-z)).
  by rewrite hv -hroot addn0 shrincs_fxmss_spec_ancestor_zero.
have [j [hj hstates hstep]] := foldl_first_collision hne he.
have hprefix := shrincs_fxmss_recover_honest_prefix P keys pk hd hs (ltnW hj).
rewrite hprefix in hstates hstep.
rewrite add0n !shrincs_fxmss_recover_step_pair in hstep.
exists j, (shrincs_fxmss_auth_pair z i ap
  (foldl (shrincs_fxmss_recover_step P pk z i ap) node (iota 0 j)) j).
split=> //.
- (* Distinct authentication pairs encode distinct target messages. *)
  rewrite -(@shrincs_fxmss_auth_pair_honest P keys pk b d z i j hj).
  apply/eqP=> heq.
  have hepair := shrincs_fxmss_tree_message_inj _ _ heq.
  have hpair := shrincs_fxmss_auth_pair_neq z i ap
    (flatten [seq tval x | x <- shrincs_fxmss_honest_auth P keys pk b d z i]) j hstates.
  by move: hpair; rewrite hepair eqxx.
- by rewrite shrincs_fxmss_auth_pair_honest // in hstep.
Qed.

Lemma shrincs_fxmss_leaf_recover_structure P a b d b' d' pk md ws :
  Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P a b d pk md ws =
    Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P a b' d' pk md ws.
Proof. by []. Qed.

Lemma shrincs_fxmss_recover_fold P pk z i sg md root :
  (z < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  shrincs_fxmss_recover P (wrepr U64 i) (uint U8 z) sg md pk = Some root ->
  exists node,
    Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P (uint U8 z, wrepr
      U64 i) false (uint U8 0)
      pk md (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node /\
    foldl (shrincs_fxmss_recover_step P pk z i (drop (2 + WOTS_C_CHAINS_SIZE) sg))
      node (iota 0 (255-z)) = root.
Proof.
move=> hz hi.
rewrite /shrincs_fxmss_recover shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT.
rewrite wunsigned_repr_small //.
case: ifP => hguard //.
case he: (Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover _ _ _ _ _ _
  _) => [node|] //.
move=> hroot.
exists node; split; first by [].
rewrite /range subn0 in hroot.
by case: hroot.
Qed.

Lemma shrincs_fxmss_verify_bad_path_collision P keys pk b d z i sg md node :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P (uint U8 z, wrepr
    U64 i) b (uint U8 d)
    pk md (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node ->
  node != shrincs_fxmss_honest_node P keys pk b d z i ->
  shrincs_fxmss_verify P pk (shrincs_fxmss_honest_node P keys pk b d 255 0)
    (uint U8 z, wrepr U64 i) sg md ->
  exists j candidate,
    [/\ j < 255-z,
        fxmss_tree_class (shrincs_fxmss_tree_tweak (shrincs_fxmss_auth_parent z i j)),
        shrincs_fxmss_spec_on_shape b d (z+j+1) (shrincs_fxmss_spec_ancestor i (j+1)),
        shrincs_fxmss_tree_message candidate !=
          shrincs_fxmss_tree_message (shrincs_fxmss_auth_honest_pair P keys pk b d z i
            j) &
        th_eval (shrincs_fxmss_hash_function P) pk (shrincs_fxmss_tree_tweak
          (shrincs_fxmss_auth_parent z i j))
          (shrincs_fxmss_tree_message candidate) =
        th_eval (shrincs_fxmss_hash_function P) pk (shrincs_fxmss_tree_tweak
          (shrincs_fxmss_auth_parent z i j))
          (shrincs_fxmss_tree_message (shrincs_fxmss_auth_honest_pair P keys pk b d z i
            j))].
Proof.
move=> hd hs hleaf hne /eqP hv.
have hz : (z < 256)%coq_nat by have := hs.1.1; lia.
have hi := shrincs_fxmss_spec_index_bound hd hs.
have [node' [hleaf' hfold]] := shrincs_fxmss_recover_fold hz hi hv.
have hsame : node' = node.
  rewrite (shrincs_fxmss_leaf_recover_structure P _ false (uint U8 0) b (uint U8 d))
    hleaf in hleaf'.
  by case: hleaf'.
subst node'.
have [j [candidate [hj hn hc]]] := shrincs_fxmss_bad_path_collision hd hs hne hfold.
exists j, candidate.
split=> //.
exact: (shrincs_fxmss_auth_parent_shape hs hj).1.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree recover *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Fixpoint shrincs_fxmss_recover_nodes P pk z i j (node : bytes 16)
    (siblings : seq (bytes 16)) : bytes 16 :=
  if siblings is sibling :: rest then
    let parent := shrincs_fxmss_auth_parent z i j in
    let next := if Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1 then
      shrincs_fxmss_hash_node P pk parent sibling node else shrincs_fxmss_hash_node P pk
        parent node sibling in
    shrincs_fxmss_recover_nodes P pk z i j.+1 next rest
  else node.

Lemma shrincs_fxmss_recover_nodes_slices P pk z i n j node ap :
  shrincs_fxmss_recover_nodes P pk z i j node
    [seq slice ap (k*16) 16 | k <- iota j n] =
    foldl (shrincs_fxmss_recover_step P pk z i ap) node (iota j n).
Proof.
elim: n j node => [|n ih] j node //=.
Qed.

Lemma shrincs_fxmss_ancestor_path_parent p c i j :
  shrincs_fxmss_spec_ancestor i j = Z.of_nat (idx_of_path (rcons p c)) ->
  shrincs_fxmss_spec_ancestor i j.+1 = Z.of_nat (idx_of_path p).
Proof.
move=> he.
rewrite shrincs_fxmss_spec_ancestor_succ he shrincs_fxmss_path_index_child Z.mul_comm
  Z.div_add_l;
  first discriminate.
clear he.
by case: c; rewrite Z.add_0_r.
Qed.

Lemma shrincs_fxmss_ancestor_path_side p c i j :
  shrincs_fxmss_spec_ancestor i j = Z.of_nat (idx_of_path (rcons p c)) ->
  Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1 = c.
Proof.
move=> he.
rewrite he shrincs_fxmss_path_index_child Z.mul_comm Z.add_comm Z.mod_add;
  first discriminate.
clear he.
by case: c.
Qed.

Lemma shrincs_fxmss_auth_parent_path p c z i j :
  size (rcons p c) <= 255 -> z+j = 255-size (rcons p c) ->
  shrincs_fxmss_spec_ancestor i j = Z.of_nat (idx_of_path (rcons p c)) ->
  shrincs_fxmss_auth_parent z i j = shrincs_fxmss_path_coord p.
Proof.
move=> hp hz hi.
have hz' : z+j+1 = 255-size p.
  move/leP: hp=> hp.
  rewrite size_rcons subnE addnE in hz.
  rewrite size_rcons in hp.
  rewrite subnE !addnE.
  lia.
rewrite /shrincs_fxmss_auth_parent hz' addn1 (shrincs_fxmss_ancestor_path_parent hi).
by [].
Qed.

Lemma shrincs_fxmss_recover_nodes_merkle P pk p ap z i j node :
  size p <= 255 -> z+j = 255-size p ->
  shrincs_fxmss_spec_ancestor i j = Z.of_nat (idx_of_path p) ->
  size ap = size p ->
  Some (shrincs_fxmss_recover_nodes P pk z i j node (rev ap)) =
    val_ap (shrincs_fxmss_tree_node_hash P pk) [::] p ap node.
Proof.
elim/last_ind: p ap j node => [|p c ih] ap j node hp hz hi hs.
- have -> : ap = [::] by apply/eqP; rewrite -size_eq0 hs.
  by [].
- case/lastP: ap hs => [|ap s] hs; first by move: hs; rewrite size_rcons.
  have hs' : size ap = size p by move: hs; rewrite !size_rcons => -[].
  rewrite (@val_ap_rcons (bytes 16) (shrincs_fxmss_tree_node_hash P pk)
    [::] p ap c s node hs') rev_rcons.
  cbn [shrincs_fxmss_recover_nodes].
  rewrite (shrincs_fxmss_auth_parent_path hp hz hi) (shrincs_fxmss_ancestor_path_side
    hi) cat0s.
  apply: ih => //.
  + by move: hp; rewrite size_rcons => /ltnW.
  + rewrite addnS hz size_rcons subnSK //.
    by move: hp; rewrite size_rcons.
  + exact: shrincs_fxmss_ancestor_path_parent hi.
Qed.

Definition shrincs_fxmss_signature_path z i := path_of_idx (255-z) (Z.to_nat i).

Definition shrincs_fxmss_signature_auth z (sg : seq UInt8) :=
  rev [seq slice (drop (2 + WOTS_C_CHAINS_SIZE) sg) (k*16) 16
    | k <- iota 0 (255-z)].

Lemma shrincs_fxmss_recover_merkle P pk z i sg md root :
  (z < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  shrincs_fxmss_recover P (wrepr U64 i) (uint U8 z) sg md pk = Some root ->
  exists node,
    Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P (uint U8 z, wrepr
      U64 i) false (uint U8 0)
      pk md (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node /\
    val_ap (shrincs_fxmss_tree_node_hash P pk) [::] (shrincs_fxmss_signature_path z i)
      (shrincs_fxmss_signature_auth z sg) node = Some root.
Proof.
move=> hz hi.
rewrite /shrincs_fxmss_recover shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT.
rewrite wunsigned_repr_small //.
case: ifP => [/andP[hsig hindex]|] //.
case he: (Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover _ _ _ _ _ _
  _) => [node|] //.
move=> hroot.
exists node; split; first by [].
have hfold :
    foldl (shrincs_fxmss_recover_step P pk z i (drop (2 + WOTS_C_CHAINS_SIZE) sg))
      node (iota 0 (255-z)) = root.
  rewrite /range subn0 in hroot.
  by case: hroot.
have hi_full : (i < 2 ^ Z.of_nat (255-z))%Z.
  move/Z.ltb_lt: hindex=> hindex.
  apply: (Z.lt_le_trans _ _ _ hindex).
  apply Z.pow_le_mono_r; first lia.
  apply Znat.Nat2Z.inj_le.
  apply/leP.
  exact: geq_minr.
have hir : Z.to_nat i < expn 2 (255-z).
  apply/ltP/Znat.Nat2Z.inj_lt.
  rewrite Znat.Z2Nat.id; first exact: hi.1.
  by rewrite shape.Z_of_nat_expn2.
have hp : size (shrincs_fxmss_signature_path z i) <= 255.
  by rewrite /shrincs_fxmss_signature_path size_path_of_idx leq_subr.
have hheight : z+0 = 255-size (shrincs_fxmss_signature_path z i).
  rewrite /shrincs_fxmss_signature_path size_path_of_idx addn0 !subnE.
  lia.
have hidx : shrincs_fxmss_spec_ancestor i 0 = Z.of_nat (idx_of_path
  (shrincs_fxmss_signature_path z i)).
  by rewrite shrincs_fxmss_spec_ancestor_zero /shrincs_fxmss_signature_path
    idx_of_path_of_idx //
    Znat.Z2Nat.id; first exact: hi.1.
have hlen : size (shrincs_fxmss_signature_auth z sg) = size
  (shrincs_fxmss_signature_path z i).
  by rewrite /shrincs_fxmss_signature_auth /shrincs_fxmss_signature_path size_rev
    size_map
    size_iota size_path_of_idx.
rewrite -(shrincs_fxmss_recover_nodes_merkle P pk node hp hheight hidx hlen).
by rewrite /shrincs_fxmss_signature_auth revK shrincs_fxmss_recover_nodes_slices hfold.
Qed.

Lemma shrincs_fxmss_verify_merkle_extract P keys pk b d z i sg md :
  shrincs_fxmss_spec_legal_shape b d ->
  (z < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  shrincs_fxmss_verify P pk (shrincs_fxmss_honest_node P keys pk b d 255 0)
    (uint U8 z, wrepr U64 i) sg md ->
  exists node,
    Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P (uint U8 z, wrepr
      U64 i) false (uint U8 0)
      pk md (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node /\
    extract_ok (shrincs_fxmss_tree_node_hash P pk) [::] (shrincs_fxmss_value_tree P pk
      keys b d)
      (shrincs_fxmss_signature_path z i) node
      (extract (shrincs_fxmss_tree_node_hash P pk) [::] (shrincs_fxmss_value_tree P pk
        keys b d)
        (shrincs_fxmss_signature_path z i) (shrincs_fxmss_signature_auth z sg) node).
Proof.
move=> hd hz hi /eqP hv.
have hroot : shrincs_fxmss_honest_node P keys pk b d 255 0 =
    val_bt (shrincs_fxmss_tree_node_hash P pk) [::] (shrincs_fxmss_value_tree P pk keys
      b d).
  by rewrite /shrincs_fxmss_honest_node (shrincs_fxmss_root_materialized P keys pk hd).
have [node [hleaf hpath]] := shrincs_fxmss_recover_merkle hz hi hv.
rewrite hroot in hpath.
exists node; split; first exact: hleaf.
exact: extractP hpath.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree auth model *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_path_node P keys pk b d p :=
  shrincs_fxmss_honest_node P keys pk b d (255-size p) (Z.of_nat (idx_of_path p)).

Lemma shrincs_fxmss_value_lookup P keys pk b d p u :
  shrincs_fxmss_spec_legal_shape b d ->
  subtree_at (shrincs_fxmss_value_tree P pk keys b d) p = Some u ->
  shrincs_fxmss_path_node P keys pk b d p = val_bt (shrincs_fxmss_tree_node_hash P pk) p
    u.
Proof.
move=> hd.
rewrite /shrincs_fxmss_value_tree subtree_at_posmap cat0s.
case hs: (subtree_at (shrincs_fxmss_tree_shape b d) p) => [t|] //= [<-].
have hn := @shrincs_fxmss_materialized_lookup P keys pk b d d [::] p t
  hd erefl (fun _ => erefl) hs.
exact: (congr1 (odflt (zeros 16)) hn).
Qed.

Lemma shrincs_fxmss_path_index_sibling p c :
  Z.of_nat (idx_of_path (rcons p (~~c))) =
  Z.lxor (Z.of_nat (idx_of_path (rcons p c))) 1.
Proof.
rewrite shrincs_fxmss_spec_xor_one; first exact: Znat.Nat2Z.is_nonneg.
have hside := @shrincs_fxmss_ancestor_path_side p c (Z.of_nat (idx_of_path (rcons p c)))
  0
  (shrincs_fxmss_spec_ancestor_zero _).
rewrite shrincs_fxmss_spec_ancestor_zero in hside.
have hdiv : (Z.of_nat (idx_of_path (rcons p c)) / 2)%Z = Z.of_nat (idx_of_path p).
  rewrite shrincs_fxmss_path_index_child Z.mul_comm Z.div_add_l; first discriminate.
  by case: c {hside}; rewrite Z.add_0_r.
rewrite hside hdiv shrincs_fxmss_path_index_child.
by case: c {hside hdiv} => /=; rewrite ?Z.add_0_r.
Qed.

Lemma shrincs_fxmss_sibling_paths_bottom_up P keys pk b d p z i j :
  size p <= 255 -> z+j = 255-size p ->
  shrincs_fxmss_spec_ancestor i j = Z.of_nat (idx_of_path p) ->
  rev [seq shrincs_fxmss_path_node P keys pk b d q | q <- sibling_paths [::] p] =
  [seq shrincs_fxmss_honest_sibling P keys pk b d z i k | k <- iota j (size p)].
Proof.
elim/last_ind: p j => [|p c ih] j hp hz hi; first by [].
rewrite sibling_paths_rcons map_rcons rev_rcons size_rcons /=.
congr (_ :: _).
- by rewrite /shrincs_fxmss_path_node /shrincs_fxmss_honest_sibling hz hi !size_rcons
  shrincs_fxmss_path_index_sibling.
- apply: ih.
  + by move: hp; rewrite size_rcons => /ltnW.
  + rewrite addnS hz size_rcons subnSK //.
    by move: hp; rewrite size_rcons.
  + exact: shrincs_fxmss_ancestor_path_parent hi.
Qed.

Lemma shrincs_fxmss_cons_ap_honest P keys pk b d p u ap z i :
  shrincs_fxmss_spec_legal_shape b d -> size p <= 255 ->
  z = 255-size p -> i = Z.of_nat (idx_of_path p) ->
  subtree_at (shrincs_fxmss_value_tree P pk keys b d) p = Some u ->
  cons_ap (shrincs_fxmss_tree_node_hash P pk) [::] (shrincs_fxmss_value_tree P pk keys b
    d) p = Some ap ->
  rev ap = shrincs_fxmss_honest_auth P keys pk b d z i.
Proof.
move=> hd hp hz hi hs ha.
have hf : forall q v, subtree_at (shrincs_fxmss_value_tree P pk keys b d) q = Some v ->
    shrincs_fxmss_path_node P keys pk b d q = val_bt (shrincs_fxmss_tree_node_hash P pk)
      q v.
  move=> q v; exact: shrincs_fxmss_value_lookup hd.
have he := @cons_ap_sibling_values (bytes 16) (shrincs_fxmss_tree_node_hash P pk)
  (shrincs_fxmss_path_node P keys pk b d) [::] (shrincs_fxmss_value_tree P pk keys b d)
    p u hf hs.
rewrite ha in he; case: he => ->.
rewrite (@shrincs_fxmss_sibling_paths_bottom_up P keys pk b d p z i 0 hp);
  first by rewrite addn0.
- by rewrite shrincs_fxmss_spec_ancestor_zero.
- rewrite /shrincs_fxmss_honest_auth /range subn0 hz subKn //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree targets *)

Import Shrincs.internal.ssprove.fxmss.scheme.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_tree_target_pair P keys pk b d (a : shrincs_fxmss_coord) :
    bytes 16 * bytes 16 :=
  let z := (Z.to_nat (wunsigned a.1)).-1 in
  let i := wunsigned a.2 in
  (shrincs_fxmss_honest_node P keys pk b d z (2*i),
   shrincs_fxmss_honest_node P keys pk b d z (2*i+1)).

Lemma shrincs_fxmss_auth_pair_children P keys pk b d z i j :
  shrincs_fxmss_spec_on_shape b d z i -> j < 255-z ->
  shrincs_fxmss_auth_honest_pair P keys pk b d z i j =
    (shrincs_fxmss_honest_node P keys pk b d (z+j) (2*(shrincs_fxmss_spec_ancestor i j /
      2)),
     shrincs_fxmss_honest_node P keys pk b d (z+j) (2*(shrincs_fxmss_spec_ancestor i j /
       2)+1)).
Proof.
move=> hs hj.
have hlt : (z+j < 255)%coq_nat.
  move/ltP: hj; rewrite subnE addnE; lia.
have ha := shrincs_fxmss_spec_on_shape_ancestor hs (Nat.lt_le_incl _ _ hlt).
have hi := ha.2.1.
have hsum := Z.div_mod (shrincs_fxmss_spec_ancestor i j) 2 ltac:(lia).
have hmod := Z.mod_pos_bound (shrincs_fxmss_spec_ancestor i j) 2 ltac:(lia).
rewrite /shrincs_fxmss_auth_honest_pair /shrincs_fxmss_honest_sibling
  (shrincs_fxmss_spec_xor_one hi).
case he: (Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1).
- move/Z.eqb_eq: he=> he.
  have -> : (2*(shrincs_fxmss_spec_ancestor i j / 2)+1 = shrincs_fxmss_spec_ancestor i
    j)%Z by lia.
  by [].
- move/Z.eqb_neq: he=> he.
  have -> : (2*(shrincs_fxmss_spec_ancestor i j / 2) = shrincs_fxmss_spec_ancestor i
    j)%Z by lia.
  by [].
Qed.

Lemma shrincs_fxmss_auth_pair_target P keys pk b d z i j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i -> j < 255-z
    ->
  shrincs_fxmss_auth_honest_pair P keys pk b d z i j =
    shrincs_fxmss_tree_target_pair P keys pk b d (shrincs_fxmss_auth_parent z i j).
Proof.
move=> hd hs hj.
have [hp _] := shrincs_fxmss_auth_parent_shape hs hj.
have hi := shrincs_fxmss_spec_index_bound hd hp.
have hz : (z+j+1 < 256)%coq_nat by have := hp.1.1; lia.
change (shrincs_fxmss_auth_honest_pair P keys pk b d z i j =
  (shrincs_fxmss_honest_node P keys pk b d
     (Z.to_nat (wunsigned (uint U8 (z+j+1)))).-1
     (2 * wunsigned (wrepr U64 (shrincs_fxmss_spec_ancestor i (j+1)))),
   shrincs_fxmss_honest_node P keys pk b d
     (Z.to_nat (wunsigned (uint U8 (z+j+1)))).-1
     (2 * wunsigned (wrepr U64 (shrincs_fxmss_spec_ancestor i (j+1))) + 1))).
rewrite shrincs_fxmss_spec_uint8_nat // wunsigned_repr_small // !addn1.
rewrite shrincs_fxmss_spec_ancestor_succ.
exact: shrincs_fxmss_auth_pair_children hs hj.
Qed.

Definition shrincs_fxmss_tree_targets P keys pk b d : seq (tweak * seq UInt8) :=
  [seq (shrincs_fxmss_tree_path_tweak p,
        shrincs_fxmss_tree_message (shrincs_fxmss_tree_target_pair P keys pk b d
          (shrincs_fxmss_path_coord p)))
    | p <- internal_paths (shrincs_fxmss_tree_shape b d)].

Lemma shrincs_fxmss_verify_tree_target_collision P keys pk b d z i sg md node :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover P (uint U8 z, wrepr
    U64 i) b (uint U8 d)
    pk md (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node ->
  node != shrincs_fxmss_honest_node P keys pk b d z i ->
  shrincs_fxmss_verify P pk (shrincs_fxmss_honest_node P keys pk b d 255 0)
    (uint U8 z, wrepr U64 i) sg md ->
  exists t target candidate,
    [/\ (t, target) \in shrincs_fxmss_tree_targets P keys pk b d,
        fxmss_tree_class t,
        candidate != target &
        th_eval (shrincs_fxmss_hash_function P) pk t candidate = th_eval
          (shrincs_fxmss_hash_function P) pk t target].
Proof.
move=> hd hs hleaf hne hv.
have [j [candidate [hj hclass hp hdiff heq]]] :=
  shrincs_fxmss_verify_bad_path_collision hd hs hleaf hne hv.
have [_ hl] := shrincs_fxmss_auth_parent_shape hs hj.
have [p [hmem ht]] := shrincs_fxmss_tree_internal_cover hd hp hl.
have hcoord : shrincs_fxmss_path_coord p = shrincs_fxmss_auth_parent z i j.
  exact: shrincs_fxmss_tree_tweak_inj _ _ ht.
have hpair := shrincs_fxmss_auth_pair_target P keys pk hd hs hj.
exists (shrincs_fxmss_tree_path_tweak p),
  (shrincs_fxmss_tree_message (shrincs_fxmss_tree_target_pair P keys pk b d
    (shrincs_fxmss_path_coord p))),
  (shrincs_fxmss_tree_message candidate).
split.
- by apply/mapP; exists p.
- exact: shrincs_fxmss_tree_path_class.
- by rewrite hcoord -hpair.
- by rewrite ht hcoord -hpair.
Qed.

Lemma shrincs_fxmss_tree_targets_budget P keys pk b d (Q : shrincs_fxmss_resources) :
  shrincs_fxmss_spec_legal_shape b d ->
  size (shrincs_fxmss_tree_targets P keys pk b d) <= shrincs_fxmss_leaf_capacity Q - 1.
Proof.
move=> /shrincs_fxmss_legal_shapeP hd.
rewrite /shrincs_fxmss_tree_targets size_map.
have := shrincs_fxmss_tree_target_budget Q b d hd.
by rewrite size_map.
Qed.

Lemma shrincs_fxmss_tree_targets_fresh P keys pk b d :
  shrincs_fxmss_spec_legal_shape b d -> uniq (unzip1 (shrincs_fxmss_tree_targets P keys
    pk b d)).
Proof.
move=> /shrincs_fxmss_legal_shapeP hd.
rewrite /shrincs_fxmss_tree_targets /unzip1 -map_comp /=.
exact: shrincs_fxmss_tree_targets_uniq b d hd.
Qed.
