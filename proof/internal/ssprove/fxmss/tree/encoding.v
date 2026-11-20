(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.encoding

    Pure tree shapes for the two legal FXMSS structures. Merkle collision
    witnesses at the byte-domain tree targets. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree tree_paths merkle.
From Shrincs.internal.ssprove.fxmss Require Import params shape model.nodes scheme.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Tree shape *)

#[local] Open Scope nat_scope.

Fixpoint shrincs_fxmss_tree_shape (b : bool) (d : nat) : bt unit :=
  if d is d'.+1 then
    BNode (shrincs_fxmss_tree_shape b d')
      (if b then shrincs_fxmss_tree_shape b d' else BLeaf tt)
  else BLeaf tt.

Lemma shrincs_fxmss_tree_shape_depth b d : bt_depth (shrincs_fxmss_tree_shape b d) = d.
Proof.
elim: d => [|d ih] //=.
by case: b in ih *; rewrite /= ih ?maxnn ?maxn0.
Qed.

Lemma shrincs_fxmss_tree_shape_count b d :
  bt_nleaves (shrincs_fxmss_tree_shape b d) = shrincs_fxmss_leaf_count b d.
Proof.
elim: d => [|d ih]; first by case: b.
case: b in ih *; rewrite /= ih /shrincs_fxmss_leaf_count.
- by rewrite expnS mul2n addnn.
- by rewrite addn1.
Qed.

Lemma shrincs_fxmss_tree_internal_size b d p :
  shrincs_fxmss_structure_legal b d ->
  p \in internal_paths (shrincs_fxmss_tree_shape b d) -> size p < d.
Proof.
move=> _ hp.
by have := internal_path_depth hp; rewrite shrincs_fxmss_tree_shape_depth.
Qed.

Lemma shrincs_fxmss_tree_internal_count b d :
  size (internal_paths (shrincs_fxmss_tree_shape b d)) =
    (shrincs_fxmss_leaf_count b d).-1.
Proof. by rewrite size_internal_paths shrincs_fxmss_tree_shape_count. Qed.

Lemma shrincs_fxmss_tree_unbalanced_internal d p :
  p \in internal_paths (shrincs_fxmss_tree_shape false d) ->
  p = nseq (size p) false.
Proof.
elim: d p => [|d ih] p /=; first by rewrite in_nil.
rewrite cats0 inE => /orP[/eqP ->|]; first by [].
move/mapP=> [q hq ->] /=.
by congr (false :: _); exact: ih q hq.
Qed.

Lemma idx_of_path_false n : idx_of_path (nseq n false) = 0.
Proof.
rewrite /idx_of_path rev_nseq.
by elim: n => [|n ih] //=; rewrite ih.
Qed.

Lemma shrincs_fxmss_tree_internal_index b d p :
  shrincs_fxmss_structure_legal b d ->
  p \in internal_paths (shrincs_fxmss_tree_shape b d) -> idx_of_path p < 2 ^ 64.
Proof.
move=> hd hp.
case: b hd hp => hd hp.
- have hs := shrincs_fxmss_tree_internal_size true d p hd hp.
  have hd64 := shrincs_fxmss_balanced_depth d hd.
  apply: (leq_trans (idx_of_path_lt p)).
  by rewrite leq_exp2l //; exact: leq_trans (ltnW hs) hd64.
- rewrite (shrincs_fxmss_tree_unbalanced_internal d p hp) idx_of_path_false.
  by rewrite expn_gt0.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree encoding *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_path_coord (p : seq bool) : shrincs_fxmss_coord :=
  (uint U8 (255 - size p), uint U64 (idx_of_path p)).

Definition shrincs_fxmss_path_valid (p : seq bool) : bool :=
  (size p <= 255) && (idx_of_path p < 2 ^ 64).

Lemma shrincs_fxmss_uint64_nat n : n < 2 ^ 64 ->
  Z.to_nat (wunsigned (uint U64 n)) = n.
Proof.
move/ltP/Znat.Nat2Z.inj_lt=> hn.
rewrite shape.Z_of_nat_expn2 in hn.
rewrite /uint wunsigned_repr_small ?Znat.Nat2Z.id //.
by split; [exact: Znat.Nat2Z.is_nonneg | exact: hn].
Qed.

Lemma shrincs_fxmss_path_coord_inj p q :
  shrincs_fxmss_path_valid p -> shrincs_fxmss_path_valid q ->
  shrincs_fxmss_path_coord p = shrincs_fxmss_path_coord q -> p = q.
Proof.
move=> /andP[hp hpi] /andP[hq hqi] he.
have hh := congr1 (fun a : shrincs_fxmss_coord => Z.to_nat (wunsigned a.1)) he.
have hi := congr1 (fun a : shrincs_fxmss_coord => Z.to_nat (wunsigned a.2)) he.
change (Z.to_nat (wunsigned (uint U8 (255 - size p))) =
  Z.to_nat (wunsigned (uint U8 (255 - size q)))) in hh.
rewrite !shrincs_fxmss_spec_uint8_nat in hh; try (rewrite subnE; lia).
change (Z.to_nat (wunsigned (uint U64 (idx_of_path p))) =
  Z.to_nat (wunsigned (uint U64 (idx_of_path q)))) in hi.
rewrite !shrincs_fxmss_uint64_nat // in hi.
have hs : size p = size q.
  move/leP: hp=> hp; move/leP: hq=> hq.
  rewrite !subnE in hh.
  lia.
by rewrite -[p]path_of_idx_of_path -[q]path_of_idx_of_path hs hi.
Qed.

Definition shrincs_fxmss_tree_message (xy : bytes 16 * bytes 16) : seq UInt8 :=
  xy.1 ++ xy.2.

Lemma shrincs_fxmss_tree_message_size xy : size (shrincs_fxmss_tree_message xy) = 32.
Proof. by rewrite /shrincs_fxmss_tree_message size_cat !size_tuple. Qed.

Lemma shrincs_fxmss_tree_message_inj : injective shrincs_fxmss_tree_message.
Proof.
move=> [x y] [x' y'] he.
have hx := congr1 (fun bs => slice bs 0 16) he.
have hy := congr1 (fun bs => slice bs 16 16) he.
rewrite /shrincs_fxmss_tree_message /= !shape.slice_cat_head in hx.
rewrite /shrincs_fxmss_tree_message /= -[16]/(16 + 0)
  !shape.slice_cat_tail !shape.slice_all in hy.
by rewrite hx hy.
Qed.

Lemma shrincs_fxmss_tree_class_public : shrincs_fxmss_tree_class = fxmss_tree_class.
Proof. by []. Qed.

Definition shrincs_fxmss_tree_path_tweak p := shrincs_fxmss_tree_tweak
  (shrincs_fxmss_path_coord p).

Lemma shrincs_fxmss_tree_path_class p : fxmss_tree_class (shrincs_fxmss_tree_path_tweak
  p).
Proof. by []. Qed.

Lemma shrincs_fxmss_tree_internal_valid b d p :
  shrincs_fxmss_structure_legal b d ->
  p \in internal_paths (shrincs_fxmss_tree_shape b d) -> shrincs_fxmss_path_valid p.
Proof.
move=> hd hp.
apply/andP; split.
- apply: (leq_trans (ltnW (shrincs_fxmss_tree_internal_size b d p hd hp))).
  exact: shrincs_fxmss_legal_depth b d hd.
- exact: shrincs_fxmss_tree_internal_index b d p hd hp.
Qed.

Lemma shrincs_fxmss_tree_path_tweak_inj p q :
  shrincs_fxmss_path_valid p -> shrincs_fxmss_path_valid q ->
  shrincs_fxmss_tree_path_tweak p = shrincs_fxmss_tree_path_tweak q -> p = q.
Proof.
move=> hp hq /shrincs_fxmss_tree_tweak_inj he.
exact: shrincs_fxmss_path_coord_inj p q hp hq he.
Qed.

Lemma shrincs_fxmss_tree_targets_uniq b d :
  shrincs_fxmss_structure_legal b d ->
  uniq [seq shrincs_fxmss_tree_path_tweak p | p <- internal_paths
    (shrincs_fxmss_tree_shape b d)].
Proof.
move=> hd.
rewrite map_inj_in_uniq.
- move=> p q hp hq.
  exact: shrincs_fxmss_tree_path_tweak_inj p q
    (shrincs_fxmss_tree_internal_valid b d p hd hp) (shrincs_fxmss_tree_internal_valid b
      d q hd hq).
- exact: internal_paths_uniq.
Qed.

Lemma shrincs_fxmss_tree_hash_eval P pp p xy :
  th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_tree_path_tweak p)
    (shrincs_fxmss_tree_message xy) =
    shrincs_fxmss_hash_node P pp (shrincs_fxmss_path_coord p) xy.1 xy.2.
Proof. by []. Qed.

Lemma shrincs_fxmss_tree_target_budget (Q : shrincs_fxmss_resources) b d :
  shrincs_fxmss_structure_legal b d ->
  size [seq shrincs_fxmss_tree_path_tweak p | p <- internal_paths
    (shrincs_fxmss_tree_shape b d)]
    <= shrincs_fxmss_leaf_capacity Q - 1.
Proof.
move=> hd.
rewrite size_map shrincs_fxmss_tree_internal_count -subn1.
apply: leq_sub2r.
exact: shrincs_fxmss_leaf_count_bound b d hd.
Qed.

Lemma shrincs_fxmss_tree_target_fresh b d p ps :
  shrincs_fxmss_structure_legal b d ->
  p \in internal_paths (shrincs_fxmss_tree_shape b d) ->
  all (fun q => q \in internal_paths (shrincs_fxmss_tree_shape b d)) ps ->
  p \notin ps -> shrincs_fxmss_tree_path_tweak p \notin [seq
    shrincs_fxmss_tree_path_tweak q | q <- ps].
Proof.
move=> hd hp /allP hps hfresh.
apply/negP=> /mapP[q hq he].
have heq := shrincs_fxmss_tree_path_tweak_inj p q
  (shrincs_fxmss_tree_internal_valid b d p hd hp)
  (shrincs_fxmss_tree_internal_valid b d q hd (hps q hq)) he.
by move: hfresh; rewrite heq hq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree extraction *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Open Scope nat_scope.

Definition shrincs_fxmss_tree_node_hash (P : shrincs_fxmss_params) (pp : bytes 16)
    (p : seq bool) (x y : bytes 16) : bytes 16 :=
  shrincs_fxmss_hash_node P pp (shrincs_fxmss_path_coord p) x y.

Definition shrincs_fxmss_value_tree (P : shrincs_fxmss_params) (pp : bytes 16)
    (keys : shrincs_fxmss_coord -> seq (bytes 16)) (b : bool) (d : nat) :=
  bt_posmap (fun p _ => shrincs_fxmss_leaf_pubkey P (shrincs_fxmss_path_coord p) b (uint
    U8 d)
    pp (keys (shrincs_fxmss_path_coord p))) [::] (shrincs_fxmss_tree_shape b d).

Lemma shrincs_fxmss_value_tree_internal P pp keys b d :
  internal_paths (shrincs_fxmss_value_tree P pp keys b d) =
    internal_paths (shrincs_fxmss_tree_shape b d).
Proof. exact: internal_paths_posmap. Qed.

Lemma shrincs_fxmss_value_tree_leaf P pp keys b d :
  leaf_paths (shrincs_fxmss_value_tree P pp keys b d) = leaf_paths
    (shrincs_fxmss_tree_shape b d).
Proof. exact: leaf_paths_posmap. Qed.

Lemma shrincs_fxmss_tree_collision P pp keys b d p ap a q x y :
  shrincs_fxmss_structure_legal b d ->
  val_ap (shrincs_fxmss_tree_node_hash P pp) [::] p ap a =
    Some (val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
      (shrincs_fxmss_value_tree P pp keys b d)) ->
  extract (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d) p ap a = FColl q x y ->
  exists l r,
    [/\ q \in internal_paths (shrincs_fxmss_tree_shape b d),
        subtree_at (shrincs_fxmss_value_tree P pp keys b d) q = Some (BNode l r),
        y = (val_bt (shrincs_fxmss_tree_node_hash P pp) (rcons q false) l,
             val_bt (shrincs_fxmss_tree_node_hash P pp) (rcons q true) r),
        shrincs_fxmss_tree_message x != shrincs_fxmss_tree_message y &
        th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_tree_path_tweak q)
          (shrincs_fxmss_tree_message x) =
          th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_tree_path_tweak q)
            (shrincs_fxmss_tree_message y)].
Proof.
move=> hd hv he.
have hspec := extractP hv.
rewrite he /extract_ok in hspec.
case: hspec => qrel [l [r [hq hs hy hc hn]]].
rewrite cat0s in hq.
subst qrel.
exists l, r.
split=> //.
- rewrite -(shrincs_fxmss_value_tree_internal P pp keys b d).
  exact: internal_pathsP hs.
- apply/eqP=> heq.
  exact: hn (shrincs_fxmss_tree_message_inj x y heq).
Qed.

Corollary shrincs_fxmss_tree_collision_target P pp keys b d p ap a q x y :
  shrincs_fxmss_structure_legal b d ->
  val_ap (shrincs_fxmss_tree_node_hash P pp) [::] p ap a =
    Some (val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
      (shrincs_fxmss_value_tree P pp keys b d)) ->
  extract (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d) p ap a = FColl q x y ->
  [/\ fxmss_tree_class (shrincs_fxmss_tree_path_tweak q),
      shrincs_fxmss_tree_path_tweak q \in
        [seq shrincs_fxmss_tree_path_tweak r | r <- internal_paths
          (shrincs_fxmss_tree_shape b d)],
      shrincs_fxmss_tree_message x != shrincs_fxmss_tree_message y &
      th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_tree_path_tweak q)
        (shrincs_fxmss_tree_message x) =
        th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_tree_path_tweak q)
          (shrincs_fxmss_tree_message y)].
Proof.
move=> hd hv he.
have [l [r [hq hs hy hn hc]]] :=
  shrincs_fxmss_tree_collision P pp keys b d p ap a q x y hd hv he.
split=> //.
by apply/mapP; exists q.
Qed.
