(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.tree_paths

    Internal-node target enumeration and its exact leaf-count budget.
    Mapping leaf values by absolute position leaves the target positions
    unchanged. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Fixpoint bt_posmap {A B : Type} (f : seq bool -> A -> B)
    (pos : seq bool) (t : bt A) : bt B :=
  match t with
  | BLeaf a => BLeaf (f pos a)
  | BNode l r => BNode (bt_posmap f (rcons pos false) l)
      (bt_posmap f (rcons pos true) r)
  end.

Lemma internal_paths_posmap {A B : Type} (f : seq bool -> A -> B)
    pos (t : bt A) :
  internal_paths (bt_posmap f pos t) = internal_paths t.
Proof.
elim: t pos => [a|l ihl r ihr] pos //=.
by rewrite ihl ihr.
Qed.

Lemma leaf_paths_posmap {A B : Type} (f : seq bool -> A -> B)
    pos (t : bt A) :
  leaf_paths (bt_posmap f pos t) = leaf_paths t.
Proof.
elim: t pos => [a|l ihl r ihr] pos //=.
by rewrite ihl ihr.
Qed.

Lemma internal_path_depth {A : Type} (t : bt A) (q : seq bool) :
  q \in internal_paths t -> size q < bt_depth t.
Proof.
elim: t q => [a|l ihl r ihr] q /=; first by rewrite in_nil.
rewrite inE => /orP[/eqP ->|]; first by [].
rewrite mem_cat => /orP[] /mapP[q' hq' ->] /=.
- by rewrite ltnS leq_max ihl.
- by rewrite ltnS leq_max ihr ?orbT.
Qed.

Lemma internal_paths_uniq {A : Type} (t : bt A) :
  uniq (internal_paths t).
Proof.
elim: t => [a|l ihl r ihr] //.
change (uniq ([::] :: ([seq false :: q | q <- internal_paths l]
  ++ [seq true :: q | q <- internal_paths r]))).
rewrite cons_uniq.
apply/andP; split.
- rewrite mem_cat negb_or.
  apply/andP; split.
  + by apply/negP => /mapP[q _].
  + by apply/negP => /mapP[q _].
- have hinj (b : bool) : injective (cons b) by move=> p q [].
  rewrite cat_uniq !(map_inj_uniq (hinj _)) ihl ihr /= andbT.
  apply/hasPn => z /mapP[q _ ->].
  by apply/negP => /mapP[q' _].
Qed.

Lemma bt_nleaves_pos {A : Type} (t : bt A) : 0 < bt_nleaves t.
Proof.
by elim: t => [a|l ihl r ihr] //=; rewrite addn_gt0 ihl.
Qed.

Lemma size_internal_paths {A : Type} (t : bt A) :
  size (internal_paths t) = (bt_nleaves t).-1.
Proof.
elim: t => [a|l ihl r ihr] //=.
rewrite size_cat !size_map ihl ihr.
have hl := bt_nleaves_pos l.
have hr := bt_nleaves_pos r.
rewrite -(prednK hl) -(prednK hr) addSn addnS /=.
by rewrite -addnS prednK.
Qed.

Lemma internal_paths_subtree {A : Type} (t : bt A) p :
  p \in internal_paths t ->
  exists l r, subtree_at t p = Some (BNode l r).
Proof.
elim: t p => [a|l ihl r ihr] p /=; first by rewrite in_nil.
rewrite inE => /orP[/eqP ->|].
- by exists l, r.
- rewrite mem_cat => /orP[] /mapP[q hq ->] /=.
  + exact: ihl hq.
  + exact: ihr hq.
Qed.

Lemma internal_paths_leaf_disjoint {A : Type} (t : bt A) p :
  p \in internal_paths t -> p \notin leaf_paths t.
Proof.
move=> hp.
have [l [r hs]] := internal_paths_subtree hp.
apply/negP=> hl.
have := leaf_paths_correct hl.
by rewrite /leaf_at hs.
Qed.

(** Right subtree, left subtree, then parent: both children are available
    before the parent is queried, while the hash keeps its ordered inputs. *)
Definition tree_postorder {A : Type} (pos : seq bool) (t : bt A) :
    seq (seq bool) :=
  [seq pos ++ q | q <- rev (internal_paths t)].

Lemma tree_postorder_leaf {A : Type} pos (a : A) :
  tree_postorder pos (BLeaf a) = [::].
Proof. by []. Qed.

Lemma tree_postorder_node {A : Type} pos (l r : bt A) :
  tree_postorder pos (BNode l r) =
    tree_postorder (rcons pos true) r ++
    tree_postorder (rcons pos false) l ++ [:: pos].
Proof.
rewrite /tree_postorder /= rev_cons rev_cat -!map_rev
  map_rcons !map_cat -!map_comp /= cats0 -cats1 catA.
congr (_ ++ [:: pos]).
congr (_ ++ _); apply: eq_map => q /=; by rewrite cat_rcons.
Qed.

Lemma tree_postorder_root {A : Type} (t : bt A) :
  tree_postorder [::] t = rev (internal_paths t).
Proof. by rewrite /tree_postorder /= map_id. Qed.

Lemma tree_postorder_uniq {A : Type} (t : bt A) :
  uniq (tree_postorder [::] t).
Proof. by rewrite tree_postorder_root rev_uniq internal_paths_uniq. Qed.

Lemma tree_postorder_size {A : Type} pos (t : bt A) :
  size (tree_postorder pos t) = (bt_nleaves t).-1.
Proof. by rewrite /tree_postorder size_map size_rev size_internal_paths. Qed.
