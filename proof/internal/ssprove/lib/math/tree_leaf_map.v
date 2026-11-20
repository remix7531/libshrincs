(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.tree_leaf_map

    A position-dependent leaf map only observes positions in the tree.
    This permits a finite leaf table to replace a total leaf evaluator. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree tree_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Lemma bt_posmap_leaf_congr {A B : Type}
    (f g : seq bool -> A -> B) pos (t : bt A) :
  (forall p x, p \in leaf_paths t -> f (pos ++ p) x = g (pos ++ p) x) ->
  bt_posmap f pos t = bt_posmap g pos t.
Proof.
elim: t pos => [x|l ihl r ihr] pos he /=.
- have hx := he [::] x (mem_head _ _).
  by rewrite cats0 in hx; rewrite hx.
- congr BNode.
  + apply: ihl => p x hp.
    rewrite cat_rcons.
    apply: he.
    by rewrite /= mem_cat (map_f (cons false) hp).
  + apply: ihr => p x hp.
    rewrite cat_rcons.
    apply: he.
    by rewrite /= mem_cat (map_f (cons true) hp) orbT.
Qed.
