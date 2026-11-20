(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.tree_lookup

    Subtree and leaf lookup commute with a position-dependent leaf map. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree tree_paths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma subtree_at_posmap {A B : Type} (f : seq bool -> A -> B)
    pos (t : bt A) p :
  subtree_at (bt_posmap f pos t) p =
    omap (bt_posmap f (pos ++ p)) (subtree_at t p).
Proof.
elim: p pos t => [|b p ih] pos [x|l r] /=.
- by rewrite cats0.
- by rewrite cats0.
- by [].
- by case: b => /=; rewrite ih cat_rcons.
Qed.

Lemma leaf_at_posmap {A B : Type} (f : seq bool -> A -> B)
    pos (t : bt A) p :
  leaf_at (bt_posmap f pos t) p =
    omap (f (pos ++ p)) (leaf_at t p).
Proof.
rewrite /leaf_at subtree_at_posmap.
by case: (subtree_at t p) => [[x|l r]|].
Qed.
