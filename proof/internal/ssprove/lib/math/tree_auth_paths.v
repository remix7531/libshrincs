(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.tree_auth_paths

    Authentication paths enumerate the values at the sibling positions. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint sibling_paths (pos p : seq bool) : seq (seq bool) :=
  if p is b :: q then rcons pos (~~ b) :: sibling_paths (rcons pos b) q
  else [::].

Lemma sibling_paths_rcons pos p b :
  sibling_paths pos (rcons p b) =
  rcons (sibling_paths pos p) (rcons (pos ++ p) (~~ b)).
Proof.
elim: p pos => [|c p ih] pos /=; first by rewrite cats0.
by rewrite ih cat_rcons.
Qed.

Lemma cons_ap_sibling_values (A : eqType) (h : seq bool -> A -> A -> A)
    (f : seq bool -> A) pos t p u :
  (forall q v, subtree_at t q = Some v -> f (pos ++ q) = val_bt h (pos ++ q) v) ->
  subtree_at t p = Some u ->
  cons_ap h pos t p = Some [seq f q | q <- sibling_paths pos p].
Proof.
elim: p pos t => [|b p ih] pos [a|l r] hf hs //=.
case: b hs => hs /=.
- rewrite (ih (rcons pos true) r) //.
  + move=> q v hq.
    have hv := hf (true :: q) v hq.
    by rewrite -cat_rcons in hv.
  + have hv := hf [:: false] l erefl.
    by rewrite cats1 in hv; rewrite /= hv.
- rewrite (ih (rcons pos false) l) //.
  + move=> q v hq.
    have hv := hf (false :: q) v hq.
    by rewrite -cat_rcons in hv.
  + have hv := hf [:: true] r erefl.
    by rewrite cats1 in hv; rewrite /= hv.
Qed.
