(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.merkle_fold

    Peeling the last path edge computes the first bottom-up authentication
    hash. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Lemma val_ap_rcons {A : eqType} (h : seq bool -> A -> A -> A)
    pos p ap b s v :
  size ap = size p ->
  val_ap h pos (rcons p b) (rcons ap s) v =
  val_ap h pos p ap
    (if b then h (pos ++ p) s v else h (pos ++ p) v s).
Proof.
elim: p pos ap => [|c p ih] pos [|a ap] //= hs.
- by rewrite cats0; case: b.
- rewrite ih; first by case: hs.
  by rewrite cat_rcons.
Qed.
