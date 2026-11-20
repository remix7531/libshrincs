(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.fold_collision

    Unequal starting states that reach the same final state must meet at
    a step. The witness retains the exact prefix states and loop index,
    allowing a Merkle reduction to recover the two hash inputs. *)

From mathcomp Require Import boot order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Lemma foldl_first_collision (A : eqType) (f g : A -> nat -> A)
    n j (x y : A) :
  x != y -> foldl f x (iota j n) = foldl g y (iota j n) ->
  exists k,
    [/\ k < n,
        foldl f x (iota j k) != foldl g y (iota j k) &
        f (foldl f x (iota j k)) (j + k) =
          g (foldl g y (iota j k)) (j + k)].
Proof.
elim: n j x y => [|n ih] j x y hne he.
- (* No steps: equal final states contradict unequal inputs. *)
  change (x = y) in he.
  by move: hne; rewrite he eqxx.
- (* At least one step: compare the next states. *)
  case heq: (f x j == g y j).
  + (* The first step collides. *)
    exists 0.
    by rewrite /= addn0 (eqP heq).
  + (* The states remain distinct; recurse on the suffix. *)
    have [k [hk hstates hstep]] :=
      ih j.+1 (f x j) (g y j) (negbT heq) he.
    exists k.+1.
    by rewrite /= ltnS addnS -addSn.
Qed.
