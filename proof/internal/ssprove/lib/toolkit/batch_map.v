(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.batch_map

    Deferring total local computations across a finite list of queries.
    Queries may use state and may abort. Their arguments must already be
    fixed: the next query cannot depend on an earlier completed result. *)

From Shrincs.internal.ssprove.lib Require Import prelude.

Import PackageNotation.
#[local] Open Scope package_scope.

Section BatchMap.
Context {X : Type} {Y Z : choice_type}.
Context (query : X -> raw_code Y) (finish : X -> Y -> Z).

Fixpoint query_list (xs : seq X) : raw_code (chList Y) :=
  match xs with
  | [::] => ret [::]
  | x :: xs' =>
      y ← query x ;;
      ys ← query_list xs' ;;
      ret (y :: ys)
  end.

Fixpoint eager_map (xs : seq X) : raw_code (chList Z) :=
  match xs with
  | [::] => ret [::]
  | x :: xs' =>
      y ← query x ;;
      let z := finish x y in
      zs ← eager_map xs' ;;
      ret (z :: zs)
  end.

Lemma eager_map_batch xs :
  eager_map xs =
  (ys ← query_list xs ;;
   ret [seq finish xy.1 xy.2 | xy <- zip xs ys]).
Proof.
elim: xs => [|x xs ih] //=.
rewrite bind_assoc.
congr (bind (query x) _).
apply boolp.funext => y.
rewrite ih !bind_assoc.
by congr (bind (query_list xs) _).
Qed.

End BatchMap.
