(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.fmap_size

    A finite map has no more distinct values than keys. *)

From mathcomp Require Import boot order.
From extructures Require Import ord fset fmap.
Local Open Scope fset_scope.

Lemma size_codomm_le {T S : ordType} (m : {fmap T -> S}) :
  (size (codomm m) <= size (domm m))%nat.
Proof.
case: (altP (fset0Pn (codomm m))) => [[y0 hy0] | ]; last first.
- by rewrite negbK => /eqP ->; rewrite sizes0.
- (* A nonempty codomain is contained in the image of the domain. *)
  have hsub : codomm m `<=` (fun k => odflt y0 (getm m k)) @` domm m.
  { apply/fsubsetP => y /codommP [k hk].
    have hkd : k \in domm m by rewrite mem_domm hk.
    have := mem_imfset (fun k' => odflt y0 (getm m k')) hkd.
    by rewrite hk. }
  apply: leq_trans (fsubset_leq_size hsub) _.
  exact: size_imfset.
Qed.
