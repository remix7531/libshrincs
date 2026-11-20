(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.heap_observe

    Observable equality of typed heaps suffices for output distributions.
    Explicitly storing a location's default need not preserve the raw map. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp Require Import reals distr realsum.

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma heap_location_unique L (l l' : Location) :
  fhas L l -> fhas L l' -> l.1 = l'.1 -> l = l'.
Proof.
case: l => n v; case: l' => n' v' /=.
move=> h h' he. subst n'.
move: h h'; rewrite /fhas => -> [<-]. by [].
Qed.

Definition heap_observe (L : Locations) (h h' : heap) : Prop :=
  forall l, fhas L l -> get_heap h l = get_heap h' l.

Lemma heap_observe_put L h h' l v :
  heap_observe L h h' -> fhas L l ->
  heap_observe L (set_heap h l v) (set_heap h' l v).
Proof.
move=> he hl l' hl'.
case: (eqVneq l'.1 l.1) => hn.
- have -> := heap_location_unique L l' l hl' hl hn.
  by rewrite !get_set_heap_eq.
- rewrite !get_set_heap_neq //; exact: he.
Qed.

Lemma Pr_code_heap_observe L I {T : choiceType} (c : raw_code T)
    (vc : ValidCode L I c) : forall h h', heap_observe L h h' ->
  dfst (Pr_code c h) = dfst (Pr_code c h').
Proof.
induction vc as [a | o x k ho hk ih | lo k hl hk ih |
  lo v k hl hk ih | op k hk ih]; move=> h h' he.
- by apply/distr_ext => z; rewrite !Pr_code_ret !dmargin_dunit.
- by rewrite !Pr_code_call.
- rewrite !Pr_code_get (he _ hl). exact: ih.
- rewrite !Pr_code_put. apply: ih. exact: heap_observe_put he hl.
- rewrite !Pr_code_sample !dfst_dlet_commut. apply: eq_dlet => x. exact: ih.
Qed.

Lemma heap_observe_initial L lo : fhas L lo ->
  heap_observe L (set_heap empty_heap lo (heap_init lo)) empty_heap.
Proof.
move=> hl l hl'.
case: (eqVneq l.1 lo.1) => hn.
- have -> := heap_location_unique L l lo hl' hl hn.
  by rewrite get_set_heap_eq get_empty_heap.
- by rewrite get_set_heap_neq.
Qed.
