(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.denotational_rules

    Exact evaluation of stateless sampling before a continuation. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation.
#[local] Open Scope package_scope.

(** Stateless sampling leaves the continuation's heap unchanged. *)
Lemma Pr_code_bind_stateless {A B : choiceType} (c : raw_code A)
    (k0 k1 : A -> raw_code B) h :
  ValidCode emptym [interface] c ->
  (forall x, Pr_code (k0 x) h = Pr_code (k1 x) h) ->
  Pr_code (bind c k0) h = Pr_code (bind c k1) h.
Proof.
move=> hc hk.
elim: hc => /=.
- exact hk.
- by move=> [o [S T]] x k.
- by move=> l k /fhas_empty.
- by move=> l v k /fhas_empty.
- move=> o k hv ih.
  rewrite !Pr_code_sample.
  exact: eq_dlet ih.
Qed.
