(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.link_forward

    Linking a program to a package that forwards every imported operation
    preserves the program. This lets contexts retain opaque batch loops. *)

From Shrincs.internal.ssprove.lib Require Import prelude.

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma code_link_forward {A : choiceType} L I (c : raw_code A)
    (p : raw_package) :
  ValidCode L I c ->
  (forall o, fhas I o -> forall x, resolve p o x = (opr o x (fun y => ret y))) ->
  code_link c p = c.
Proof.
move=> hc hp.
elim: hc => [x|o x k ho hv ih|l k hl hv ih|l v k hl hv ih|op k hv ih] /=.
- by [].
- rewrite hp // /=.
  congr (opr _ _ _).
  exact: functional_extensionality ih.
- congr (getr _ _).
  exact: functional_extensionality ih.
- by rewrite ih.
- congr (sampler _ _).
  exact: functional_extensionality ih.
Qed.
