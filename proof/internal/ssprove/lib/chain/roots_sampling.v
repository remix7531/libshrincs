(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.chain.roots_sampling

    Exact code normalization of re-rooted chain sampling: sample the
    independent nodes first, then apply the pure signature map. This
    strengthens the relational view in chain.ud to a code equality. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.sample_seq chain.core chain.ud.

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma sample_sig_roots_code (PP N : choice_type) w
    (F : PP -> nat -> nat -> N -> N) (d : dist N)
    pp i ds {B : choice_type} (k : chList N -> raw_code B) :
  (sg ← sample_sig_roots PP N w F d pp i ds ;; k sg) =
  (xs ← sample_seq d (size ds) ;; k (sig_map PP N w F pp i ds xs)).
Proof.
elim: ds i k => [|a ds ih] i k.
- by [].
- (* The head chain consumes one sample before the remaining chains. *)
  cbn [sample_sig_roots sample_seq size].
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  congr (bind _ _).
  apply boolp.funext => x.
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  cbn [bind sig_map].
  exact: ih.
Qed.
