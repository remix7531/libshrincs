(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.sample_seq_facts

    Continuation congruence for independent list sampling. Its exact output
    length can be used without inserting an assertion or assuming the
    sampler is lossless. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.sample_seq.

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma sample_seq_congr {A B : choice_type} (d : dist A) n
    (k0 k1 : chList A -> raw_code B) :
  (forall xs, size xs = n -> k0 xs = k1 xs) ->
  (xs ← sample_seq d n ;; k0 xs) = (xs ← sample_seq d n ;; k1 xs).
Proof.
elim: n k0 k1 => [|n ih] k0 k1 hk /=.
- exact: (hk [::] erefl).
- (* Sample the head, then use the known tail length. *)
  rewrite !bind_assoc.
  congr (bind _ _).
  apply boolp.funext => x.
  rewrite !bind_assoc.
  apply: ih => xs hxs.
  apply: hk.
  by rewrite /= hxs.
Qed.
