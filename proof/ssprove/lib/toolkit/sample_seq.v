(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.toolkit.sample_seq

    n-fold independent sampling as code, with the ValidCode instance
    package validity inference needs.  Used by every scheme's key
    generation (WOTS chain starts, FORS secrets, ...).

    Micro-test at the end of the file (see proof/STYLE.md). *)

From Sec.lib Require Import prelude.

Import PackageNotation.
#[local] Open Scope package_scope.

Section SampleSeq.

Context {A : choice_type} (d : dist A).

Fixpoint sample_seq (n : nat) : raw_code (chList A) :=
  match n with
  | 0 => ret [::]
  | n'.+1 =>
      x ← d ;;
      xs ← sample_seq n' ;;
      ret (x :: xs)
  end.

#[export] Instance sample_seq_valid (L : Locations) (I : Interface) (n : nat) :
  ValidCode L I (sample_seq n).
Proof.
elim: n => [|n IH] /=.
- apply valid_ret.
- eapply valid_bind.
  + eapply valid_scheme, prog_valid.
  + move=> x; eapply valid_bind; [exact: IH | move=> xs; apply valid_ret].
Qed.

End SampleSeq.

(* Micro-test: a package using sample_seq validates. *)
Module SampleSeqTest.

Definition TEST : nat := 990.

Definition test_pkg (d : dist 'nat) : game [interface [ TEST ] : { 'unit ~> 'list ('nat) } ] :=
  [package emptym ;
    [ TEST ] : { 'unit ~> 'list ('nat) } (_) {
      xs ← sample_seq d 5 ;;
      ret xs
    }
  ].

End SampleSeqTest.
