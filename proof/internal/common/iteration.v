(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.common.iteration: list-comprehension helpers for scheme models.

    Defines the two pieces used by [model.wots] (and any future scheme
    model) to read like RFC-8391-style pseudocode:

    - [l[i]]        -- list indexing with a per-type default supplied
      through the [Default] typeclass.
    - [for_idx_dep] -- indexed list comprehension whose body receives a
      proof of its own index bound (plain function, no notation). *)

From Stdlib Require Import List PeanoNat Compare_dec Arith.Peano_dec.
Import ListNotations.

(* ================================================================= *)
(** ** List indexing via a per-type default. *)

Class Default (A : Type) := default : A.
#[global] Instance default_nat : Default nat := 0%nat.

Notation "l [ i ]" := (nth i l default)
  (at level 2, left associativity, format "l [ i ]").

(* ================================================================= *)
(** ** Dependent indexed comprehension.

    Like [for_idx], but the body receives a proof [i < k] of its own
    index bound -- so a body that builds a bound-carrying [fin] field
    (chain index [< 32], position [< 15]) can discharge the range from
    [i < k] rather than a saturating clamp.  Built over [seq 0 k]
    exactly like [for_idx]; the out-of-range branch (never reached on
    [seq 0 k]) returns the [Default].  Its [length] / [nth] lemmas are
    the only facts downstream ([correct.v], the VST loop invariants)
    consume. *)

Definition for_idx_dep {A} `{Default A} (k : nat) (f : forall i, (i < k)%nat -> A) : list A :=
  map (fun i => match lt_dec i k with
                | left  H => f i H
                | right _ => default
                end) (seq 0 k).

(** Sugar for [for_idx_dep k (fun i Hi => body)], reading like shrincs.py's
    [for i in range(k):] loops (with the index bound proof [Hi] bound
    alongside [i]). Only-parsing: the underlying term is plain
    [for_idx_dep], so every by-name lemma about it (below) is unaffected. *)
Notation "'for' i 'in' 'range' k 'as' Hi {{ body }}" :=
  (for_idx_dep k (fun i Hi => body))
  (at level 200, i ident, Hi ident, body at level 200, only parsing).

Lemma length_for_idx_dep {A} `{Default A} (k : nat) (f : forall i, (i < k)%nat -> A) :
  length (for_idx_dep k f) = k.
Proof. unfold for_idx_dep. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_for_idx_dep {A} `{Default A} (k : nat) (f : forall i, (i < k)%nat -> A)
    (d : A) (i : nat) (Hi : (i < k)%nat) :
  nth i (for_idx_dep k f) d = f i Hi.
Proof.
  unfold for_idx_dep.
  rewrite (nth_indep _ d (match lt_dec 0 k with
                          | left H => f 0%nat H | right _ => default end))
    by (rewrite length_map, length_seq; exact Hi).
  rewrite (map_nth (fun i => match lt_dec i k with
                             | left H => f i H | right _ => default end) (seq 0 k) 0%nat i).
  rewrite seq_nth by exact Hi. cbn [Nat.add].
  destruct (lt_dec i k) as [Hlt|Hlt].
  - f_equal. apply le_unique.
  - exfalso. exact (Hlt Hi).
Qed.

(** Extensionality: two dependent comprehensions with pointwise-equal
    bodies are equal.  The body-equality is at the SAME index proof, so
    consumers can reuse the [i < k] proof [for_idx_dep] handed them
    (proof-irrelevance is not needed at the call site). *)
Lemma for_idx_dep_ext {A} `{Default A} (k : nat) (f g : forall i, (i < k)%nat -> A) :
  (forall i (Hi : (i < k)%nat), f i Hi = g i Hi) -> for_idx_dep k f = for_idx_dep k g.
Proof.
  intros Hfg. unfold for_idx_dep. apply map_ext_in. intros i _.
  destruct (lt_dec i k) as [Hlt|Hlt]; [ apply Hfg | reflexivity ].
Qed.
