(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.machine: fixed-width modular integers (the [Byte] instance).

    A framework-neutral, CompCert-free clone of the core of CompCert's
    [Integers] [Make(WORDSIZE)] functor: a bounded-[Z] record with a
    total modular constructor [repr] and an [unsigned] projection,
    shaped exactly like CompCert's [Byte.int]/[Int.int] so the VST
    tree can bridge to CompCert by a trivial isomorphism, but with no
    CompCert dependency (the SSProve tree imports this too) and no
    axiom ([mkint_eq] is proved by [eq_proofs_unicity], as in
    CompCert, not by a proof-irrelevance axiom). *)

From Stdlib Require Import ZArith Lia Eqdep_dec.
#[local] Open Scope Z_scope.

(* ================================================================= *)
(** ** Parameterization by the word size, in bits. *)

Module Type WORDSIZE.
  Parameter wordsize : nat.
  Axiom wordsize_not_zero : wordsize <> 0%nat.
End WORDSIZE.

Module Make (WS : WORDSIZE).

Definition wordsize : nat := WS.wordsize.
Definition modulus : Z := 2 ^ Z.of_nat wordsize.

Lemma modulus_pos : modulus > 0.
Proof.
  unfold modulus.
  apply Z.lt_gt.
  apply Z.pow_pos_nonneg; lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Representation of machine integers. *)

(** A machine integer (type [int]) is a Coq arbitrary-precision
    integer (type [Z]) plus a proof that it lies in [[0, modulus)]. *)

Record int : Type := mkint { intval : Z ; intrange : -1 < intval < modulus }.

Definition unsigned (n : int) : Z := intval n.

Lemma repr_range : forall x : Z, -1 < x mod modulus < modulus.
Proof.
  intros x.
  generalize (Z.mod_pos_bound x modulus (Z.gt_lt _ _ modulus_pos)).
  lia.
Qed.

Definition repr (x : Z) : int := mkint (x mod modulus) (repr_range x).

(** Proof-uniqueness on [-1 < _ < modulus] (a decidable comparison),
    axiom-free: no [proof_irr], no classical reasoning. Cloned from
    CompCert's [Integers.mkint_eq]. *)
Lemma mkint_eq : forall x y Px Py, x = y -> mkint x Px = mkint y Py.
Proof.
  intros x y Px Py ->.
  assert (Hu : forall (n m : Z) (P1 P2 : n < m), P1 = P2).
  {
    unfold Z.lt.
    intros n m P1 P2.
    apply eq_proofs_unicity.
    intros c1 c2.
    destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
  }
  destruct Px as [Px1 Px2].
  destruct Py as [Py1 Py2].
  rewrite (Hu _ _ Px1 Py1).
  rewrite (Hu _ _ Px2 Py2).
  reflexivity.
Qed.

Definition eq_dec : forall x y : int, {x = y} + {x <> y}.
Proof.
  intros x y.
  destruct x as [xv xp].
  destruct y as [yv yp].
  destruct (Z.eq_dec xv yv) as [e | n].
  - left. apply mkint_eq. exact e.
  - right. intros H. injection H as H. contradiction.
Defined.

Definition eqb (x y : int) : bool := Z.eqb (unsigned x) (unsigned y).

Lemma eqb_spec : forall x y : int, reflect (x = y) (eqb x y).
Proof.
  intros x y.
  unfold eqb, unsigned.
  destruct (Z.eqb_spec (intval x) (intval y)) as [Heq | Hneq].
  - apply ReflectT. destruct x, y; cbn in Heq; apply mkint_eq; exact Heq.
  - apply ReflectF. intros ->. contradiction.
Qed.

Lemma unsigned_range : forall n : int, 0 <= unsigned n < modulus.
Proof.
  intros n.
  unfold unsigned.
  destruct n as [v p]; cbn; lia.
Qed.

Lemma unsigned_repr_eq : forall z : Z, unsigned (repr z) = z mod modulus.
Proof.
  intros z. reflexivity.
Qed.

Lemma unsigned_repr : forall z : Z, 0 <= z < modulus -> unsigned (repr z) = z.
Proof.
  intros z Hz.
  rewrite unsigned_repr_eq.
  apply Z.mod_small.
  exact Hz.
Qed.

Lemma repr_unsigned : forall n : int, repr (unsigned n) = n.
Proof.
  intros n.
  unfold repr.
  generalize (unsigned_range n); intros Hr.
  assert (Heq : unsigned n mod modulus = unsigned n) by (apply Z.mod_small; exact Hr).
  destruct n as [v p]; unfold unsigned in *; cbn in *.
  apply mkint_eq.
  exact Heq.
Qed.

(** [unsigned] is injective: two machine integers with the same
    unsigned value are equal (the canonical-representative fact, via
    [mkint_eq]; axiom-free). *)
Lemma unsigned_inj : forall x y : int, unsigned x = unsigned y -> x = y.
Proof.
  intros [xv xp] [yv yp] H.
  unfold unsigned in H; cbn in H; subst yv.
  apply mkint_eq; reflexivity.
Qed.

Definition zero : int := repr 0.

End Make.

(* ================================================================= *)
(** ** Concrete instances: [Byte] (8-bit). *)

Module Wordsize_8.
  Definition wordsize := 8%nat.
  Lemma wordsize_not_zero : wordsize <> 0%nat.
  Proof. discriminate. Qed.
End Wordsize_8.
Module Byte := Make Wordsize_8.
(** [Byte] is the only instance the proofs need; the [Make] functor is
    kept general (the VST tree bridges its shape to CompCert's
    [Integers]). *)
