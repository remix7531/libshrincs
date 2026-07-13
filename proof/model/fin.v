(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.fin: [fin bound], the Z-bounded ordinal (reachable-states scalar).

    A [fin bound] is a Coq integer ([Z]) paired with a proof that it
    lies in [[0, bound)].  It is the model's "reachable-states" scalar:
    every ADRS field is a [fin] at its spec-tight bound (chain [< 32],
    position [< 15], node height [< 256], node index [< 2^64], ...), so
    illegal field values are unrepresentable and field/tweak
    injectivity is intrinsic.

    Two design points, contrasted with the neighbours it replaces:

    - The bound is a [Z], NOT a [nat].  Stdlib's [Vectors.Fin.t] is
      [nat]-indexed and unary, so a bound near [2^64] is uncomputable
      ([2^64 : nat] does not even reduce, and [lia] cannot prove a
      [nat] bound that large).  With a [Z] bound, [fin (2^64)] costs
      nothing and [lia] discharges every range obligation.

    - The constructor CARRIES the range proof; it does not truncate.
      [model.machine]'s modular [int] builds a field with [repr], which
      wraps mod a power of two, so inverting a field equality needs a
      [< modulus] side condition ([machine.*.repr] is only injective
      in range).  Here [mk_fin] takes the [Z] together with its bound,
      so two [fin]s with the same [val] are equal ([fin_eq], axiom-free
      via [eq_proofs_unicity], exactly as CompCert's [mkint_eq]) and
      distinct indices give distinct [fin]s UNCONDITIONALLY -- which is
      what makes address/tweak injectivity free with no range premises.

    Modeled on [model.machine]'s [int]: same proof-uniqueness argument,
    same flat-name API convention as [model.byte] (so no [Fin.]-qualified
    name can collide with Stdlib's [Vectors.Fin]).  Stdlib-only, no
    scheme vocabulary: reusable by any SHRINCS scheme model. *)

From Stdlib Require Import ZArith Lia Eqdep_dec.
#[local] Open Scope Z_scope.

(* ================================================================= *)
(** ** [fin bound]: a [Z] in [[0, bound)].

    The range is stored as [-1 < val < bound] (two strict [<], matching
    [machine.int]) rather than [0 <= val < bound]: strict [<] on [Z] has
    the clean [eq_proofs_unicity] proof-uniqueness used by [fin_eq]. *)

Record fin (bound : Z) : Type := mk_fin {
  fin_val : Z ;
  fin_val_range : -1 < fin_val < bound ;
}.

Arguments mk_fin {bound} fin_val fin_val_range.
Arguments fin_val {bound} _.
Arguments fin_val_range {bound} _.

(** Proof-uniqueness on [-1 < _ < bound] (a decidable comparison),
    axiom-free: no [proof_irr], no classical reasoning. Cloned from
    [machine]'s [mkint_eq]. *)
Lemma mk_fin_eq (bound : Z) :
  forall x y Px Py, x = y -> @mk_fin bound x Px = @mk_fin bound y Py.
Proof.
  intros x y Px Py ->.
  assert (Hu : forall (n m : Z) (P1 P2 : n < m), P1 = P2).
  {
    unfold Z.lt.
    intros n m P1 P2.
    apply eq_proofs_unicity.
    intros c1 c2. destruct c1; destruct c2; (left; reflexivity) || (right; congruence).
  }
  destruct Px as [Px1 Px2]. destruct Py as [Py1 Py2].
  rewrite (Hu _ _ Px1 Py1). rewrite (Hu _ _ Px2 Py2). reflexivity.
Qed.

(** [fin_val] is injective: equal underlying integers give equal
    ordinals (the canonical-representative fact; axiom-free). *)
Lemma fin_val_inj {bound : Z} (x y : fin bound) : fin_val x = fin_val y -> x = y.
Proof.
  destruct x as [xv xp], y as [yv yp]; cbn; intros ->.
  apply mk_fin_eq; reflexivity.
Qed.

(** The range, as an ordinary [0 <= _ < bound] fact. *)
Lemma fin_range {bound : Z} (x : fin bound) : 0 <= fin_val x < bound.
Proof. destruct x as [v [p1 p2]]; cbn; lia. Qed.

Definition fin_eq_dec {bound : Z} : forall x y : fin bound, {x = y} + {x <> y}.
Proof.
  intros [xv xp] [yv yp]. destruct (Z.eq_dec xv yv) as [e | n].
  - left. apply mk_fin_eq. exact e.
  - right. intros H. injection H as H. contradiction.
Defined.

Definition fin_eqb {bound : Z} (x y : fin bound) : bool := Z.eqb (fin_val x) (fin_val y).

Lemma fin_eqb_spec {bound : Z} (x y : fin bound) : reflect (x = y) (fin_eqb x y).
Proof.
  unfold fin_eqb. destruct (Z.eqb_spec (fin_val x) (fin_val y)) as [e | n].
  - apply ReflectT, fin_val_inj, e.
  - apply ReflectF. intros ->. apply n. reflexivity.
Qed.

(* ================================================================= *)
(** ** Smart constructors.

    [fin_of_Z]/[fin_of_nat] build a [fin] from a value plus an ordinary
    [0 <= _ < bound] / [_ < bound] proof, preserving the value exactly
    ([fin_val (fin_of_* ...) = ...] holds definitionally): no truncation,
    unlike [machine.*.repr]. *)

Definition fin_of_Z (bound v : Z) (H : 0 <= v < bound) : fin bound :=
  mk_fin v (conj (proj1 (Z.le_succ_l (-1) v) (proj1 H)) (proj2 H)).

Lemma fin_val_of_Z (bound v : Z) (H : 0 <= v < bound) : fin_val (fin_of_Z bound v H) = v.
Proof. reflexivity. Qed.

Definition fin_of_nat (bound : Z) (n : nat) (H : Z.of_nat n < bound) : fin bound :=
  fin_of_Z bound (Z.of_nat n) (conj (Zle_0_nat n) H).

Lemma fin_val_of_nat (bound : Z) (n : nat) (H : Z.of_nat n < bound) :
  fin_val (fin_of_nat bound n H) = Z.of_nat n.
Proof. reflexivity. Qed.


(* ================================================================= *)
(** ** Injectivity of the smart constructors (free -- no range side
    conditions beyond the bounds already carried by the arguments). *)

Lemma fin_of_Z_inj (bound v v' : Z) (H : 0 <= v < bound) (H' : 0 <= v' < bound) :
  fin_of_Z bound v H = fin_of_Z bound v' H' -> v = v'.
Proof.
  intros E. apply (f_equal fin_val) in E. rewrite !fin_val_of_Z in E. exact E.
Qed.

Lemma fin_of_nat_inj (bound : Z) (n m : nat) (H : Z.of_nat n < bound) (H' : Z.of_nat m < bound) :
  fin_of_nat bound n H = fin_of_nat bound m H' -> n = m.
Proof.
  intros E. apply (f_equal fin_val) in E. rewrite !fin_val_of_nat in E.
  apply Nat2Z.inj. exact E.
Qed.

(** NOTE: the model deliberately has NO saturating totalizer.  A TOTAL
    [Z -> fin] clamp used to live here (and briefly at the SSProve tweak
    boundary); the zero-clamp refactor deleted it everywhere.  The
    reachable-states model is now EXACT -- every [fin] field is built
    from a bound proof (via [fin_of_Z] / [fin_of_nat]), so a construct
    that saturates out-of-range inputs is not part of the model's
    vocabulary.  The one residual total adapter, at the SSProve
    abstract-scheme boundary where a bare [nat] index arrives
    ([Sec.addressing]'s [shrincs_wots_chain_adrs_tot]), is a
    [Bool.bool_dec] exact-in-range / dummy-out-of-range wrapper -- NOT a
    clamp: it never truncates, and its out-of-range branch is a distinct
    unused address that is provably never reached.  [Model.fin] is now
    pristine exact-ordinal algebra. *)
