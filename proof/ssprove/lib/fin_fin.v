(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.fin_fin: a mathcomp [finType] on [Model.fin.fin bnd].

    [Model.fin] is deliberately Stdlib-only (a Z-backed ordinal, no
    mathcomp), so this SSProve-layer shim equips [fin bnd] with the
    mathcomp [Finite] structure needed to use it as -- or inside -- a
    [choice_type] tweak space.  The instance is a clamp-free two-sided
    bijection to [ 'I_(Z.to_nat bnd) ]:

    - [f2o : fin bnd -> 'I_(Z.to_nat bnd)]  (via [Z.to_nat . fin_val])
    - [o2f : 'I_(Z.to_nat bnd) -> fin bnd]  (via [fin_of_Z . Z.of_nat . nat_of_ord])

    with cancels [f2oK]/[o2fK], transported by [Finite.copy _ (can_type
    f2oK)].  It works for ANY [bnd : Z] with a SYMBOLIC bound: [fin bnd]
    is empty when [bnd <= 0] (an inhabitant witnesses [bnd > 0] for [f2o],
    so no [0 <= bnd] hypothesis is needed), and in particular [fin (2^64)]
    is a [finType] with no [Z.to_nat (2^64)] materialization -- the ordinal
    bound stays the symbolic term, dodging the [2^64 : nat] simpl wall.
    [card_fin : #|{: fin b}| = Z.to_nat b] records the cardinality
    symbolically. *)

From HB Require Import structures.
From Sec.lib Require Import prelude.
From Model Require Import fin.
From Stdlib Require Import ZArith Lia.

(* [Finite.copy] through a bijection re-registers the lower structures
   (eqType/choice/countable) HB already knows, tripping
   [redundant-canonical-projection] both at the instance and at the
   section [End] -- inherent to the idiom (mathcomp itself builds with
   this warning off).  Scoped off around the section, restored after. *)
Set Warnings "-redundant-canonical-projection".

Section FinFin.
Variable bnd : Z.

Lemma f2o_pf (x : fin bnd) : ltn (Z.to_nat (fin_val x)) (Z.to_nat bnd).
Proof. apply/ltP. destruct (fin_range x). lia. Qed.

Definition f2o (x : fin bnd) : 'I_(Z.to_nat bnd) := Ordinal (f2o_pf x).

Lemma o2f_pf (o : 'I_(Z.to_nat bnd)) : (0 <= Z.of_nat (nat_of_ord o) < bnd)%Z.
Proof. have := ltn_ord o => /ltP ?. split; [apply Zle_0_nat | lia]. Qed.

Definition o2f (o : 'I_(Z.to_nat bnd)) : fin bnd :=
  fin_of_Z bnd (Z.of_nat (nat_of_ord o)) (o2f_pf o).

Lemma f2oK : cancel f2o o2f.
Proof.
  move=> x. apply fin_val_inj. rewrite /o2f fin_val_of_Z /f2o /=.
  destruct (fin_range x). lia.
Qed.

Lemma o2fK : cancel o2f f2o.
Proof. move=> o. apply: val_inj. rewrite /f2o /o2f /= Nat2Z.id. reflexivity. Qed.

HB.instance Definition _ := Finite.copy (fin bnd) (can_type f2oK).

End FinFin.

Set Warnings "redundant-canonical-projection".

(** The cardinality, kept symbolic ([#|fin (2^64)| = Z.to_nat (2^64)], never
    materialized). *)
Lemma card_fin (b : Z) : #|{: fin b}| = Z.to_nat b.
Proof.
  rewrite -[RHS](card_ord (Z.to_nat b)).
  apply: (bij_eq_card (f := @f2o b)).
  by exists (@o2f b); [apply f2oK | apply o2fK].
Qed.
