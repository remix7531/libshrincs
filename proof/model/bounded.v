(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.bounded: length-bounded and exact-length lists.

    Two thin wrappers around [list A] that put a length constraint
    into the type instead of threading it as a side condition
    ([Forall]/length hypothesis) through every definition and lemma
    that touches the value: [Vec.t A n] holds exactly [n] elements
    ([SHA256]'s 32-byte output, a scheme's fixed-width seeds and
    chain state); [BList.t A max] holds at most [max] elements
    ([SHA256]'s input, which has a real, and genuinely large,
    maximum message length). Both bounds are [Z], not [nat] --
    [nat]'s unary representation makes [lia] unusable above a
    literal of about 5000 (Coq's "abstract large number" [Number
    Notation] threshold wraps bigger literals in [Nat.of_num_uint],
    which [lia]'s preprocessing does not see through; verified
    empirically). [Z] is binary, so a literal near SHA-256's actual
    2^61-byte limit costs nothing, and every scheme-level width in
    this repo is already [Z] anyway.

    Both bounds are [bool] tests, not [Prop]s, so two values built
    from the same payload list are equal regardless of which proof
    of the bound they carry ([Vec.eq]/[BList.eq], via [Eqdep_dec]
    over [bool]'s decidable equality -- no classical proof-
    irrelevance axiom needed).

    Modeled as two modules ([BList], [Vec]), mirroring how CompCert
    wraps its own bounded-representation types (e.g. [Byte], [Int]):
    a record type [t], its constructor [mk], and the operations that
    build/observe/combine it, all qualified under the module name.

    Stdlib-only, no scheme-specific vocabulary: reusable by any
    future SHRINCS scheme model, not just WOTS+C. *)

From Stdlib Require Import List Arith ZArith Lia Bool Eqdep_dec.
Import ListNotations.

(* ================================================================= *)
(** ** [BList.t A max]: at most [max] elements ([max : Z] -- can be
    genuinely large, e.g. [SHA256]'s input limit). *)

Module BList.

Record t (A : Type) (max : Z) : Type := mk {
  to_list : list A;
  wf  : Z.leb (Z.of_nat (length to_list)) max = true;
}.

Arguments mk {A max} to_list wf.
Arguments to_list {A max} _.
Arguments wf {A max} _.

Lemma eq {A : Type} {max : Z} (x y : t A max) :
  to_list x = to_list y -> x = y.
Proof.
  destruct x as [lx px], y as [ly py]; cbn; intros ->.
  f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(** Build a [BList.t] from an ordinary [Z] upper-bound proof (not
    [Z.leb]). *)
Definition of {A : Type} {max : Z} (l : list A) (pf : (Z.of_nat (length l) <= max)%Z)
  : t A max :=
  mk l (proj2 (Z.leb_le (Z.of_nat (length l)) max) pf).

Lemma length_to_list {A : Type} {max : Z} (x : t A max) :
  (Z.of_nat (length (to_list x)) <= max)%Z.
Proof. apply Z.leb_le, (wf x). Qed.

Lemma length_firstn_le {A : Type} (k : nat) (l : list A) : length (firstn k l) <= k.
Proof. rewrite length_firstn. apply Nat.le_min_l. Qed.

(** Every list, clipped to [max] elements, fits in a [BList.t] -- total
    on the input (no precondition on [l]'s own length; only [max]
    itself must be nonnegative, which every concrete bound this repo
    uses is). Used to make a [Parameter]-typed consumer like [SHA256]
    callable from plain [list A] plumbing without threading a length
    invariant through every producer: real callers never actually
    hit the clip. *)
Definition clip {A : Type} (max : Z) (hmax : (0 <= max)%Z) (l : list A) : t A max :=
  of (firstn (Z.to_nat max) l)
    (eq_ind (Z.of_nat (Z.to_nat max)) (fun k => (Z.of_nat (length (firstn (Z.to_nat max) l)) <= k)%Z)
       (proj1 (Nat2Z.inj_le _ _) (length_firstn_le (Z.to_nat max) l))
       max (Z2Nat.id max hmax)).

End BList.

(* ================================================================= *)
(** ** [Vec.t A n]: exactly [n] elements. *)

Module Vec.

Record t (A : Type) (n : Z) : Type := mk {
  to_list : list A;
  wf  : Z.eqb (Z.of_nat (length to_list)) n = true;
}.

Arguments mk {A n} to_list wf.
Arguments to_list {A n} _.
Arguments wf {A n} _.

Lemma eq {A : Type} {n : Z} (x y : t A n) :
  to_list x = to_list y -> x = y.
Proof.
  destruct x as [lx px], y as [ly py]; cbn; intros ->.
  f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

(** Build a [Vec.t] from an exact-length proof (the ergonomic entry
    point: callers prove [Z.of_nat (length l) = n] with ordinary [Z]
    reasoning, not [Z.eqb]). *)
Definition of {A : Type} {n : Z} (l : list A) (pf : Z.of_nat (length l) = n) : t A n :=
  mk l (proj2 (Z.eqb_eq (Z.of_nat (length l)) n) pf).

Lemma to_list_of {A : Type} {n : Z} (l : list A) (pf : Z.of_nat (length l) = n) :
  to_list (of l pf) = l.
Proof. reflexivity. Qed.

Lemma length_to_list {A : Type} {n : Z} (x : t A n) : Z.of_nat (length (to_list x)) = n.
Proof. apply Z.eqb_eq, (wf x). Qed.

(** Concatenate two exact-length vectors into an exact-length vector.

    Unused today (WOTS+C carries its whole tweak input as a single flat
    [block], never as a pair of [Vec.t]s); provisioned for the FXMSS /
    hypertree stateless-path expansion planned next, where a node's
    tweak input is naturally built by splicing a handful of
    fixed-length pieces (e.g. two sibling node values, or an anchor
    half plus a payload half) and wants to stay [Vec.t]-typed end to
    end rather than dropping to [list] and re-deriving the length at
    every splice. *)
Definition app {A : Type} {n1 n2 : Z} (x : t A n1) (y : t A n2)
  : t A (n1 + n2) :=
  of (to_list x ++ to_list y)
    (eq_trans (f_equal Z.of_nat (length_app (to_list x) (to_list y)))
       (eq_trans (Nat2Z.inj_add (length (to_list x)) (length (to_list y)))
          (f_equal2 Z.add (length_to_list x) (length_to_list y)))).

(** Length side-lemma for [concat] below: folding a LIST of same-length
    vectors down to plain lists and concatenating gives exactly
    [length xs] copies of the shared width [n].

    Like [app] above, unused today; provisioned for the FXMSS /
    hypertree stateless-path expansion planned next, where a
    multi-layer signature concatenates a statically-known-length list
    of same-shaped pieces (e.g. one [Vec.t] per hypertree layer) --
    exactly the shape [concat] / [length_concat_map_to_list] give. *)
Lemma length_concat_map_to_list {A : Type} {n : Z} (xs : list (t A n)) :
  Z.of_nat (length (concat (map to_list xs))) = (Z.of_nat (length xs) * n)%Z.
Proof.
  induction xs as [| x xs' IH]; [reflexivity |].
  cbn [concat map length].
  rewrite length_app, Nat2Z.inj_add, length_to_list, IH.
  rewrite Nat2Z.inj_succ. ring.
Qed.

Definition concat {A : Type} {n : Z} (xs : list (t A n)) : t A (Z.of_nat (length xs) * n)%Z :=
  of (concat (map to_list xs)) (length_concat_map_to_list xs).

End Vec.
