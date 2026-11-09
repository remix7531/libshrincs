(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.repr.seqlist: mathcomp [seq] against stdlib [list]

    Both libraries are in scope in every proof of this tier, and they
    name the same operations differently. This file is the dictionary
    between them, and nothing in it mentions C or sha256 --
    it is only [seq] on one side and [list]/[Zlength]/[sublist] on the
    other.

    Kept separate from [repr.words] because it is what makes a floyd
    tactic apply to a mathcomp term at all: [list_solve] and
    [list_simplify] know [app], [firstn], [skipn] and [Zlength], while
    the specification is written in [cat], [take], [drop] and [size].
    Every proof in the tier crosses that boundary; only some of them
    touch bytes. *)

From Vst Require Export base.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

(* ================================================================= *)
(** ** seq/list bridges

    The merged import stack gives one list type two vocabularies:
    mathcomp's ([size], [take], [drop], [nth], [cat], [nseq],
    [seq.map]) and the one every VST list lemma is stated in (Stdlib's
    [length], [firstn], [skipn], [List.nth], [List.app], [List.repeat],
    [List.map], plus floyd's [Z]-indexed [Zlength], [Znth], [sublist]).
    Each pair names the same function on the same type, so every bridge
    below is one unfolding. They are collected here, and not in a
    sha256-specific file, because nothing in them is about sha256. *)

(* mathcomp's [size] and Stdlib's [length] are the same fixpoint on the
   same type (seq = list); this bridge lets Zlength facts consume
   [bytes_of_word_size]. *)
Lemma size_length {T : Type} (l : seq T) : size l = length l.
Proof. induction l as [|x l IH]; simpl; congruence. Qed.

Lemma nth_seq_list {A : Type} (d : A) (l : seq A) (k : nat) :
  nth d l k = List.nth k l d.
Proof.
revert k.
induction l as [|x l IH].
- (* the empty list: both spellings return the default *)
  intros [|k].
  + reflexivity.
  + reflexivity.
- (* cons: index 0 is the head, a successor index recurses *)
  intros [|k].
  + reflexivity.
  + apply IH.
Qed.

Lemma map_seq_list {A B : Type} (f : A -> B) (l : seq A) :
  List.map f l = [seq f x | x <- l].
Proof.
induction l as [|x l IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma size_map_list {A B : Type} (f : A -> B) (l : list A) :
  size (List.map f l) = size l.
Proof.
induction l as [|x l IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma catE {A : Type} (l1 l2 : seq A) : List.app l1 l2 = cat l1 l2.
Proof.
induction l1 as [|x l1 IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma repeatE {A : Type} (x : A) (k : nat) : List.repeat x k = nseq k x.
Proof.
induction k as [|k IH].
- reflexivity.
- simpl.
  rewrite IH.
  reflexivity.
Qed.

Lemma take_firstn {A : Type} (m : nat) (l : seq A) : take m l = firstn m l.
Proof.
revert l.
induction m as [|m IH].
- (* a zero-width take is empty on either spelling *)
  intros [|x l].
  + reflexivity.
  + reflexivity.
- intros [|x l].
  + reflexivity.
  + simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma drop_skipn {A : Type} (m : nat) (l : seq A) : drop m l = skipn m l.
Proof.
revert l.
induction m as [|m IH].
- (* dropping nothing is the identity on either spelling *)
  intros [|x l].
  + reflexivity.
  + reflexivity.
- intros [|x l].
  + reflexivity.
  + apply IH.
Qed.

(* ---------- the same, [Z]-indexed: floyd counts in [Z] ---------- *)

Lemma Zlength_size {A : Type} (l : list A) : Zlength l = Z.of_nat (size l).
Proof.
rewrite Zlength_correct.
now rewrite size_length.
Qed.

(* A [sublist] of known width is a [take] of a [drop]: the shape the
   model states every windowed read in, and the one place the two
   index conventions have to be reconciled by hand. *)
Lemma sublist_take_drop {A : Type} (lo m : Z) (l : seq A) :
  0 <= lo -> 0 <= m -> sublist lo (lo + m) l = take (Z.to_nat m) (drop (Z.to_nat lo) l).
Proof.
intros Hlo Hm.
unfold sublist.
(* restate floyd's two cuts in the mathcomp vocabulary *)
rewrite <- take_firstn.
rewrite <- drop_skipn.
(* [take_drop] wants the two widths summed in the mathcomp order *)
assert (Hwidth : Z.to_nat (lo + m) = (Z.to_nat m + Z.to_nat lo)%nat).
{ rewrite <- plusE.
  lia. }
rewrite Hwidth.
rewrite take_drop.
reflexivity.
Qed.

Lemma sublist_0_take {A : Type} (n : Z) (l : seq A) :
  0 <= n -> sublist 0 n l = take (Z.to_nat n) l.
Proof.
intros Hn.
(* the [lo = 0] instance of the take-of-drop shape *)
rewrite (sublist_take_drop 0 n l ltac:(lia) ltac:(lia)).
rewrite drop0.
reflexivity.
Qed.

(* The only window any of these proofs cuts: the C reads and writes
   32-bit words, so every [sublist] it takes is four bytes wide at a
   4-byte offset. Floyd states that window with [sublist] over [Z]
   indices and the model states it with [take]/[drop] over [nat] ones,
   so both offsets need casting; doing it once here keeps the cast out
   of the three call sites (sha256_parse, and both directions of
   compress). *)
Lemma sublist_word4 {A : Type} (i : Z) (l : seq A) :
  0 <= i -> sublist (4 * i) (4 * i + 4) l = take 4 (drop (4 * Z.to_nat i) l).
Proof.
intros Hi.
rewrite (sublist_take_drop (4 * i) 4 l ltac:(lia) ltac:(lia)).
(* the seq side indexes in [nat], so both offsets need casting *)
assert (Hw : Z.to_nat 4 = 4%nat) by reflexivity.
rewrite Hw.
assert (Hoff : Z.to_nat (4 * i) = (4 * Z.to_nat i)%nat).
{ rewrite <- multE.
  lia. }
rewrite Hoff.
reflexivity.
Qed.
