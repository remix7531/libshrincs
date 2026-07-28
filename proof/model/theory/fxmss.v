(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Model.theory.fxmss: facts about [Model.fxmss].

    [Model.fxmss] is definitions; this is what one may CONCLUDE from
    them.  Everything here exists to let a consumer -- the FXMSS model
    bridge, and eventually a VST refinement of an FXMSS C
    implementation -- reason about the dependent node recursion
    [fx_node] without having to reproduce its bound proofs:

    - PROOF IRRELEVANCE ([fin_of_nat_pirr] ... [fx_node_pirr]): the
      dependent [fin] fields carry range PROOFS, so two calls that
      differ only in which proof they supply must be shown equal.
      [Model.fin]'s [fin_val_inj] makes that axiom-free -- no
      [proof_irrelevance], no classical reasoning.
    - UNFOLDING ([fx_node_anchorE], [fx_node_stepE]): the two branches
      of [fx_node], stated with the caller's own bound proofs rather
      than the ones the [Fixpoint] built internally.

    Companion of [Model.theory.wots] (facts about [Model.wots]) and
    [Model.theory.address]. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Export fxmss.
From Model Require Import theory.wots.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** Proof irrelevance for the dependent address fields.

    A [fin] is determined by its value ([Model.fin.fin_val_inj]), so a
    range proof never reaches the computed hash. *)

Lemma fin_of_nat_pirr (bound : Z) (k : nat) (H H' : Z.of_nat k < bound) :
  fin_of_nat bound k H = fin_of_nat bound k H'.
Proof. apply fin_val_inj. reflexivity. Qed.

Lemma fxmss_tree_adrs_pirr (nd i : nat) (H H' : Z.of_nat i < 2 ^ 64) :
  fxmss_tree_adrs nd i H = fxmss_tree_adrs nd i H'.
Proof.
  unfold fxmss_tree_adrs. now rewrite (fin_of_nat_pirr (2 ^ 64) i H H').
Qed.

Lemma fxmss_anchor_adrs_pirr (nd i : nat) (H H' : Z.of_nat i < 2 ^ 64) :
  fxmss_anchor_adrs nd i H = fxmss_anchor_adrs nd i H'.
Proof.
  unfold fxmss_anchor_adrs. now rewrite (fin_of_nat_pirr (2 ^ 64) i H H').
Qed.

Lemma fxmss_H_pirr (pk_seed : block) (nd i : nat)
    (H H' : Z.of_nat i < 2 ^ 64) (x y : block) :
  fxmss_H pk_seed nd i H x y = fxmss_H pk_seed nd i H' x y.
Proof. unfold fxmss_H. now rewrite (fxmss_tree_adrs_pirr nd i H H'). Qed.

Lemma fxmss_anchor_pirr (sk_seed pk_seed : block) (nd i : nat)
    (H H' : Z.of_nat i < 2 ^ 64) :
  fxmss_anchor sk_seed pk_seed nd i H = fxmss_anchor sk_seed pk_seed nd i H'.
Proof.
  unfold fxmss_anchor. now rewrite (fxmss_anchor_adrs_pirr nd i H H').
Qed.

(** The node recursion does not depend on which bound proofs it is
    given -- so a caller may re-derive them however it likes. *)
Lemma fx_node_pirr (sh : fxmss_shape) (sk_seed pk_seed : block) (rem nd i : nat)
    (Hd Hd' : (nd + rem <= fxmss_max_depth sh)%nat)
    (Hi Hi' : node_idx_ok sh nd i) :
  fx_node sh sk_seed pk_seed rem nd i Hd Hi
  = fx_node sh sk_seed pk_seed rem nd i Hd' Hi'.
Proof.
  revert nd i Hd Hd' Hi Hi'.
  induction rem as [|r IH]; intros nd i Hd Hd' Hi Hi'.
  - apply fxmss_anchor_pirr.
  - cbn [fx_node]. destruct (fx_anchor_dec sh i) as [Ha|Hne].
    + apply fxmss_anchor_pirr.
    + rewrite (IH (S nd) (2 * i)%nat
                (fx_depth_child nd r (fxmss_max_depth sh) Hd)
                (fx_depth_child nd r (fxmss_max_depth sh) Hd')
                (node_idx_ok_left sh nd i Hne Hi)
                (node_idx_ok_left sh nd i Hne Hi')).
      rewrite (IH (S nd) (2 * i + 1)%nat
                (fx_depth_child nd r (fxmss_max_depth sh) Hd)
                (fx_depth_child nd r (fxmss_max_depth sh) Hd')
                (node_idx_ok_right sh nd i Hne Hi)
                (node_idx_ok_right sh nd i Hne Hi')).
      apply fxmss_H_pirr.
Qed.

(* ================================================================= *)
(** ** Output widths.

    Every FXMSS value -- anchor, internal node, recovered root -- is a
    [thash] output, hence exactly [n = 16] bytes.  The model bridge
    needs this to close [decode16 o encode16 = id] at each fold step. *)

Lemma thash_length (pk_seed : block) (a : address.adrs len w_pred) (m : block) :
  length (thash pk_seed a m) = 16%nat.
Proof.
  unfold thash, trunc16. rewrite length_firstn, length_sha256'. reflexivity.
Qed.

Lemma fxmss_H_length (pk_seed : block) (nd i : nat)
    (H : Z.of_nat i < 2 ^ 64) (x y : block) :
  length (fxmss_H pk_seed nd i H x y) = 16%nat.
Proof. apply thash_length. Qed.

Lemma fxmss_anchor_length (sk_seed pk_seed : block) (nd i : nat)
    (H : Z.of_nat i < 2 ^ 64) :
  length (fxmss_anchor sk_seed pk_seed nd i H) = 16%nat.
Proof. apply thash_length. Qed.

Lemma fx_node_length (sh : fxmss_shape) (sk_seed pk_seed : block) (rem nd i : nat)
    (Hd : (nd + rem <= fxmss_max_depth sh)%nat) (Hi : node_idx_ok sh nd i) :
  length (fx_node sh sk_seed pk_seed rem nd i Hd Hi) = 16%nat.
Proof.
  revert nd i Hd Hi.
  induction rem as [|r IH]; intros nd i Hd Hi.
  - apply fxmss_anchor_length.
  - cbn [fx_node]. destruct (fx_anchor_dec sh i) as [Ha|Hne].
    + apply fxmss_anchor_length.
    + apply fxmss_H_length.
Qed.

(* ================================================================= *)
(** ** Unfolding [fx_node]. *)

(** The anchor branch: at the bottom of the tree ([rem = 0]), or at a
    position that is an anchor whatever the remaining depth (the UXMSS
    index-1 leaf). *)
Lemma fx_node_anchorE (sh : fxmss_shape) (sk_seed pk_seed : block) (rem nd i : nat)
    (Hd : (nd + rem <= fxmss_max_depth sh)%nat) (Hi : node_idx_ok sh nd i)
    (Hlt : Z.of_nat i < 2 ^ 64) :
  rem = 0%nat \/ fx_anchor_here sh i ->
  fx_node sh sk_seed pk_seed rem nd i Hd Hi = fxmss_anchor sk_seed pk_seed nd i Hlt.
Proof.
  intros [Hrem|Ha].
  - subst rem. apply fxmss_anchor_pirr.
  - destruct rem as [|r].
    + apply fxmss_anchor_pirr.
    + cbn [fx_node]. destruct (fx_anchor_dec sh i) as [Ha'|Hne].
      * apply fxmss_anchor_pirr.
      * contradiction.
Qed.

(** The internal branch, with the caller's own bound proofs. *)
Lemma fx_node_stepE (sh : fxmss_shape) (sk_seed pk_seed : block) (r nd i : nat)
    (Hd : (nd + S r <= fxmss_max_depth sh)%nat) (Hi : node_idx_ok sh nd i)
    (Hne : ~ fx_anchor_here sh i)
    (Hlt : Z.of_nat i < 2 ^ 64)
    (Hdc : (S nd + r <= fxmss_max_depth sh)%nat)
    (Hil : node_idx_ok sh (S nd) (2 * i))
    (Hir : node_idx_ok sh (S nd) (2 * i + 1)) :
  fx_node sh sk_seed pk_seed (S r) nd i Hd Hi
  = fxmss_H pk_seed nd i Hlt
      (fx_node sh sk_seed pk_seed r (S nd) (2 * i) Hdc Hil)
      (fx_node sh sk_seed pk_seed r (S nd) (2 * i + 1) Hdc Hir).
Proof.
  cbn [fx_node]. destruct (fx_anchor_dec sh i) as [Ha|Hne']; [ contradiction | ].
  rewrite (fx_node_pirr sh sk_seed pk_seed r (S nd) (2 * i)%nat
             (fx_depth_child nd r (fxmss_max_depth sh) Hd) Hdc
             (node_idx_ok_left sh nd i Hne' Hi) Hil).
  rewrite (fx_node_pirr sh sk_seed pk_seed r (S nd) (2 * i + 1)%nat
             (fx_depth_child nd r (fxmss_max_depth sh) Hd) Hdc
             (node_idx_ok_right sh nd i Hne' Hi) Hir).
  apply fxmss_H_pirr.
Qed.

(** [fx_node_stepE] with the two child INDICES supplied by the caller
    (up to the defining equations), so a consumer may name them in
    whatever already-reduced form it has -- [0] and [1] rather than
    [2 * 0] and [2 * 0 + 1], say. *)
Lemma fx_node_stepE' (sh : fxmss_shape) (sk_seed pk_seed : block)
    (r nd i il ir : nat)
    (Hd : (nd + S r <= fxmss_max_depth sh)%nat) (Hi : node_idx_ok sh nd i)
    (Hne : ~ fx_anchor_here sh i)
    (Hlt : Z.of_nat i < 2 ^ 64)
    (Hdc : (S nd + r <= fxmss_max_depth sh)%nat)
    (Hil : node_idx_ok sh (S nd) il) (Hir : node_idx_ok sh (S nd) ir)
    (Eil : il = (2 * i)%nat) (Eir : ir = (2 * i + 1)%nat) :
  fx_node sh sk_seed pk_seed (S r) nd i Hd Hi
  = fxmss_H pk_seed nd i Hlt
      (fx_node sh sk_seed pk_seed r (S nd) il Hdc Hil)
      (fx_node sh sk_seed pk_seed r (S nd) ir Hdc Hir).
Proof.
  subst il ir.
  exact (fx_node_stepE sh sk_seed pk_seed r nd i Hd Hi Hne Hlt Hdc Hil Hir).
Qed.

(* ================================================================= *)
(** ** Unfolding the verifier's walk. *)

Lemma fxmss_walk_nil (pk_seed : block) (i : nat) (node : block)
    (Hi : Z.of_nat i < 2 ^ 64) :
  fxmss_walk pk_seed i node nil Hi = node.
Proof. reflexivity. Qed.

Lemma fxmss_walk_pirr (pk_seed : block) (i : nat) (node : block) (ap : list block)
    (Hi Hi' : Z.of_nat i < 2 ^ 64) :
  fxmss_walk pk_seed i node ap Hi = fxmss_walk pk_seed i node ap Hi'.
Proof.
  revert i node Hi Hi'.
  induction ap as [|s ap' IH]; intros i node Hi Hi'; [ reflexivity | ].
  cbn [fxmss_walk].
  rewrite (IH (Nat.div2 i) _ (fxmss_walk_idx_lt i Hi) (fxmss_walk_idx_lt i Hi')).
  now rewrite (fxmss_H_pirr pk_seed (length ap') (Nat.div2 i)
                 (fxmss_walk_idx_lt i Hi) (fxmss_walk_idx_lt i Hi')).
Qed.

(** One step of the walk, with the caller's own bound proof: absorb the
    closest sibling, then continue at the parent. *)
Lemma fxmss_walk_consE (pk_seed : block) (i : nat) (node s : block)
    (ap : list block) (Hi : Z.of_nat i < 2 ^ 64)
    (Hh : Z.of_nat (Nat.div2 i) < 2 ^ 64) :
  fxmss_walk pk_seed i node (s :: ap) Hi
  = fxmss_walk pk_seed (Nat.div2 i)
      (fxmss_H pk_seed (length ap) (Nat.div2 i) Hh
         (if Nat.odd i then s else node)
         (if Nat.odd i then node else s))
      ap Hh.
Proof.
  cbn [fxmss_walk].
  rewrite (fxmss_H_pirr pk_seed (length ap) (Nat.div2 i)
             (fxmss_walk_idx_lt i Hi) Hh).
  apply fxmss_walk_pirr.
Qed.

Lemma fxmss_walk_length (pk_seed : block) (i : nat) (node : block)
    (ap : list block) (Hi : Z.of_nat i < 2 ^ 64) :
  length node = 16%nat -> length (fxmss_walk pk_seed i node ap Hi) = 16%nat.
Proof.
  revert i node Hi.
  induction ap as [|s ap' IH]; intros i node Hi hn; [ exact hn | ].
  cbn [fxmss_walk]. apply IH. apply fxmss_H_length.
Qed.
