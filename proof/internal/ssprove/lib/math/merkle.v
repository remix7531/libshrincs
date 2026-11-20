(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.merkle

    Merkle-tree evaluation, authentication paths and forgery analysis
    over trees of arbitrary shape, with root-to-node paths as tweaks.
    Honest anchors may sit at any depth. A verifying forgery yields one
    of four outcomes: a two-child hash collision at an internal position
    ([FColl]), a forged internal node hashing into an honest anchor
    ([FEscape]), a forged anchor at an honest internal position ([FShort]),
    or an exact anchor match ([FAnchor]). The two structure mismatches
    yield paired-tweak witnesses; an anchor match passes the forgery to
    the leaf scheme.

    The node hash [h] takes the absolute position as tweak. Consumers
    compose it from a tweakable hash and an injective address map.
    Pure MathComp; no SSProve imports. *)

From mathcomp Require Import boot order.

From Shrincs.internal.ssprove.lib.math Require Import bin_tree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section Merkle.

Context {A : eqType}.

(** Node hash, tweaked by the absolute position of the computed node. *)
Variable h : seq bool -> A -> A -> A.

(* ------------------------------------------------------------------ *)
(** ** Evaluation, authentication paths, verification *)

(** Value of tree [t] whose root sits at absolute position [pos].
    Anchors ([BLeaf]) carry their value directly. *)
Fixpoint val_bt (pos : seq bool) (t : bt A) : A :=
  match t with
  | BLeaf a => a
  | BNode l r => h pos (val_bt (rcons pos false) l) (val_bt (rcons pos true) r)
  end.

(** Authentication path for the node at relative path [p] below
    [pos]: sibling VALUES, top-down. [None] if [p] exits the tree. *)
Fixpoint cons_ap (pos : seq bool) (t : bt A) (p : seq bool)
    {struct p} : option (seq A) :=
  match p, t with
  | [::], _ => Some [::]
  | b :: p', BNode l r =>
      omap (cons (val_bt (rcons pos (~~ b)) (if b then l else r)))
           (cons_ap (rcons pos b) (if b then r else l) p')
  | _ :: _, BLeaf _ => None
  end.

(** Verifier: recompute the value at [pos] from the anchor value [a]
    claimed at relative path [p] below [pos], using sibling values
    [ap] (top-down).  [None] on length mismatch. *)
Fixpoint val_ap (pos : seq bool) (p : seq bool) (ap : seq A) (a : A)
    {struct p} : option A :=
  match p, ap with
  | [::], [::] => Some a
  | b :: p', s :: ap' =>
      omap (fun c => if b then h pos s c else h pos c s)
           (val_ap (rcons pos b) p' ap' a)
  | _, _ => None
  end.

Lemma size_cons_ap pos t p ap : cons_ap pos t p = Some ap -> size ap = size p.
Proof.
elim: p pos t ap => [|b p ih] pos [a|l r] ap //=; first by case=> <-.
- by case=> <-.
- case e: cons_ap => [ap'|] //= [<-] /=.
  by rewrite (ih _ _ _ e).
Qed.

(** An authentication path exists exactly when the path stays inside
    the tree. *)
Lemma isSome_cons_ap pos t p :
  isSome (cons_ap pos t p) = isSome (subtree_at t p).
Proof.
elim: p pos t => [//|b p ih] pos [a|l r] //=.
case: b => /=.
- by rewrite -(ih (rcons pos true) r); case: cons_ap.
- by rewrite -(ih (rcons pos false) l); case: cons_ap.
Qed.

(** Correctness: the honest authentication path for any node of the
    tree verifies to the tree's root value. *)
Lemma val_ap_correct pos t p ap u :
  cons_ap pos t p = Some ap ->
  subtree_at t p = Some u ->
  val_ap pos p ap (val_bt (pos ++ p) u) = Some (val_bt pos t).
Proof.
elim: p pos t ap => [|b p ih] pos [a|l r] ap //=.
- by case=> <- [<-]; rewrite cats0.
- by case=> <- [<-]; rewrite cats0.
- case e: cons_ap => [ap'|] //= [<-] hsub /=.
  by rewrite -cat_rcons (ih _ _ _ e hsub); case: b {e hsub}.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Forgery analysis *)

(** Outcome of comparing a verifying (anchor, path, auth-path) triple
    against the honest tree. *)
Variant fcase : Type :=
  | FColl   of seq bool & (A * A) & (A * A)
    (** [FColl q x y]: hash collision at internal position [q] of the
        honest tree: [h q x.1 x.2 = h q y.1 y.2], [x != y], where [y]
        are the honest children values at [q]. *)
  | FEscape of seq bool & (A * A) & A
    (** [FEscape q x a0]: the forged path runs THROUGH position [q]
        at which the honest tree has an anchor of value [a0], and the
        forged node value at [q] -- computed as [h q x.1 x.2] -- equals
        [a0].  In SHRINCS the honest [a0] is not an output of [h q]
        (anchors are compressed WOTS+C keys under a different address
        type), so this feeds the TCR-exclusive game. *)
  | FShort  of seq bool & A
    (** [FShort q a]: the forged path ENDS at position [q] where the
        honest tree has an internal node, and the forged anchor value
        [a] equals the honest [h q]-output there.  Mirror image of
        [FEscape] for the TCR-exclusive game. *)
  | FAnchor
    (** The forged path ends exactly at an honest anchor with equal
        value: the forgery must break the anchor (leaf) scheme. *).

(** Forgery classifier.  Total function; the spec lemma [extractP]
    characterizes its output under the verification invariant. *)
Fixpoint extract (pos : seq bool) (t : bt A) (p : seq bool) (ap : seq A)
    (a : A) {struct p} : fcase :=
  match p, ap, t with
  | [::], _, BLeaf _ => FAnchor
  | [::], _, BNode _ _ => FShort pos a
  | b :: p', s :: ap', BLeaf a0 =>
      if val_ap (rcons pos b) p' ap' a is Some c
      then FEscape pos (if b then (s, c) else (c, s)) a0
      else FAnchor (* unreachable under the invariant *)
  | b :: p', s :: ap', BNode l r =>
      let y := (val_bt (rcons pos false) l, val_bt (rcons pos true) r) in
      if val_ap (rcons pos b) p' ap' a is Some c
      then
        let x := if b then (s, c) else (c, s) in
        if x == y
        then extract (rcons pos b) (if b then r else l) p' ap' a
        else FColl pos x y
      else FAnchor (* unreachable *)
  | _ :: _, [::], _ => FAnchor (* unreachable *)
  end.

(** Specification of [extract]'s outcomes.  All positions are
    reported in absolute form [pos ++ q] with [q] a position of the
    honest tree [t], so consumers can relate them to committed
    targets via [subtree_at]/[internal_pathsP]. *)
Definition extract_ok (pos : seq bool) (t : bt A) (p : seq bool) (a : A)
    (fc : fcase) : Prop :=
  match fc with
  | FColl q x y =>
      exists qrel l r,
        [/\ q = pos ++ qrel,
            subtree_at t qrel = Some (BNode l r),
            y = (val_bt (rcons q false) l, val_bt (rcons q true) r),
            h q x.1 x.2 = h q y.1 y.2 & x <> y]
  | FEscape q x a0 =>
      exists qrel,
        [/\ q = pos ++ qrel,
            subtree_at t qrel = Some (BLeaf a0) &
            h q x.1 x.2 = a0]
  | FShort q a' =>
      exists l r,
        [/\ q = pos ++ p, a' = a,
            subtree_at t p = Some (BNode l r) &
            a = val_bt q (BNode l r)]
  | FAnchor => subtree_at t p = Some (BLeaf a)
  end.

Lemma extractP pos t p ap a :
  val_ap pos p ap a = Some (val_bt pos t) ->
  extract_ok pos t p a (extract pos t p ap a).
Proof.
elim: p pos t ap => [|b p ih] pos [a0|l r] ap /=.
- (* p = [::], honest anchor *)
  by case: ap => [|s ap'] //= [->].
- (* p = [::], honest internal node *)
  case: ap => [|s ap'] //= [ha].
  by exists l, r; rewrite cats0.
- (* p = b :: p', honest anchor: escape *)
  case: ap => [|s ap'] //=.
  case: (val_ap (rcons pos b) p ap' a) => [c|] //= [hv].
  exists [::]; rewrite cats0; split=> //.
  by case: b hv => /=.
- (* p = b :: p', honest internal node *)
  case: ap => [|s ap'] //=.
  case e: (val_ap (rcons pos b) p ap' a) => [c|] //= [hv].
  case: eqP => [hx|hx] /=; last first.
  + (* Collision at this position. *)
    exists [::], l, r; rewrite cats0; split=> //.
    by clear e hx; case: b hv => /=.
  + (* Children agree: recurse on the side of the path. *)
    have hc : val_ap (rcons pos b) p ap' a
              = Some (val_bt (rcons pos b) (if b then r else l)).
    { rewrite e; clear e; congr Some.
      by case: b hv hx => /= _ [h1 h2]; [rewrite h2 | rewrite h1]. }
    clear e hv hx c s.
    have {ih hc} := ih (rcons pos b) (if b then r else l) ap' hc.
    case: (extract _ _ _ _ _) => [q x y|q x a1|q a'|] /=.
    * (* Lift the internal collision position through this edge. *)
      move=> [qrel [l' [r' [hq hsub hy hcol hne]]]].
      by exists (b :: qrel), l', r'; split=> //; rewrite hq cat_rcons.
    * (* Lift the escape position through this edge. *)
      move=> [qrel [hq hsub hh]].
      by exists (b :: qrel); split=> //; rewrite hq cat_rcons.
    * (* Lift the short-path witness through this edge. *)
      move=> [l' [r' [hq ha' hsub hval]]].
      by exists l', r'; split=> //; rewrite hq cat_rcons.
    * by [].
Qed.

End Merkle.
