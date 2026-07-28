(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * HBS.math.bin_tree

    Binary trees of arbitrary shape, with positions given as
    root-to-node paths of booleans ([false] = left child).

    Counterpart of [resources/FV-SPHINCSPLUS-EC/proofs/BinaryTrees.ec],
    generalized: no balancedness assumption.  SHRINCS's unbalanced
    UXMSS tree (xmss.tex, "UXMSS") is a right-skewed spine; its
    verifier embeds any actual tree into an imaginary balanced tree of
    declared height and addresses nodes by (height, index) positions in
    that embedding.  We therefore also provide the conversions between
    (length, index) pairs and paths, proved once here and reused by
    HBS.math.MerkleBalanced / HBS.math.MerkleSkewed.

    Pure MathComp; no SSProve imports (see docs/STYLE.md rule 5). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HB Require Import structures.
From mathcomp Require Import all_boot all_order.
Set Warnings "notation-overridden,ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------ *)
(** ** Trees *)

Section BinTreeDef.

Context {A : Type}.

Inductive bt : Type :=
  | BLeaf of A
  | BNode of bt & bt.

(** Depth of the deepest leaf. *)
Fixpoint bt_depth (t : bt) : nat :=
  if t is BNode l r then (maxn (bt_depth l) (bt_depth r)).+1 else 0.

(** Number of leaves. *)
Fixpoint bt_nleaves (t : bt) : nat :=
  if t is BNode l r then bt_nleaves l + bt_nleaves r else 1.

(** Subtree at a position; [None] if the path exits the tree. *)
Fixpoint subtree_at (t : bt) (p : seq bool) {struct p} : option bt :=
  match p, t with
  | [::], _ => Some t
  | b :: p', BNode l r => subtree_at (if b then r else l) p'
  | _ :: _, BLeaf _ => None
  end.

Definition leaf_at (t : bt) (p : seq bool) : option A :=
  if subtree_at t p is Some (BLeaf a) then Some a else None.

(** Positions of all leaves, root-to-leaf, left to right. *)
Fixpoint leaf_paths (t : bt) : seq (seq bool) :=
  if t is BNode l r
  then [seq false :: p | p <- leaf_paths l] ++ [seq true :: p | p <- leaf_paths r]
  else [:: [::] ].

(** Positions of all internal nodes, root first. *)
Fixpoint internal_paths (t : bt) : seq (seq bool) :=
  if t is BNode l r
  then [::] :: ([seq false :: q | q <- internal_paths l]
                ++ [seq true :: q | q <- internal_paths r])
  else [::].

Lemma subtree_at_nil t : subtree_at t [::] = Some t.
Proof. by []. Qed.

Lemma subtree_at_cons l r b p :
  subtree_at (BNode l r) (b :: p) = subtree_at (if b then r else l) p.
Proof. by []. Qed.

Lemma subtree_at_cat t p q :
  subtree_at t (p ++ q) = obind (subtree_at ^~ q) (subtree_at t p).
Proof.
by elim: p t => [//|b p IH] [a|l r] //=.
Qed.

Lemma size_leaf_paths t : size (leaf_paths t) = bt_nleaves t.
Proof. by elim: t => [//|l IHl r IHr] /=; rewrite size_cat !size_map IHl IHr. Qed.

Lemma leaf_paths_correct t p : p \in leaf_paths t -> leaf_at t p <> None.
Proof.
elim: t p => [a|l IHl r IHr] p /=.
  by rewrite inE => /eqP ->.
rewrite mem_cat => /orP[] /mapP[q hq ->]; rewrite /leaf_at /=.
- exact: IHl.
- exact: IHr.
Qed.

Lemma internal_pathsP t q l r :
  subtree_at t q = Some (BNode l r) -> q \in internal_paths t.
Proof.
elim: q t => [|b q IH] [a|tl tr] //=.
case: b => h; rewrite inE mem_cat; apply/orP; right; apply/orP.
- by right; apply/mapP; exists q; first exact: IH h.
- by left; apply/mapP; exists q; first exact: IH h.
Qed.

(** A leaf path never exceeds the tree depth. *)
Lemma leaf_at_size t p a : leaf_at t p = Some a -> size p <= bt_depth t.
Proof.
elim: t p => [b|l IHl r IHr] [|[] p] //=; rewrite /leaf_at /=.
- by move/IHr=> hp; rewrite ltnS leq_max hp orbT.
- by move/IHl=> hp; rewrite ltnS leq_max hp.
Qed.

End BinTreeDef.

Arguments bt : clear implicits.

(* ------------------------------------------------------------------ *)
(** ** Mapping over trees *)

Section BinTreeMap.

Context {A B : Type} (f : A -> B).

Fixpoint bt_map (t : bt A) : bt B :=
  match t with
  | BLeaf a => BLeaf (f a)
  | BNode l r => BNode (bt_map l) (bt_map r)
  end.

Lemma bt_depth_map t : bt_depth (bt_map t) = bt_depth t.
Proof. by elim: t => [//|l IHl r IHr] /=; rewrite IHl IHr. Qed.

Lemma subtree_at_map t p :
  subtree_at (bt_map t) p = omap bt_map (subtree_at t p).
Proof. by elim: p t => [//|b p IH] [a|l r] //=; case: b; rewrite IH. Qed.

Lemma leaf_at_map t p : leaf_at (bt_map t) p = omap f (leaf_at t p).
Proof.
by rewrite /leaf_at subtree_at_map; case: (subtree_at t p) => [[a|l r]|].
Qed.

End BinTreeMap.

(* ------------------------------------------------------------------ *)
(** ** Decidable equality *)

Section BinTreeEq.

Context {A : eqType}.

Fixpoint eq_bt (t1 t2 : bt A) : bool :=
  match t1, t2 with
  | BLeaf a1, BLeaf a2 => a1 == a2
  | BNode l1 r1, BNode l2 r2 => eq_bt l1 l2 && eq_bt r1 r2
  | _, _ => false
  end.

Lemma eq_btP : Equality.axiom eq_bt.
Proof.
elim=> [a1|l1 IHl r1 IHr] [a2|l2 r2] /=; try by constructor.
- by apply: (iffP eqP) => [-> | [->]].
- apply: (iffP andP).
  + by case=> h1 h2; rewrite (elimT (IHl l2) h1) (elimT (IHr r2) h2).
  + by case=> <- <-; split; [apply/IHl | apply/IHr].
Qed.

HB.instance Definition _ := hasDecEq.Build (bt A) eq_btP.

End BinTreeEq.

(* ------------------------------------------------------------------ *)
(** ** Positions: (length, index) <-> path conversions

    In an imaginary balanced tree of height [h], the node at height
    [z] and horizontal index [i] (with [i < 2 ^ (h - z)]) is reached
    from the root by the path of length [l = h - z] whose bits are the
    binary digits of [i], most significant first.  We work with the
    path length [l] here; consumers translate height to length. *)

(** Least-significant-bit-first digits of [i], padded/truncated to
    length [l]. *)
Fixpoint bits_lsb (l i : nat) : seq bool :=
  if l is l'.+1 then odd i :: bits_lsb l' i./2 else [::].

(** Path (MSB first) of length [l] for horizontal index [i]. *)
Definition path_of_idx (l i : nat) : seq bool := rev (bits_lsb l i).

Fixpoint idx_of_lsb (s : seq bool) : nat :=
  if s is b :: s' then b + (idx_of_lsb s').*2 else 0.

(** Horizontal index of a path (MSB first). *)
Definition idx_of_path (p : seq bool) : nat := idx_of_lsb (rev p).

Lemma size_bits_lsb l i : size (bits_lsb l i) = l.
Proof. by elim: l i => [//|l IH] i /=; rewrite IH. Qed.

Lemma size_path_of_idx l i : size (path_of_idx l i) = l.
Proof. by rewrite /path_of_idx size_rev size_bits_lsb. Qed.

Lemma idx_of_lsb_bits l i : idx_of_lsb (bits_lsb l i) = i %% 2 ^ l.
Proof.
elim: l i => [|l IH] i /=; first by rewrite expn0 modn1.
rewrite IH -divn2 expnSr.
rewrite [in X in _ = X](divn_eq i 2) -modnDml -muln_modl.
have hlt : (i %/ 2) %% 2 ^ l * 2 + i %% 2 < 2 ^ l * 2.
  apply: leq_trans (_ : ((i %/ 2) %% 2 ^ l).+1 * 2 <= 2 ^ l * 2).
  - by rewrite mulSn addnC ltn_add2r ltn_pmod.
  - by rewrite leq_mul2r ltn_pmod ?expn_gt0 ?orbT.
by rewrite (modn_small hlt) addnC modn2 muln2.
Qed.

Lemma idx_of_path_of_idx l i : i < 2 ^ l -> idx_of_path (path_of_idx l i) = i.
Proof.
move=> hi; rewrite /idx_of_path /path_of_idx revK idx_of_lsb_bits.
by rewrite modn_small.
Qed.

Lemma idx_of_lsb_lt s : idx_of_lsb s < 2 ^ size s.
Proof.
elim: s => [//|b s IH] /=; rewrite expnS mul2n.
apply: leq_ltn_trans (_ : b + (idx_of_lsb s).*2 <= 1 + (idx_of_lsb s).*2) _.
- by rewrite leq_add2r; case: b.
- by rewrite add1n -doubleS leq_double.
Qed.

Lemma idx_of_path_lt p : idx_of_path p < 2 ^ size p.
Proof. by rewrite /idx_of_path -(size_rev p) idx_of_lsb_lt. Qed.

Lemma path_of_idx_of_path p : path_of_idx (size p) (idx_of_path p) = p.
Proof.
rewrite /path_of_idx /idx_of_path -[X in _ = X](revK p) -(size_rev p).
congr rev; elim: (rev p) => {p} [//|b s IH] /=.
case: b => /=.
- by rewrite add0n odd_double uphalf_double IH.
- by rewrite add0n odd_double doubleK IH.
Qed.

Lemma path_of_idx_inj l : {in [pred i | i < 2 ^ l] &, injective (path_of_idx l)}.
Proof.
move=> i j hi hj /(congr1 idx_of_path).
by rewrite !idx_of_path_of_idx.
Qed.
