(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Model.fxmss: FXMSS -- the stateful Merkle layer, as a neutral model.

    FXMSS ("flexible XMSS") is the stateful tree layer of SHRINCS: a
    Merkle tree whose anchors are WOTS+C one-time instances
    ([Model.wots]) and whose internal nodes are [thash] calls on
    SF_FXMSS_TREE (type 18) addresses.  This file is the shared,
    Stdlib-only ground-truth model of that layer, exactly as
    [Model.wots] is for the one-time signature underneath it: the same
    role, one level up.  Definitions plus the handful of bound lemmas
    the dependent addresses consume; no security content.

    Reference: shrincs-bip/impl/shrincs.py @ c9ae8bb (the authoritative
    spec) -- [fxmss_node] (:762), [fxmss_sign] (:809),
    [fxmss_pubkey_from_sig] (:848) and [shrincs_sf_leaf_select]
    (:1226).  Read the Python, not SHRINCS.md.

    ** What is modelled, and what is not

    Modelled: the FXMSS tree of a fixed 2-byte [structure] (shape +
    depth), its root, its authentication paths, its signer (at a state
    counter) and its verifier -- i.e. everything shrincs.py does
    between a MESSAGE DIGEST and an FXMSS root.

    NOT modelled here (deliberately, and nothing below precludes them):
    - [Model.shrincs], the OR-combiner: the stateful message digest
      Hmsg^sf / randomness PRFmsg^stateful and the cross-binding of
      sl_root/sf_root into the signed string (shrincs.py :1300, :1310,
      :1341, :1371).  The spec's [fxmss_sign] likewise takes a
      [message_digest], so this file's [fxmss_sign] does too.
    - the stateless SLH-DSA path (FORS, the hypertree).  Its ADRS arms
      already exist in [Model.address]; none is used here.

    ** Divergences from shrincs.py, all deliberate

    1. DEPTH ZERO IS UNREPRESENTABLE (a spec-bug fix; report upstream).

       [shrincs_sf_leaf_select] (shrincs.py :1245-1249) guards the
       BXMSS branch with [tree_depth > 0] but NOT the UXMSS
       fall-through:

         if tree_shape == FXMSS_SHAPE_UNBALANCED:
           if state_ctr == tree_depth and tree_depth > 0:
             return (0, FXMSS_HEIGHT - tree_depth)
           if state_ctr >= 0 and state_ctr < tree_depth + 1:
             return (1, FXMSS_HEIGHT - 1 - state_ctr)

       At [tree_depth = 0] with [state_ctr = 0] the first guard fails
       on [tree_depth > 0] and the second fires, returning [(1, 254)]
       -- a leaf one level BELOW a depth-zero tree.  Signing at it
       ([fxmss_sign] :841) then asks [fxmss_node] for the sibling at
       [(0, 254)], which is neither a UXMSS nor a BXMSS anchor, so the
       recursion descends forever (child_height 253, 252, ..., 0, -1,
       ...).  The spec's own comment block (:1256-1260) lists
       "depth-zero tree" among the cases that return None, so the code
       contradicts its stated intent.

       [Model.fxmss] therefore makes depth zero UNREPRESENTABLE: the
       [fxmss_structure] record carries [fx_depth_pos : 0 < fx_depth].
       No definition below has to re-check it, and no caller can build
       the offending input.

    2. BXMSS depth is capped at 64 ([fxmss_max_depth]).  A balanced
       tree of depth [d] has leaf indices up to [2^d - 1], and the ADRS
       node-index field is eight bytes ([fin (2^64)] in
       [Model.address]); at [d > 64] distinct positions would collide
       on one address.  The cap is the address-level half of the spec's
       own verifier check [leaf_index < 2 ** min(64, leaf_depth)]
       (:871), moved to the signer's side, and it is exactly the
       [index_bounded] conjunct of the games layer's shape
       well-formedness.  The UXMSS spine needs no cap: being a left
       spine, every one of its positions carries index 0 or 1 whatever
       its depth, which is why the spec can run it at the full
       [FXMSS_HEIGHT = 255].

    3. AUTH-PATH ORIENTATION is the spec's: BOTTOM-UP, closest sibling
       first ([fxmss_sign] :841-844, [fxmss_pubkey_from_sig] :885-892).
       The SSProve games layer stores it top-down; that [rev] is one of
       the differences the model bridge absorbs.

    4. The tree walk is EXACT, never clamped: the node-index field is a
       dependent [fin (2^64)] built from a bound proof, in the
       [Model.address] discipline ([Model.fin]'s header: "the model
       deliberately has NO saturating totalizer").  Where a bound
       cannot be established from the caller's data -- the
       authentication path of an out-of-range leaf -- the model REFUSES
       ([option]); it does not substitute a default.  Node HEIGHTS need
       no such proof: a height is always [FXMSS_HEIGHT - node_depth],
       hence [<= 255] by construction (saturating [nat] subtraction),
       which is also how the spec derives [leaf_height] from a
       signature's length ([fxmss_pubkey_from_sig] :868, :873).

    Naming: [fx_*] for the structure record's fields and the internal
    node recursion, [fxmss_*] for everything a caller uses. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Export wots.
Import ListNotations.
Open Scope Z_scope.

(** FXMSS instantiates [Model.address]'s parametric ADRS at the same
    WOTS+C row as [Model.wots] ([chain_count = len], [pos_bound =
    w_pred]): the tree's anchors ARE WOTS+C instances, so one address
    type serves both layers. *)
Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** Parameters (shrincs.py :60, :77-78, :90). *)

(** The declared height of the imaginary balanced tree every FXMSS
    position is addressed against: a node at depth [d] has height
    [FXMSS_HEIGHT - d]. *)
Definition FXMSS_HEIGHT : nat := 255.

(** The two tree shapes.  UNBALANCED is the UXMSS left spine (an anchor
    hangs off every level); BALANCED is a perfect tree. *)
Inductive fxmss_shape : Type :=
  | FXMSS_SHAPE_UNBALANCED
  | FXMSS_SHAPE_BALANCED.

(** The greatest depth at which a shape's positions still address
    injectively (divergence 2 in the header): the spine keeps every
    index in [{0, 1}], so it runs to the full declared height; the
    perfect tree's deepest index is [2^d - 1], which must fit the
    eight-byte node-index field. *)
Definition fxmss_max_depth (sh : fxmss_shape) : nat :=
  match sh with
  | FXMSS_SHAPE_UNBALANCED => FXMSS_HEIGHT
  | FXMSS_SHAPE_BALANCED   => 64
  end.

(** The 2-byte [structure] of shrincs.py, with its two implicit
    well-formedness conditions made intrinsic: depth is POSITIVE (the
    spec bug of divergence 1 is unrepresentable) and within the
    shape's addressable range. *)
Record fxmss_structure : Type := mk_fxmss_structure {
  fx_shape : fxmss_shape ;
  fx_depth : nat ;
  fx_depth_pos : (0 < fx_depth)%nat ;
  fx_depth_max : (fx_depth <= fxmss_max_depth fx_shape)%nat ;
}.

(* ================================================================= *)
(** ** Addresses.

    An FXMSS position is a (node_depth, node_index) pair; the address
    carries the node HEIGHT [FXMSS_HEIGHT - node_depth] in its one-byte
    anchor-tag slot and the index in its eight-byte slot (shrincs.py
    :786-787, :803-806).  Internal nodes are typed SF_FXMSS_TREE
    ([Fxmss]); an anchor's carrier is typed SF_SHRINCS_WOTS_PK
    ([Wc_pk]) -- [Model.wots]'s smart constructors read back only the
    anchor through [adrs_nh]/[adrs_ni], so the carrier's own type byte
    never reaches a hash. *)

(** A node height is always [<= FXMSS_HEIGHT = 255]: no hypothesis
    needed, saturating [nat] subtraction supplies the bound. *)
Lemma fxmss_height_lt_256 (nd : nat) : Z.of_nat (FXMSS_HEIGHT - nd) < 256.
Proof. unfold FXMSS_HEIGHT. lia. Qed.

Definition fxmss_node_height (nd : nat) : fin 256 :=
  fin_of_nat 256 (FXMSS_HEIGHT - nd) (fxmss_height_lt_256 nd).

(** SF_FXMSS_TREE address of the internal node at depth [nd], index
    [i]. *)
Definition fxmss_tree_adrs (nd i : nat) (Hi : Z.of_nat i < 2 ^ 64) : adrs :=
  Fxmss (fxmss_node_height nd) (fin_of_nat (2 ^ 64) i Hi).

(** The WOTS+C anchor carrier at depth [nd], index [i]. *)
Definition fxmss_anchor_adrs (nd i : nat) (Hi : Z.of_nat i < 2 ^ 64) : adrs :=
  Wc_pk (fxmss_node_height nd) (fin_of_nat (2 ^ 64) i Hi).

(** The tree-node hash H(pk_seed, ADRS, lchild || rchild) of shrincs.py
    :807 -- the same [thash] as every other SHRINCS tweakable hash, on
    a SF_FXMSS_TREE address, over the 2n-byte concatenation of the two
    children. *)
Definition fxmss_H (pk_seed : block) (nd i : nat) (Hi : Z.of_nat i < 2 ^ 64)
    (x y : block) : block :=
  thash pk_seed (fxmss_tree_adrs nd i Hi) (x ++ y).

(** The anchor value: the compressed WOTS+C public key of the instance
    anchored at this position (shrincs.py :788). *)
Definition fxmss_anchor (sk_seed pk_seed : block) (nd i : nat)
    (Hi : Z.of_nat i < 2 ^ 64) : block :=
  shrincs_wots_pubkey_gen sk_seed pk_seed (fxmss_anchor_adrs nd i Hi).

(* ================================================================= *)
(** ** The node-index invariant.

    [Model.address]'s node-index field is a [fin (2^64)], so the tree
    recursion has to carry a bound on the index it descends into.  One
    shape-dependent invariant does it, and it is exactly the reason
    each shape has the [fxmss_max_depth] it has:

    - the UXMSS spine descends only from index 0 (shrincs.py :792
      asserts it), whose children are 0 and 1 -- so "index [<= 1]" is
      preserved at every depth;
    - the BXMSS tree descends everywhere, and index [< 2^depth] is
      preserved by [i |-> 2i, 2i+1].

    Both give [i < 2^64] once the depth is within [fxmss_max_depth]. *)

Definition node_idx_ok (sh : fxmss_shape) (nd i : nat) : Prop :=
  match sh with
  | FXMSS_SHAPE_UNBALANCED => (i <= 1)%nat
  | FXMSS_SHAPE_BALANCED   => Z.of_nat i < 2 ^ Z.of_nat nd
  end.

(** "This position is an anchor at every depth": the UXMSS disjunct
    [node_index == 1] of shrincs.py's [is_uxmss_leaf] (:782).  The
    other disjunct ([node_depth == tree_depth]) is the recursion's base
    case, not this predicate. *)
Definition fx_anchor_here (sh : fxmss_shape) (i : nat) : Prop :=
  match sh with
  | FXMSS_SHAPE_UNBALANCED => i = 1%nat
  | FXMSS_SHAPE_BALANCED   => False
  end.

Definition fx_anchor_dec (sh : fxmss_shape) (i : nat)
  : {fx_anchor_here sh i} + {~ fx_anchor_here sh i}.
Proof.
  destruct sh as [|].
  - apply Nat.eq_dec.
  - right. exact (fun H => H).
Defined.

(** Bound obligations of the dependent [fx_node] below, factored out as
    named lemmas: an [ltac:(lia)] inside a Fixpoint term cannot see the
    match-bound hypotheses (same reason as [Model.wots]'s
    [chain_iter_pos_lt] / [chain_iter_rec_le]). *)

Lemma fx_depth_here (nd rem m : nat) (H : (nd + rem <= m)%nat) : (nd <= m)%nat.
Proof. lia. Qed.

Lemma fx_depth_child (nd r m : nat) (H : (nd + S r <= m)%nat) : (S nd + r <= m)%nat.
Proof. lia. Qed.

(** The invariant delivers the field bound the address needs. *)
Lemma node_idx_ok_lt (sh : fxmss_shape) (nd i : nat) :
  (nd <= fxmss_max_depth sh)%nat -> node_idx_ok sh nd i -> Z.of_nat i < 2 ^ 64.
Proof.
  destruct sh as [|]; simpl; intros Hnd Hi.
  - assert (H1 : 2 ^ 0 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.pow_0_r in H1. lia.
  - assert (Hle : 2 ^ Z.of_nat nd <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    lia.
Qed.

(** Descent preserves the invariant.  The UXMSS half needs the guard
    [~ fx_anchor_here] (index 1 is an anchor, so the spine only ever
    descends from index 0 -- shrincs.py :792). *)
Lemma node_idx_ok_left (sh : fxmss_shape) (nd i : nat) :
  ~ fx_anchor_here sh i -> node_idx_ok sh nd i -> node_idx_ok sh (S nd) (2 * i).
Proof.
  unfold fx_anchor_here, node_idx_ok.
  destruct sh as [|]; intros Hne Hi; [ lia | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  lia.
Qed.

Lemma node_idx_ok_right (sh : fxmss_shape) (nd i : nat) :
  ~ fx_anchor_here sh i -> node_idx_ok sh nd i -> node_idx_ok sh (S nd) (2 * i + 1).
Proof.
  unfold fx_anchor_here, node_idx_ok.
  destruct sh as [|]; intros Hne Hi; [ lia | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  lia.
Qed.

(* ================================================================= *)
(** ** The node recursion (shrincs.py [fxmss_node], :762).

    [fx_node sh sk pk rem nd i] is the FXMSS node at depth [nd], index
    [i], with [rem] levels of tree still below it ([rem = tree_depth -
    nd]).  Structural in [rem], so the spec's "catch and throw if
    control would enter an infinite recursive loop" (:790) is not a
    runtime check here: the recursion cannot diverge.

    The two anchor conditions of :782-783 are [rem = 0] (node_depth =
    tree_depth, both shapes) and [fx_anchor_here] (node_index = 1,
    UXMSS only). *)
Fixpoint fx_node (sh : fxmss_shape) (sk_seed pk_seed : block)
    (rem nd i : nat) {struct rem}
  : (nd + rem <= fxmss_max_depth sh)%nat -> node_idx_ok sh nd i -> block :=
  match rem
    return (nd + rem <= fxmss_max_depth sh)%nat -> node_idx_ok sh nd i -> block
  with
  | O =>
      fun Hd Hi =>
        fxmss_anchor sk_seed pk_seed nd i
          (node_idx_ok_lt sh nd i (fx_depth_here nd 0 _ Hd) Hi)
  | S r =>
      fun Hd Hi =>
        match fx_anchor_dec sh i with
        | left _ =>
            fxmss_anchor sk_seed pk_seed nd i
              (node_idx_ok_lt sh nd i (fx_depth_here nd (S r) _ Hd) Hi)
        | right Hne =>
            fxmss_H pk_seed nd i
              (node_idx_ok_lt sh nd i (fx_depth_here nd (S r) _ Hd) Hi)
              (fx_node sh sk_seed pk_seed r (S nd) (2 * i)
                 (fx_depth_child nd r _ Hd) (node_idx_ok_left sh nd i Hne Hi))
              (fx_node sh sk_seed pk_seed r (S nd) (2 * i + 1)
                 (fx_depth_child nd r _ Hd) (node_idx_ok_right sh nd i Hne Hi))
        end
  end.

(* ================================================================= *)
(** ** The root (shrincs.py :1220: [fxmss_node(sk_seed, 0,
    FXMSS_HEIGHT, pk_seed, sf_structure, ...)]). *)

Lemma fxmss_root_depth_ok (st : fxmss_structure) :
  (0 + fx_depth st <= fxmss_max_depth (fx_shape st))%nat.
Proof. pose proof (fx_depth_max st). lia. Qed.

Lemma fxmss_root_idx_ok (st : fxmss_structure) : node_idx_ok (fx_shape st) 0 0.
Proof.
  unfold node_idx_ok. destruct (fx_shape st) as [|]; [ lia | ].
  replace (Z.of_nat 0) with 0 by reflexivity.
  rewrite Z.pow_0_r. lia.
Qed.

Definition fxmss_root (st : fxmss_structure) (sk_seed pk_seed : block) : block :=
  fx_node (fx_shape st) sk_seed pk_seed (fx_depth st) 0 0
    (fxmss_root_depth_ok st) (fxmss_root_idx_ok st).

(* ================================================================= *)
(** ** Total node lookup (used by the authentication path).

    [fxmss_node_at st sk pk nd i] is the node at (depth, index) when
    that position is one this structure addresses, and [None]
    otherwise -- a REFUSAL, not a clamped default (header divergence
    4).  Both side conditions are decidable, so no caller has to supply
    a proof. *)

Definition node_idx_ok_dec (sh : fxmss_shape) (nd i : nat)
  : {node_idx_ok sh nd i} + {~ node_idx_ok sh nd i}.
Proof.
  unfold node_idx_ok. destruct sh as [|].
  - apply Compare_dec.le_dec.
  - apply Z_lt_dec.
Defined.

Lemma fxmss_node_at_depth (st : fxmss_structure) (nd : nat)
    (H : (nd <= fx_depth st)%nat) :
  (nd + (fx_depth st - nd) <= fxmss_max_depth (fx_shape st))%nat.
Proof. pose proof (fx_depth_max st). lia. Qed.

Definition fxmss_node_at (st : fxmss_structure) (sk_seed pk_seed : block)
    (nd i : nat) : option block :=
  match Compare_dec.le_dec nd (fx_depth st), node_idx_ok_dec (fx_shape st) nd i with
  | left Hnd, left Hi =>
      Some (fx_node (fx_shape st) sk_seed pk_seed (fx_depth st - nd) nd i
              (fxmss_node_at_depth st nd Hnd) Hi)
  | _, _ => None
  end.

(* ================================================================= *)
(** ** Leaf selection (shrincs.py [shrincs_sf_leaf_select], :1226).

    Returns the (index, height) of the leaf the [state_ctr]-th
    signature uses, or [None] when the budget is exhausted.  The
    spec's other two [None] cases are unreachable here by
    construction: a [nat] counter cannot be negative, and
    [fxmss_structure] has no depth-zero inhabitant (header divergence
    1). *)
Definition fxmss_leaf_select (st : fxmss_structure) (state_ctr : nat)
  : option (nat * nat) :=
  match fx_shape st with
  | FXMSS_SHAPE_UNBALANCED =>
      if Nat.eqb state_ctr (fx_depth st)
      then Some (0%nat, (FXMSS_HEIGHT - fx_depth st)%nat)
      else if Nat.ltb state_ctr (fx_depth st)
           then Some (1%nat, (FXMSS_HEIGHT - 1 - state_ctr)%nat)
           else None
  | FXMSS_SHAPE_BALANCED =>
      if Z.ltb (Z.of_nat state_ctr) (2 ^ Z.of_nat (fx_depth st))
      then Some (state_ctr, (FXMSS_HEIGHT - fx_depth st)%nat)
      else None
  end.

(* ================================================================= *)
(** ** Authentication path (shrincs.py [fxmss_sign], :841-844).

    BOTTOM-UP: entry [j] is the sibling of the [j]-th ancestor of the
    signing leaf, at index [(leaf_index >> j) xor 1] and height
    [leaf_height + j] (equivalently depth [leaf_depth - j]).  [None] if
    any of those siblings is not a position this structure
    addresses. *)

#[global] Instance default_option_block : Default (option block) := None.

(** [x xor 1] on the low bit: the sibling of node index [x]. *)
Definition fxmss_sibling (x : nat) : nat :=
  if Nat.odd x then Nat.pred x else S x.

(** [option] traversal, left to right ([None] if any entry is
    [None]). *)
Fixpoint fxmss_sequence (xs : list (option block)) : option (list block) :=
  match xs with
  | [] => Some nil
  | ox :: xs' =>
      match ox, fxmss_sequence xs' with
      | Some x, Some ys => Some (x :: ys)
      | _, _ => None
      end
  end.

Definition fxmss_auth (st : fxmss_structure) (sk_seed pk_seed : block)
    (leaf_index leaf_height : nat) : option (list block) :=
  let leaf_depth := (FXMSS_HEIGHT - leaf_height)%nat in
  fxmss_sequence
    (for j in range leaf_depth as Hj {{
       fxmss_node_at st sk_seed pk_seed
         (leaf_depth - j)%nat (fxmss_sibling (Nat.shiftr leaf_index j)) }}).

(* ================================================================= *)
(** ** Signatures, signing, verification. *)

(** The wire signature of shrincs.py :838-844 and :865-868: the leaf
    index, the WOTS+C signature (chain values plus the grinding
    counter) and the bottom-up authentication path.  The leaf HEIGHT is
    NOT transmitted -- the verifier derives it from the path length
    (:868, :873). *)
Definition fxmss_signature : Type := nat * (list block * Z) * list block.

(** [fxmss_sign] at an explicit leaf position: refuse unless the index
    fits the address field, then sign the digest with the anchor's
    WOTS+C instance and attach the authentication path.  [None] also on
    WOTS+C grinding failure ([Model.wots.shrincs_wots_sign]) or on an
    unaddressable sibling. *)
Definition fxmss_sign_at (st : fxmss_structure) (sk_seed pk_seed : block)
    (md : block) (leaf_index leaf_height : nat) : option fxmss_signature :=
  match Z_lt_dec (Z.of_nat leaf_index) (2 ^ 64) with
  | left Hi =>
      match shrincs_wots_sign md sk_seed pk_seed
              (fxmss_anchor_adrs (FXMSS_HEIGHT - leaf_height) leaf_index Hi),
            fxmss_auth st sk_seed pk_seed leaf_index leaf_height
      with
      | Some ws, Some ap => Some (leaf_index, ws, ap)
      | _, _ => None
      end
  | right _ => None
  end.

(** The signer proper: the [state_ctr]-th signature uses the leaf
    [fxmss_leaf_select] names (shrincs.py :1295 feeding :838). *)
Definition fxmss_sign (st : fxmss_structure) (sk_seed pk_seed : block)
    (md : block) (state_ctr : nat) : option fxmss_signature :=
  match fxmss_leaf_select st state_ctr with
  | Some (leaf_index, leaf_height) =>
      fxmss_sign_at st sk_seed pk_seed md leaf_index leaf_height
  | None => None
  end.

(** The verifier's bottom-up walk (shrincs.py :885-892).  At each step
    the current node sits at index [i] and depth [length ap]; its
    parent is at index [i / 2] and depth [length ap - 1], and the
    sibling goes left or right according to [i]'s low bit.  Recursion
    is structural in the path, and the parent's DEPTH is read off the
    remaining path length -- which is why no height bound has to be
    threaded. *)

Lemma fxmss_walk_idx_lt (i : nat) (Hi : Z.of_nat i < 2 ^ 64) :
  Z.of_nat (Nat.div2 i) < 2 ^ 64.
Proof. pose proof (Nat.le_div2_diag_l i). lia. Qed.

Fixpoint fxmss_walk (pk_seed : block) (i : nat) (node : block) (ap : list block)
    {struct ap} : Z.of_nat i < 2 ^ 64 -> block :=
  match ap return Z.of_nat i < 2 ^ 64 -> block with
  | [] => fun _ => node
  | s :: ap' =>
      fun Hi =>
        fxmss_walk pk_seed (Nat.div2 i)
          (fxmss_H pk_seed (length ap') (Nat.div2 i) (fxmss_walk_idx_lt i Hi)
             (if Nat.odd i then s else node)
             (if Nat.odd i then node else s))
          ap' (fxmss_walk_idx_lt i Hi)
  end.

(** [fxmss_pubkey_from_sig] (shrincs.py :848): recover the anchor with
    WOTS+C, then walk up.  The leaf depth is the path length and the
    leaf height [FXMSS_HEIGHT - length ap], per :868/:873. *)
Definition fxmss_root_from_sig (pk_seed : block) (md : block)
    (leaf_index : nat) (ws : list block * Z) (ap : list block)
    (Hi : Z.of_nat leaf_index < 2 ^ 64) : block :=
  fxmss_walk pk_seed leaf_index
    (shrincs_wots_pubkey_from_sig md (fst ws) (snd ws) pk_seed
       (fxmss_anchor_adrs (length ap) leaf_index Hi))
    ap Hi.

(** The spec's leaf-identifier check, [assert leaf_index < 2 **
    min(64, leaf_depth)] (:871), kept in [Z]: the [min] splits into
    "the index names a position of the imaginary tree at that depth"
    and "the index fits the eight-byte field".  The second half is what
    keeps distinct positions on distinct addresses once the leaf depth
    exceeds 64. *)
Definition fxmss_leaf_id_bound (leaf_depth : nat) : Z :=
  2 ^ Z.min 64 (Z.of_nat leaf_depth).

Lemma fxmss_leaf_id_lt (leaf_index leaf_depth : nat) :
  Z.of_nat leaf_index < fxmss_leaf_id_bound leaf_depth ->
  Z.of_nat leaf_index < 2 ^ 64.
Proof.
  unfold fxmss_leaf_id_bound. intros H.
  assert (Hle : 2 ^ Z.min 64 (Z.of_nat leaf_depth) <= 2 ^ 64)
    by (apply Z.pow_le_mono_r; lia).
  lia.
Qed.

Definition block_eqb (x y : block) : bool :=
  if list_eq_dec byte_eq_dec x y then true else false.

(** FXMSS verification: the leaf identifier is in range and names a
    depth the declared height admits, the WOTS+C digest at the
    signature's counter is in the post-grinding space, and the walk
    recovers the root.  The spec's signature-size window
    ([FXMSS_SIGNATURE_SIZE_MAX], :70) is the [length ap <=
    FXMSS_HEIGHT] conjunct; its WOTS+C half is
    [Model.wots.valid_digest]. *)
Definition fxmss_verify (pk_seed root md : block) (sg : fxmss_signature) : bool :=
  let '(leaf_index, ws, ap) := sg in
  match Z_lt_dec (Z.of_nat leaf_index) (fxmss_leaf_id_bound (length ap)) with
  | left Hi =>
      Nat.leb (length ap) FXMSS_HEIGHT
      && valid_digest
           (digest_of pk_seed
              (fxmss_anchor_adrs (length ap) leaf_index
                 (fxmss_leaf_id_lt leaf_index (length ap) Hi))
              md (snd ws))
      && block_eqb
           (fxmss_root_from_sig pk_seed md leaf_index ws ap
              (fxmss_leaf_id_lt leaf_index (length ap) Hi))
           root
  | right _ => false
  end.

(* ================================================================= *)
(** ** Spec conformance at the recommended parameters.

    shrincs.py's recommended stateful tree is the UXMSS spine of depth
    [FXMSS_HEIGHT = 255], with 256 WOTS+C anchors.  The example below
    is the [Model.fxmss] counterpart of the games layer's
    [shrincs_fxmss_uxmss_at_spec_height]: that structure is
    representable, and its leaf schedule issues exactly 256 signatures
    (counters [0 .. 255]) before refusing. *)

Definition uxmss_spec_structure : fxmss_structure :=
  {| fx_shape := FXMSS_SHAPE_UNBALANCED ;
     fx_depth := FXMSS_HEIGHT ;
     fx_depth_pos := ltac:(unfold FXMSS_HEIGHT; lia) ;
     fx_depth_max := ltac:(unfold fxmss_max_depth; lia) |}.

Example fxmss_uxmss_at_spec_height :
  fx_depth uxmss_spec_structure = 255%nat
  /\ (forall k, (k <= 255)%nat ->
       exists p, fxmss_leaf_select uxmss_spec_structure k = Some p)
  /\ fxmss_leaf_select uxmss_spec_structure 256 = None.
Proof.
  split; [ reflexivity | split ].
  - intros k Hk.
    unfold fxmss_leaf_select, uxmss_spec_structure, FXMSS_HEIGHT. simpl.
    destruct (Nat.eqb_spec k 255) as [->|Hne]; [ eexists; reflexivity | ].
    destruct (Nat.ltb_spec k 255) as [Hlt|Hge]; [ eexists; reflexivity | lia ].
  - reflexivity.
Qed.

(** Projections used to invert [fxmss_leaf_select]'s [Some] below.  A
    plain [inversion]/[injection] would first SIMPLIFY the concrete
    [FXMSS_HEIGHT - 1 - state_ctr], expanding it into a 256-way [match]
    on the counter that no arithmetic decision procedure can then read;
    projecting with [f_equal] and reducing only these two constants
    keeps the subtraction folded. *)
Definition fxmss_sel_index (o : option (nat * nat)) : nat :=
  match o with
  | Some (i, _) => i
  | None => 0%nat
  end.

Definition fxmss_sel_height (o : option (nat * nat)) : nat :=
  match o with
  | Some (_, h) => h
  | None => 0%nat
  end.

(** The schedule is injective, which is all a leaf-placement map has to
    be: no two counters name the same anchor, so no anchor is ever used
    twice. *)
Lemma fxmss_leaf_select_inj (st : fxmss_structure) (k k' : nat) (p : nat * nat) :
  fxmss_leaf_select st k = Some p -> fxmss_leaf_select st k' = Some p -> k = k'.
Proof.
  pose proof (fx_depth_pos st) as Hpos.
  assert (Hmax : (fx_depth st <= 255)%nat).
  { pose proof (fx_depth_max st) as H.
    destruct (fx_shape st); cbv [fxmss_max_depth FXMSS_HEIGHT] in H; lia. }
  unfold fxmss_leaf_select, FXMSS_HEIGHT.
  destruct (fx_shape st) as [|].
  - destruct (Nat.eqb_spec k (fx_depth st)) as [Hk|Hk],
             (Nat.eqb_spec k' (fx_depth st)) as [Hk'|Hk'],
             (Nat.ltb_spec k (fx_depth st)) as [Hlt|Hge],
             (Nat.ltb_spec k' (fx_depth st)) as [Hlt'|Hge'];
      intros H1 H2; try discriminate H1; try discriminate H2;
      rewrite <- H1 in H2;
      first [ lia
            | (pose proof H2 as H3;
               apply (f_equal fxmss_sel_index) in H2;
               apply (f_equal fxmss_sel_height) in H3;
               cbv beta iota delta [fxmss_sel_index fxmss_sel_height] in H2, H3;
               lia) ].
  - destruct (Z.ltb_spec (Z.of_nat k) (2 ^ Z.of_nat (fx_depth st))) as [Hlt|Hge],
             (Z.ltb_spec (Z.of_nat k') (2 ^ Z.of_nat (fx_depth st))) as [Hlt'|Hge'];
      intros H1 H2; try discriminate H1; try discriminate H2;
      rewrite <- H1 in H2;
      first [ lia
            | (pose proof H2 as H3;
               apply (f_equal fxmss_sel_index) in H2;
               apply (f_equal fxmss_sel_height) in H3;
               cbv beta iota delta [fxmss_sel_index fxmss_sel_height] in H2, H3;
               lia) ].
Qed.
