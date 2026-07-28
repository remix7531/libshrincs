(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.fxmss.model_bridge

    The games <-> model correspondence for the FXMSS TREE layer: the
    machine link between [SHRINCS.fxmss.scheme] (SSProve idiom --
    [seq], [bt], ordinals, an adversary-chosen shape, node positions as
    [seq bool] paths) and [Model.fxmss] (Stdlib idiom -- [list], [Z],
    dependent [fin] address fields, the spec's own (node_depth,
    node_index) recursion).  One level up from
    [Sec.wots.model_bridge], and reusing it for the WOTS+C anchors.

    ** What the bridge absorbs

    Four representation differences, none of them semantic:

    1. VALUES: games hash values are ordinals ([N_shrincs = 'fin
       (2^128)]); model ones are 16-byte strings.  Every statement
       QUANTIFIES the games value and DECODES it ([decode16]) -- never
       the reverse, exactly as in [Sec.wots.model_bridge].
    2. ADDRESSES: the games layer places address components through
       [Sec.addressing]'s exact-or-zero facade (bare [nat] in, [fin]
       out); [Model.fxmss] builds the same [fin] fields from bound
       PROOFS.  The two agree on every representable component
       ([anchor_heightE] / [anchor_indexE]) -- which is what
       [tree_adrsE] / [anchor_adrsE] below say, and they are the
       leaf-position <-> ADRS agreement of the phase brief.
    3. TREE SHAPE: the games scheme evaluates an arbitrary [bt unit]
       over [seq bool] positions; [Model.fxmss] runs the spec's
       recursion on (node_depth, node_index) at ONE of the two spec
       shapes.  [root_uxmssE] is the two meeting at the spec's
       recommended UXMSS spine; the position dictionary is
       [size pos <-> node_depth] and [idx_of_path pos <-> node_index].
    4. AUTH-PATH ORIENTATION: the games layer stores authentication
       paths TOP-DOWN (root-side sibling first, [cons_ap]/[val_ap]);
       shrincs.py and hence [Model.fxmss] store them BOTTOM-UP.  That
       is the [rev] in [val_ap_walkE].

    ** The instantiation

    The games scheme is a [Section] over abstract building blocks, so
    the bridge fixes them at the concrete truncated-SHA-256 hashes of
    [Sec.axioms] -- [F_sha256], [T_sf_sha256] and [PRF_sha256] for the
    WOTS+C anchors, plus [Htree_sha256] here for the tree nodes -- and
    at [h_sf := Model.fxmss.FXMSS_HEIGHT = 255], the spec's declared
    height (shrincs.py :60).  This is the same [wc_sha256] hash family
    the native WOTS+C tree's headline theorem is instantiated against,
    so the FXMSS leaves ARE the WOTS+C instances [Sec.wots.model_bridge]
    already bridged.

    ** Out of scope, and why

    - [Hmsg^sf] / [PRFmsg^stateful] and the SHRINCS-level cross-binding
      are [Model.shrincs], deliberately not built (see [Model.fxmss]'s
      header).  shrincs.py's [fxmss_sign] likewise takes a MESSAGE
      DIGEST, which is where this bridge cuts.
    - The WOTS+C leaf's SIGNATURE (as opposed to its public key) is not
      bridged here: [SHRINCS.wotsc.scheme] instantiates the generic
      WOTS+C construction at [dig_msb := false] (LSB-first grinding
      digits) while [Sec.wots.scheme], shrincs.py's base-w parse and
      [Model.wots.base_2b] are all MSB-first.  Public keys are digit
      order independent (every chain runs to [w-1]), so [leaf_pkE] and
      [root_uxmssE] are unaffected; a signature-level bridge would
      first have to reconcile that ordering.  Recorded as a finding.

    IMPORT DISCIPLINE (see [Sec.bridge] / [Sec.wots.model_bridge]
    headers, load-bearing): [BinInt] stays a plain [Import] and [Znat]
    a plain [Require] -- `Require Import ZArith` / `Require Import Znat`
    both silently shadow mathcomp's nat "^" ([expn] -> [Nat.pow]).
    Numeric comparisons take an explicit [%nat] annotation. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude math.bin_tree math.merkle sig.scheme.
From SHRINCS Require Import addressing wotsc.scheme fxmss.scheme.
Set Warnings "notation-overridden,ambiguous-paths".
From Sec Require addressing.
Require Import Sec.wots.instantiation.
Require Import Sec.axioms.
Require Import Sec.wots.model_bridge.
From Model Require fxmss address fin sha256 wots.
Require Model.theory.fxmss.
(* See header IMPORT DISCIPLINE. *)
From Stdlib Require Import BinInt Lia.
From Stdlib Require Znat.

Import PackageNotation.
#[local] Open Scope package_scope.

(** The address type of the FXMSS games layer at the shrincs numbers.
    It is CONVERTIBLE to [Model.wots]'s [adrs = address.adrs 32 15]
    ([chain_count_shrincs = wots.len], [w_shrincs.-1 = wots.w_pred]), so
    a model address passes wherever this one is expected and back. *)
Local Notation adrs_s :=
  (address.adrs chain_count_shrincs w_shrincs.-1).

(** The declared imaginary-tree height, from the model (shrincs.py
    [FXMSS_HEIGHT = 255]). *)
Local Notation h_sf := Model.fxmss.FXMSS_HEIGHT.

(* ------------------------------------------------------------------ *)
(** ** The concrete FXMSS building blocks

    [F_sha256] / [T_sf_sha256] / [PRF_sha256] are [Sec.axioms]'; only
    the tree-node hash is new here.  H : B^n x B^288 x B^2n -> B^n is
    the same [Model.wots.thash] as every other SHRINCS tweakable hash,
    fed the two children's concatenation (shrincs.py :807). *)

Definition Htree_sha256 (pp : PP_shrincs) (a : adrs_s)
    (xy : N_shrincs * N_shrincs) : N_shrincs :=
  encode16 (wots.thash (decode16 pp) a
              (List.app (decode16 xy.1) (decode16 xy.2))).

(** PRF_f(PKseed, SKseed, ADRS_sf) in the games layer's argument order
    (key before address); [Sec.axioms]' [PRF_sha256] takes the address
    first. *)
Definition PRFf_sha256 (pp : PP_shrincs) (k : K_shrincs) (a : adrs_s)
  : N_shrincs :=
  PRF_sha256 pp a k.

(** The games-layer FXMSS operations at those blocks and at the spec's
    declared height. *)

Definition fx_node_hash (pp : PP_shrincs) : seq bool -> N_shrincs -> N_shrincs -> N_shrincs :=
  shrincs_fxmss_node_hash PP_shrincs N_shrincs Htree_sha256 h_sf pp.

Definition fx_leaf_pk (pp : PP_shrincs) (ks : K_shrincs) (zi : nat * nat) : N_shrincs :=
  shrincs_fxmss_leaf_public_key PP_shrincs N_shrincs K_shrincs
    F_sha256 T_sf_sha256 PRFf_sha256 pp ks zi.

Definition fx_value_tree (pp : PP_shrincs) (ks : K_shrincs) (t : bt unit) : bt N_shrincs :=
  shrincs_fxmss_value_tree PP_shrincs N_shrincs K_shrincs
    F_sha256 T_sf_sha256 PRFf_sha256 h_sf pp ks t.

Definition fx_root (pp : PP_shrincs) (ks : K_shrincs) (t : bt unit) : N_shrincs :=
  shrincs_fxmss_root PP_shrincs N_shrincs K_shrincs
    F_sha256 T_sf_sha256 Htree_sha256 PRFf_sha256 h_sf pp ks t.

(* ------------------------------------------------------------------ *)
(** ** GLUE: position arithmetic

    [idx_of_path] reads a path MSB-first, so appending one more step
    doubles the index -- the games-side counterpart of the model
    recursion's [i |-> 2i, 2i+1]. *)

Lemma idx_of_path_rcons (p : seq bool) (b : bool) :
  idx_of_path (rcons p b) = (idx_of_path p * 2 + b)%nat.
Proof. by rewrite -cats1 idx_of_path_cat /=; case: b; rewrite ?addn0 ?muln2 ?addn1. Qed.

(** The model walk tests the low bit with Stdlib's [Nat.odd] and halves
    with [Nat.div2]; both read straight off a games-side path. *)
Lemma nat_odd_idx (n : nat) (b : bool) : Nat.odd (n * 2 + b)%nat = b.
Proof.
elim: n => [|n IH]; first by case: b.
have -> : (n.+1 * 2 + b)%nat = ((n * 2 + b).+2)%nat
  by rewrite !muln2 doubleS !addSn.
exact: IH.
Qed.

Lemma nat_div2_idx (n : nat) (b : bool) : Nat.div2 (n * 2 + b)%nat = n.
Proof.
elim: n => [|n IH]; first by case: b.
have -> : (n.+1 * 2 + b)%nat = ((n * 2 + b).+2)%nat
  by rewrite !muln2 doubleS !addSn.
by rewrite /= IH.
Qed.

Lemma odd_idx_rcons (p : seq bool) (b : bool) :
  Nat.odd (idx_of_path (rcons p b)) = b.
Proof. by rewrite idx_of_path_rcons nat_odd_idx. Qed.

Lemma div2_idx_rcons (p : seq bool) (b : bool) :
  Nat.div2 (idx_of_path (rcons p b)) = idx_of_path p.
Proof. by rewrite idx_of_path_rcons nat_div2_idx. Qed.

(** [decode16 o encode16 = id] at the FXMSS widths: every model value
    the bridge round-trips is a [thash] output, hence 16 bytes. *)
Lemma decode16_encode16_len (Y : sha256.block) :
  length Y = 16%nat -> decode16 (encode16 Y) = Y.
Proof. by move=> h; apply: decode16_encode16; rewrite size_lengthE h. Qed.

(* ------------------------------------------------------------------ *)
(** ** ADDRESS AGREEMENT (the leaf-position <-> ADRS stratum)

    The games layer's exact-or-zero placement of a representable
    (height, index) IS the model's dependent-[fin] address.  The height
    slot is filled from the node DEPTH on the model side and from the
    node HEIGHT on the games side -- the two are [h_sf - _] apart, and
    the lemmas below fix the dictionary. *)

Lemma tree_adrsE (nd i : nat) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  @addressing.fxmss_tree_adrs chain_count_shrincs w_shrincs (h_sf - nd)%nat i
  = Model.fxmss.fxmss_tree_adrs nd i Hi.
Proof.
rewrite /addressing.fxmss_tree_adrs /Model.fxmss.fxmss_tree_adrs
        /Model.fxmss.fxmss_node_height.
rewrite (addressing.anchor_heightE _ (Model.fxmss.fxmss_height_lt_256 nd)).
by rewrite (addressing.anchor_indexE i Hi).
Qed.

Lemma anchor_adrsE (nd i : nat) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  @addressing.wc_pk_adrs chain_count_shrincs w_shrincs ((h_sf - nd)%nat, i)
  = Model.fxmss.fxmss_anchor_adrs nd i Hi.
Proof.
rewrite /addressing.wc_pk_adrs /Model.fxmss.fxmss_anchor_adrs
        /Model.fxmss.fxmss_node_height /=.
rewrite (addressing.anchor_heightE _ (Model.fxmss.fxmss_height_lt_256 nd)).
by rewrite (addressing.anchor_indexE i Hi).
Qed.

(** The WOTS+C anchor address of [Sec.wots.model_bridge] ([A0], the
    carrier the native tree's pubkey correspondence is stated at) at a
    representable FXMSS leaf position IS the model's. *)
Lemma A0_anchorE (nd i : nat) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  A0 (h_sf - nd)%nat i = Model.fxmss.fxmss_anchor_adrs nd i Hi.
Proof. exact: anchor_adrsE. Qed.

(* ------------------------------------------------------------------ *)
(** ** NODE-HASH AGREEMENT

    The games node hash at path [pos] IS the model's tweakable hash at
    node depth [size pos] and node index [idx_of_path pos]. *)

Lemma node_hashE (pp : PP_shrincs) (pos : seq bool) (x y : N_shrincs)
    (Hi : (Z.of_nat (idx_of_path pos) < 2 ^ 64)%Z) :
  fx_node_hash pp pos x y
  = encode16 (Model.fxmss.fxmss_H (decode16 pp) (size pos) (idx_of_path pos) Hi
                (decode16 x) (decode16 y)).
Proof.
rewrite /fx_node_hash /shrincs_fxmss_node_hash /Htree_sha256 /=.
by rewrite (tree_adrsE (size pos) (idx_of_path pos) Hi).
Qed.

(* ------------------------------------------------------------------ *)
(** ** ANCHOR (LEAF PUBLIC-KEY) AGREEMENT

    An FXMSS anchor is a WOTS+C instance whose chain starts are
    PRF-derived, which is exactly the shape [Sec.wots.model_bridge]'s
    [pubkey_gen_modelE] bridges.  The two developments' WOTS+C public
    keys are the SAME generic construction ([Sec.lib.wots.wotsc]) at the
    same addresses, so the only content here is the address dictionary
    and the PRF argument order. *)

Lemma leaf_secretE (pp : PP_shrincs) (ks : K_shrincs) (zi : nat * nat) :
  shrincs_fxmss_leaf_secret PP_shrincs N_shrincs K_shrincs PRFf_sha256 pp ks zi
  = Sec.wots.hop.prf.derive_sk (wc_sha256 zi.1 zi.2) K_shrincs PRF_sha256 pp ks.
Proof. by []. Qed.

Lemma leaf_pkE (pp : PP_shrincs) (ks : K_shrincs) (nd i : nat)
    (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  fx_leaf_pk pp ks ((h_sf - nd)%nat, i)
  = encode16 (Model.fxmss.fxmss_anchor (decode16 ks) (decode16 pp) nd i Hi).
Proof.
rewrite /fx_leaf_pk /shrincs_fxmss_leaf_public_key leaf_secretE /=.
have -> : shrincs_fxmss_wots_public_key PP_shrincs N_shrincs F_sha256 T_sf_sha256
            (h_sf - nd)%nat i pp
            (Sec.wots.hop.prf.derive_sk (wc_sha256 (h_sf - nd)%nat i) K_shrincs
               PRF_sha256 pp ks)
        = Sec.wots.scheme.shrincs_wots_pubkey (wc_sha256 (h_sf - nd)%nat i) pp
            (Sec.wots.hop.prf.derive_sk (wc_sha256 (h_sf - nd)%nat i) K_shrincs
               PRF_sha256 pp ks) by [].
rewrite pubkey_gen_modelE /Model.fxmss.fxmss_anchor.
by rewrite (A0_anchorE nd i Hi).
Qed.

(* ------------------------------------------------------------------ *)
(** ** ROOT AGREEMENT (the UXMSS spine)

    The spec's recommended stateful tree.  The induction runs down the
    spine: at every level the games tree is
    [BNode (uxmss_bt k) (BLeaf tt)] and the model recursion is at index
    0 (never an anchor until the bottom), whose right child is the
    index-1 anchor and whose left child is the rest of the spine.  The
    position dictionary [size pos <-> node_depth],
    [idx_of_path pos = 0] is maintained by [idx_of_path_rcons]. *)

(** Definitional view of the games root, so the induction below can be
    applied to it without a fold step. *)
Lemma fx_rootE (pp : PP_shrincs) (ks : K_shrincs) (t : bt unit) :
  fx_root pp ks t
  = val_bt (fx_node_hash pp) [::]
      (bt_posmap (fun p => fx_leaf_pk pp ks (shrincs_fxmss_pos_id h_sf p)) [::] t).
Proof. by []. Qed.

(** The node-hash dictionary with the position's coordinates named by
    the caller, so a proof can supply them already reduced. *)
Lemma node_hashE' (pp : PP_shrincs) (pos : seq bool) (nd i : nat)
    (x y : N_shrincs) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  size pos = nd -> idx_of_path pos = i ->
  fx_node_hash pp pos x y
  = encode16 (Model.fxmss.fxmss_H (decode16 pp) nd i Hi (decode16 x) (decode16 y)).
Proof. move=> hsz hidx; subst nd i; exact: node_hashE. Qed.

Lemma val_bt_uxmssE (pp : PP_shrincs) (ks : K_shrincs) (k : nat) :
  forall (pos : seq bool) (nd : nat)
    (Hd : ((nd + k)%coq_nat
             <= Model.fxmss.fxmss_max_depth
                  Model.fxmss.FXMSS_SHAPE_UNBALANCED)%coq_nat)
    (Hz : Model.fxmss.node_idx_ok Model.fxmss.FXMSS_SHAPE_UNBALANCED nd 0),
  size pos = nd -> idx_of_path pos = 0%nat ->
  val_bt (fx_node_hash pp) pos
    (bt_posmap (fun p => fx_leaf_pk pp ks (shrincs_fxmss_pos_id h_sf p)) pos (uxmss_bt k))
  = encode16 (Model.fxmss.fx_node Model.fxmss.FXMSS_SHAPE_UNBALANCED
                (decode16 ks) (decode16 pp) k nd 0 Hd Hz).
Proof.
elim: k => [|k IH] pos nd Hd Hz hsz hidx.
- (* bottom of the spine: the anchor at (nd, 0) *)
  have Hlt0 : (Z.of_nat 0 < 2 ^ 64)%Z
    := Model.fxmss.node_idx_ok_lt _ nd 0
         (Model.fxmss.fx_depth_here nd 0 _ Hd) Hz.
  rewrite (Model.theory.fxmss.fx_node_anchorE _ (decode16 ks) (decode16 pp)
             0 nd 0 Hd Hz Hlt0 (or_introl (@erefl nat 0))).
  rewrite [LHS]/= /shrincs_fxmss_pos_id hidx hsz.
  by rewrite (leaf_pkE pp ks nd 0 Hlt0).
- (* one level down: the sub-spine on the left, the index-1 anchor on the right *)
  have Hne : ~ Model.fxmss.fx_anchor_here Model.fxmss.FXMSS_SHAPE_UNBALANCED 0 by [].
  have Hlt : (Z.of_nat 0 < 2 ^ 64)%Z
    := Model.fxmss.node_idx_ok_lt _ nd 0
         (Model.fxmss.fx_depth_here nd k.+1 _ Hd) Hz.
  have Hdc : ((nd.+1 + k)%coq_nat
                <= Model.fxmss.fxmss_max_depth
                     Model.fxmss.FXMSS_SHAPE_UNBALANCED)%coq_nat
    := Model.fxmss.fx_depth_child nd k _ Hd.
  have Hzl : Model.fxmss.node_idx_ok Model.fxmss.FXMSS_SHAPE_UNBALANCED nd.+1 0
    := Model.fxmss.node_idx_ok_left _ nd 0 Hne Hz.
  have Hzr : Model.fxmss.node_idx_ok Model.fxmss.FXMSS_SHAPE_UNBALANCED nd.+1 1
    := Model.fxmss.node_idx_ok_right _ nd 0 Hne Hz.
  have Hlt1 : (Z.of_nat 1 < 2 ^ 64)%Z
    := Model.fxmss.node_idx_ok_lt _ nd.+1 1
         (Model.fxmss.fx_depth_here nd.+1 k _ Hdc) Hzr.
  have hszl : size (rcons pos false) = nd.+1 by rewrite size_rcons hsz.
  have hszr : size (rcons pos true) = nd.+1 by rewrite size_rcons hsz.
  have hidxl : idx_of_path (rcons pos false) = 0%nat
    by rewrite idx_of_path_rcons hidx.
  have hidxr : idx_of_path (rcons pos true) = 1%nat
    by rewrite idx_of_path_rcons hidx.
  rewrite (Model.theory.fxmss.fx_node_stepE' _ (decode16 ks) (decode16 pp)
             k nd 0 0 1 Hd Hz Hne Hlt Hdc Hzl Hzr erefl erefl).
  rewrite (Model.theory.fxmss.fx_node_anchorE _ (decode16 ks) (decode16 pp)
             k nd.+1 1 Hdc Hzr Hlt1 (or_intror (@erefl nat 1))).
  rewrite [LHS]/=.
  rewrite (IH (rcons pos false) nd.+1 Hdc Hzl hszl hidxl).
  rewrite /shrincs_fxmss_pos_id hidxr hszr.
  rewrite (leaf_pkE pp ks nd.+1 1 Hlt1).
  rewrite (node_hashE' pp pos nd 0 _ _ Hlt hsz hidx).
  rewrite (decode16_encode16_len _ (Model.theory.fxmss.fx_node_length _ _ _ _ _ _ _ _)).
  by rewrite (decode16_encode16_len _ (Model.theory.fxmss.fxmss_anchor_length _ _ _ _ _)).
Qed.

(** THE ROOT CORRESPONDENCE: at the spec's declared height, the games
    scheme's PKsf over the UXMSS spine of depth [k] IS the model's
    [fxmss_root] of the structure with that shape and depth. *)
Lemma root_uxmssE (pp : PP_shrincs) (ks : K_shrincs) (k : nat)
    (Hpos : (0 < k)%coq_nat)
    (Hmax : (k <= Model.fxmss.fxmss_max_depth
                    Model.fxmss.FXMSS_SHAPE_UNBALANCED)%coq_nat) :
  fx_root pp ks (uxmss_bt k)
  = encode16 (Model.fxmss.fxmss_root
                (Model.fxmss.mk_fxmss_structure
                   Model.fxmss.FXMSS_SHAPE_UNBALANCED k Hpos Hmax)
                (decode16 ks) (decode16 pp)).
Proof.
set st := Model.fxmss.mk_fxmss_structure
            Model.fxmss.FXMSS_SHAPE_UNBALANCED k Hpos Hmax.
rewrite fx_rootE
  (val_bt_uxmssE pp ks k [::] 0
     (Model.fxmss.fxmss_root_depth_ok st) (Model.fxmss.fxmss_root_idx_ok st)
     erefl erefl).
by congr encode16; exact: Model.theory.fxmss.fx_node_pirr.
Qed.

(** Delivery at the spec's recommended parameters is [root_uxmssE]
    instantiated at [k = 255]: shrincs.py's recommended stateful tree is
    the UXMSS spine of depth [FXMSS_HEIGHT = 255] (256 WOTS+C anchors),
    and [fxmss_max_depth FXMSS_SHAPE_UNBALANCED] is exactly 255, so the
    hypotheses are discharged by computation.  It is deliberately NOT
    spelled out as a separate corollary: at a NUMERAL depth the
    conversion check behind [congr] unfolds [fx_node] 255 levels deep
    and blows up, while at a variable [k] it is instant.  The
    spec-height statements live where they cost nothing --
    [Model.fxmss.fxmss_uxmss_at_spec_height] on the model side and
    [SHRINCS.fxmss.scheme.shrincs_fxmss_uxmss_at_spec_height] on the
    games side. *)

(* ------------------------------------------------------------------ *)
(** ** VERIFICATION AGREEMENT (the tree walk)

    The games verifier recomputes the root TOP-DOWN with [val_ap] along
    [path_of_idx (h_sf - z) i]; the model walks BOTTOM-UP along the
    reversed authentication path, reading each parent's depth off the
    remaining path length (shrincs.py :885-892).  The two agree.

    [val_ap_rcons] is the snoc view of [val_ap] that makes the two
    recursions line up: the games' DEEPEST hash is the model's FIRST
    step. *)

Lemma val_ap_rcons {A : eqType} (h : seq bool -> A -> A -> A)
    (pos p : seq bool) (b : bool) (ap : seq A) (s : A) (a : A) :
  size ap = size p ->
  val_ap h pos (rcons p b) (rcons ap s) a
  = val_ap h pos p ap (if b then h (pos ++ p) s a else h (pos ++ p) a s).
Proof.
elim: p pos ap => [|c p IH] pos [|x ap] //= hsz.
by rewrite cats0.
by rewrite (IH (rcons pos c) ap (succn_inj hsz)) cat_rcons.
Qed.

(** THE WALK CORRESPONDENCE.  [a] is the recovered anchor value (the
    WOTS+C half of the verifier, quantified here), [ap] the games'
    TOP-DOWN authentication path; the model consumes [rev ap]. *)
Lemma val_ap_walkE (pp : PP_shrincs) (p : seq bool) (ap : seq N_shrincs)
    (a : N_shrincs) (Hi : (Z.of_nat (idx_of_path p) < 2 ^ 64)%Z) :
  size ap = size p ->
  val_ap (fx_node_hash pp) [::] p ap a
  = Some (encode16 (Model.fxmss.fxmss_walk (decode16 pp) (idx_of_path p)
                      (decode16 a) (rev [seq decode16 x | x <- ap]) Hi)).
Proof.
elim/last_ind: p ap a Hi => [|p b IH] ap a Hi hsz.
- (* empty path: the walk returns the anchor value unchanged *)
  move: hsz => /size0nil ->.
  by rewrite -[RHS]/(Some (encode16 (decode16 a))) encode16_decode16.
- (* peel the games' DEEPEST hash, which is the model's FIRST step *)
  move: hsz; rewrite size_rcons.
  case/lastP: ap => [|ap s]; first by [].
  rewrite size_rcons => /succn_inj hsz.
  rewrite (val_ap_rcons _ [::] p b ap s a hsz) cat0s.
  have Hp : (Z.of_nat (idx_of_path p) < 2 ^ 64)%Z.
    have hle : (idx_of_path p <= idx_of_path (rcons p b))%coq_nat.
      by apply/leP; rewrite idx_of_path_rcons muln2 -addnn -addnA leq_addr.
    lia.
  rewrite (IH ap (if b then fx_node_hash pp p s a else fx_node_hash pp p a s) Hp hsz).
  congr (Some (encode16 _)).
  rewrite map_rcons rev_rcons.
  have Hh : (Z.of_nat (Nat.div2 (idx_of_path (rcons p b))) < 2 ^ 64)%Z
    by rewrite div2_idx_rcons.
  rewrite (Model.theory.fxmss.fxmss_walk_consE (decode16 pp) (idx_of_path (rcons p b))
             (decode16 a) (decode16 s) (rev [seq decode16 x | x <- ap]) Hi Hh).
  move: Hh;
    rewrite div2_idx_rcons odd_idx_rcons -size_lengthE size_rev size_map hsz => Hh.
  rewrite (Model.theory.fxmss.fxmss_walk_pirr _ _ _ _ Hh Hp).
  apply: (f_equal (fun nd : sha256.block =>
            Model.fxmss.fxmss_walk (decode16 pp) (idx_of_path p) nd
              (rev [seq decode16 x | x <- ap]) Hp)).
  clear Hi.
  case: b;
    by rewrite (node_hashE pp p _ _ Hp)
       (decode16_encode16_len _ (Model.theory.fxmss.fxmss_H_length _ _ _ _ _ _)).
Qed.
