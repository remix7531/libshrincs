(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.fxmss.model_bridge

    The games <-> model correspondence for the FXMSS TREE layer: the
    machine link between [SHRINCS.fxmss.scheme] (SSProve idiom --
    [seq], [bt], ordinals, an adversary-chosen shape, node positions as
    [seq bool] paths) and [Model.shrincs] (Stdlib idiom -- [list], [Z],
    22-byte WIRE addresses, the spec's own (node_height, node_index)
    recursion), through the per-node FXMSS views of
    [Model.theory.shrincs] section 6.  One level up from
    [Sec.wots.model_bridge], and reusing it for the WOTS+C anchors.

    ** What the bridge absorbs

    Five representation differences, none of them semantic:

    1. VALUES: games hash values are ordinals ([N_shrincs = 'fin
       (2^128)]); model ones are 16-byte strings.  Every statement
       QUANTIFIES the games value and DECODES it ([decode16]) -- never
       the reverse, exactly as in [Sec.wots.model_bridge].
    2. ADDRESSES: the games layer places address components through
       [Sec.addressing]'s exact-or-zero facade (bare [nat] in,
       dependent [fin] out); the port has no address TYPE at all -- it
       hashes the 22 wire bytes.  So the address statements below
       ([tree_adrsE] / [anchor_adrsE] / [A0_anchorE]) are equalities
       under [address.adrs_bytes], and they are the leaf-position <->
       ADRS agreement of the phase brief.
    3. COORDINATES: the games layer names a node by its path [pos] and
       hence by its DEPTH [size pos]; the port names it by its HEIGHT,
       with [FXMSS_HEIGHT - node_height] as the depth.  The dictionary
       is [h_sf - size pos <-> node_height] and
       [idx_of_path pos <-> node_index], and it is why the height side
       conditions ([nd + k <= h_sf], [size p <= h_sf]) are stated: [-]
       on [nat] truncates, so outside the declared height the two
       coordinate systems stop being inverse.
    4. TREE SHAPE: the games scheme evaluates an arbitrary [bt unit]
       over [seq bool] positions; [Model.theory.shrincs]'s [fx_node]
       runs the spec's recursion on (node_height, node_index) at ONE of
       the two spec shapes.  [root_uxmssE] is the two meeting at the
       spec's recommended UXMSS spine.
    5. AUTH-PATH ORIENTATION: the games layer stores authentication
       paths TOP-DOWN (root-side sibling first, [cons_ap]/[val_ap]);
       shrincs.py and hence [fx_walk] consume them BOTTOM-UP, one
       [nh + 1] at a time.  That is the [rev] in [val_ap_walkE].

    ** The one surviving bound proof

    The port carries no dependent fields and no invariant: an
    out-of-range node index serializes by TRUNCATION, which is what
    shrincs.py does.  So nothing below carries a MODEL-side invariant
    -- no tree-structure record, no index-range predicate, no
    proof-irrelevance lemma.  What survives is a GAMES-side exactness
    condition: [Sec.addressing] places an unrepresentable index as
    ZERO, not as its low 64 bits, so the two agree on an index only
    while it is representable.  That is the
    [Hi : Z.of_nat i < 2 ^ 64] the address, node-hash, leaf and walk
    statements still take, and it is the same kind of fact as the
    height conditions of point 3 -- a claim about where the games
    layer's totalization is exact, not about the port.

    ** The instantiation

    The games scheme is a [Section] over abstract building blocks, so
    the bridge fixes them at the concrete truncated-SHA-256 hashes of
    [Sec.axioms] -- [F_sha256], [T_sf_sha256] and [PRF_sha256] for the
    WOTS+C anchors, plus [Htree_sha256] here for the tree nodes -- and
    at [h_sf := 255], the spec's declared height (shrincs.py :60).  The
    port's [Model.shrincs.FXMSS_HEIGHT] is a [Z] and the games layer
    wants a [nat], so [h_sf] is spelled as the [nat] literal and
    [node_depthE] is the [Z]-level dictionary between them.  This is
    the same [wc_sha256] hash family the native WOTS+C tree's headline
    theorem is instantiated against, so the FXMSS leaves ARE the WOTS+C
    instances [Sec.wots.model_bridge] already bridged.

    ** Out of scope, and why

    - [Hmsg^sf] / [PRFmsg^stateful] and the SHRINCS-level cross-binding
      are deliberately not built (model/PORTING.md).  shrincs.py's
      [fxmss_sign] likewise takes a MESSAGE DIGEST, which is where this
      bridge cuts.
    - The WOTS+C leaf's SIGNATURE (as opposed to its public key) is not
      bridged here: [SHRINCS.wotsc.scheme] instantiates the generic
      WOTS+C construction at [dig_msb := false] (LSB-first grinding
      digits) while [Sec.wots.scheme], shrincs.py's base-w parse and
      [Model.shrincs.base_2b] are all MSB-first.  Public keys are digit
      order independent (every chain runs to [w-1]), so [leaf_pkE] and
      [root_uxmssE] are unaffected; a signature-level bridge would
      first have to reconcile that ordering.  Recorded as a finding.

    IMPORT DISCIPLINE (see [Sec.bridge] / [Sec.wots.model_bridge]
    headers, load-bearing): [BinInt] stays a plain [Import] and [Znat]
    a plain [Require] -- `Require Import ZArith` / `Require Import Znat`
    both silently shadow mathcomp's nat "^" ([expn] -> [Nat.pow]).
    Numeric comparisons take an explicit [%nat] annotation.
    [Model.shrincs] is reached QUALIFIED ([shrincs.foo]): the port's
    [len] is Python's [len] builtin at [Z] and would shadow. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude math.bin_tree math.merkle sig.scheme.
From SHRINCS Require Import addressing wotsc.scheme fxmss.scheme.
Set Warnings "notation-overridden,ambiguous-paths".
From Sec Require addressing.
Require Import Sec.wots.instantiation.
Require Import Sec.axioms.
Require Import Sec.wots.model_bridge.
From Model Require address fin sha256 shrincs.
Require Model.theory.shrincs.
(* See header IMPORT DISCIPLINE. *)
From Stdlib Require Import BinInt Lia.
From Stdlib Require Znat.

Import PackageNotation.
#[local] Open Scope package_scope.

(** The address type of the FXMSS games layer at the shrincs numbers. *)
Local Notation adrs_s :=
  (address.adrs chain_count_shrincs w_shrincs.-1).

(** The declared imaginary-tree height (shrincs.py [FXMSS_HEIGHT =
    255]).  The port states it at [Z]; the games layer's positions are
    [nat]s, so the bridge fixes the [nat] literal here and crosses to
    [shrincs.FXMSS_HEIGHT] through [h_sfZ] / [node_depthE]. *)
Local Notation h_sf := 255%nat.

(* ------------------------------------------------------------------ *)
(** ** The concrete FXMSS building blocks

    [F_sha256] / [T_sf_sha256] / [PRF_sha256] are [Sec.axioms]'; only
    the tree-node hash is new here.  H : B^n x B^288 x B^2n -> B^n is
    the spec's own tree-node hash [Model.shrincs.H] -- the same
    construction as every other SHRINCS tweakable hash -- fed the two
    children's concatenation (shrincs.py :807).  The address is
    serialized to its 22 wire bytes, which is what the port hashes; at
    a tree address that composite IS the port's [fx_H] ([node_hashE]). *)

Definition Htree_sha256 (pp : PP_shrincs) (a : adrs_s)
    (xy : N_shrincs * N_shrincs) : N_shrincs :=
  encode16 (shrincs.H (decode16 pp) (address.adrs_bytes a)
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
(** ** GLUE: the height dictionary

    A games DEPTH and a port HEIGHT add up to [h_sf], in whichever of
    the two numeric worlds the statement lives. *)

Lemma h_sfZ : Z.of_nat h_sf = 255%Z.
Proof. by []. Qed.

(** A node height is always [<= 255], so the games layer's one-byte
    height slot is filled EXACTLY -- no hypothesis needed. *)
Lemma height_lt_256 (nd : nat) : (Z.of_nat (h_sf - nd) < 256)%Z.
Proof.
have /leP/Znat.Nat2Z.inj_le := leq_subr nd h_sf.
rewrite h_sfZ; lia.
Qed.

(** The port's [node_depth] read off a games depth: the dictionary
    entry the UXMSS-spine unfoldings are gated on. *)
Lemma node_depthE (nd : nat) :
  (nd <= h_sf)%nat ->
  (shrincs.FXMSS_HEIGHT - Z.of_nat (h_sf - nd))%Z = Z.of_nat nd.
Proof.
move=> hnd.
rewrite -minusE Znat.Nat2Z.inj_sub; last exact/leP.
rewrite h_sfZ /shrincs.FXMSS_HEIGHT; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** GLUE: position arithmetic

    [idx_of_path] reads a path MSB-first, so appending one more step
    doubles the index -- the games-side counterpart of the model
    recursion's [i |-> 2i, 2i+1].  The port's walk halves with
    [Z.shiftr _ 1] and reads the low bit with [Z.land _ 1], so those
    are the two operations to read off a games path. *)

Lemma idx_of_path_rcons (p : seq bool) (b : bool) :
  idx_of_path (rcons p b) = (idx_of_path p * 2 + b)%nat.
Proof. by rewrite -cats1 idx_of_path_cat /=; case: b; rewrite ?addn0 ?muln2 ?addn1. Qed.

Lemma idx_of_path_rconsZ (p : seq bool) (b : bool) :
  Z.of_nat (idx_of_path (rcons p b))
  = (Z.of_nat (idx_of_path p) * 2 + Z.of_nat b)%Z.
Proof.
by rewrite idx_of_path_rcons -multE -plusE Znat.Nat2Z.inj_add Znat.Nat2Z.inj_mul.
Qed.

Lemma shiftr_idx_rcons (p : seq bool) (b : bool) :
  Z.shiftr (Z.of_nat (idx_of_path (rcons p b))) 1 = Z.of_nat (idx_of_path p).
Proof.
rewrite idx_of_path_rconsZ Z.shiftr_div_pow2; last lia.
rewrite Z.pow_1_r Z.div_add_l; last lia.
by case: b; rewrite Z.add_0_r.
Qed.

Lemma land_idx_rcons (p : seq bool) (b : bool) :
  (Z.land (Z.of_nat (idx_of_path (rcons p b))) 1 =? 1)%Z = b.
Proof.
have hl : forall a : Z, Z.land a 1 = (a mod 2)%Z.
  move=> a.
  have h : Z.land a (Z.ones 1) = (a mod 2 ^ 1)%Z by apply: Z.land_ones; lia.
  by rewrite Z.pow_1_r in h; exact: h.
rewrite idx_of_path_rconsZ hl.
case: b; first by apply/Z.eqb_eq; rewrite /= Z.add_comm Z.mod_add.
by rewrite /= Z.add_0_r Z.mod_mul.
Qed.

(** [decode16 o encode16 = id] at the FXMSS widths: every model value
    the bridge round-trips is a [thash] output, hence 16 bytes. *)
Lemma decode16_encode16_len (Y : sha256.block) :
  length Y = 16%nat -> decode16 (encode16 Y) = Y.
Proof. by move=> h; apply: decode16_encode16; rewrite size_lengthE h. Qed.

(* ------------------------------------------------------------------ *)
(** ** ADDRESS AGREEMENT (the leaf-position <-> ADRS stratum)

    The games layer's exact-or-zero placement of a representable
    (height, index), SERIALIZED, IS the port's 22-byte wire address.
    The height slot is filled from the node HEIGHT on both sides now;
    what the games layer calls [h_sf - nd] the port calls the node
    height, and [nd] is its [node_depth]. *)

Lemma tree_adrsE (nd i : nat) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  address.adrs_bytes
    (@addressing.fxmss_tree_adrs chain_count_shrincs w_shrincs (h_sf - nd)%nat i)
  = shrincs.fx_tree_adrs (Z.of_nat (h_sf - nd)) (Z.of_nat i).
Proof.
rewrite /addressing.fxmss_tree_adrs shrincs.adrs_bytes_fxmss.
by rewrite (addressing.fin_of_nat_or_zero_val _ _ _ (height_lt_256 nd))
           (addressing.fin_of_nat_or_zero_val _ _ _ Hi).
Qed.

Lemma anchor_adrsE (nd i : nat) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  address.adrs_bytes
    (@addressing.wc_pk_adrs chain_count_shrincs w_shrincs ((h_sf - nd)%nat, i))
  = shrincs.wc_pk_adrs (Z.of_nat (h_sf - nd)) (Z.of_nat i).
Proof.
rewrite /addressing.wc_pk_adrs shrincs.adrs_bytes_wc_pk /=.
by rewrite (addressing.fin_of_nat_or_zero_val _ _ _ (height_lt_256 nd))
           (addressing.fin_of_nat_or_zero_val _ _ _ Hi).
Qed.

(** The WOTS+C anchor address of [Sec.wots.model_bridge] ([A0], the
    carrier the native tree's pubkey correspondence is stated at) at a
    representable FXMSS leaf position IS the port's. *)
Lemma A0_anchorE (nd i : nat) (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  address.adrs_bytes (A0 (h_sf - nd)%nat i)
  = shrincs.wc_pk_adrs (Z.of_nat (h_sf - nd)) (Z.of_nat i).
Proof. exact: anchor_adrsE. Qed.

(* ------------------------------------------------------------------ *)
(** ** NODE-HASH AGREEMENT

    The games node hash at path [pos] IS the port's [fx_H] at node
    height [h_sf - size pos] and node index [idx_of_path pos]. *)

Lemma node_hashE (pp : PP_shrincs) (pos : seq bool) (x y : N_shrincs)
    (Hi : (Z.of_nat (idx_of_path pos) < 2 ^ 64)%Z) :
  fx_node_hash pp pos x y
  = encode16 (shrincs.fx_H (decode16 pp) (Z.of_nat (h_sf - size pos))
                (Z.of_nat (idx_of_path pos)) (decode16 x) (decode16 y)).
Proof.
rewrite /fx_node_hash /shrincs_fxmss_node_hash /Htree_sha256 /shrincs.fx_H /=.
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
  = encode16 (shrincs.fx_anchor (decode16 ks) (decode16 pp)
                (Z.of_nat (h_sf - nd)) (Z.of_nat i)).
Proof.
rewrite /fx_leaf_pk /shrincs_fxmss_leaf_public_key leaf_secretE /=.
have -> : shrincs_fxmss_wots_public_key PP_shrincs N_shrincs F_sha256 T_sf_sha256
            (h_sf - nd)%nat i pp
            (Sec.wots.hop.prf.derive_sk (wc_sha256 (h_sf - nd)%nat i) K_shrincs
               PRF_sha256 pp ks)
        = Sec.wots.scheme.shrincs_wots_pubkey (wc_sha256 (h_sf - nd)%nat i) pp
            (Sec.wots.hop.prf.derive_sk (wc_sha256 (h_sf - nd)%nat i) K_shrincs
               PRF_sha256 pp ks) by [].
rewrite pubkey_gen_modelE (A0_anchorE nd i Hi) /shrincs.wc_pk_adrs.
by rewrite shrincs.wots_c_pubkey_gen_fx_anchor.
Qed.

(* ------------------------------------------------------------------ *)
(** ** ROOT AGREEMENT (the UXMSS spine)

    The spec's recommended stateful tree.  The induction runs down the
    spine: at every level the games tree is
    [BNode (uxmss_bt k) (BLeaf tt)] and the port's recursion is at
    index 0 (never an anchor until the bottom), whose right child is
    the index-1 anchor and whose left child is the rest of the spine.
    The position dictionary [h_sf - size pos <-> node_height],
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
  = encode16 (shrincs.fx_H (decode16 pp) (Z.of_nat (h_sf - nd)) (Z.of_nat i)
                (decode16 x) (decode16 y)).
Proof. move=> hsz hidx; subst nd i; exact: node_hashE. Qed.

(** [td] is passed as a [Z] parameter rather than computed: the
    induction moves one level DOWN the spine ([nd] up, [k] down) while
    the tree depth both are measured against stays put, and naming it
    keeps that invariance out of the rewriting. *)
Lemma val_bt_uxmssE (pp : PP_shrincs) (ks : K_shrincs) (k : nat) :
  forall (pos : seq bool) (nd : nat) (td : Z),
  (nd + k <= h_sf)%nat -> td = Z.of_nat (nd + k) ->
  size pos = nd -> idx_of_path pos = 0%nat ->
  val_bt (fx_node_hash pp) pos
    (bt_posmap (fun p => fx_leaf_pk pp ks (shrincs_fxmss_pos_id h_sf p)) pos (uxmss_bt k))
  = encode16 (shrincs.fx_node (h_sf - nd)%nat shrincs.FXMSS_SHAPE_UNBALANCED td
                (decode16 ks) (decode16 pp) 0).
Proof.
elim: k => [|k IH] pos nd td Hd Htd hsz hidx.
- (* bottom of the spine: the anchor at (h_sf - nd, 0) *)
  have hnd : (nd <= h_sf)%nat by move: Hd; rewrite addn0.
  rewrite Htd addn0.
  rewrite (shrincs.fx_node_uxmss_anchor (Z.of_nat nd) (decode16 ks) (decode16 pp)
             (h_sf - nd)%nat 0 (or_intror (node_depthE nd hnd))).
  rewrite [LHS]/= /shrincs_fxmss_pos_id hidx hsz.
  by rewrite (leaf_pkE pp ks nd 0 (ltac:(lia) : (Z.of_nat 0 < 2 ^ 64)%Z)).
- (* one level down: the sub-spine on the left, the index-1 anchor on the right *)
  have hnd : (nd < h_sf)%nat.
    by apply: leq_trans Hd; rewrite addnS ltnS leq_addr.
  have hsub : (h_sf - nd)%nat = (h_sf - nd.+1).+1 by rewrite subnSK.
  have Hdc : (nd.+1 + k <= h_sf)%nat by rewrite addSn -addnS.
  have Htdc : td = Z.of_nat (nd.+1 + k) by rewrite addSn -addnS.
  have Hlt1 : (Z.of_nat 1 < 2 ^ 64)%Z by lia.
  have Hlt0 : (Z.of_nat 0 < 2 ^ 64)%Z by lia.
  (* this node is NOT the bottom: its depth is short of the tree depth *)
  have Hne : (shrincs.FXMSS_HEIGHT - Z.of_nat (h_sf - nd.+1).+1)%Z <> td.
    rewrite -hsub (node_depthE nd (ltnW hnd)) Htd -plusE Znat.Nat2Z.inj_add.
    lia.
  rewrite hsub (shrincs.fx_node_uxmss_step td (decode16 ks) (decode16 pp)
                  (h_sf - nd.+1)%nat Hne) -hsub.
  rewrite (shrincs.fx_node_uxmss_anchor td (decode16 ks) (decode16 pp)
             (h_sf - nd.+1)%nat 1 (or_introl erefl)).
  have hszl : size (rcons pos false) = nd.+1 by rewrite size_rcons hsz.
  have hszr : size (rcons pos true) = nd.+1 by rewrite size_rcons hsz.
  have hidxl : idx_of_path (rcons pos false) = 0%nat
    by rewrite idx_of_path_rcons hidx.
  have hidxr : idx_of_path (rcons pos true) = 1%nat
    by rewrite idx_of_path_rcons hidx.
  rewrite [LHS]/=.
  rewrite (IH (rcons pos false) nd.+1 td Hdc Htdc hszl hidxl).
  rewrite /shrincs_fxmss_pos_id hidxr hszr.
  rewrite (leaf_pkE pp ks nd.+1 1 Hlt1).
  rewrite (node_hashE' pp pos nd 0 _ _ Hlt0 hsz hidx).
  rewrite (decode16_encode16_len _ (shrincs.length_fx_node _ _ _ _ _ _)).
  by rewrite (decode16_encode16_len _ (shrincs.length_fx_anchor _ _ _ _)).
Qed.

(** THE ROOT CORRESPONDENCE: at the spec's declared height, the games
    scheme's PKsf over the UXMSS spine of depth [k] IS the port's
    [fx_root] at the unbalanced shape and that depth.  The dependent
    [fxmss_structure] the retired model demanded is gone; [k <= h_sf]
    is what genuinely survives of it, and it is the coordinate
    dictionary's own condition, not a shape invariant. *)
Lemma root_uxmssE (pp : PP_shrincs) (ks : K_shrincs) (k : nat)
    (Hk : (k <= h_sf)%nat) :
  fx_root pp ks (uxmss_bt k)
  = encode16 (shrincs.fx_root shrincs.FXMSS_SHAPE_UNBALANCED (Z.of_nat k)
                (decode16 ks) (decode16 pp)).
Proof.
have hd : (0 + k <= h_sf)%nat by rewrite add0n.
have htd : Z.of_nat k = Z.of_nat (0 + k) by rewrite add0n.
have hh : (h_sf - 0)%nat = Z.to_nat shrincs.FXMSS_HEIGHT by rewrite subn0.
by rewrite fx_rootE (val_bt_uxmssE pp ks k [::] 0 (Z.of_nat k) hd htd erefl erefl)
           /shrincs.fx_root hh.
Qed.

(** Delivery at the spec's recommended parameters is [root_uxmssE]
    instantiated at [k = 255]: shrincs.py's recommended stateful tree is
    the UXMSS spine of depth [FXMSS_HEIGHT = 255] (256 WOTS+C anchors).
    It is deliberately NOT spelled out as a separate corollary: at a
    NUMERAL depth the conversion check unfolds [fx_node] 255 levels
    deep and blows up, while at a variable [k] it is instant.  The
    spec-height statement lives where it costs nothing --
    [SHRINCS.fxmss.scheme.shrincs_fxmss_uxmss_at_spec_height] on the
    games side. *)

(* ------------------------------------------------------------------ *)
(** ** VERIFICATION AGREEMENT (the tree walk)

    The games verifier recomputes the root TOP-DOWN with [val_ap] along
    [path_of_idx (h_sf - z) i]; the port walks BOTTOM-UP, starting at
    the leaf's own height and adding one per level (shrincs.py
    :885-892).  The two agree.

    [val_ap_rcons] is the snoc view of [val_ap] that makes the two
    recursions line up: the games' DEEPEST hash is the port's FIRST
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

(** One step of the port's walk, as an equation.  Belongs next to
    [fx_walk] in [Model.theory.shrincs]; kept local because that file
    is owned elsewhere. *)
