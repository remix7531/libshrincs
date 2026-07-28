(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.leaf2_common

    Structure-independent support for the second FXMSS leaf hop over the
    shared game [MIW_km]. Multi-target reductions commit every leaf, so
    their target-freshness obligations depend on cross-leaf uniqueness:

    - [l2_panchor_inj] gives distinct public-key-compression tweaks for
      distinct leaves;
    - [l2_chain_inj] gives distinct chain tweaks for distinct leaf, chain,
      and position coordinates.

    Both results follow from [encode_adrs], the structured-address
    injectivity lemmas, and [shrincs_fxmss_pos_id_inj]. The target builders
    [leafcommitq], [qmap_from], and [getm_leafcommitq] live in
    [fxmss.leaf_reduction] and are shared by the per-assumption bounds. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From HBS Require Import prelude math.bin_tree math.merkle math.chain math.encoding
  sig.scheme games.thf games.smtcr toolkit.sample_seq.
From HBS Require Import wots.games wots.tcr_hop.
From Model Require Import fin.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop
  fxmss.leaf_reduction fxmss.leaf_km.
From mathcomp Require Import all_boot all_order.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section leaf2_common.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same data-only section context as [fxmss.leaf_km]. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (Hh : (h_sf <= 64)%N).
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (n0 : N) (d0 : D).

(* ------------------------------------------------------------------ *)
(** ** Shorthands (LeafKM's / LeafReduction's). *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation panchor p :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (posid p))).
Local Notation lchaintw p c pos :=
  (@encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w (posid p) c pos)).

(* ------------------------------------------------------------------ *)
(** ** Finite-address projection facts *)

Lemma l2_fin256_bounded (z : fin (BinInt.Z.of_nat 256)) :
  BinInt.Z.lt (BinInt.Z.of_nat (BinInt.Z.to_nat (fin_val z)))
    (BinInt.Z.of_nat 256).
Proof.
have [hz0 hz256] := fin_range z.
by rewrite Znat.Z2Nat.id.
Qed.

Lemma l2_layer_bounded (z : fin address.hypertree_layers) :
  BinInt.Z.lt (BinInt.Z.of_nat (BinInt.Z.to_nat (fin_val z)))
    (BinInt.Z.of_nat 256).
Proof.
have [hz0 _] := fin_range z.
rewrite Znat.Z2Nat.id //.
exact: (address.fin6_lt_256 z).2.
Qed.

Lemma l2_fin64_bounded
    (i : fin (BinInt.Z.pow (BinInt.Z.of_nat 2) (BinInt.Z.of_nat 64))) :
  BinInt.Z.lt (BinInt.Z.of_nat (BinInt.Z.to_nat (fin_val i)))
    (BinInt.Z.pow (BinInt.Z.of_nat 2) (BinInt.Z.of_nat 64)).
Proof.
have [hi0 hi64] := fin_range i.
by rewrite Znat.Z2Nat.id.
Qed.

Lemma l2_lcoord_bounded (t : adrs_sf_ch) :
  anchor_bounded (@leaf_km.lcoord w l t).
Proof.
rewrite /leaf_km.lcoord /anchor_bounded /adrs_keypair
  /adrs_height /adrs_index.
case: (decode_tweak t) => * /=; split;
  first [exact: l2_fin256_bounded | exact: l2_layer_bounded |
         exact: l2_fin64_bounded].
Qed.

Lemma l2_lcoord_chain (zi : nat * nat) (c pos : nat) :
  anchor_bounded zi ->
  component_bounded l c -> component_bounded w.-1 pos ->
  @leaf_km.lcoord w l
      (@encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w zi c pos)) = zi.
Proof.
move=> hzi hc hpos.
rewrite /leaf_km.lcoord decode_tweakK
  (shrincs_fxmss_wots_chain_adrsE l w zi c pos hzi hc hpos).
case: zi hzi => z i hzi.
cbv [addressing.adrs_keypair addressing.adrs_height addressing.adrs_index].
by rewrite !Znat.Nat2Z.id.
Qed.

Lemma l2_lcoord_pk (zi : nat * nat) :
  anchor_bounded zi ->
  @leaf_km.lcoord w l (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w zi)) = zi.
Proof.
move=> hzi; rewrite /leaf_km.lcoord decode_tweakK.
exact: (shrincs_fxmss_wots_pk_adrs_keypair l w zi hzi).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf-path size bound (LeafReduction's [leaf_path_size], re-derived
    self-contained from the shape machinery). *)

Lemma l2_leaf_path_size sp (p : seq bool) :
  p \in leaf_paths (tshape sp) -> (size p <= h_sf)%N.
Proof.
move=> hp.
have hla : leaf_at (tshape sp) p = Some tt.
  by rewrite /leaf_at (@leaf_paths_subtree (tshape sp) p hp).
have h1 := leaf_at_size hla.
exact: leq_trans h1 (shrincs_fxmss_shape_wf h_sf sp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** CROSS-LEAF unique-tweak backbone *)

(** Distinct leaves give distinct pk tweaks (the SM-TCR(Theta_l) target
    set; = LeafReduction's [panchor_inj_leaf], re-derived here). *)
Lemma l2_panchor_inj sp (p q : seq bool) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  panchor p = panchor q -> p = q.
Proof.
move=> hp hq /encode_adrs_inj he.
have hps := l2_leaf_path_size sp p hp.
have hqs := l2_leaf_path_size sp q hq.
have [e1 e2] := @shrincs_fxmss_wots_pk_adrs_inj l w (posid p).1 (posid p).2
  (posid q).1 (posid q).2
  (shrincs_fxmss_path_anchor_bounded h_sf p Hh hps)
  (shrincs_fxmss_path_anchor_bounded h_sf q Hh hqs) he.
apply: (shrincs_fxmss_pos_id_inj h_sf p q (l2_leaf_path_size sp p hp)
          (l2_leaf_path_size sp q hq)).
by rewrite [posid p]surjective_pairing [posid q]surjective_pairing e1 e2.
Qed.

(** Distinct (leaf, chain, position) give distinct chain tweaks (the
    SM-UD(F) / SM-TCR(F) / SM-PRE(F) target set).  This is the NEW
    cross-leaf chain-tweak injectivity (combining [shrincs_fxmss_wots_chain_adrs_inj] with
    [shrincs_fxmss_pos_id_inj]) the multi-target chain reductions need. *)
Lemma l2_chain_inj sp (p q : seq bool) (c pos c' pos' : nat) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  component_bounded l c -> component_bounded w.-1 pos ->
  component_bounded l c' -> component_bounded w.-1 pos' ->
  lchaintw p c pos = lchaintw q c' pos' ->
  [/\ p = q, c = c' & pos = pos'].
Proof.
move=> hp hq hc hpos hc' hpos' /encode_adrs_inj he.
have hps := l2_leaf_path_size sp p hp.
have hqs := l2_leaf_path_size sp q hq.
have [e1 e2 e3 e4] := @shrincs_fxmss_wots_chain_adrs_inj l w
  (posid p).1 (posid p).2 c pos
  (posid q).1 (posid q).2 c' pos'
  (shrincs_fxmss_path_anchor_bounded h_sf p Hh hps)
  (shrincs_fxmss_path_anchor_bounded h_sf q Hh hqs)
  hc hpos hc' hpos' he.
have hpq : p = q.
  apply: (shrincs_fxmss_pos_id_inj h_sf p q (l2_leaf_path_size sp p hp)
            (l2_leaf_path_size sp q hq)).
  by rewrite [posid p]surjective_pairing [posid q]surjective_pairing e1 e2.
by split.
Qed.

(** Corollary in the contrapositive form the SM-* freshness side
    conditions ([t \notin tws]) are discharged with: distinct
    coordinates force distinct tweaks. *)
Lemma l2_panchor_neq sp (p q : seq bool) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  p <> q -> panchor p <> panchor q.
Proof. by move=> hp hq hne /(l2_panchor_inj sp p q hp hq). Qed.

Lemma l2_chain_neq sp (p q : seq bool) (c pos c' pos' : nat) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  component_bounded l c -> component_bounded w.-1 pos ->
  component_bounded l c' -> component_bounded w.-1 pos' ->
  (p, c, pos) <> (q, c', pos') -> lchaintw p c pos <> lchaintw q c' pos'.
Proof.
move=> hp hq hc hpos hc' hpos' hne.
move=> /(l2_chain_inj sp p q c pos c' pos' hp hq
  hc hpos hc' hpos') [ep ec epos].
by apply: hne; rewrite ep ec epos.
Qed.

End leaf2_common.
