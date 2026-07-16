(** * SHRINCS.FXMSS.Leaf2Common

    M-int ROOT for the FXMSS leaf hop LAYER (ii), over the now-corrected
    (slog-gated EU-CMA) banked game [MIW_km] (FXMSS.LeafKM).

    This file banks the STRUCTURE-INDEPENDENT M-int sub-pieces that every
    layer-(ii) SM-* sub-bound (M-cp / M-gr / M-ct / M-pr / M-ud) consumes
    regardless of the concrete intermediate-game shape: the CROSS-LEAF
    unique-tweak backbone (the multi-target freshness guarantee).  A
    multi-target SM-* reduction commits ALL leaves as its target set; the
    per-game `t \notin tws` (target freshness) discharges exactly because
    distinct (leaf, chain, position) coordinates produce distinct ENCODED
    address tweaks:

    - [l2_panchor_inj] : distinct leaves give distinct pk tweaks [AdrPk]
      (the SM-TCR(Theta_l) target set);
    - [l2_chain_inj]   : distinct (leaf, chain, position) give distinct
      chain tweaks [AdrChain] (the SM-UD(F)/SM-TCR(F)/SM-PRE(F) target set).

    Both are derived from the primitive [encode_adrs] / [AdrPk] / [AdrChain]
    injectivity (Addressing.v) + [pos_id_inj] (FXMSS.Scheme), self-contained
    in this file's section context (= LeafKM.v's), so the sub-bound files can
    [Require] just this root.

    STATUS (M-int): the cross-leaf uniqueness backbone is admit-free here.
    The CONCRETE intermediate games [game I_MIW_km] (the other M-int
    component) are NOT in this file: they are definable but require a
    [find_ctr]-conditional re-root (signed-digit re-root for grinding
    leaves so LSIGN reveals the re-rooted roots directly; virtual-digit
    re-root for non-grinding / never-signed leaves) AND Gmid-lift nulling
    discriminants that thread the slog-gating
    [(j \notin slog) || (mw.1 != md0)] (so the grind/compress/chain nulls
    fire only on genuine collisions, not on an unsigned leaf's chain-break
    at its own committed digest).  That is a large, intricate build and is
    deferred; see the work-log in LEAF_LAYER2_PLAN.md.  The all-leaves
    target builders ([leafcommitq] / [qmap_from] / [getm_leafcommitq]) are
    banked in FXMSS.LeafReduction and reusable verbatim by the sub-bounds. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From HBS Require Import Prelude Math.BinTree Math.Merkle Math.Chain Math.Encoding
  Sig.Scheme Games.THF Games.SMTCR Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Games FixedSumOTS.TCRHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames FXMSS.TreeHop
  FXMSS.LeafReduction FXMSS.LeafKM.
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Leaf2Common.

(** Same DATA-ONLY section context as FXMSS/LeafKM.v. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (w l S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (n0 : N) (d0 : D).

(* ------------------------------------------------------------------ *)
(** ** Shorthands (LeafKM's / LeafReduction's). *)

Local Notation tshape := (shape_of h_sf).
Local Notation posid := (pos_id h_sf).
Local Notation panchor p := (encode_adrs (AdrPk (posid p).1 (posid p).2)).
Local Notation lchaintw p c pos :=
  (encode_adrs (AdrChain (posid p).1 (posid p).2 c pos)).

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
exact: leq_trans h1 (wf_shape_of h_sf sp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** CROSS-LEAF unique-tweak backbone *)

(** Distinct leaves give distinct pk tweaks (the SM-TCR(Theta_l) target
    set; = LeafReduction's [panchor_inj_leaf], re-derived here). *)
Lemma l2_panchor_inj sp (p q : seq bool) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  panchor p = panchor q -> p = q.
Proof.
move=> hp hq /encode_adrs_inj /AdrPk_inj [e1 e2].
apply: (pos_id_inj h_sf p q (l2_leaf_path_size sp p hp)
          (l2_leaf_path_size sp q hq)).
by rewrite [posid p]surjective_pairing [posid q]surjective_pairing e1 e2.
Qed.

(** Distinct (leaf, chain, position) give distinct chain tweaks (the
    SM-UD(F) / SM-TCR(F) / SM-PRE(F) target set).  This is the NEW
    cross-leaf chain-tweak injectivity (combining [AdrChain_inj] with
    [pos_id_inj]) the multi-target chain reductions need. *)
Lemma l2_chain_inj sp (p q : seq bool) (c pos c' pos' : nat) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  lchaintw p c pos = lchaintw q c' pos' ->
  [/\ p = q, c = c' & pos = pos'].
Proof.
move=> hp hq /encode_adrs_inj /AdrChain_inj [e1 e2 e3 e4].
have hpq : p = q.
  apply: (pos_id_inj h_sf p q (l2_leaf_path_size sp p hp)
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
  (p, c, pos) <> (q, c', pos') -> lchaintw p c pos <> lchaintw q c' pos'.
Proof.
move=> hp hq hne /(l2_chain_inj sp p q c pos c' pos' hp hq) [ep ec epos].
by apply: hne; rewrite ep ec epos.
Qed.

End Leaf2Common.
