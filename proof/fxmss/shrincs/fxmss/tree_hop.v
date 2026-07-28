(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.tree_hop

    Hop 7 (F.8 -> F.9, [claim:fxmss-tree-tcr]): nulling the [FColl]
    forgery verdicts is bounded by the SM-TCR advantage of the tree-node
    hash [Htree],

      [Tree_hop (b = true) A VA :
         Adv (G6f true) (G7f true) A
           = AdvOf (SMTCR_game Th Cth (n_max - 1)) (A ∘ R_tree)].

    This file defines [Th] and [Cth] and proves the pure collision and
    target-bookkeeping facts consumed by [R_tree]. A verifying [FColl]
    forgery yields, via [merkle.extractP], a collision between the forged
    and honest children of an internal node. The internal-node target
    positions are exactly those of the shape, have depth at most [h_sf],
    use pairwise-distinct [shrincs_fxmss_adr_tree] tweaks, and number at most
    [n_max - 1].

    [Th] evaluates [Htree] at a tree-stateful address through the
    proven-cancelling [decode_tweak]. [Cth] exposes [F], [Tl], and
    [Hgrind], allowing the reduction to construct the WOTS+C anchors and
    grind under the hidden [pp] before [GETPP].

    [fxmss.tree_hop_proof] defines [R_tree], proves its real and ideal
    perfect simulations, and assembles [Tree_hop]. The [b = false]
    direction is observational equality because both forge oracles return
    false. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From Sec.lib Require Import prelude math.bin_tree math.merkle.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme games.thf games.smtcr toolkit.sample_seq.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.

Section FXMSSTreeHop.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same section context as [fxmss.late_games]. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (Hh : (h_sf <= 255)%N).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(* ------------------------------------------------------------------ *)
(** ** Shorthands *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation valtree := (value_tree_x PP N F Tl h_sf).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).
Local Notation fxvermd :=
  (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation frecover := (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind).
Local Notation shrincs_fxmss_forgery_case_at_N :=
  (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf).

(* ------------------------------------------------------------------ *)
(** ** The thf [Th] for the tree-node hash (the proof architecture "Tree hop")

    [th_T := adrs_sf_ch], [th_M := N × N] (the two children), evaluated
    by [Htree] at the decoded address; the answer at an encoded
    [shrincs_fxmss_adr_tree] tweak is exactly [shrincs_fxmss_node_hash] ([th_evalE_Th]). *)

Definition Th : thf :=
  {| th_PP := PP ; th_T := adrs_sf_ch ; th_M := N × N ; th_N := N ;
     th_eval := fun pp t xy => Htree pp (decode_tweak t) xy ;
     th_dPP := dPP ;
     th_dM := {code x ← dN ;; y ← dN ;; ret ((x, y) : N × N) } ;
     th_dN := dN |}.

(** [Cth]: the leaf-layer collection — [F] (chain steps), [Tl]
    (compression) and [Hgrind] (grinding), summed on the message side
    so one [tc_eval] dispatches all three under the shared (hidden)
    [pp], following the [Cf]/[Cpk] collection pattern in
    [SHRINCS.wotsc.games]. *)

Definition Cth : thf_coll Th :=
  Build_thf_coll Th adrs_sf_ch (N ∐ (('list N) ∐ (D × 'nat))) (N ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr (inl xs) => inl (Tl pp (decode_tweak t) xs)
       | inr (inr dc) => inr (Hgrind pp (decode_tweak t) dc : 'nat)
       end).

(** Sanity: on an encoded [shrincs_fxmss_adr_tree] tweak [Th] evaluates [shrincs_fxmss_node_hash]
    (the verifier's tree hash). *)
Lemma th_evalE_Th pp (z i : nat) (xy : N * N) :
  th_eval Th pp (encode_adrs (shrincs_fxmss_adr_tree z i)) xy = Htree pp (shrincs_fxmss_adr_tree z i) xy.
Proof. by rewrite /= decode_tweakK. Qed.

Lemma node_hash_Th pp (pos : seq bool) (x y : N) :
  th_eval Th pp (encode_adrs (shrincs_fxmss_tree_node_adrs (h_sf - size pos)
                                (idx_of_path pos))) (x, y)
  = nhash pp pos x y.
Proof. by rewrite /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the FColl forgery yields an SM-TCR collision

    A verifying forgery with [shrincs_fxmss_forgery_case = FColl q x y] gives a hash
    collision at an internal node [q] of the honest value tree:
    [nhash pp q x.1 x.2 = nhash pp q y.1 y.2] with [x <> y] and [y]
    the honest children values at [q].  This is exactly [extractP]'s
    FColl branch applied to the verification equation. *)

(** The verify equation extracted from [fxvermd]'s 4th conjunct, in
    the shape [extractP] consumes (h := nhash pp, t := honest tree). *)
Lemma shrincs_fxmss_verify_md_val_ap pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  val_ap (nhash pp) [::] (path_of_idx (h_sf - zi.1) zi.2) ap
         (frecover pp zi md ws)
  = Some (val_bt (nhash pp) [::] (valtree pp sp xss)).
Proof.
rewrite /shrincs_fxmss_verify_md => /and4P[_ _ _ /eqP].
by rewrite /shrincs_fxmss_root_x.
Qed.

(** The FColl extraction: position [q], the colliding inputs [x] and
    the honest children [y], the collision and the disequality. *)
Lemma shrincs_fxmss_forgery_case_FColl pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) (q : seq bool) (x y : N * N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  shrincs_fxmss_forgery_case_at_N pp sp xss zi md ws ap = FColl q x y ->
  exists qrel ltr,
    [/\ q = qrel,
        subtree_at (valtree pp sp xss) qrel = Some (BNode ltr.1 ltr.2),
        y = (val_bt (nhash pp) (rcons q false) ltr.1,
             val_bt (nhash pp) (rcons q true) ltr.2),
        nhash pp q x.1 x.2 = nhash pp q y.1 y.2 & x <> y].
Proof.
move=> hver hcase.
have hval := shrincs_fxmss_verify_md_val_ap _ _ _ _ _ _ _ hver.
have hok := extractP hval.
have heq : extract (nhash pp) [::] (valtree pp sp xss)
             (path_of_idx (h_sf - zi.1) zi.2) ap (frecover pp zi md ws)
           = FColl q x y by exact: hcase.
rewrite heq in hok.
move: hok => [qrel [lr [rr [hq hsub hy hcol hne]]]].
rewrite cat0s in hq; subst qrel.
by exists q, (lr, rr); split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Internal-node bookkeeping (the SM-TCR target list)

    The reduction commits one SM-TCR target per internal node of the
    honest VALUE tree, in [internal_paths] order.  [bt_posmap]
    preserves shape, so [internal_paths (valtree ...) = internal_paths
    (tshape sp)] ([internal_paths_valtree]); the targets are pairwise
    distinct because the [shrincs_fxmss_adr_tree]-tweaks are ([node_adrs_inj_paths]),
    and there are [#internal nodes = #leaves - 1] of them, all bounded
    by [n_max - 1] for a capped shape. *)

(** Generic: [internal_paths] only depends on the tree's shape, so
    decorating leaves ([bt_posmap]) does not change it. *)
Lemma internal_paths_posmap {A B : Type} (f : seq bool -> B)
    (pos : seq bool) (t : bt A) :
  internal_paths (bt_posmap f pos t) = internal_paths t.
Proof.
elim: t pos => [a|tl IHl tr IHr] pos //=.
by rewrite IHl IHr.
Qed.

Lemma internal_paths_valtree pp sp xss :
  internal_paths (valtree pp sp xss) = internal_paths (tshape sp).
Proof. by rewrite /value_tree_x internal_paths_posmap. Qed.

(** Every internal position of the value tree has size <= h_sf (it is
    a position of a well-formed shape; [internal_path_depth] is
    Sec.lib.math.bin_tree's generic depth bound). *)
Lemma internal_path_size sp (q : seq bool) :
  q \in internal_paths (tshape sp) -> (size q <= h_sf)%N.
Proof.
move=> hq.
have hlt := internal_path_depth hq.
have hd := shrincs_fxmss_shape_wf h_sf sp.
by apply: leq_trans (ltnW hlt) hd.
Qed.

(** Internal-position lists are duplicate-free (the cons-prefix
    structure of [internal_paths] forbids repeats). *)
Lemma internal_paths_uniq {A : Type} (t : bt A) :
  uniq (internal_paths t).
Proof.
elim: t => [a|tl IHl tr IHr] //.
have -> : internal_paths (BNode tl tr)
  = [::] :: ([seq false :: q | q <- internal_paths tl]
             ++ [seq true :: q | q <- internal_paths tr]) by [].
rewrite cons_uniq; apply/andP; split.
- rewrite mem_cat negb_or; apply/andP; split.
  + by apply/negP => /mapP[q _].
  + by apply/negP => /mapP[q _].
- rewrite cat_uniq !map_inj_uniq ?IHl ?IHr //=; first last.
  + by move=> p q [].
  + by move=> p q [].
  rewrite andbT; apply/hasPn => z /mapP[q _ ->].
  by apply/negP => /mapP[q' _].
Qed.

(** The committed-target order and its key facts: the [shrincs_fxmss_adr_tree]
    tweaks along [internal_paths] are pairwise distinct (the
    distinctness side condition every SM-TCR commit needs). *)
Definition tnode_tw (q : seq bool) : adrs_sf_ch :=
  encode_adrs (shrincs_fxmss_tree_node_adrs (h_sf - size q) (idx_of_path q)).

Lemma tnode_tw_inj sp (p q : seq bool) :
  p \in internal_paths (tshape sp) -> q \in internal_paths (tshape sp) ->
  tnode_tw p = tnode_tw q -> p = q.
Proof.
move=> hp hq.
rewrite /tnode_tw => /encode_adrs_inj he.
have hps := shrincs_fxmss_internal_pos_ok h_sf sp p hp.
have hqs := shrincs_fxmss_internal_pos_ok h_sf sp q hq.
exact: (@shrincs_fxmss_node_adrs_inj w l h_sf p q Hh hps hqs he).
Qed.

(** The committed tweak list is duplicate-free. *)
Lemma tnode_tws_uniq sp :
  uniq [seq tnode_tw q | q <- internal_paths (tshape sp)].
Proof.
rewrite map_inj_in_uniq; first exact: internal_paths_uniq.
by move=> p q hp hq; apply: (@tnode_tw_inj sp p q hp hq).
Qed.

(** Target-count budget (SM-TCR's [p := n_max - 1]): the number of
    internal nodes is one less than the number of leaves
    ([size_internal_paths]); for a capped shape ([n_a <= n_max], the
    GEN assert) this is at most [n_max - 1]. *)
Lemma bt_nleaves_pos {A : Type} (t : bt A) : (0 < bt_nleaves t)%N.
Proof. by elim: t => [a|tl IHl tr IHr] //=; rewrite addn_gt0 IHl. Qed.

Lemma size_internal_paths {A : Type} (t : bt A) :
  size (internal_paths t) = (bt_nleaves t).-1.
Proof.
elim: t => [a|tl IHl tr IHr] //=.
rewrite size_cat !size_map IHl IHr.
have hl := bt_nleaves_pos tl.
have hr := bt_nleaves_pos tr.
rewrite -(prednK hl) -(prednK hr) addSn addnS /=.
by rewrite -addnS prednK.
Qed.

Lemma internal_count_cap sp :
  (size (leaf_paths (tshape sp)) <= n_max)%N ->
  (size (internal_paths (tshape sp)) <= n_max - 1)%N.
Proof.
rewrite size_leaf_paths size_internal_paths => hcap.
rewrite -subn1; apply: leq_sub2r.
exact: hcap.
Qed.

End FXMSSTreeHop.
