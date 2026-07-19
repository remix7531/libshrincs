(** * SHRINCS.FXMSS.TreeHop

    Hop 7 (F.8 -> F.9, [claim:fxmss-tree-tcr]; PROOF_PLAN.md "Tree hop
    (7)"): nulling the FColl forgery verdicts is bounded by the SM-TCR
    advantage of the tree-node hash [Htree],

      [Tree_hop (b = true) A VA :
         Adv (G6f true) (G7f true) A
           = AdvOf (SMTCR_game Th Cth (n_max - 1)) (A ∘ R_tree)].

    ** STATUS / scope of THIS file

    Delivered and Qed-closed (no Admitted/Axiom/Hypothesis): the thf
    [Th] and collection [Cth] under attack, and the COMPLETE PURE LAYER
    the [R_tree] reduction consumes —

      - [fxcase_FColl]: a verifying FColl forgery yields, via
        [Merkle.extractP], the SM-TCR collision data ([q] an honest
        internal node, the colliding inputs [x] and honest children
        [y], [nhash pp q x.1 x.2 = nhash pp q y.1 y.2], [x <> y]);
      - the internal-node SM-TCR target bookkeeping: the value tree's
        internal positions are exactly the shape's ([internal_paths_
        valtree]), all of size <= h_sf ([internal_path_size]), the
        [AdrTree]-tweaks are pairwise distinct ([tnode_tw_inj],
        [tnode_tws_uniq]) and number [n_a - 1 <= n_max - 1]
        ([size_internal_paths], [internal_count_cap]) — the SM-TCR
        budget [p := n_max - 1] of the statement.

    The [R_tree] reduction PACKAGE and the two [perfect] lemmas
    ([R_tree ∘ SMTCR-real ≈ G6f true], [R_tree ∘ SMTCR-ideal ≈
    G7f true]) that assemble [Tree_hop] via [Adv_perfect_l/r] +
    [Adv_reduction] (WOTSC/Theorem.v idiom, ~line 101) are the
    remaining step (a WOTSC/ChainHop-scale relational proof: the
    bottom-up tree construction through TQUERY coupled with G6f's pure
    root, under the COLLQ pin).  All the spec each side of that proof
    consumes is in this file.

    The [b = false] direction of the hop is trivial ([G6f false] and
    [G7f false] both have the constant-false FORGE — observationally
    equal, [Adv = 0]); it is discharged at telescope assembly.

    ** The thf [Th] and collection [Cth]

    [Th] is [Htree] read at a TREESTATEFUL ([AdrTree]) address via the
    proven-cancelling [decode_tweak] (WOTSC/Games.v); the SM-TCR
    targets are the internal nodes of the honest value tree, committed
    bottom-up at distinct [AdrTree] tweaks (distinctness =
    [node_adrs_inj] + [encode_adrs_inj]).  [Cth] exposes the leaf-layer
    members [F]/[Tl]/[Hgrind] (summed on the message side) so the
    reduction can build the WOTS+C anchors and grind under the hidden
    [pp] BEFORE [GETPP] (the COLLQ-pin pattern of WOTSC/CompressHop).

    ** The reduction [R_tree]

    [R_tree : package (I_SMTCR Th Cth (n_max-1)) (I_G0f ...)] simulates
    the FXMSS game.  GEN pins [pp] through one COLLQ, builds every
    WOTS+C anchor purely under that [pp] (leaf chains/compression via
    [F]/[Tl], grinding the presampled digests via [Hgrind] — all
    through COLLQ), commits every INTERNAL node bottom-up through
    [TQUERY (encode_adrs (AdrTree z i), (lval, rval))] (the answer is
    exactly the honest node value), then [GETPP] and returns
    (pp, root).  SIGN/HASH are G6f's bodies verbatim (the reduction
    stores the keys; signing is pure).  FORGE classifies the forgery
    with [fxcase]; on the [FColl q x y] case it submits
    [CHECK (j_q, x)] at the committed index [j_q] of the colliding
    internal node — SM-TCR's win, equal to G6f's kept verdict; the
    SM-TCR-ideal CHECK returns false = G7f's nulled verdict.

    Pure layer first: [fxcase_FColl] turns a verifying FColl forgery
    into the SM-TCR collision data via [Merkle.extractP].

    Style/idiom: WOTSC/Theorem.v (the [Adv_perfect_l/r] + [Adv_reduction]
    assembly, ~line 101), WOTSC/{ChainHop,CompressHop}.v (the
    COLLQ-pin reduction), FXMSS/DigestHop.v (the shared game skeleton).

    NOTE on scope: the SIGN oracle is identical in G6f/G7f, so the
    perfect step for it is a plain sync (no [sign4_step]-style two-sided
    rewrite — that is what blew up the digest hop and is unnecessary
    here). *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From HBS Require Import Prelude Math.BinTree Math.Merkle Math.Encoding
  Sig.Scheme Games.THF Games.SMTCR Toolkit.SampleSeq.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.

Section FXMSSTreeHop.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same section context as FXMSS/LateGames.v. *)
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

(* ------------------------------------------------------------------ *)
(** ** Shorthands *)

Local Notation tshape := (shape_of h_sf).
Local Notation posid := (pos_id h_sf).
Local Notation nhash := (node_hash PP N Htree h_sf).
Local Notation valtree := (value_tree_x PP N F Tl h_sf).
Local Notation fxroot := (fx_root_x PP N F Tl Htree h_sf).
Local Notation fxvermd :=
  (fx_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation frecover := (recover_anchor PP N D F Tl Hgrind).
Local Notation fxcaseN :=
  (fxcase PP N D F Tl Hgrind Htree h_sf).

(* ------------------------------------------------------------------ *)
(** ** The thf [Th] for the tree-node hash (PROOF_PLAN.md "Tree hop")

    [th_T := adrs_sf_ch], [th_M := N × N] (the two children), evaluated
    by [Htree] at the decoded address; the answer at an encoded
    [AdrTree] tweak is exactly [node_hash] ([th_evalE_Th]). *)

Definition Th : thf :=
  {| th_PP := PP ; th_T := adrs_sf_ch ; th_M := N × N ; th_N := N ;
     th_eval := fun pp t xy => Htree pp (decode_tweak t) xy ;
     th_dPP := dPP ;
     th_dM := {code x ← dN ;; y ← dN ;; ret ((x, y) : N × N) } ;
     th_dN := dN |}.

(** [Cth]: the leaf-layer collection — [F] (chain steps), [Tl]
    (compression) and [Hgrind] (grinding), summed on the message side
    so one [tc_eval] dispatches all three under the shared (hidden)
    [pp].  Mirrors WOTSC/Games.v's [Cf]/[Cpk] collections. *)

Definition Cth : thf_coll Th :=
  Build_thf_coll Th adrs_sf_ch (N ∐ (('list N) ∐ (D × 'nat))) (N ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr (inl xs) => inl (Tl pp (decode_tweak t) xs)
       | inr (inr dc) => inr (Hgrind pp (decode_tweak t) dc : 'nat)
       end).

(** Sanity: on an encoded [AdrTree] tweak [Th] evaluates [node_hash]
    (the verifier's tree hash). *)
Lemma th_evalE_Th pp (z i : nat) (xy : N * N) :
  th_eval Th pp (encode_adrs (AdrTree z i)) xy = Htree pp (AdrTree z i) xy.
Proof. by rewrite /= decode_tweakK. Qed.

Lemma node_hash_Th pp (pos : seq bool) (x y : N) :
  th_eval Th pp (encode_adrs (tree_node_adrs (h_sf - size pos)
                                (idx_of_path pos))) (x, y)
  = nhash pp pos x y.
Proof. by rewrite /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the FColl forgery yields an SM-TCR collision

    A verifying forgery with [fxcase = FColl q x y] gives a hash
    collision at an internal node [q] of the honest value tree:
    [nhash pp q x.1 x.2 = nhash pp q y.1 y.2] with [x <> y] and [y]
    the honest children values at [q].  This is exactly [extractP]'s
    FColl branch applied to the verification equation. *)

(** The verify equation extracted from [fxvermd]'s 4th conjunct, in
    the shape [extractP] consumes (h := nhash pp, t := honest tree). *)
Lemma fxvermd_val_ap pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  val_ap (nhash pp) [::] (path_of_idx (h_sf - zi.1) zi.2) ap
         (frecover pp zi md ws)
  = Some (val_bt (nhash pp) [::] (valtree pp sp xss)).
Proof.
rewrite /fx_verify_md => /and4P[_ _ _ /eqP].
by rewrite /fx_root_x.
Qed.

(** The FColl extraction: position [q], the colliding inputs [x] and
    the honest children [y], the collision and the disequality. *)
Lemma fxcase_FColl pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) (q : seq bool) (x y : N * N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  fxcaseN pp sp xss zi md ws ap = FColl q x y ->
  exists qrel ltr,
    [/\ q = qrel,
        subtree_at (valtree pp sp xss) qrel = Some (BNode ltr.1 ltr.2),
        y = (val_bt (nhash pp) (rcons q false) ltr.1,
             val_bt (nhash pp) (rcons q true) ltr.2),
        nhash pp q x.1 x.2 = nhash pp q y.1 y.2 & x <> y].
Proof.
move=> hver hcase.
have hval := fxvermd_val_ap _ _ _ _ _ _ _ hver.
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
    distinct because the [AdrTree]-tweaks are ([node_adrs_inj_paths]),
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
    a position of a well-formed shape). *)
(** Generic: an internal position is no deeper than the tree. *)
Lemma internal_path_depth {A : Type} (t : bt A) (q : seq bool) :
  q \in internal_paths t -> (size q < bt_depth t)%N.
Proof.
elim: t q => [a|tl IHl tr IHr] q /=; first by rewrite in_nil.
rewrite inE => /orP[/eqP ->|]; first by [].
rewrite mem_cat => /orP[] /mapP[q' hq' ->] /=.
- by rewrite ltnS leq_max IHl.
- by rewrite ltnS leq_max IHr ?orbT.
Qed.

Lemma internal_path_size sp (q : seq bool) :
  q \in internal_paths (tshape sp) -> (size q <= h_sf)%N.
Proof.
move=> hq.
have hlt := internal_path_depth _ _ hq.
have hd := wf_shape_of h_sf sp.
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

(** The committed-target order and its key facts: the [AdrTree]
    tweaks along [internal_paths] are pairwise distinct (the
    distinctness side condition every SM-TCR commit needs). *)
Definition tnode_tw (q : seq bool) : adrs_sf_ch :=
  encode_adrs (tree_node_adrs (h_sf - size q) (idx_of_path q)).

Lemma tnode_tw_inj sp (p q : seq bool) :
  p \in internal_paths (tshape sp) -> q \in internal_paths (tshape sp) ->
  tnode_tw p = tnode_tw q -> p = q.
Proof.
move=> hp hq.
rewrite /tnode_tw => /encode_adrs_inj he.
have hps := internal_path_size sp p hp.
have hqs := internal_path_size sp q hq.
exact: (@node_adrs_inj w l h_sf p q Hh hps hqs he).
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
