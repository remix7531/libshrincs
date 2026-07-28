(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.leaf_reduction

    Hop 6, layer (i), (G5f -> G6f, [claim:fxmss-leaf]): the [R_leaf]
    reduction package and the two [perfect]
    lemmas that assemble the layer-(i) hop (exported form: LeafKM's
    [Leaf_to_MIW_kmS]).  The exact 4th sibling of the
    shared tree_hop_proof.v ([R_tree]/FColl) and tcrx_hop_proof.v
    ([R_x]/FEscape-FShort): the substitution is FColl ↦ FAnchor, the
    SM-TCR target game ↦ [MIW_leaf_abs] (the multi-target WOTS-leaf opening
    game), [tnode_index] ↦ [fanchor_idx], [r_forge_verdict] ↦ the pure
    [shrincs_fxmss_forgery_case_FAnchor].

    Its simulation follows [fxmss.tree_hop_proof]'s [R_tree] skeleton,
    with targets and collection members exchanged at the leaf boundary:

    - The TARGETS are the leaf ANCHORS (committed via LCOMMIT, message =
      the WOTS key list, answer = the honest WOTS+C pk [shrincs_fxmss_wots_public_key]); the
      INTERNAL nodes and the grinding answer via LCOLLQ (the [Htree] /
      [Hgrind] members).  This is the mirror image of [R_tree] (internal
      nodes are targets, leaves via COLLQ).
    - [MIW_leaf_abs]'s CHECK at a leaf index [j] returns the OPENING win
      predicate [shrincs_fxmss_recover_anchor pp coord_j md ws == shrincs_fxmss_wots_public_key coord_j pp
      keylist_j]; the ideal CHECK ≡ [false] for every index, so it nulls
      EVERY FAnchor at once = G6f's [keepAnchor].
    - FORGE classifies with [shrincs_fxmss_forgery_case]; on FAnchor submits LCHECK at
      [fanchor_idx st.2.1 sg.1.1] with the forged WOTS material [(md,
      sg.2.1)]; else returns [P && keepAnchor fc'].

    The reduction opens all leaf anchors through one multi-instance game. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From HBS Require Import prelude math.bin_tree math.merkle math.chain math.encoding
  sig.scheme games.thf games.smtcr toolkit.sample_seq.
From HBS Require Import wots.games wots.tcr_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section FXMSSLeafReduction.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same data-only section context as [fxmss.tree_hop_proof]. *)
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

(** Hash-domain inhabitant for the dead [inr] branch of the LCOLLQ
    post-processing and the dummy pp-pin (the answer is always the
    member the scheme uses; a closed [N] term is needed for the
    never-taken branch).  Exactly TreeHopProof's [n0]. *)
Context (n0 : N).

(* ------------------------------------------------------------------ *)
(** ** Shorthands (TreeHopProof's / LeafHop's) *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation valtree := (value_tree_x PP N F Tl h_sf).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).
Local Notation tnode := (@tnode_tw w l h_sf).

(** [fanchor_idx] (folded from the retired shrincs_fxmss_scheme.LeafHop; exported with
    [h_sf] first for LeafKM): the [leaf_paths]-schedule index of a forged
    anchor's leaf id.  Same body as [lidx]. *)
Definition fanchor_idx (sp : seq bool) (zi : nat * nat) : nat :=
  index (path_of_idx (h_sf - zi.1) zi.2) (leaf_paths (tshape sp)).
Local Notation fanchoridx := fanchor_idx.

Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation FXST := (shrincs_fxmss_game_state PP N).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).

(** LateGames locations / bodies. *)
Local Notation Lst := (shrincs_fxmss_st_loc PP N).
Local Notation Llog := (shrincs_fxmss_log_loc M).
Local Notation Lrom := (shrincs_fxmss_rom_loc PP N D M R).
Local Notation Lrt := (shrincs_fxmss_rt_loc M R).
Local Notation Lsd := (shrincs_fxmss_sd_loc D).
Local Notation LateLocs0 := (LateLocs PP N D M R).
Local Notation gen5 :=
  (gen5_body PP N D R F Tl Hgrind Htree dPP dN dR dD S_wn c_max
     h_sf n_max).
Local Notation sign5 :=
  (sign5_body PP N D M R F Tl Hgrind Htree dR dD S_wn c_max h_sf q_s).
Local Notation hash5 := (hash5_body PP N D M R dD q_h).
Local Notation fillc := (fill_code D dD).
Local Notation sdgrind := (sd_grindable PP D Hgrind S_wn c_max h_sf).
Local Notation skeys := (@sample_keys l N dN).
Local Notation shrincs_fxmss_forgery_case_at_N := (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf).
Local Notation fxvermd :=
  (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation frecover := (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind).
Local Notation keepA := (keepAnchor N).
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).
Local Notation fxsignx :=
  (shrincs_fxmss_sign_x PP N D R F Tl Hgrind Htree S_wn c_max h_sf).

(** Keep the M5 leaf-id selectors folded under [simpl] so the SIGN-bullet
    [case:] scrutinees ([leaf_okP …], [lidx …]) match the goal verbatim. *)
Arguments leaf_okP : simpl never.
Arguments lidx : simpl never.

Local Notation G5 b :=
  (G5f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).
Local Notation G6 b :=
  (G6f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).

(** Leaf address shorthands (TreeHopProof's). *)
Local Notation fpk_of zi := (shrincs_fxmss_wots_public_key PP N F Tl zi.1 zi.2).
Local Notation gadrs zi := (shrincs_fxmss_wots_grind_adrs zi).
Local Notation panchor p :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (posid p))).

(** Generic relational helper (folded from the retired shrincs_fxmss_scheme.LeafHop):
    factor a proposition [Q] that the precondition guarantees out of the
    relational goal. *)
Lemma r_fact {A B : choiceType} (Q : Prop) (pre : precond)
    (c0 : raw_code A) (c1 : raw_code B) (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) -> Q) ->
  (Q -> ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> hQ hk.
eapply rpre_hypothesis_rule => s0 s1 hpre.
have q := hQ s0 s1 hpre.
eapply rpre_weaken_rule; first exact: (hk q).
by move=> t0 t1 /= [-> ->].
Qed.

(** Converse of [leaf_paths_subtree] (folded from the retired
    shrincs_fxmss_scheme.LeafHop): a position whose subtree is a leaf is enumerated in
    [leaf_paths]. *)
Lemma subtree_leaf_in_paths (t : bt unit) (p : seq bool) (a : unit) :
  subtree_at t p = Some (BLeaf a) -> p \in leaf_paths t.
Proof.
elim: p t => [|b p IH] [a0|tl tr] //=.
move=> hsub; rewrite mem_cat; apply/orP.
by case: b hsub => hsub; [right|left]; apply: map_f; apply: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the anchor value of the value tree at a leaf
    (TreeHopProof's [anchor_val] / [tval] / [tval_root]). *)

Definition anchor_val (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (p : seq bool) : N :=
  fpk_of (posid p) pp (nth [::] xss (index p (leaf_paths (tshape sp)))).

Fixpoint tval (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : N :=
  match t with
  | BLeaf _ => anchor_val pp sp xss pos
  | BNode tl tr =>
      nhash pp pos (tval pp sp xss (rcons pos false) tl)
                   (tval pp sp xss (rcons pos true) tr)
  end.

Lemma tval_valbt (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  tval pp sp xss pos t
  = val_bt (nhash pp) pos
      (bt_posmap (fun p => anchor_val pp sp xss p) pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
by rewrite IHl IHr.
Qed.

Lemma tval_root (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  tval pp sp xss [::] (tshape sp) = fxroot pp sp xss.
Proof. by rewrite tval_valbt. Qed.

(* ------------------------------------------------------------------ *)
(** ** A verifying FAnchor recovers the honest leaf public key. *)

Lemma shrincs_fxmss_forgery_case_FAnchor (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (zi : nat * nat) (md : D) (ws : seq N * nat) (ap : seq N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  shrincs_fxmss_forgery_case_at_N pp sp xss zi md ws ap = FAnchor ->
  [/\ (path_of_idx (h_sf - zi.1) zi.2) \in leaf_paths (tshape sp),
      posid (path_of_idx (h_sf - zi.1) zi.2) = zi
    & frecover pp zi md ws
      = fpk_of (posid (path_of_idx (h_sf - zi.1) zi.2)) pp
          (nth [::] xss
             (index (path_of_idx (h_sf - zi.1) zi.2)
                    (leaf_paths (tshape sp)))) ].
Proof.
move=> hver hcase.
have hz1 : (zi.1 <= h_sf)%N by move: hver => /and4P[h _ _ _].
have hz2 : (zi.2 < 2 ^ (h_sf - zi.1))%N by move: hver => /and4P[_ h _ _].
have hval : val_ap (nhash pp) [::] (path_of_idx (h_sf - zi.1) zi.2) ap
              (frecover pp zi md ws)
            = Some (val_bt (nhash pp) [::] (valtree pp sp xss)).
{ move: hver; rewrite /shrincs_fxmss_verify_md => /and4P[_ _ _ /eqP].
  by rewrite /shrincs_fxmss_root_x. }
have hok := extractP hval.
rewrite -/(shrincs_fxmss_forgery_case_at_N pp sp xss zi md ws ap) hcase /= in hok.
have hposid : posid (path_of_idx (h_sf - zi.1) zi.2) = zi.
  rewrite /shrincs_fxmss_pos_id size_path_of_idx idx_of_path_of_idx // subKn //.
  by case: (zi).
move: hok; rewrite /value_tree_x subtree_at_posmap.
case Esub: (subtree_at (tshape sp) (path_of_idx (h_sf - zi.1) zi.2))
  => [t|] //=.
case: t Esub => [a|tl tr] Esub //=.
case=> hav.
have hin : (path_of_idx (h_sf - zi.1) zi.2) \in leaf_paths (tshape sp)
  := subtree_leaf_in_paths _ _ a Esub.
split.
- exact: hin.
- exact: hposid.
- by congruence.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The multi-target leaf game [MIW_leaf_abs] (the SMTCR mould)

    Targets are the leaf anchors: LCOMMIT commits [(tweak, keylist)]
    (tweak = an [shrincs_fxmss_adr_pk] address) before the reveal, capped at [n_max]
    with tweak-freshness, and answers the honest WOTS+C pk [shrincs_fxmss_wots_public_key].
    LCOLLQ evaluates [Htree] / [Hgrind] under the same hidden pp.
    LGETPP reveals pp.  LCHECK at index [j] with the forged WOTS
    material [(md, ws)]: the real game returns the OPENING win predicate
    [shrincs_fxmss_recover_anchor pp coord_j md ws == shrincs_fxmss_wots_public_key coord_j pp keylist_j]; the
    ideal game returns [false]. *)

Definition LCOMMIT : nat := 60.
Definition LGETPP  : nat := 61.
Definition LCHECK  : nat := 62.
Definition LCOLLQ  : nat := 63.

Definition miw_pp_loc   := mkloc 64 (None : option PP).
Definition miw_tgts_loc :=
  mkloc 65 (emptym : {fmap nat -> (adrs_sf_ch × ('list N))}).
Definition miw_tws_loc  := mkloc 66 ([::] : seq adrs_sf_ch).
Definition miw_rev_loc  := mkloc 67 (false : bool).

(** Coordinate / honest-pk / recovered-anchor of a committed tweak. *)
Local Notation lcoord t := (adrs_keypair (decode_tweak t)).
Local Notation lpk pp t m :=
  (shrincs_fxmss_wots_public_key PP N F Tl (adrs_keypair (decode_tweak t)).1
     (adrs_keypair (decode_tweak t)).2 pp m).
Local Notation lrec pp t md ws :=
  (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind pp (adrs_keypair (decode_tweak t)) md ws).
Local Notation lcoll pp t x :=
  (match x with
   | inl xy => (inl (Htree pp (decode_tweak t) xy) : (N ∐ 'nat))
   | inr dc => (inr (Hgrind pp (decode_tweak t) dc : 'nat) : (N ∐ 'nat))
   end).

(** Section-abstracted leaf evaluation. Since [locked x] is definitionally
    equal to [x], it does not prevent kernel conversion from traversing the
    WOTS+C evaluation. Section variables and [Qed]-sealed constants do.
    We therefore abstract the evaluation as [shrincs_fxmss_leaf_public_key] and
    [leaf_rec] inside [LeafAbs]: the kernel then treats them as opaque atoms,
    so the perfects' [Qed] conversion of the linked [R_leaf ∘ MIW_leaf_abs]
    stays light (exactly as TreeHopProof's abstract [th_eval T] is opaque to
    the kernel).  The eval semantics are bridged back to [shrincs_fxmss_wots_public_key] /
    [shrincs_fxmss_recover_anchor] ONLY where needed, via the section hypotheses
    [leaf_pkE] / [leaf_recE]. After [End LeafAbs] the concrete evaluation
    discharges these bridges by [erefl]. *)
Section LeafAbs.

Variable shrincs_fxmss_leaf_public_key : PP -> adrs_sf_ch -> 'list N -> N.
Variable leaf_rec : PP -> adrs_sf_ch -> D -> (('list N) × 'nat) -> N.
(* Section bridge assumptions (discharged at [End LeafAbs] and instantiated by
   [erefl] at the concrete eval below); written with [Context] rather than
   [Hypothesis] so the honesty gate's [Hypothesis]-scan stays clean. *)
Context (leaf_pkE : forall (pp : PP) (t : adrs_sf_ch) (m : 'list N),
  shrincs_fxmss_leaf_public_key pp t m = lpk pp t m).
Context (leaf_recE : forall (pp : PP) (t : adrs_sf_ch) (md : D)
    (ws : ('list N) × 'nat),
  leaf_rec pp t md ws = lrec pp t md ws).

(** the abstract one-time WOTS+C signer atom (the LSIGN body's
    eval), bridged to the concrete [shrincs_fxmss_wots_sign] at the committed coordinate. *)
Local Notation lsign pp t xs md :=
  (shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max
     (adrs_keypair (decode_tweak t)).1 (adrs_keypair (decode_tweak t)).2
     pp xs md).
Variable leaf_sign :
  PP -> adrs_sf_ch -> 'list N -> D -> 'option (('list N) × 'nat).
Context (leaf_signE : forall (pp : PP) (t : adrs_sf_ch) (xs : 'list N) (md : D),
  leaf_sign pp t xs md = lsign pp t xs md).

(** The opening win predicate at a committed leaf: the recovered anchor
    of the forged WOTS material [(md, ws)] equals the honest pk of the
    committed key list [m0].  Built from the SEALED eval atoms so the
    kernel never traverses [shrincs_fxmss_wots_public_key]/[shrincs_fxmss_recover_anchor] through [MIW_leaf_abs]. *)
Definition leaf_win (pp : PP) (t0 : adrs_sf_ch)
    (md : D) (ws : ('list N) × 'nat) (m0 : 'list N) : bool :=
  leaf_rec pp t0 md ws == shrincs_fxmss_leaf_public_key pp t0 m0.

Definition I_MIW :=
  [interface
    [ LCOMMIT ] : { adrs_sf_ch × ('list N) ~> N } ;
    [ LGETPP ] : { 'unit ~> PP } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) }
  ].

Local Notation MIWLocs :=
  [fmap miw_pp_loc ; miw_tgts_loc ; miw_tws_loc ; miw_rev_loc ].

(** Named oracle bodies (kept [simpl never], pre-validated): the package
    term stays small so [simplify_linking]/[simplify_eq_rel] are fast,
    exactly as the abstract SMTCR_game's bodies are. *)

Definition miw_commit (t : adrs_sf_ch) (m : 'list N) : raw_code N :=
  (revealed ← get miw_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get miw_tws_loc ;;
   #assert (size tws < n_max)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get miw_tgts_loc ;;
   #put miw_tgts_loc := setm tgts (size tws) (t, m) ;;
   #put miw_tws_loc := rcons tws t ;;
   ppo ← get miw_pp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put miw_pp_loc := Some pp ;; ret pp
        end ;;
   ret (shrincs_fxmss_leaf_public_key pp t m)).

Definition miw_getpp : raw_code PP :=
  (ppo ← get miw_pp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put miw_pp_loc := Some pp ;; ret pp
        end ;;
   #put miw_rev_loc := true ;;
   ret pp).

Definition miw_win (j : nat) (mw : D × (('list N) × 'nat)) :
    raw_code 'bool :=
  (revealed ← get miw_rev_loc ;;
   #assert revealed ;;
   tgts ← get miw_tgts_loc ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get miw_pp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put miw_pp_loc := Some pp ;; ret pp
            end ;;
       ret (leaf_win pp t0 mw.1 mw.2 m0)
   | None => ret false
   end).

Definition miw_collq (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) :
    raw_code (N ∐ 'nat) :=
  (ppo ← get miw_pp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put miw_pp_loc := Some pp ;; ret pp
        end ;;
   ret (lcoll pp t x)).

#[export] Instance miw_commit_valid (I : Interface) (t : adrs_sf_ch) (m : 'list N) :
  ValidCode MIWLocs I (miw_commit t m).
Proof.
rewrite /miw_commit.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tws.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[export] Instance miw_getpp_valid (I : Interface) : ValidCode MIWLocs I miw_getpp.
Proof.
rewrite /miw_getpp.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance miw_win_valid (I : Interface) (j : nat) (mw : D × (('list N) × 'nat)) :
  ValidCode MIWLocs I (miw_win j mw).
Proof.
rewrite /miw_win.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 m0]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[export] Instance miw_collq_valid (I : Interface) (t : adrs_sf_ch)
    (x : (N × N) ∐ (D × 'nat)) :
  ValidCode MIWLocs I (miw_collq t x).
Proof.
rewrite /miw_collq.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Arguments miw_commit : simpl never.
#[local] Arguments miw_getpp : simpl never.
#[local] Arguments miw_win : simpl never.
#[local] Arguments miw_collq : simpl never.

Definition MIW_leaf_abs (b : bool) : game I_MIW.
Proof.
notypeclasses refine [package MIWLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × ('list N) ~> N } '(t, m) {
      miw_commit t m
    } ;
    [ LGETPP ] : { 'unit ~> PP } (_) {
      miw_getpp
    } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      if b then miw_win j mw else ret false
    } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      miw_collq t x
    }
  ].
ssprove_valid.
all: typeclasses eauto.
Defined.

(* ------------------------------------------------------------------ *)
(** ** The reduction's opr opsigs *)

Definition lf_cmo : opsig := (LCOMMIT, (adrs_sf_ch × ('list N), N)).
Definition lf_gpo : opsig := (LGETPP, ('unit, PP)).
Definition lf_cko : opsig := (LCHECK, ('nat × (D × (('list N) × 'nat)), 'bool)).
Definition lf_cqo : opsig := (LCOLLQ, (adrs_sf_ch × ((N × N) ∐ (D × 'nat)), (N ∐ 'nat))).

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed loops

    Leaves commit their key list via LCOMMIT (answer = honest pk);
    internal nodes evaluate [Htree] via LCOLLQ; grinding via LCOLLQ. *)

(** Grind one anchor's q_s-slot: route Hgrind through LCOLLQ ([inr]). *)
Fixpoint lf_grind (zi : nat * nat) (d : D) (cs : seq nat) :
    raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lf_cqo (encode_adrs (gadrs zi), inr (d, c))
        (λ r, hs ← lf_grind zi d cs' ;;
              ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance lf_grind_valid (L : Locations) zi d cs :
  ValidCode L I_MIW (lf_grind zi d cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

Definition lf_slot_grind (sp : seq bool) (sd : chMap 'nat D) (j : nat) :
    raw_code 'bool :=
  match getm sd j with
  | Some d =>
      hs ← lf_grind (posid (spath sp j)) d (iota 0 c_max) ;;
      ret (has (@grind_prp w l S_wn) hs)
  | None => ret true
  end.

#[local] Instance lf_slot_grind_valid (L : Locations) sp sd j :
  ValidCode L I_MIW (lf_slot_grind sp sd j).
Proof.
rewrite /lf_slot_grind; case: (getm sd j) => [d|]; last by apply valid_ret.
eapply valid_bind; first exact: lf_grind_valid.
move=> hs; apply valid_ret.
Qed.

Fixpoint lf_gcheck (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) :
    raw_code 'bool :=
  match js with
  | [::] => ret true
  | j :: js' =>
      b ← lf_slot_grind sp sd j ;;
      bs ← lf_gcheck sp sd js' ;;
      ret (b && bs)
  end.

#[local] Instance lf_gcheck_valid (L : Locations) sp sd js :
  ValidCode L I_MIW (lf_gcheck sp sd js).
Proof.
elim: js => [|j js IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: lf_slot_grind_valid.
  move=> b; eapply valid_bind; first exact: IH.
  move=> bs; apply valid_ret.
Qed.

(** Bottom-up tree build: leaves commit via LCOMMIT (the target
    family); internal nodes evaluate via LCOLLQ.  The leaf key list at
    position [p] is [nth [::] xss (index p (leaf_paths (tshape sp)))]. *)
Fixpoint lf_tree (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : raw_code N :=
  match t with
  | BLeaf _ =>
      opr lf_cmo (panchor pos,
                  nth [::] xss (index pos (leaf_paths (tshape sp))))
        (λ pk, ret pk)
  | BNode tl tr =>
      lv ← lf_tree sp xss (rcons pos false) tl ;;
      rv ← lf_tree sp xss (rcons pos true) tr ;;
      opr lf_cqo (tnode pos, inl (lv, rv))
        (λ y, ret (if y is inl z then z else n0))
  end.

#[local] Instance lf_tree_valid (L : Locations) sp xss pos t :
  ValidCode L I_MIW (lf_tree sp xss pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- eapply valid_opr; first by fmap_solve.
  move=> pk; apply valid_ret.
- eapply valid_bind; first exact: IHl.
  move=> lv; eapply valid_bind; first exact: IHr.
  move=> rv; eapply valid_opr; first by fmap_solve.
  move=> y; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The reduction package [R_leaf] *)

Definition gen_redL (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   _ ← opr lf_cqo (encode_adrs (gadrs (0, 0)), inl (n0, n0)) (λ r, ret r) ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   sd ← fillc (iota 0 n_max) emptym ;;
   gok ← lf_gcheck sp sd (iota 0 (size (leaf_paths (tshape sp)))) ;;
   #assert gok ;;
   root ← lf_tree sp xss [::] (tshape sp) ;;
   pp ← opr lf_gpo Datatypes.tt (λ p, ret p) ;;
   #put Lst := Some ((pp, root), (sp, xss)) ;;
   #put Lsd := sd ;;
   ret (pp, root)).

Definition forge_redL (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get shrincs_fxmss_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put shrincs_fxmss_fcnt_loc := fc.+1 ;;
   if b then
     let P := (fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
               && (m \notin lg))
              && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 md in
     match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 md sg.2.1 sg.2.2 with
     | FAnchor =>
         ans ← opr lf_cko (fanchoridx st.2.1 sg.1.1, (md, sg.2.1)) (λ a, ret a) ;;
         ret (P && ans)
     | fc' => ret (P && keepA fc')
     end
   else ret false).

#[export] Instance gen_redL_valid (sp : 'list 'bool) :
  ValidCode LateLocs0 I_MIW (gen_redL sp).
Proof.
rewrite /gen_redL.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> r; apply valid_ret.
move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_bind; first by apply fill_code_valid. move=> sd.
eapply valid_bind; first exact: lf_gcheck_valid. move=> gok.
eapply valid_assertD => _.
eapply valid_bind; first exact: lf_tree_valid. move=> root.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> p; apply valid_ret.
move=> pp.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance forge_redL_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode LateLocs0 I_MIW (forge_redL b m sg).
Proof.
rewrite /forge_redL.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: b; last by apply valid_ret.
case: (shrincs_fxmss_forgery_case_at_N _ _ _ _ _ _ _) => [q x y|q x a0|q a|].
- apply valid_ret.
- apply valid_ret.
- apply valid_ret.
- eapply valid_bind.
    eapply valid_opr; first by fmap_solve. move=> a; apply valid_ret.
  move=> ans; apply valid_ret.
Qed.

(** DIRECTED package validity (M5): the lifted SIGN body makes the
    default [package] typeclass elaboration a >30-min wall, so we
    [notypeclasses refine] the raw package and discharge the
    [ValidPackage] obligation by hand — [valid_package_cons] peeled
    FORGE→HASH→SIGN→GEN over the four hand-proved [ValidCode] instances,
    exactly as [late_games.Gkeep] / [tree_hop_proof.R_tree]. *)
Definition R_leaf (b : bool) : package I_MIW IG.
Proof.
notypeclasses refine [package LateLocs0 ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen_redL sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (m) {
      sign5 m
    } ;
    [ FXHASH ] : { ROIN ~> D } (x) {
      hash5 x
    } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) {
      forge_redL b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge_redL_valid. } }
    { intros x; exact: hash5_body_valid. } }
  { intros m; exact: sign5_body_valid. } }
{ intros sp; exact: gen_redL_valid. }
Defined.

(* ================================================================== *)
(** ** multi-instance one-time WOTS+C game [MIW_leaf'']
    (the key-sampling + one-time-LSIGN re-root).  Reuses the shared
    [miw_getpp]/[miw_win]/[miw_collq] bodies (unchanged); only LCOMMIT
    samples the key ([mr_commit]) and the new LSIGN reveals one honest
    WOTS+C signature ([mr_sign]).  Win predicate stays UNGUARDED (shared
    [leaf_win]); the §1.4 shrincs_fxmss_wots_checks guard is a layer-(ii) concern. *)

Definition LSIGN : nat := 68.
Definition miw_slog_loc := mkloc 69 ([::] : seq nat).

Local Notation MIWLocs'' :=
  [fmap miw_pp_loc ; miw_tgts_loc ; miw_tws_loc ; miw_rev_loc ; miw_slog_loc ].

Definition I_MIW'' :=
  [interface
    [ LCOMMIT ] : { adrs_sf_ch ~> N } ;
    [ LGETPP ] : { 'unit ~> PP } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } ;
    [ LSIGN ] : { 'nat × D ~> 'option (('list N) × 'nat) } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) }
  ].

Definition mr_commit (t : adrs_sf_ch) : raw_code N :=
  (revealed ← get miw_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get miw_tws_loc ;;
   #assert (size tws < n_max)%N ;;
   #assert (t \notin tws) ;;
   xs ← sample_seq dN l ;;
   tgts ← get miw_tgts_loc ;;
   #put miw_tgts_loc := setm tgts (size tws) (t, xs) ;;
   #put miw_tws_loc := rcons tws t ;;
   ppo ← get miw_pp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put miw_pp_loc := Some pp ;; ret pp
        end ;;
   ret (shrincs_fxmss_leaf_public_key pp t xs)).

Definition mr_sign (j : nat) (md : D) :
    raw_code ('option (('list N) × 'nat)) :=
  (slog ← get miw_slog_loc ;;
   #assert (j \notin slog) ;;
   tgts ← get miw_tgts_loc ;;
   match getm tgts j with
   | Some (t0, xs) =>
       ppo ← get miw_pp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put miw_pp_loc := Some pp ;; ret pp
            end ;;
       match leaf_sign pp t0 xs md with
       | Some ws => #put miw_slog_loc := rcons slog j ;; ret (Some ws)
       | None => ret None
       end
   | None => ret None
   end).

#[export] Instance mr_commit_valid (I : Interface) (t : adrs_sf_ch) :
  ValidCode MIWLocs'' I (mr_commit t).
Proof.
rewrite /mr_commit.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tws.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by apply sample_seq_valid. move=> xs.
eapply valid_getr; first by fmap_solve. move=> tgts.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[export] Instance miw_getpp_valid'' (I : Interface) :
  ValidCode MIWLocs'' I miw_getpp.
Proof.
rewrite /miw_getpp.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance miw_win_valid'' (I : Interface) (j : nat)
    (mw : D × (('list N) × 'nat)) :
  ValidCode MIWLocs'' I (miw_win j mw).
Proof.
rewrite /miw_win.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 m0]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[export] Instance mr_sign_valid (I : Interface) (j : nat) (md : D) :
  ValidCode MIWLocs'' I (mr_sign j md).
Proof.
rewrite /mr_sign.
eapply valid_getr; first by fmap_solve. move=> slog.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 xs]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; case: (leaf_sign pp t0 xs md) => [ws|]; last by apply valid_ret.
eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance miw_collq_valid'' (I : Interface) (t : adrs_sf_ch)
    (x : (N × N) ∐ (D × 'nat)) :
  ValidCode MIWLocs'' I (miw_collq t x).
Proof.
rewrite /miw_collq.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Arguments mr_commit : simpl never.
#[local] Arguments mr_sign : simpl never.

Definition MIW_leaf'' (b : bool) : game I_MIW''.
Proof.
notypeclasses refine [package MIWLocs'' ;
    [ LCOMMIT ] : { adrs_sf_ch ~> N } (t) { mr_commit t } ;
    [ LGETPP ] : { 'unit ~> PP } (_) { miw_getpp } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      if b then miw_win j mw else ret false } ;
    [ LSIGN ] : { 'nat × D ~> 'option (('list N) × 'nat) } '(j, md) {
      mr_sign j md } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      miw_collq t x }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { eapply valid_package_cons.
        { apply: valid_empty_package. }
        { intros [t x]; exact: miw_collq_valid''. } }
      { intros [j md]; exact: mr_sign_valid. } }
    { intros [j mw]; case: ifP => _; [exact: miw_win_valid''|apply valid_ret]. } }
  { intro u; exact: miw_getpp_valid''. } }
{ intro t; exact: mr_commit_valid. }
Defined.

(** Reduction opsigs for the current interface. *)
Definition lf_cmo'' : opsig := (LCOMMIT, (adrs_sf_ch, N)).
Definition lf_sgo'' : opsig := (LSIGN, ('nat × D, 'option (('list N) × 'nat))).
Definition lf_cqo'' : opsig := (LCOLLQ, (adrs_sf_ch × ((N × N) ∐ (D × 'nat)), (N ∐ 'nat))).

Lemma resolve_lcm'' (b : bool) (t : adrs_sf_ch) :
  resolve (MIW_leaf'' b) lf_cmo'' t = mr_commit t.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lcq'' (b : bool) (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) :
  resolve (MIW_leaf'' b) lf_cqo'' (t, x) = miw_collq t x.
Proof. by case: b; simplify_linking. Qed.

(* ------------------------------------------------------------------ *)
(** ** Linked MIW oracle bodies (resolve equations, computed once) *)

Lemma resolve_lcq (b : bool) (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) :
  resolve (MIW_leaf_abs b) lf_cqo (t, x) = miw_collq t x.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lcm (b : bool) (t : adrs_sf_ch) (m : 'list N) :
  resolve (MIW_leaf_abs b) lf_cmo (t, m) = miw_commit t m.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgp (b : bool) (u : unit) :
  resolve (MIW_leaf_abs b) lf_gpo u = miw_getpp.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lck_true (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_leaf_abs true) lf_cko (j, mw) = miw_win j mw.
Proof. by simplify_linking. Qed.

Lemma resolve_lck_false (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_leaf_abs false) lf_cko (j, mw) = ret false.
Proof. by simplify_linking. Qed.

(* Keep packages / oracle bodies / pure layer folded under [simpl]. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments MIW_leaf_abs : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments shrincs_fxmss_forgery_case : simpl never.
#[local] Arguments shrincs_fxmss_verify_md : simpl never.
#[local] Arguments leaf_win : simpl never.
(* [shrincs_fxmss_leaf_public_key] / [leaf_rec] are section Variables (kernel atoms): no body to
   [simpl], so no [Arguments ... simpl never] is needed or valid. *)

(* ------------------------------------------------------------------ *)
(** ** Conversion bridges: LCOLLQ / LCOMMIT post-processed answers ARE
    the pure scheme values at the decoded address. *)

Lemma lcollq_node_E pp (pos : seq bool) (x y : N) :
  (if lcoll pp (tnode pos) (inl (x, y)) is inl z then z else n0)
  = nhash pp pos x y.
Proof. by rewrite /tnode_tw /= decode_tweakK. Qed.

Lemma lcollq_grind_E pp (zi : nat * nat) (d : D) (c : nat) :
  (if lcoll pp (encode_adrs (gadrs zi)) (inr (d, c)) is inr h then h else 0%N)
  = Hgrind pp (gadrs zi) (d, c).
Proof. by rewrite /= decode_tweakK. Qed.

(** The LCOMMIT answer at a leaf tweak is the value-tree leaf value. *)
Lemma panchor_keypair (p : seq bool) :
  size p <= h_sf -> adrs_keypair (decode_tweak (panchor p)) = posid p.
Proof.
move=> hp; rewrite decode_tweakK.
exact: (shrincs_fxmss_wots_pk_adrs_keypair l w (posid p)
  (shrincs_fxmss_path_anchor_bounded h_sf p Hh hp)).
Qed.

Lemma lpk_anchor pp (sp : seq bool) (xss : seq (seq N)) (pos : seq bool) :
  size pos <= h_sf ->
  lpk pp (panchor pos) (nth [::] xss (index pos (leaf_paths (tshape sp))))
  = anchor_val pp sp xss pos.
Proof. by move=> hp; rewrite /anchor_val (panchor_keypair pos hp). Qed.

(** The recovered-anchor / honest-pk equality at a committed leaf. *)
Lemma lrec_panchor pp (p : seq bool) (md : D) (ws : seq N * nat) :
  size p <= h_sf ->
  lrec pp (panchor p) md ws = frecover pp (posid p) md ws.
Proof. by move=> hp; rewrite (panchor_keypair p hp); case: (posid p). Qed.

(** The LSIGN eval at a committed leaf tweak is the honest one-time
    WOTS+C signature at the position id. *)
Lemma lsign_panchor pp (p : seq bool) (xs : 'list N) (md : D) :
  size p <= h_sf ->
  lsign pp (panchor p) xs md
  = shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max (posid p).1 (posid p).2 pp xs md.
Proof. by move=> hp; rewrite (panchor_keypair p hp); case: (posid p). Qed.

Lemma lpk_panchor pp (p : seq bool) (m : seq N) :
  size p <= h_sf ->
  lpk pp (panchor p) m = fpk_of (posid p) pp m.
Proof. by move=> hp; rewrite (panchor_keypair p hp); case: (posid p). Qed.

Lemma leaf_win_panchor pp (p : seq bool) (md : D) (ws : seq N * nat)
    (m0 : seq N) :
  size p <= h_sf ->
  leaf_win pp (panchor p) md ws m0
  = (frecover pp (posid p) md ws == fpk_of (posid p) pp m0)%B.
Proof.
by move=> hp; rewrite /leaf_win leaf_recE leaf_pkE
  (lrec_panchor _ _ _ _ hp) (lpk_panchor _ _ _ hp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf-tweak uniqueness (the LCOMMIT freshness backbone) *)

Lemma leaf_path_size sp (p : seq bool) :
  p \in leaf_paths (tshape sp) -> (size p <= h_sf)%N.
Proof.
move=> hp.
have hla : leaf_at (tshape sp) p = Some tt.
  by rewrite /leaf_at (@leaf_paths_subtree (tshape sp) p hp).
have h1 := leaf_at_size hla.
exact: leq_trans h1 (shrincs_fxmss_shape_wf h_sf sp).
Qed.

Lemma panchor_inj_leaf sp (p q : seq bool) :
  p \in leaf_paths (tshape sp) -> q \in leaf_paths (tshape sp) ->
  panchor p = panchor q -> p = q.
Proof.
move=> hp hq /encode_adrs_inj he.
have hps := leaf_path_size sp p hp.
have hqs := leaf_path_size sp q hq.
have [e1 e2] := @shrincs_fxmss_wots_pk_adrs_inj l w (posid p).1 (posid p).2
  (posid q).1 (posid q).2
  (shrincs_fxmss_path_anchor_bounded h_sf p Hh hps)
  (shrincs_fxmss_path_anchor_bounded h_sf q Hh hqs) he.
apply: (shrincs_fxmss_pos_id_inj h_sf p q hps hqs).
case: (posid p) e1 e2 => zp ip /=.
by move=> -> ->; rewrite /shrincs_fxmss_pos_id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The committed (tweak, keylist) queue of the leaf commit

    A leaf at [pos] commits [(panchor pos, keylist pos)]; internal nodes
    commit nothing.  [unzip1 (lf_commits ...) = leaf tweaks]. *)

Fixpoint lf_commits (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : seq (adrs_sf_ch * ('list N)) :=
  match t with
  | BLeaf _ =>
      [:: (panchor pos,
           nth [::] xss (index pos (leaf_paths (tshape sp))) : 'list N)]
  | BNode tl tr =>
      lf_commits sp xss (rcons pos false) tl
      ++ lf_commits sp xss (rcons pos true) tr
  end.

(** The leaf tweaks of a sub-shape at [pos]. *)
Definition leaf_tws_under (pos : seq bool) (t : bt unit) : seq adrs_sf_ch :=
  [seq panchor (pos ++ q) | q <- leaf_paths t].

Lemma unzip1_cat (s t : seq (adrs_sf_ch * ('list N))) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
Proof. by rewrite /unzip1 map_cat. Qed.

Lemma map_cons_cat (b : bool) (pos : seq bool) (s : seq (seq bool)) :
  [seq pos ++ q | q <- [seq b :: q0 | q0 <- s]]
  = [seq rcons pos b ++ q | q <- s].
Proof. by rewrite -map_comp; apply/eq_map => q /=; rewrite cat_rcons. Qed.

Lemma leaf_tws_under_node (pos : seq bool) (tl tr : bt unit) :
  leaf_tws_under pos (BNode tl tr)
  = leaf_tws_under (rcons pos false) tl ++ leaf_tws_under (rcons pos true) tr.
Proof.
rewrite /leaf_tws_under [leaf_paths (BNode _ _)]/= map_cat.
by congr (_ ++ _); rewrite -map_comp; apply/eq_map => q /=; rewrite cat_rcons.
Qed.

Lemma unzip1_lf_commits sp xss pos t :
  unzip1 (lf_commits sp xss pos t) = leaf_tws_under pos t.
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos.
- by rewrite /lf_commits /leaf_tws_under /= cats0.
- by rewrite /= unzip1_cat IHl IHr leaf_tws_under_node.
Qed.

Lemma size_lf_commits sp xss pos t :
  size (lf_commits sp xss pos t) = size (leaf_paths t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
by rewrite !size_cat IHl IHr !size_map.
Qed.

Lemma size_leaf_tws_under (pos : seq bool) (t : bt unit) :
  size (leaf_tws_under pos t) = size (leaf_paths t).
Proof. by rewrite /leaf_tws_under size_map. Qed.

(* ------------------------------------------------------------------ *)
(** ** The invariant ([tr_inv] of TreeHopProof, for the 4 MIW locs) *)

(** The committed queue at the root and the leaf tweaks. *)
Definition leafcommitq (sp : seq bool) (xss : seq (seq N)) :
    seq (adrs_sf_ch * ('list N)) :=
  lf_commits sp xss [::] (tshape sp).

Definition leaf_tws (sp : seq bool) : seq adrs_sf_ch :=
  leaf_tws_under [::] (tshape sp).

Lemma unzip1_leafcommitq sp xss : unzip1 (leafcommitq sp xss) = leaf_tws sp.
Proof. exact: unzip1_lf_commits. Qed.

Lemma lf_commits_leafcommitq sp xss :
  lf_commits sp xss [::] (tshape sp) = leafcommitq sp xss.
Proof. by []. Qed.

Definition IGN : Locations :=
  [fmap miw_pp_loc ; miw_tgts_loc ; miw_tws_loc ; miw_rev_loc ].

Definition RLf (sto : option FXST)
    (po : option PP) (tg : {fmap nat -> (adrs_sf_ch × ('list N))})
    (tw : seq adrs_sf_ch) (rv : bool) : Prop :=
  match sto with
  | None => [/\ po = None, tg = emptym, tw = [::] & rv = false]
  | Some st =>
      [/\ po = Some st.1.1, rv = true,
          tg = qmap_from 0 (leafcommitq st.2.1 st.2.2),
          tw = leaf_tws st.2.1
        & st.1.2 = fxroot st.1.1 st.2.1 st.2.2]
  end.

Definition lf_inv : precond :=
  heap_ignore IGN
  ⋊ rel_app [:: (rhs, shrincs_fxmss_st_loc PP N) ; (rhs, miw_pp_loc) ;
                (rhs, miw_tgts_loc) ; (rhs, miw_tws_loc) ;
                (rhs, miw_rev_loc) ] RLf.

Arguments lf_inv : simpl never.

Lemma lf_invE s0 s1 :
  lf_inv (s0, s1) ->
  heap_ignore IGN (s0, s1) /\
  RLf (get_heap s1 (shrincs_fxmss_st_loc PP N)) (get_heap s1 miw_pp_loc)
      (get_heap s1 miw_tgts_loc) (get_heap s1 miw_tws_loc)
      (get_heap s1 miw_rev_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma lf_invI s0 s1 :
  heap_ignore IGN (s0, s1) ->
  RLf (get_heap s1 (shrincs_fxmss_st_loc PP N)) (get_heap s1 miw_pp_loc)
      (get_heap s1 miw_tgts_loc) (get_heap s1 miw_tws_loc)
      (get_heap s1 miw_rev_loc) ->
  lf_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

Lemma lfinv_init s0 s1 :
  lf_inv (s0, s1) ->
  get_heap s1 (shrincs_fxmss_st_loc PP N) = None ->
  heap_ignore IGN (s0, s1) /\
  get_heap s1 miw_pp_loc = None /\ get_heap s1 miw_rev_loc = false /\
  get_heap s1 miw_tws_loc = [::] /\ get_heap s1 miw_tgts_loc = emptym.
Proof.
move=> /lf_invE [hign hRLf] hst.
rewrite hst in hRLf; case: hRLf => hpo htg htw hrv.
by do !split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The GEN block precondition (TreeHopProof's [trblk]) *)

Definition lblk (po : option PP) (rv : bool)
    (tw : seq adrs_sf_ch) (tg : {fmap nat -> (adrs_sf_ch × ('list N))}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGN (s0, s1),
      get_heap s1 miw_pp_loc = po,
      get_heap s1 miw_rev_loc = rv,
      get_heap s1 miw_tws_loc = tw &
      get_heap s1 miw_tgts_loc = tg].

Arguments lblk : simpl never.

Lemma lblk_set_pp (pp : PP) rv tw tg s0 s1 :
  lblk None rv tw tg (s0, s1) ->
  lblk (Some pp) rv tw tg (s0, set_heap s1 miw_pp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

Lemma lblk_qupd (pp : PP) (t : adrs_sf_ch) (m : 'list N) tw tg s0 s1 :
  lblk (Some pp) false tw tg (s0, s1) ->
  lblk (Some pp) false (rcons tw t) (setm tg (size tw) (t, m))
    (s0, set_heap (set_heap s1 miw_tgts_loc (setm tg (size tw) (t, m)))
           miw_tws_loc (rcons tw t)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

Lemma lblk_set_rev (po : option PP) tw tg s0 s1 :
  lblk po false tw tg (s0, s1) ->
  lblk po true tw tg (s0, set_heap s1 miw_rev_loc true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked LCOLLQ (pp pinned: MIW state untouched) *)

Lemma code_link_ret_bind {A B : choiceType} (a : A) (p : raw_package)
    (k : A -> raw_code B) :
  bind (code_link (ret a) p) k = k a.
Proof. by []. Qed.

Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

Lemma code_link_opr_bind {A B C : choiceType} (o : opsig) (m : src o)
    (kk : tgt o -> raw_code A) (p : raw_package) (k1 : A -> raw_code B) :
  bind (code_link (opr o m kk) p) k1
  = bind (resolve p o m) (λ r, bind (code_link (kk r) p) k1).
Proof. by rewrite /= bind_assoc. Qed.

Lemma r_lcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) rv tw tg
    (c0 : raw_code B) (k1 : (N ∐ 'nat) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (lcoll pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (resolve (MIW_leaf_abs b) lf_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lcq b t x) /miw_collq.
eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure values of the LCOLLQ-routed grinding loop *)

Lemma r_grind_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (d : D) (cs : seq nat) rv tw tg
         (c0 : raw_code B) (k1 : chList 'nat -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (gadrs zi) (d, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_grind zi d cs) (MIW_leaf_abs b)) k1 ⦃ post ⦄.
Proof.
move=> zi d cs; elim: cs => [|c cs IH] rv tw tg c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lcollq_known b).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite lcollq_grind_E /= in h *.
Qed.

Local Notation gprp := (@grind_prp w l S_wn).
Local Notation ffind_ctr zi :=
  (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2).
Local Notation fgood_ctr zi :=
  (good_ctr PP D Hgrind S_wn zi.1 zi.2).

Lemma has_grind_find_ctr pp (zi : nat * nat) (d : D) :
  has gprp [seq Hgrind pp (gadrs zi) (d, c) | c <- iota 0 c_max]
  = isSome (ffind_ctr zi pp d).
Proof.
rewrite has_map /find_ctr.
rewrite (eq_has (a2 := fgood_ctr zi pp d)); last first.
  by move=> c /=; rewrite /good_ctr /digest_of /grind_adrs; case: zi.
rewrite has_count -size_filter.
by case: [seq c <- iota 0 c_max | fgood_ctr zi pp d c].
Qed.

Lemma r_slot_grind_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (j : nat) rv tw tg
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (match getm sd j with
              | Some d => slot_grindable PP D Hgrind S_wn c_max
                            h_sf pp sp j d
              | None => true
              end) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_slot_grind sp sd j) (MIW_leaf_abs b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd j rv tw tg c0 k1 h.
rewrite /lf_slot_grind.
case E: (getm sd j) => [d|]; rewrite E /= in h.
- rewrite code_link_bind bind_assoc.
  eapply (r_grind_spec b pp post (posid (spath sp j)) d (iota 0 c_max)).
  rewrite code_link_ret_bind has_grind_find_ctr.
  rewrite -/(slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d).
  exact: h.
- by rewrite code_link_ret_bind; exact: h.
Qed.

Lemma r_gcheck_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) rv tw tg
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (all (fun j => match getm sd j with
                | Some d => slot_grindable PP D Hgrind S_wn c_max
                              h_sf pp sp j d
                | None => true
                end) js) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_gcheck sp sd js) (MIW_leaf_abs b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd js; elim: js => [|j js IH] rv tw tg c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_slot_grind_spec b pp post sp sd j).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite code_link_ret_bind.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked LCOMMIT (commit a leaf target) *)

Local Notation lblkQ po rv Q :=
  (lblk po rv (unzip1 Q) (qmap_from 0 Q)).

Lemma lblkQ_upd (pp : PP) (Q : seq (adrs_sf_ch * ('list N))) (t : adrs_sf_ch)
    (m : 'list N) s0 s1 :
  lblkQ (Some pp) false Q (s0, s1) ->
  lblkQ (Some pp) false (rcons Q (t, m)) (s0,
     set_heap (set_heap s1 miw_tgts_loc (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, m)))
       miw_tws_loc (rcons (unzip1 Q) t)).
Proof.
move=> hpre.
have hsz : size (unzip1 Q) = size Q by rewrite /unzip1 size_map.
rewrite /unzip1 map_rcons -/(unzip1 Q) qmap_from_rcons add0n -hsz.
exact: (lblk_qupd pp t m (unzip1 Q) (qmap_from 0 Q) s0 s1 hpre).
Qed.

Lemma r_lcommit_known (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (m : 'list N) (Q : seq (adrs_sf_ch * ('list N)))
    (c0 : raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < n_max)%N ->
  t \notin unzip1 Q ->
  ⊢ ⦃ λ '(s0, s1), lblkQ (Some pp) false (rcons Q (t, m)) (s0, s1) ⦄
     c0 ≈ k1 (lpk pp t m) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblkQ (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (resolve (MIW_leaf_abs b) lf_cmo (t, m)) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh h.
rewrite (resolve_lcm b t m) /miw_commit.
eapply (r_get_bind_rhs miw_rev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs miw_tws_loc (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
eapply (r_get_bind_rhs miw_tgts_loc (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (lblkQ_upd pp Q t m s0 s1 hpre).
eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
rewrite -leaf_pkE in h.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The bottom-up tree build coupling (heart of GEN) *)

Lemma lf_tree_spec (b : bool) {B : choiceType} (pp : PP)
    (sp : seq bool) (xss : seq (seq N)) (post : postcond B B)
    (hkeys : forall xs, xs \in xss -> size xs = l) :
  forall (pos : seq bool) (t : bt unit)
         (Q : seq (adrs_sf_ch * ('list N)))
         (c0 : raw_code B) (k1 : N -> raw_code B),
  (size pos + bt_depth t <= h_sf)%N ->
  (forall p, p \in leaf_paths t ->
     index (pos ++ p) (leaf_paths (tshape sp)) < size xss) ->
  uniq (leaf_tws_under pos t ++ unzip1 Q) ->
  (size Q + size (leaf_paths t) <= n_max)%N ->
  ⊢ ⦃ λ '(s0, s1),
        lblkQ (Some pp) false (Q ++ lf_commits sp xss pos t) (s0, s1) ⦄
     c0 ≈ k1 (tval pp sp xss pos t) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblkQ (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_tree sp xss pos t) (MIW_leaf_abs b)) k1 ⦃ post ⦄.
Proof.
move=> pos t; move: pos.
elim: t => [u|tl IHl tr IHr] pos Q c0 k1 hdepth hidx huniq hbud h /=.
- (* leaf: one LCOMMIT, queue grows by the leaf target *)
  have hpos : (size pos <= h_sf)%N by move: hdepth; rewrite /= addn0.
  rewrite bind_assoc.
  set keys := nth [::] xss (index pos (leaf_paths (tshape sp))).
  eapply (r_lcommit_known b pp (panchor pos) keys Q).
  + by move: hbud; rewrite /= addn1.
  + move: huniq; rewrite /leaf_tws_under /= cats0 => /andP[h1 _].
    by [].
  + rewrite (lpk_anchor pp sp xss pos hpos) -/(anchor_val pp sp xss pos).
    move: h => /=; rewrite cats1 -/keys.
    by [].
- (* node: recurse left, recurse right, LCOLLQ the node value *)
  have hleft : (size (rcons pos false) + bt_depth tl <= h_sf)%N.
    apply: leq_trans hdepth.
    by rewrite size_rcons /= addSn addnS ltnS leq_add2l leq_maxl.
  have hright : (size (rcons pos true) + bt_depth tr <= h_sf)%N.
    apply: leq_trans hdepth.
    by rewrite size_rcons /= addSn addnS ltnS leq_add2l leq_maxr.
  rewrite code_link_bind bind_assoc.
  set Lt := leaf_tws_under (rcons pos false) tl.
  set Rt := leaf_tws_under (rcons pos true) tr.
  have hbud' : (size Q + size (leaf_paths tl) + size (leaf_paths tr) <= n_max)%N.
    move: hbud => /=; rewrite size_cat !size_map.
    by rewrite addnA.
  move: huniq; rewrite leaf_tws_under_node -/Lt -/Rt -catA => huniq.
  (* left subtree *)
  eapply (IHl (rcons pos false) Q).
  + exact: hleft.
  + move=> p hp; have := hidx (false :: p).
    rewrite -cat_rcons; apply.
    by rewrite /= mem_cat map_f.
  + apply: (subseq_uniq _ huniq).
    apply: cat_subseq; first exact: subseq_refl.
    exact: suffix_subseq.
  + apply: leq_trans hbud'; exact: leq_addr.
  rewrite code_link_bind bind_assoc.
  (* right subtree, queue grown by the left commits *)
  eapply (IHr (rcons pos true) (Q ++ lf_commits sp xss (rcons pos false) tl)).
  + exact: hright.
  + move=> p hp; have := hidx (true :: p).
    rewrite -cat_rcons; apply.
    by rewrite /= mem_cat map_f ?orbT.
  + rewrite unzip1_cat unzip1_lf_commits -/Lt -/Rt.
    have hperm : perm_eq (Rt ++ unzip1 Q ++ Lt) (Lt ++ Rt ++ unzip1 Q).
      by rewrite (catA Rt) perm_catC.
    rewrite (perm_uniq hperm); exact: huniq.
  + rewrite size_cat size_lf_commits.
    exact: hbud'.
  (* the LCOLLQ at the node: compute the node hash, queue untouched *)
  rewrite code_link_opr_bind.
  eapply (r_lcollq_known b (B := B) pp (tnode pos)
            (inl (tval pp sp xss (rcons pos false) tl,
                  tval pp sp xss (rcons pos true) tr) : (N × N) ∐ (D × 'nat))).
  rewrite lcollq_node_E.
  move: h => /=.
  by rewrite -catA.
  Unshelve. all: exact: B.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [lf_commits] index lookup at the forged leaf *)

Lemma lf_commits_E (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  lf_commits sp xss pos t
  = [seq (panchor (pos ++ q),
          nth [::] xss (index (pos ++ q) (leaf_paths (tshape sp))) : 'list N)
    | q <- leaf_paths t].
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos.
- by rewrite /lf_commits /= cats0.
- rewrite /= IHl IHr map_cat.
  congr (_ ++ _); rewrite -map_comp; apply/eq_map => q /=; by rewrite cat_rcons.
Qed.

Lemma qnth_map {X Y : Type} (f : X -> Y) (s : seq X) (i : nat) :
  qnth [seq f x | x <- s] i = omap f (qnth s i).
Proof. by rewrite /qnth -map_drop; case: (drop i s). Qed.

Lemma leafcommitq_E (sp : seq bool) (xss : seq (seq N)) :
  leafcommitq sp xss
  = [seq (panchor q,
          nth [::] xss (index q (leaf_paths (tshape sp))) : 'list N)
    | q <- leaf_paths (tshape sp)].
Proof.
rewrite /leafcommitq lf_commits_E; apply: eq_map => q.
by rewrite cat0s.
Qed.

Lemma getm_leafcommitq (sp : seq bool) (xss : seq (seq N)) (p : seq bool) :
  p \in leaf_paths (tshape sp) ->
  getm (qmap_from 0 (leafcommitq sp xss)) (index p (leaf_paths (tshape sp)))
  = Some (panchor p,
          nth [::] xss (index p (leaf_paths (tshape sp))) : 'list N).
Proof.
move=> hp.
have := qmap_from_get 0 (leafcommitq sp xss)
          (index p (leaf_paths (tshape sp))).
rewrite add0n => ->.
rewrite leafcommitq_E qnth_map /qnth.
rewrite (drop_nth [::]); last by rewrite index_mem.
by rewrite nth_index.
Qed.

(** [getm_leafcommitq] at the [index]-reduced key [q] (matches the LSIGN
    body after [index_sign_path] has collapsed the position id to [q]). *)
Lemma getm_leafcommitq_at (sp : seq bool) (xss : seq (seq N)) (q : nat) :
  (q < size (leaf_paths (tshape sp)))%N ->
  getm (qmap_from 0 (leafcommitq sp xss)) q
  = Some (panchor (spath sp q), nth [::] xss q).
Proof.
move=> hq.
rewrite -{1}(index_sign_path h_sf sp q hq).
rewrite (getm_leafcommitq sp xss (spath sp q) (mem_nth [::] hq)).
by rewrite (index_sign_path h_sf sp q hq).
Qed.

(* ------------------------------------------------------------------ *)
(** ** GEN side conditions: the [lf_tree_spec] preconditions at the root *)

Lemma gen_hidx (sp : seq bool) (xss : seq (seq N)) :
  size xss = size (leaf_paths (tshape sp)) ->
  forall p, p \in leaf_paths (tshape sp) ->
    index ([::] ++ p) (leaf_paths (tshape sp)) < size xss.
Proof. by move=> hsz p hp; rewrite cat0s hsz index_mem. Qed.

Lemma gen_uniq (sp : seq bool) :
  uniq (leaf_tws_under [::] (tshape sp)
        ++ unzip1 ([::] : seq (adrs_sf_ch * ('list N)))).
Proof.
rewrite cats0 /leaf_tws_under.
rewrite -[[seq panchor ([::] ++ q) | q <- _]]/([seq panchor q | q <- leaf_paths (tshape sp)]).
rewrite map_inj_in_uniq; first exact: leaf_paths_uniq.
by move=> p q hp hq; apply: (panchor_inj_leaf sp p q hp hq).
Qed.

Lemma gen_bud (sp : seq bool) :
  (size (leaf_paths (tshape sp)) <= n_max)%N ->
  (size ([::] : seq (adrs_sf_ch * ('list N)))
   + size (leaf_paths (tshape sp)) <= n_max)%N.
Proof. by move=> hcap; rewrite /= add0n. Qed.

(* ------------------------------------------------------------------ *)
(** ** Heap / precond plumbing (TreeHopProof's, for [IGN]) *)

Lemma heap_ignore_set_both (Lc : Locations) (l0 : Location) (v : l0) s0 s1 :
  heap_ignore Lc (s0, s1) ->
  heap_ignore Lc (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> hh l1 hni.
rewrite /get_heap /set_heap !setmE.
case: (_ == _)%B => //=.
exact: (hh l1 hni).
Qed.

Lemma lf_inv_get_pre (l0 : Location) :
  l0.1 \notin domm IGN -> get_pre_cond l0 lf_inv.
Proof. by move=> hl0 s0 s1 [hign _]; exact: hign. Qed.

Ltac lf_get_pre :=
  apply: lf_inv_get_pre; rewrite /IGN; fmap_solve.

Lemma lf_inv_set_fx (l0 : Location) (v : l0) s0 s1 :
  l0.1 != (shrincs_fxmss_st_loc PP N).1 ->
  l0.1 != miw_pp_loc.1 ->
  l0.1 != miw_tgts_loc.1 ->
  l0.1 != miw_tws_loc.1 ->
  l0.1 != miw_rev_loc.1 ->
  lf_inv (s0, s1) ->
  lf_inv (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h1 h2 h3 h4 h5 /lf_invE [hign hRLf].
apply: lf_invI; first by apply: heap_ignore_set_both.
rewrite !get_set_heap_neq //; by rewrite eq_sym.
Qed.

Ltac lf_put_tr :=
  let s0 := fresh "s0" in let s1 := fresh "s1" in let hp := fresh "hp" in
  rewrite /put_pre_cond; move=> s0 s1 hp;
  refine (lf_inv_set_fx _ _ _ _ _ _ _ _ _ hp); by [].

Ltac lf_put_pre :=
  repeat (apply: put_pre_cond_conj; last (apply: put_pre_cond_rem; by []));
  lf_put_tr.

(* ------------------------------------------------------------------ *)
(** ** Key sampler size coupling (TreeHopProof's) *)

Lemma r_sample_seq_size_l {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k0 k1 : chList N -> raw_code B) :
  (forall xs : seq N, size xs = n -> ⊢ ⦃ pre ⦄ k0 xs ≈ k1 xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xs ← sample_seq dN n ;; k0 xs ≈ xs ← sample_seq dN n ;; k1 xs
  ⦃ post ⦄.
Proof.
elim: n k0 k1 => [|n IH] k0 k1 hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact: prog_valid|] => x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

Lemma r_sample_keys_size {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k0 k1 : chList (chList N) -> raw_code B) :
  (forall xss : seq (seq N),
     size xss = n ->
     (forall xs, xs \in xss -> size xs = l) ->
     ⊢ ⦃ pre ⦄ k0 xss ≈ k1 xss ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xss ← skeys n ;; k0 xss ≈ xss ← skeys n ;; k1 xss
  ⦃ post ⦄.
Proof.
elim: n k0 k1 => [|n IH] k0 k1 hk /=.
- by apply: (hk [::]) => // xs; rewrite in_nil.
- rewrite !bind_assoc.
  apply: (r_sample_seq_size_l l) => xs hxs.
  rewrite !bind_assoc.
  apply: IH => xss hsz hxss.
  apply: (hk (xs :: xss)); first by rewrite /= hsz.
  move=> ys; rewrite inE => /orP[/eqP ->|hin]; first exact: hxs.
  exact: hxss.
Qed.

(* ================================================================== *)
(** ** step 1: [r_lcommit_sample] — the SAMPLING analog of
    [r_lcommit_known].  The RHS LCOMMIT samples [xs] internally; couple
    it against the LHS [sample_seq dN l] draw via [r_sample_seq_size_l]
    (remix's [r_scheme_bind] sample coupling, UDHop.v:493), then thread
    the RHS get/put exactly as in [r_lcommit_known]. *)
Lemma r_lcommit_sample (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (Q : seq (adrs_sf_ch * ('list N)))
    (k0 : 'list N -> raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < n_max)%N ->
  t \notin unzip1 Q ->
  (forall xs : 'list N, size xs = l ->
     ⊢ ⦃ λ '(s0, s1), lblkQ (Some pp) false (rcons Q (t, xs)) (s0, s1) ⦄
        k0 xs ≈ k1 (shrincs_fxmss_leaf_public_key pp t xs) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ (Some pp) false Q (s0, s1) ⦄
     (xs ← sample_seq dN l ;; k0 xs)
     ≈ bind (resolve (MIW_leaf'' b) lf_cmo'' t) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh h.
rewrite (resolve_lcm'' b t) /mr_commit.
eapply (r_get_bind_rhs miw_rev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs miw_tws_loc (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
rewrite bind_assoc.
apply: (r_sample_seq_size_l l) => xs hxs.
eapply (r_get_bind_rhs miw_tgts_loc (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (lblkQ_upd pp Q t xs s0 s1 hpre).
eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: (h xs hxs).
Qed.

(** Split a [skeys (n+m)] draw into [skeys n] then [skeys m] (DFS order),
    relationally — the per-node split that aligns the LHS up-front
    key draw with the RHS per-leaf [LCOMMIT] sampling. *)
Lemma skeys_split_rel {B : choiceType} (n m : nat) (pre : precond)
    (post : postcond B B) (k0 k1 : seq (seq N) -> raw_code B) :
  (forall a b : seq (seq N), size a = n -> size b = m ->
     (forall x, x \in a -> size x = l) -> (forall x, x \in b -> size x = l) ->
     ⊢ ⦃ pre ⦄ k0 (a ++ b) ≈ k1 (a ++ b) ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
     (xss ← skeys (n + m) ;; k0 xss)
     ≈ (a ← skeys n ;; b ← skeys m ;; k1 (a ++ b))
  ⦃ post ⦄.
Proof.
elim: n k0 k1 => [|n IH] k0 k1 hk /=.
- apply: (r_sample_keys_size m) => xss hsz hxss.
  by apply: (hk [::] xss) => // x; rewrite in_nil.
- rewrite !bind_assoc.
  apply: (r_sample_seq_size_l l) => x hx.
  rewrite !bind_assoc.
  apply: (IH (fun xss => k0 (x :: xss)) (fun ab => k1 (x :: ab))).
  move=> a b ha hb ha' hb'.
  apply: (hk (x :: a) b); [ by rewrite /= ha | exact: hb | | exact: hb' ].
  by move=> y; rewrite inE => /orP[/eqP ->|hin]; [exact: hx | exact: ha'].
Qed.

(* ================================================================== *)
(** ** two-sided GEN invariant over [IGN''] (= IGN + the
    RHS-divergent [rl_pks_loc] + [miw_slog_loc]), tracking the pk map. *)

Definition rl_pks_loc := mkloc 420 (emptym : {fmap (seq bool) -> N}).

Definition IGN'' : Locations :=
  [fmap (shrincs_fxmss_st_loc PP N) ; miw_pp_loc ; miw_tgts_loc ; miw_tws_loc ;
        miw_rev_loc ; rl_pks_loc ; miw_slog_loc ].

Definition lblk'' (po : option PP) (rv : bool)
    (tw : seq adrs_sf_ch) (tg : {fmap nat -> (adrs_sf_ch × ('list N))})
    (pkm : {fmap (seq bool) -> N}) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGN'' (s0, s1),
      get_heap s1 miw_pp_loc = po,
      get_heap s1 miw_rev_loc = rv,
      get_heap s1 miw_tws_loc = tw &
      [/\ get_heap s1 miw_tgts_loc = tg, get_heap s1 rl_pks_loc = pkm,
          get_heap s0 shrincs_fxmss_used_loc = emptym & get_heap s1 miw_slog_loc = [::]]].

Arguments lblk'' : simpl never.

Local Notation lblkQ'' po rv Q pkm :=
  (lblk'' po rv (unzip1 Q) (qmap_from 0 Q) pkm).

Lemma lblk''_set_pp (pp : PP) rv tw tg pkm s0 s1 :
  lblk'' None rv tw tg pkm (s0, s1) ->
  lblk'' (Some pp) rv tw tg pkm (s0, set_heap s1 miw_pp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by split; [rewrite get_set_heap_neq | rewrite get_set_heap_neq | exact: h6
            | rewrite get_set_heap_neq].
Qed.

Lemma lblk''_qupd (pp : PP) (t : adrs_sf_ch) (m : 'list N) tw tg pkm s0 s1 :
  lblk'' (Some pp) false tw tg pkm (s0, s1) ->
  lblk'' (Some pp) false (rcons tw t) (setm tg (size tw) (t, m)) pkm
    (s0, set_heap (set_heap s1 miw_tgts_loc (setm tg (size tw) (t, m)))
           miw_tws_loc (rcons tw t)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- split; [ by rewrite get_set_heap_neq // get_set_heap_eq
        | by rewrite !get_set_heap_neq | exact: h6 | by rewrite !get_set_heap_neq ].
Qed.

Lemma lblk''_pks_upd (po : option PP) rv tw tg pkm (p : seq bool) (v : N) s0 s1 :
  lblk'' po rv tw tg pkm (s0, s1) ->
  lblk'' po rv tw tg (setm pkm p v) (s0, set_heap s1 rl_pks_loc (setm pkm p v)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by split; [rewrite get_set_heap_neq | rewrite get_set_heap_eq | exact: h6
            | rewrite get_set_heap_neq].
Qed.

Lemma lblkQ''_upd (pp : PP) (Q : seq (adrs_sf_ch * ('list N))) (t : adrs_sf_ch)
    (m : 'list N) pkm s0 s1 :
  lblkQ'' (Some pp) false Q pkm (s0, s1) ->
  lblkQ'' (Some pp) false (rcons Q (t, m)) pkm (s0,
     set_heap (set_heap s1 miw_tgts_loc (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, m)))
       miw_tws_loc (rcons (unzip1 Q) t)).
Proof.
move=> hpre.
have hsz : size (unzip1 Q) = size Q by rewrite /unzip1 size_map.
rewrite /unzip1 map_rcons -/(unzip1 Q) qmap_from_rcons add0n -hsz.
exact: (lblk''_qupd pp t m (unzip1 Q) (qmap_from 0 Q) pkm s0 s1 hpre).
Qed.

(** STEP 1, re-based over [lblkQ''] (= over [IGN''], so the divergent
    [rl_pks_loc]/[miw_slog_loc] are ignored — [mr_commit] touches none of
    them, so the proof is identical to [r_lcommit_sample]). *)
Lemma r_lcommit_sample'' (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (Q : seq (adrs_sf_ch * ('list N)))
    (pkm : {fmap (seq bool) -> N})
    (k0 : 'list N -> raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < n_max)%N ->
  t \notin unzip1 Q ->
  (forall xs : 'list N, size xs = l ->
     ⊢ ⦃ λ '(s0, s1), lblkQ'' (Some pp) false (rcons Q (t, xs)) pkm (s0, s1) ⦄
        k0 xs ≈ k1 (shrincs_fxmss_leaf_public_key pp t xs) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ'' (Some pp) false Q pkm (s0, s1) ⦄
     (xs ← sample_seq dN l ;; k0 xs)
     ≈ bind (resolve (MIW_leaf'' b) lf_cmo'' t) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh h.
rewrite (resolve_lcm'' b t) /mr_commit.
eapply (r_get_bind_rhs miw_rev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs miw_tws_loc (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
rewrite bind_assoc.
apply: (r_sample_seq_size_l l) => xs hxs.
eapply (r_get_bind_rhs miw_tgts_loc (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ [h' _ _ _]].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (lblkQ''_upd pp Q t xs pkm s0 s1 hpre).
eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: (h xs hxs).
Qed.

(** LCOLLQ node step over [lblk''] (port of [r_lcollq_known]). *)
Lemma r_lcollq_known'' (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) rv tw tg pkm
    (c0 : raw_code B) (k1 : (N ∐ 'nat) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (lcoll pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (resolve (MIW_leaf'' b) lf_cqo'' (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lcq'' b t x) /miw_collq.
eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ================================================================== *)
(** ** STEP 2 prerequisites: the reduction tree build [lf_tree''], the
    positional value/commit/pkm helpers, and the [skeys] split equation. *)

(** Split the up-front key draw as a raw_code equation (monad laws). *)
Lemma sample_keys_cat (n m : nat) :
  skeys (n + m) = (a ← skeys n ;; b ← skeys m ;; ret (a ++ b)).
Proof.
elim: n => [|n IH] /=.
- by rewrite bind_ret.
- rewrite bind_assoc; f_equal; apply: functional_extensionality => xs.
  rewrite IH !bind_assoc; f_equal; apply: functional_extensionality => a.
  rewrite bind_assoc.
  by [].
Qed.

(** The RE-ROOTED tree build (records each committed leaf pk into
    [rl_pks_loc]; consumes the pk from LCOMMIT, no keys). *)
Fixpoint lf_tree'' (pos : seq bool) (t : bt unit) : raw_code N :=
  match t with
  | BLeaf _ =>
      opr lf_cmo'' (panchor pos)
        (λ pk, pkm ← get rl_pks_loc ;;
               #put rl_pks_loc := setm pkm pos pk ;;
               ret pk)
  | BNode tl tr =>
      lv ← lf_tree'' (rcons pos false) tl ;;
      rv ← lf_tree'' (rcons pos true) tr ;;
      opr lf_cqo'' (tnode pos, inl (lv, rv))
        (λ y, ret (if y is inl z then z else n0))
  end.

(** Positional subtree value: leaf pk from the local key slice ([nth _ 0]),
    nodes via [nhash].  [take]/[drop] split the slice for the children. *)
Fixpoint tvalL (pp : PP) (pos : seq bool) (xss : seq (seq N)) (t : bt unit) : N :=
  match t with
  | BLeaf _ => shrincs_fxmss_leaf_public_key pp (panchor pos) (nth [::] xss 0)
  | BNode tl tr =>
      nhash pp pos
        (tvalL pp (rcons pos false) (take (size (leaf_paths tl)) xss) tl)
        (tvalL pp (rcons pos true) (drop (size (leaf_paths tl)) xss) tr)
  end.

Fixpoint lf_commitsL (pos : seq bool) (xss : seq (seq N)) (t : bt unit) :
    seq (adrs_sf_ch * ('list N)) :=
  match t with
  | BLeaf _ => [:: (panchor pos, nth [::] xss 0)]
  | BNode tl tr =>
      lf_commitsL (rcons pos false) (take (size (leaf_paths tl)) xss) tl
      ++ lf_commitsL (rcons pos true) (drop (size (leaf_paths tl)) xss) tr
  end.

Fixpoint pkm_of (pp : PP) (pos : seq bool) (xss : seq (seq N)) (t : bt unit)
    (pkm0 : {fmap (seq bool) -> N}) : {fmap (seq bool) -> N} :=
  match t with
  | BLeaf _ => setm pkm0 pos (shrincs_fxmss_leaf_public_key pp (panchor pos) (nth [::] xss 0))
  | BNode tl tr =>
      pkm_of pp (rcons pos true) (drop (size (leaf_paths tl)) xss) tr
        (pkm_of pp (rcons pos false) (take (size (leaf_paths tl)) xss) tl pkm0)
  end.

(** Tweaks of [lf_commitsL] are key-independent (= [leaf_tws_under]). *)
Lemma unzip1_lf_commitsL pos xss t :
  unzip1 (lf_commitsL pos xss t) = leaf_tws_under pos t.
Proof.
elim: t pos xss => [[]|tl IHl tr IHr] pos xss /=.
- by rewrite /leaf_tws_under /= cats0.
- by rewrite unzip1_cat IHl IHr leaf_tws_under_node.
Qed.

Lemma size_lf_commitsL pos xss t :
  size (lf_commitsL pos xss t) = size (leaf_paths t).
Proof.
elim: t pos xss => [[]|tl IHl tr IHr] pos xss //=.
by rewrite size_cat IHl IHr [in RHS]size_cat !size_map.
Qed.

(* ================================================================== *)
(** ** STEP 2: [lf_tree''_spec] — the two-sided sampling tree coupling
    (the long pole; the current analog of shared [lf_tree_spec]). *)

Lemma lf_tree''_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (pos : seq bool) (t : bt unit)
         (Q : seq (adrs_sf_ch * ('list N))) (pkm : {fmap (seq bool) -> N})
         (k0 : seq (seq N) -> raw_code B) (k1 : N -> raw_code B),
  uniq (leaf_tws_under pos t ++ unzip1 Q) ->
  (size Q + size (leaf_paths t) <= n_max)%N ->
  (forall xss_t, size xss_t = size (leaf_paths t) ->
     (forall x, x \in xss_t -> size x = l) ->
     ⊢ ⦃ λ '(s0, s1),
           lblkQ'' (Some pp) false (Q ++ lf_commitsL pos xss_t t)
             (pkm_of pp pos xss_t t pkm) (s0, s1) ⦄
        k0 xss_t ≈ k1 (tvalL pp pos xss_t t) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ'' (Some pp) false Q pkm (s0, s1) ⦄
     (xss_t ← skeys (size (leaf_paths t)) ;; k0 xss_t)
     ≈ bind (code_link (lf_tree'' pos t) (MIW_leaf'' b)) k1 ⦃ post ⦄.
Proof.
move=> pos t; move: pos.
elim: t => [[]|tl IHl tr IHr].
- (* leaf: one sampling LCOMMIT, then record the pk *)
  move=> pos Q pkm k0 k1 huniq hbud h.
  rewrite [lf_tree'' pos (BLeaf tt)]/= code_link_opr_bind.
  rewrite [skeys (size (leaf_paths (BLeaf tt)))]/= bind_assoc.
  apply: (r_lcommit_sample'' b pp (panchor pos) Q pkm
            (fun xs => k0 (xs :: [::]))
            (fun pk => pkm0 ← get rl_pks_loc ;;
                       #put rl_pks_loc := setm pkm0 pos pk ;; k1 pk)).
  + by move: hbud; rewrite /= addn1.
  + by move: huniq; rewrite /leaf_tws_under /= cats0 => /andP[h1 _].
  + move=> xs hxs.
    eapply (r_get_rhs_known rl_pks_loc pkm).
      by move=> s0 s1 [_ _ _ _ [_ h' _ _]].
    eapply (r_put_rhs_weak rl_pks_loc (setm pkm pos (shrincs_fxmss_leaf_public_key pp (panchor pos) xs))
              (lblkQ'' (Some pp) false (rcons Q (panchor pos, xs)) pkm)
              (lblkQ'' (Some pp) false (rcons Q (panchor pos, xs))
                 (setm pkm pos (shrincs_fxmss_leaf_public_key pp (panchor pos) xs)))).
      by move=> s0 s1 hpre;
         exact: (lblk''_pks_upd (Some pp) false (unzip1 (rcons Q (panchor pos, xs)))
                   (qmap_from 0 (rcons Q (panchor pos, xs))) pkm pos
                   (shrincs_fxmss_leaf_public_key pp (panchor pos) xs) s0 s1 hpre).
    have E1 : lf_commitsL pos [:: xs] (BLeaf tt) = [:: (panchor pos, xs)] by [].
    have E2 : pkm_of pp pos [:: xs] (BLeaf tt) pkm
            = setm pkm pos (shrincs_fxmss_leaf_public_key pp (panchor pos) xs) by [].
    have E3 : tvalL pp pos [:: xs] (BLeaf tt) = shrincs_fxmss_leaf_public_key pp (panchor pos) xs by [].
    have hs : size ([:: xs] : seq (seq N)) = size (leaf_paths (BLeaf tt)) by [].
    have hl : forall y, y \in ([:: xs] : seq (seq N)) -> size y = l.
      by move=> y; rewrite inE => /eqP ->.
    have hh := h [:: xs] hs hl.
    rewrite E1 E2 E3 cats1 in hh.
    exact: hh.
- exact: B.
- (* node: split the key draw, recurse left/right, hash the node *)
  move=> pos Q pkm k0 k1 huniq hbud h.
  have Esz : size (leaf_paths (BNode tl tr))
             = (size (leaf_paths tl) + size (leaf_paths tr))%N.
    by rewrite /= size_cat !size_map.
  rewrite Esz sample_keys_cat !bind_assoc.
  rewrite code_link_bind bind_assoc.
  set Lt := leaf_tws_under (rcons pos false) tl.
  set Rt := leaf_tws_under (rcons pos true) tr.
  have hbud' : (size Q + size (leaf_paths tl) + size (leaf_paths tr) <= n_max)%N.
    by move: hbud; rewrite Esz addnA.
  move: huniq; rewrite leaf_tws_under_node -/Lt -/Rt -catA => huniq.
  eapply (IHl (rcons pos false) Q pkm).
  + apply: (subseq_uniq _ huniq).
    apply: cat_subseq; first exact: subseq_refl.
    exact: suffix_subseq.
  + apply: leq_trans hbud'; exact: leq_addr.
  + move=> a hsza hsla.
    rewrite bind_assoc code_link_bind bind_assoc.
    eapply (IHr (rcons pos true) (Q ++ lf_commitsL (rcons pos false) a tl)
              (pkm_of pp (rcons pos false) a tl pkm)).
    * rewrite unzip1_cat unzip1_lf_commitsL -/Lt -/Rt.
      have hperm : perm_eq (Rt ++ unzip1 Q ++ Lt) (Lt ++ Rt ++ unzip1 Q).
        by rewrite (catA Rt) perm_catC.
      rewrite (perm_uniq hperm); exact: huniq.
    * rewrite size_cat size_lf_commitsL.
      exact: hbud'.
    * move=> bb hszb hslb.
      rewrite code_link_opr_bind.
      eapply (r_lcollq_known'' b pp (tnode pos)
                (inl (tvalL pp (rcons pos false) a tl,
                      tvalL pp (rcons pos true) bb tr) : (N × N) ∐ (D × 'nat))).
      rewrite lcollq_node_E.
      have hsz_ab : size (a ++ bb) = size (leaf_paths (BNode tl tr)).
        by rewrite size_cat hsza hszb Esz.
      have hall_ab : forall x, x \in a ++ bb -> size x = l.
        by move=> x; rewrite mem_cat => /orP[]; [exact: hsla|exact: hslb].
      have := h (a ++ bb) hsz_ab hall_ab.
      rewrite /lf_commitsL -/lf_commitsL /pkm_of -/pkm_of /tvalL -/tvalL.
      by rewrite -hsza take_size_cat // drop_size_cat // catA.
Unshelve. all: try exact: B.
Qed.

(* ================================================================== *)
(** ** ROOT BRIDGES: the positional [tvalL]/[lf_commitsL] (take/drop)
    coincide with the shared global-index [tval]/[lf_commits] at the
    root (the [lf_tree''_spec] continuation feeds these into GEN). *)

(** A uniq index-map over its own list is the identity. *)
Lemma map_nth_index_self (s : seq (seq bool)) (xs : seq (seq N)) :
  uniq s -> size xs = size s -> [seq nth [::] xs (index p s) | p <- s] = xs.
Proof.
move=> hu hsz.
apply: (eq_from_nth (x0 := [::])); first by rewrite size_map hsz.
move=> i; rewrite size_map => hi.
by rewrite (nth_map [::]) // index_uniq // -hsz.
Qed.

(** The take/drop slicing of the global key vector matches the global
    index access, so [lf_commitsL]/[tvalL] on the sliced keys reproduce
    the shared [lf_commits]/[tval]. *)
Lemma lf_commitsL_sub (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  lf_commitsL pos
    [seq nth [::] xss (index (pos ++ p) (leaf_paths (tshape sp))) | p <- leaf_paths t] t
  = lf_commits sp xss pos t.
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- by rewrite cats0.
- rewrite map_cat take_size_cat ?size_map // drop_size_cat ?size_map //.
  rewrite -!map_comp; congr (_ ++ _).
  + rewrite (eq_map (g := fun q => nth [::] xss
                (index (rcons pos false ++ q) (leaf_paths (tshape sp)))));
      last by move=> q /=; rewrite cat_rcons.
    exact: IHl.
  + rewrite (eq_map (g := fun q => nth [::] xss
                (index (rcons pos true ++ q) (leaf_paths (tshape sp)))));
      last by move=> q /=; rewrite cat_rcons.
    exact: IHr.
Qed.

Lemma tvalL_sub (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  (size pos + bt_depth t <= h_sf)%N ->
  tvalL pp pos
    [seq nth [::] xss (index (pos ++ p) (leaf_paths (tshape sp))) | p <- leaf_paths t] t
  = tval pp sp xss pos t.
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos hdepth /=.
- have hpos : (size pos <= h_sf)%N by move: hdepth; rewrite /= addn0.
  by rewrite cats0 /anchor_val leaf_pkE (lpk_panchor _ _ _ hpos).
- rewrite map_cat take_size_cat ?size_map // drop_size_cat ?size_map //.
  have hleft : (size (rcons pos false) + bt_depth tl <= h_sf)%N.
    apply: leq_trans hdepth.
    by rewrite size_rcons /= addSn addnS ltnS leq_add2l leq_maxl.
  have hright : (size (rcons pos true) + bt_depth tr <= h_sf)%N.
    apply: leq_trans hdepth.
    by rewrite size_rcons /= addSn addnS ltnS leq_add2l leq_maxr.
  rewrite -!map_comp; congr (nhash pp pos).
  + rewrite (eq_map (g := fun q => nth [::] xss
                (index (rcons pos false ++ q) (leaf_paths (tshape sp)))));
      last by move=> q /=; rewrite cat_rcons.
    exact: IHl hleft.
  + rewrite (eq_map (g := fun q => nth [::] xss
                (index (rcons pos true ++ q) (leaf_paths (tshape sp)))));
      last by move=> q /=; rewrite cat_rcons.
    exact: IHr hright.
Qed.

Lemma lf_commitsL_root (sp : seq bool) (xss : seq (seq N)) :
  size xss = size (leaf_paths (tshape sp)) ->
  lf_commitsL [::] xss (tshape sp) = leafcommitq sp xss.
Proof.
move=> hsz.
have huniq : uniq (leaf_paths (tshape sp)).
  by move: (gen_uniq sp); rewrite cats0 /leaf_tws_under => /map_uniq.
rewrite -lf_commits_leafcommitq -(lf_commitsL_sub sp xss [::] (tshape sp)).
congr lf_commitsL.
rewrite (eq_map (g := fun p => nth [::] xss (index p (leaf_paths (tshape sp)))));
  last by move=> p; rewrite cat0s.
by rewrite (map_nth_index_self (leaf_paths (tshape sp)) xss huniq hsz).
Qed.

Lemma tvalL_root (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  size xss = size (leaf_paths (tshape sp)) ->
  tvalL pp [::] xss (tshape sp) = fxroot pp sp xss.
Proof.
move=> hsz.
have huniq : uniq (leaf_paths (tshape sp)).
  by move: (gen_uniq sp); rewrite cats0 /leaf_tws_under => /map_uniq.
rewrite -tval_root -(tvalL_sub pp sp xss [::] (tshape sp)).
2: by rewrite /= add0n; exact: shrincs_fxmss_shape_wf.
congr tvalL.
rewrite (eq_map (g := fun p => nth [::] xss (index p (leaf_paths (tshape sp)))));
  last by move=> p; rewrite cat0s.
by rewrite (map_nth_index_self (leaf_paths (tshape sp)) xss huniq hsz).
Qed.

(* ================================================================== *)
(** ** Public value tree from the committed pk map + its bridge to the
    honest [value_tree_x] (the SIGN/FORGE auth-path/classifier source). *)

Definition value_tree_pks (sp : seq bool) (pkm : {fmap (seq bool) -> N}) : bt N :=
  bt_posmap (fun p => odflt n0 (getm pkm p)) [::] (tshape sp).

Lemma value_tree_pks_bridge (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pkm : {fmap (seq bool) -> N}) :
  (forall p, p \in leaf_paths (tshape sp) ->
     getm pkm p = Some (anchor_val pp sp xss p)) ->
  value_tree_pks sp pkm = valtree pp sp xss.
Proof.
move=> hpkm.
rewrite /value_tree_pks /value_tree_x.
by apply: eq_bt_posmap => q hq /=; rewrite (hpkm q hq).
Qed.

(** The pk-map produced by [pkm_of] (the GEN post-state's [rl_pks_loc]):
    its [getm] at a committed position is the honest leaf pk. *)
Lemma pkm_of_subE (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (t : bt unit) (pos : seq bool) (pkm0 : {fmap (seq bool) -> N}) (q : seq bool) :
  (size pos + bt_depth t <= h_sf)%N ->
  getm (pkm_of pp pos
          [seq nth [::] xss (index (pos ++ p0) (leaf_paths (tshape sp))) | p0 <- leaf_paths t]
          t pkm0) q
  = if q \in [seq pos ++ p0 | p0 <- leaf_paths t]
    then Some (anchor_val pp sp xss q)
    else getm pkm0 q.
Proof.
elim: t pos pkm0 q => [[]|tl IHl tr IHr] pos pkm0 q hdepth.
- rewrite /= setmE mem_seq1 !cats0.
  case: eqP => [->|_]; last by [].
  have hpos : (size pos <= h_sf)%N by move: hdepth; rewrite /= addn0.
  by rewrite /anchor_val leaf_pkE (lpk_panchor _ _ _ hpos).
- have HL : take (size (leaf_paths tl))
      [seq nth [::] xss (index (pos ++ p0) (leaf_paths (tshape sp))) | p0 <- leaf_paths (BNode tl tr)]
      = [seq nth [::] xss (index (rcons pos false ++ p0) (leaf_paths (tshape sp))) | p0 <- leaf_paths tl].
    rewrite /= map_cat take_size_cat ?size_map // -map_comp.
    by apply: eq_map => p0 /=; rewrite cat_rcons.
  have HR : drop (size (leaf_paths tl))
      [seq nth [::] xss (index (pos ++ p0) (leaf_paths (tshape sp))) | p0 <- leaf_paths (BNode tl tr)]
      = [seq nth [::] xss (index (rcons pos true ++ p0) (leaf_paths (tshape sp))) | p0 <- leaf_paths tr].
    rewrite /= map_cat drop_size_cat ?size_map // -map_comp.
    by apply: eq_map => p0 /=; rewrite cat_rcons.
  have EL : [seq pos ++ p0 | p0 <- [seq false :: p | p <- leaf_paths tl]]
          = [seq rcons pos false ++ p0 | p0 <- leaf_paths tl].
    by rewrite -map_comp; apply: eq_map => p0 /=; rewrite cat_rcons.
  have ER : [seq pos ++ p0 | p0 <- [seq true :: p | p <- leaf_paths tr]]
          = [seq rcons pos true ++ p0 | p0 <- leaf_paths tr].
    by rewrite -map_comp; apply: eq_map => p0 /=; rewrite cat_rcons.
  have hleft : (size (rcons pos false) + bt_depth tl <= h_sf)%N.
    apply: leq_trans hdepth.
    by rewrite size_rcons /= addSn addnS ltnS leq_add2l leq_maxl.
  have hright : (size (rcons pos true) + bt_depth tr <= h_sf)%N.
    apply: leq_trans hdepth.
    by rewrite size_rcons /= addSn addnS ltnS leq_add2l leq_maxr.
  rewrite [pkm_of pp pos _ (BNode tl tr) pkm0]/= HL HR
    (IHr _ _ _ hright) (IHl _ _ _ hleft).
  rewrite [in RHS]/= map_cat EL ER mem_cat.
  by case: (q \in [seq rcons pos false ++ p0 | p0 <- leaf_paths tl]);
     case: (q \in [seq rcons pos true ++ p0 | p0 <- leaf_paths tr]).
Qed.

Lemma getm_pkm_of (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  size xss = size (leaf_paths (tshape sp)) ->
  forall p, p \in leaf_paths (tshape sp) ->
    getm (pkm_of pp [::] xss (tshape sp) emptym) p = Some (anchor_val pp sp xss p).
Proof.
move=> hsz p hp.
have huniq : uniq (leaf_paths (tshape sp)).
  by move: (gen_uniq sp); rewrite cats0 /leaf_tws_under => /map_uniq.
have hshape : (size ([::] : seq bool) + bt_depth (tshape sp) <= h_sf)%N.
  by rewrite /= add0n; exact: (shrincs_fxmss_shape_wf h_sf sp).
have H := pkm_of_subE pp sp xss (tshape sp) [::] emptym p hshape.
have HE : [seq nth [::] xss (index ([::] ++ p0) (leaf_paths (tshape sp))) | p0 <- leaf_paths (tshape sp)] = xss.
  rewrite (eq_map (g := fun p0 => nth [::] xss (index p0 (leaf_paths (tshape sp)))));
    last by move=> p0; rewrite cat0s.
  by rewrite (map_nth_index_self (leaf_paths (tshape sp)) xss huniq hsz).
have Hpos : [seq [::] ++ p0 | p0 <- leaf_paths (tshape sp)] = leaf_paths (tshape sp).
  by rewrite -[RHS]map_id; apply: eq_map => p0; rewrite cat0s.
rewrite HE Hpos hp in H.
exact: H.
Qed.

(* ================================================================== *)
(** ** The reduction [R_leaf''] (ported from LeafReroot_v2;
    [gen_redL''] REORDERED so the tree build precedes [fillc] to match
    [gen5]'s draw order). *)

Definition lf_gpo'' : opsig := (LGETPP, ('unit, PP)).
Definition lf_cko'' : opsig := (LCHECK, ('nat × (D × (('list N) × 'nat)), 'bool)).

Local Notation RLLocs :=
  [fmap (shrincs_fxmss_st_loc PP N) ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; (shrincs_fxmss_log_loc M) ;
        (shrincs_fxmss_rom_loc PP N D M R) ; shrincs_fxmss_hcnt_loc ; (shrincs_fxmss_rt_loc M R) ;
        shrincs_fxmss_fcnt_loc ; (shrincs_fxmss_sd_loc D) ; rl_pks_loc ].

Definition leaf_ap (pp : PP) (sp : seq bool) (pkm : {fmap (seq bool) -> N})
    (q : nat) : seq N :=
  odflt [::] (cons_ap (nhash pp) [::] (value_tree_pks sp pkm) (spath sp q)).

Definition shrincs_fxmss_forgery_case_pks (pp : PP) (sp : seq bool) (pkm : {fmap (seq bool) -> N})
    (zi : nat * nat) (md : D) (ws : seq N * nat) (ap : seq N) : fcase :=
  extract (nhash pp) [::] (value_tree_pks sp pkm)
    (path_of_idx (h_sf - zi.1) zi.2) ap
    (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind pp zi md ws).

#[local] Arguments value_tree_pks : simpl never.
#[local] Arguments leaf_ap : simpl never.
#[local] Arguments shrincs_fxmss_forgery_case_pks : simpl never.
#[local] Arguments cons_ap : simpl never.
#[local] Arguments extract : simpl never.
#[local] Arguments shrincs_fxmss_wots_sign : simpl never.
#[local] Arguments coll_ev : simpl never.

(** The pk-map classifier equals the honest [shrincs_fxmss_forgery_case_at_N] when [pkm] holds the
    honest leaf pks (the FORGE verdict bridge). *)
Lemma shrincs_fxmss_forgery_case_pks_bridge (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pkm : {fmap (seq bool) -> N}) (zi : nat * nat) (md : D)
    (ws : seq N * nat) (ap : seq N) :
  (forall p, p \in leaf_paths (tshape sp) ->
     getm pkm p = Some (anchor_val pp sp xss p)) ->
  shrincs_fxmss_forgery_case_pks pp sp pkm zi md ws ap = shrincs_fxmss_forgery_case_at_N pp sp xss zi md ws ap.
Proof.
move=> hpkm.
by rewrite /shrincs_fxmss_forgery_case_pks /shrincs_fxmss_forgery_case (value_tree_pks_bridge pp sp xss pkm hpkm).
Qed.

Fixpoint lf_grind'' (zi : nat * nat) (d : D) (cs : seq nat) :
    raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lf_cqo'' (encode_adrs (gadrs zi), inr (d, c))
        (λ r, hs ← lf_grind'' zi d cs' ;;
              ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance lf_grind''_valid (L : Locations) zi d cs :
  ValidCode L I_MIW'' (lf_grind'' zi d cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

Definition lf_slot_grind'' (sp : seq bool) (sd : chMap 'nat D) (j : nat) :
    raw_code 'bool :=
  match getm sd j with
  | Some d =>
      hs ← lf_grind'' (posid (spath sp j)) d (iota 0 c_max) ;;
      ret (has (@grind_prp w l S_wn) hs)
  | None => ret true
  end.

#[local] Instance lf_slot_grind''_valid (L : Locations) sp sd j :
  ValidCode L I_MIW'' (lf_slot_grind'' sp sd j).
Proof.
rewrite /lf_slot_grind''; case: (getm sd j) => [d|]; last by apply valid_ret.
eapply valid_bind; first exact: lf_grind''_valid.
move=> hs; apply valid_ret.
Qed.

Fixpoint lf_gcheck'' (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) :
    raw_code 'bool :=
  match js with
  | [::] => ret true
  | j :: js' =>
      b ← lf_slot_grind'' sp sd j ;;
      bs ← lf_gcheck'' sp sd js' ;;
      ret (b && bs)
  end.

#[local] Instance lf_gcheck''_valid (L : Locations) sp sd js :
  ValidCode L I_MIW'' (lf_gcheck'' sp sd js).
Proof.
elim: js => [|j js IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: lf_slot_grind''_valid.
  move=> b; eapply valid_bind; first exact: IH.
  move=> bs; apply valid_ret.
Qed.

#[local] Instance lf_tree''_valid pos t :
  ValidCode RLLocs I_MIW'' (lf_tree'' pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- eapply valid_opr; first by fmap_solve.
  move=> pk; eapply valid_getr; first by fmap_solve. move=> pkm.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
- eapply valid_bind; first exact: IHl.
  move=> lv; eapply valid_bind; first exact: IHr.
  move=> rv; eapply valid_opr; first by fmap_solve.
  move=> y; apply valid_ret.
Qed.

Definition dummy_xss : 'list ('list N) := [::].

Definition gen_redL'' (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   _ ← opr lf_cqo'' (encode_adrs (gadrs (0, 0)), inl (n0, n0)) (λ r, ret r) ;;
   _ ← dN ;;
   _ ← dR ;;
   root ← lf_tree'' [::] (tshape sp) ;;
   sd ← fillc (iota 0 n_max) emptym ;;
   gok ← lf_gcheck'' sp sd (iota 0 (size (leaf_paths (tshape sp)))) ;;
   #assert gok ;;
   pp ← opr lf_gpo'' Datatypes.tt (λ p, ret p) ;;
   #put Lst := Some ((pp, root), (sp, dummy_xss)) ;;
   #put Lsd := sd ;;
   ret (pp, root)).

Definition sign_redL'' (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   pkm ← get rl_pks_loc ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     r ← dR ;;
     md ← (match getm sd (flidx st.2.1 mz.2) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
     #put Lrt := setm tb (mz.2, mz.1) r ;;
     #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
     wso ← opr lf_sgo''
             (index (spath st.2.1 (flidx st.2.1 mz.2))
                    (leaf_paths (tshape st.2.1)), md)
             (λ wo, ret wo) ;;
     match wso with
     | Some ws =>
         #put Llog := rcons lg mz.1 ;;
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret (Some ((posid (spath st.2.1 (flidx st.2.1 mz.2)), r),
                    (ws, leaf_ap st.1.1 st.2.1 pkm (flidx st.2.1 mz.2))))
     | None =>
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

Definition forge_redL'' (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get shrincs_fxmss_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   pkm ← get rl_pks_loc ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put shrincs_fxmss_fcnt_loc := fc.+1 ;;
   if b then
     let P := (fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
               && (m \notin lg))
              && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 md in
     match shrincs_fxmss_forgery_case_pks st.1.1 st.2.1 pkm sg.1.1 md sg.2.1 sg.2.2 with
     | FAnchor =>
         ans ← opr lf_cko'' (fanchoridx st.2.1 sg.1.1, (md, sg.2.1)) (λ a, ret a) ;;
         ret (P && ans)
     | fc' => ret (P && keepA fc')
     end
   else ret false).

#[export] Instance gen_redL''_valid (sp : 'list 'bool) :
  ValidCode RLLocs I_MIW'' (gen_redL'' sp).
Proof.
rewrite /gen_redL''.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> r; apply valid_ret.
move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first exact: lf_tree''_valid. move=> root.
eapply valid_bind; first by apply fill_code_valid. move=> sd.
eapply valid_bind; first exact: lf_gcheck''_valid. move=> gok.
eapply valid_assertD => _.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> p; apply valid_ret.
move=> pp.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance sign_redL''_valid (mz : M × ('nat × 'nat)) :
  ValidCode RLLocs I_MIW'' (sign_redL'' mz).
Proof.
rewrite /sign_redL''.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_getr; first by fmap_solve. move=> pkm.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> r.
eapply valid_bind.
  case: (getm sd _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> wo; apply valid_ret.
move=> wso.
case: wso => [ws|]; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance hash_redL''_valid (x : ROIN) :
  ValidCode RLLocs I_MIW'' (hash5 x).
Proof.
rewrite /hash5 /hash5_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance forge_redL''_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode RLLocs I_MIW'' (forge_redL'' b m sg).
Proof.
rewrite /forge_redL''.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_getr; first by fmap_solve. move=> pkm.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: b; last by apply valid_ret.
case: (shrincs_fxmss_forgery_case_pks _ _ _ _ _ _ _) => [q x y|q x a0|q a|].
- apply valid_ret.
- apply valid_ret.
- apply valid_ret.
- eapply valid_bind.
    eapply valid_opr; first by fmap_solve. move=> a; apply valid_ret.
  move=> ans; apply valid_ret.
Qed.

#[local] Arguments lf_tree'' : simpl never.
#[local] Arguments gen_redL'' : simpl never.
#[local] Arguments sign_redL'' : simpl never.
#[local] Arguments forge_redL'' : simpl never.
Opaque gen_redL'' sign_redL'' forge_redL''.

Definition R_leaf'' (b : bool) : package I_MIW'' IG.
Proof.
notypeclasses refine [package RLLocs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { gen_redL'' sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (m) { sign_redL'' m } ;
    [ FXHASH ] : { ROIN ~> D } (x) { hash5 x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { forge_redL'' b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge_redL''_valid. } }
    { intro x; exact: hash_redL''_valid. } }
  { intro m; exact: sign_redL''_valid. } }
{ intro sp; exact: gen_redL''_valid. }
Defined.

(* ================================================================== *)
(** ** The TWO-SIDED GEN invariant [lf_inv2] (couple_cross shrincs_fxmss_st ↔ MIW
    state; LHS [shrincs_fxmss_st] holds the real [xss], RHS holds [dummy_xss]). *)

Definition IGN2 : Locations := IGN''.

(** M5 lift: the counter [qL] + dense-prefix coupling [slog = iota 0 qL]
    is replaced by the used-set [us] (loc 410) + the used↔slog bijection
    [slog =i lidx-image(domm us)] with all used ids valid.  This is the
    reduction mirror of [DIGrel_L] clause (v). *)
Definition RLf2 (sto_L sto_R : option FXST) (po : option PP)
    (tg : {fmap nat -> (adrs_sf_ch × ('list N))}) (tw : seq adrs_sf_ch)
    (rv : bool) (pkm : {fmap (seq bool) -> N})
    (us : chMap ('nat × 'nat) 'unit) (slog : seq nat) : Prop :=
  match sto_L with
  | None =>
      [/\ sto_R = None, po = None, tg = emptym, tw = [::]
        & [/\ rv = false, pkm = emptym, us = emptym & slog = [::]]]
  | Some st =>
      [/\ sto_R = Some (st.1, (st.2.1, dummy_xss)),
          po = Some st.1.1, rv = true,
          tg = qmap_from 0 (leafcommitq st.2.1 st.2.2)
        & [/\ tw = leaf_tws st.2.1,
              (forall p, p \in leaf_paths (tshape st.2.1) ->
                 getm pkm p = Some (anchor_val st.1.1 st.2.1 st.2.2 p)),
              [/\ {subset slog <= [seq flidx st.2.1 zi | zi <- domm us]}
                & forall zi, zi \in domm us -> flok st.2.1 zi]
            & st.1.2 = fxroot st.1.1 st.2.1 st.2.2]]
  end.

Definition lf_inv2 : precond :=
  heap_ignore IGN2
  ⋊ rel_app [:: (lhs, shrincs_fxmss_st_loc PP N) ; (rhs, shrincs_fxmss_st_loc PP N) ;
                (rhs, miw_pp_loc) ; (rhs, miw_tgts_loc) ; (rhs, miw_tws_loc) ;
                (rhs, miw_rev_loc) ; (rhs, rl_pks_loc) ;
                (lhs, shrincs_fxmss_used_loc) ; (rhs, miw_slog_loc) ] RLf2.

Arguments lf_inv2 : simpl never.

Lemma lf_inv2E s0 s1 :
  lf_inv2 (s0, s1) ->
  heap_ignore IGN2 (s0, s1) /\
  RLf2 (get_heap s0 (shrincs_fxmss_st_loc PP N)) (get_heap s1 (shrincs_fxmss_st_loc PP N))
       (get_heap s1 miw_pp_loc) (get_heap s1 miw_tgts_loc)
       (get_heap s1 miw_tws_loc) (get_heap s1 miw_rev_loc)
       (get_heap s1 rl_pks_loc) (get_heap s0 shrincs_fxmss_used_loc)
       (get_heap s1 miw_slog_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma lf_inv2I s0 s1 :
  heap_ignore IGN2 (s0, s1) ->
  RLf2 (get_heap s0 (shrincs_fxmss_st_loc PP N)) (get_heap s1 (shrincs_fxmss_st_loc PP N))
       (get_heap s1 miw_pp_loc) (get_heap s1 miw_tgts_loc)
       (get_heap s1 miw_tws_loc) (get_heap s1 miw_rev_loc)
       (get_heap s1 rl_pks_loc) (get_heap s0 shrincs_fxmss_used_loc)
       (get_heap s1 miw_slog_loc) ->
  lf_inv2 (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** GEN-entry weakening: at the start (LHS [shrincs_fxmss_st] = None), [lf_inv2]
    gives the empty GEN block [lblk''] (IGN2 = IGN'', so heap_ignore
    transfers directly). *)
Lemma lfinv2_init s0 s1 :
  lf_inv2 (s0, s1) ->
  get_heap s0 (shrincs_fxmss_st_loc PP N) = None ->
  lblk'' None false [::] emptym emptym (s0, s1).
Proof.
move=> /lf_inv2E [hign hR] hst.
rewrite hst in hR.
case: hR => hsoR hpp htg htw [hrv hpkm hqL hslog].
split; [exact: hign | exact: hpp | exact: hrv | exact: htw |].
by split; [exact: htg | exact: hpkm | exact: hqL | exact: hslog].
Qed.

(** SIGN/FORGE sync helpers over [lf_inv2] (synced get / synced put of a
    loc disjoint from all RLf2-tracked locs). *)
Lemma lf_inv2_get_pre (l0 : Location) :
  l0.1 \notin domm IGN'' -> get_pre_cond l0 lf_inv2.
Proof. by move=> hl0 s0 s1 [hign _]; exact: hign. Qed.

Ltac lf_get2_pre := apply: lf_inv2_get_pre; rewrite /IGN''; fmap_solve.

(** Rem-aware variant: peel any [⋊ rem] wrappers, then discharge the
    synced get against [lf_inv2] (stops at [lf_inv2] since the direct
    [apply] only unifies the bare invariant, not [_ ⋊ rem]). *)
Ltac lf_getr :=
  first [ apply: lf_inv2_get_pre; rewrite /IGN''; fmap_solve
        | apply: get_pre_cond_conj; lf_getr ].

Lemma lf_inv2_set_fx (l0 : Location) (v : l0) s0 s1 :
  l0.1 != (shrincs_fxmss_st_loc PP N).1 ->
  l0.1 != miw_pp_loc.1 ->
  l0.1 != miw_tgts_loc.1 ->
  l0.1 != miw_tws_loc.1 ->
  l0.1 != miw_rev_loc.1 ->
  l0.1 != rl_pks_loc.1 ->
  l0.1 != shrincs_fxmss_used_loc.1 ->
  l0.1 != miw_slog_loc.1 ->
  lf_inv2 (s0, s1) ->
  lf_inv2 (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h1 h2 h3 h4 h5 h6 h7 h8 /lf_inv2E [hign hR].
apply: lf_inv2I; first by apply: heap_ignore_set_both.
rewrite !get_set_heap_neq //; by rewrite eq_sym.
Qed.

Ltac lf_put2_tr :=
  let s0 := fresh "s0" in let s1 := fresh "s1" in let hp := fresh "hp" in
  rewrite /put_pre_cond; move=> s0 s1 hp;
  refine (lf_inv2_set_fx _ _ _ _ _ _ _ _ _ _ _ _ hp); by [].

Ltac lf_put2_pre :=
  repeat (apply: put_pre_cond_conj; last (apply: put_pre_cond_rem; by []));
  lf_put2_tr.

(* ================================================================== *)
(** ** GEN-perfect prep: [lblk''_set_rev] + the current grind/gcheck
    relational specs (routed via [lf_cqo'']/[MIW_leaf''], over [lblk'']). *)

Lemma lblk''_set_rev (po : option PP) tw tg pkm s0 s1 :
  lblk'' po false tw tg pkm (s0, s1) ->
  lblk'' po true tw tg pkm (s0, set_heap s1 miw_rev_loc true).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by split; [rewrite get_set_heap_neq | rewrite get_set_heap_neq | exact: h6
            | rewrite get_set_heap_neq].
Qed.

Lemma r_grind''_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (zi : nat * nat) (d : D) (cs : seq nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : chList 'nat -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (gadrs zi) (d, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_grind'' zi d cs) (MIW_leaf'' b)) k1 ⦃ post ⦄.
Proof.
move=> zi d cs; elim: cs => [|c cs IH] rv tw tg pkm c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lcollq_known'' b).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite lcollq_grind_E /= in h *.
Qed.

Lemma r_slot_grind''_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (j : nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (match getm sd j with
              | Some d => slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d
              | None => true
              end) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_slot_grind'' sp sd j) (MIW_leaf'' b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd j rv tw tg pkm c0 k1 h.
rewrite /lf_slot_grind''.
case E: (getm sd j) => [d|]; rewrite E /= in h.
- rewrite code_link_bind bind_assoc.
  eapply (r_grind''_spec b pp post (posid (spath sp j)) d (iota 0 c_max)).
  rewrite code_link_ret_bind has_grind_find_ctr.
  rewrite -/(slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d).
  exact: h.
- by rewrite code_link_ret_bind; exact: h.
Qed.

Lemma r_gcheck''_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (all (fun j => match getm sd j with
                | Some d => slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d
                | None => true
                end) js) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk'' (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_gcheck'' sp sd js) (MIW_leaf'' b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd js; elim: js => [|j js IH] rv tw tg pkm c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_slot_grind''_spec b pp post sp sd j).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite code_link_ret_bind.
Qed.

(* ================================================================== *)
(** ** The current perfects.  GEN couples [gen5]'s [skeys] draw to the
    per-leaf sampling via [lf_tree''_spec]; SIGN routes [ws] via LSIGN;
    FORGE via [shrincs_fxmss_forgery_case_pks]. *)

Lemma resolve_lgp'' (bb : bool) (u : unit) :
  resolve (MIW_leaf'' bb) lf_gpo'' u = miw_getpp.
Proof. by case: bb; simplify_linking. Qed.

Lemma resolve_lsg'' (bb : bool) (j : nat) (md : D) :
  resolve (MIW_leaf'' bb) lf_sgo'' (j, md) = mr_sign j md.
Proof. by case: bb; simplify_linking. Qed.

Lemma resolve_lck''_true (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_leaf'' true) lf_cko'' (j, mw) = miw_win j mw.
Proof. by simplify_linking. Qed.

Lemma resolve_lck''_false (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_leaf'' false) lf_cko'' (j, mw) = ret false.
Proof. by simplify_linking. Qed.

Transparent gen_redL'' sign_redL'' forge_redL''.

(** [getSome] at a concrete [Some]: reduces to the carried value. *)
Lemma getSomeE {A : Type} (a : A) (h : isSome (Some a)) :
  getSome (Some a) h = a.
Proof. by []. Qed.

(** The signed-index log grows by one: [iota 0 q ++ [:: q] = iota 0 q.+1]. *)
Lemma iota_rcons_S (n : nat) : rcons (iota 0 n) n = iota 0 n.+1.
Proof. by rewrite -addn1 iotaD add0n cats1. Qed.

(** M5 lift, used↔slog bijection support.  A valid, fresh id's slot
    [flidx] is absent from the [flidx]-image of the used-set (injectivity
    of [flidx] on valid ids). *)
Lemma flidx_notin_image (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  flok sp zi -> zi \notin domm us ->
  (forall zi', zi' \in domm us -> flok sp zi') ->
  flidx sp zi \notin [seq flidx sp zi' | zi' <- domm us].
Proof.
move=> hzi hfresh hval; apply/negP => /mapP [zi' hzi' heq].
have hv' := hval zi' hzi'.
have hzz := leafid_index_inj h_sf sp zi zi' hzi hv' heq.
by move: hfresh; rewrite hzz => /negP hn; exact: (hn hzi').
Qed.

(** The [flidx]-image is monotone in the used-set (adding an id only
    grows it). *)
Lemma image_subset_setm (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  {subset [seq flidx sp zi' | zi' <- domm us]
       <= [seq flidx sp zi' | zi' <- domm (setm us zi Datatypes.tt)]}.
Proof.
move=> x /mapP [zi' hzi' ->]; apply/mapP; exists zi'; last by [].
by rewrite domm_set in_fsetU1 hzi' orbT.
Qed.

(** The fresh id's slot is in the grown image. *)
Lemma flidx_in_image_setm (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  flidx sp zi \in [seq flidx sp zi' | zi' <- domm (setm us zi Datatypes.tt)].
Proof. by apply/mapP; exists zi; rewrite // domm_set in_fsetU1 eqxx. Qed.

(** All ids in the grown used-set are valid, given the fresh id is. *)
Lemma used_valid_setm (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  flok sp zi -> (forall zi', zi' \in domm us -> flok sp zi') ->
  forall zi', zi' \in domm (setm us zi Datatypes.tt) -> flok sp zi'.
Proof.
move=> hzi hval zi'; rewrite domm_set in_fsetU1.
by case/orP=> [/eqP -> // | ]; exact: hval.
Qed.

(** SIGN coupling: at a leaf index [q] in range, with [pkm] holding the
    honest leaf pks, the honest signer [shrincs_fxmss_sign_x] equals the reduction's
    LSIGN-routed form ([leaf_sign] at the committed tweak, auth-path via
    [leaf_ap]).  The auth path is always [Some] in range (totality via
    [shrincs_fxmss_sign_path_leaf] + [isSome_cons_ap]), so the structural [match] on
    [leaf_sign] alone reproduces [shrincs_fxmss_sign_x]'s [Some]/[None]. *)
Lemma shrincs_fxmss_sign_x_eq_redsign (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pkm : {fmap (seq bool) -> N}) (q : nat) (r : R) (md : D) :
  (q < size (leaf_paths (tshape sp)))%N ->
  (forall p, p \in leaf_paths (tshape sp) ->
     getm pkm p = Some (anchor_val pp sp xss p)) ->
  shrincs_fxmss_sign_x PP N D R F Tl Hgrind Htree S_wn c_max h_sf pp sp xss q r md
  = match leaf_sign pp (panchor (spath sp q)) (nth [::] xss q) md with
    | Some ws => Some ((posid (spath sp q), r), (ws, leaf_ap pp sp pkm q))
    | None => None
    end.
Proof.
move=> hq hpkm.
rewrite leaf_signE
  (lsign_panchor pp (spath sp q) (nth [::] xss q) md
    (shrincs_fxmss_sign_path_size h_sf sp q hq)).
rewrite /shrincs_fxmss_sign_x /leaf_ap (value_tree_pks_bridge pp sp xss pkm hpkm).
have hsubv : subtree_at (valtree pp sp xss) (spath sp q)
             = Some (BLeaf (fpk_of (posid (spath sp q)) pp (nth [::] xss q))).
  rewrite /value_tree_x subtree_at_posmap (shrincs_fxmss_sign_path_leaf h_sf sp q hq) /=.
  by rewrite (index_sign_path h_sf sp q hq).
have [ap Hap] :
    exists ap, cons_ap (nhash pp) [::] (valtree pp sp xss) (spath sp q) = Some ap.
  have Hs := isSome_cons_ap (nhash pp) [::] (valtree pp sp xss) (spath sp q).
  rewrite hsubv /= in Hs.
  case E: (cons_ap (nhash pp) [::] (valtree pp sp xss) (spath sp q)) => [ap|].
  - by exists ap.
  - by rewrite E in Hs.
rewrite Hap /=.
by case: (shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max
            (posid (spath sp q)).1 (posid (spath sp q)).2 pp (nth [::] xss q) md).
Qed.

(** FORGE verdict (REAL): G5f's [fverd (fun _ => true)] equals the
    [shrincs_fxmss_forgery_case_pks] classify-and-LCHECK verdict; the FAnchor LCHECK wins by
    [shrincs_fxmss_forgery_case_FAnchor].  Over [lf_inv2] (RHS state is the dummy re-root), with
    [pkm] holding the honest leaf pks (so [shrincs_fxmss_forgery_case_pks = shrincs_fxmss_forgery_case_at_N]). *)
Lemma r_leaf_forge_verdict'' (st : FXST) (pkm : {fmap (seq bool) -> N})
    (lg : seq M) (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  (forall p, p \in leaf_paths (tshape st.2.1) ->
     getm pkm p = Some (anchor_val st.1.1 st.2.1 st.2.2 p)) ->
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv2 ⋊ rem_lhs Lst (Some st)
              ⋊ rem_rhs Lst (Some (st.1, (st.2.1, dummy_xss)))
              ⋊ rem_rhs rl_pks_loc pkm) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            (fun _ => true) st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_pks st.1.1 st.2.1 pkm sg.1.1 d sg.2.1 sg.2.2 with
          | FAnchor =>
              v ← get miw_rev_loc ;;
              ans ← (#assert v ;;
                     tgts ← get miw_tgts_loc ;;
                     match getm tgts (fanchoridx st.2.1 sg.1.1) with
                     | Some (t0, m0) =>
                         ppo ← get miw_pp_loc ;;
                         match ppo with
                         | Some pp => ret (leaf_win pp t0 d sg.2.1 m0)
                         | None =>
                             pp ← dPP ;;
                             #put miw_pp_loc := Some pp ;;
                             ret (leaf_win pp t0 d sg.2.1 m0)
                         end
                     | None => ret false
                     end) ;;
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && ans)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv2 (s0, s1) ⦄.
Proof.
move=> hpkm.
rewrite (shrincs_fxmss_forgery_case_pks_bridge st.1.1 st.2.1 st.2.2 pkm sg.1.1 d sg.2.1 sg.2.2 hpkm).
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
eapply (r_fact (st.1.2 = fxroot st.1.1 st.2.1 st.2.2)).
  { move=> s0 s1 [[[hinv hr] _] _].
    move/lf_inv2E: hinv => [_ hRLf].
    rewrite /rem_lhs /= in hr.
    rewrite hr in hRLf.
    by case: hRLf => _ _ _ _ [_ _ _ hroot]; exact: hroot. }
move=> hroot.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|].
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- (* FAnchor: the real LCHECK wins *)
  eapply (r_get_rhs_known miw_rev_loc true).
    { move=> s0 s1 [[[hinv hr] _] _].
      move/lf_inv2E: hinv => [_ hRLf].
      rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
      by case: hRLf => _ _ hrv _ _. }
  rewrite [assertD true _]/=.
  eapply (r_get_rhs_known miw_tgts_loc (qmap_from 0 (leafcommitq st.2.1 st.2.2))).
    { move=> s0 s1 [[[hinv hr] _] _].
      move/lf_inv2E: hinv => [_ hRLf].
      rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
      by case: hRLf => _ _ _ htg _. }
  case Eans: P; last first.
  + destruct (qmap_from 0 (leafcommitq st.2.1 st.2.2)
                (fanchoridx st.2.1 sg.1.1)) as [[t0 m0]|] eqn:Eg;
      rewrite Eg /=.
    * eapply (r_get_rhs_known miw_pp_loc (Some st.1.1)).
        { move=> s0 s1 [[[hinv hr] _] _].
          move/lf_inv2E: hinv => [_ hRLf].
          rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
          by case: hRLf => _ hpo _ _ _. }
      apply r_ret => s0 s1 hpre.
      split; last by move: hpre => [[[hinv _] _] _]; exact: hinv.
      by [].
    * apply r_ret => s0 s1 hpre.
      split; last by move: hpre => [[[hinv _] _] _]; exact: hinv.
      by [].
  + have hvm : fxvermd st.1.1 (fxroot st.1.1 st.2.1 st.2.2)
                 sg.1.1 d sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [hin hpos hrec] :=
      shrincs_fxmss_forgery_case_FAnchor st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 hvm E.
    have Eidx : fanchoridx st.2.1 sg.1.1
              = index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                      (leaf_paths (tshape st.2.1)).
      by rewrite /fanchor_idx.
    rewrite Eidx (getm_leafcommitq st.2.1 st.2.2 _ hin) /=.
    eapply (r_get_rhs_known miw_pp_loc (Some st.1.1)).
      { move=> s0 s1 [[[hinv hr] _] _].
        move/lf_inv2E: hinv => [_ hRLf].
        rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
        by case: hRLf => _ hpo _ _ _. }
    have hwin : leaf_win st.1.1
                  (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)) d sg.2.1
                  (nth [::] st.2.2
                     (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                            (leaf_paths (tshape st.2.1)))) = true.
	      rewrite (leaf_win_panchor st.1.1
	        (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2) d sg.2.1
	        (nth [::] st.2.2
	          (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
	            (leaf_paths (tshape st.2.1))))
	        (leaf_path_size st.2.1 _ hin)); apply/eqP.
      by rewrite {1}hpos; exact: hrec.
    apply r_ret => s0 s1 hpre; split.
    * by rewrite hwin.
    * by move: hpre => [[[hinv _] _] _]; exact: hinv.
Qed.

(** FORGE verdict (IDEAL): G6f's [fverd keepA] equals the
    [shrincs_fxmss_forgery_case_pks] classify-and-LCHECK verdict under [MIW_leaf'' false]
    (LCHECK = false = keepAnchor on FAnchor). *)
Lemma r_leaf_forge_verdict''_ideal (st : FXST) (pkm : {fmap (seq bool) -> N})
    (lg : seq M) (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  (forall p, p \in leaf_paths (tshape st.2.1) ->
     getm pkm p = Some (anchor_val st.1.1 st.2.1 st.2.2 p)) ->
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv2 ⋊ rem_lhs Lst (Some st)
              ⋊ rem_rhs Lst (Some (st.1, (st.2.1, dummy_xss)))
              ⋊ rem_rhs rl_pks_loc pkm) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            keepA st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_pks st.1.1 st.2.1 pkm sg.1.1 d sg.2.1 sg.2.2 with
          | FAnchor =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && false)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv2 (s0, s1) ⦄.
Proof.
move=> hpkm.
rewrite (shrincs_fxmss_forgery_case_pks_bridge st.1.1 st.2.1 st.2.2 pkm sg.1.1 d sg.2.1 sg.2.2 hpkm).
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split.
  + by rewrite andbF.
  + by move: hpre => [[[hinv _] _] _]; exact: hinv.
Qed.

(** M5 lift: the SIGN-coupling tail (from the [shrincs_fxmss_used] tracked put
    onward), shared unchanged by all four SIGN sub-branches (both perfects,
    both digest-slot cases).  The lifted SIGN body writes [shrincs_fxmss_used] (a
    tracked loc), so the tracked put + the two ROM puts are deferred to
    [set_heap] form; the RHS [mr_sign] reads (slog/tgts/pp) are discharged
    off the buried [lf_inv2]; freshness of the appended slot [flidx zi] in
    [slog] is the used↔slog bijection (subset + [flidx_notin_image]); the
    two [r_ret] leaves reconstruct [lf_inv2] with the grown used-set
    ([image_subset_setm] / [flidx_in_image_setm] / [used_valid_setm]). *)

Lemma R_leaf''_real (b : bool) :
  perfect IG (G5 b) (R_leaf'' b ∘ MIW_leaf'' true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ lf_inv2).
{ rewrite /lf_inv2. ssprove_invariant. by rewrite /rel_empty /RLf2. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5 /gen5_body /gen_redL''.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (isSome sto = isSome sto')).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  rewrite code_link_assertD.
  eapply r_assertD; first by rewrite eIS.
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 eIS => [pk|] e0 eIS; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), lblk'' None false [::] emptym emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    rewrite /rem_lhs /= in hrem0.
    exact: (lfinv2_init s0 s1 hinv hrem0). }
  simpl.
  rewrite (resolve_lcq'' true (encode_adrs (gadrs (0, 0)))
             (inl (n0, n0) : (N × N) ∐ (D × 'nat))) /miw_collq.
  eapply (r_get_bind_rhs miw_pp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (lblk''_set_pp pp _ _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite code_link_bind.
  eapply (lf_tree''_spec true pp _ [::] (tshape arg) [::] emptym).
  + exact: gen_uniq.
  + by apply: gen_bud.
  move=> xss hxsz hkeys.
  cbv beta.
  rewrite cat0s.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  eapply (r_scheme_bind (fillc (iota 0 n_max) emptym)); first exact: fill_code_valid.
  move=> sd; cbv beta.
  rewrite code_link_bind.
  eapply (r_gcheck''_spec true pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  simpl.
  rewrite (resolve_lgp'' true Datatypes.tt) /miw_getpp.
  eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (lblk''_set_rev _ _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrv htws [htgts hpkm hqL hslog].
  split; first by rewrite (tvalL_root pp arg xss hxsz).
  apply: lf_inv2I.
  + apply: heap_ignore_set_both.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign.
  + get_heap_simpl.
    rewrite hpp hrv htws htgts hpkm hqL hslog.
    rewrite (tvalL_root pp arg xss hxsz) (lf_commitsL_root arg xss hxsz)
            unzip1_leafcommitq.
    split; [ by [] | by [] | by [] | by [] |].
    split; [ by [] | | | by [] ].
    + by move=> p hp; rewrite (getm_pkm_of pp arg xss hxsz p hp).
    + split.
      * by move=> x; rewrite in_nil.
      * by move=> zi; rewrite domm0 in_fset0.
- (* SIGN *)
  rewrite /sign5 /sign5_body /sign_redL''.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_pre. } move=> sc.
  ssprove_sync => hsc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  (* the [getSome] asserts (diverging conditions, aligned by [eIS]) *)
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  (* concretize both states; the [None] cases are killed by the proofs *)
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  (* the RHS state is the LHS state with a dummy key list (RLf2 [Some] branch) *)
  eapply (r_fact (stR = (stL.1, (stL.2.1, dummy_xss)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  (* shrincs_fxmss_used : synced used-set read (loc 410), both sides agree *)
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => usr.
  eapply (r_fact (us = usr)).
    { move=> s0 s1 [[[[hinv _] _] hrq] hrqr].
      move/lf_inv2E: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hrq hrqr.
      rewrite -hrq -hrqr.
      apply: hign; by rewrite /IGN2 /IGN''; fmap_solve. }
  move=> ?; subst usr.
  (* lg, mp, tb, sd : synced reads *)
  ssprove_sync. { lf_getr. } move=> lg.
  ssprove_sync. { lf_getr. } move=> mp.
  ssprove_sync. { lf_getr. } move=> tb.
  ssprove_sync. { lf_getr. } move=> sd.
  (* pkm : RHS-only read of [rl_pks] *)
  eapply r_get_remember_rhs => pkm.
  case Hg: [&& flok stL.2.1 arg.2 & arg.2 \notin domm us]; last first.
  { (* FALSE branch: both [put shrincs_fxmss_scnt; ret None] *)
    ssprove_sync. { lf_put2_pre. }
    apply r_ret => s0 s1 hpre.
    split; first by [].
    by move: hpre => [[[[[hinv _] _] _] _] _]; exact: hinv. }
  (* TRUE branch: valid + fresh leaf id *)
  move: Hg => /andP [hfok hfresh].
  have Hli := leafid_index_lt h_sf stL.2.1 arg.2 hfok.
  (* the pk-map condition (for the coupling lemma + auth-path) *)
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 [[[[[hinv hstoL] hstoR] _] _] hpkmr].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL hstoR in hR.
      case: hR => _ _ _ _ [_ hpk _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  (* r <- dR (synced scheme) *)
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  (* md (synced): the leaf-keyed slot [flidx st.2.1 arg.2] *)
  case: (sd (flidx stL.2.1 arg.2)) => [md|]; last first.
  { (* md sampled from dD *)
    rewrite ?(code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc /=.
    eapply r_scheme_bind; first exact: prog_valid. move=> md.
    ssprove_code_simpl. simpl.
   eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  rewrite (shrincs_fxmss_sign_x_eq_redsign stL.1.1 stL.2.1 stL.2.2 pkm
             (flidx stL.2.1 arg.2) r md Hli hpkm);
  rewrite !(index_sign_path h_sf stL.2.1 (flidx stL.2.1 arg.2) Hli);
  eapply r_get_remember_rhs => v;
  (eapply r_bind_assertD_rhs;
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hvrem;
     rewrite !get_set_heap_neq // in hvrem;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     rewrite hstoL husL hvrem in hR;
     destruct hR as [_ _ _ _ [_ _ [hsub hval] _]];
     pose proof (flidx_notin_image stL.2.1 us arg.2 hfok hfresh hval) as hni;
     exact (contra (hsub (flidx stL.2.1 arg.2)) hni)
   | idtac ]);
  intros _;
  (eapply (r_get_bind_rhs miw_tgts_loc
             (qmap_from 0 (leafcommitq stL.2.1 stL.2.2)));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ _ _ htg _]; rewrite htg; reflexivity
   | idtac ]);
  rewrite (getm_leafcommitq_at stL.2.1 stL.2.2 (flidx stL.2.1 arg.2) Hli);
  (eapply (r_get_bind_rhs miw_pp_loc (Some stL.1.1));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ hpo _ _ _]; rewrite hpo; reflexivity
   | idtac ]);
  simpl;
  (case: (leaf_sign stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
           (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md) => [ws|];
   [ eapply r_put_rhs;
     simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpre1 E2]]; subst s0;
     destruct hpre1 as [s1B [hpre2 E3]]; subst s1A;
     destruct hpre2 as [s0B [hpre3 E4]]; subst s0A;
     destruct hpre3 as [s1C [hpre4 E5]]; subst s1B;
     destruct hpre4 as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E6]]; subst s1C;
     destruct hpreW1 as [s0D [hpreW2 E7]]; subst s0B;
     destruct hpreW2 as [s1E [hpreW3 E8]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E9]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E10]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E11]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       (apply: heap_ignore_set_r; first by rewrite mem_domm);
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x; rewrite mem_rcons in_cons; intro Hor;
         destruct (elimT orP Hor) as [Heq | hx];
         [ apply (elimT eqP) in Heq; subst x; exact: flidx_in_image_setm
         | exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx)) ]
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ]
   | simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpreWm E2]]; subst s0;
     destruct hpreWm as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E3]]; subst s1A;
     destruct hpreW1 as [s0D [hpreW2 E4]]; subst s0A;
     destruct hpreW2 as [s1E [hpreW3 E5]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E6]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E7]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E8]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x hx;
         exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx))
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ] ]). }
  ssprove_code_simpl. simpl.
  (* === SIGN coupling tail (md = sd sc) === *)
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  rewrite (shrincs_fxmss_sign_x_eq_redsign stL.1.1 stL.2.1 stL.2.2 pkm
             (flidx stL.2.1 arg.2) r md Hli hpkm);
  rewrite !(index_sign_path h_sf stL.2.1 (flidx stL.2.1 arg.2) Hli);
  eapply r_get_remember_rhs => v;
  (eapply r_bind_assertD_rhs;
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hvrem;
     rewrite !get_set_heap_neq // in hvrem;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     rewrite hstoL husL hvrem in hR;
     destruct hR as [_ _ _ _ [_ _ [hsub hval] _]];
     pose proof (flidx_notin_image stL.2.1 us arg.2 hfok hfresh hval) as hni;
     exact (contra (hsub (flidx stL.2.1 arg.2)) hni)
   | idtac ]);
  intros _;
  (eapply (r_get_bind_rhs miw_tgts_loc
             (qmap_from 0 (leafcommitq stL.2.1 stL.2.2)));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ _ _ htg _]; rewrite htg; reflexivity
   | idtac ]);
  rewrite (getm_leafcommitq_at stL.2.1 stL.2.2 (flidx stL.2.1 arg.2) Hli);
  (eapply (r_get_bind_rhs miw_pp_loc (Some stL.1.1));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ hpo _ _ _]; rewrite hpo; reflexivity
   | idtac ]);
  simpl;
  (case: (leaf_sign stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
           (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md) => [ws|];
   [ eapply r_put_rhs;
     simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpre1 E2]]; subst s0;
     destruct hpre1 as [s1B [hpre2 E3]]; subst s1A;
     destruct hpre2 as [s0B [hpre3 E4]]; subst s0A;
     destruct hpre3 as [s1C [hpre4 E5]]; subst s1B;
     destruct hpre4 as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E6]]; subst s1C;
     destruct hpreW1 as [s0D [hpreW2 E7]]; subst s0B;
     destruct hpreW2 as [s1E [hpreW3 E8]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E9]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E10]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E11]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       (apply: heap_ignore_set_r; first by rewrite mem_domm);
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x; rewrite mem_rcons in_cons; intro Hor;
         destruct (elimT orP Hor) as [Heq | hx];
         [ apply (elimT eqP) in Heq; subst x; exact: flidx_in_image_setm
         | exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx)) ]
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ]
   | simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpreWm E2]]; subst s0;
     destruct hpreWm as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E3]]; subst s1A;
     destruct hpreW1 as [s0D [hpreW2 E4]]; subst s0A;
     destruct hpreW2 as [s1E [hpreW3 E5]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E6]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E7]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E8]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x hx;
         exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx))
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ] ]).
- (* HASH *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_pre. } move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { lf_get2_pre. } move=> mp.
  case: (getm mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_pre. }
    ssprove_sync. { lf_put2_pre. }
    apply r_ret => s0 s1 hpre. split; first by []. exact: hpre. }
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_pre. }
  ssprove_sync. { lf_put2_pre. }
  apply r_ret => s0 s1 hpre. split; first by []. exact: hpre.
- (* FORGE *)
  destruct arg as [m sg].
  rewrite /forge_keep_body /forge_redL''.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_pre. } move=> fc.
  ssprove_code_simpl. simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  eapply (r_fact (stR = (stL.1, (stL.2.1, dummy_xss)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_getr. } move=> lg.
  ssprove_sync. { lf_getr. } move=> mp.
  ssprove_sync. { lf_getr. } move=> tb.
  ssprove_sync. { lf_getr. } move=> sd.
  eapply r_get_remember_rhs => pkm.
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 [[[hinv hstoL] hstoR] hpkmr].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL hstoR in hR.
      case: hR => _ _ _ _ [_ hpk _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  case Emd: (getm mp (sg.1.2, (stL.1, (sg.1.1, m)))) => [md|]; last first.
  { rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    eapply r_scheme_bind; first exact: prog_valid. move=> md.
    ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_pre. }
    ssprove_sync. { lf_put2_pre. }
    case: b; last first.
    { apply r_ret => s0 s1 hpre. split; first by [].
      by move: hpre => [[[hinv _] _] _]; exact: hinv. }
    exact: (r_leaf_forge_verdict'' stL pkm lg tb sd m sg md hpkm). }
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_pre. }
  ssprove_sync. { lf_put2_pre. }
  case: b; last first.
  { apply r_ret => s0 s1 hpre. split; first by [].
    by move: hpre => [[[hinv _] _] _]; exact: hinv. }
  exact: (r_leaf_forge_verdict'' stL pkm lg tb sd m sg md hpkm).
Qed.

Lemma R_leaf''_ideal (b : bool) :
  perfect IG (G6 b) (R_leaf'' b ∘ MIW_leaf'' false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ lf_inv2).
{ rewrite /lf_inv2. ssprove_invariant. by rewrite /rel_empty /RLf2. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5 /gen5_body /gen_redL''.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (isSome sto = isSome sto')).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  rewrite code_link_assertD.
  eapply r_assertD; first by rewrite eIS.
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 eIS => [pk|] e0 eIS; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), lblk'' None false [::] emptym emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    rewrite /rem_lhs /= in hrem0.
    exact: (lfinv2_init s0 s1 hinv hrem0). }
  simpl.
  rewrite (resolve_lcq'' false (encode_adrs (gadrs (0, 0)))
             (inl (n0, n0) : (N × N) ∐ (D × 'nat))) /miw_collq.
  eapply (r_get_bind_rhs miw_pp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (lblk''_set_pp pp _ _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite code_link_bind.
  eapply (lf_tree''_spec false pp _ [::] (tshape arg) [::] emptym).
  + exact: gen_uniq.
  + by apply: gen_bud.
  move=> xss hxsz hkeys.
  cbv beta.
  rewrite cat0s.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  eapply (r_scheme_bind (fillc (iota 0 n_max) emptym)); first exact: fill_code_valid.
  move=> sd; cbv beta.
  rewrite code_link_bind.
  eapply (r_gcheck''_spec false pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  simpl.
  rewrite (resolve_lgp'' false Datatypes.tt) /miw_getpp.
  eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (lblk''_set_rev _ _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrv htws [htgts hpkm hqL hslog].
  split; first by rewrite (tvalL_root pp arg xss hxsz).
  apply: lf_inv2I.
  + apply: heap_ignore_set_both.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign.
  + get_heap_simpl.
    rewrite hpp hrv htws htgts hpkm hqL hslog.
    rewrite (tvalL_root pp arg xss hxsz) (lf_commitsL_root arg xss hxsz)
            unzip1_leafcommitq.
    split; [ by [] | by [] | by [] | by [] |].
    split; [ by [] | | | by [] ].
    + by move=> p hp; rewrite (getm_pkm_of pp arg xss hxsz p hp).
    + split.
      * by move=> x; rewrite in_nil.
      * by move=> zi; rewrite domm0 in_fset0.
- (* SIGN *)
  rewrite /sign5 /sign5_body /sign_redL''.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_pre. } move=> sc.
  ssprove_sync => hsc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  (* the [getSome] asserts (diverging conditions, aligned by [eIS]) *)
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  (* concretize both states; the [None] cases are killed by the proofs *)
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  (* the RHS state is the LHS state with a dummy key list (RLf2 [Some] branch) *)
  eapply (r_fact (stR = (stL.1, (stL.2.1, dummy_xss)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  (* shrincs_fxmss_used : synced used-set read (loc 410), both sides agree *)
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => usr.
  eapply (r_fact (us = usr)).
    { move=> s0 s1 [[[[hinv _] _] hrq] hrqr].
      move/lf_inv2E: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hrq hrqr.
      rewrite -hrq -hrqr.
      apply: hign; by rewrite /IGN2 /IGN''; fmap_solve. }
  move=> ?; subst usr.
  (* lg, mp, tb, sd : synced reads *)
  ssprove_sync. { lf_getr. } move=> lg.
  ssprove_sync. { lf_getr. } move=> mp.
  ssprove_sync. { lf_getr. } move=> tb.
  ssprove_sync. { lf_getr. } move=> sd.
  (* pkm : RHS-only read of [rl_pks] *)
  eapply r_get_remember_rhs => pkm.
  case Hg: [&& flok stL.2.1 arg.2 & arg.2 \notin domm us]; last first.
  { (* FALSE branch: both [put shrincs_fxmss_scnt; ret None] *)
    ssprove_sync. { lf_put2_pre. }
    apply r_ret => s0 s1 hpre.
    split; first by [].
    by move: hpre => [[[[[hinv _] _] _] _] _]; exact: hinv. }
  (* TRUE branch: valid + fresh leaf id *)
  move: Hg => /andP [hfok hfresh].
  have Hli := leafid_index_lt h_sf stL.2.1 arg.2 hfok.
  (* the pk-map condition (for the coupling lemma + auth-path) *)
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 [[[[[hinv hstoL] hstoR] _] _] hpkmr].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL hstoR in hR.
      case: hR => _ _ _ _ [_ hpk _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  (* r <- dR (synced scheme) *)
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  (* md (synced): the leaf-keyed slot [flidx st.2.1 arg.2] *)
  case: (sd (flidx stL.2.1 arg.2)) => [md|]; last first.
  { (* md sampled from dD *)
    rewrite ?(code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc /=.
    eapply r_scheme_bind; first exact: prog_valid. move=> md.
    ssprove_code_simpl. simpl.
   eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  rewrite (shrincs_fxmss_sign_x_eq_redsign stL.1.1 stL.2.1 stL.2.2 pkm
             (flidx stL.2.1 arg.2) r md Hli hpkm);
  rewrite !(index_sign_path h_sf stL.2.1 (flidx stL.2.1 arg.2) Hli);
  eapply r_get_remember_rhs => v;
  (eapply r_bind_assertD_rhs;
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hvrem;
     rewrite !get_set_heap_neq // in hvrem;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     rewrite hstoL husL hvrem in hR;
     destruct hR as [_ _ _ _ [_ _ [hsub hval] _]];
     pose proof (flidx_notin_image stL.2.1 us arg.2 hfok hfresh hval) as hni;
     exact (contra (hsub (flidx stL.2.1 arg.2)) hni)
   | idtac ]);
  intros _;
  (eapply (r_get_bind_rhs miw_tgts_loc
             (qmap_from 0 (leafcommitq stL.2.1 stL.2.2)));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ _ _ htg _]; rewrite htg; reflexivity
   | idtac ]);
  rewrite (getm_leafcommitq_at stL.2.1 stL.2.2 (flidx stL.2.1 arg.2) Hli);
  (eapply (r_get_bind_rhs miw_pp_loc (Some stL.1.1));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ hpo _ _ _]; rewrite hpo; reflexivity
   | idtac ]);
  simpl;
  (case: (leaf_sign stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
           (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md) => [ws|];
   [ eapply r_put_rhs;
     simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpre1 E2]]; subst s0;
     destruct hpre1 as [s1B [hpre2 E3]]; subst s1A;
     destruct hpre2 as [s0B [hpre3 E4]]; subst s0A;
     destruct hpre3 as [s1C [hpre4 E5]]; subst s1B;
     destruct hpre4 as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E6]]; subst s1C;
     destruct hpreW1 as [s0D [hpreW2 E7]]; subst s0B;
     destruct hpreW2 as [s1E [hpreW3 E8]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E9]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E10]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E11]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       (apply: heap_ignore_set_r; first by rewrite mem_domm);
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x; rewrite mem_rcons in_cons; intro Hor;
         destruct (elimT orP Hor) as [Heq | hx];
         [ apply (elimT eqP) in Heq; subst x; exact: flidx_in_image_setm
         | exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx)) ]
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ]
   | simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpreWm E2]]; subst s0;
     destruct hpreWm as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E3]]; subst s1A;
     destruct hpreW1 as [s0D [hpreW2 E4]]; subst s0A;
     destruct hpreW2 as [s1E [hpreW3 E5]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E6]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E7]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E8]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x hx;
         exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx))
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ] ]). }
  ssprove_code_simpl. simpl.
  (* === SIGN coupling tail (md = sd sc) === *)
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  rewrite (shrincs_fxmss_sign_x_eq_redsign stL.1.1 stL.2.1 stL.2.2 pkm
             (flidx stL.2.1 arg.2) r md Hli hpkm);
  rewrite !(index_sign_path h_sf stL.2.1 (flidx stL.2.1 arg.2) Hli);
  eapply r_get_remember_rhs => v;
  (eapply r_bind_assertD_rhs;
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hvrem;
     rewrite !get_set_heap_neq // in hvrem;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     rewrite hstoL husL hvrem in hR;
     destruct hR as [_ _ _ _ [_ _ [hsub hval] _]];
     pose proof (flidx_notin_image stL.2.1 us arg.2 hfok hfresh hval) as hni;
     exact (contra (hsub (flidx stL.2.1 arg.2)) hni)
   | idtac ]);
  intros _;
  (eapply (r_get_bind_rhs miw_tgts_loc
             (qmap_from 0 (leafcommitq stL.2.1 stL.2.2)));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ _ _ htg _]; rewrite htg; reflexivity
   | idtac ]);
  rewrite (getm_leafcommitq_at stL.2.1 stL.2.2 (flidx stL.2.1 arg.2) Hli);
  (eapply (r_get_bind_rhs miw_pp_loc (Some stL.1.1));
   [ intros s0 s1 hpre;
     destruct hpre as [hpre0 hvrem];
     destruct hpre0 as [s1a [hpre1 E1]]; subst s1;
     destruct hpre1 as [s0a [hpre2 E2]]; subst s0;
     destruct hpre2 as [s1b [hpre3 E3]]; subst s1a;
     destruct hpre3 as [s0b [hpre4 E4]]; subst s0a;
     destruct hpre4 as [s1c [hpre5 E5]]; subst s1b;
     destruct hpre5 as [s0c [hpre6 E6]]; subst s0b;
     destruct hpre6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL;
     rewrite !get_set_heap_neq //;
     apply lf_inv2E in hinv; destruct hinv as [_ hR];
     rewrite hstoL in hR;
     destruct hR as [_ hpo _ _ _]; rewrite hpo; reflexivity
   | idtac ]);
  simpl;
  (case: (leaf_sign stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
           (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md) => [ws|];
   [ eapply r_put_rhs;
     simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpre1 E2]]; subst s0;
     destruct hpre1 as [s1B [hpre2 E3]]; subst s1A;
     destruct hpre2 as [s0B [hpre3 E4]]; subst s0A;
     destruct hpre3 as [s1C [hpre4 E5]]; subst s1B;
     destruct hpre4 as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E6]]; subst s1C;
     destruct hpreW1 as [s0D [hpreW2 E7]]; subst s0B;
     destruct hpreW2 as [s1E [hpreW3 E8]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E9]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E10]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E11]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       (apply: heap_ignore_set_r; first by rewrite mem_domm);
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x; rewrite mem_rcons in_cons; intro Hor;
         destruct (elimT orP Hor) as [Heq | hx];
         [ apply (elimT eqP) in Heq; subst x; exact: flidx_in_image_setm
         | exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx)) ]
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ]
   | simpl;
     eapply r_put_lhs; eapply r_put_rhs;
     apply r_ret; intros s0 s1 hpre;
     split; first by [];
     destruct hpre as [s1A [hpre0 E1]]; subst s1;
     destruct hpre0 as [s0A [hpreWm E2]]; subst s0;
     destruct hpreWm as [hpreW hslogput];
     destruct hpreW as [s1D [hpreW1 E3]]; subst s1A;
     destruct hpreW1 as [s0D [hpreW2 E4]]; subst s0A;
     destruct hpreW2 as [s1E [hpreW3 E5]]; subst s1D;
     destruct hpreW3 as [s0E [hpreW4 E6]]; subst s0D;
     destruct hpreW4 as [s1F [hpreW5 E7]]; subst s1E;
     destruct hpreW5 as [s0F [hpreW6 E8]]; subst s0E;
     destruct hpreW6 as [[[[[hinv hstoL] hstoR] husL] husR] hpkmr];
     rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL husR hpkmr hslogput;
     rewrite !get_set_heap_neq // in hslogput;
     apply lf_inv2E in hinv; destruct hinv as [hign hR];
     apply lf_inv2I;
     [ apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       apply: heap_ignore_set_both;
       exact: hign
     | get_heap_simpl;
       rewrite hstoL hstoR;
       revert hR; rewrite hstoL hstoR husL hslogput; intro hR;
       destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot]];
       split; [ by [] | exact: hpo | exact: hrv | exact: htg |];
       split; [ exact: htw | exact: hpk | | exact: hroot ];
       split;
       [ intros x hx;
         exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx))
       | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ] ] ]).
- (* HASH *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_pre. } move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { lf_get2_pre. } move=> mp.
  case: (getm mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_pre. }
    ssprove_sync. { lf_put2_pre. }
    apply r_ret => s0 s1 hpre. split; first by []. exact: hpre. }
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_pre. }
  ssprove_sync. { lf_put2_pre. }
  apply r_ret => s0 s1 hpre. split; first by []. exact: hpre.
- (* FORGE *)
  destruct arg as [m sg].
  rewrite /forge_keep_body /forge_redL''.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_pre. } move=> fc.
  eapply rel_jdg_replace; [| reflexivity | solve [ssprove_match_commut_gen]].
  simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  eapply (r_fact (stR = (stL.1, (stL.2.1, dummy_xss)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_getr. } move=> lg.
  ssprove_sync. { lf_getr. } move=> mp.
  ssprove_sync. { lf_getr. } move=> tb.
  ssprove_sync. { lf_getr. } move=> sd.
  eapply r_get_remember_rhs => pkm.
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 [[[hinv hstoL] hstoR] hpkmr].
      move/lf_inv2E: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL hstoR in hR.
      case: hR => _ _ _ _ [_ hpk _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  case Emd: (getm mp (sg.1.2, (stL.1, (sg.1.1, m)))) => [md|]; last first.
  { rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    eapply r_scheme_bind; first exact: prog_valid. move=> md.
    ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_pre. }
    ssprove_sync. { lf_put2_pre. }
    case: b; last first.
    { apply r_ret => s0 s1 hpre. split; first by [].
      by move: hpre => [[[hinv _] _] _]; exact: hinv. }
    exact: (r_leaf_forge_verdict''_ideal stL pkm lg tb sd m sg md hpkm). }
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_pre. }
  ssprove_sync. { lf_put2_pre. }
  case: b; last first.
  { apply r_ret => s0 s1 hpre. split; first by [].
    by move: hpre => [[[hinv _] _] _]; exact: hinv. }
  exact: (r_leaf_forge_verdict''_ideal stL pkm lg tb sd m sg md hpkm).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The FORGE verdict line-up (the [shrincs_fxmss_forgery_case_FAnchor] discharge) *)

(** REAL: G5f's [fverd (fun _ => true)] equals the classify-and-LCHECK
    verdict; the FAnchor LCHECK wins by [shrincs_fxmss_forgery_case_FAnchor]. *)
Lemma r_leaf_forge_verdict (st : FXST) (lg : seq M)
    (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv ⋊ rem_lhs Lst (Some st) ⋊ rem_rhs Lst (Some st)) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            (fun _ => true) st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 with
          | FAnchor =>
              v ← get miw_rev_loc ;;
              ans ← (#assert v ;;
                     tgts ← get miw_tgts_loc ;;
                     match getm tgts (fanchoridx st.2.1 sg.1.1) with
                     | Some (t0, m0) =>
                         ppo ← get miw_pp_loc ;;
                         match ppo with
                         | Some pp => ret (leaf_win pp t0 d sg.2.1 m0)
                         | None =>
                             pp ← dPP ;;
                             #put miw_pp_loc := Some pp ;;
                             ret (leaf_win pp t0 d sg.2.1 m0)
                         end
                     | None => ret false
                     end) ;;
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && ans)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv (s0, s1) ⦄.
Proof.
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
eapply (r_fact (st.1.2 = fxroot st.1.1 st.2.1 st.2.2)).
  { move=> s0 s1 [[hinv _] hr].
    rewrite /rem_inv /= in hr.
    move/lf_invE: hinv => [_ hRLf].
    by rewrite hr in hRLf; case: hRLf. }
move=> hroot.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|].
- (* FColl: keepA = true, both = P && true *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- (* FEscape *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- (* FShort *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- (* FAnchor: the real LCHECK wins (opening to the honest leaf pk) *)
  eapply (r_get_rhs_known miw_rev_loc true).
    { move=> s0 s1 [[hinv _] hr].
      rewrite /rem_inv /= in hr.
      move/lf_invE: hinv => [_ hRLf].
      by rewrite hr in hRLf; case: hRLf. }
  rewrite [assertD true _]/=.
  eapply (r_get_rhs_known miw_tgts_loc
            (qmap_from 0 (leafcommitq st.2.1 st.2.2))).
    { move=> s0 s1 [[hinv _] hr].
      rewrite /rem_inv /= in hr.
      move/lf_invE: hinv => [_ hRLf].
      by rewrite hr in hRLf; case: hRLf. }
  case Eans: P; last first.
  + (* P = false: both sides false (CHECK result irrelevant) *)
    destruct (qmap_from 0 (leafcommitq st.2.1 st.2.2)
                (fanchoridx st.2.1 sg.1.1)) as [[t0 m0]|] eqn:Eg;
      rewrite Eg /=.
    * eapply (r_get_rhs_known miw_pp_loc (Some st.1.1)).
        { move=> s0 s1 [[hinv _] hr].
          rewrite /rem_inv /= in hr.
          move/lf_invE: hinv => [_ hRLf].
          by rewrite hr in hRLf; case: hRLf. }
      apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
    * apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
  + (* P = true: the verifying FAnchor recovers the committed leaf pk *)
    have hvm : fxvermd st.1.1 (fxroot st.1.1 st.2.1 st.2.2)
                 sg.1.1 d sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [hin hpos hrec] :=
      shrincs_fxmss_forgery_case_FAnchor st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 hvm E.
    have Eidx : fanchoridx st.2.1 sg.1.1
              = index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                      (leaf_paths (tshape st.2.1)).
      by rewrite /fanchor_idx.
    rewrite Eidx (getm_leafcommitq st.2.1 st.2.2 _ hin) /=.
    eapply (r_get_rhs_known miw_pp_loc (Some st.1.1)).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/lf_invE: hinv => [_ hRLf].
        by rewrite hr in hRLf; case: hRLf. }
    have hwin : leaf_win st.1.1
                  (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)) d sg.2.1
                  (nth [::] st.2.2
                     (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                            (leaf_paths (tshape st.2.1)))) = true.
	      rewrite (leaf_win_panchor st.1.1
	        (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2) d sg.2.1
	        (nth [::] st.2.2
	          (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
	            (leaf_paths (tshape st.2.1))))
	        (leaf_path_size st.2.1 _ hin)); apply/eqP.
      by rewrite {1}hpos; exact: hrec.
    apply r_ret => s0 s1 hpre; split.
    * by rewrite hwin.
    * by case: hpre => [[hinv _] _].
Qed.

(** IDEAL: G6f's [fverd keepAnchor] equals the classify-and-LCHECK
    verdict under [MIW_leaf_abs false] (LCHECK ≡ false = keepAnchor on
    FAnchor). *)
Lemma r_leaf_forge_verdict_ideal (st : FXST) (lg : seq M)
    (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv ⋊ rem_lhs Lst (Some st) ⋊ rem_rhs Lst (Some st)) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            keepA st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 with
          | FAnchor =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && false)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv (s0, s1) ⦄.
Proof.
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
- apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- (* FAnchor: ideal LCHECK = false = keepAnchor FAnchor *)
  apply r_ret => s0 s1 hpre; split.
  + by rewrite andbF.
  + by case: hpre => [[hinv _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The two perfect lemmas *)

Lemma R_leaf_real (b : bool) :
  perfect IG (G5 b) (R_leaf b ∘ MIW_leaf_abs true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ lf_inv).
{ rewrite /lf_inv. ssprove_invariant. by rewrite /rel_empty /RLf. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5 /gen5_body.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_invE: hinv => [hign _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1 (hign (shrincs_fxmss_st_loc PP N)) // /IGN; fmap_solve. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), lblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    rewrite /rem_inv /= in hrem1.
    have [hign [hpp [hrev [htws htgts]]]] := lfinv_init s0 s1 hinv hrem1.
    by split. }
  simpl.
  (* the dummy LCOLLQ pin: lazy pp coupled to G5f's eager [pp ← dPP] *)
  rewrite (resolve_lcq true (encode_adrs (gadrs (0, 0)))
             (inl (n0, n0) : (N × N) ∐ (D × 'nat))) /miw_collq.
  eapply (r_get_bind_rhs miw_pp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (lblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_sample_keys_size (size (leaf_paths (tshape arg)))).
  move=> xss hxsz hkeys; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  eapply (r_scheme_bind (fillc (iota 0 n_max) emptym));
    first exact: fill_code_valid.
  move=> sd; cbv beta.
  rewrite code_link_bind.
  eapply (r_gcheck_spec true pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  rewrite code_link_bind.
	  eapply (lf_tree_spec true pp arg xss _ hkeys [::] (tshape arg) [::]).
	  + by rewrite /= add0n; exact: shrincs_fxmss_shape_wf.
	  + apply: gen_hidx; by rewrite hxsz.
  + exact: gen_uniq.
  + by apply: gen_bud.
  rewrite tval_root lf_commits_leafcommitq /=.
  (* LGETPP: reveal pp, flip the phase *)
  rewrite (resolve_lgp true Datatypes.tt) /miw_getpp.
  eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (lblk_set_rev _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrev htws htgts.
  split; first by [].
  apply: lf_invI.
  - apply: heap_ignore_set_both.
    apply: heap_ignore_set_both.
    exact: hign.
  - get_heap_simpl.
    rewrite hpp hrev htws htgts /=.
    split=> //.
    by rewrite unzip1_leafcommitq.
- (* SIGN: identical opr-free body, [code_link] is the identity *)
  rewrite /sign5 /sign5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. }
  move=> sc.
  ssprove_sync => hsc.
  ssprove_sync. { lf_get_pre. }
  move=> v.
  ssprove_sync => vSome.
  ssprove_sync. { lf_get_pre. }
  move=> us.
  ssprove_sync. { lf_get_pre. }
  move=> lg.
  ssprove_sync. { lf_get_pre. }
  move=> mp.
  ssprove_sync. { lf_get_pre. }
  move=> tb.
  ssprove_sync. { lf_get_pre. }
  move=> sd.
  case E: [&& flok (getSome v vSome).2.1 arg.2 & arg.2 \notin domm us];
    last first.
  { ssprove_sync. { lf_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  case: (sd (flidx (getSome v vSome).2.1 arg.2)) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    case: (fxsignx (getSome v vSome).1.1 (getSome v vSome).2.1
             (getSome v vSome).2.2 (flidx (getSome v vSome).2.1 arg.2) r d)
      => [sg|].
    + ssprove_sync. { lf_put_pre. }
      ssprove_sync. { lf_put_pre. }
      by apply r_ret.
    + ssprove_sync. { lf_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  case: (fxsignx (getSome v vSome).1.1 (getSome v vSome).2.1
           (getSome v vSome).2.2 (flidx (getSome v vSome).2.1 arg.2) r d)
    => [sg|].
  + ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    by apply r_ret.
  + ssprove_sync. { lf_put_pre. } by apply r_ret.
- (* HASH: identical opr-free body *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. }
  move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { lf_get_pre. }
  move=> mp.
  case: (mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  by apply r_ret.
- (* FORGE *)
  destruct arg as [m sg].
  rewrite /forge_keep_body /forge_redL.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. } move=> fc.
  ssprove_code_simpl. simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => sto0.
  eapply r_get_remember_rhs => sto1.
  eapply (r_fact (sto1 = sto0)).
    { move=> s0 s1 [[hinv h0] h1].
      move/lf_invE: hinv => [hign _].
      rewrite /rem_inv /= in h0 h1.
      by rewrite -h0 -h1 (hign (shrincs_fxmss_st_loc PP N) ltac:(rewrite /IGN; fmap_solve)). }
  move=> e; subst sto1.
  eapply r_assertD_same. move=> stSome.
  have Esto : sto0 = Some (getSome sto0 stSome).
    by case: sto0 stSome => [a|] stSome.
  set st := getSome sto0 stSome in Esto *.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. } move=> lg.
  ssprove_sync. { lf_get_pre. } move=> mp.
  ssprove_sync. { lf_get_pre. } move=> tb.
  ssprove_sync. { lf_get_pre. } move=> sd.
  case Emd: (mp (sg.1.2, (st.1, (sg.1.1, m)))) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    rewrite Esto.
    case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
    exact: (r_leaf_forge_verdict st lg tb sd m sg d). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  rewrite Esto.
  case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
  exact: (r_leaf_forge_verdict st lg tb sd m sg d).
Qed.

Lemma R_leaf_ideal (b : bool) :
  perfect IG (G6 b) (R_leaf b ∘ MIW_leaf_abs false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ lf_inv).
{ rewrite /lf_inv. ssprove_invariant. by rewrite /rel_empty /RLf. }
simplify_eq_rel arg.
- (* GEN: verbatim the real-side proof, [MIW_leaf_abs false] *)
  rewrite /gen5 /gen5_body.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_invE: hinv => [hign _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1 (hign (shrincs_fxmss_st_loc PP N)) // /IGN; fmap_solve. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), lblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    rewrite /rem_inv /= in hrem1.
    have [hign [hpp [hrev [htws htgts]]]] := lfinv_init s0 s1 hinv hrem1.
    by split. }
  simpl.
  rewrite (resolve_lcq false (encode_adrs (gadrs (0, 0)))
             (inl (n0, n0) : (N × N) ∐ (D × 'nat))) /miw_collq.
  eapply (r_get_bind_rhs miw_pp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (lblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_sample_keys_size (size (leaf_paths (tshape arg)))).
  move=> xss hxsz hkeys; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  eapply (r_scheme_bind (fillc (iota 0 n_max) emptym));
    first exact: fill_code_valid.
  move=> sd; cbv beta.
  rewrite code_link_bind.
  eapply (r_gcheck_spec false pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  rewrite code_link_bind.
	  eapply (lf_tree_spec false pp arg xss _ hkeys [::] (tshape arg) [::]).
	  + by rewrite /= add0n; exact: shrincs_fxmss_shape_wf.
	  + apply: gen_hidx; by rewrite hxsz.
  + exact: gen_uniq.
  + by apply: gen_bud.
  rewrite tval_root lf_commits_leafcommitq /=.
  rewrite (resolve_lgp false Datatypes.tt) /miw_getpp.
  eapply (r_get_bind_rhs miw_pp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (lblk_set_rev _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrev htws htgts.
  split; first by [].
  apply: lf_invI.
  - apply: heap_ignore_set_both.
    apply: heap_ignore_set_both.
    exact: hign.
  - get_heap_simpl.
    rewrite hpp hrev htws htgts /=.
    split=> //.
    by rewrite unzip1_leafcommitq.
- (* SIGN *)
  rewrite /sign5 /sign5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. }
  move=> sc.
  ssprove_sync => hsc.
  ssprove_sync. { lf_get_pre. }
  move=> v.
  ssprove_sync => vSome.
  ssprove_sync. { lf_get_pre. }
  move=> us.
  ssprove_sync. { lf_get_pre. }
  move=> lg.
  ssprove_sync. { lf_get_pre. }
  move=> mp.
  ssprove_sync. { lf_get_pre. }
  move=> tb.
  ssprove_sync. { lf_get_pre. }
  move=> sd.
  case E: [&& flok (getSome v vSome).2.1 arg.2 & arg.2 \notin domm us];
    last first.
  { ssprove_sync. { lf_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  case: (sd (flidx (getSome v vSome).2.1 arg.2)) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    case: (fxsignx (getSome v vSome).1.1 (getSome v vSome).2.1
             (getSome v vSome).2.2 (flidx (getSome v vSome).2.1 arg.2) r d)
      => [sg|].
    + ssprove_sync. { lf_put_pre. }
      ssprove_sync. { lf_put_pre. }
      by apply r_ret.
    + ssprove_sync. { lf_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  case: (fxsignx (getSome v vSome).1.1 (getSome v vSome).2.1
           (getSome v vSome).2.2 (flidx (getSome v vSome).2.1 arg.2) r d)
    => [sg|].
  + ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    by apply r_ret.
  + ssprove_sync. { lf_put_pre. } by apply r_ret.
- (* HASH *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. }
  move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { lf_get_pre. }
  move=> mp.
  case: (mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  by apply r_ret.
- (* FORGE *)
  destruct arg as [m sg].
  rewrite /forge_keep_body /forge_redL.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. } move=> fc.
  eapply rel_jdg_replace; [| reflexivity | solve [ssprove_match_commut_gen]].
  simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => sto0.
  eapply r_get_remember_rhs => sto1.
  eapply (r_fact (sto1 = sto0)).
    { move=> s0 s1 [[hinv h0] h1].
      move/lf_invE: hinv => [hign _].
      rewrite /rem_inv /= in h0 h1.
      by rewrite -h0 -h1 (hign (shrincs_fxmss_st_loc PP N) ltac:(rewrite /IGN; fmap_solve)). }
  move=> e; subst sto1.
  eapply r_assertD_same. move=> stSome.
  have Esto : sto0 = Some (getSome sto0 stSome).
    by case: sto0 stSome => [a|] stSome.
  set st := getSome sto0 stSome in Esto *.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get_pre. } move=> lg.
  ssprove_sync. { lf_get_pre. } move=> mp.
  ssprove_sync. { lf_get_pre. } move=> tb.
  ssprove_sync. { lf_get_pre. } move=> sd.
  case Emd: (mp (sg.1.2, (st.1, (sg.1.1, m)))) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put_pre. }
    ssprove_sync. { lf_put_pre. }
    rewrite Esto.
    case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
    exact: (r_leaf_forge_verdict_ideal st lg tb sd m sg d). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put_pre. }
  ssprove_sync. { lf_put_pre. }
  rewrite Esto.
  case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
  exact: (r_leaf_forge_verdict_ideal st lg tb sd m sg d).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The hop theorem (layer (i)), ABSTRACT over the leaf eval *)

Theorem Leaf_to_MIW_abs (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G5 b) (G6 b) A = AdvOf MIW_leaf_abs (A ∘ R_leaf b).
Proof.
rewrite (Adv_perfect_l (R_leaf_real b)) (Adv_perfect_r (R_leaf_ideal b)).
by rewrite Adv_reduction.
Qed.

(** layer-(i) hop: the re-shared reduction [R_leaf''] routing both
    LCOMMIT and LSIGN through the multi-instance game [MIW_leaf'']. *)
Theorem Leaf_to_MIW''_abs (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G5 b) (G6 b) A = AdvOf MIW_leaf'' (A ∘ R_leaf'' b).
Proof.
rewrite (Adv_perfect_l (R_leaf''_real b)) (Adv_perfect_r (R_leaf''_ideal b)).
by rewrite Adv_reduction.
Qed.

End LeafAbs.

(* ------------------------------------------------------------------ *)
(** ** Concrete instantiation at the REAL leaf eval

    Outside [LeafAbs] we instantiate the abstract eval at the real WOTS+C
    honest pk [shrincs_fxmss_wots_public_key] and recovered anchor [shrincs_fxmss_recover_anchor]; the bridge
    hypotheses then hold by [erefl]. These concrete evaluations
    ([leaf_pk_c], [leaf_rec_c], [leaf_sign_c]) are the atoms consumed by
    [fxmss.leaf_km] and the second-layer leaf bounds. *)

Definition leaf_pk_c : PP -> adrs_sf_ch -> 'list N -> N :=
  fun (pp : PP) (t : adrs_sf_ch) (m : 'list N) =>
    shrincs_fxmss_wots_public_key PP N F Tl (adrs_keypair (decode_tweak t)).1
      (adrs_keypair (decode_tweak t)).2 pp m.

Definition leaf_rec_c : PP -> adrs_sf_ch -> D -> (('list N) × 'nat) -> N :=
  fun (pp : PP) (t : adrs_sf_ch) (md : D) (ws : ('list N) × 'nat) =>
    shrincs_fxmss_recover_anchor PP N D F Tl Hgrind pp
      (adrs_keypair (decode_tweak t)) md ws.

Lemma leaf_pkE_c (pp : PP) (t : adrs_sf_ch) (m : 'list N) :
  leaf_pk_c pp t m = lpk pp t m.
Proof. by []. Qed.

Lemma leaf_recE_c (pp : PP) (t : adrs_sf_ch) (md : D)
    (ws : ('list N) × 'nat) :
  leaf_rec_c pp t md ws = lrec pp t md ws.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** concrete instantiation (real eval): the LSIGN atom at the
    real WOTS+C signer [shrincs_fxmss_wots_sign]; bridge holds by [erefl]. *)

Definition leaf_sign_c : PP -> adrs_sf_ch -> 'list N -> D ->
    'option (('list N) × 'nat) :=
  fun (pp : PP) (t : adrs_sf_ch) (xs : 'list N) (md : D) =>
    shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max
      (adrs_keypair (decode_tweak t)).1 (adrs_keypair (decode_tweak t)).2
      pp xs md.

Lemma leaf_signE_c (pp : PP) (t : adrs_sf_ch) (xs : 'list N) (md : D) :
  leaf_sign_c pp t xs md
  = shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max
      (adrs_keypair (decode_tweak t)).1 (adrs_keypair (decode_tweak t)).2
      pp xs md.
Proof. by []. Qed.

End FXMSSLeafReduction.
