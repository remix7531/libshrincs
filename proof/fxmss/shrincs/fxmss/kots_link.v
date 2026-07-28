(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.kots_link

    THE link lemma (P7): the generic valid-commit known-message KOTS
    game [KOTS_vc_game] (Sec.lib.sig.kots), instantiated at the one
    WOTS+C scheme anchored at a leaf coordinate, is PERFECTLY simulated
    by the FXMSS banked multi-instance digest-at-commit game [MIW_kmS]
    at bank size [n_max = 1] through the stateless wrapper [R_kots]:

      [KOTS_vc_MIW_kmS_link :
         perfect (I_KOTS S0) (KOTS_vc_game S0 b) (R_kots ∘ MIW_kmS … 1 … b)]

    with [S0 := shrincs_fxmss_wots_scheme … (lcoord t0).1 (lcoord t0).2]
    for a fixed tweak [t0].  The wrapper:

      COMMIT (sp, m) := root ← LCOMMIT (t0, m) ;; r ← LSIGN 0 ;;
                        pp ← LGETPP ;;
                        match r with Some ws => ret ((pp, root), Some ws)
                                   | None    => fail end
      KFORGE (m, s)  := LCHECK (0, (m, s)).

    Alignment facts making this a PERFECT simulation:
    - the two freshness gates coincide: KOTS's [~~ isSome pko] is
      MIW's [~~ revealed] (COMMIT reveals via its trailing LGETPP);
    - [mkm_winSG]'s first two conjuncts are [verify S0] verbatim (both
      unfold to the same [wotsc_verify] application, modulo [andbA]);
    - after a SUCCESSFUL sign the committed digest is grindable, so
      [gateL] degenerates to the KOTS one-time freshness [dd != md0];
    - the sign-refusal branch: the KOTS side [fail]s outright while the
      MIW side has already written its bank; [fail] is null-measure, so
      the one-sided peel rules discharge the branch against [r_fail];
    - the opposite key-generation sampling orders (KOTS: PKseed then
      chain starts; LCOMMIT: chain starts then PKseed) are aligned by
      [r_swap_scheme_scheme] through [r_transL].

    The two-phase existential invariant [RK] over the 7 live locations
    (KOTS pk/log; MIW pp/tgts/tws/rev/slog) carries the FUNCTIONAL
    conjunct [pk = (pp, lpk pp t0 xs)] plus the grindability witness
    [isSome (find_ctr … pp md0)] — which is why a [couple_cross … eq]
    invariant cannot express it.

    The corollary [KOTS_vc_to_MIW_kmS] is P8's entry point: it demotes
    the native hop ladder's KOTS endpoint to the banked
    [Leaf_MIW_km_bound] at [n_max = 1]. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From Sec.lib Require Import prelude math.bin_tree math.merkle math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme sig.kots toolkit.sample_seq
  toolkit.relational_rules chain.core wots.wotsc.
From SHRINCS Require Import addressing wotsc.scheme
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop
  fxmss.leaf_reduction fxmss.leaf_km.
From mathcomp Require Import all_boot all_order.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section kots_miw_link.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** The data-only context of [fxmss.leaf_km], restricted to what
    [MIW_kmS] itself consumes. *)
Context (PP N D : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (S_wn c_max : nat).

(** The instance tweak: the KOTS experiment lives at ONE leaf
    coordinate. *)
Context (t0 : adrs_sf_ch).

(* ------------------------------------------------------------------ *)
(** ** Shorthands (LeafKM's) *)

Local Notation zi0 := (@leaf_km.lcoord w l t0).
Local Notation lpk := (leaf_pk_c PP N F Tl).
Local Notation lfind pp md :=
  (find_ctr PP D Hgrind S_wn c_max zi0.1 zi0.2 pp md).

Local Notation Lpp := (miw_pp_loc PP).
Local Notation Ltw := (@miw_tws_loc w l).
Local Notation Lrv := miw_rev_loc.
Local Notation Lsl := miw_slog_loc.
Local Notation Ktg := (@mkm_tgts_loc w l N D).

Local Notation IKM := (@I_MIW_km w l PP N D).
Local Notation MIWkm b :=
  (MIW_kmS PP N D F Tl Hgrind Htree dPP dN S_wn c_max 1 b).

(** The one scheme, anchored at [t0]'s leaf coordinate. *)
Definition S0 : sig_scheme :=
  shrincs_fxmss_wots_scheme PP N D F Tl Hgrind dPP dN S_wn c_max zi0.1 zi0.2.

Local Notation Kpk := (kots_pk_loc S0).
Local Notation Klog := (kots_log_loc S0).

(* Keep the scheme functions and oracle bodies folded under [simpl]
   (the known simpl-unrolling trap; mirrors Sec.wots.kots_link). *)
#[local] Arguments wotsc_find_ctr : simpl never.
#[local] Arguments wotsc_sign : simpl never.
#[local] Arguments wotsc_verify : simpl never.
#[local] Arguments wotsc_pubkey : simpl never.
#[local] Arguments wotsc_sign_chains : simpl never.
#[local] Arguments wotsc_digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments shrincs_fxmss_wots_sign : simpl never.
#[local] Arguments shrincs_fxmss_wots_verify : simpl never.
#[local] Arguments shrincs_fxmss_wots_public_key : simpl never.
#[local] Arguments leaf_pk_c : simpl never.
#[local] Arguments leaf_rec_c : simpl never.
#[local] Arguments leaf_sign_c : simpl never.
#[local] Arguments mkm_commit : simpl never.
#[local] Arguments mkm_signS : simpl never.
#[local] Arguments mkm_getpp : simpl never.
#[local] Arguments mkm_winSG : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The wrapper [R_kots] : package IKM (I_KOTS S0) — stateless. *)

Local Notation cmo := (@lf_cmo_km w l N D).
Local Notation sgo := (@lf_sgo_km N).
Local Notation gpo := (@lf_gpo_km PP).
Local Notation cko := (@lf_cko_km N D).

Definition kcommit (m : D) :
    raw_code ((PP × N) × 'option (('list N) × 'nat)) :=
  opr cmo (t0, m) (λ root,
  opr sgo 0%N (λ r,
  opr gpo Datatypes.tt (λ pp,
  match r with
  | Some ws => ret ((pp, root), Some ws)
  | None => fail
  end))).

Definition kforge (ms : D × (('list N) × 'nat)) : raw_code 'bool :=
  opr cko (0%N, ms) (λ ans, ret ans).

#[local] Instance kcommit_valid (m : D) :
  ValidCode emptym IKM (kcommit m).
Proof.
rewrite /kcommit.
eapply valid_opr; first by rewrite /lf_cmo_km; fmap_solve. move=> root.
eapply valid_opr; first by rewrite /lf_sgo_km; fmap_solve. move=> r.
eapply valid_opr; first by rewrite /lf_gpo_km; fmap_solve. move=> pp.
case: r => [ws|]; first by apply valid_ret.
exact: valid_fail.
Qed.

#[local] Instance kforge_valid (ms : D × (('list N) × 'nat)) :
  ValidCode emptym IKM (kforge ms).
Proof.
rewrite /kforge.
eapply valid_opr; first by rewrite /lf_cko_km; fmap_solve. move=> ans.
apply valid_ret.
Qed.

Definition R_kots : package IKM (I_KOTS S0).
Proof.
notypeclasses refine [package emptym ;
    [ COMMIT ] : { 'unit × D ~> (PP × N) × 'option (('list N) × 'nat) }
      '(sp, m) { kcommit m } ;
    [ KFORGE ] : { D × (('list N) × 'nat) ~> 'bool } (ms) { kforge ms }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { apply: valid_empty_package. }
  { intro ms; exact: kforge_valid. } }
{ intros [sp m]; exact: kcommit_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** The two-phase invariant *)

(** The 7 live locations. *)
Definition KL : Locations := [fmap Kpk ; Klog ; Lpp ; Ktg ; Ltw ; Lrv ; Lsl ].

(** Phase relation: pre-commit everything is at its initial value;
    post-commit the ONE bank slot mirrors the KOTS key/log, and the
    committed digest is grindable (the successful-sign witness that
    degenerates [gateL] to KOTS freshness). *)
Definition RK (pko : option (PP × N)) (lg : seq D) (po : option PP)
    (tg : {fmap nat -> (adrs_sf_ch × ('list N × D))}) (tw : seq adrs_sf_ch)
    (rv : bool) (sl : seq nat) : Prop :=
  match pko with
  | None =>
      [/\ lg = [::], po = None, tg = emptym
        & [/\ tw = [::], rv = false & sl = [::]]]
  | Some pk =>
      exists (pp : PP) (xs : 'list N) (md0 : D),
        [/\ pk = (pp, lpk pp t0 xs), lg = [:: md0], po = Some pp
          & [/\ tg = setm emptym 0%N (t0, (xs, md0)), tw = [:: t0],
                rv = true, sl = [:: 0%N] & isSome (lfind pp md0)]]
  end.

Definition kinv : precond :=
  heap_ignore KL
  ⋊ rel_app [:: (lhs, Kpk) ; (lhs, Klog) ; (rhs, Lpp) ; (rhs, Ktg) ;
                (rhs, Ltw) ; (rhs, Lrv) ; (rhs, Lsl) ] RK.

Arguments kinv : simpl never.

Lemma kinvE s0 s1 :
  kinv (s0, s1) ->
  heap_ignore KL (s0, s1) /\
  RK (get_heap s0 Kpk) (get_heap s0 Klog) (get_heap s1 Lpp)
     (get_heap s1 Ktg) (get_heap s1 Ltw) (get_heap s1 Lrv)
     (get_heap s1 Lsl).
Proof. by move=> [h1 h2]; split. Qed.

Lemma kinvI s0 s1 :
  heap_ignore KL (s0, s1) ->
  RK (get_heap s0 Kpk) (get_heap s0 Klog) (get_heap s1 Lpp)
     (get_heap s1 Ktg) (get_heap s1 Ltw) (get_heap s1 Lrv)
     (get_heap s1 Lsl) ->
  kinv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** The pinned stepping block (LeafKM's [lblk_km] / prf_link's [blk]
    pattern) *)

Definition kblk (pko : option (PP × N)) (lg : seq D) (po : option PP)
    (tg : {fmap nat -> (adrs_sf_ch × ('list N × D))}) (tw : seq adrs_sf_ch)
    (rv : bool) (sl : seq nat) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore KL (s0, s1),
      get_heap s0 Kpk = pko, get_heap s0 Klog = lg, get_heap s1 Lpp = po
    & [/\ get_heap s1 Ktg = tg, get_heap s1 Ltw = tw,
          get_heap s1 Lrv = rv & get_heap s1 Lsl = sl]].

Arguments kblk : simpl never.

(** Phase-1 re-entry: pinned post-commit heaps + the grindability
    witness re-establish the invariant. *)
Lemma kinv_phase1 (pp : PP) (xs : 'list N) (md0 : D) s0 s1 :
  isSome (lfind pp md0) ->
  kblk (Some (pp, lpk pp t0 xs)) [:: md0] (Some pp)
       (setm emptym 0%N (t0, (xs, md0))) [:: t0] true [:: 0%N] (s0, s1) ->
  kinv (s0, s1).
Proof.
move=> hfind [hign hpk hlg hpo [htg htw hrv hsl]].
apply: kinvI; first exact: hign.
rewrite hpk hlg hpo htg htw hrv hsl.
by exists pp, xs, md0; split; last split.
Qed.

(** Heap-update steps for [kblk] (each write is to a location inside
    [KL], so [heap_ignore KL] survives one-sidedly). *)

Lemma kblk_set_tgtw pko lg po tg tw rv sl
    (tg' : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (tw' : seq adrs_sf_ch) s0 s1 :
  kblk pko lg po tg tw rv sl (s0, s1) ->
  kblk pko lg po tg' tw' rv sl
    (s0, set_heap (set_heap s1 Ktg tg') Ltw tw').
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- exact: h1.
- exact: h2.
- by rewrite !get_set_heap_neq.
- by split; [ rewrite get_set_heap_neq // get_set_heap_eq
            | rewrite get_set_heap_eq
            | rewrite !get_set_heap_neq
            | rewrite !get_set_heap_neq ].
Qed.

Lemma kblk_set_pp pko lg po tg tw rv sl (pp : PP) s0 s1 :
  kblk pko lg po tg tw rv sl (s0, s1) ->
  kblk pko lg (Some pp) tg tw rv sl (s0, set_heap s1 Lpp (Some pp)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- exact: h1.
- exact: h2.
- by rewrite get_set_heap_eq.
- by split; rewrite get_set_heap_neq.
Qed.

Lemma kblk_set_sl pko lg po tg tw rv sl (sl' : seq nat) s0 s1 :
  kblk pko lg po tg tw rv sl (s0, s1) ->
  kblk pko lg po tg tw rv sl' (s0, set_heap s1 Lsl sl').
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- exact: h1.
- exact: h2.
- by rewrite get_set_heap_neq.
- by split; [ rewrite get_set_heap_neq | rewrite get_set_heap_neq
            | rewrite get_set_heap_neq | rewrite get_set_heap_eq ].
Qed.

Lemma kblk_set_rv pko lg po tg tw rv sl (rv' : bool) s0 s1 :
  kblk pko lg po tg tw rv sl (s0, s1) ->
  kblk pko lg po tg tw rv' sl (s0, set_heap s1 Lrv rv').
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- exact: h1.
- exact: h2.
- by rewrite get_set_heap_neq.
- by split; [ rewrite get_set_heap_neq | rewrite get_set_heap_neq
            | rewrite get_set_heap_eq | rewrite get_set_heap_neq ].
Qed.

Lemma kblk_set_kpk pko lg po tg tw rv sl (pko' : option (PP × N)) s0 s1 :
  kblk pko lg po tg tw rv sl (s0, s1) ->
  kblk pko' lg po tg tw rv sl (set_heap s0 Kpk pko', s1).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_l h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- exact: h3.
- by split.
Qed.

Lemma kblk_set_klog pko lg po tg tw rv sl (lg' : seq D) s0 s1 :
  kblk pko lg po tg tw rv sl (s0, s1) ->
  kblk pko lg' po tg tw rv sl (set_heap s0 Klog lg', s1).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7]]; split.
- by apply: heap_ignore_set_l h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- exact: h3.
- by split.
Qed.

(** Entering an oracle: drop the [rel_app] machinery and split on the
    phase, naming every pinned location value (prf_link's [r_blk_intro],
    with the phase disjunction).  In phase 1 the KOTS key is the literal
    committed pair, so no equation shuffling is left to the bullets. *)
Lemma r_kblk_intro {A B : choiceType} (c0 : raw_code A) (c1 : raw_code B)
    (post : postcond A B) :
  (⊢ ⦃ λ '(s0, s1), kblk None [::] None emptym [::] false [::] (s0, s1) ⦄
     c0 ≈ c1 ⦃ post ⦄) ->
  (forall (pp : PP) (xs : 'list N) (md0 : D),
     isSome (lfind pp md0) ->
     ⊢ ⦃ λ '(s0, s1), kblk (Some (pp, lpk pp t0 xs)) [:: md0] (Some pp)
                        (setm emptym 0%N (t0, (xs, md0))) [:: t0] true
                        [:: 0%N] (s0, s1) ⦄
        c0 ≈ c1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), kinv (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> h0 h1.
apply rpre_hypothesis_rule => s0 s1 hpre.
have [hign hRK] := kinvE s0 s1 hpre.
case E0: (get_heap s0 Kpk) hRK => [pk|] hRK.
- case: hRK => pp [xs] [md0] [hpk hlg hpo [htg htw hrv hsl hfind]].
  eapply rpre_weaken_rule; first exact: (h1 pp xs md0 hfind).
  move=> s0' s1' /= [-> ->]; split.
  + exact: hign.
  + by rewrite E0 hpk.
  + exact: hlg.
  + exact: hpo.
  + by split.
- case: hRK => hlg hpo htg [htw hrv hsl].
  eapply rpre_weaken_rule; first exact: h0.
  move=> s0' s1' /= [-> ->]; split.
  + exact: hign.
  + exact: E0.
  + exact: hlg.
  + exact: hpo.
  + by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The link lemma *)

Theorem KOTS_vc_MIW_kmS_link (b : bool) :
  perfect (I_KOTS S0) (KOTS_vc_game S0 b) (R_kots ∘ MIWkm b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ kinv).
{ rewrite /kinv. ssprove_invariant.
  by rewrite /rel_empty /RK. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  rewrite (resolve_lcm_kmS PP N D F Tl Hgrind Htree dPP dN S_wn c_max 1 b t0 m).
  rewrite (resolve_lsg_kmS PP N D F Tl Hgrind Htree dPP dN S_wn c_max 1 b 0%N).
  rewrite (resolve_lgp_kmS PP N D F Tl Hgrind Htree dPP dN S_wn c_max 1 b
             Datatypes.tt).
  rewrite /mkm_commit.
  apply: r_kblk_intro; last first.
  + (* phase 1: both freshness gates abort *)
    move=> pp xs md0 _.
    eapply (r_get_lhs_known Kpk (Some (pp, lpk pp t0 xs))).
    { by move=> ? ? [_ e _ _ _]. }
    eapply (r_get_bind_rhs Lrv true).
    { by move=> ? ? [_ _ _ _ [_ _ e _]]. }
    cbv beta.
    exact: r_fail_bind_rhs.
  + (* phase 0: the commit round *)
    eapply (r_get_lhs_known Kpk None).
    { by move=> ? ? [_ e _ _ _]. }
    eapply (r_get_bind_rhs Lrv false).
    { by move=> ? ? [_ _ _ _ [_ _ e _]]. }
    cbv beta.
    (* the three RHS gates all compute to true at the empty bank *)
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_get_bind_rhs Ltw [::]).
    { by move=> ? ? [_ _ _ _ [_ e _ _]]. }
    cbv beta.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    rewrite bind_assoc.
    simpl.
    (* swap the LHS keygen order to match the RHS: xs first, pp second *)
    eapply r_transL.
    { apply: (r_swap_scheme_scheme (sample_seq dN l) (prog dPP)). }
    apply: (r_sample_seq_size_l N dN l) => xs hxs.
    cbv beta.
    eapply (r_get_rhs_known Ktg emptym).
    { by move=> ? ? [_ _ _ _ [e _ _ _]]. }
    eapply r_put2_rhs_weak.
    { move=> s0' s1' hp; exact: (kblk_set_tgtw _ _ _ _ _ _ _ _ _ _ _ hp). }
    eapply (r_get_rhs_known Lpp None).
    { by move=> ? ? [_ _ _ e _]. }
    cbv iota.
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> pp; cbv beta.
    eapply r_put_bind_rhs.
    { move=> s0' s1' hp; exact: (kblk_set_pp _ _ _ _ _ _ _ pp _ _ hp). }
    simpl.
    (* LSIGN 0: the slot-0 lookup *)
    eapply (r_get_rhs_known Lsl [::]).
    { by move=> ? ? [_ _ _ _ [_ _ _ e]]. }
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_get_bind_rhs Ktg (setm emptym 0%N (t0, (xs, m)))).
    { by move=> ? ? [_ _ _ _ [e _ _ _]]. }
    cbv beta.
    rewrite setmE eqxx /=.
    eapply (r_get_bind_rhs Lpp (Some pp)).
    { by move=> ? ? [_ _ _ e _]. }
    cbv beta iota.
    simpl.
    (* the sign-refusal pivot, on the shared scrutinee *)
    rewrite /leaf_sign_c.
    simpl.
    rewrite -/(shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max
                 (adrs_height (games.decode_tweak t0))
                 (adrs_index (games.decode_tweak t0)) pp xs m).
    case E: (find_ctr PP D Hgrind S_wn c_max
               (adrs_height (games.decode_tweak t0))
               (adrs_index (games.decode_tweak t0)) pp m) => [c|].
    (* Some c: both sides commit and return the same signature *)
    rewrite (shrincs_fxmss_wots_sign_Some PP N D F Hgrind S_wn c_max
               (adrs_height (games.decode_tweak t0))
               (adrs_index (games.decode_tweak t0)) pp xs m c E).
    simpl.
    eapply r_put_rhs_pre.
    { move=> s0' s1' hp; exact: (kblk_set_sl _ _ _ _ _ _ _ [:: 0%N] _ _ hp). }
    eapply (r_get_rhs_known Lpp (Some pp)).
    { by move=> ? ? [_ _ _ e _]. }
    cbv iota.
    simpl.
    eapply r_put_rhs_pre.
    { move=> s0' s1' hp; exact: (kblk_set_rv _ _ _ _ _ _ _ true _ _ hp). }
    eapply r_put_lhs_pre.
    { move=> s0' s1' hp; exact: (kblk_set_kpk _ _ _ _ _ _ _ _ _ _ hp). }
    eapply r_put_lhs_pre.
    { move=> s0' s1' hp; exact: (kblk_set_klog _ _ _ _ _ _ _ [:: m] _ _ hp). }
    apply r_ret => s0' s1' hp; split; first by [].
    apply: (kinv_phase1 pp xs m); last exact: hp.
    by rewrite E.
    (* None: the KOTS side fails; the MIW side's writes are null *)
    rewrite (shrincs_fxmss_wots_sign_None PP N D F Hgrind S_wn c_max
               (adrs_height (games.decode_tweak t0))
               (adrs_index (games.decode_tweak t0)) pp xs m E).
    simpl.
    eapply (r_get_rhs_known Lpp (Some pp)).
    { by move=> ? ? [_ _ _ e _]. }
    cbv iota.
    simpl.
    eapply r_put_rhs_pre.
    { move=> s0' s1' hp; exact: (kblk_set_rv _ _ _ _ _ _ _ true _ _ hp). }
    exact: r_fail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  destruct b; last first.
  + (* ideal: both return false *)
    simpl.
    by apply r_ret => s0 s1 hpre; split.
  + simpl.
    rewrite /mkm_winSG.
    apply: r_kblk_intro; last first.
    * (* phase 1: the win conditions coincide *)
      move=> pp xs md0 hfind.
      eapply (r_get_lhs_known Kpk (Some (pp, lpk pp t0 xs))).
      { by move=> ? ? [_ e _ _ _]. }
      simpl.
      eapply (r_get_lhs_known Klog [:: md0]).
      { by move=> ? ? [_ _ e _ _]. }
      eapply (r_get_bind_rhs Lrv true).
      { by move=> ? ? [_ _ _ _ [_ _ e _]]. }
      cbv beta.
      eapply r_bind_assertD_rhs; first by [].
      move=> _.
      eapply (r_get_bind_rhs Ktg (setm emptym 0%N (t0, (xs, md0)))).
      { by move=> ? ? [_ _ _ _ [e _ _ _]]. }
      cbv beta.
      rewrite setmE eqxx /=.
      eapply (r_get_bind_rhs Lpp (Some pp)).
      { by move=> ? ? [_ _ _ e _]. }
      cbv beta iota.
      simpl.
      apply r_ret => s0' s1' hp; split; last first.
      { apply: (kinv_phase1 pp xs md0); [exact: hfind | exact: hp]. }
      (* the win-condition equation: verify is the first two conjuncts
         ([andbA]); the successful-sign witness kills [gateL]'s
         ungrindable disjunct; [mem_seq1] is the one-time log *)
      rewrite /leaf_km.gateL.
      case E2: (lfind pp md0) hfind => [c|] // _.
      by rewrite /wotsc_verify mem_seq1 andbA.
    * (* phase 0: both sides abort *)
      eapply (r_get_lhs_known Kpk None).
      { by move=> ? ? [_ e _ _ _]. }
      eapply (r_get_bind_rhs Lrv false).
      { by move=> ? ? [_ _ _ _ [_ _ e _]]. }
      cbv beta.
      exact: r_fail_bind_rhs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The advantage form (P8's entry point) *)

Theorem KOTS_vc_to_MIW_kmS (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS S0) A_export A) :
  Adv (KOTS_vc_game S0 true) (KOTS_vc_game S0 false) A
  = Adv (MIWkm true) (MIWkm false) (A ∘ R_kots).
Proof.
rewrite (Adv_perfect_l (KOTS_vc_MIW_kmS_link true))
        (Adv_perfect_r (KOTS_vc_MIW_kmS_link false)).
by rewrite Adv_reduction.
Qed.

End kots_miw_link.
