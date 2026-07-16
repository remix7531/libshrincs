(** * SHRINCS.FXMSS.Leaf2Grind
    FXMSS leaf-hop LAYER (ii) GRIND sub-bound (G1l -> Glmid1).

    The multi-instance lift of WOTSC/GrindHop.v's [R_gr] (S-TCR(Prop) grinding
    hop) to ALL leaves, over the STATIC-gate EU-CMA endpoint [MIW_kmS]
    (M1a re-landing: predicates/reduction re-pointed to the slog-FREE
    [P_g1lS]/[P_gm1S] with the simple [grind_hitS] null, the slot-keyed digit
    [l_rrdigS] and the budget-guarded LSIGN; the perfects are the M1e
    milestone -- the F5 residual is UNBLOCKED, enc-pair freshness is FORCED
    by the gate on pop-1 and pop-2 leaves are never SQUERYed on a win).
    This is the FIRST nulling hop of the ladder: [G1l] keeps the full
    re-rooted win, [Glmid1] additionally nulls the grind collision
    [grind_hitS].

    Delivered:
      [R_gr_leaf_real  : perfect IKM G1l    (R_gr_leaf o STCRP(TGl,CGl_leaf) q1 true)]
      [R_gr_leaf_ideal : perfect IKM Glmid1 (R_gr_leaf o STCRP(TGl,CGl_leaf) q1 false)]
      [sub_gr : Adv G1l Glmid1 B = AdvOf (STCRP_game TGl CGl_leaf D genc gprp c_max q1)
                                         (B o R_gr_leaf)]

    ** Design (COMPRESS chain/grind machinery + ChainPRE offset remap, retargeted
       to the S-TCR(Prop) grinding target Hgrind).

    - Target = the grinding hash [Hgrind] (TGl = Tgr at [M := D]); budget
      [q1 = n_max] (at most one SQUERY per GRINDABLE leaf).  The S-TCR(Prop)
      break is a target-sum coincidence: a forgery whose recomputed grinding
      digit vector coincides with the committed leaf's, at a fresh digest.
    - Collection [CGl_leaf] exposes F (chain walks), Tl (pk compression), Htree
      (exported LCOLLQ.inl) and Hgrind (grinding search + exported LCOLLQ.inr),
      all under the hidden pp -- same 4-member shape as Leaf2ChainPRE's
      [CFl_leaf], over the grinding target [TGl].  As in COMPRESS the chains are
      sampled LOCALLY (dN) and walked via COLLQ(F); the pk is COLLQ(Tl); the
      grinding digit search is COLLQ(Hgrind) over all counters.
    - NEW infra beyond COMPRESS (two pieces):
      (a) a leaf -> STCRP index REMAP: the STCRP challenge is committed
          per-GRINDING-QUERY (only grindable leaves SQUERY), not per-leaf, so
          the reduction stores the leaf's STCRP index [sidx] (= running
          grindable count [rgr_cnt_loc]) in its target record; LCHECK routes
          SCHECK at [sidx].  Non-grindable leaves carry [copt = None] and NO
          STCRP target.
      (b) a grind-tweak injectivity backbone: distinct leaf coordinates give
          distinct grind tweaks [AdrGrind] (via [encode_adrs_inj]+[AdrGrind_inj]),
          so the SQUERY tweak-distinctness [grtw_of t \notin stw] discharges from
          the game's coordinate freshness [gtw_of t \notin map gtw_of ltw].
    - The real-side SCHECK routing lifts the digit-vector collision [fdv ==
      rr_digit] to the Hgrind-output collision via [wdigest_inj] (the [Hrange]
      side condition), exactly as WOTSC/GrindHop's [R_gr_real]. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From HBS Require Import Prelude Math.BinTree Math.Merkle Math.Chain Math.Encoding
  Sig.Scheme Games.THF Games.SMTCR Games.STCRP Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames FXMSS.TreeHop
  FXMSS.LeafReduction FXMSS.LeafKM FXMSS.Leaf2Common FXMSS.Leaf2Games.
From mathcomp Require Import all_ssreflect reals.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section Leaf2Grind.

(** Same DATA-ONLY section context as FXMSS/Leaf2Games.v. *)
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
(** ** Shorthands.  [lcoord] (= adrs_keypair o decode) is imported from
    Leaf2Games (no section args). *)

Local Notation IKM := (I_MIW_km PP N D).

(** The leaf S-TCR(Prop) target THF: Tgr at the leaf grinding hash. *)
Local Notation TGl := (Tgr PP D Hgrind dPP dD).
Local Notation genc := (grind_enc D).
Local Notation gprp := (grind_prp w l S_wn).

(** The collection: F (chain walks), Tl (pk compression), Htree
    (LCOLLQ.inl), Hgrind (grinding + LCOLLQ.inr) -- all under hidden pp.
    Same 4-member shape as Leaf2ChainPRE's CFl_leaf, over the target TGl. *)
Definition CGl_leaf : thf_coll TGl :=
  Build_thf_coll TGl adrs_sf_ch
    (N ∐ (('list N) ∐ ((N × N) ∐ (D × 'nat))))
    (N ∐ (N ∐ (N ∐ 'nat)))
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr (inl xs) => inr (inl (Tl pp (decode_tweak t) xs))
       | inr (inr (inl xy)) => inr (inr (inl (Htree pp (decode_tweak t) xy)))
       | inr (inr (inr dc)) => inr (inr (inr (Hgrind pp (decode_tweak t) dc)))
       end).

Local Notation IMP := (I_STCRP TGl CGl_leaf D).

(** q1 = n_max committed grinding targets (at most one SQUERY per leaf). *)
Local Notation q1 := n_max.

Local Notation gtw_of t := (encode_adrs (wotsc_pk_adrs (lcoord t))).
Local Notation grtw_of t := (encode_adrs (wotsc_grind_adrs (lcoord t))).
Local Notation chtw_of t i k := (encode_adrs (wotsc_chain_adrs (lcoord t) i k)).

(** Inlined re-root digit / pk (= Leaf2Games.rr_digit / rr_pk at zi = lcoord t). *)
Definition l_rrdig (zi : nat * nat) (pp : PP) (md : D) : seq nat :=
  match find_ctr PP D Hgrind w l S_wn c_max zi.1 zi.2 pp md with
  | Some c => digest_of PP D Hgrind w l zi.1 zi.2 pp md c
  | None => nseq l w.-1
  end.

Definition l_rrpk (zi : nat * nat) (pp : PP) (md : D) (sg : seq N) : N :=
  Tl pp (wotsc_pk_adrs zi)
     (complete_ends PP N F w l zi.1 zi.2 pp (l_rrdig zi pp md) sg).

(** The SLOT-KEYED static digit / pk (= Leaf2Games.rr_digitS / rr_pkS at
    zi = lcoord t, M1a): virtual [nseq l w.-1] for out-of-budget slots. *)
Definition l_rrdigS (zi : nat * nat) (pp : PP) (md : D) (j : nat) : seq nat :=
  l_rrdig zi pp md.

Definition l_rrpkS (zi : nat * nat) (pp : PP) (md : D) (j : nat)
    (sg : seq N) : N :=
  Tl pp (wotsc_pk_adrs zi)
     (complete_ends PP N F w l zi.1 zi.2 pp (l_rrdigS zi pp md j) sg).

(** The leaf chain hash (= Leaf2Games.rr_F). *)
Local Notation lF zi := (Fw PP N F zi.1 zi.2).

(* ------------------------------------------------------------------ *)
(** ** Import opsigs. *)

Definition lgr_cqo : opsig := (SCOLLQ, (tc_T CGl_leaf × tc_M CGl_leaf, tc_N CGl_leaf)).
Definition lgr_sqo : opsig := (SQUERY, (th_T TGl × D, th_N TGl × 'nat)).
Definition lgr_gpo : opsig := (SGETPP, ('unit, th_PP TGl)).
Definition lgr_cko : opsig := (SCHECK, ('nat × (D × 'nat), 'bool)).

(* ------------------------------------------------------------------ *)
(** ** The COLLQ-routed loops (COMPRESS's grind/walk/chains at the leaf,
    with the 4-member collection tags). *)

(** Grinding loop: one SCOLLQ (Hgrind member, [inr (inr (inr _))]) per counter. *)
Fixpoint lgr_grind (zi : nat * nat) (md : D) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lgr_cqo (encode_adrs (wotsc_grind_adrs zi), inr (inr (inr (md, c))))
        (λ r, hs ← lgr_grind zi md cs' ;;
              ret ((if r is inr (inr (inr h)) then h else 0) :: hs))
  end.

#[local] Instance lgr_grind_valid (L : Locations) zi md cs :
  ValidCode L IMP (lgr_grind zi md cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n] steps,
    one SCOLLQ (F member, [inl]) per step. *)
Fixpoint lgr_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr lgr_cqo (encode_adrs (wotsc_chain_adrs zi i k), inl x)
         (λ r, lgr_walk zi i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance lgr_walk_valid (L : Locations) zi i k n x :
  ValidCode L IMP (lgr_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
  move=> r; exact: IH.
Qed.

(** All chains: per chain, sample root LOCALLY, one SCOLLQ F-step to the
    signature position (positive digit), walk upward; returns (sig values,
    completed ends). *)
Fixpoint lgr_chains (zi : nat * nat) (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1
           then opr lgr_cqo (encode_adrs (wotsc_chain_adrs zi st d'), inl u)
                  (λ r, ret (if r is inl y then y else u))
           else ret u) ;;
      e ← lgr_walk zi st d (w.-1 - d) s ;;
      '(ss, es) ← lgr_chains zi st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance lgr_chains_valid (L : Locations) zi st ds :
  ValidCode L IMP (lgr_chains zi st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
    move=> r; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: lgr_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(** The bounded grind search on the answer list (= scheme [find_ctr]). *)
Definition lgr_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 c_max) hs | gprp ch.2].

Definition lgr_digit (hs : seq nat) : seq nat :=
  match lgr_pick hs with
  | Some ch => digits_w w l ch.2
  | None => nseq l w.-1
  end.

(** The SLOT-KEYED commit digit (= rr_digitS reconstructed at slot [j]). *)
Definition lgr_digitS (j : nat) (hs : seq nat) : seq nat :=
  lgr_digit hs.

(* ------------------------------------------------------------------ *)
(** ** The LCHECK pure decisions (M1a S-forms, slog-FREE).  [lgr_v] is the
    FULL re-rooted guarded win (= P_g1lS at the stored find_ctr counter:
    verokS && gateS); [lgr_ghit] is the SIMPLE grind-collision discriminant
    (= grind_hitS: pop-1 AND digit coincidence -- the (C1) enc-pair disjunct
    and the slog disjunct DROPPED; freshness of the routed enc-pair is FORCED
    by the gate, LeafKM.stcrp_fresh_forced). *)

Definition lgr_v (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (copt : 'option 'nat) (j : nat) (mw : D × (('list N) × 'nat)) : bool :=
  let vchecks := wots_checks PP N D Hgrind w l S_wn pp (lcoord t0) mw.1 mw.2 in
  let verok := (vchecks
                && (recover_anchor PP N D F Tl Hgrind w l pp (lcoord t0) mw.1 mw.2
                    == l_rrpkS (lcoord t0) pp md0 j sg))%B in
  let gate := (~~ isSome copt || (mw.1 != md0))%B in
  (verok && gate)%B.

Definition lgr_ghit (pp : PP) (t0 : adrs_sf_ch) (md0 : D) (copt : 'option 'nat)
    (j : nat) (mw : D × (('list N) × 'nat)) : bool :=
  let fdv := digest_of PP D Hgrind w l (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2 in
  let rdg := l_rrdigS (lcoord t0) pp md0 j in
  (isSome copt && (fdv == rdg))%B.

(* ------------------------------------------------------------------ *)
(** ** The reduction package R_gr_leaf : package IMP IKM. *)

(** R's own state (800+).  The tgts record stores (tweak, roots, digest,
    find_ctr counter option [copt], STCRP index [sidx]). *)
Definition rgr_rev_loc  := mkloc 800 (false : bool).
Definition rgr_tws_loc  := mkloc 801 ([::] : seq adrs_sf_ch).
Definition rgr_tgts_loc :=
  mkloc 802 (emptym : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))}).
Definition rgr_slog_loc := mkloc 803 ([::] : seq nat).
Definition rgr_pp_loc   := mkloc 804 (None : option PP).
Definition rgr_cnt_loc  := mkloc 805 (0%N : nat).

Local Notation RGRLocs :=
  [fmap rgr_rev_loc ; rgr_tws_loc ; rgr_tgts_loc ; rgr_slog_loc ; rgr_pp_loc ;
        rgr_cnt_loc ].

Definition R_gr_leaf : package IMP IKM.
Proof.
notypeclasses refine [package RGRLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) {
      revealed ← get rgr_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get rgr_tws_loc ;;
      #assert (size tws < n_max)%N ;;
      #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
      _ ← opr lgr_cqo (grtw_of t, inr (inr (inr (md, 0)))) (λ r, ret r) ;;
      hs ← lgr_grind (lcoord t) md (iota 0 c_max) ;;
      '(sg, ends) ← lgr_chains (lcoord t) 0 (lgr_digitS (size tws) hs) ;;
      pk ← opr lgr_cqo (gtw_of t, inr (inl ends))
             (λ r, ret (match r with inr (inl y) => y | _ => n0 end)) ;;
      sidx ← get rgr_cnt_loc ;;
      match lgr_pick hs with
      | Some ch =>
          _ ← opr lgr_sqo (grtw_of t, md) (λ r, ret r) ;;
          #put rgr_cnt_loc := sidx.+1 ;;
          tgts ← get rgr_tgts_loc ;;
          #put rgr_tgts_loc := setm tgts (size tws) (t, (((sg, md), Some ch.1), sidx)) ;;
          #put rgr_tws_loc := rcons tws t ;;
          ret pk
      | None =>
          tgts ← get rgr_tgts_loc ;;
          #put rgr_tgts_loc := setm tgts (size tws) (t, (((sg, md), None), sidx)) ;;
          #put rgr_tws_loc := rcons tws t ;;
          ret pk
      end
    } ;
    [ LGETPP ] : { 'unit ~> PP } (_) {
      pp ← opr lgr_gpo Datatypes.tt (λ p, ret p) ;;
      #put rgr_pp_loc := Some pp ;;
      #put rgr_rev_loc := true ;;
      ret pp
    } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      revealed ← get rgr_rev_loc ;;
      #assert revealed ;;
      tgts ← get rgr_tgts_loc ;;
      match getm tgts j with
      | Some (t0, (((sg, md0), copt), sidx)) =>
          ppo ← get rgr_pp_loc ;;
          pp ← match ppo with
               | Some pp => ret pp
               | None => pp ← dPP ;; #put rgr_pp_loc := Some pp ;; ret pp
               end ;;
          if lgr_v pp t0 sg md0 copt j mw && lgr_ghit pp t0 md0 copt j mw
          then opr lgr_cko (sidx, (mw.1, mw.2.2)) (λ ans, ret ans)
          else ret (lgr_v pp t0 sg md0 copt j mw)
      | None => ret false
      end
    } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) {
      slog ← get rgr_slog_loc ;;
      #assert (j \notin slog) ;;
      tgts ← get rgr_tgts_loc ;;
      match getm tgts j with
      | Some (t0, (((sg, md0), copt), sidx)) =>
          match copt with
          | Some c => #put rgr_slog_loc := rcons slog j ;; ret (Some (sg, c))
          | None => ret None
          end
      | None => ret None
      end
    } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      match x with
      | inl xy =>
          opr lgr_cqo (t, inr (inr (inl xy)))
            (λ r, ret (match r with inr (inr (inl h)) => inl h | _ => inl n0 end))
      | inr dc =>
          opr lgr_cqo (t, inr (inr (inr dc)))
            (λ r, ret (match r with inr (inr (inr g)) => inr g | _ => inr 0 end))
      end
    }
  ].
(* directed valid_package_cons, each oracle by an explicit instance. *)
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { eapply valid_package_cons.
        { apply: valid_empty_package. }
        { (* LCOLLQ *)
          intros [t x]; case: x => [xy|dc].
          - eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
            move=> r; apply valid_ret.
          - eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
            move=> r; apply valid_ret. } }
      { (* LSIGN *)
        intro j.
        eapply valid_getr; first by fmap_solve. move=> slog.
        eapply valid_assertD => _.
        eapply valid_getr; first by fmap_solve. move=> tgts.
        case: (getm tgts j) => [[t0 [[[sg md0] copt] sidx]]|]; last by apply valid_ret.
        case: copt => [c|]; last by apply valid_ret.
        eapply valid_putr; first by fmap_solve. apply valid_ret. } }
    { (* LCHECK *)
      intros [j mw].
      eapply valid_getr; first by fmap_solve. move=> revealed.
      eapply valid_assertD => _.
      eapply valid_getr; first by fmap_solve. move=> tgts.
      case: (getm tgts j) => [[t0 [[[sg md0] copt] sidx]]|]; last by apply valid_ret.
      eapply valid_getr; first by fmap_solve. move=> ppo.
      eapply valid_bind.
        case: ppo => [pp|]; first by apply valid_ret.
        eapply valid_bind; first by eapply valid_scheme, prog_valid.
        move=> pp; eapply valid_putr; first by fmap_solve.
        apply valid_ret.
      move=> pp.
      case: ifP => _.
      - eapply valid_opr; first by rewrite /lgr_cko; fmap_solve.
        move=> ans; apply valid_ret.
      - apply valid_ret. } }
  { (* LGETPP *)
    intro u.
    eapply valid_opr; first by rewrite /lgr_gpo; fmap_solve.
    move=> p; eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve. apply valid_ret. } }
{ (* LCOMMIT *)
  intros [t md].
  eapply valid_getr; first by fmap_solve. move=> revealed.
  eapply valid_assertD => _.
  eapply valid_getr; first by fmap_solve. move=> tws.
  eapply valid_assertD => _.
  eapply valid_assertD => _.
  eapply valid_bind.
    eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> _.
  eapply valid_bind; first exact: lgr_grind_valid. move=> hs.
  eapply valid_bind; first exact: lgr_chains_valid. move=> [sg ends].
  eapply valid_bind.
    eapply valid_opr; first by rewrite /lgr_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> pk.
  eapply valid_getr; first by fmap_solve. move=> sidx.
  case: (lgr_pick hs) => [ch|].
  - eapply valid_bind.
      eapply valid_opr; first by rewrite /lgr_sqo; fmap_solve.
      move=> r; apply valid_ret.
    move=> _.
    eapply valid_putr; first by fmap_solve.
    eapply valid_getr; first by fmap_solve. move=> tgts.
    eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve. apply valid_ret.
  - eapply valid_getr; first by fmap_solve. move=> tgts.
    eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve. apply valid_ret. }
Defined.

Check (R_gr_leaf : package IMP IKM).
Check (fun (B : nom_package) => B ∘ R_gr_leaf).

(* ================================================================== *)
(** ** STCRP location shorthands + resolve equations. *)

Local Notation Lpp := (miw_pp_loc PP).
Local Notation Ltg := (mkm_tgts_loc N D).
Local Notation Ltw := miw_tws_loc.
Local Notation Lrv := miw_rev_loc.
Local Notation Lsl := miw_slog_loc.
Local Notation Spp := (stcr_pp_loc TGl).
Local Notation Stg := (stcr_tgts_loc TGl D).
Local Notation Stw := (stcr_tws_loc TGl).
Local Notation Srv := stcr_rev_loc.

Local Notation STB b := (STCRP_game TGl CGl_leaf D genc gprp c_max q1 b).

Lemma resolve_lgr_cq (b : bool) (t : tc_T CGl_leaf) (x : tc_M CGl_leaf) :
  resolve (STB b) lgr_cqo (t, x) =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   ret (tc_eval CGl_leaf pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgr_sq (b : bool) (t : th_T TGl) (m : D) :
  resolve (STB b) lgr_sqo (t, m) =
  (revealed ← get Srv ;;
   #assert ~~ revealed ;;
   tws ← get Stw ;;
   #assert (size tws < q1)%N ;;
   #assert (t \notin tws) ;;
   ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   match [seq i <- iota 0 c_max | gprp (th_eval TGl pp t (genc m i))] with
   | i :: _ =>
       tgts ← get Stg ;;
       #put Stg := setm tgts (size tws) (t, (m, i)) ;;
       #put Stw := rcons tws t ;;
       ret (th_eval TGl pp t (genc m i), i)
   | [::] =>
       #assert false ;;
       ret (th_eval TGl pp t (genc m 0), 0%N)
   end).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgr_gp (b : bool) (u : unit) :
  resolve (STB b) lgr_gpo u =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   #put Srv := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgr_ck (j : nat) (m : D) (ctr : nat) :
  resolve (STB true) lgr_cko (j, (m, ctr)) =
  (revealed ← get Srv ;;
   #assert revealed ;;
   tgts ← get Stg ;;
   match getm tgts j with
   | Some (t0, (m0, i0)) =>
       ppo ← get Spp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
            end ;;
       ret ((m != m0) &&
            (th_eval TGl pp t0 (genc m0 i0) == th_eval TGl pp t0 (genc m ctr)))
   | None => ret false
   end).
Proof. by simplify_linking. Qed.

Lemma resolve_lgr_ck_false (j : nat) (m : D) (ctr : nat) :
  resolve (STB false) lgr_cko (j, (m, ctr)) = ret false.
Proof. by simplify_linking. Qed.

(* ------------------------------------------------------------------ *)
(** ** Conversion bridges (canonical tweaks compute). *)

Lemma collq_H_E (pp : PP) (zi : nat * nat) (md : D) (c : nat) :
  (if tc_eval CGl_leaf pp (encode_adrs (wotsc_grind_adrs zi)) (inr (inr (inr (md, c))))
      is inr (inr (inr h)) then h else 0)
  = Hgrind pp (wotsc_grind_adrs zi) (md, c).
Proof. by rewrite /tc_eval /CGl_leaf decode_tweakK. Qed.

Lemma collq_F_E (pp : PP) (zi : nat * nat) (i k : nat) (x : N) :
  (if tc_eval CGl_leaf pp (encode_adrs (wotsc_chain_adrs zi i k)) (inl x)
      is inl y then y else x)
  = F pp (wotsc_chain_adrs zi i k) x.
Proof. by rewrite /tc_eval /CGl_leaf decode_tweakK. Qed.

Lemma collq_Tl_E (pp : PP) (zi : nat * nat) (ends : seq N) :
  (match tc_eval CGl_leaf pp (encode_adrs (wotsc_pk_adrs zi)) (inr (inl ends))
     with inr (inl y) => y | _ => n0 end)
  = Tl pp (wotsc_pk_adrs zi) ends.
Proof. by rewrite /tc_eval /CGl_leaf decode_tweakK. Qed.

(** [th_eval TGl] at a canonical grind tweak is the scheme's Hgrind. *)
Lemma th_eval_grtw (pp : PP) (zi : nat * nat) (mc : D * nat) :
  th_eval TGl pp (encode_adrs (wotsc_grind_adrs zi)) mc
  = Hgrind pp (wotsc_grind_adrs zi) mc.
Proof. by rewrite /th_eval /TGl /= decode_tweakK. Qed.

(** The picked grinding result on the honest answer list = the scheme's
    [find_ctr] (identical to Leaf2Compress's [lcp_*_E]). *)
Lemma lgr_zip_filter (f : nat -> nat) (P : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | P ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | P (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (P (f c)) => /=; [|exact: IH].
Qed.

Lemma lgr_pick_map (pp : PP) (zi : nat * nat) (md : D) :
  lgr_pick [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = omap (fun c => (c, Hgrind pp (wotsc_grind_adrs zi) (md, c)))
         (find_ctr PP D Hgrind w l S_wn c_max zi.1 zi.2 pp md).
Proof.
rewrite /lgr_pick lgr_zip_filter /find_ctr.
have hf :
  [seq c <- iota 0 c_max
   | grind_prp w l S_wn (Hgrind pp (wotsc_grind_adrs zi) (md, c))]
  = [seq c <- iota 0 c_max | good_ctr PP D Hgrind w l S_wn zi.1 zi.2 pp md c].
  by apply: eq_filter => c;
     rewrite /grind_prp /good_ctr /valid_digest /digest_of.
by rewrite hf.
Qed.

Lemma lgr_digit_E (pp : PP) (zi : nat * nat) (md : D) :
  lgr_digit [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = l_rrdig zi pp md.
Proof.
rewrite /lgr_digit /l_rrdig lgr_pick_map.
by case: (find_ctr PP D Hgrind w l S_wn c_max zi.1 zi.2 pp md) => [c|].
Qed.

Lemma lgr_copt_E (pp : PP) (zi : nat * nat) (md : D) :
  omap fst (lgr_pick [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- iota 0 c_max])
  = find_ctr PP D Hgrind w l S_wn c_max zi.1 zi.2 pp md.
Proof.
by rewrite lgr_pick_map; case: (find_ctr _ _ _ _ _ _ _ _ _ _) => [c|].
Qed.

(* ------------------------------------------------------------------ *)
(** ** grind-tweak injectivity backbone (piece (b)). *)

(** The coordinate of an encoded grind tweak is its anchor. *)
Lemma lcoord_grtw (t : adrs_sf_ch) : lcoord (grtw_of t) = lcoord t.
Proof. by rewrite /lcoord decode_tweakK. Qed.

Lemma lcoord_gtw (t : adrs_sf_ch) : lcoord (gtw_of t) = lcoord t.
Proof. by rewrite /lcoord decode_tweakK. Qed.

(** [gtw_of] / [grtw_of] equality is coordinate equality. *)
Lemma gtw_of_eq_coord (x y : adrs_sf_ch) :
  (gtw_of x == gtw_of y) = (lcoord x == lcoord y).
Proof.
apply/eqP/eqP => [/encode_adrs_inj /AdrPk_inj [e1 e2]|e].
- by rewrite [lcoord x]surjective_pairing [lcoord y]surjective_pairing e1 e2.
- by rewrite e.
Qed.

Lemma grtw_of_eq_coord (x y : adrs_sf_ch) :
  (grtw_of x == grtw_of y) = (lcoord x == lcoord y).
Proof.
apply/eqP/eqP => [/encode_adrs_inj /AdrGrind_inj [e1 e2]|e].
- by rewrite [lcoord x]surjective_pairing [lcoord y]surjective_pairing e1 e2.
- by rewrite e.
Qed.

(* ================================================================== *)
(** ** The invariant (heap_ignore + rel_app RG), STCRP remap. *)

#[local] Arguments resolve : simpl never.
#[local] Arguments STCRP_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments lgr_pick : simpl never.
#[local] Arguments l_rrdig : simpl never.

Local Notation lfind zi pp md :=
  (find_ctr PP D Hgrind w l S_wn c_max zi.1 zi.2 pp md).
Local Notation lcompl zi pp ds sg := (complete_ends PP N F w l zi.1 zi.2 pp ds sg).
Local Notation FWl zi := (Fw PP N F zi.1 zi.2).
Local Notation wsigs zi := (sigs_of PP N (FWl zi)).
Local Notation wends zi := (ends_of PP N (FWl zi) w).

Definition IGNG : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rgr_pp_loc ; rgr_tgts_loc ; rgr_tws_loc ; rgr_rev_loc ; rgr_slog_loc ;
        rgr_cnt_loc ; Spp ; Stg ; Stw ; Srv ].

(** The per-leaf coherence of the three target tables with the STCRP remap. *)
Definition RGrel (pp : PP) (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))})
    (stg : {fmap nat -> (th_T TGl × (D × 'nat))})
    (stw : seq (th_T TGl)) : Prop :=
  (forall g, g \in stw -> lcoord g \in [seq lcoord x | x <- ltw])
  /\ forall j,
    match getm ltg j with
    | Some (t0, (sg, md0)) =>
        exists sidx : nat,
          getm rtg j = Some (t0, (((sg, md0), lfind (lcoord t0) pp md0), sidx))
          /\ match lfind (lcoord t0) pp md0 with
             | Some c => (sidx < size stw)%N /\
                         getm stg sidx = Some (grtw_of t0, (md0, c))
             | None => True
             end
    | None => getm rtg j = None
    end.

(** The top-level relation. *)
Definition RG
    (lpp : option PP) (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (ltw : seq adrs_sf_ch) (lrv : bool) (lsl : seq nat)
    (rpp : option PP)
    (rtg : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))})
    (rtw : seq adrs_sf_ch) (rrv : bool) (rsl : seq nat) (rcnt : nat)
    (spp : option (th_PP TGl)) (stg : {fmap nat -> (th_T TGl × (D × 'nat))})
    (stw : seq (th_T TGl)) (srv : bool) : Prop :=
  [/\ rtw = ltw, rrv = lrv, rsl = lsl, rpp = (if lrv then lpp else None)
    & [/\ spp = lpp, srv = lrv, rcnt = size stw, (size stw <= size ltw)%N
      & match lpp with
        | None => [/\ ltg = emptym, rtg = emptym, stg = emptym, stw = [::] & lrv = false]
        | Some pp => RGrel pp ltw ltg rtg stg stw
        end]].

Definition gr_inv : precond :=
  heap_ignore IGNG
  ⋊ rel_app [:: (lhs, Lpp) ; (lhs, Ltg) ; (lhs, Ltw) ; (lhs, Lrv) ; (lhs, Lsl) ;
                (rhs, rgr_pp_loc) ; (rhs, rgr_tgts_loc) ; (rhs, rgr_tws_loc) ;
                (rhs, rgr_rev_loc) ; (rhs, rgr_slog_loc) ; (rhs, rgr_cnt_loc) ;
                (rhs, Spp) ; (rhs, Stg) ; (rhs, Stw) ; (rhs, Srv) ] RG.

Arguments gr_inv : simpl never.

Lemma gr_invE s0 s1 :
  gr_inv (s0, s1) ->
  heap_ignore IGNG (s0, s1) /\
  RG (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rgr_pp_loc) (get_heap s1 rgr_tgts_loc) (get_heap s1 rgr_tws_loc)
     (get_heap s1 rgr_rev_loc) (get_heap s1 rgr_slog_loc) (get_heap s1 rgr_cnt_loc)
     (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv).
Proof. by move=> [h1 h2]; split. Qed.

Lemma gr_invI s0 s1 :
  heap_ignore IGNG (s0, s1) ->
  RG (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rgr_pp_loc) (get_heap s1 rgr_tgts_loc) (get_heap s1 rgr_tws_loc)
     (get_heap s1 rgr_rev_loc) (get_heap s1 rgr_slog_loc) (get_heap s1 rgr_cnt_loc)
     (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv) ->
  gr_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ================================================================== *)
(** ** Monad-law helpers + lazy-pp pushes (port of Leaf2Compress). *)

Lemma bind_getr {A B : choiceType} (ℓ : Location) (f : ℓ -> raw_code A)
    (k : A -> raw_code B) :
  bind (x ← get ℓ ;; f x) k = (x ← get ℓ ;; bind (f x) k).
Proof. by []. Qed.

Lemma bind_put_ret {A B : choiceType} (ℓ : Location) (v : ℓ) (a : A)
    (k : A -> raw_code B) :
  bind (#put ℓ := v ;; ret a) k = (#put ℓ := v ;; k a).
Proof. by []. Qed.

Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

Lemma push_getSpp {A B : choiceType} (X : PP -> raw_code A) (Y : A -> raw_code B) :
  (ppo ← get Spp ;;
   b ← (pp ← match ppo with
             | Some pp => ret pp
             | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
             end ;; X pp) ;; Y b)
  = (ppo ← get Spp ;;
     pp ← match ppo with
          | Some pp => ret pp
          | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
          end ;; bind (X pp) Y).
Proof. setoid_rewrite bind_assoc. exact: erefl. Qed.

Lemma collq_rhs_E {B : choiceType} (a : PP -> tc_N CGl_leaf)
    (k : tc_N CGl_leaf -> raw_code B) :
  (ppo ← get Spp ;;
   b ← (pp ← match ppo with
             | Some pp => ret pp
             | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
             end ;; ret (a pp)) ;; k b)
  = (ppo ← get Spp ;;
     pp ← match ppo with
          | Some pp => ret pp
          | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
          end ;; k (a pp)).
Proof. setoid_rewrite bind_assoc. exact: erefl. Qed.

(* ================================================================== *)
(** ** Stepping one linked SCOLLQ (pp pinned) + the loop specs. *)

Lemma r_lgrcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CGl_leaf) (x : tc_M CGl_leaf) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : tc_N CGl_leaf -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CGl_leaf pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (resolve (STB b) lgr_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lgr_cq b t x).
eapply (r_get_bind_rhs Spp (Some pp)); first exact: hpp.
cbv beta iota.
exact: h.
Qed.

Lemma r_lgrgrind_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (md : D) (cs : seq nat) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lgr_grind zi md cs) (STB b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lgrcollq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

Lemma r_lgrwalk_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (post : postcond B B) :
  forall n i k (x : N)
         (c0 : raw_code B) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (chain (HBS.Examples.FixedSumOTS.Scheme.chainf PP N (FWl zi) pp i) x k n)
   ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lgr_walk zi i k n x) (STB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lgrcollq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_F_E.
  exact: IH.
Qed.

Lemma r_lgrchains_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (post : postcond B B) :
  forall ds st
         (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
        K0 (wsigs zi pp st ds us)
      ≈ K1 (wsigs zi pp st ds us, wends zi pp st ds (wsigs zi pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     bind (sample_sig_roots PP N (FWl zi) dN pp st ds) K0
   ≈ bind (code_link (lgr_chains zi st ds) (STB b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st K0 K1 h.
- exact: (h [::] erefl).
- rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN))
          !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d h => [|d'] h.
  + rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    eapply (r_lgrwalk_spec b pp zi pre hpp post (w.-1 - 0) st 0 u).
    rewrite (code_link_bind (lgr_chains zi st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
  + rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_lgrcollq_known b pp _ _ pre hpp).
    cbv beta.
    rewrite collq_F_E /=.
    rewrite (code_link_bind (lgr_walk zi st d'.+1 (w.-1 - d'.+1)
              (F pp (wotsc_chain_adrs zi st d') u))) bind_assoc.
    eapply (r_lgrwalk_spec b pp zi pre hpp post (w.-1 - d'.+1) st d'.+1
              (F pp (wotsc_chain_adrs zi st d') u)).
    rewrite /= (code_link_bind (lgr_chains zi st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
Qed.

Lemma wendsEl (zi : nat * nat) pp (ds : seq nat) (ys : seq N) :
  size ds = l -> wends zi pp 0 ds ys = lcompl zi pp ds ys.
Proof.
move=> h.
by rewrite (ends_of_from_sig PP N (FWl zi) l w pp ds ys h)
   (wcendsE PP N F w l zi.1 zi.2).
Qed.

(* ================================================================== *)
(** ** Win-predicate bridges (P_g1lS / P_gm1S = lgr_v / lgr_v && ~~lgr_ghit,
    M1a S-forms). *)

Lemma P_g1l_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_g1lS PP N D F Tl Hgrind w l S_wn c_max pp t0 sg md0 j mw
  = lgr_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw.
Proof.
by rewrite /P_g1lS /lgr_v /LeafKM.gateL /l_rrpkS /l_rrdigS /l_rrdig
   /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c.
Qed.

Lemma P_gm1_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_gm1S PP N D F Tl Hgrind w l S_wn c_max pp t0 sg md0 j mw
  = lgr_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw
    && ~~ lgr_ghit pp t0 md0 (lfind (lcoord t0) pp md0) j mw.
Proof.
rewrite /P_gm1S /lgr_v /lgr_ghit /grind_hitS /LeafKM.gateL /l_rrpkS /l_rrdigS
        /l_rrdig /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c.
by rewrite andbA.
Qed.

(* ================================================================== *)
(** ** The block precondition (inside an oracle, machinery dropped). *)

Definition grblk (po : option PP) (lrv : bool) (lsl : seq nat)
    (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))})
    (stg : {fmap nat -> (th_T TGl × (D × 'nat))})
    (stw : seq (th_T TGl)) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNG (s0, s1),
      [/\ get_heap s0 Lpp = po, get_heap s0 Lrv = lrv, get_heap s0 Lsl = lsl,
          get_heap s0 Ltw = ltw & get_heap s0 Ltg = ltg],
      [/\ get_heap s1 rgr_pp_loc = (if lrv then po else None),
          get_heap s1 rgr_rev_loc = lrv, get_heap s1 rgr_slog_loc = lsl,
          get_heap s1 rgr_tws_loc = ltw & get_heap s1 rgr_tgts_loc = rtg],
      [/\ get_heap s1 Spp = po, get_heap s1 Srv = lrv,
          get_heap s1 Stw = stw, get_heap s1 Stg = stg
        & get_heap s1 rgr_cnt_loc = size stw]
    & [/\ (size stw <= size ltw)%N
        & match po with
          | None => [/\ ltg = emptym, rtg = emptym, stg = emptym & stw = [::]]
          | Some pp => RGrel pp ltw ltg rtg stg stw
          end]].

Arguments grblk : simpl never.

(** A [Some pp] block precondition IS the invariant. *)
Lemma grblk_gr_inv (pp : PP) lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk (Some pp) lrv lsl ltw ltg rtg stg stw (s0, s1) -> gr_inv (s0, s1).
Proof.
move=> [hign [hLpp hLrv hLsl hLtw hLtg] [hrpp hrrv hrsl hrtw hrtg]
        [hSpp hSrv hStw hStg hcnt] [hle hm]].
apply: gr_invI; first exact: hign.
rewrite /RG hLpp hLrv hLsl hLtw hLtg hrpp hrrv hrsl hrtw hrtg hcnt
        hSpp hSrv hStw hStg.
by split=> //; split=> //.
Qed.

(** The invariant gives the block precondition once [rev = false]. *)
Lemma gr_inv_grblk s0 s1 :
  gr_inv (s0, s1) -> get_heap s0 Lrv = false ->
  grblk (get_heap s0 Lpp) false (get_heap s0 Lsl) (get_heap s0 Ltw)
        (get_heap s0 Ltg) (get_heap s1 rgr_tgts_loc) (get_heap s1 Stg)
        (get_heap s1 Stw) (s0, s1).
Proof.
move=> hinv hrv.
case/gr_invE: hinv => hign hRG.
case: hRG => hrtw hrrv hrsl hrpp [hspp hsrv hcnt hle hm].
split.
- exact: hign.
- by [].
- by split=> //; rewrite ?hrpp ?hrrv hrv.
- by split=> //; rewrite ?hsrv ?hcnt hrv.
- split; first exact: hle.
  move: hm; case: (get_heap s0 Lpp) => [pp|] hm; first exact: hm.
  by case: hm => he1 he2 he3 he4 _; split.
Qed.

(** Pin [pp] on both [Lpp] and [Spp] (from [None]); preserves the invariant. *)
Lemma grblk_set_both_pp (pp : PP) lsl ltw ltg rtg stg stw s0 s1 :
  grblk None false lsl ltw ltg rtg stg stw (s0, s1) ->
  grblk (Some pp) false lsl ltw ltg rtg stg stw
    (set_heap s0 Lpp (Some pp), set_heap s1 Spp (Some pp)).
Proof.
move=> [h0 [h1 h2 h3 h4 h5] [h6 h7 h8 h9 h10] [h11 h12 h13 h14 h15] [hle hm]].
case: hm => he1 he2 he3 he4; split.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: h0.
- split; [by rewrite get_set_heap_eq | by rewrite get_set_heap_neq
         | by rewrite get_set_heap_neq | by rewrite get_set_heap_neq
         | by rewrite get_set_heap_neq].
- split; [by rewrite get_set_heap_neq | by rewrite get_set_heap_neq
         | by rewrite get_set_heap_neq | by rewrite get_set_heap_neq
         | by rewrite get_set_heap_neq].
- split; [by rewrite get_set_heap_eq | by rewrite get_set_heap_neq
         | by rewrite get_set_heap_neq | by rewrite get_set_heap_neq
         | by rewrite get_set_heap_neq].
- split; first exact: hle.
  by rewrite he1 he2 he3 he4; split=> // g; rewrite in_nil.
Qed.

Lemma gr_inv_pin (pp : PP) s0 s1 :
  gr_inv (s0, s1) -> get_heap s0 Lpp = None ->
  gr_inv (set_heap s0 Lpp (Some pp), set_heap s1 Spp (Some pp)).
Proof.
move=> hinv hL.
have hrv : get_heap s0 Lrv = false.
  case/gr_invE: hinv => _ hRG.
  by move: hRG; rewrite hL => -[_ _ _ _ [_ _ _ _ [_ _ _ _ ->]]].
have hblk := gr_inv_grblk s0 s1 hinv hrv.
move: hblk; rewrite hL => hblk.
apply: (grblk_gr_inv pp false (get_heap s0 Lsl) (get_heap s0 Ltw)
          (get_heap s0 Ltg) (get_heap s1 rgr_tgts_loc) (get_heap s1 Stg)
          (get_heap s1 Stw)).
exact: (grblk_set_both_pp pp _ _ _ _ _ _ s0 s1 hblk).
Qed.

(** GETPP: reveal pp (rev false -> true), R copies pp into its own pp loc. *)
Lemma gr_inv_reveal (pp : PP) s0 s1 :
  gr_inv (s0, s1) -> get_heap s0 Lpp = Some pp ->
  gr_inv (set_heap s0 Lrv true,
          set_heap (set_heap (set_heap s1 Srv true) rgr_pp_loc (Some pp))
            rgr_rev_loc true).
Proof.
move=> hinv hL.
case/gr_invE: hinv => hign hRG.
move: hRG; rewrite hL => -[hrtw hrrv hrsl hrpp [hspp hsrv hcnt hle hm]].
apply: gr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- have e_Lpp : get_heap (set_heap s0 Lrv true) Lpp = Some pp
    by rewrite get_set_heap_neq.
  have e_Ltg : get_heap (set_heap s0 Lrv true) Ltg = get_heap s0 Ltg
    by rewrite get_set_heap_neq.
  have e_Ltw : get_heap (set_heap s0 Lrv true) Ltw = get_heap s0 Ltw
    by rewrite get_set_heap_neq.
  have e_Lrv : get_heap (set_heap s0 Lrv true) Lrv = true
    by rewrite get_set_heap_eq.
  have e_Lsl : get_heap (set_heap s0 Lrv true) Lsl = get_heap s0 Lsl
    by rewrite get_set_heap_neq.
  set S1 := set_heap (set_heap (set_heap s1 Srv true) rgr_pp_loc (Some pp))
                     rgr_rev_loc true.
  have e_rpp : get_heap S1 rgr_pp_loc = Some pp
    by rewrite /S1 get_set_heap_neq // get_set_heap_eq.
  have e_rtg : get_heap S1 rgr_tgts_loc = get_heap s1 rgr_tgts_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_rtw : get_heap S1 rgr_tws_loc = get_heap s1 rgr_tws_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_rrv : get_heap S1 rgr_rev_loc = true
    by rewrite /S1 get_set_heap_eq.
  have e_rsl : get_heap S1 rgr_slog_loc = get_heap s1 rgr_slog_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_rcnt : get_heap S1 rgr_cnt_loc = get_heap s1 rgr_cnt_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_Spp : get_heap S1 Spp = get_heap s1 Spp
    by rewrite /S1 !get_set_heap_neq.
  have e_Stg : get_heap S1 Stg = get_heap s1 Stg
    by rewrite /S1 !get_set_heap_neq.
  have e_Stw : get_heap S1 Stw = get_heap s1 Stw
    by rewrite /S1 !get_set_heap_neq.
  have e_Srv : get_heap S1 Srv = true
    by rewrite /S1 get_set_heap_neq // get_set_heap_neq // get_set_heap_eq.
  rewrite /RG -/S1 e_Lpp e_Ltg e_Ltw e_Lrv e_Lsl
    e_rpp e_rtg e_rtw e_rrv e_rsl e_rcnt e_Spp e_Stg e_Stw e_Srv.
  by rewrite hrtw hrsl hcnt hle hspp; split=> //; split.
Qed.

(** LSIGN: set [Lsl] and [rgr_slog] to the same value; preserves the invariant. *)
Lemma gr_inv_setsl (vw : seq nat) s0 s1 :
  gr_inv (s0, s1) ->
  gr_inv (set_heap s0 Lsl vw, set_heap s1 rgr_slog_loc vw).
Proof.
move=> hinv.
case/gr_invE: hinv => hign hRG.
case: hRG => hrtw hrrv hrsl hrpp [hspp hsrv hcnt hle hm].
apply: gr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RG
    [get_heap (set_heap s0 Lsl vw) Lpp]get_set_heap_neq //
    [get_heap (set_heap s0 Lsl vw) Ltg]get_set_heap_neq //
    [get_heap (set_heap s0 Lsl vw) Ltw]get_set_heap_neq //
    [get_heap (set_heap s0 Lsl vw) Lrv]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) rgr_pp_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) rgr_tgts_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) rgr_tws_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) rgr_rev_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) rgr_cnt_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) Spp]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) Stg]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) Stw]get_set_heap_neq //
    [get_heap (set_heap s1 rgr_slog_loc vw) Srv]get_set_heap_neq //
    !get_set_heap_eq.
  by rewrite hrtw hrrv hrpp hspp hsrv hcnt hle; split=> //; split.
Qed.

(** The pinned invariant with [Lpp] known (so generic rules unify first-order). *)
Definition gr_invL (pp : PP) : precond :=
  λ '(s0, s1), gr_inv (s0, s1) /\ get_heap s0 Lpp = Some pp.

Arguments gr_invL : simpl never.

(** Couple the two lazy [pp] reads (game [Lpp] vs STCRP [Spp]); land in a
    per-[pp] goal under the invariant with [Lpp] pinned. *)
Lemma r_pp2 {B : choiceType} (k0 k1 : PP -> raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), gr_invL pp (s0, s1) ⦄
                 k0 pp ≈ k1 pp ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), gr_inv (s0, s1) ⦄
     (ppo ← get Lpp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
           end ;; k0 pp)
   ≈ (ppo ← get Spp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
           end ;; k1 pp) ⦃ post ⦄.
Proof.
move=> h.
eapply r_get_remember_lhs => lpp.
eapply r_get_remember_rhs => spp.
eapply (r_fact (spp = lpp)).
  { move=> s0 s1 [[hinv hr0] hr1].
    case/gr_invE: hinv => _ [_ _ _ _ [hsp _ _ _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hsp hr0. }
move=> e; subst spp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv hr0] hr1].
  rewrite /rem_inv /= in hr0.
  rewrite /gr_invL /=.
  by split; [exact: hinv | exact: hr0].
- cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite !bind_put_ret.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [[[hinv hr0] hr1] e0]] e1]].
  rewrite /rem_inv /= in hr0.
  subst s0 s1; rewrite /gr_invL /=; split.
  + exact: (gr_inv_pin pp s0' s1' hinv hr0).
  + by rewrite get_set_heap_eq.
Qed.

(* ================================================================== *)
(** ** The COMMIT pin (carry pp + Ltw + the coordinate freshness). *)

Definition bcm (pp : PP) (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  gr_inv (s0, s1) /\ get_heap s0 Lpp = Some pp /\ get_heap s0 Lrv = false /\
  (size ltw < n_max)%N /\ get_heap s0 Ltw = ltw /\
  gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments bcm : simpl never.

Definition bpre (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  gr_inv (s0, s1) /\ get_heap s0 Lrv = false /\ (size ltw < n_max)%N /\
  get_heap s0 Ltw = ltw /\ gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments bpre : simpl never.

Lemma bcm_Spp (pp : PP) t ltw s0 s1 :
  bcm pp t ltw (s0, s1) -> get_heap s1 Spp = Some pp.
Proof.
move=> [hinv [hlpp _]]; case/gr_invE: hinv => _ [_ _ _ _ [hspp _ _ _ _]].
by rewrite hspp hlpp.
Qed.

Lemma r_pin_commit {B : choiceType} (t : adrs_sf_ch)
    (ltw : seq adrs_sf_ch)
    (k0 : PP -> raw_code B) (k1 : raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), bcm pp t ltw (s0, s1) ⦄ k0 pp ≈ k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), bpre t ltw (s0, s1) ⦄
     (ppo ← get Lpp ;;
      match ppo with
      | Some pp => k0 pp
      | None => pp ← dPP ;; #put Lpp := Some pp ;; k0 pp
      end)
   ≈ (v ← get Spp ;;
      match v with
      | Some _ => k1
      | None => vp ← dPP ;; #put Spp := Some vp ;; k1
      end) ⦃ post ⦄.
Proof.
move=> h.
eapply r_get_remember_lhs => lpp.
eapply r_get_remember_rhs => spp.
eapply (r_fact (spp = lpp)).
  { move=> s0 s1 [[[hinv _] hr0] hr1].
    case/gr_invE: hinv => _ [_ _ _ _ [hsp _ _ _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hsp hr0. }
move=> e; subst spp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[[hinv [hrv [hsz [hltw hfr]]]] hr0] hr1].
  rewrite /rem_inv /= in hr0.
  rewrite /bcm /=.
  by split; [exact: hinv | split; [exact: hr0|split; [exact: hrv|
     split; [exact: hsz|split; [exact: hltw|exact: hfr]]]]].
- cbv beta iota.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 H.
  case: H => s1' [H1 e1]; case: H1 => s0' [H2 e0].
  case: H2 => [[[hinv [hrv [hsz [hltw hfr]]]] hr0] hr1].
  rewrite /rem_inv /= in hr0.
  subst s0 s1; rewrite /bcm /=; split.
  + exact: (gr_inv_pin pp s0' s1' hinv hr0).
  + split; first by rewrite get_set_heap_eq.
    split; first by rewrite get_set_heap_neq.
    split; first exact: hsz.
    split; first by rewrite get_set_heap_neq.
    exact: hfr.
Qed.

(* ------------------------------------------------------------------ *)
(** ** RGrel accessors + the COMMIT-tail reconstruction. *)

(** Coordinate membership -> pk-tweak membership (used for the grind-tweak
    distinctness [grtw_of t \notin stw]). *)
Lemma coord_in_gtw (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) :
  lcoord t \in [seq lcoord x | x <- ltw] ->
  gtw_of t \in [seq gtw_of x | x <- ltw].
Proof.
move=> H; case/mapP: H => x hx hcx.
apply/mapP; exists x => //.
by rewrite hcx.
Qed.

(** grblk field accessors. *)
Lemma grblk_ign po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> heap_ignore IGNG (s0, s1).
Proof. by case. Qed.
Lemma grblk_Ltg po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s0 Ltg = ltg.
Proof. by case=> _ [_ _ _ _ ?]. Qed.
Lemma grblk_Spp po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s1 Spp = po.
Proof. by case=> _ _ _ [? _ _ _ _]. Qed.
Lemma grblk_Srv po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s1 Srv = lrv.
Proof. by case=> _ _ _ [_ ? _ _ _]. Qed.
Lemma grblk_Stw po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s1 Stw = stw.
Proof. by case=> _ _ _ [_ _ ? _ _]. Qed.
Lemma grblk_Stg po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s1 Stg = stg.
Proof. by case=> _ _ _ [_ _ _ ? _]. Qed.
Lemma grblk_cnt po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s1 rgr_cnt_loc = size stw.
Proof. by case=> _ _ _ [_ _ _ _ ?]. Qed.
Lemma grblk_rtg po lrv lsl ltw ltg rtg stg stw s0 s1 :
  grblk po lrv lsl ltw ltg rtg stg stw (s0, s1) -> get_heap s1 rgr_tgts_loc = rtg.
Proof. by case=> _ _ [_ _ _ _ ?] _ _. Qed.

(** RGrel update, grindable leaf (SQUERY commits a new target at index
    [size stw]). *)
Lemma RGrel_qupd_some (pp : PP) (t : adrs_sf_ch) (md : D) (sg : seq N) (c : nat)
    (ltws : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))})
    (stg : {fmap nat -> (th_T TGl × (D × 'nat))})
    (stw : seq (th_T TGl)) :
  find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md = Some c ->
  RGrel pp ltws ltg rtg stg stw ->
  RGrel pp (rcons ltws t)
    (setm ltg (size ltws) (t, (sg, md)))
    (setm rtg (size ltws) (t, (sg, md, Some c, size stw)))
    (setm stg (size stw) (grtw_of t, (md, c)))
    (rcons stw (grtw_of t)).
Proof.
move=> hfc [hcoh hmap]; split.
- move=> g; rewrite mem_rcons in_cons => /orP[/eqP->|hg].
  + by rewrite lcoord_grtw map_rcons mem_rcons in_cons eqxx.
  + by rewrite map_rcons mem_rcons in_cons (hcoh g hg) orbT.
- move=> j; case: (eqVneq j (size ltws)) => [->|hne].
  + rewrite setmE eqxx; exists (size stw); rewrite setmE eqxx hfc.
    split; first by [].
    rewrite size_rcons; split; first by [].
    by rewrite setmE eqxx.
  + rewrite setmE (negbTE hne).
    move: (hmap j); case: (getm ltg j) => [[t0 [sg0 md0]]|].
    * move=> [sidx' [hrtg hmt]]; exists sidx'.
      rewrite setmE (negbTE hne) hrtg; split; first by [].
      case: (find_ctr PP D Hgrind w l S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0) hmt
        => [c0|] // [hlt hstg].
      rewrite size_rcons; split; first exact: (ltn_trans hlt (ltnSn _)).
      by rewrite setmE (ltn_eqF hlt) hstg.
    * by rewrite setmE (negbTE hne).
Qed.

(** RGrel update, non-grindable leaf (no SQUERY; STCRP tables unchanged). *)
Lemma RGrel_qupd_none (pp : PP) (t : adrs_sf_ch) (md : D) (sg : seq N) (sidx : nat)
    (ltws : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))})
    (stg : {fmap nat -> (th_T TGl × (D × 'nat))})
    (stw : seq (th_T TGl)) :
  find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md = None ->
  RGrel pp ltws ltg rtg stg stw ->
  RGrel pp (rcons ltws t)
    (setm ltg (size ltws) (t, (sg, md)))
    (setm rtg (size ltws) (t, (sg, md, None, sidx)))
    stg stw.
Proof.
move=> hfc [hcoh hmap]; split.
- move=> g hg; by rewrite map_rcons mem_rcons in_cons (hcoh g hg) orbT.
- move=> j; case: (eqVneq j (size ltws)) => [->|hne].
  + rewrite setmE eqxx; exists sidx; rewrite setmE eqxx hfc; split=> //.
  + rewrite setmE (negbTE hne).
    move: (hmap j); case: (getm ltg j) => [[t0 [sg0 md0]]|].
    * move=> [sidx' [hrtg hmt]]; exists sidx'.
      by rewrite setmE (negbTE hne) hrtg; split.
    * by rewrite setmE (negbTE hne).
Qed.

(** The COMMIT tail (b-independent): both sides record the leaf; the RHS
    additionally SQUERYs a fresh S-TCR grinding target on grindable leaves.
    The invariant is re-established from the final block state (STCRP remap). *)
Lemma r_lgr_tail (pp : PP) (t : adrs_sf_ch) (md : D)
    (ltws : seq adrs_sf_ch) (sg : seq N) (lsl : seq nat)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))})
    (stg : {fmap nat -> (th_T TGl × (D × 'nat))})
    (stw : seq (th_T TGl)) :
  (size ltws < n_max)%N ->
  gtw_of t \notin [seq gtw_of x | x <- ltws] ->
  RGrel pp ltws ltg rtg stg stw ->
  ⊢ ⦃ λ '(s0, s1), grblk (Some pp) false lsl ltws ltg rtg stg stw (s0, s1) ⦄
     (tgts ← get Ltg ;;
      #put Ltg := setm tgts (size ltws) (t, (sg, md)) ;;
      #put Ltw := rcons ltws t ;;
      ret (rr_pkS PP N D F Tl Hgrind w l S_wn c_max pp t md (size ltws) sg))
   ≈
     (v ← get Spp ;;
      match v with
      | Some s =>
          x6 ← get rgr_cnt_loc ;;
          match lgr_pick [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max] with
          | Some p =>
              v0 ← get Srv ;;
              (#assert ~~ v0 ;;
               tws ← get Stw ;;
               #assert (size tws < q1)%N ;;
               #assert grtw_of t \notin tws ;;
               ppo ← get Spp ;;
               match ppo with
               | Some s0 =>
                   match [seq i <- iota 0 c_max | gprp (th_eval TGl s0 (grtw_of t) (genc md i))] with
                   | [::] => fail
                   | n :: _ =>
                       tgts ← get Stg ;;
                       #put Stg := setm tgts (size tws) (grtw_of t, (md, n)) ;;
                       #put Stw := rcons tws (grtw_of t) ;;
                       ret (th_eval TGl s0 (grtw_of t) (genc md n), n)
                   end
               | None =>
                   x10 ← dPP ;;
                   #put Spp := Some x10 ;;
                   match [seq i <- iota 0 c_max | gprp (th_eval TGl x10 (grtw_of t) (genc md i))] with
                   | [::] => fail
                   | n :: _ =>
                       tgts ← get Stg ;;
                       #put Stg := setm tgts (size tws) (grtw_of t, (md, n)) ;;
                       #put Stw := rcons tws (grtw_of t) ;;
                       ret (th_eval TGl x10 (grtw_of t) (genc md n), n)
                   end
               end) ;;
              #put rgr_cnt_loc := x6.+1 ;;
              x7 ← get rgr_tgts_loc ;;
              #put rgr_tgts_loc := setm x7 (size ltws) (t, (sg, md, Some p.1, x6)) ;;
              #put rgr_tws_loc := rcons ltws t ;;
              ret (Tl s (decode_tweak (gtw_of t))
                     (lcompl (lcoord t) pp (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) sg))
          | None =>
              x7 ← get rgr_tgts_loc ;;
              #put rgr_tgts_loc := setm x7 (size ltws) (t, (sg, md, None, x6)) ;;
              #put rgr_tws_loc := rcons ltws t ;;
              ret (Tl s (decode_tweak (gtw_of t))
                     (lcompl (lcoord t) pp (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) sg))
          end
      | None =>
          x6 ← dPP ;;
          #put Spp := Some x6 ;;
          x7 ← get rgr_cnt_loc ;;
          match lgr_pick [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max] with
          | Some p =>
              v0 ← get Srv ;;
              (#assert ~~ v0 ;;
               tws ← get Stw ;;
               #assert (size tws < q1)%N ;;
               #assert grtw_of t \notin tws ;;
               ppo ← get Spp ;;
               match ppo with
               | Some s =>
                   match [seq i <- iota 0 c_max | gprp (th_eval TGl s (grtw_of t) (genc md i))] with
                   | [::] => fail
                   | n :: _ =>
                       tgts ← get Stg ;;
                       #put Stg := setm tgts (size tws) (grtw_of t, (md, n)) ;;
                       #put Stw := rcons tws (grtw_of t) ;;
                       ret (th_eval TGl s (grtw_of t) (genc md n), n)
                   end
               | None =>
                   x11 ← dPP ;;
                   #put Spp := Some x11 ;;
                   match [seq i <- iota 0 c_max | gprp (th_eval TGl x11 (grtw_of t) (genc md i))] with
                   | [::] => fail
                   | n :: _ =>
                       tgts ← get Stg ;;
                       #put Stg := setm tgts (size tws) (grtw_of t, (md, n)) ;;
                       #put Stw := rcons tws (grtw_of t) ;;
                       ret (th_eval TGl x11 (grtw_of t) (genc md n), n)
                   end
               end) ;;
              #put rgr_cnt_loc := x7.+1 ;;
              x8 ← get rgr_tgts_loc ;;
              #put rgr_tgts_loc := setm x8 (size ltws) (t, (sg, md, Some p.1, x7)) ;;
              #put rgr_tws_loc := rcons ltws t ;;
              ret (Tl x6 (decode_tweak (gtw_of t))
                     (lcompl (lcoord t) pp (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) sg))
          | None =>
              x8 ← get rgr_tgts_loc ;;
              #put rgr_tgts_loc := setm x8 (size ltws) (t, (sg, md, None, x7)) ;;
              #put rgr_tws_loc := rcons ltws t ;;
              ret (Tl x6 (decode_tweak (gtw_of t))
                     (lcompl (lcoord t) pp (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) sg))
          end
      end)
   ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ gr_inv (s0, s1) ⦄.
Proof.
move=> hsz hfr hRC.
have hpick : omap fst (lgr_pick [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max])
   = find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md.
  by rewrite (lgr_copt_E pp (lcoord t) md).
have hsearch : [seq i <- iota 0 c_max | gprp (th_eval TGl pp (grtw_of t) (genc md i))]
   = [seq c <- iota 0 c_max | good_ctr PP D Hgrind w l S_wn (lcoord t).1 (lcoord t).2 pp md c].
  apply: eq_filter => i.
  by rewrite th_eval_grtw /genc /grind_enc /grind_prp /good_ctr /valid_digest /digest_of.
eapply (r_get_rhs_known Spp (Some pp)).
  { move=> s0 s1; exact: grblk_Spp. }
eapply (r_get_rhs_known rgr_cnt_loc (size stw)).
  { move=> s0 s1; exact: grblk_cnt. }
case Ep: (lgr_pick [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max]) => [p|].
- (* grindable leaf: SQUERY commits target at index (size stw) *)
  have Hfc : find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md = Some p.1
    by rewrite -hpick Ep.
  eapply (r_get_rhs_known Srv false).
    { move=> s0 s1; exact: grblk_Srv. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs Stw stw).
    { move=> s0 s1; exact: grblk_Stw. }
  eapply r_bind_assertD_rhs.
    { move=> s0 s1; case=> _ _ _ _ [hle _]; exact: (leq_ltn_trans hle hsz). }
  move=> _.
  eapply r_bind_assertD_rhs.
    { move=> s0 s1 _; apply/negP => Hin.
      have Hc := proj1 hRC (grtw_of t) Hin.
      rewrite lcoord_grtw in Hc.
      by move/negP: hfr; apply; exact: coord_in_gtw. }
  move=> _.
  eapply (r_get_bind_rhs Spp (Some pp)).
    { move=> s0 s1; exact: grblk_Spp. }
  have HLo : ohead [seq i <- iota 0 c_max | gprp (th_eval TGl pp (grtw_of t) (genc md i))] = Some p.1
    by rewrite hsearch; exact: Hfc.
  move: HLo; case EL: [seq i <- iota 0 c_max | gprp (th_eval TGl pp (grtw_of t) (genc md i))]
    => [|n rest] /=; first by move=> [].
  move=> [Hn]; subst n.
  eapply (r_get_rhs_known Stg stg).
    { move=> s0 s1; exact: grblk_Stg. }
  apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  eapply (r_get_rhs_known rgr_tgts_loc rtg).
    { move=> s0 s1 [s1a [[s1b [[s1c [hb ->]] ->]] ->]].
      rewrite !get_set_heap_neq //; exact: (grblk_rtg _ _ _ _ _ _ _ _ _ _ hb). }
  apply r_put_rhs; apply r_put_rhs.
  eapply (r_get_lhs_known Ltg ltg).
    { move=> s0 s1 [s1a [[s1b [[s1c [[s1d [[s1e [hb _]] _]] _]] _]] _]].
      exact: (grblk_Ltg _ _ _ _ _ _ _ _ _ _ hb). }
  apply r_put_lhs; apply r_put_lhs.
  apply r_ret => s0 s1 hpre.
  move: hpre =>
    [s0a [[s0b [[s1a [[s1b [[s1c [[s1d [[s1e [hb e6]] e5]] e4]] e3]] e2]] e1]] e0]].
  subst s0 s0a s1 s1a s1b s1c s1d.
  case: hb => hign [hLpp hLrv hLsl hLtw hLtg] [hrpp hrrv hrsl hrtw hrtg]
              [hSpp hSrv hStw hStg hcnt] [hle hRGr].
  split.
  + by rewrite /rr_pkS decode_tweakK.
  + apply: gr_invI.
    * apply: heap_ignore_set_l; first by rewrite mem_domm.
      apply: heap_ignore_set_l; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      exact: hign.
    * rewrite /RG.
      get_heap_simpl.
      rewrite hLpp hLrv hLsl hrpp hrrv hrsl hSpp hSrv.
      split=> //; split=> //.
      -- by rewrite size_rcons.
      -- by rewrite !size_rcons; exact: (leq_ltn_trans hle (ltnSn _)).
      -- exact: (RGrel_qupd_some pp t md sg p.1 ltws ltg rtg stg stw Hfc hRGr).
- (* non-grindable leaf: no SQUERY, STCRP tables unchanged *)
  have Hfc : find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md = None
    by rewrite -hpick Ep.
  eapply (r_get_rhs_known rgr_tgts_loc rtg).
    { move=> s0 s1; exact: grblk_rtg. }
  apply r_put_rhs; apply r_put_rhs.
  eapply (r_get_lhs_known Ltg ltg).
    { move=> s0 s1 [s1a [[s1b [hb _]] _]].
      exact: (grblk_Ltg _ _ _ _ _ _ _ _ _ _ hb). }
  apply r_put_lhs; apply r_put_lhs.
  apply r_ret => s0 s1 hpre.
  move: hpre => [s0a [[s0b [[s1a [[s1b [hb e4]] e3]] e2]] e1]].
  subst s0 s0a s1 s1a.
  case: hb => hign [hLpp hLrv hLsl hLtw hLtg] [hrpp hrrv hrsl hrtw hrtg]
              [hSpp hSrv hStw hStg hcnt] [hle hRGr].
  split.
  + by rewrite /rr_pkS decode_tweakK.
  + apply: gr_invI.
    * apply: heap_ignore_set_l; first by rewrite mem_domm.
      apply: heap_ignore_set_l; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      apply: heap_ignore_set_r; first by rewrite mem_domm.
      exact: hign.
    * rewrite /RG.
      get_heap_simpl.
      rewrite hLpp hLrv hLsl hrpp hrrv hrsl hSpp hSrv hStw hStg hcnt.
      split=> //; split=> //.
      -- by rewrite size_rcons; apply: leqW hle.
      -- exact: (RGrel_qupd_none pp t md sg (size stw) ltws ltg rtg stg stw Hfc hRGr).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The GRIND sub-bound (ladder step G1l -> Glmid1). *)

Local Notation GM0 := (G1l    PP N D F Tl Hgrind Htree dPP dN w l S_wn c_max n_max).
Local Notation GM1 := (Glmid1 PP N D F Tl Hgrind Htree dPP dN w l S_wn c_max n_max).

(** The two perfect equivalences (perfect-routing recipe). *)
Lemma R_gr_leaf_real
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : D * nat), (Hgrind pp' a x < w ^ l)%N) :
  perfect IKM GM0 (R_gr_leaf ∘ STB true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ gr_inv).
{ rewrite /gr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *)
  rewrite /rr_commit.
  ssprove_code_simpl; simpl.
  destruct arg as [t md].
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/gr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws.
  eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/gr_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws.
  eapply r_assertD_same => hsz.
  eapply r_assertD_same => hfr.
  eapply rpre_weaken_rule with (pre := λ '(s0, s1), bpre t ltws (s0, s1)).
  2:{ move=> s0 s1 H.
      case: H => [[[[hinv hrL] _] hr0] _].
      rewrite /rem_inv /= in hrL hr0.
      rewrite /bpre; split; first exact: hinv.
      split; first by rewrite hrL (negbTE erev).
      split; first exact: hsz.
      split; first exact: hr0.
      exact: hfr. }
  eapply r_pin_commit => pp.
  eapply (r_lgrgrind_spec true pp (lcoord t) md (iota 0 c_max)
            (bcm pp t ltws) (bcm_Spp pp t ltws)).
  set hs := [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max].
  have hds : lgr_digitS (size ltws) hs
           = rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws).
    rewrite /lgr_digitS /rr_digitS.
    by rewrite /hs lgr_digit_E /rr_digit.
  rewrite hds.
  rewrite /rr_F.
  eapply (r_lgrchains_spec true pp (lcoord t)
            (bcm pp t ltws) (bcm_Spp pp t ltws)).
  move=> us hus.
  cbv beta iota.
  set sg := wsigs (lcoord t) pp 0
              (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) us.
  have hszl : size (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) = l.
    rewrite /rr_digitS /rr_digit;
    case: (find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md) => [c|];
      [exact: (size_digest_of PP D Hgrind w l (lcoord t).1 (lcoord t).2 pp md c)
      | exact: size_nseq].
  rewrite -/sg (wendsEl (lcoord t) pp _ sg hszl).
  apply rpre_hypothesis_rule => s0 s1 hbcm.
  move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
  have hblk := gr_inv_grblk s0 s1 hinv hrv.
  rewrite hlpp hltw in hblk.
  eapply rpre_weaken_rule.
  { apply: (r_lgr_tail pp t md ltws sg (get_heap s0 Lsl)
              (get_heap s0 Ltg) (get_heap s1 rgr_tgts_loc) (get_heap s1 Stg)
              (get_heap s1 Stw)).
    - exact: hsz'.
    - exact: hfr'.
    - by case: hblk => _ _ _ _ [_ hm]. }
  by move=> s0' s1' /= [-> ->]; exact: hblk.
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rgr_pp_loc := Some b ;; #put rgr_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (gr_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK *)
  destruct arg as [j mw].
  rewrite /rr_winbody.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/gr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  { eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => _ hm2; by move: (hm2 j); rewrite hr2 E /= -hr3.
        - by case: hm => _ hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split. }
  eapply r_get_remember_lhs => lpp.
  eapply (r_fact (exists pp sidx, lpp = Some pp /\
            getm rtg j = Some (t0, (sg, md0, lfind (lcoord t0) pp md0, sidx)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
      case/gr_invE: hinv => _ [_ hrrv _ _ [_ _ _ _ hm]].
      have hlrv : get_heap s0 Lrv = true by rewrite hr0.
      move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
      - case: hm => _ hm2; move: (hm2 j); rewrite hr2 E /= => -[sidx [hrtg _]].
        exists pp, sidx; split; first by rewrite -hr4.
        by rewrite -hr3.
      - by case: hm => _ _ _ _ habs; rewrite habs in hlrv. }
  move=> [pp [sidx [hlpp hrtgj]]].
  rewrite hlpp hrtgj /=.
  eapply (r_get_rhs_known rgr_pp_loc (Some pp)).
    { move=> s0 s1 [[[[[hinv hA] _] _] _] hE].
      rewrite /rem_inv /= in hA hE.
      case/gr_invE: hinv => _ [_ _ _ hrpp _].
      by rewrite hrpp hA erev /= hE. }
  cbv beta iota.
  rewrite bind_ret_l.
  rewrite P_g1l_E.
  set cc := find_ctr PP D Hgrind w l S_wn c_max (adrs_height (decode_tweak t0))
              (adrs_index (decode_tweak t0)) pp md0.
  case Ev: (lgr_v pp t0 sg md0 cc j mw && lgr_ghit pp t0 md0 cc j mw); last first.
  { apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[hinv _] _] _] _] _]. }
  move: (Ev) => /andP[Hv Hgh].
  move: (Hgh) => /andP[Hcc Hdv].
  have [c Hcceq] : exists c, cc = Some c by case: (cc) Hcc => [cc0|] // _; exists cc0.
  have Hfc : find_ctr PP D Hgrind w l S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0 = Some c
    by exact: Hcceq.
  simplify_linking.
  eapply (r_get_rhs_known Srv true).
    { move=> s0 s1 [[[[[hinv hA] _] _] _] _].
      rewrite /rem_inv /= in hA.
      case/gr_invE: hinv => _ [_ _ _ _ [_ hsrv _ _ _]].
      by rewrite hsrv hA erev. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_get_remember_rhs => stgv.
  eapply (r_fact (getm stgv sidx = Some (grtw_of t0, (md0, c)))).
    { move=> s0 s1 [[[[[[hinv hA] _] hLtgr] hRtgr] hLppr] hStgr].
      rewrite /rem_inv /= in hLtgr hRtgr hLppr hStgr.
      case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
      have hpp0 : get_heap s0 Lpp = Some pp by rewrite hLppr.
      move: hm; rewrite hpp0 => -[_ hm2]; move: (hm2 j); rewrite hLtgr E /= => -[sidx' [hrtg' hmt]].
      rewrite hRtgr in hrtg'.
      have esidx : sidx' = sidx.
        have E3 : Some (t0, (sg, md0, lfind (lcoord t0) pp md0, sidx'))
                = Some (t0, (sg, md0, lfind (lcoord t0) pp md0, sidx))
          by rewrite -hrtg' hrtgj.
        exact: (congr1 (fun o => match o with Some x => x.2.2 | None => sidx end) E3).
      move: hmt; rewrite esidx Hfc => -[_ hstgeq].
      by rewrite -hStgr. }
  move=> Hstg.
  rewrite Hstg /=.
  eapply (r_get_rhs_known Spp (Some pp)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hLppr] _].
      rewrite /rem_inv /= in hLppr.
      case/gr_invE: hinv => _ [_ _ _ _ [hspp _ _ _ _]].
      by rewrite hspp hLppr. }
  apply r_ret => s0 s1 hpre.
  have hgr : gr_inv (s0, s1) by case: hpre => [[[[[[hinv _] _] _] _] _] _].
  split; last exact: hgr.
  have Hfresh : mw.1 != md0.
    move: Hv => /andP[_ Hg]; rewrite Hcceq /= in Hg; exact: Hg.
  move: Hdv; rewrite /l_rrdigS /l_rrdig Hfc => /eqP Hdv'.
  have Hcol' : Hgrind pp (wotsc_grind_adrs (lcoord t0)) (mw.1, mw.2.2)
             = Hgrind pp (wotsc_grind_adrs (lcoord t0)) (md0, c)
    := wdigest_inj PP D Hgrind w l (lcoord t0).1 (lcoord t0).2 pp
         mw.1 mw.2.2 md0 c Hrange Hdv'.
  have -> : lgr_v pp t0 sg md0 cc j mw = true by exact: Hv.
  symmetry; apply/andP; split; first exact: Hfresh.
  by apply/eqP; rewrite !th_eval_grtw /genc /grind_enc Hcol'.
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/gr_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  eapply r_assertD_same => _.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  { eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => _ hm2; by move: (hm2 j); rewrite hr2 E /= -hr3.
        - by case: hm => _ hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split. }
  eapply r_get_remember_lhs => lpp.
  eapply (r_fact (exists pp sidx, lpp = Some pp /\
            getm rtg j = Some (t0, (sg, md0, lfind (lcoord t0) pp md0, sidx)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr2 hr3 hr4.
      case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
      move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
      - case: hm => _ hm2; move: (hm2 j); rewrite hr2 E /= => -[sidx [hrtg _]].
        exists pp, sidx; split; first by rewrite -hr4.
        by rewrite -hr3.
      - by case: hm => habs _ _ _ _; rewrite -hr2 habs emptymE in E. }
  move=> [pp [sidx [hlpp hrtgj]]].
  rewrite hlpp hrtgj /=.
  case E2: (find_ctr PP D Hgrind w l S_wn c_max (adrs_height (decode_tweak t0))
             (adrs_index (decode_tweak t0)) pp md0) => [c|].
  + apply r_put_lhs; apply r_put_rhs.
    apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
    rewrite /rem_inv /= in hr0 hr1.
    subst s0 s1; split=> //.
    exact: (gr_inv_setsl (rcons slog j) s0' s1' hinv).
  + apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CGl_leaf pp t (inr (inr (inl xy))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CGl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CGl_leaf pp t (inr (inr (inr dc))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CGl_leaf.
Qed.

Lemma R_gr_leaf_ideal :
  perfect IKM GM1 (R_gr_leaf ∘ STB false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ gr_inv).
{ rewrite /gr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *)
  rewrite /rr_commit.
  ssprove_code_simpl; simpl.
  destruct arg as [t md].
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/gr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws.
  eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/gr_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws.
  eapply r_assertD_same => hsz.
  eapply r_assertD_same => hfr.
  eapply rpre_weaken_rule with (pre := λ '(s0, s1), bpre t ltws (s0, s1)).
  2:{ move=> s0 s1 H.
      case: H => [[[[hinv hrL] _] hr0] _].
      rewrite /rem_inv /= in hrL hr0.
      rewrite /bpre; split; first exact: hinv.
      split; first by rewrite hrL (negbTE erev).
      split; first exact: hsz.
      split; first exact: hr0.
      exact: hfr. }
  eapply r_pin_commit => pp.
  eapply (r_lgrgrind_spec false pp (lcoord t) md (iota 0 c_max)
            (bcm pp t ltws) (bcm_Spp pp t ltws)).
  set hs := [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max].
  have hds : lgr_digitS (size ltws) hs
           = rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws).
    rewrite /lgr_digitS /rr_digitS.
    by rewrite /hs lgr_digit_E /rr_digit.
  rewrite hds.
  rewrite /rr_F.
  eapply (r_lgrchains_spec false pp (lcoord t)
            (bcm pp t ltws) (bcm_Spp pp t ltws)).
  move=> us hus.
  cbv beta iota.
  set sg := wsigs (lcoord t) pp 0
              (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) us.
  have hszl : size (rr_digitS PP D Hgrind w l S_wn c_max pp t md (size ltws)) = l.
    rewrite /rr_digitS /rr_digit;
    case: (find_ctr PP D Hgrind w l S_wn c_max (lcoord t).1 (lcoord t).2 pp md) => [c|];
      [exact: (size_digest_of PP D Hgrind w l (lcoord t).1 (lcoord t).2 pp md c)
      | exact: size_nseq].
  rewrite -/sg (wendsEl (lcoord t) pp _ sg hszl).
  apply rpre_hypothesis_rule => s0 s1 hbcm.
  move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
  have hblk := gr_inv_grblk s0 s1 hinv hrv.
  rewrite hlpp hltw in hblk.
  eapply rpre_weaken_rule.
  { apply: (r_lgr_tail pp t md ltws sg (get_heap s0 Lsl)
              (get_heap s0 Ltg) (get_heap s1 rgr_tgts_loc) (get_heap s1 Stg)
              (get_heap s1 Stw)).
    - exact: hsz'.
    - exact: hfr'.
    - by case: hblk => _ _ _ _ [_ hm]. }
  by move=> s0' s1' /= [-> ->]; exact: hblk.
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rgr_pp_loc := Some b ;; #put rgr_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (gr_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK *)
  destruct arg as [j mw].
  rewrite /rr_winbody.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/gr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  { eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => _ hm2; by move: (hm2 j); rewrite hr2 E /= -hr3.
        - by case: hm => _ hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split. }
  eapply r_get_remember_lhs => lpp.
  eapply (r_fact (exists pp sidx, lpp = Some pp /\
            getm rtg j = Some (t0, (sg, md0, lfind (lcoord t0) pp md0, sidx)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
      case/gr_invE: hinv => _ [_ hrrv _ _ [_ _ _ _ hm]].
      have hlrv : get_heap s0 Lrv = true by rewrite hr0.
      move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
      - case: hm => _ hm2; move: (hm2 j); rewrite hr2 E /= => -[sidx [hrtg _]].
        exists pp, sidx; split; first by rewrite -hr4.
        by rewrite -hr3.
      - by case: hm => _ _ _ _ habs; rewrite habs in hlrv. }
  move=> [pp [sidx [hlpp hrtgj]]].
  rewrite hlpp hrtgj /=.
  eapply (r_get_rhs_known rgr_pp_loc (Some pp)).
    { move=> s0 s1 [[[[[hinv hA] _] _] _] hE].
      rewrite /rem_inv /= in hA hE.
      case/gr_invE: hinv => _ [_ _ _ hrpp _].
      by rewrite hrpp hA erev /= hE. }
  cbv beta iota.
  rewrite bind_ret_l.
  rewrite P_gm1_E.
  set cc := find_ctr PP D Hgrind w l S_wn c_max (adrs_height (decode_tweak t0))
              (adrs_index (decode_tweak t0)) pp md0.
  case Ev: (lgr_v pp t0 sg md0 cc j mw && lgr_ghit pp t0 md0 cc j mw).
  + (* GRIND route: ideal SCHECK = false; Glmid1 nulls *)
    ssprove_code_simpl; simpl.
    apply r_ret => s0 s1 hpre.
    have hgr : gr_inv (s0, s1) by case: hpre => [[[[[hinv _] _] _] _] _].
    split; last exact: hgr.
    by move: (Ev) => /andP[_ Hgh]; rewrite Hgh andbF.
  + (* no route: Glmid1 = lgr_v *)
    ssprove_code_simpl; simpl.
    apply r_ret => s0 s1 hpre.
    have hgr : gr_inv (s0, s1) by case: hpre => [[[[[hinv _] _] _] _] _].
    split; last exact: hgr.
    move: Ev => /negbT; rewrite negb_and => /orP[hnv|hgh].
    * by rewrite (negbTE hnv).
    * by rewrite hgh andbT.
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/gr_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  eapply r_assertD_same => _.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  { eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => _ hm2; by move: (hm2 j); rewrite hr2 E /= -hr3.
        - by case: hm => _ hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split. }
  eapply r_get_remember_lhs => lpp.
  eapply (r_fact (exists pp sidx, lpp = Some pp /\
            getm rtg j = Some (t0, (sg, md0, lfind (lcoord t0) pp md0, sidx)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr2 hr3 hr4.
      case/gr_invE: hinv => _ [_ _ _ _ [_ _ _ _ hm]].
      move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
      - case: hm => _ hm2; move: (hm2 j); rewrite hr2 E /= => -[sidx [hrtg _]].
        exists pp, sidx; split; first by rewrite -hr4.
        by rewrite -hr3.
      - by case: hm => habs _ _ _ _; rewrite -hr2 habs emptymE in E. }
  move=> [pp [sidx [hlpp hrtgj]]].
  rewrite hlpp hrtgj /=.
  case E2: (find_ctr PP D Hgrind w l S_wn c_max (adrs_height (decode_tweak t0))
             (adrs_index (decode_tweak t0)) pp md0) => [c|].
  + apply r_put_lhs; apply r_put_rhs.
    apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
    rewrite /rem_inv /= in hr0 hr1.
    subst s0 s1; split=> //.
    exact: (gr_inv_setsl (rcons slog j) s0' s1' hinv).
  + apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CGl_leaf pp t (inr (inr (inl xy))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CGl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CGl_leaf pp t (inr (inr (inr dc))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CGl_leaf.
Qed.

(** sub_gr : the GRIND step of the ladder. *)
Lemma sub_gr
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : D * nat), (Hgrind pp' a x < w ^ l)%N)
    (B : nom_package) (VB : ValidPackage (loc B) IKM A_export B) :
  Adv GM0 GM1 B = AdvOf (STCRP_game TGl CGl_leaf D genc gprp c_max q1) (B ∘ R_gr_leaf).
Proof.
rewrite (Adv_perfect_l (R_gr_leaf_real Hrange)).
rewrite (Adv_perfect_r R_gr_leaf_ideal).
by rewrite Adv_reduction.
Qed.

End Leaf2Grind.
