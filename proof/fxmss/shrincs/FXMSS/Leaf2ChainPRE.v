(** * SHRINCS.FXMSS.Leaf2ChainPRE
    FXMSS leaf-hop LAYER (ii) CHAIN-PRE sub-bound (Glmid3 -> G1l', TERMINAL).

    The multi-instance lift of WOTSC/ChainHop.v's [R_cpre] (SM-PRE(F) hop)
    to ALL leaves, over the STATIC-gate EU-CMA endpoint [MIW_kmS] (M1a
    re-landing: [lpr_v] = P_gm3S-form, slog-free; slot-keyed digit
    [l_rrdigS]; uniform [lpr_pd] placement at [rr_digitS_i - 1]; the
    perfects are the M1d milestone).  This is the TERMINAL hop of the
    ladder: [G1l'] answers [ret false] on LCHECK.

    Delivered:
      [R_cpre_leaf_real  : perfect IKM Glmid3 (R_cpre_leaf o SMPRE(TFl,CFl) q2 true)]
      [R_cpre_leaf_ideal : perfect IKM G1l'   (R_cpre_leaf o SMPRE(TFl,CFl) q2 false)]
      [sub_cpre : Adv Glmid3 G1l' B = AdvOf (SMPRE_game TFl CFl_leaf q2) (B o R_cpre_leaf)]

    ** Design (the COMPRESS pattern, retargeted to SM-PRE(F)).

    - Target = the chain hash [F] (TFl = Tf at the leaf), budget
      [q2 = n_max * l] (one PQUERY per positive-digit chain per leaf).
      The SM-PRE challenge IMAGE is planted at the chain endpoint (the hidden
      root sampled inside PQUERY); the forgery's chain-recover gives the
      preimage which wins PCHECK.
    - Collection [CFl_leaf] exposes F (chain walks), Tl (pk compression),
      Htree (exported LCOLLQ.inl) and Hgrind (grinding + exported LCOLLQ.inr),
      all under the hidden pp.  Unlike WOTSC/ChainHop (single instance, one
      PGETPP), the multi-leaf reduction NEVER calls PGETPP inside LCOMMIT (it
      would disable later leaves' PQUERYs); instead it computes the pk via
      COLLQ(Tl) on the COLLQ(F)-completed ends, exactly like Leaf2Compress.
    - Cross-leaf re-indexing: each leaf's PQUERYs land at running keys; the
      reduction stores the leaf's OFFSET [ofs] in its target record so LCHECK
      routes PCHECK at [ofs + pre_index].
    - MIXED POPULATION (key finding): a grindable leaf re-roots at the SIGNED
      digest ([find_ctr = Some]) where [valid_msg] holds and the used-instance
      [pre_decisionP] applies; a never-grinding leaf re-roots at the VIRTUAL
      all-max digit [nseq l w.-1] where [valid_msg] FAILS (under
      [S_wn != l*w.-1]) and the zero-query [zpre_win] preimage extraction
      applies.  The F3 [wots_checks] guard (in [P_gm3]'s [verok]) kills the
      degenerate all-max FORGERY (fdv = all-max fails valid_digest under Hdeg),
      so every surviving Glmid3-win routes to a genuine SM-PRE preimage. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From HBS Require Import Prelude Math.BinTree Math.Merkle Math.Chain Math.Encoding
  Sig.Scheme Games.THF Games.SMTCR Games.SMPRE Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop FixedSumOTS.PREHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis
  WOTSC.ZeroGames WOTSC.ZeroChainHop
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames FXMSS.TreeHop
  FXMSS.LeafReduction FXMSS.LeafKM FXMSS.Leaf2Common FXMSS.Leaf2Games.
From Stdlib Require Import ZArith.
From mathcomp Require Import all_ssreflect reals.
From Model Require Import fin.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section Leaf2ChainPRE.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same DATA-ONLY section context as FXMSS/Leaf2Games.v. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (n0 : N) (d0 : D).

(* ------------------------------------------------------------------ *)
(** ** Shorthands. *)

Local Notation lcoord t := (@LeafKM.lcoord w l t).
Local Notation IKM := (@I_MIW_km w l PP N D).

(** The leaf SM-PRE(F) target THF: Tf at the leaf chain hash. *)
Local Notation TFl := (Tf PP N F dPP dN).

(** The collection: F (chain walks), Tl (pk compression), Htree
    (LCOLLQ.inl), Hgrind (grinding + LCOLLQ.inr) -- all under hidden pp. *)
Definition CFl_leaf : thf_coll TFl :=
  Build_thf_coll TFl adrs_sf_ch
    (N ∐ (('list N) ∐ ((N × N) ∐ (D × 'nat))))
    (N ∐ (N ∐ (N ∐ 'nat)))
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr (inl xs) => inr (inl (Tl pp (decode_tweak t) xs))
       | inr (inr (inl xy)) => inr (inr (inl (Htree pp (decode_tweak t) xy)))
       | inr (inr (inr dc)) => inr (inr (inr (Hgrind pp (decode_tweak t) dc)))
       end).

Local Notation IMP := (I_SMPRE TFl CFl_leaf).

(** q2 = n_max*l committed chain targets (one PQUERY per positive digit
    per leaf). *)
Local Notation q2 := (n_max * l)%N.

Local Notation gtw_of t :=
  (@encode_adrs l w (@wotsc_pk_adrs l w (lcoord t))).
Local Notation chtw_of t i k :=
  (@encode_adrs l w (@wotsc_chain_adrs l w (lcoord t) i k)).
Local Notation grtw_of t :=
  (@encode_adrs l w (@wotsc_grind_adrs l w (lcoord t))).

Local Notation gprp := (@grind_prp w l S_wn).
Local Notation lnpq ds := (count (fun d => (0 < d)%N) ds).

(** Inlined re-root digit / pk (= Leaf2Games.rr_digit / rr_pk at
    zi = lcoord t; inlined to avoid depending on the section-discharge
    signatures). *)
Definition l_rrdig (zi : nat * nat) (pp : PP) (md : D) : seq nat :=
  match find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md with
  | Some c => digest_of PP D Hgrind zi.1 zi.2 pp md c
  | None => nseq l w.-1
  end.

Definition l_rrpk (zi : nat * nat) (pp : PP) (md : D) (sg : seq N) : N :=
  Tl pp (wotsc_pk_adrs zi)
     (complete_ends PP N F zi.1 zi.2 pp (l_rrdig zi pp md) sg).

(** The SLOT-KEYED static digit / pk (= Leaf2Games.rr_digitS / rr_pkS at
    zi = lcoord t, M1a): virtual [nseq l w.-1] for out-of-budget slots. *)
Definition l_rrdigS (zi : nat * nat) (pp : PP) (md : D) (j : nat) : seq nat :=
  l_rrdig zi pp md.

Definition l_rrpkS (zi : nat * nat) (pp : PP) (md : D) (j : nat)
    (sg : seq N) : N :=
  Tl pp (wotsc_pk_adrs zi)
     (complete_ends PP N F zi.1 zi.2 pp (l_rrdigS zi pp md j) sg).

(** The leaf chain hash (= Leaf2Games.rr_F). *)
Local Notation lF zi := (Fw PP N F zi.1 zi.2).

(* ------------------------------------------------------------------ *)
(** ** Import opsigs. *)

Definition lpr_cqo : opsig := (PCOLLQ, (tc_T CFl_leaf × tc_M CFl_leaf, tc_N CFl_leaf)).
Definition lpr_pqo : opsig := (PQUERY, (th_T TFl, th_N TFl)).
Definition lpr_gpo : opsig := (PGETPP, ('unit, th_PP TFl)).
Definition lpr_cko : opsig := (PCHECK, ('nat × th_M TFl, 'bool)).

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed loops. *)

(** Grinding loop: one PCOLLQ (Hgrind member, [inr (inr (inr _))]) per
    counter. *)
Fixpoint lpr_grind (zi : nat * nat) (md : D) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lpr_cqo (encode_adrs (wotsc_grind_adrs zi), inr (inr (inr (md, c))))
        (λ r, hs ← lpr_grind zi md cs' ;;
              ret ((if r is inr (inr (inr h)) then h else 0) :: hs))
  end.

#[local] Instance lpr_grind_valid (L : Locations) zi md cs :
  ValidCode L IMP (lpr_grind zi md cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lpr_cqo; fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n] steps,
    one PCOLLQ (F member, [inl]) per step. *)
Fixpoint lpr_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr lpr_cqo (encode_adrs (wotsc_chain_adrs zi i k), inl x)
         (λ r, lpr_walk zi i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance lpr_walk_valid (L : Locations) zi i k n x :
  ValidCode L IMP (lpr_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lpr_cqo; fmap_solve.
  move=> r; exact: IH.
Qed.

(** All chains: per positive-digit chain, PQUERY the sig value (planting
    the SM-PRE challenge at the endpoint, root hidden); zero-digit chains
    sample the value locally.  Then walk upward (PCOLLQ F) to the ends;
    returns (sig values, completed ends). *)
Fixpoint lpr_chains (zi : nat * nat) (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      s ← (if d is d'.+1
           then opr lpr_pqo (encode_adrs (wotsc_chain_adrs zi st d')) (λ y, ret y)
           else (dN : raw_code N)) ;;
      e ← lpr_walk zi st d (w.-1 - d) s ;;
      '(ss, es) ← lpr_chains zi st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance lpr_chains_valid (L : Locations) zi st ds :
  ValidCode L IMP (lpr_chains zi st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind.
  + case: d => [|d'].
    * eapply valid_scheme, prog_valid.
    * eapply valid_opr; first by rewrite /lpr_pqo; fmap_solve.
      move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: lpr_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(** The bounded grind search on the answer list (= scheme [find_ctr]). *)
Definition lpr_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 c_max) hs | gprp ch.2].

Definition lpr_digit (hs : seq nat) : seq nat :=
  match lpr_pick hs with
  | Some ch => digits_w w l ch.2
  | None => nseq l w.-1
  end.

(** The SLOT-KEYED commit digit (= rr_digitS reconstructed at slot [j]). *)
Definition lpr_digitS (j : nat) (hs : seq nat) : seq nat :=
  lpr_digit hs.

(* ------------------------------------------------------------------ *)
(** ** The LCHECK pure decisions. *)

(** The re-rooted guarded "verify" + STATIC-gate nulls, expressed inline
    (= P_gm3S at the stored find_ctr counter, M1a slog-FREE form). *)
Definition lpr_v (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (copt : 'option 'nat) (j : nat)
    (mw : D × (('list N) × 'nat)) : bool :=
  let fdv := digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2 in
  let rdg := l_rrdigS (lcoord t0) pp md0 j in
  let vchecks := wots_checks PP N D Hgrind S_wn pp (lcoord t0) mw.1 mw.2 in
  let verok := (vchecks
                && (recover_anchor PP N D F Tl Hgrind pp (lcoord t0) mw.1 mw.2
                    == l_rrpkS (lcoord t0) pp md0 j sg))%B in
  let gate := (~~ isSome copt || (mw.1 != md0))%B in
  let ghit := (isSome copt && (fdv == rdg))%B in
  let compress_ok :=
    (complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp fdv mw.2.1
     == complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp rdg sg)%B in
  let tcr_none :=
    (~~ isSome (tcr_decision PP N (lF (lcoord t0)) l w pp rdg fdv sg mw.2.1))%B in
  [&& verok, gate, ~~ ghit, compress_ok & tcr_none].

(** The PRE routing decision (which chain to invert), at the slot-keyed
    digit: the placement [rr_digitS_i - 1] covers BOTH populations (the
    virtual digit specializes it to the zero-query endpoint placement w-2,
    WLOG_DESIGN.md probes E/F/F'). *)
Definition lpr_pd (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) : option (nat * N) :=
  pre_decision PP N (lF (lcoord t0)) l w pp
    (l_rrdigS (lcoord t0) pp md0 j)
    (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
    sg mw.2.1.

(* ------------------------------------------------------------------ *)
(** ** The reduction package R_cpre_leaf : package IMP IKM. *)

(** R's own state (700+).  The tgts record adds the find_ctr counter option
    [copt] (LSIGN reveals it, LCHECK reads grindability) AND the running
    offset [ofs] into the concatenated SM-PRE target list. *)
Definition rpr_rev_loc  := mkloc 700 (false : bool).
Definition rpr_tws_loc  := mkloc 701 ([::] : seq adrs_sf_ch).
Definition rpr_tgts_loc :=
  mkloc 702 (emptym : {fmap nat -> (adrs_sf_ch × ((('list N × D) × 'option 'nat) × 'nat))}).
Definition rpr_slog_loc := mkloc 703 ([::] : seq nat).
Definition rpr_pp_loc   := mkloc 704 (None : option PP).
Definition rpr_cnt_loc  := mkloc 705 (0%N : nat).

Local Notation RPRLocs :=
  [fmap rpr_rev_loc ; rpr_tws_loc ; rpr_tgts_loc ; rpr_slog_loc ; rpr_pp_loc ;
        rpr_cnt_loc ].

Definition R_cpre_leaf : package IMP IKM.
Proof.
notypeclasses refine [package RPRLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) {
      revealed ← get rpr_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get rpr_tws_loc ;;
      #assert (size tws < n_max)%N ;;
      #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
      _ ← opr lpr_cqo (grtw_of t, inr (inr (inr (md, 0)))) (λ r, ret r) ;;
      hs ← lpr_grind (lcoord t) md (iota 0 c_max) ;;
      ofs ← get rpr_cnt_loc ;;
      '(sg, ends) ← lpr_chains (lcoord t) 0 (lpr_digitS (size tws) hs) ;;
      root ← opr lpr_cqo (gtw_of t, inr (inl ends))
               (λ r, ret (match r with inr (inl y) => y | _ => n0 end)) ;;
      #put rpr_cnt_loc := (ofs + lnpq (lpr_digitS (size tws) hs))%N ;;
      tgts ← get rpr_tgts_loc ;;
      #put rpr_tgts_loc := setm tgts (size tws)
                             (t, (((sg, md), omap fst (lpr_pick hs)), ofs)) ;;
      #put rpr_tws_loc := rcons tws t ;;
      ret root
    } ;
    [ LGETPP ] : { 'unit ~> PP } (_) {
      pp ← opr lpr_gpo Datatypes.tt (λ p, ret p) ;;
      #put rpr_pp_loc := Some pp ;;
      #put rpr_rev_loc := true ;;
      ret pp
    } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      revealed ← get rpr_rev_loc ;;
      if revealed then
        tgts ← get rpr_tgts_loc ;;
        match getm tgts j with
        | Some (t0, (((sg, md0), copt), ofs)) =>
            ppo ← get rpr_pp_loc ;;
            pp ← match ppo with
                 | Some pp => ret pp
                 | None => pp ← dPP ;; #put rpr_pp_loc := Some pp ;; ret pp
                 end ;;
            match lpr_pd pp t0 sg md0 j mw with
            | Some (jc, x) =>
                if lpr_v pp t0 sg md0 copt j mw
                then opr lpr_cko ((ofs + jc)%N, x) (λ ans, ret ans)
                else ret false
            | None => ret false
            end
        | None => ret false
        end
      else
        (* pre-commitment gadget (WOTSC R_cpre): real PCHECK fails on the
           phase assert (= Glmid3's [#assert revealed] fail); ideal PCHECK
           returns false (= G1l''s [ret false]). *)
        opr lpr_cko (0, n0) (λ ans, ret ans)
    } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) {
      slog ← get rpr_slog_loc ;;
      #assert (j \notin slog) ;;
      tgts ← get rpr_tgts_loc ;;
      match getm tgts j with
      | Some (t0, (((sg, md0), copt), ofs)) =>
          match copt with
          | Some c => #put rpr_slog_loc := rcons slog j ;; ret (Some (sg, c))
          | None => ret None
          end
      | None => ret None
      end
    } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      match x with
      | inl xy =>
          opr lpr_cqo (t, inr (inr (inl xy)))
            (λ r, ret (match r with inr (inr (inl h)) => inl h | _ => inl n0 end))
      | inr dc =>
          opr lpr_cqo (t, inr (inr (inr dc)))
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
          - eapply valid_opr; first by rewrite /lpr_cqo; fmap_solve.
            move=> r; apply valid_ret.
          - eapply valid_opr; first by rewrite /lpr_cqo; fmap_solve.
            move=> r; apply valid_ret. } }
      { (* LSIGN *)
        intro j.
        eapply valid_getr; first by fmap_solve. move=> slog.
        eapply valid_assertD => _.
        eapply valid_getr; first by fmap_solve. move=> tgts.
        case: (getm tgts j) => [[t0 [[[sg md0] copt] ofs]]|]; last by apply valid_ret.
        case: copt => [c|]; last by apply valid_ret.
        eapply valid_putr; first by fmap_solve. apply valid_ret. } }
    { (* LCHECK *)
      intros [j mw].
      eapply valid_getr; first by fmap_solve. move=> revealed.
      case: revealed; last first.
      { (* else: pre-commitment PCHECK gadget *)
        eapply valid_opr; first by rewrite /lpr_cko; fmap_solve.
        move=> ans; apply valid_ret. }
      eapply valid_getr; first by fmap_solve. move=> tgts.
      case: (getm tgts j) => [[t0 [[[sg md0] copt] ofs]]|]; last by apply valid_ret.
      eapply valid_getr; first by fmap_solve. move=> ppo.
      eapply valid_bind.
        case: ppo => [pp|]; first by apply valid_ret.
        eapply valid_bind; first by eapply valid_scheme, prog_valid.
        move=> pp; eapply valid_putr; first by fmap_solve.
        apply valid_ret.
      move=> pp.
      case: (lpr_pd pp t0 sg md0 j mw) => [[jc x]|]; last by apply valid_ret.
      case: ifP => _.
      - eapply valid_opr; first by rewrite /lpr_cko; fmap_solve.
        move=> ans; apply valid_ret.
      - apply valid_ret. } }
  { (* LGETPP *)
    intro u.
    eapply valid_opr; first by rewrite /lpr_gpo; fmap_solve.
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
    eapply valid_opr; first by rewrite /lpr_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> _.
  eapply valid_bind; first exact: lpr_grind_valid. move=> hs.
  eapply valid_getr; first by fmap_solve. move=> ofs.
  eapply valid_bind; first exact: lpr_chains_valid. move=> [sg ends].
  eapply valid_bind.
    eapply valid_opr; first by rewrite /lpr_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> root.
  eapply valid_putr; first by fmap_solve.
  eapply valid_getr; first by fmap_solve. move=> tgts.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve. apply valid_ret. }
Defined.

Check (R_cpre_leaf : package IMP IKM).
Check (fun (B : nom_package) => B ∘ R_cpre_leaf).

(* ================================================================== *)
(** ** SM-PRE location shorthands + resolve equations for the linked
    oracle bodies (computed once; mirror WOTSC/ChainHop's [resolve_pr_*]). *)

Local Notation Spp := (pre_pp_loc TFl).
Local Notation Stg := (pre_tgts_loc TFl).
Local Notation Stw := (pre_tws_loc TFl).
Local Notation Srv := pre_rev_loc.

Local Notation SMB b := (SMPRE_game TFl CFl_leaf q2 b).

Lemma resolve_lpr_cq (b : bool) (t : tc_T CFl_leaf) (x : tc_M CFl_leaf) :
  resolve (SMB b) lpr_cqo (t, x) =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   ret (tc_eval CFl_leaf pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lpr_pq (b : bool) (t : th_T TFl) :
  resolve (SMB b) lpr_pqo t =
  (revealed ← get Srv ;;
   #assert ~~ revealed ;;
   tws ← get Stw ;;
   #assert (size tws < q2)%N ;;
   #assert (t \notin tws) ;;
   x ← dN ;;
   tgts ← get Stg ;;
   #put Stg := setm tgts (size tws) (t, x) ;;
   #put Stw := rcons tws t ;;
   ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   ret (th_eval TFl pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lpr_gp (b : bool) (u : unit) :
  resolve (SMB b) lpr_gpo u =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   #put Srv := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lpr_ck (j : nat) (x : th_M TFl) :
  resolve (SMB true) lpr_cko (j, x) =
  (revealed ← get Srv ;;
   #assert revealed ;;
   tgts ← get Stg ;;
   match getm tgts j with
   | Some (t0, x0) =>
       ppo ← get Spp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
            end ;;
       ret (th_eval TFl pp t0 x == th_eval TFl pp t0 x0)%B
   | None => ret false
   end).
Proof. by simplify_linking. Qed.

Lemma resolve_lpr_ck_false (j : nat) (x : th_M TFl) :
  resolve (SMB false) lpr_cko (j, x) = ret false.
Proof. by simplify_linking. Qed.

(** Conversion bridges: the (P)COLLQ answer at a canonical tweak, after the
    loop's projection, IS the scheme's function (canonical tweaks compute). *)
Lemma lpr_collq_H_E (pp : PP) (zi : nat * nat) (md : D) (c : nat) :
  (if tc_eval CFl_leaf pp (encode_adrs (wotsc_grind_adrs zi)) (inr (inr (inr (md, c))))
      is inr (inr (inr h)) then h else 0)
  = Hgrind pp (wotsc_grind_adrs zi) (md, c).
Proof. by rewrite /tc_eval /CFl_leaf decode_tweakK. Qed.

Lemma lpr_collq_F_E (pp : PP) (zi : nat * nat) (i k : nat) (x : N) :
  (if tc_eval CFl_leaf pp (encode_adrs (wotsc_chain_adrs zi i k)) (inl x)
      is inl y then y else x)
  = F pp (wotsc_chain_adrs zi i k) x.
Proof. by rewrite /tc_eval /CFl_leaf decode_tweakK. Qed.

Lemma lpr_collq_Tl_E (pp : PP) (zi : nat * nat) (ends : seq N) :
  (match tc_eval CFl_leaf pp (encode_adrs (wotsc_pk_adrs zi)) (inr (inl ends))
     with inr (inl y) => y | _ => n0 end)
  = Tl pp (wotsc_pk_adrs zi) ends.
Proof. by rewrite /tc_eval /CFl_leaf decode_tweakK. Qed.

(** [th_eval TFl] at a canonical chain tweak is the wrapped chain hash. *)
Lemma th_eval_lF (pp : PP) (zi : nat * nat) (i k : nat) (x : N) :
  th_eval TFl pp (encode_adrs (wotsc_chain_adrs zi i k)) x
  = lF zi pp (i, k) x.
Proof. by case: zi => z i0; rewrite /th_eval /TFl /= decode_tweakK. Qed.

(** The picked grinding result on the honest answer list = the scheme's
    [find_ctr] (identical to Leaf2Compress's [lcp_*_E]). *)
Lemma lpr_zip_filter (f : nat -> nat) (P : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | P ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | P (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (P (f c)) => /=; [|exact: IH].
Qed.

Lemma lpr_pick_map (pp : PP) (zi : nat * nat) (md : D) :
  lpr_pick [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = omap (fun c => (c, Hgrind pp (wotsc_grind_adrs zi) (md, c)))
         (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md).
Proof.
rewrite /lpr_pick lpr_zip_filter /find_ctr.
have hf :
  [seq c <- iota 0 c_max
   | @grind_prp w l S_wn (Hgrind pp (wotsc_grind_adrs zi) (md, c))]
  = [seq c <- iota 0 c_max | good_ctr PP D Hgrind S_wn zi.1 zi.2 pp md c].
  by apply: eq_filter => c;
     rewrite /grind_prp /good_ctr /valid_digest /digest_of.
by rewrite hf.
Qed.

Lemma lpr_digit_E (pp : PP) (zi : nat * nat) (md : D) :
  lpr_digit [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = l_rrdig zi pp md.
Proof.
rewrite /lpr_digit /l_rrdig lpr_pick_map.
by case: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md) => [c|].
Qed.

Lemma lpr_copt_E (pp : PP) (zi : nat * nat) (md : D) :
  omap fst (lpr_pick [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- iota 0 c_max])
  = find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md.
Proof.
by rewrite lpr_pick_map; case: (find_ctr _ _ _ _ _ _ _ _ _) => [c|].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The CHAIN-PRE sub-bound (ladder step Glmid3 -> G1l'). *)

Local Notation GM3 := (Glmid3 PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation G1L := (G1l'  PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).

(* ================================================================== *)
(** ** F4 TERMINAL OBSTRUCTION: DEAD under the M1a static gate.

    CHAIN-PRE is the TERMINAL hop ([G1l'] = [ret false]), so the real perfect
    requires TOTALITY: [P_gm3S -> isSome (lpr_pd ...)] (route every
    [Glmid3]-win to SM-PRE).  The F4 obstruction (the grindable never-signed
    same-digit re-signature [mw = (md0,(sg,c))], non-routable because
    [fdv = rr_digit] advances no chain) is KILLED at the TOP of the ladder by
    the static gate: the regression witnesses are
    [Leaf2Games.obstruction_input_dead] / [flavourA_dead_gm3S] (probe D,
    superseding the old [obstruction_probe] here).  Terminal totality now
    HOLDS for all three leaf cases (WLOG_probe.v: [pop1_terminal_total] via
    the simple [grind_hitS] null forcing a digit difference,
    [oob_terminal_total] / [inb_virtual_terminal_total] via the virtual digit
    + [valid_not_allmax] under [Hdeg : S_wn != l*w.-1]) -- so
    [R_cpre_leaf_real] is now expected TRUE: the M1d milestone proves it, with
    [Hdeg] as a section hypothesis-of-the-ladder (ZeroChainHop precedent) and
    the PCHECK-wins step case-split [pre_decisionP] (pop-1) vs the zero-query
    preimage lemma (pop-2). *)

Lemma filter_ltnn (dd s : seq nat) :
  [seq i <- s | (nth 0%N dd i < nth 0%N dd i)%N] = [::].
Proof.
rewrite -[RHS](filter_pred0 s); apply: eq_in_filter => i _ /=.
by rewrite ltnn.
Qed.

(* ================================================================== *)
(** ** Banked cores (M1d, iteration 1): the LCHECK win/route bridge, the
    obstruction certification, and the two state-preserving pin loop specs.

    These are compile-checked (rocq MCP) and independent of the still-open
    relational assembly; they are the pieces the two perfects consume for the
    LCHECK routing and the COMMIT grinding loop. *)

(** The Glmid3 win IS the reduction's decision [lpr_v] at the stored find_ctr
    counter (the P_gm2_E analogue: verok/gate/ghit/compress/tcr all agree by
    conversion, with the tcr conjunct now BUILT-IN to [lpr_v]).  This is the
    LCHECK routing bridge: R answers [ret false] when [lpr_v = false]
    (regardless of [lpr_pd]), matching Glmid3, and routes to PCHECK exactly
    when [lpr_v = P_gm3S = true]. *)
Lemma P_gm3_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_gm3S PP N D F Tl Hgrind S_wn c_max pp t0 sg md0 j mw
  = lpr_v pp t0 sg md0
      (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0)
      j mw.
Proof.
rewrite /P_gm3S /lpr_v /grind_hitS /LeafKM.gateL /l_rrpkS /l_rrdigS /l_rrdig
        /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c.
by rewrite !andbA.
Qed.

(** OBSTRUCTION CERTIFICATION (restated, per M1d brief — the old
    [obstruction_probe] proved the REAL perfect FALSE pre-fix; it is now DEAD).
    The flavour-A input (a GRINDABLE, never-signed leaf re-submitting its own
    committed enc-pair [mw = (md0, (sg, c))] with [find_ctr md0 = Some c]) is
    killed at the TOP of the ladder by the static gate: BOTH the reduction's
    decision [lpr_v] (at the stored counter) and Glmid3's win [P_gm3S] are
    [false], so R_cpre_leaf answers [ret false] exactly as Glmid3 does -- no
    perfect-breaking disagreement.  (Supersedes the deleted counterexample;
    the underlying kill is [Leaf2Games.obstruction_input_dead] via [gateS].) *)
Lemma obstruction_probe (pp : PP) (t0 : adrs_sf_ch) (md0 : D)
    (c : nat) (sg : seq N) (j : nat) :
  find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0 = Some c ->
  lpr_v pp t0 sg md0 (Some c) j (md0, (sg, c)) = false /\
  P_gm3S PP N D F Tl Hgrind S_wn c_max pp t0 sg md0 j (md0, (sg, c)) = false.
Proof.
move=> hfc.
have hdead := obstruction_input_dead PP N D F Tl Hgrind S_wn c_max
                pp t0 md0 c sg j hfc.
split; last exact: hdead.
by rewrite (P_gm3_E pp t0 sg md0 j (md0, (sg, c))) hfc in hdead.
Qed.

(** State-preserving stepping of one linked PCOLLQ ([pp] pinned): the SM-PRE
    collection query touches no relational state, so this is generic over any
    precond [pre] that pins [Spp = Some pp] (ported from
    Leaf2ChainTCR.r_lctcollq_known at the PRE collection). *)
Lemma r_lpr_collq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CFl_leaf) (x : tc_M CFl_leaf) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : tc_N CFl_leaf -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CFl_leaf pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) lpr_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lpr_cq b t x).
eapply (r_get_bind_rhs Spp (Some pp)); first exact: hpp.
cbv beta iota.
exact: h.
Qed.

(** The grinding loop through PCOLLQ (state-preserving; the [find_ctr] answer
    list, generic over [pre]). *)
Lemma r_lpr_grind_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (md : D) (cs : seq nat) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (wotsc_grind_adrs zi) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lpr_grind zi md cs) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lpr_collq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite lpr_collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(* ================================================================== *)
(** ** Multi-instance offset machinery (M1d, iteration 2).

    The SM-PRE state is a FLATTENED concatenation of per-leaf chain-query
    blocks at running offsets.  [Q : seq (adrs_sf_ch * N)] is the flattened
    committed list (encoded chain tweak, HIDDEN input); [Stg] = [qmap_from 0 Q],
    [Stw] = [unzip1 Q].  The block precondition [pblk] carries [Q]; the COMMIT
    loop specs GROW it by one leaf's [lchain_block].  Freshness is the
    coordinate/chain-index disjunct [pfresh] (cross-leaf: distinct coordinate;
    within-leaf: strictly-smaller chain index). *)

Local Notation Lpp := (miw_pp_loc PP).
Local Notation Ltg := (@mkm_tgts_loc w l N D).
Local Notation Ltw := (@miw_tws_loc w l).
Local Notation Lrv := miw_rev_loc.
Local Notation Lsl := miw_slog_loc.

Local Notation FWl zi := (Fw PP N F zi.1 zi.2).
Local Notation cfWl zi := (HBS.Examples.FixedSumOTS.Scheme.chainf PP N (FWl zi)).
Local Notation wsigs zi := (sigs_of PP N (FWl zi)).
Local Notation wends zi := (ends_of PP N (FWl zi) w).
Local Notation lfind zi pp md :=
  (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md).
Local Notation lcompl zi pp ds sg := (complete_ends PP N F zi.1 zi.2 pp ds sg).

(** The SM-PRE query entry type (encoded chain tweak, hidden input). *)
Local Notation sqentry := ((adrs_sf_ch * N)%type).

(** Re-tag one abstract chain query into an encoded SM-PRE target entry. *)
Definition lwq (zi : nat * nat) (q : (nat * nat) * N) : sqentry :=
  (encode_adrs (wotsc_chain_adrs zi q.1.1 q.1.2), q.2).

(** One leaf's block: its [pre_queries] re-tagged. *)
Definition lchain_block (zi : nat * nat) (st : nat) (ds : seq nat)
    (us : seq N) : seq sqentry :=
  [seq lwq zi q | q <- pre_queries N st ds us].

Lemma lchain_block_cons (zi : nat * nat) st d ds u us :
  lchain_block zi st (d :: ds) (u :: us)
  = (if d is d'.+1 then [:: (encode_adrs (wotsc_chain_adrs zi st d'), u)]
     else [::]) ++ lchain_block zi st.+1 ds us.
Proof.
rewrite /lchain_block (pre_queries_cons N) map_cat.
by case: d => [|d'].
Qed.

(** Chain-index / coordinate of an encoded chain tweak. *)
Lemma adrs_chain_chtw (zi : nat * nat) (i k : nat) :
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  @adrs_chain l w (decode_tweak (encode_adrs (wotsc_chain_adrs zi i k))) = i.
Proof.
move=> hzi hi hk; rewrite decode_tweakK
  (wotsc_chain_adrsE l w zi i k hzi hi hk) /adrs_chain /=.
by rewrite Nat2Z.id.
Qed.

Lemma lcoord_chtw (zi : nat * nat) (i k : nat) :
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  lcoord (encode_adrs (wotsc_chain_adrs zi i k)) = zi.
Proof. exact: l2_lcoord_chain. Qed.

Lemma lcoord_pkadr (zi : nat * nat) :
  anchor_bounded zi -> lcoord (encode_adrs (wotsc_pk_adrs zi)) = zi.
Proof. exact: l2_lcoord_pk. Qed.

(** Freshness of the tweaks in [Q] w.r.t. leaf [zi]'s chains from [st] on. *)
Definition pfresh (zi : nat * nat) (st : nat) (Q : seq sqentry) : bool :=
  all (fun tw => ((lcoord tw != zi)
                 || (adrs_chain (decode_tweak tw) < st)%N)%B) (unzip1 Q).

Lemma pfresh_notin (zi : nat * nat) (st k : nat) (Q : seq sqentry) :
  anchor_bounded zi ->
  component_bounded l st ->
  component_bounded w.-1 k ->
  pfresh zi st Q -> encode_adrs (wotsc_chain_adrs zi st k) \notin unzip1 Q.
Proof.
move=> hzi hi hk /allP hf; apply/negP => hin.
by move: (hf _ hin); rewrite (lcoord_chtw zi st k hzi hi hk) eqxx
  (adrs_chain_chtw zi st k hzi hi hk) ltnn.
Qed.

Lemma pfresh_S (zi : nat * nat) (st : nat) (Q : seq sqentry) :
  pfresh zi st Q -> pfresh zi st.+1 Q.
Proof.
apply: sub_all => tw /orP[->//|hlt].
by rewrite (leq_trans hlt (leqnSn st)) orbT.
Qed.

Lemma pfresh_rcons (zi : nat * nat) (st k : nat) (Q : seq sqentry) (x : N) :
  anchor_bounded zi ->
  component_bounded l st ->
  component_bounded w.-1 k ->
  pfresh zi st Q ->
  pfresh zi st.+1 (rcons Q (encode_adrs (wotsc_chain_adrs zi st k), x)).
Proof.
move=> hzi hi hk hf; rewrite /pfresh /unzip1 map_rcons all_rcons.
rewrite [(_, x).1]/= (lcoord_chtw zi st k hzi hi hk) eqxx
  (adrs_chain_chtw zi st k hzi hi hk) ltnSn /=.
by move: (pfresh_S zi st Q hf).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside COMMIT). *)

Definition IGNP : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rpr_pp_loc ; rpr_tgts_loc ; rpr_tws_loc ; rpr_rev_loc ; rpr_slog_loc ;
        rpr_cnt_loc ; Spp ; Stg ; Stw ; Srv ].

(** Frame [Φ] insensitive to writes at the four SM-PRE locations (54-57)
    (PREHop's [pphi_stable]).  During COMMIT [Φ] freezes the game/R state. *)
Definition pphi_stable (Φ : precond) : Prop :=
  forall s0 s1 (ℓ : Location) (v : ℓ),
    (ℓ.1 \in [:: 54; 55; 56; 57])%N -> Φ (s0, s1) -> Φ (s0, set_heap s1 ℓ v).

Definition pblk (Φ : precond) (po : option PP) (rv : bool)
    (Q : seq sqentry) : precond :=
  λ '(s0, s1),
  [/\ Φ (s0, s1),
      get_heap s1 Spp = po,
      get_heap s1 Srv = rv,
      get_heap s1 Stw = unzip1 Q &
      get_heap s1 Stg = qmap_from 0 Q].

Arguments pblk : simpl never.

Lemma pblk_set_pp (Φ : precond) (pp : PP) rv Q s0 s1 :
  pphi_stable Φ -> pblk Φ None rv Q (s0, s1) ->
  pblk Φ (Some pp) rv Q (s0, set_heap s1 Spp (Some pp)).
Proof.
move=> hΦ [h0 h1 h2 h3 h4]; split.
- apply: (hΦ _ _ Spp); first by []. exact: h0.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

Lemma pblk_qupd (Φ : precond) (pp : PP) (Q : seq sqentry) (tw : adrs_sf_ch)
    (x : N) s0 s1 :
  pphi_stable Φ -> pblk Φ (Some pp) false Q (s0, s1) ->
  pblk Φ (Some pp) false (rcons Q (tw, x))
    (s0, set_heap (set_heap s1 Stg
            (setm (qmap_from 0 Q) (size (unzip1 Q)) (tw, x)))
          Stw (rcons (unzip1 Q) tw)).
Proof.
move=> hΦ [h0 h1 h2 h3 h4]; split.
- apply: (hΦ _ _ Stw); first by []. apply: (hΦ _ _ Stg); first by []. exact: h0.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq /unzip1 map_rcons.
- rewrite get_set_heap_neq // get_set_heap_eq.
  by rewrite qmap_from_rcons add0n /unzip1 size_map.
Qed.

Lemma pblk_set_rev (Φ : precond) (po : option PP) Q s0 s1 :
  pphi_stable Φ -> pblk Φ po false Q (s0, s1) ->
  pblk Φ po true Q (s0, set_heap s1 Srv true).
Proof.
move=> hΦ [h0 h1 h2 h3 h4]; split.
- apply: (hΦ _ _ Srv); first by []. exact: h0.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The COMMIT loop specs (walk / PQUERY / chains). *)

(** Walk to the chain end via PCOLLQ (state-preserving; generic [pre]). *)
Lemma r_lprwalk_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (post : postcond B B) :
  forall n i k (x : N) (c0 : raw_code B) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (chain (cfWl zi pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lpr_walk zi i k n x) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lpr_collq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite lpr_collq_F_E.
  exact: IH.
Qed.

(** Step one linked PQUERY: couple the game's [dN] root sample with the
    oracle's hidden one (mirror ChainHop [r_prquery]). *)
Lemma r_lprquery (b : bool) {B : choiceType} (Φ : precond) (pp : PP)
    (zi : nat * nat) (i k : nat) (Q : seq sqentry)
    (k0 k1 : N -> raw_code B) (post : postcond B B) :
  pphi_stable Φ ->
  (size Q < q2)%N ->
  encode_adrs (wotsc_chain_adrs zi i k) \notin unzip1 Q ->
  (forall x : N,
     ⊢ ⦃ λ '(s0, s1), pblk Φ (Some pp) false
            (rcons Q (encode_adrs (wotsc_chain_adrs zi i k), x)) (s0, s1) ⦄
        k0 x ≈ k1 (FWl zi pp (i, k) x) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk Φ (Some pp) false Q (s0, s1) ⦄
     bind dN k0
   ≈ bind (resolve (SMB b) lpr_pqo
             (encode_adrs (wotsc_chain_adrs zi i k))) k1 ⦃ post ⦄.
Proof.
move=> hΦ hbud hfresh h.
rewrite (resolve_lpr_pq b (encode_adrs (wotsc_chain_adrs zi i k))).
eapply (r_get_bind_rhs Srv false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs Stw (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> x; cbv beta.
eapply (r_get_bind_rhs Stg (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre;
     exact: (pblk_qupd Φ pp Q (encode_adrs (wotsc_chain_adrs zi i k)) x s0 s1 hΦ hpre).
eapply (r_get_bind_rhs Spp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
rewrite bind_ret_l bind_ret_l (th_eval_lF pp zi i k x).
exact: (h x).
Qed.

(** The per-chain induction: LHS re-rooted sampling, RHS linked PQUERY roots +
    PCOLLQ walk to ends; the committed [Q] grows by [lchain_block]. *)
Lemma r_lprchains_spec (b : bool) {B : choiceType} (Φ : precond) (pp : PP)
    (zi : nat * nat) (post : postcond B B) :
  pphi_stable Φ ->
  forall ds st (Q : seq sqentry)
         (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  anchor_bounded zi ->
  (st + size ds <= l)%N ->
  all (fun d => (d < w)%N) ds ->
  (size Q + npq ds <= q2)%N ->
  pfresh zi st Q ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), pblk Φ (Some pp) false
            (Q ++ lchain_block zi st ds us) (s0, s1) ⦄
        K0 (wsigs zi pp st ds us)
      ≈ K1 (wsigs zi pp st ds us, wends zi pp st ds (wsigs zi pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk Φ (Some pp) false Q (s0, s1) ⦄
     bind (sample_sig_roots PP N (FWl zi) dN pp st ds) K0
   ≈ bind (code_link (lpr_chains zi st ds) (SMB b)) K1 ⦃ post ⦄.
Proof.
move=> hΦ.
elim=> [|d ds IH] st Q K0 K1 hzi hst hds hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- move: hst => /=; rewrite addnS => hst2.
  have hstl : (st < l)%N := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : (st.+1 + size ds <= l)%N := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /= code_link_bind.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* d = 0 : both sides sample the root locally *)
    rewrite (code_link_scheme _ _ _ _ (prog_valid dN)) !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> u; cbv beta; rewrite !bind_assoc.
    rewrite (code_link_bind (lpr_walk zi st 0 (w.-1 - 0) u)) bind_assoc.
    eapply (r_lprwalk_spec b pp zi (pblk Φ (Some pp) false Q)).
      { by move=> s0 s1 [_ h' _ _ _]. }
    rewrite (code_link_bind (lpr_chains zi st.+1 ds)) bind_assoc.
    eapply IH => //.
    * exact: pfresh_S.
    * move=> us hus.
      move: (h (u :: us)); rewrite /= hus => /(_ erefl).
      by rewrite lchain_block_cons cat0s.
  + (* d = d'.+1 : the sigma PQUERY *)
    have hw0 : (0 < w)%N := leq_trans (ltn0Sn d') (ltnW hd0).
    have hdw1 : (d'.+1 <= w.-1)%N by rewrite -ltnS (prednK hw0).
    rewrite bind_assoc /= !bind_assoc.
    eapply r_lprquery => //.
    * by apply: leq_trans hbud; rewrite /npq /= addnS ltnS leq_addr.
    * apply: pfresh_notin => //; exact: component_bounded_lt.
    * move=> x; cbv beta; rewrite !bind_assoc /=.
      rewrite (code_link_bind (lpr_walk zi st d'.+1 (w.-1 - d'.+1) (FWl zi pp (st, d') x)))
              bind_assoc.
      eapply (r_lprwalk_spec b pp zi
                (pblk Φ (Some pp) false
                   (rcons Q (encode_adrs (wotsc_chain_adrs zi st d'), x)))).
        { by move=> s0 s1 [_ h' _ _ _]. }
      rewrite (code_link_bind (lpr_chains zi st.+1 ds)) bind_assoc.
      eapply IH => //.
      -- by move: hbud; rewrite size_rcons /npq /= addnS addSn.
      -- apply: pfresh_rcons => //; exact: component_bounded_lt.
      -- move=> us hus.
         move: (h (x :: us)); rewrite /= hus => /(_ erefl).
         by rewrite lchain_block_cons cat_rcons.
Qed.

Lemma wendsEl (zi : nat * nat) pp (ds : seq nat) (ys : seq N) :
  size ds = l -> wends zi pp 0 ds ys = lcompl zi pp ds ys.
Proof.
move=> h.
by rewrite (ends_of_from_sig PP N (FWl zi) l w pp ds ys h)
   (wcendsE PP N F zi.1 zi.2).
Qed.

(* ================================================================== *)
(** ** The flattened per-leaf query layer.

    [qflat pp 0 CS] is the SM-PRE committed query list; leaf [j]'s block
    [qblk pp j (nth ... CS j)] sits at offset [size (qflat pp 0 (take j CS))].
    [CS] is the per-leaf carrier: [((t, (sg, md)), us)] with [us] the HIDDEN
    PQUERY inputs. *)

Local Notation lrec := ((adrs_sf_ch * (('list N) * D)) * seq N)%type.

Definition dflt_lrec : lrec := (encode_adrs (wotsc_pk_adrs (0, 0)), ([::], d0), [::]).

(** One leaf's flattened block, at slot [j]. *)
Definition qblk (pp : PP) (j : nat) (r : lrec) : seq sqentry :=
  lchain_block (lcoord r.1.1) 0 (l_rrdigS (lcoord r.1.1) pp r.1.2.2 j) r.2.

Fixpoint qflat (pp : PP) (j : nat) (cs : seq lrec) : seq sqentry :=
  match cs with
  | [::] => [::]
  | r :: cs' => qblk pp j r ++ qflat pp j.+1 cs'
  end.

Lemma qflat_cat (pp : PP) (j : nat) (cs1 cs2 : seq lrec) :
  qflat pp j (cs1 ++ cs2) = qflat pp j cs1 ++ qflat pp (j + size cs1) cs2.
Proof.
elim: cs1 j => [|r cs1 IH] j /=; first by rewrite addn0.
by rewrite -catA IH addSnnS.
Qed.

Lemma qflat_rcons (pp : PP) (j : nat) (cs : seq lrec) (r : lrec) :
  qflat pp j (rcons cs r) = qflat pp j cs ++ qblk pp (j + size cs) r.
Proof. by rewrite -cats1 qflat_cat /= cats0. Qed.

(** [take]/[drop] split of the flatten at leaf [j] (offset-get support). *)
Lemma qflat_take_drop (pp : PP) (cs : seq lrec) (j : nat) :
  qflat pp 0 cs
  = qflat pp 0 (take j cs) ++ qflat pp (size (take j cs)) (drop j cs).
Proof.
by rewrite -{1}(cat_take_drop j cs) qflat_cat add0n.
Qed.

(* ================================================================== *)
(** ** The per-leaf-table relation and the top invariant. *)

(** [RPr pp CS ltg rtg]: the game table [ltg] and the reduction table [rtg]
    are the [CS]-indexed tables; each leaf's stored sig is the honest
    re-rooted [wsigs] of its hidden inputs at the slot-keyed digit. *)
Definition RPr (pp : PP) (CS : seq lrec)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch ×
             ((('list N × D) × 'option 'nat) × 'nat))}) : Prop :=
  [/\ (forall j, getm ltg j
         = (if (j < size CS)%N then Some (nth dflt_lrec CS j).1 else None)),
      (forall j, getm rtg j
         = (if (j < size CS)%N
            then Some ((nth dflt_lrec CS j).1.1,
                       (((nth dflt_lrec CS j).1.2,
                         lfind (lcoord (nth dflt_lrec CS j).1.1) pp
                               (nth dflt_lrec CS j).1.2.2),
                        size (qflat pp 0 (take j CS))))
            else None))
    & (forall j, (j < size CS)%N ->
         size (nth dflt_lrec CS j).2 = l /\
         (nth dflt_lrec CS j).1.2.1
           = wsigs (lcoord (nth dflt_lrec CS j).1.1) pp 0
               (l_rrdigS (lcoord (nth dflt_lrec CS j).1.1) pp
                  (nth dflt_lrec CS j).1.2.2 j)
               (nth dflt_lrec CS j).2)].

Lemma RPr_empty (pp : PP) : RPr pp [::] emptym emptym.
Proof. by split=> [j|j|j] //; rewrite emptymE. Qed.

(** Extend all tables at the common slot [size CS]. *)
Lemma RPr_qupd (pp : PP) (CS : seq lrec) ltg rtg
    (t : adrs_sf_ch) (sg : seq N) (md : D) (us : seq N) :
  RPr pp CS ltg rtg ->
  size us = l ->
  sg = wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size CS)) us ->
  RPr pp (rcons CS ((t, (sg, md)), us))
      (setm ltg (size CS) (t, (sg, md)))
      (setm rtg (size CS)
        (t, (((sg, md), lfind (lcoord t) pp md), size (qflat pp 0 CS)))).
Proof.
move=> [hl hr hw] hus hsg; split.
- move=> j; rewrite setmE size_rcons nth_rcons hl.
  case: (ltngtP j (size CS)) => hj.
  + by rewrite ltnS (ltnW hj).
  + by rewrite ltnS leqNgt hj.
  + by rewrite hj ltnSn.
- move=> j; rewrite setmE size_rcons nth_rcons hr.
  case: (ltngtP j (size CS)) => hj.
  + rewrite ltnS (ltnW hj) -cats1 takel_cat //; exact: ltnW.
  + by rewrite ltnS leqNgt hj.
  + by rewrite hj ltnSn -cats1 take_size_cat.
- move=> j; rewrite size_rcons nth_rcons ltnS leq_eqVlt => /orP[/eqP hj|hj].
  + rewrite hj ltnn eqxx hus; split=> //; exact: hsg.
  + rewrite hj; exact: (hw j hj).
Qed.

(** The top-level relation on all 15 tracked locations. *)
Definition RP
    (lpp : option PP) (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (ltw : seq adrs_sf_ch) (lrv : bool) (lsl : seq nat)
    (rpp : option PP)
    (rtg : {fmap nat -> (adrs_sf_ch ×
             ((('list N × D) × 'option 'nat) × 'nat))})
    (rtw : seq adrs_sf_ch) (rrv : bool) (rsl : seq nat) (rcnt : nat)
    (spp : option PP) (stg : {fmap nat -> sqentry})
    (stw : seq adrs_sf_ch) (srv : bool) : Prop :=
  [/\ rtw = ltw, rrv = lrv, rsl = lsl, rpp = (if lrv then lpp else None)
    & [/\ spp = lpp, srv = lrv
      & match lpp with
        | None => [/\ ltg = emptym, rtg = emptym, stg = emptym
                    & [/\ stw = [::], rcnt = 0%N, ltw = [::] & lrv = false]]
        | Some pp => exists CS,
            [/\ RPr pp CS ltg rtg,
                ltw = [seq r.1.1 | r <- CS],
                stg = qmap_from 0 (qflat pp 0 CS),
                stw = unzip1 (qflat pp 0 CS)
              & rcnt = size (qflat pp 0 CS)]
        end]].

Definition pr_inv : precond :=
  heap_ignore IGNP
  ⋊ rel_app [:: (lhs, Lpp) ; (lhs, Ltg) ; (lhs, Ltw) ; (lhs, Lrv) ; (lhs, Lsl) ;
                (rhs, rpr_pp_loc) ; (rhs, rpr_tgts_loc) ; (rhs, rpr_tws_loc) ;
                (rhs, rpr_rev_loc) ; (rhs, rpr_slog_loc) ; (rhs, rpr_cnt_loc) ;
                (rhs, Spp) ; (rhs, Stg) ; (rhs, Stw) ; (rhs, Srv) ] RP.

Arguments pr_inv : simpl never.

Lemma pr_invE s0 s1 :
  pr_inv (s0, s1) ->
  heap_ignore IGNP (s0, s1) /\
  RP (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rpr_pp_loc) (get_heap s1 rpr_tgts_loc) (get_heap s1 rpr_tws_loc)
     (get_heap s1 rpr_rev_loc) (get_heap s1 rpr_slog_loc) (get_heap s1 rpr_cnt_loc)
     (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv).
Proof. by move=> [h1 h2]; split. Qed.

Lemma pr_invI s0 s1 :
  heap_ignore IGNP (s0, s1) ->
  RP (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rpr_pp_loc) (get_heap s1 rpr_tgts_loc) (get_heap s1 rpr_tws_loc)
     (get_heap s1 rpr_rev_loc) (get_heap s1 rpr_slog_loc) (get_heap s1 rpr_cnt_loc)
     (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv) ->
  pr_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

Definition pr_invL (pp : PP) : precond :=
  λ '(s0, s1), pr_inv (s0, s1) /\ get_heap s0 Lpp = Some pp.
Arguments pr_invL : simpl never.

(** Pin [pp] on both [Lpp] and [Spp] (from [None]); preserves the invariant. *)
Lemma pr_inv_pin (pp : PP) s0 s1 :
  pr_inv (s0, s1) -> get_heap s0 Lpp = None ->
  pr_inv (set_heap s0 Lpp (Some pp), set_heap s1 Spp (Some pp)).
Proof.
move=> hinv hL.
case/pr_invE: hinv => hign hRP.
move: hRP; rewrite hL => -[hrtw hrrv hrsl hrpp [hspp hsrv hm]].
case: hm => hltg hrtg hstg [hstw hcnt hltw hlrv].
apply: pr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RP; get_heap_simpl.
  split; [exact: hrtw | exact: hrrv | exact: hrsl
         | by rewrite hlrv; move: hrpp; rewrite hlrv |].
  split; [by [] | exact: hsrv |].
  exists [::]; split.
  + by rewrite hltg hrtg; exact: RPr_empty.
  + by rewrite hltw.
  + by rewrite hstg.
  + by rewrite hstw.
  + by rewrite hcnt.
Qed.

(** GETPP reveal (rev false -> true; R copies pp; SM-PRE Srv true). *)
Lemma pr_inv_reveal (pp : PP) s0 s1 :
  pr_inv (s0, s1) -> get_heap s0 Lpp = Some pp ->
  pr_inv (set_heap s0 Lrv true,
          set_heap (set_heap (set_heap s1 Srv true) rpr_pp_loc (Some pp))
            rpr_rev_loc true).
Proof.
move=> hinv hL.
case/pr_invE: hinv => hign hRP.
move: hRP; rewrite hL => -[hrtw hrrv hrsl hrpp [hspp hsrv hm]].
apply: pr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RP; get_heap_simpl.
  rewrite hL hrtw hrsl hspp.
  case: hm => CS [hRPr hltw hstg hstw hcnt].
  split=> //; split=> //.
  by exists CS; split.
Qed.

(** LSIGN: set [Lsl] and [rpr_slog] to the same value; preserves invariant. *)
Lemma pr_inv_setsl (vw : seq nat) s0 s1 :
  pr_inv (s0, s1) ->
  pr_inv (set_heap s0 Lsl vw, set_heap s1 rpr_slog_loc vw).
Proof.
move=> hinv.
case/pr_invE: hinv => hign hRP.
apply: pr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- move: hRP; rewrite /RP; get_heap_simpl.
  by move=> -[hrtw hrrv _ hrpp hrest]; split.
Qed.

Lemma bind_put_ret {A B : choiceType} (ℓ : Location) (v : ℓ) (a : A)
    (k : A -> raw_code B) :
  bind (#put ℓ := v ;; ret a) k = (#put ℓ := v ;; k a).
Proof. by []. Qed.

Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

(** Couple the two lazy [pp] reads (game [Lpp] vs SM-PRE [Spp]); land per-[pp]
    under the invariant with [Lpp] pinned (mirror Leaf2Compress [r_pp2]). *)
Lemma r_pp2 {B : choiceType} (k0 k1 : PP -> raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), pr_invL pp (s0, s1) ⦄
                 k0 pp ≈ k1 pp ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pr_inv (s0, s1) ⦄
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
    case/pr_invE: hinv => _ [_ _ _ _ [hsp _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hsp hr0. }
move=> e; subst spp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv hr0] hr1].
  rewrite /rem_inv /= in hr0.
  by rewrite /pr_invL /=; split; [exact: hinv | exact: hr0].
- cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite !bind_put_ret.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [[[hinv hr0] hr1] e0]] e1]].
  rewrite /rem_inv /= in hr0.
  subst s0 s1; rewrite /pr_invL /=; split.
  + exact: (pr_inv_pin pp s0' s1' hinv hr0).
  + by rewrite get_set_heap_eq.
Qed.

(* ================================================================== *)
(** ** Generic RHS re-association helpers (mirror Leaf2ChainTCR). *)

Lemma bind_getr {A B : choiceType} (ℓ : Location) (f : ℓ -> raw_code A)
    (k : A -> raw_code B) :
  bind (x ← get ℓ ;; f x) k = (x ← get ℓ ;; bind (f x) k).
Proof. by []. Qed.

Lemma push_Spp {A B : choiceType} (a : PP -> A) (k : A -> raw_code B) :
  bind (ppo ← get Spp ;;
        pp ← match ppo with
             | Some pp => ret pp
             | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
             end ;; ret (a pp)) k
  = (ppo ← get Spp ;;
     pp ← match ppo with
          | Some pp => ret pp
          | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
          end ;; k (a pp)).
Proof.
rewrite bind_getr. setoid_rewrite bind_assoc. exact: erefl.
Qed.

Lemma collq_rhs_E {B : choiceType} (a : PP -> tc_N CFl_leaf)
    (k : tc_N CFl_leaf -> raw_code B) :
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

#[local] Arguments resolve : simpl never.
#[local] Arguments SMPRE_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments lpr_pick : simpl never.
#[local] Arguments l_rrdig : simpl never.
#[local] Arguments tcr_decision : simpl never.
#[local] Arguments pre_decision : simpl never.
#[local] Arguments pre_queries : simpl never.

(** [code_link] one-step commuters (definitional), used to pull RHS
    gets/puts OUT of [code_link] while keeping the tail folded, so
    [code_link_assertD] keeps matching across an interleaved get. *)
Lemma cl_getr {A : choiceType} (ℓ : Location) (kk : ℓ -> raw_code A)
    (g : raw_package) :
  code_link (getr ℓ kk) g = getr ℓ (fun xx => code_link (kk xx) g).
Proof. by []. Qed.

Lemma cl_putr {A : choiceType} (ℓ : Location) (v : ℓ) (kk : raw_code A)
    (g : raw_package) :
  code_link (putr ℓ v kk) g = putr ℓ v (code_link kk g).
Proof. by []. Qed.

(* ================================================================== *)
(** ** COMMIT machinery: the frozen frame [cfrm], its [pphi_stable], and
    the digit / size bridges consumed by the COMMIT-tail assembly. *)

(** The COMMIT frame: heap_ignore + FROZEN game side + FROZEN R non-SM-PRE
    side + the per-leaf table relation [RPr].  During the COMMIT loops only
    the four SM-PRE locations (54-57) move; [cfrm] freezes everything else. *)
Definition cfrm (pp : PP) (CS : seq lrec) (lsl : seq nat)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch ×
             ((('list N × D) × 'option 'nat) × 'nat))}) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNP (s0, s1),
      [/\ get_heap s0 Lpp = Some pp, get_heap s0 Lrv = false,
          get_heap s0 Lsl = lsl, get_heap s0 Ltw = [seq r.1.1 | r <- CS]
        & get_heap s0 Ltg = ltg],
      [/\ get_heap s1 rpr_pp_loc = None, get_heap s1 rpr_rev_loc = false,
          get_heap s1 rpr_slog_loc = lsl,
          get_heap s1 rpr_tws_loc = [seq r.1.1 | r <- CS]
        & get_heap s1 rpr_tgts_loc = rtg
          /\ get_heap s1 rpr_cnt_loc = size (qflat pp 0 CS)]
    & RPr pp CS ltg rtg].

Arguments cfrm : simpl never.

Lemma pphi_stable_cfrm pp CS lsl ltg rtg :
  pphi_stable (cfrm pp CS lsl ltg rtg).
Proof.
move=> s0 s1 ℓ v hin [hign hG hR hRPr].
have hne : forall L : Location, L.1 \notin [:: 54; 55; 56; 57] ->
    get_heap (set_heap s1 ℓ v) L = get_heap s1 L.
  move=> L hL; rewrite get_set_heap_neq //.
  by apply/eqP => e; move: hL; rewrite e => /negP; apply; exact: hin.
split.
- apply: heap_ignore_set_r; last exact: hign.
  by move: hin; rewrite !inE => /or4P[] /eqP ->; rewrite mem_domm.
- exact: hG.
- case: hR => h1 h2 h3 h4 [h5 h6]; split; try by rewrite hne //.
  by split; rewrite hne //.
- exact: hRPr.
Qed.

(** Digit bridges: the game static digit [rr_digitS], the reduction's
    slot digit [l_rrdigS] and the grind-answer digit [lpr_digitS] agree. *)
Lemma rr_digitSE (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat) :
  rr_digitS PP D Hgrind S_wn c_max pp t md j
  = l_rrdigS (lcoord t) pp md j.
Proof. by rewrite /rr_digitS /l_rrdigS /rr_digit /l_rrdig. Qed.

Lemma lpr_digitSE (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat) :
  lpr_digitS j [seq Hgrind pp (wotsc_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max]
  = l_rrdigS (lcoord t) pp md j.
Proof.
by rewrite /lpr_digitS /l_rrdigS lpr_digit_E.
Qed.

Lemma size_l_rrdigS (zi : nat * nat) (pp : PP) (md : D) (j : nat) :
  size (l_rrdigS zi pp md j) = l.
Proof.
rewrite /l_rrdigS /l_rrdig;
  case: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md) => [c|];
  [exact: (size_digest_of PP D Hgrind zi.1 zi.2 pp md c) | exact: size_nseq].
Qed.

Lemma wf_l_rrdigS (hw : (0 < w)%N) (zi : nat * nat) (pp : PP)
    (md : D) (j : nat) :
  wf_digits w (l_rrdigS zi pp md j).
Proof.
rewrite /l_rrdigS /l_rrdig.
case E: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md) => [c|].
- by move: (find_ctr_good PP D Hgrind S_wn c_max zi.1 zi.2 pp md c E)
    => /andP[h1 _].
- by rewrite /wf_digits all_nseq ltn_predL hw orbT.
Qed.

Lemma lnpqE (ds : seq nat) : lnpq ds = npq ds.
Proof. by []. Qed.

Lemma size_lchain_block (zi : nat * nat) (st : nat) (ds : seq nat) (us : seq N) :
  size us = size ds -> size (lchain_block zi st ds us) = npq ds.
Proof.
elim: ds st us => [|d ds IH] st [|u us] //= [hsz].
rewrite lchain_block_cons size_cat (IH st.+1 us hsz) /npq /=.
by case: d => [|d'] /=; rewrite ?add0n ?add1n.
Qed.

Lemma all_lcoord_lchain_block (zi : nat * nat) (st : nat)
    (ds : seq nat) (us : seq N) :
  anchor_bounded zi ->
  (st + size ds <= l)%N ->
  all (fun d => (d < w)%N) ds ->
  all (fun tw => lcoord tw == zi) (unzip1 (lchain_block zi st ds us)).
Proof.
elim: ds st us => [|d ds IH] st [|u us] //= hzi hst hds.
move: hst => /=; rewrite addnS => hst2.
have hstl : (st < l)%N := leq_ltn_trans (leq_addr _ _) hst2.
have hstds : (st.+1 + size ds <= l)%N := hst2.
move: hds => /= /andP[hd hds].
rewrite lchain_block_cons /unzip1 map_cat all_cat.
case: d hd => [|d'] hd /=.
- exact: (IH st.+1 us hzi hstds hds).
- have hw0 : (0 < w)%N := leq_trans (ltn0Sn d') (ltnW hd).
  have hdw : (d' < w.-1)%N by rewrite -ltnS (prednK hw0).
  rewrite (lcoord_chtw zi st d' hzi (component_bounded_lt l st hstl)
    (component_bounded_lt w.-1 d' hdw)) eqxx.
  exact: (IH st.+1 us hzi hstds hds).
Qed.

(* ------------------------------------------------------------------ *)
(** ** COMMIT budget + cross-leaf freshness for the flattened query list. *)

Lemma size_qblk_le (pp : PP) (j : nat) (r : lrec) :
  size r.2 = l -> (size (qblk pp j r) <= l)%N.
Proof.
move=> hr; rewrite /qblk size_lchain_block; last by rewrite hr size_l_rrdigS.
exact: (npq_le l _ (size_l_rrdigS (lcoord r.1.1) pp r.1.2.2 j)).
Qed.

Lemma size_qflat_le (pp : PP) (CS : seq lrec) :
  (forall j, (j < size CS)%N -> size (nth dflt_lrec CS j).2 = l) ->
  (size (qflat pp 0 CS) <= size CS * l)%N.
Proof.
move=> hCS.
suff gen : forall CS0 st, (forall j, (j < size CS0)%N -> size (nth dflt_lrec CS0 j).2 = l) ->
             (size (qflat pp st CS0) <= size CS0 * l)%N by apply: gen.
elim=> [|r CS0 IH] st hs0 //=.
rewrite size_cat mulSn; apply: leq_add.
- by apply: size_qblk_le; apply: (hs0 0%N).
- by apply: IH => j hj; apply: (hs0 j.+1).
Qed.

Lemma pfresh_coord (hw : (0 < w)%N) (pp : PP) (zi : nat * nat) (CS : seq lrec) :
  (forall r, r \in CS -> lcoord r.1.1 != zi) ->
  forall stq st, pfresh zi st (qflat pp stq CS).
Proof.
elim: CS => [|r CS IH] hco stq st.
- by rewrite /pfresh /qflat.
- rewrite /= /pfresh /unzip1 map_cat all_cat; apply/andP; split.
  + have hsize : (0 + size (l_rrdigS (lcoord r.1.1) pp r.1.2.2 stq) <= l)%N
      by rewrite add0n size_l_rrdigS.
    have hall := all_lcoord_lchain_block (lcoord r.1.1) 0
      (l_rrdigS (lcoord r.1.1) pp r.1.2.2 stq) r.2
      (l2_lcoord_bounded r.1.1) hsize
      (wf_l_rrdigS hw (lcoord r.1.1) pp r.1.2.2 stq).
    rewrite /qblk in hall.
    apply: sub_all hall => tw /eqP ->; apply/orP; left.
    exact: (hco r (mem_head _ _)).
  + by apply: (IH _ stq.+1 st) => r0 hr0; apply: hco; rewrite in_cons hr0 orbT.
Qed.

Lemma coord_of_gtw (t0 : adrs_sf_ch) (CS : seq lrec) :
  gtw_of t0 \notin [seq gtw_of x | x <- [seq r0.1.1 | r0 <- CS]] ->
  forall r, r \in CS -> lcoord r.1.1 != lcoord t0.
Proof.
rewrite -map_comp => hni r hr; apply/negP => /eqP e.
move/negP: hni; apply; apply/mapP; exists r => //=.
by rewrite e.
Qed.

Lemma pr_inv_cblk (pp : PP) s0 s1 :
  pr_inv (s0, s1) -> get_heap s0 Lpp = Some pp -> get_heap s0 Lrv = false ->
  exists CS,
    [/\ pblk (cfrm pp CS (get_heap s0 Lsl) (get_heap s0 Ltg) (get_heap s1 rpr_tgts_loc))
             (Some pp) false (qflat pp 0 CS) (s0, s1),
        get_heap s0 Ltw = [seq r.1.1 | r <- CS]
      & RPr pp CS (get_heap s0 Ltg) (get_heap s1 rpr_tgts_loc)].
Proof.
move=> hinv hLpp hLrv.
case/pr_invE: hinv => hign hRP.
move: hRP; rewrite hLpp hLrv => -[hrtw hrrv hrsl hrpp [hspp hsrv hm]].
case: hm => CS [hRPr hltw hstg hstw hcnt].
exists CS; split.
- rewrite /pblk; split.
  + rewrite /cfrm; split.
    * exact: hign.
    * by split; rewrite ?hLpp ?hLrv.
    * by split; rewrite ?hrpp ?hrrv ?hrsl -?hltw ?hrtw //; split.
    * exact: hRPr.
  + by rewrite hspp.
  + by rewrite hsrv.
  + by rewrite hstw.
  + by rewrite hstg.
- exact: hltw.
- exact: hRPr.
Qed.

(* ================================================================== *)
(** ** Terminal crux (M1d, iteration 2): offset-read + the multi-leaf
    SM-PRE(F) totality/win.  Banked (Qed) above the perfects; consumed by
    the LCHECK-true terminal goal. *)

Lemma qnth_cat_l {X : Type} (A B : seq X) i :
  (i < size A)%N -> qnth (A ++ B) i = qnth A i.
Proof.
move=> hi; rewrite /qnth drop_cat hi.
have hsz : (0 < size (drop i A))%N by rewrite size_drop subn_gt0.
by case: (drop i A) hsz => [|a s].
Qed.

Lemma qnth_cat_r {X : Type} (A B : seq X) i :
  qnth (A ++ B) (size A + i) = qnth B i.
Proof. by rewrite /qnth drop_cat ltnNge leq_addr /= addKn. Qed.

(** THE multi-leaf SM-PRE(F) totality/win at leaf coordinate [zi] (the
    coordinate-general merge of FixedSumOTS [classify_some]+[pre_decisionP],
    with the strictly-lower coordinate SUPPLIED — pop-1 via [eq_sumn_exists_lt],
    pop-2 via [valid_not_allmax]; the honest digit [dds] is NOT required valid,
    so it covers the virtual all-max digit).  [tcr_decision = None] excludes the
    ChainColl branch, so [pre_decision] fires with the F-preimage that wins
    PCHECK. *)
Lemma l2_pre_win (zi : nat * nat) (pp : PP) (dds : seq nat)
    (us sgstar : seq N) (mstar : seq nat) :
  size dds = l -> all (fun d => (d < w)%N) dds -> size us = l ->
  valid_msg l w S_wn mstar ->
  (size sgstar == l)%B ->
  has (fun i => (nth 0 mstar i < nth 0 dds i)%N) (iota 0 l) ->
  lcompl zi pp mstar sgstar = lcompl zi pp dds (wsigs zi pp 0 dds us) ->
  tcr_decision PP N (FWl zi) l w pp dds mstar (wsigs zi pp 0 dds us) sgstar = None ->
  exists jc x t u,
    [/\ pre_decision PP N (FWl zi) l w pp dds mstar (wsigs zi pp 0 dds us) sgstar
        = Some (jc, x),
        qnth (pre_queries N 0 dds us) jc = Some (t, u)
      & FWl zi pp t x = FWl zi pp t u].
Proof.
move=> hddsz hddw hus hvmf hsgsz hhas hends hnone.
have hmsz : size mstar = l by case/and3P: hvmf => /eqP.
have hussz : size us = size dds by rewrite hus hddsz.
have hsgs : size (wsigs zi pp 0 dds us) = l.
  by rewrite (size_sigs_of PP N (FWl zi) pp 0 dds us hussz) hddsz.
(* forged completion = honest completion ⇒ the same ends_from_sig public key *)
have hEE : ends_from_sig PP N (FWl zi) l w pp dds (wsigs zi pp 0 dds us)
         = ends_from_sig PP N (FWl zi) l w pp mstar sgstar.
  rewrite -(ends_of_from_sig PP N (FWl zi) l w pp dds (wsigs zi pp 0 dds us) hddsz).
  rewrite -(ends_of_from_sig PP N (FWl zi) l w pp mstar sgstar hmsz).
  rewrite (wendsEl zi pp dds (wsigs zi pp 0 dds us) hddsz)
          (wendsEl zi pp mstar sgstar hmsz).
  exact: esym hends.
have hAC : forall (n st : nat) (ds0 : seq nat) (ys : seq N),
  all (fun q => chain_check PP N (FWl zi) w pp q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st n)
           (zip ds0 (zip ys
              [seq chain (cfWl zi pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
              | q <- zip (iota st n) (zip ds0 ys)]))).
  elim=> [|n IH] st ds0 ys; first by case: ds0 => [|d ds0]; case: ys => [|y ys].
  case: ds0 => [|d ds0]; case: ys => [|y ys] => //=.
  apply/andP; split; last exact: IH.
  by rewrite /HBS.Examples.FixedSumOTS.Scheme.chain_check eqxx.
have hverify : HBS.Examples.FixedSumOTS.Scheme.verify_sig PP N (FWl zi) l w S_wn pp
    (ends_from_sig PP N (FWl zi) l w pp dds (wsigs zi pp 0 dds us)) mstar sgstar.
  rewrite hEE /HBS.Examples.FixedSumOTS.Scheme.verify_sig hvmf hsgsz /= /ends_from_sig.
  exact: (hAC l 0 mstar sgstar).
(* now the shared ohead coordinate drives both totality and the win *)
rewrite /pre_decision; move: hnone; rewrite /tcr_decision.
case E1: (ohead _) => [i|]; last first.
  by move=> _; move: hhas E1; rewrite has_filter; case: (filter _ _) => [|a s].
have hifacts : i \in [seq i0 <- iota 0 l | (nth 0 mstar i0 < nth 0 dds i0)%N].
  by move: E1; case: (filter _ _) => //= a s [<-]; rewrite in_cons eqxx.
move: hifacts; rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
have [si E2] : exists si, qnth (wsigs zi pp 0 dds us) i = Some si.
  by apply: qnth_some; rewrite hsgs.
have [si' E3] : exists si', qnth sgstar i = Some si'.
  by apply: qnth_some; rewrite (eqP hsgsz).
rewrite E2 E3.
have hdw : (nth 0 dds i < w)%N by apply: (allP hddw); rewrite mem_nth // hddsz.
have hszends := size_ends_from_sig PP N (FWl zi) l w pp dds
                  (wsigs zi pp 0 dds us) hddsz hsgs.
have h1 := verify_sig_nth PP N (FWl zi) l w S_wn pp _ mstar sgstar si' i
             hverify hszends hil.
rewrite (ends_from_sig_nth PP N (FWl zi) l w pp dds (wsigs zi pp 0 dds us)
           si' i hddsz hsgs hil) in h1.
rewrite (qnth_nth si' _ _ _ E3) (qnth_nth si' _ _ _ E2) in h1.
have hfc := forgery_cases PP N (FWl zi) w pp i (nth 0 dds i) si (nth 0 mstar i) si'
              hlt hdw h1.
move: hfc; case E4: (chain_extract (cfWl zi pp i) si'
                       (nth 0 mstar i) si (nth 0 dds i) w.-1) => [k u v|] hfc.
  by [].
move=> _.
have hpim := forgery_pre_preimage PP N (FWl zi) pp i (nth 0 dds i) si si'
               (nth 0 mstar i) hlt hfc.
have hilm : (i < size dds)%N by rewrite hddsz.
have [ui hui] : exists ui, qnth us i = Some ui.
  by apply: qnth_some; rewrite hus.
have hsig0 := qnth_sigs_of PP N (FWl zi) pp 0 dds us i ui hussz hilm hui.
rewrite add0n E2 in hsig0.
case: hsig0 => hsig.
have hd0 : (0 < nth 0 dds i)%N := leq_ltn_trans (leq0n _) hlt.
have hsr : sig_of_root PP N (FWl zi) pp i (nth 0 dds i) ui
         = FWl zi pp (i, (nth 0 dds i).-1) ui by case: (nth 0 dds i) hd0.
exists (pre_index dds i),
       (chain (cfWl zi pp i) si' (nth 0 mstar i)
              ((nth 0 dds i).-1 - nth 0 mstar i)),
       (i, (nth 0 dds i).-1), ui; split.
- by [].
- by rewrite (qnth_pre_queries N 0 dds us i ui hussz hilm hui hd0).
- by rewrite hpim hsig hsr.
Qed.

(** Offset read of the flattened SM-PRE target map: leaf [j]'s block sits at
    running offset [size (qflat pp 0 (take j CS))]; its [jc]-th entry is the
    [jc]-th [pre_queries] entry re-tagged by [lwq]. *)
Lemma qflat_block_get (pp : PP) (CS : seq lrec) (j jc : nat) :
  (j < size CS)%N -> (jc < size (qblk pp j (nth dflt_lrec CS j)))%N ->
  getm (qmap_from 0 (qflat pp 0 CS)) ((size (qflat pp 0 (take j CS)) + jc)%N)
  = qnth (qblk pp j (nth dflt_lrec CS j)) jc.
Proof.
move=> hj hjc.
have := qmap_from_get 0 (qflat pp 0 CS) (size (qflat pp 0 (take j CS)) + jc)%N.
rewrite add0n => ->.
rewrite {1}(qflat_take_drop pp CS j) qnth_cat_r (size_takel (ltnW hj)).
rewrite (drop_nth dflt_lrec hj) /=.
by rewrite qnth_cat_l.
Qed.

Lemma pre_block_get (pp : PP) (CS : seq lrec) (j jc : nat) (t : nat * nat) (u : N) :
  (j < size CS)%N ->
  qnth (pre_queries N 0
          (l_rrdigS (lcoord (nth dflt_lrec CS j).1.1) pp (nth dflt_lrec CS j).1.2.2 j)
          (nth dflt_lrec CS j).2) jc = Some (t, u) ->
  getm (qmap_from 0 (qflat pp 0 CS)) ((size (qflat pp 0 (take j CS)) + jc)%N)
  = Some (encode_adrs
            (wotsc_chain_adrs (lcoord (nth dflt_lrec CS j).1.1) t.1 t.2), u).
Proof.
move=> hj hqn.
have hblk : qblk pp j (nth dflt_lrec CS j)
          = [seq lwq (lcoord (nth dflt_lrec CS j).1.1) q
            | q <- pre_queries N 0
                     (l_rrdigS (lcoord (nth dflt_lrec CS j).1.1) pp
                        (nth dflt_lrec CS j).1.2.2 j) (nth dflt_lrec CS j).2].
  by rewrite /qblk /lchain_block.
have hjc : (jc < size (qblk pp j (nth dflt_lrec CS j)))%N.
  by rewrite hblk size_map; exact: (qnth_size _ _ _ hqn).
rewrite (qflat_block_get pp CS j jc hj hjc) hblk qnth_map hqn /=.
by rewrite /lwq.
Qed.

(** All digits of the slot-keyed committed digit are [< w] (digest_of is
    [wf_digits]; the virtual all-max digit [w.-1 < w] via [0 < w], forced by any
    valid non-empty reference digit). *)
Lemma all_lt_dds (zi : nat * nat) (pp0 : PP) (md : D) (j0 : nat) (ref : seq nat) :
  size ref = l -> all (fun d => (d < w)%N) ref ->
  all (fun d => (d < w)%N) (l_rrdigS zi pp0 md j0).
Proof.
move=> hsz href.
have hnseq : all (fun d => (d < w)%N) (nseq l w.-1).
  rewrite all_nseq ltn_predL.
  case E: (l == 0) => //=.
  have hsr : (0 < size ref)%N by rewrite hsz lt0n E.
  clear hsz.
  case: ref hsr href => [|a r] //= _ /andP[ha _].
  exact: leq_ltn_trans (leq0n a) ha.
rewrite /l_rrdigS /l_rrdig; case E0: (find_ctr _ _ _ _ _ _ _ _ _) => [c|] //.
by move: (find_ctr_good PP D Hgrind S_wn c_max zi.1 zi.2 pp0 md c E0);
   rewrite /good_ctr /valid_digest => /andP[].
Qed.

(* ================================================================== *)
(** ** The two perfect equivalences (M1d milestone, IN PROGRESS).

    (* FRONTIER (iteration 2): R_cpre_leaf_real / R_cpre_leaf_ideal — the
       COMMIT-tail assembly + LCHECK routing (2 Admitted).  NO structural
       mismatch; the design is validated by the machinery below.

       ====================================================================
       BANKED THIS ITERATION (all compile, Qed; the shared M1c/M1d blocker —
       the offset-FLATTENING invariant + multi-instance PQUERY loop specs):

       * Loop layer (the ChainHop [r_prquery]/[r_prchains_spec] lift, with
         the Compress walk-to-ends fused in):
         - block precond [pblk Φ po rv Q] over the flattened SM-PRE query list
           [Q : seq (adrs_sf_ch * N)] (Stg = [qmap_from 0 Q], Stw = [unzip1 Q]),
           frame [Φ] frozen via [pphi_stable] (PREHop design; SM-PRE locs 54-57);
           helpers [pblk_set_pp]/[pblk_qupd]/[pblk_set_rev].
         - cross-leaf freshness [pfresh zi st Q] (coordinate/chain-index
           disjunct) + [pfresh_notin]/[pfresh_S]/[pfresh_rcons].
         - [r_lprwalk_spec] (PCOLLQ walk, generic pre), [r_lprquery] (couple
           game [dN] with hidden PQUERY sample), [r_lprchains_spec] (per-chain
           induction: [sample_sig_roots] LHS vs [code_link (lpr_chains) SMB]
           RHS; Q grows by [lchain_block]; returns (sigs, ends=[wends])).
         - conversion bridges [lpr_collq_{H,F,Tl}_E], [th_eval_lF],
           [lcoord_chtw]/[lcoord_pkadr]/[adrs_chain_chtw], [wendsEl].
       * Flatten layer: [lwq]/[lchain_block]/[lchain_block_cons];
         [qflat]/[qflat_cat]/[qflat_rcons]/[qflat_take_drop]; [dflt_lrec].
       * Invariant layer: [RPr pp CS ltg rtg] (pointwise: [ltg]/[rtg] are the
         CS-indexed tables, [rtg] carries [copt=lfind] + running offset
         [size (qflat pp 0 (take j CS))], sig = honest [wsigs] at [l_rrdigS]);
         [RPr_empty], [RPr_qupd] (extend at slot [size CS]); top invariant [RP]
         (15 locs) + [pr_inv] + [pr_invE]/[pr_invI]; [pr_invL];
         [pr_inv_pin]/[pr_inv_reveal]/[pr_inv_setsl]; pp-coupler [r_pp2]
         (lands in [pr_invL pp]).

       ====================================================================
       REMAINING (mirror Leaf2Compress second half + ChainHop KFORGE):

       A. COMMIT pin+tail.  After the asserts, couple game [get Lpp] with the
          leading PCOLLQ's [get Spp] (a Compress-[r_pin_commit] variant
          landing in a frozen block [cbm pp t CS ltg rtg lsl]: heap_ignore +
          frozen game locs [Lpp=Some pp,Lrv=false,Lsl,Ltw=map .1.1 CS,Ltg=ltg]
          + frozen R locs [rpr_pp=None,rpr_rev=false,rpr_slog=lsl,
          rpr_tws=map .1.1 CS,rpr_tgts=rtg,rpr_cnt=size(qflat pp 0 CS)] + RPr;
          [cbm] must be [pphi_stable]).  Then:
            - [r_lpr_grind_spec] (banked) skips the RHS grind loop → hs;
              [lpr_digitS (size CS) hs = l_rrdigS (lcoord t) pp md (size CS)]
              via [lpr_digit_E]; [lpr_copt_E] gives copt=[lfind].
            - [r_get_rhs_known rpr_cnt_loc (size (qflat pp 0 CS))] reads ofs.
            - [r_lprchains_spec] with Q0 := [qflat pp 0 CS], ds := the digit;
              LHS [sample_sig_roots] matches the game's [rr_commit] sample
              (rewrite [rr_digitSE]-style: game [rr_digitS pp t md (size CS)]
              = [l_rrdigS (lcoord t) pp md (size CS)]).  Budget [q2 = n_max*l]:
              need [size (qflat pp 0 CS) + npq ds <= q2] (from RPr + per-leaf
              [npq <= l] + [size CS < n_max]); pfresh from the [gtw_of]-freshness.
            - TAIL (K0/K1 continuations): RHS pk-COLLQ [opr lpr_cqo
              (gtw_of t, inr (inl ends))] → [lpr_collq_Tl_E]; [ends = wends =
              lcompl] ([wendsEl]); then the three puts (Ltg/Ltw game; rpr_cnt/
              rpr_tgts/rpr_tws R) re-establish [pr_inv] with CS' = [rcons CS
              ((t,(sg,md)),us)] via [RPr_qupd] + [qflat_rcons] (new offset =
              old size(qflat CS) = ofs; [rpr_cnt += lnpq ds = npq ds =
              size(lchain_block ..)]).  Game root = [rr_pkS] = [Tl .. lcompl].
       B. IDEAL LCHECK: G1L = [ret false]; every R branch is false on [SMB
          false] ([resolve_lpr_ck_false]); reads rpr_rev (=Lrv via RP),
          getm rtg j, rpr_pp (=Some pp after reveal), lpr_pd/lpr_v pure → all
          [ret false]. Needs only A (no totality).  LGETPP: [r_pp2] +
          [pr_inv_reveal].  LSIGN: budget guard [case hj:(j<q_s)]; then
          getm ltg/rtg via RPr, find_ctr case, [pr_inv_setsl].  LCOLLQ:
          [r_pp2] + [lpr_collq_{H..}] as in Compress.
       C. REAL LCHECK: rewrite [P_gm3_E]; case [lpr_v]: false→both [ret false];
          true→ TOTALITY [lpr_pd = Some (jc,x)]:
            pop-1 ([j<q_s]&grindable): reconstruct ChainHop [wpre_decisionP]
              at [zstar:=(lcoord t0).1,istar:=(lcoord t0).2] (import ChainHop
              or inline [verify_from_ends]+[pre_decisionP]); needs the
              [verokS -> FixedSumOTS verify_sig] bridge (FXMSS.Scheme
              [verify_sigE] + [wcendsE]).
            pop-2 (else, virtual digit [nseq l w.-1]): [ZeroChainHop.zpre_win]
              under section hyp [Hdeg : S_wn != l*w.-1] (add [Context (Hdeg)]),
              bridged to [pre_decision] at the all-max digit.
          Then PCHECK win: [opr lpr_cko ((ofs+jc)%N, x)]; [getm Stg (ofs+jc)]
          via [qmap_from_get] + [qflat_take_drop] (block j sits at offset
          [size(qflat pp 0 (take j CS))]=ofs) + [qnth (lchain_block ..) jc]
          = the pre_queries entry; [th_eval_lF] + the preimage eq wins. *)
*)

(** The degeneracy side-hypothesis of the TERMINAL CHAIN-PRE hop (ZeroChainHop
    [R_zp_ideal] precedent): under [S_wn != l*w.-1] the all-max virtual digit
    fails [valid_digest] ([valid_not_allmax]), so pop-2 wins route to SM-PRE at
    the endpoint placement.  Anticipated by the ladder design; M3 supplies it.
    It is a DATA-level Prop hypothesis (NOT an axiom): it ripples into
    [R_cpre_leaf_real]/[sub_cpre] only once the terminal totality consumes it. *)
Context (Hdeg : S_wn != (l * w.-1)%N).

(** pop-2 (virtual all-max digit [nseq l w.-1]) strictly-lower coordinate:
    a valid forged digest is never all-max under [Hdeg]. *)
Lemma virtual_coord (fdv : seq nat) :
  size fdv = l -> @valid_digest w S_wn fdv ->
  has (fun i => (nth 0 fdv i < nth 0 (nseq l w.-1) i)%N) (iota 0 l).
Proof.
move=> hsz hvd.
have hh := valid_not_allmax S_wn fdv Hdeg hvd hsz.
set k := find (fun d => (d < w.-1)%N) fdv.
have hk : (k < size fdv)%N by rewrite -has_find.
have hlt : (nth 0 fdv k < w.-1)%N := nth_find 0 hh.
apply/hasP; exists k; first by rewrite mem_iota /= add0n -hsz.
by rewrite nth_nseq -hsz hk.
Qed.

(** The strictly-lower coordinate that drives [pre_decision] to fire, at the
    slot-keyed committed digit [l_rrdigS]: pop-1 (grindable, in-budget) via
    [eq_sumn_exists_lt] on the equal-sum digest space; pop-2 (virtual all-max
    digit) via [virtual_coord] under [Hdeg]. *)
Lemma lpr_coord (pp : PP) (t0 : adrs_sf_ch) (md0 : D) (j : nat) (fdv : seq nat) :
  @valid_digest w S_wn fdv -> size fdv = l ->
  ~~ (isSome (lfind (lcoord t0) pp md0)
       && (fdv == l_rrdigS (lcoord t0) pp md0 j)) ->
  has (fun i => (nth 0 fdv i < nth 0 (l_rrdigS (lcoord t0) pp md0 j) i)%N)
      (iota 0 l).
Proof.
move=> hvd hsz; rewrite /l_rrdigS /l_rrdig.
case hfc: (lfind (lcoord t0) pp md0) => [c|];
  last by move=> _; exact: (virtual_coord fdv hsz hvd).
rewrite /= => hne.
have hdds := find_ctr_good PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2
               pp md0 c hfc.
have hszd : size (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c)
          = l := size_digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c.
have hsum : sumn fdv
          = sumn (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c).
  by move: hvd hdds => /andP[_ /eqP ->] /andP[_ /eqP ->].
have hszeq : size fdv
           = size (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c)
  by rewrite hsz hszd.
have hne' : fdv <> digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c
  by apply/eqP.
have [k hk hlt] := eq_sumn_exists_lt hszeq hsum hne'.
apply/hasP; exists k; first by rewrite mem_iota /= add0n -hsz.
exact: hlt.
Qed.

Lemma R_cpre_leaf_real (hw : (0 < w)%N) :
  perfect IKM GM3 (R_cpre_leaf ∘ SMB true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pr_inv).
{ rewrite /pr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT — same COMMIT-tail FRONTIER as R_cpre_leaf_ideal (the reduction
     body / resolves are b-independent: resolve_lpr_cq/pq/gp hold for both b).
     See the ideal's LCOMMIT comment for the exact remaining pin/tail plan. *)
  destruct arg as [t md]. rewrite /rr_commit. ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev. eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/pr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev. rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws. eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/pr_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws. rewrite -/(code_link _ _).
  rewrite code_link_assertD. eapply r_assertD_same => hsz.
  rewrite code_link_assertD. eapply r_assertD_same => hfr.
  have hopr : forall (A : choiceType)
      (a : adrs_sf_ch × (N ∐ ('list N ∐ ((N × N) ∐ (D × 'nat)))))
      (kk : (N ∐ (N ∐ (N ∐ 'nat))) -> raw_code A) (g : raw_package),
      code_link (x ← op lpr_cqo ⋅ a ;; kk x) g
      = (r ← resolve g lpr_cqo a ;; code_link (kk r) g) by [].
  rewrite hopr; simplify_linking.
  have hpin : forall (k0 : PP -> raw_code N) (crest : raw_code N),
    (forall pp, ⊢ ⦃ λ '(s0, s1),
        [/\ pr_inv (s0, s1), get_heap s0 Lpp = Some pp,
            get_heap s0 Lrv = false, get_heap s0 Ltw = ltws
          & get_heap s1 Spp = Some pp] ⦄
       k0 pp ≈ crest ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pr_inv (s0, s1) ⦄) ->
    ⊢ ⦃ λ '(s0, s1),
        (pr_inv ⋊ rem_lhs Lrv lrev ⋊ rem_rhs rpr_rev_loc lrev
         ⋊ rem_lhs Ltw ltws ⋊ rem_rhs rpr_tws_loc ltws) (s0, s1) ⦄
       (ppo ← get Lpp ;;
        match ppo with
        | Some pp => k0 pp
        | None => pp ← dPP ;; #put Lpp := Some pp ;; k0 pp
        end)
     ≈ (v ← get Spp ;;
        (pp ← match v with
              | Some pp => ret pp
              | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
              end ;;
         ret (tc_eval CFl_leaf pp (grtw_of t) (inr (inr (inr (md, 0)))))) ;;
        crest) ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pr_inv (s0, s1) ⦄.
  { move=> k0 crest hk.
    eapply r_get_remember_lhs => lpp.
    eapply r_get_remember_rhs => spp.
    eapply (r_fact (spp = lpp)).
      { move=> s0 s1 [[[[[[hinv _] _] _] _] hr0] hr1].
        case/pr_invE: hinv => _ [_ _ _ _ [hsp _ _]].
        rewrite /rem_inv /= in hr0 hr1.
        by rewrite -hr1 hsp hr0. }
    move=> e; subst spp.
    case: lpp hk => [pp0|] hk.
    { rewrite bind_ret_l bind_ret_l.
      eapply rpre_weaken_rule; first exact: (hk pp0).
      move=> s0 s1 [[[[[[hinv hrL] hrB] hrC] hrD] hrLpp] hrSpp].
      rewrite /rem_inv /= in hrL hrC hrLpp hrSpp.
      split=> //.
      by rewrite hrL (negbTE erev). }
    cbv beta iota.
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> pp; cbv beta.
    eapply r_put_lhs; eapply r_put_rhs.
    rewrite bind_ret_l.
    eapply rpre_weaken_rule; first exact: (hk pp).
    move=> s0 s1 [s1' [[s0' [Hbase e0]] e1]].
    move: Hbase => [[[[[[hinv hrL] hrB] hrC] hrD] hrLpp] hrSpp].
    rewrite /rem_inv /= in hrL hrC hrLpp hrSpp.
    subst s0 s1; split.
    { apply: (pr_inv_pin pp s0' s1' hinv hrLpp). }
    { by rewrite get_set_heap_eq. }
    { rewrite get_set_heap_neq //; by rewrite hrL (negbTE erev). }
    { rewrite get_set_heap_neq //; exact: hrC. }
    by rewrite get_set_heap_eq. }
  apply: hpin => pp.
  apply rpre_hypothesis_rule => s0 s1 HPB.
  move: (HPB) => [hinv hLpp hLrv hLtw hSpp].
  move: (pr_inv_cblk pp s0 s1 hinv hLpp hLrv) => [CS [hpblk hLtwCS hRPr]].
  have hltwE : ltws = [seq r.1.1 | r <- CS] by rewrite -hLtw hLtwCS.
  have hszE : size ltws = size CS by rewrite hltwE size_map.
  eapply rpre_weaken_rule.
  2:{ move=> s2 s3 /= [-> ->]; exact: hpblk. }
  rewrite code_link_bind.
  eapply (r_lpr_grind_spec true pp (lcoord t) md (iota 0 c_max)
            (pblk (cfrm pp CS (get_heap s0 Lsl) (get_heap s0 Ltg)
                     (get_heap s1 rpr_tgts_loc)) (Some pp) false
                  (qflat pp 0 CS))).
    { move=> s2 s3 [_ h' _ _ _]; exact: h'. }
  rewrite lpr_digitSE.
  rewrite cl_getr.
  eapply (r_get_rhs_known rpr_cnt_loc (size (qflat pp 0 CS))).
    { move=> s2 s3 [hcfrm _ _ _ _].
      case: hcfrm => _ _ [_ _ _ _ [_ hcnt]] _; exact: hcnt. }
  rewrite code_link_bind.
  rewrite rr_digitSE /rr_F.
  eapply (r_lprchains_spec true
            (cfrm pp CS (get_heap s0 Lsl) (get_heap s0 Ltg)
               (get_heap s1 rpr_tgts_loc)) pp (lcoord t) _
            (pphi_stable_cfrm _ _ _ _ _)).
  { exact: l2_lcoord_bounded. }
  { by rewrite add0n size_l_rrdigS. }
  { exact: wf_l_rrdigS. }
  { have h2 : (npq (l_rrdigS (lcoord t) pp md (size ltws)) <= l)%N.
      exact: (npq_le l _ (size_l_rrdigS (lcoord t) pp md (size ltws))).
    have h1 : (size (qflat pp 0 CS) <= size CS * l)%N.
      apply: size_qflat_le => j hj.
      by case: hRPr => _ _ hrec; case: (hrec j hj) => ->.
    apply: (leq_trans (leq_add h1 h2)).
    have hCS : (size CS < n_max)%N by rewrite -hszE.
    have hmul := leq_mul hCS (leqnn l).
    by move: hmul; rewrite mulSn addnC. }
  { apply: (pfresh_coord hw) => r hr.
    move: hfr; rewrite hltwE => hfr'.
    exact: (coord_of_gtw t CS hfr' r hr). }
  move=> us hus.
  set sg := wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size ltws)) us.
  rewrite (lpr_copt_E pp (lcoord t) md).
  rewrite (wendsEl (lcoord t) pp (l_rrdigS (lcoord t) pp md (size ltws)) sg
             (size_l_rrdigS (lcoord t) pp md (size ltws))).
  rewrite hopr; simplify_linking.
  eapply (r_get_rhs_known Spp (Some pp)).
    { move=> s2 s3 [_ hspp _ _ _]; exact: hspp. }
  cbv beta iota.
  rewrite bind_ret_l.
  rewrite bind_ret_l.
  rewrite (lpr_collq_Tl_E pp (lcoord t)).
  eapply (r_get_lhs_known Ltg (get_heap s0 Ltg)).
    { move=> s2 s3 [hcfrm _ _ _ _].
      case: hcfrm => _ hG _ _; case: hG => _ _ _ _ hltg; exact: hltg. }
  apply r_put_rhs.
  eapply (r_get_rhs_known rpr_tgts_loc (get_heap s1 rpr_tgts_loc)).
    { move=> s2 s3 [s3' [[hcfrm _ _ _ _] e3]]; subst s3;
        rewrite get_set_heap_neq //.
      case: hcfrm => _ _ hR _; case: hR => _ _ _ _ [hrtg _]; exact: hrtg. }
  apply r_put_lhs; apply r_put_lhs.
  apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s2 s3
    [s3a [[s3b [[s2a [[s2b [[s3c [Hpblk e_cnt]] e_ltg]] e_ltw]] e_tgts]] e_tws]].
  case: Hpblk => hcfrm hSpp' hSrv' hStw' hStg'.
  case: hcfrm => hign hGame hR hRPr'.
  case: hGame => hLpp' hLrv' hLsl' hLtw' hLtg'.
  case: hR => hrpp' hrrv' hrsl' hrtw' [hrtg' hrcnt'].
  subst s3 s3a s3b s2 s2a.
  split; first by rewrite /rr_pkS rr_digitSE.
  apply: pr_invI.
  { apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign. }
  rewrite /RP; get_heap_simpl.
  rewrite hLpp' hLrv' hLsl' hrpp' hrrv' hrsl' hSpp' hSrv' hStg' hStw'.
  have husl : size us = l by rewrite hus size_l_rrdigS.
  have hqf : qflat pp 0 (rcons CS ((t, (sg, md)), us))
           = qflat pp 0 CS
             ++ lchain_block (lcoord t) 0
                  (l_rrdigS (lcoord t) pp md (size ltws)) us
    by rewrite qflat_rcons add0n /qblk /= hszE.
  split=> //; split=> //.
  exists (rcons CS ((t, (sg, md)), us)); rewrite hqf.
  split.
  { rewrite hszE.
    have hsgE : sg = wsigs (lcoord t) pp 0
                       (l_rrdigS (lcoord t) pp md (size CS)) us
      by rewrite /sg hszE.
    exact: (RPr_qupd pp CS (get_heap s0 Ltg) (get_heap s1 rpr_tgts_loc)
              t sg md us hRPr' husl hsgE). }
  { by rewrite map_rcons -hltwE. }
  { by []. }
  { by []. }
  by rewrite size_cat
       (size_lchain_block (lcoord t) 0 (l_rrdigS (lcoord t) pp md (size ltws))
          us hus) lnpqE.
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rpr_pp_loc := Some b ;; #put rpr_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (pr_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK — the TERMINAL win/route bridge (real side).  The structural
     routing is now MECHANIZED down to the SINGLE terminal goal (the totality
     + PCHECK-win step; see the (* FRONTIER *) at the [admit] below).
     Steps: couple [rpr_rev]/[Lrv] ([r_fact rrv=lrv]); [revealed=false] ⇒ both
     fail (game [#assert false]; R's else-PCHECK on SMB true [#assert Srv=false]
     via [resolve_lpr_ck] + [r_fail_bind_rhs]); [revealed=true] ⇒ couple
     [Ltg]/[rpr_tgts] then [Lpp]/[rpr_pp] (both = [Some pp] since revealed, RPr
     giving [copt=lfind], [ofs=size(qflat pp 0 (take j CS))]); [rewrite P_gm3_E]
     turns the game win into [lpr_v pp t0 sg md0 (lfind ..) j mw] = R's [lpr_v]
     (same [copt]); [case lpr_v]: false ⇒ both [ret false] (any [lpr_pd]). *)
  move: arg => [j mw]. rewrite /rr_winbody. ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev. eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/pr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  case: lrev; last first.
  { (* revealed = false: game [#assert false]; R's SMB-true else-PCHECK reads
       [Srv = Lrv = false] and [#assert]s it — both fail. *)
    ssprove_code_simpl; simpl.
    rewrite resolve_lpr_ck.
    eapply r_get_remember_rhs => srv.
    eapply (r_fact (srv = false)).
      { move=> s0 s1 [[[hinv hL] hR] hS].
        rewrite /rem_inv /= in hL hS.
        case/pr_invE: hinv => _ [_ _ _ _ [_ hsrv _]].
        by rewrite -hS hsrv hL. }
    move=> e; subst srv.
    apply r_fail_bind_rhs. }
  (* revealed = true *)
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  - (* no committed leaf at slot j: [rtg j = None] too (RPr) — both [ret false]. *)
    eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => CS [hRPr _ _ _ _].
          case: hRPr => hl hr _.
          by move: (hr j); rewrite -hr3; move: (hl j); rewrite hr2 E;
             case: ifP => _ // -[?].
        - case: hm => hltg hrtg _; by rewrite -hr3 hrtg emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - (* committed leaf at slot j: extract [pp] + the [rtg] entry via RPr,
       couple [Lpp]/[rpr_pp] (= [Some pp] since revealed), route via P_gm3_E. *)
    eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp ofs, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0, ofs)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr2 hr3 hr4.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => CS [hRPr _ _ _ _].
          case: hRPr => hl hr _.
          have hjs : (j < size CS)%N.
            by move: (hl j); rewrite hr2 E; case: ifP => // _ [].
          exists pp, (size (qflat pp 0 (take j CS))); split; first by rewrite -hr4.
          move: (hr j); rewrite hjs -hr3 => ->.
          move: (hl j); rewrite hr2 E hjs => -[hnth].
          by rewrite -hnth.
        - case: hm => hltg _ _; move: E; rewrite -hr2 hltg emptymE => H;
             discriminate H. }
    move=> [pp [ofs [hlpp hrtgj]]].
    rewrite hlpp hrtgj.
    rewrite cl_getr.
    eapply r_get_remember_rhs => rpp.
    eapply (r_fact (rpp = Some pp)).
      { move=> s0 s1 [[[[[[hinv hr0] hr1] hr2] hr3] hr4] hr5].
        rewrite /rem_inv /= in hr0 hr4 hr5.
        case/pr_invE: hinv => _ [_ _ _ hrpp _].
        by rewrite -hr5 hrpp hr0 hr4. }
    move=> e; subst rpp.
    rewrite bind_ret_l (P_gm3_E pp t0 sg md0 j mw).
    case Hv: (lpr_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw); last first.
    + (* lpr_v = false: both sides answer [ret false] (regardless of lpr_pd). *)
      case: (lpr_pd pp t0 sg md0 j mw) => [[jc x]|];
        apply r_ret => s0 s1 [[[[[[hinv _] _] _] _] _] _]; by split.
    + (* CLOSED (M1d, iteration 2): the LCHECK-true TERMINAL win/route.
         (1) TOTALITY: extract [Hv]'s pure facts (valid forged digest, size,
             compress, tcr-none), derive the strictly-lower coordinate via
             [lpr_coord] (pop-1 [eq_sumn_exists_lt] / pop-2 [valid_not_allmax]
             under [Hdeg]); read [sg = wsigs] from the invariant, then
             [l2_pre_win] forces [lpr_pd = Some (jc,x)].
         (2) PCHECK WIN: [op lpr_cko ((ofs+jc)%N,x)] via [SMB true] reads
             [Stg (ofs+jc)] = leaf j's block entry ([pre_block_get] =
             [qflat_take_drop]+[qmap_from_get]+[qnth_map] at the [pre_queries]
             offset); [th_eval_lF] + [l2_pre_win]'s preimage equation close it. *)
      rewrite /lpr_v in Hv.
      case/and5P: Hv => hverok hgate hnghit hcompress htcrnone.
      case/andP: hverok => hwc hanchor.
      rewrite /wots_checks in hwc.
      case/andP: hwc => hvd hsgsz.
      have hddsz := size_l_rrdigS (lcoord t0) pp md0 j.
      have hfdvsz : size (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2
                            pp mw.1 mw.2.2) = l
        := size_digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2.
      have hallfdv : all (fun d => (d < w)%N)
          (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2).
        by move: hvd; rewrite /valid_digest /wf_digits => /andP[].
      have hvmf : valid_msg l w S_wn
          (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2).
        by rewrite /valid_msg hfdvsz eqxx /=;
           move: hvd; rewrite /valid_digest /wf_digits.
      have hddw := all_lt_dds (lcoord t0) pp md0 j _ hfdvsz hallfdv.
      have hhas := lpr_coord pp t0 md0 j _ hvd hfdvsz hnghit.
      have htcrN : tcr_decision PP N (FWl (lcoord t0)) l w pp
          (l_rrdigS (lcoord t0) pp md0 j)
          (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
          sg mw.2.1 = None.
        by move: htcrnone; case: (tcr_decision _ _ _ _ _ _ _ _ _).
      eapply (r_fact (exists jc x, lpr_pd pp t0 sg md0 j mw = Some (jc, x))).
      { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
        rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; rewrite h4 => -[CS [hRPr hltweq hstg hstw hcnt]].
        case: hRPr => hl hr hwalk.
        have hjs : (j < size CS)%N.
          by move: (hr j); rewrite h3 hrtgj; case: ifP => // _ [].
        move: (hr j); rewrite h3 hrtgj hjs => hE.
        case: hE => ht0 [[hsgmd _] _].
        have [hussz hsgw0] := hwalk j hjs.
        have hsg : (nth dflt_lrec CS j).1.2.1 = sg by rewrite -hsgmd.
        have hmd : (nth dflt_lrec CS j).1.2.2 = md0 by rewrite -hsgmd.
        have hsgwf : sg = wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j)
                             (nth dflt_lrec CS j).2.
          by rewrite -hsg hsgw0 ht0 hmd.
        have hends' : lcompl (lcoord t0) pp
            (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
            mw.2.1
          = lcompl (lcoord t0) pp (l_rrdigS (lcoord t0) pp md0 j)
              (wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j)
                 (nth dflt_lrec CS j).2).
          by apply/eqP; rewrite -hsgwf.
        have hnone' : tcr_decision PP N (FWl (lcoord t0)) l w pp
            (l_rrdigS (lcoord t0) pp md0 j)
            (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
            (wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j)
               (nth dflt_lrec CS j).2) mw.2.1 = None.
          by rewrite -hsgwf.
        have [jc [x [t [u [hpd _ _]]]]] := l2_pre_win (lcoord t0) pp
            (l_rrdigS (lcoord t0) pp md0 j) (nth dflt_lrec CS j).2 mw.2.1
            (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
            hddsz hddw hussz hvmf hsgsz hhas hends' hnone'.
        by exists jc, x; rewrite /lpr_pd hsgwf. }
      move=> [jc [x hpd]].
      rewrite hpd.
      ssprove_code_simpl; simplify_linking.
      eapply (r_get_rhs_known Srv true).
      { move=> s0 s1 [[[[[[hinv h0] _] _] _] _] _].
        rewrite /rem_inv /= in h0.
        case/pr_invE: hinv => _ [_ _ _ _ [_ hsrv _]].
        by rewrite hsrv h0. }
      simpl.
      eapply r_get_remember_rhs => tg.
      eapply (r_fact (exists (t : nat * nat) u,
        [/\ getm tg ((ofs + jc)%N)
            = Some (encode_adrs (wotsc_chain_adrs (lcoord t0) t.1 t.2), u)
          & FWl (lcoord t0) pp t x = FWl (lcoord t0) pp t u])).
      { move=> s0 s1 [[[[[[[hinv h0] h1] h2] h3] h4] h5] htg].
        rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 htg.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; rewrite h4 => -[CS [hRPr hltweq hstg hstw hcnt]].
        case: hRPr => hl hr hwalk.
        have hjs : (j < size CS)%N.
          by move: (hr j); rewrite h3 hrtgj; case: ifP => // _ [].
        move: (hr j); rewrite h3 hrtgj hjs => hE.
        case: hE => ht0 [[hsgmd _] hofse].
        have [hussz hsgw0] := hwalk j hjs.
        have hsg : (nth dflt_lrec CS j).1.2.1 = sg by rewrite -hsgmd.
        have hmd : (nth dflt_lrec CS j).1.2.2 = md0 by rewrite -hsgmd.
        have hsgwf : sg = wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j)
                             (nth dflt_lrec CS j).2.
          by rewrite -hsg hsgw0 ht0 hmd.
        have hends' : lcompl (lcoord t0) pp
            (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
            mw.2.1
          = lcompl (lcoord t0) pp (l_rrdigS (lcoord t0) pp md0 j)
              (wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j)
                 (nth dflt_lrec CS j).2).
          by apply/eqP; rewrite -hsgwf.
        have hnone' : tcr_decision PP N (FWl (lcoord t0)) l w pp
            (l_rrdigS (lcoord t0) pp md0 j)
            (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
            (wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j)
               (nth dflt_lrec CS j).2) mw.2.1 = None.
          by rewrite -hsgwf.
        have [jc2 [x2 [t [u [hpd2 hqn hcol]]]]] := l2_pre_win (lcoord t0) pp
            (l_rrdigS (lcoord t0) pp md0 j) (nth dflt_lrec CS j).2 mw.2.1
            (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
            hddsz hddw hussz hvmf hsgsz hhas hends' hnone'.
        have hpd' : lpr_pd pp t0 sg md0 j mw = Some (jc2, x2)
          by rewrite /lpr_pd hsgwf.
        move: hpd; rewrite hpd' => -[hjcE hxE].
        exists t, u; split; last by rewrite -hxE.
        rewrite -htg hstg hofse -hjcE ht0.
        apply: (pre_block_get pp CS j jc2 t u hjs).
        by rewrite ht0 -hmd in hqn. }
      move=> [t [u [hgetm hcol]]].
      rewrite hgetm.
      eapply (r_get_rhs_known Spp (Some pp)).
      { move=> s0 s1 [[[[[[[hinv _] _] _] _] h4] _] _].
        rewrite /rem_inv /= in h4.
        case/pr_invE: hinv => _ [_ _ _ _ [hspp _ _]].
        by rewrite hspp h4. }
      cbv beta iota.
      rewrite bind_ret_l !th_eval_lF -!surjective_pairing hcol eqxx.
      apply r_ret => s0 s1 hpre; split; first by [].
      by case: hpre => [[[[[[[hinv _] _] _] _] _] _] _].
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/pr_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  rewrite ?code_link_assertD.
  eapply r_assertD_same => _.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  - eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => CS [hRPr _ _ _ _].
          case: hRPr => hl hr _.
          by move: (hr j); rewrite -hr3; move: (hl j); rewrite hr2 E;
             case: ifP => _ // -[?].
        - case: hm => hltg hrtg _; by rewrite -hr3 hrtg emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp ofs, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0, ofs)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr2 hr3 hr4.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => CS [hRPr _ _ _ _].
          case: hRPr => hl hr _.
          have hjs : (j < size CS)%N.
            by move: (hl j); rewrite hr2 E; case: ifP => // _ [].
          exists pp, (size (qflat pp 0 (take j CS))); split; first by rewrite -hr4.
          move: (hr j); rewrite hjs -hr3 => ->.
          move: (hl j); rewrite hr2 E hjs => -[hnth].
          by rewrite -hnth.
        - case: hm => hltg _ _; move: E; rewrite -hr2 hltg emptymE => H;
             discriminate H. }
    move=> [pp [ofs [hlpp hrtgj]]].
    rewrite hlpp hrtgj /=.
    case E2: (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0) => [c|].
    + apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
      rewrite /rem_inv /= in hr0 hr1.
      subst s0 s1; split=> //.
      exact: (pr_inv_setsl (rcons slog j) s0' s1' hinv).
    + apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inr (inl xy))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inr (inr dc))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
(* M1d CLOSED (iteration 2): the LCHECK-true TERMINAL win/route is proved.
   TOTALITY [lpr_v = true -> lpr_pd = Some (jc,x)] via [l2_pre_win] (the
   coordinate-general merge of FixedSumOTS [classify_some]+[pre_decisionP],
   honest digit NOT required valid) fed by [lpr_coord] (pop-1 [eq_sumn_exists_lt]
   / pop-2 [valid_not_allmax] under the section hyp [Hdeg]).  PCHECK WIN reads
   [Stg (ofs+jc)] = leaf j's block entry via [pre_block_get]
   ([qflat_take_drop]+[qmap_from_get]+[qnth_map] at the [pre_queries] offset),
   closed by [th_eval_lF] + [l2_pre_win]'s preimage equation. *)
Qed.

Lemma R_cpre_leaf_ideal (hw : (0 < w)%N) :
  perfect IKM G1L (R_cpre_leaf ∘ SMB false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pr_inv).
{ rewrite /pr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT.
     FRONTIER (M1d, iteration 4): the COMMIT-tail assembly.  The EXACT prefix
     that reaches the pin point is now MCP-verified (below); the extraction /
     budget / freshness lemmas the last iteration flagged as "the one missing
     structural piece" are now BANKED (Qed): [pr_inv_cblk] (extract CS from the
     Some-pp branch, land in [pblk (cfrm pp CS (get_heap s0 Lsl)(get_heap s0
     Ltg)(get_heap s1 rpr_tgts_loc)) (Some pp) false (qflat pp 0 CS)] +
     [get_heap s0 Ltw = map .1.1 CS] + [RPr]); [size_qblk_le]/[size_qflat_le]
     (size (qflat pp 0 CS) <= size CS * l, so the budget size(qflat)+npq ds <=
     n_max*l follows from size CS < n_max + count_size); [coord_of_gtw] +
     [pfresh_coord] (cross-leaf freshness pfresh (lcoord t) 0 (qflat pp 0 CS)
     from the gtw_of-notin).

     VERIFIED PREFIX (reaches the pin point, RHS = code_link (op lpr_cqo
     (grtw_of t,inr inr inr(md,0)) ;; <grind;ofs;chains;pkcollq;puts>) (SMB b)):
       destruct arg as [t md]. rewrite /rr_commit. ssprove_code_simpl; simpl.
       eapply r_get_remember_lhs => lrev. eapply r_get_remember_rhs => rrev.
       eapply (r_fact (rrev = lrev)). { .. pr_invE [_ hrrv _ _ _] .. }
       move=> e; subst rrev. rewrite code_link_assertD.
       eapply r_assertD_same => erev.
       eapply r_get_remember_lhs => ltws. eapply r_get_remember_rhs => rtws.
       eapply (r_fact (rtws = ltws)). { .. pr_invE [hrtw _ _ _ _] .. }
       move=> e; subst rtws. rewrite -/(code_link _ _).  (* RE-FOLD code_link:
         r_get_remember_rhs unfolds code_link to its fix; -/(code_link _ _)
         re-folds so the next code_link_assertD matches. *)
       rewrite code_link_assertD. eapply r_assertD_same => hsz.
       rewrite code_link_assertD. eapply r_assertD_same => hfr.
       eapply r_get_remember_lhs => lpp.
     REMAINING (pin -> grind -> chains -> tail):
       PIN: expose the leading COLLQ resolve.  code_link (opr...) is NOT a
       file-level lemma (a Lemma-statement parse of [op o cdot a] fails; use a
       LOCAL [have hopr : forall {A}(o)(a)(kk)(g0), code_link (x <- op o cdot a
       ;; kk x) g0 = r <- resolve g0 o a ;; code_link (kk r) g0 by []]), then
       rewrite hopr; rewrite (resolve_lpr_cq b (grtw_of t) (inr(inr(inr(md,0)))));
       rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp (grtw_of t)
       (inr(inr(inr(md,0)))))).  RHS is now [ppo <- get Spp ;; pp <- match ;;
       code_link K1 g].  Couple game [get Lpp] (lpp) with [get Spp]: r_fact
       [spp=lpp] (pr_invE .. [hspp _ _]), case lpp: Some pp0 => use pr_inv_cblk
       to get CS + pblk(cfrm ..); None => r_scheme_bind couple dPP samples,
       r_put_lhs/r_put_rhs (Lpp/Spp:=Some pp), CS:=[::] via pr_inv_pin (or a
       [::]-instance of pr_inv_cblk after the puts).
       GRIND: rewrite code_link_bind; apply (r_lpr_grind_spec b pp (lcoord t)
       md (iota 0 c_max) (pblk (cfrm ..) (Some pp) false (qflat pp 0 CS))
       (fun s0 s1 => pblk..Spp)); rewrite lpr_digitSE / lpr_copt_E to fold hs
       into l_rrdigS. OFS: r_get_rhs_known rpr_cnt_loc via cfrm.
       CHAINS: rewrite code_link_bind; rewrite -rr_digitSE (game side digit);
       apply (r_lprchains_spec b (cfrm ..) pp (lcoord t)) with ds:=l_rrdigS
       (lcoord t) pp md (size CS); BUDGET size(qflat)+npq ds<=n_max*l via
       size_qflat_le (RPr gives size .2 = l) + count_size + size CS<n_max;
       PFRESH via pfresh_coord (coord_of_gtw hfr).  LHS sample_sig_roots matches
       rr_commit's after rr_F = FWl (lcoord t) (Print rr_F).
       TAIL: RHS pk-COLLQ (op lpr_cqo (gtw_of t, inr(inl ends))) via hopr +
       resolve_lpr_cq + lpr_collq_Tl_E; ends = wends = lcompl via wendsEl
       (size ds = l); game root rr_pkS = l_rrpkS = Tl .. lcompl (Print rr_pkS);
       three game puts (Ltg/Ltw) + three R puts (rpr_cnt/rpr_tgts/rpr_tws);
       re-establish pr_inv with CS' = rcons CS ((t,(sg,md)),us) via RPr_qupd +
       qflat_rcons (new offset ofs = size(qflat pp 0 CS); rpr_cnt += lnpq ds =
       npq ds = size(lchain_block) via size_lchain_block).  b-independent:
       the same block applies to [R_cpre_leaf_real]'s LCOMMIT branch. *)
  destruct arg as [t md]. rewrite /rr_commit. ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev. eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/pr_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev. rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws. eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/pr_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws. rewrite -/(code_link _ _).
  rewrite code_link_assertD. eapply r_assertD_same => hsz.
  rewrite code_link_assertD. eapply r_assertD_same => hfr.
  have hopr : forall (A : choiceType)
      (a : adrs_sf_ch × (N ∐ ('list N ∐ ((N × N) ∐ (D × 'nat)))))
      (kk : (N ∐ (N ∐ (N ∐ 'nat))) -> raw_code A) (g : raw_package),
      code_link (x ← op lpr_cqo ⋅ a ;; kk x) g
      = (r ← resolve g lpr_cqo a ;; code_link (kk r) g) by [].
  rewrite hopr; simplify_linking.
  have hpin : forall (k0 : PP -> raw_code N) (crest : raw_code N),
    (forall pp, ⊢ ⦃ λ '(s0, s1),
        [/\ pr_inv (s0, s1), get_heap s0 Lpp = Some pp,
            get_heap s0 Lrv = false, get_heap s0 Ltw = ltws
          & get_heap s1 Spp = Some pp] ⦄
       k0 pp ≈ crest ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pr_inv (s0, s1) ⦄) ->
    ⊢ ⦃ λ '(s0, s1),
        (pr_inv ⋊ rem_lhs Lrv lrev ⋊ rem_rhs rpr_rev_loc lrev
         ⋊ rem_lhs Ltw ltws ⋊ rem_rhs rpr_tws_loc ltws) (s0, s1) ⦄
       (ppo ← get Lpp ;;
        match ppo with
        | Some pp => k0 pp
        | None => pp ← dPP ;; #put Lpp := Some pp ;; k0 pp
        end)
     ≈ (v ← get Spp ;;
        (pp ← match v with
              | Some pp => ret pp
              | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
              end ;;
         ret (tc_eval CFl_leaf pp (grtw_of t) (inr (inr (inr (md, 0)))))) ;;
        crest) ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pr_inv (s0, s1) ⦄.
  { move=> k0 crest hk.
    eapply r_get_remember_lhs => lpp.
    eapply r_get_remember_rhs => spp.
    eapply (r_fact (spp = lpp)).
      { move=> s0 s1 [[[[[[hinv _] _] _] _] hr0] hr1].
        case/pr_invE: hinv => _ [_ _ _ _ [hsp _ _]].
        rewrite /rem_inv /= in hr0 hr1.
        by rewrite -hr1 hsp hr0. }
    move=> e; subst spp.
    case: lpp hk => [pp0|] hk.
    { rewrite bind_ret_l bind_ret_l.
      eapply rpre_weaken_rule; first exact: (hk pp0).
      move=> s0 s1 [[[[[[hinv hrL] hrB] hrC] hrD] hrLpp] hrSpp].
      rewrite /rem_inv /= in hrL hrC hrLpp hrSpp.
      split=> //.
      by rewrite hrL (negbTE erev). }
    cbv beta iota.
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> pp; cbv beta.
    eapply r_put_lhs; eapply r_put_rhs.
    rewrite bind_ret_l.
    eapply rpre_weaken_rule; first exact: (hk pp).
    move=> s0 s1 [s1' [[s0' [Hbase e0]] e1]].
    move: Hbase => [[[[[[hinv hrL] hrB] hrC] hrD] hrLpp] hrSpp].
    rewrite /rem_inv /= in hrL hrC hrLpp hrSpp.
    subst s0 s1; split.
    { apply: (pr_inv_pin pp s0' s1' hinv hrLpp). }
    { by rewrite get_set_heap_eq. }
    { rewrite get_set_heap_neq //; by rewrite hrL (negbTE erev). }
    { rewrite get_set_heap_neq //; exact: hrC. }
    by rewrite get_set_heap_eq. }
  apply: hpin => pp.
  apply rpre_hypothesis_rule => s0 s1 HPB.
  move: (HPB) => [hinv hLpp hLrv hLtw hSpp].
  move: (pr_inv_cblk pp s0 s1 hinv hLpp hLrv) => [CS [hpblk hLtwCS hRPr]].
  have hltwE : ltws = [seq r.1.1 | r <- CS] by rewrite -hLtw hLtwCS.
  have hszE : size ltws = size CS by rewrite hltwE size_map.
  eapply rpre_weaken_rule.
  2:{ move=> s2 s3 /= [-> ->]; exact: hpblk. }
  rewrite code_link_bind.
  eapply (r_lpr_grind_spec false pp (lcoord t) md (iota 0 c_max)
            (pblk (cfrm pp CS (get_heap s0 Lsl) (get_heap s0 Ltg)
                     (get_heap s1 rpr_tgts_loc)) (Some pp) false
                  (qflat pp 0 CS))).
    { move=> s2 s3 [_ h' _ _ _]; exact: h'. }
  rewrite lpr_digitSE.
  rewrite cl_getr.
  eapply (r_get_rhs_known rpr_cnt_loc (size (qflat pp 0 CS))).
    { move=> s2 s3 [hcfrm _ _ _ _].
      case: hcfrm => _ _ [_ _ _ _ [_ hcnt]] _; exact: hcnt. }
  rewrite code_link_bind.
  rewrite rr_digitSE /rr_F.
  eapply (r_lprchains_spec false
            (cfrm pp CS (get_heap s0 Lsl) (get_heap s0 Ltg)
               (get_heap s1 rpr_tgts_loc)) pp (lcoord t) _
            (pphi_stable_cfrm _ _ _ _ _)).
  { exact: l2_lcoord_bounded. }
  { by rewrite add0n size_l_rrdigS. }
  { exact: wf_l_rrdigS. }
  { have h2 : (npq (l_rrdigS (lcoord t) pp md (size ltws)) <= l)%N.
      exact: (npq_le l _ (size_l_rrdigS (lcoord t) pp md (size ltws))).
    have h1 : (size (qflat pp 0 CS) <= size CS * l)%N.
      apply: size_qflat_le => j hj.
      by case: hRPr => _ _ hrec; case: (hrec j hj) => ->.
    apply: (leq_trans (leq_add h1 h2)).
    have hCS : (size CS < n_max)%N by rewrite -hszE.
    have hmul := leq_mul hCS (leqnn l).
    by move: hmul; rewrite mulSn addnC. }
  { apply: (pfresh_coord hw) => r hr.
    move: hfr; rewrite hltwE => hfr'.
    exact: (coord_of_gtw t CS hfr' r hr). }
  move=> us hus.
  set sg := wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size ltws)) us.
  rewrite (lpr_copt_E pp (lcoord t) md).
  rewrite (wendsEl (lcoord t) pp (l_rrdigS (lcoord t) pp md (size ltws)) sg
             (size_l_rrdigS (lcoord t) pp md (size ltws))).
  rewrite hopr; simplify_linking.
  eapply (r_get_rhs_known Spp (Some pp)).
    { move=> s2 s3 [_ hspp _ _ _]; exact: hspp. }
  cbv beta iota.
  rewrite bind_ret_l.
  rewrite bind_ret_l.
  rewrite (lpr_collq_Tl_E pp (lcoord t)).
  eapply (r_get_lhs_known Ltg (get_heap s0 Ltg)).
    { move=> s2 s3 [hcfrm _ _ _ _].
      case: hcfrm => _ hG _ _; case: hG => _ _ _ _ hltg; exact: hltg. }
  apply r_put_rhs.
  eapply (r_get_rhs_known rpr_tgts_loc (get_heap s1 rpr_tgts_loc)).
    { move=> s2 s3 [s3' [[hcfrm _ _ _ _] e3]]; subst s3;
        rewrite get_set_heap_neq //.
      case: hcfrm => _ _ hR _; case: hR => _ _ _ _ [hrtg _]; exact: hrtg. }
  apply r_put_lhs; apply r_put_lhs.
  apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s2 s3
    [s3a [[s3b [[s2a [[s2b [[s3c [Hpblk e_cnt]] e_ltg]] e_ltw]] e_tgts]] e_tws]].
  case: Hpblk => hcfrm hSpp' hSrv' hStw' hStg'.
  case: hcfrm => hign hGame hR hRPr'.
  case: hGame => hLpp' hLrv' hLsl' hLtw' hLtg'.
  case: hR => hrpp' hrrv' hrsl' hrtw' [hrtg' hrcnt'].
  subst s3 s3a s3b s2 s2a.
  split; first by rewrite /rr_pkS rr_digitSE.
  apply: pr_invI.
  { apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign. }
  rewrite /RP; get_heap_simpl.
  rewrite hLpp' hLrv' hLsl' hrpp' hrrv' hrsl' hSpp' hSrv' hStg' hStw'.
  have husl : size us = l by rewrite hus size_l_rrdigS.
  have hqf : qflat pp 0 (rcons CS ((t, (sg, md)), us))
           = qflat pp 0 CS
             ++ lchain_block (lcoord t) 0
                  (l_rrdigS (lcoord t) pp md (size ltws)) us
    by rewrite qflat_rcons add0n /qblk /= hszE.
  split=> //; split=> //.
  exists (rcons CS ((t, (sg, md)), us)); rewrite hqf.
  split.
  { rewrite hszE.
    have hsgE : sg = wsigs (lcoord t) pp 0
                       (l_rrdigS (lcoord t) pp md (size CS)) us
      by rewrite /sg hszE.
    exact: (RPr_qupd pp CS (get_heap s0 Ltg) (get_heap s1 rpr_tgts_loc)
              t sg md us hRPr' husl hsgE). }
  { by rewrite map_rcons -hltwE. }
  { by []. }
  { by []. }
  by rewrite size_cat
       (size_lchain_block (lcoord t) 0 (l_rrdigS (lcoord t) pp md (size ltws))
          us hus) lnpqE.
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rpr_pp_loc := Some b ;; #put rpr_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (pr_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK — ideal endpoint: G1l' answers [ret false]; every R branch is
     [false] on SMB false (resolve_lpr_ck_false). *)
  destruct arg as [j mw].
  ssprove_code_simpl; simpl.
  eapply r_get_remember_rhs => rrev.
  case: rrev; last first.
  { ssprove_code_simpl; simpl; rewrite resolve_lpr_ck_false bind_ret_l;
    apply r_ret => s0 s1 [hinv _]; by split. }
  ssprove_code_simpl; simpl.
  eapply r_get_remember_rhs => rtg.
  case E: (getm rtg j) => [[t0 [[[sg md0] copt] ofs]]|]; last first.
  { ssprove_code_simpl; apply r_ret => s0 s1 [[hinv _] _]; by split. }
  ssprove_code_simpl; simpl.
  eapply r_get_remember_rhs => rpp.
  eapply (r_fact (exists pp, rpp = Some pp)).
    { move=> s0 s1 [[[hinv hrev] hrtg] hrpp].
      rewrite /rem_inv /= in hrev hrtg hrpp.
      case/pr_invE: hinv => _ [hrtw hrrv hrsl hrpp' [hspp hsrv hm]].
      have hlrv : get_heap s0 Lrv = true by rewrite -hrrv hrev.
      move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
      - exists pp; by rewrite -hrpp hrpp' hlrv El.
      - case: hm => hltg hrtgemp _; move: E; rewrite -hrtg hrtgemp emptymE => Hx;
           discriminate Hx. }
  move=> [pp ->].
  rewrite bind_ret_l.
  case: (lpr_pd pp t0 sg md0 j mw) => [[jc x0]|];
    last by apply r_ret => s0 s1 [[[hinv _] _] _]; split.
  case: (lpr_v pp t0 sg md0 copt j mw);
    last by apply r_ret => s0 s1 [[[hinv _] _] _]; split.
  ssprove_code_simpl; simpl; rewrite resolve_lpr_ck_false bind_ret_l;
    apply r_ret => s0 s1 [[[hinv _] _] _]; by split.
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/pr_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  rewrite ?code_link_assertD.
  eapply r_assertD_same => _.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  - eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => CS [hRPr _ _ _ _].
          case: hRPr => hl hr _.
          by move: (hr j); rewrite -hr3; move: (hl j); rewrite hr2 E;
             case: ifP => _ // -[?].
        - case: hm => hltg hrtg _; by rewrite -hr3 hrtg emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp ofs, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0, ofs)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr2 hr3 hr4.
        case/pr_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => CS [hRPr _ _ _ _].
          case: hRPr => hl hr _.
          have hjs : (j < size CS)%N.
            by move: (hl j); rewrite hr2 E; case: ifP => // _ [].
          exists pp, (size (qflat pp 0 (take j CS))); split; first by rewrite -hr4.
          move: (hr j); rewrite hjs -hr3 => ->.
          move: (hl j); rewrite hr2 E hjs => -[hnth].
          by rewrite -hnth.
        - case: hm => hltg _ _; move: E; rewrite -hr2 hltg emptymE => H;
             discriminate H. }
    move=> [pp [ofs [hlpp hrtgj]]].
    rewrite hlpp hrtgj /=.
    case E2: (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0) => [c|].
    + apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
      rewrite /rem_inv /= in hr0 hr1.
      subst s0 s1; split=> //.
      exact: (pr_inv_setsl (rcons slog j) s0' s1' hinv).
    + apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inr (inl xy))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inr (inr dc))))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
Qed.

(** sub_cpre : the CHAIN-PRE step of the ladder. *)
Lemma sub_cpre (hw : (0 < w)%N) (B : nom_package)
    (VB : ValidPackage (loc B) IKM A_export B) :
  Adv GM3 G1L B = AdvOf (SMPRE_game TFl CFl_leaf q2) (B ∘ R_cpre_leaf).
Proof.
rewrite (Adv_perfect_l (R_cpre_leaf_real hw)).
rewrite (Adv_perfect_r (R_cpre_leaf_ideal hw)).
by rewrite Adv_reduction.
Qed.

End Leaf2ChainPRE.
