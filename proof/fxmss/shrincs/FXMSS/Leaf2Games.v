(** * SHRINCS.FXMSS.Leaf2Games
    (M1a re-landing, WLOG_DESIGN.md + FXMSS_FINISH_PLAN.md)

    The CONCRETE intermediate games for the FXMSS leaf hop LAYER (ii), over the
    STATIC-GATE EU-CMA endpoint game [MIW_kmS] (FXMSS.LeafKM, the banked M0
    WLOG fix).  These are the multi-instance lift of the WOTSC_secure ladder
    (WOTSC/{Theorem,GrindHop,CompressHop,ChainHop,UDHop}.v) to ALL leaves, with
    the digest carried at LCOMMIT (the digest-at-commit boundary [I_MIW_km]).

    The ladder these games realise:

      MIW_kmS true -[UD up]-> G1l -[GRIND]-> Glmid1 -[COMPRESS]-> Glmid2
        -[CHAIN-TCR]-> Glmid3 -[CHAIN-PRE]-> G1l' -[UD down]-> MIW_kmS false.

    The five intermediate games SHARE the re-rooted COMMIT / SIGN / GETPP / COLLQ
    machinery and differ ONLY in their LCHECK win predicate:

    - LCOMMIT ([rr_commit]) is the SLOT-KEYED STATIC re-root: it pins [pp]
      first (the re-root digit needs it), then SAMPLES the signature roots
      re-rooted at the STATIC digit [rr_digitS pp t md (size tws)] -- the
      [find_ctr]-conditional digit [digest_of(md, find_ctr md)] /
      [nseq l w.-1] for an IN-BUDGET slot ([size tws < q_s]), the VIRTUAL
      digit [nseq l w.-1] UNCONDITIONALLY for an out-of-budget slot (it can
      never be signed: the LSIGN budget guard).  The roots [sg] are stored in
      the tgts record in place of the key; the returned pk is the re-rooted
      Theta_l compression [rr_pkS].  Re-root at ANY digit is a legitimate
      G0->G1 SM-UD endpoint because the leaf pk is digest-INDEPENDENT.

    - LSIGN ([rr_sign]) carries [mkm_signS]'s budget guard ([q_s <= j] =>
      None); within budget it reveals the re-rooted roots [sg] DIRECTLY at the
      signed counter for a grindable leaf (no F-inversion), and None for a
      non-grindable leaf ([find_ctr = None]) -- consistent with the virtual
      re-root.

    - LCHECK ([rr_winbody P]) is the re-rooted Section-1.4-GUARDED "verify"
      [wots_checks && (recover_anchor == rr_pkS)] under the STATIC WLOG gate
      [gateS = (q_s <= j) || ~~grindable(md0) || (mw.1 != md0)] (mkm_winSG's
      gate, threaded through every intermediate game), with the Gmid-style
      nulling discriminants cascaded: G1l keeps the full win; Glmid1 also
      nulls the GRIND case ([grind_hitS]: in-budget grindable leaf, forged
      digit vector coincides with the re-rooted committed one); Glmid2 also
      nulls the COMPRESS case; Glmid3 also nulls the CHAIN-TCR case; G1l'
      answers false (the b=false endpoint).

    MACHINERY THAT DROPPED with the single (static) population (M1a):
    - the ADAPTIVE slog-gate [(j \notin slog) || ...] from EVERY win
      predicate -- [rr_winbody] no longer reads [miw_slog_loc]; the slog
      survives only as LSIGN's one-time guard;
    - the (C1) enc-pair-freshness disjunct and the slog disjunct of the old
      [grind_hit] -- [grind_hitS] reverts to WOTSC's simple form
      [(j < q_s) && grindable && (fdv == rr_digitS)]: freshness of the routed
      STCRP enc-pair is FORCED by [gateS] on every pop-1 survivor
      (LeafKM.stcrp_fresh_forced), and same-digest wins are dead at the TOP
      of the ladder ([flavourA_dead_g1lS] below);
    - the contemplated (C2) extended equal-digit classifier (unnecessary:
      [gateS] kills the same-digest flavours A and B AND the same-digest
      Theta_l collision);
    - the adaptive 2-population reduction branching -- the population split
      is the STATIC commit-time boolean [(j < q_s) && grindable],
      case-analysed in PROOFS only; the WOTSC_zero package layer
      (ZeroGames/ZeroUDHop/ZeroChainHop) is NOT instantiated (the virtual
      digit makes [pre_decision] specialize to the zero-query endpoint
      placement -- WLOG_DESIGN.md probes E/F/F'/G).

    The population is covered by this single 6-term ladder: pop-1 =
    in-budget grindable leaves (used-instance WOTSC_secure treatment, signed
    digit re-root, digest freshness via [gateS]); pop-2 = everything else
    (zero-query treatment, virtual re-root, bare opening).

    STATUS: the games are admit-free with their [ValidPackage] (DIRECTED
    [valid_package_cons], no [ssprove_valid] search).  The obstruction
    regression witnesses ([flavourA_dead_g1lS] / [flavourA_dead_gm3S] /
    [obstruction_input_dead], superseding the old [f4_obstruction_fixed])
    are Qed at the end of the file.  The six sub-bounds are the SEPARATE
    milestones M1b-e / M2. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From HBS Require Import Prelude Math.BinTree Math.Merkle Math.Chain Math.Encoding
  Sig.Scheme Games.THF Games.SMTCR Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Games FixedSumOTS.TCRHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames FXMSS.TreeHop
  FXMSS.LeafReduction FXMSS.LeafKM FXMSS.Leaf2Common.
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Leaf2Games.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same DATA-ONLY section context as FXMSS/LeafKM.v. *)
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
(** ** Shorthands (LeafKM's).  [lcoord] (= adrs_keypair o decode, no section
    args) and the static gate [gateS] are CONSUMED from FXMSS.LeafKM (the
    banked M0 endpoint), so endpoint and ladder share the literal gate. *)

Local Notation lcoord t := (@LeafKM.lcoord w l t).
Local Notation lpk := (leaf_pk_c PP N F Tl).
Local Notation lrc := (leaf_rec_c PP N D F Tl Hgrind).

Local Notation Lpp  := (miw_pp_loc PP).
Local Notation Ltw  := (@miw_tws_loc w l).
Local Notation Lrv  := miw_rev_loc.
Local Notation Lsl  := miw_slog_loc.
Local Notation Ltg  := (@mkm_tgts_loc w l N D).
Local Notation IKM  := (@I_MIW_km w l PP N D).

Local Notation MKMLocs :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ].

Local Notation lfind t0 pp md0 :=
  (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0).

(** The LIFTED (budget-free) WLOG gate (LeafKM.gateL at this section's data):
    the [(q_s <= j)] disjunct is DELETED -- pop-1 = "committed digest
    grindable", commit-static, no budget, no slog. *)
Local Notation gateL := (LeafKM.gateL PP D Hgrind S_wn c_max).

(** The pk-compression (coordinate-level) tweak: the multi-target freshness the
    layer-(ii) SM-* reductions match against ([gtw_of t \notin map gtw_of tws]).
    [adrs_keypair] collapses every address sharing the leaf coordinate onto the
    same [AdrPk] tweak, so a generic adversary cannot commit two distinct full
    tweaks with the same coordinate; the real composed adversary commits only
    distinct leaf pk-anchors, on which [gtw_of] is the identity. *)
Local Notation gtw_of t :=
  (@encode_adrs l w (@wotsc_pk_adrs l w (lcoord t))).

(** The find_ctr-conditional re-root digit vector (the UNDERLYING in-budget
    digit): the SIGNED digits when grinding succeeds, else the VIRTUAL digit
    (WOTSC_zero G1z style). *)
Definition rr_digit (pp : PP) (t : adrs_sf_ch) (md : D) : seq nat :=
  match find_ctr PP D Hgrind S_wn c_max (lcoord t).1 (lcoord t).2 pp md with
  | Some c => digest_of PP D Hgrind (lcoord t).1 (lcoord t).2 pp md c
  | None => nseq l w.-1
  end.

(** The re-root digit at ANY slot (LIFT: the [j < q_s] budget wrapper is
    DROPPED).  Under the adversary-chosen-leaf-id lift every leaf carries a
    real committed digest, so re-root is find_ctr-conditional at EVERY slot;
    the [find_ctr]-conditional [rr_digit] already virtualizes the
    non-grindable case (yielding [nseq l w.-1]).  The [j] parameter is kept
    for interface stability (rr_pkS / rcvS / grind_hitS thread it) but is
    now vestigial. *)
Definition rr_digitS (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat) : seq nat :=
  rr_digit pp t md.

(** The address-wrapped chain hash at the leaf coordinate. *)
Definition rr_F (t : adrs_sf_ch) : PP -> nat * nat -> N -> N :=
  Fw PP N F (lcoord t).1 (lcoord t).2.

(** The re-rooted pk: Theta_l compression of the completed re-rooted ends at
    the slot-keyed digit. *)
Definition rr_pkS (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat)
    (sg : seq N) : N :=
  Tl pp (wotsc_pk_adrs (lcoord t))
     (complete_ends PP N F (lcoord t).1 (lcoord t).2 pp
        (rr_digitS pp t md j) sg).

(* ------------------------------------------------------------------ *)
(** ** Shared re-rooted oracle bodies. *)

(** LCOMMIT, re-rooted: pp pinned first (the re-root digit needs it), then the
    signature roots are SAMPLED re-rooted at the slot-keyed static digit
    position; the roots [sg] are stored in the tgts record in place of the key,
    and the public key returned is the re-rooted compression. *)
Definition rr_commit (t : adrs_sf_ch) (md : D) : raw_code N :=
  (revealed ← get Lrv ;;
   #assert ~~ revealed ;;
   tws ← get Ltw ;;
   #assert (size tws < n_max)%N ;;
   #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
   ppo ← get Lpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
        end ;;
   sg ← sample_sig_roots PP N (rr_F t) dN pp 0 (rr_digitS pp t md (size tws)) ;;
   tgts ← get Ltg ;;
   #put Ltg := setm tgts (size tws) (t, (sg, md)) ;;
   #put Ltw := rcons tws t ;;
   ret (rr_pkS pp t md (size tws) sg)).

(** LSIGN, re-rooted, ONE-TIME-GUARDED (LIFT: the [j < q_s] outer budget guard
    is DROPPED -- the budget lives only in the composed SIGN's dynamic refusal,
    never in this [forall B] game; only the one-time slog assert survives).  A
    grindable leaf reveals the re-rooted roots [sg] DIRECTLY at the signed
    counter (resolving the 6th subtlety: no F-inversion); a non-grindable leaf
    returns None (consistent with the virtual re-root). *)
Definition rr_sign (j : nat) : raw_code ('option (('list N) × 'nat)) :=
  (slog ← get Lsl ;;
   #assert (j \notin slog) ;;
   tgts ← get Ltg ;;
   match getm tgts j with
   | Some (t0, (sg, md0)) =>
       ppo ← get Lpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
            end ;;
       match find_ctr PP D Hgrind S_wn c_max
               (lcoord t0).1 (lcoord t0).2 pp md0 with
       | Some c => #put Lsl := rcons slog j ;; ret (Some (sg, c))
       | None => ret None
       end
   | None => ret None
   end).

(** The LCHECK body shape: identical plumbing for every intermediate game; the
    games differ ONLY in the pure win predicate [P].  NB no [Lsl] read: the
    predicates are slog-FREE (the static gate). *)
Definition rr_winbody
    (P : PP -> adrs_sf_ch -> seq N -> D -> nat ->
         (D × (('list N) × 'nat)) -> bool)
    (j : nat) (mw : D × (('list N) × 'nat)) : raw_code 'bool :=
  (revealed ← get Lrv ;;
   #assert revealed ;;
   tgts ← get Ltg ;;
   match getm tgts j with
   | Some (t0, (sg, md0)) =>
       ppo ← get Lpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
            end ;;
       ret (P pp t0 sg md0 j mw)
   | None => ret false
   end).

(* ------------------------------------------------------------------ *)
(** ** The pure win predicates (the re-rooted guarded "verify" + static gate
    + nulls). *)

(** Recovered anchor of the forgery; forged/re-rooted digit vectors and
    completed-ends (slot-keyed). *)
Local Notation lrcv pp t0 mw := (lrc pp t0 mw.1 mw.2).
Local Notation fdv pp t0 mw :=
  (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2).
Local Notation fcv pp t0 mw :=
  (complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp (fdv pp t0 mw) mw.2.1).
Local Notation rcvS pp t0 sg md0 j :=
  (complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp
     (rr_digitS pp t0 md0 j) sg).

(** The §1.4 [wots_checks] validity guard at the leaf coordinate (= the
    WOTS+C side checks [valid_digest] + size of the flexible verifier,
    FXMSS.Scheme.wots_checks).  This is exactly [fx_verify]'s validity
    conjunct, evaluated on the FORGED digest/signature [(mw.1, mw.2)]. *)
Local Notation vchecks pp t0 mw :=
  (wots_checks PP N D Hgrind S_wn pp (lcoord t0) mw.1 mw.2).

(** The re-rooted "verify": the §1.4-GUARDED anchor equality.  By the banked
    [verify_sigE] this is exactly [verify_sig … rr_pkS] = [wots_checks &&
    (recover_anchor == rr_pkS)].  The guard is load-bearing for the TERMINAL
    CHAIN-PRE hop (it kills the degenerate all-max-digit virtual-digit win:
    under [S_wn != l*w.-1] the all-max [fdv] fails [valid_digest]); it CANCELS
    in the NON-terminal hops (COMPRESS/CHAIN-TCR/GRIND/UD), where the extra
    conjunct sits identically in both consecutive win predicates. *)
Local Notation verokS pp t0 sg md0 j mw :=
  ((vchecks pp t0 mw && (lrcv pp t0 mw == rr_pkS pp t0 md0 j sg))%bool).

(** Grindability of the committed digest: whether the leaf carries a REAL grind
    target.  Pop-1 = [(j < q_s) && grindable] (SQUERY-ied by the STCRP
    reduction, signed-digit re-root); pop-2 = everything else (virtual re-root,
    NO STCRP target). *)
Local Notation grindable pp t0 md0 :=
  (isSome (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0)).

(** The GRIND-collision null discriminant (WOTSC Gmid1's simple unconditional
    form, restored by the WLOG): it fires iff the leaf is pop-1 (in-budget AND
    grindable -- a real STCRP target exists) and the forged digit vector
    coincides with the re-rooted committed one ([fdv == rr_digitS], the Hgrind
    digit collision after [wdigest_inj]).  NO enc-pair-freshness disjunct and
    NO slog disjunct (dropped C1/slog-gate): on any pop-1 survivor of [gateS]
    the routed STCRP enc-pair is fresh AUTOMATICALLY
    (LeafKM.stcrp_fresh_forced), and pop-2 leaves are never routed (their
    conjunct [(j < q_s) && grindable] is false). *)
Definition grind_hitS (pp : PP) (t0 : adrs_sf_ch) (md0 : D) (j : nat)
    (mw : D × (('list N) × 'nat)) : bool :=
  (grindable pp t0 md0 && (fdv pp t0 mw == rr_digitS pp t0 md0 j))%bool.

(** G1l (= multi-instance G1w-true): the full re-rooted guarded win under the
    static gate.  SAME SHAPE as the endpoint's [mkm_winSG] answer
    ([wots_checks && anchor-eq && gateS]) -- the M2 UD legs couple these
    directly. *)
Definition P_g1lS (pp : PP) (t0 : adrs_sf_ch) (sg : seq N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) : bool :=
  (verokS pp t0 sg md0 j mw && gateL pp t0 md0 mw.1)%bool.

(** Glmid1 (= multi-instance Gmid1): also null the GRIND case. *)
Definition P_gm1S (pp : PP) (t0 : adrs_sf_ch) (sg : seq N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) : bool :=
  ([&& verokS pp t0 sg md0 j mw, gateL pp t0 md0 mw.1
    & ~~ grind_hitS pp t0 md0 j mw])%bool.

(** Glmid2 (= multi-instance Gmid2): also null the COMPRESS case (forged
    completed ends differ from the re-rooted ends; the SM-TCR(Theta_l)
    freshness [fcv != rcvS] is self-contained -- the pk-compression target is
    committed for EVERY leaf). *)
Definition P_gm2S (pp : PP) (t0 : adrs_sf_ch) (sg : seq N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) : bool :=
  ([&& verokS pp t0 sg md0 j mw, gateL pp t0 md0 mw.1,
      ~~ grind_hitS pp t0 md0 j mw
    & fcv pp t0 mw == rcvS pp t0 sg md0 j])%bool.

(** Glmid3 (= multi-instance Gmid3): also null the CHAIN-TCR case (the shared
    F-collision classifier fires; the classifier structurally never fires at
    the virtual digit -- WLOG_DESIGN.md probe G -- so virtual leaves commit no
    SM-TCR(F) targets). *)
Definition P_gm3S (pp : PP) (t0 : adrs_sf_ch) (sg : seq N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) : bool :=
  ([&& verokS pp t0 sg md0 j mw, gateL pp t0 md0 mw.1,
      ~~ grind_hitS pp t0 md0 j mw,
      fcv pp t0 mw == rcvS pp t0 sg md0 j
    & ~~ isSome (tcr_decision PP N (rr_F t0) l w pp
                   (rr_digitS pp t0 md0 j) (fdv pp t0 mw) sg mw.2.1)])%bool.

(* ------------------------------------------------------------------ *)
(** ** ValidCode of the shared bodies (directed; over MKMLocs). *)

#[local] Instance rr_commit_valid (I : Interface) (t : adrs_sf_ch) (md : D) :
  ValidCode MKMLocs I (rr_commit t md).
Proof.
rewrite /rr_commit.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tws.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp.
eapply valid_bind; first by apply sample_sig_roots_valid. move=> sg.
eapply valid_getr; first by fmap_solve. move=> tgts.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[local] Instance rr_sign_valid (I : Interface) (j : nat) :
  ValidCode MKMLocs I (rr_sign j).
Proof.
rewrite /rr_sign.
eapply valid_getr; first by fmap_solve. move=> slog.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 [sg md0]]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp.
case: (find_ctr _ _ _ _ _ _ _ _ _) => [c|]; last by apply valid_ret.
eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[local] Instance rr_winbody_valid (I : Interface) P (j : nat)
    (mw : D × (('list N) × 'nat)) :
  ValidCode MKMLocs I (rr_winbody P j mw).
Proof.
rewrite /rr_winbody.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 [sg md0]]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Arguments rr_commit : simpl never.
#[local] Arguments rr_sign : simpl never.
#[local] Arguments rr_winbody : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The concrete intermediate games (directed valid_package_cons). *)

(** A uniform builder: a game with the shared re-root COMMIT/LSIGN/LGETPP/LCOLLQ
    and a given LCHECK body [chk]. *)
Definition mk_game (chk : nat -> (D × (('list N) × 'nat)) -> raw_code 'bool)
    (Hchk : forall (I : Interface) j mw, ValidCode MKMLocs I (chk j mw)) :
    game IKM.
Proof.
notypeclasses refine [package MKMLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) { rr_commit t md } ;
    [ LGETPP ] : { 'unit ~> PP } (_) { mkm_getpp PP dPP } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      chk j mw } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) { rr_sign j } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      mkm_collq PP N D Hgrind Htree dPP t x }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { eapply valid_package_cons.
        { apply: valid_empty_package. }
        { intros [t x]; exact: mkm_collq_valid. } }
      { intro j; exact: rr_sign_valid. } }
    { intros [j mw]; exact: (Hchk _ j mw). } }
  { intro u; exact: mkm_getpp_valid. } }
{ intros [t md]; exact: rr_commit_valid. }
Defined.

(** The five intermediate games of the ladder. *)
Definition G1l : game IKM :=
  mk_game (rr_winbody P_g1lS) (fun I j mw => rr_winbody_valid I P_g1lS j mw).
Definition Glmid1 : game IKM :=
  mk_game (rr_winbody P_gm1S) (fun I j mw => rr_winbody_valid I P_gm1S j mw).
Definition Glmid2 : game IKM :=
  mk_game (rr_winbody P_gm2S) (fun I j mw => rr_winbody_valid I P_gm2S j mw).
Definition Glmid3 : game IKM :=
  mk_game (rr_winbody P_gm3S) (fun I j mw => rr_winbody_valid I P_gm3S j mw).
Definition G1l' : game IKM :=
  mk_game (fun _ _ => ret false) (fun I j mw => valid_ret MKMLocs I false).

(* ------------------------------------------------------------------ *)
(** ** Obstruction regression witnesses (probe D of WLOG_DESIGN.md,
    superseding the old [f4_obstruction_fixed]).

    The F4/F5 obstruction was the flavour-A input -- a GRINDABLE leaf
    re-submitting its own committed enc-pair [mw = (md0,(sg,c))] with
    [find_ctr md0 = Some c]: the OLD slog-gated [P_gm3] accepted it on a
    never-signed leaf while the terminal [pre_decision] returned [None]
    ([fdv = rr_digit] advances NO chain) -- non-routable, and its F5
    relocation poisoned the GRIND real perfect.  Under the STATIC gate ANY
    same-digest forgery at an in-budget grindable leaf is dead at the TOP of
    the ladder (before any null), and out-of-budget/non-grindable leaves are
    virtual (an all-max [fdv] fails the §1.4 guard under [Hdeg], probes
    E/F/F').  These witnesses pin the design. *)

Lemma flavourA_dead_g1lS (pp : PP) (t0 : adrs_sf_ch) (sg : seq N)
    (md0 : D) (c : nat) (j : nat) (mw : D × (('list N) × 'nat)) :
  lfind t0 pp md0 = Some c ->
  mw.1 = md0 ->
  P_g1lS pp t0 sg md0 j mw = false.
Proof.
move=> hfc h1.
by rewrite /P_g1lS h1
   (gateL_same_digest_dead PP D Hgrind S_wn c_max pp t0 md0 c hfc)
   andbF.
Qed.

Lemma flavourA_dead_gm3S (pp : PP) (t0 : adrs_sf_ch) (sg : seq N)
    (md0 : D) (c : nat) (j : nat) (mw : D × (('list N) × 'nat)) :
  lfind t0 pp md0 = Some c ->
  mw.1 = md0 ->
  P_gm3S pp t0 sg md0 j mw = false.
Proof.
move=> hfc h1.
by rewrite /P_gm3S h1
   (gateL_same_digest_dead PP D Hgrind S_wn c_max pp t0 md0 c hfc)
   /= !andbF.
Qed.

(** The EXACT (old) Leaf2ChainPRE.obstruction_probe input, dead at the
    terminal for ANY j in budget -- and independent of any slog state (the
    predicates no longer read slog). *)
Lemma obstruction_input_dead (pp : PP) (t0 : adrs_sf_ch) (md0 : D)
    (c : nat) (sg : seq N) (j : nat) :
  lfind t0 pp md0 = Some c ->
  P_gm3S pp t0 sg md0 j (md0, (sg, c)) = false.
Proof.
move=> hfc.
by apply: flavourA_dead_gm3S; [exact: hfc |].
Qed.

End Leaf2Games.
