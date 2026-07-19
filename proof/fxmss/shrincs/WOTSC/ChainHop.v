(** * SHRINCS.WOTSC.ChainHop

    The chain-level SM-TCR(F) and SM-PRE(F) hops of the WOTS+C
    one-time security proof (P5; plan in
    theories/SHRINCS/WOTSC/PROOF_PLAN.md): the LAST TWO splits of the
    forgery analysis, from [Gmid2] (CompressHop.v) to G1w-ideal.
    These are the WOTSC ports of FixedSumOTS.{TCRHop, PREHop} at the
    address-wrapped chain hash [Fw].  Delivered:

      [R_ctcr_real  : perfect (I_KOTS WC) Gmid2
                              (R_ctcr ∘ SMTCR_game Tf Cf (p_tcr l w) true)]
      [R_ctcr_ideal : perfect (I_KOTS WC) Gmid3
                              (R_ctcr ∘ SMTCR_game Tf Cf (p_tcr l w) false)]
      [R_cpre_real  : perfect (I_KOTS WC) Gmid3
                              (R_cpre ∘ SMPRE_game Tf Cf l true)]
      [R_cpre_ideal : perfect (I_KOTS WC) (G1w ... false)
                              (R_cpre ∘ SMPRE_game Tf Cf l false)]

    where [Gmid3] is [Gmid2] with KFORGE ALSO answering false on the
    CHAIN-COLLISION case: in the CHAIN branch (digit vectors differ,
    completed ends equal) it re-runs the per-chain classifier — the
    SHARED computable decision function [tcr_decision] of
    FixedSumOTS.TCRHop, instantiated at [Fw] — and nulls the
    [Some]-answers (ChainColl), keeping [true] on [None] (ChainMeet).
    Consumer triangle steps:
      [Adv Gmid2 Gmid3 <= AdvOf (SMTCR_game Tf Cf (p_tcr l w)) (A ∘ R_ctcr)]
      [Adv Gmid3 (G1w false) <= AdvOf (SMPRE_game Tf Cf l) (A ∘ R_cpre)].

    ** Design (the FixedSumOTS ports, with the WOTSC deltas)

    - SHARED tweak space: the SM-TCR/SM-PRE games run on [Tf]
      (Games.v), whose tweaks are ENCODED stateful addresses
      [adrs_sf_ch].  All chain bookkeeping is REUSED from
      FixedSumOTS.TCRHop/PREHop over abstract (chain, position) pairs
      and re-tagged through [wq q := (wotsc_tweak q.1, q.2)]
      (injective re-tagging: list POSITIONS — the CHECK indices — are
      unchanged, and tweak freshness transfers along
      [wotsc_tweak_inj]).
    - SHARED classifier: [tcr_decision PP N FW l w] /
      [pre_decision PP N FW l w] (FixedSumOTS.TCRHop/PREHop at [Fw])
      are the EXACT discriminants of Gmid3, R_ctcr and R_cpre, so the
      KFORGE case analyses align syntactically.  Their specs are
      lifted to WOTSC hypotheses once ([wtcr_decisionP],
      [wpre_decisionP], [wclassify_some]) via [verify_from_ends]: in
      the CHAIN branch the discriminants already provide a verifying
      FixedSumOTS forgery against the honest [ends_from_sig] key (the
      forged digest is valid and its completed ends HIT the honest
      ones), and digit-vector freshness is the E1 discriminant.
    - R_ctcr COMMIT (budget p = [p_tcr l w] = l + l*w: per chain one
      sigma query for a positive digit plus at most w walk queries,
      [nqs_le]): one-shot guard; ONE unguarded COLLQ at the grinding
      address pins SM-TCR's lazy pp against Gmid2's eager one
      (CompressHop's pin — NO [0 < l]/[1 < w] side conditions, unlike
      FixedSumOTS.TCRHop's first-TQUERY swap); the grinding through
      COLLQ ([ct_grind] + the pure [cp_pick] of CompressHop, REUSED);
      per chain: root sampled LOCALLY, sigma step and the
      k = d_i..w-2 walk VIA TQUERY at encoded chain addresses
      (TCRHop's interleaved per-chain commit order, [commit_queries]/
      [q_index] bookkeeping reused at [Fw]); all TQUERYs done, then
      GETPP and the PURE pk compression [Tl pp padrs ends] (Tl needs
      pp; computing it after GETPP avoids a COLLQ whose [inl]-branch
      would need an inhabitant of N).
    - R_ctcr KFORGE: verify+freshness; GRIND (digit vectors equal) →
      false (both Gmid2 and Gmid3 null it); COMPRESS (completed ends
      differ) → false (both null it; NO oracle call needed since
      Gmid2 already answers false there); CHAIN → run the classifier:
      ChainColl (j, u) → CHECK (j, u) (real: wins by
      [wtcr_decisionP] + the committed-target bookkeeping = Gmid2's
      true; ideal: false = Gmid3's null); ChainMeet → true.
    - R_cpre COMMIT (budget l: one PQUERY per positive-digit chain,
      [npq_le]): one-shot guard; PCOLLQ pin; grinding through PCOLLQ;
      per chain with digit d_i >= 1: sigma via
      [PQUERY (encode_adrs (chain_adrs i (d_i - 1)))] — the oracle's
      hidden uniform IS G1w's re-rooted sample; d_i = 0: local [dN];
      then PGETPP + PURE completion/compression.
    - R_cpre KFORGE: GRIND/COMPRESS/ChainColl → false; ChainMeet at
      chain i → PCHECK ([pre_index], forged preimage) (real: wins by
      [wpre_decisionP] = Gmid3's true; ideal: false = G1w-ideal);
      the (ChainColl = None ∧ ChainMeet = None) branch returns true —
      on the real side that MATCHES Gmid3, on the ideal side it is
      DEAD ([wclassify_some]).  Pre-commitment KFORGE gadget: Gmid3
      fails (getSome) where G1w-ideal returns false, and the only
      b-dependent oracle is PCHECK, so KFORGE calls [PCHECK (0, n0)]
      pre-commitment — whence the SECTION PARAMETER [n0 : N]
      (DOCUMENTED side condition, exactly FixedSumOTS.PREHop's;
      data-only, trivially discharged at instantiation where N is an
      n-byte-string type).  No other side conditions: no [Hrange] (no
      digit decoding), no [0 < l]/[1 < w] (COLLQ pin), no losslessness.

    ** Invariants

    One per reduction, each serving BOTH its real and ideal lemma
    (the lhs games Gmid2/Gmid3/G1w share locations 300-302 and their
    COMMITs are verbatim equal): [heap_ignore] over all ten private
    locations ⋊ one [rel_app] relation — pk/log/sig mirrored, and R's
    pk [None] ⇒ game state initial, [Some pk] ⇒ ∃ m c us (us the
    sampled roots resp. the oracle's hidden inputs):
    log = [:: m], stored signature = ([sigs_of] at [Fw] of us, c),
    pp pinned to pk.1, size us = l, grinding success [good_ctr],
    committed targets = the re-tagged [commit_queries] (TCR) resp.
    [pre_queries] (PRE), phase revealed.

    Locations 350-352 (R_ctcr) and 360-362 (R_cpre); ids 350+ per the
    plan (WOTSC.UDHop sits at 310-315, GrindHop at 330-332,
    CompressHop at 340-342). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp.experimental_reals Require Import distr.
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Games.SMTCR Games.SMPRE Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop FixedSumOTS.PREHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis
  WOTSC.GrindHop WOTSC.CompressHop.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** [qnth] through a map (companion to TCRHop's [qnth_cat_l/r]) *)

Lemma qnth_map {X Y : Type} (f : X -> Y) (s : seq X) (i : nat) :
  qnth [seq f x | x <- s] i = omap f (qnth s i).
Proof. by rewrite /qnth -map_drop; case: (drop i s). Qed.

Section ChainHop.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same section context as WOTSC.Games minus the dummy message
    sampler [dM] (only [Tgr] needs it), plus the hash-domain
    inhabitant [n0] for the pre-commitment PCHECK gadget of [R_cpre]
    (header; data-only, the FixedSumOTS.PREHop side condition). *)
Context (PP N M : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).
Context (dPP : dist PP) (dN : dist N).
Context (S_wn c_max : nat).
Context (zstar istar : nat).
Context (n0 : N).
Context (Hanchor : anchor_bounded (zstar, istar)).
Context (hw : (0 < w)%N).

Local Notation WC :=
  (WOTSC PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation TF := (Tf PP N F dPP dN).
Local Notation CF := (Cf PP N M F Tl Hgrind dPP dN).
Local Notation SMT b := (SMTCR_game TF CF (p_tcr l w) b).
Local Notation SMP b := (SMPRE_game TF CF l b).
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation cadrs := (chain_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation gtw := (encode_adrs gadrs).
Local Notation ctw i k := (encode_adrs (cadrs i k)).
Local Notation wtw := (@wotsc_tweak w l zstar istar).
Local Notation FW := (Fw PP N F zstar istar).
Local Notation cfW := (HBS.Examples.FixedSumOTS.Scheme.chainf PP N FW).
Local Notation wdigest := (digest_of PP M Hgrind zstar istar).
Local Notation wfind_ctr :=
  (find_ctr PP M Hgrind S_wn c_max zstar istar).
Local Notation wgood := (good_ctr PP M Hgrind S_wn zstar istar).
Local Notation wcends := (complete_ends PP N F zstar istar).
Local Notation wverify :=
  (verify_sig PP N M F Tl Hgrind S_wn zstar istar).
Local Notation wsigs := (sigs_of PP N FW).
Local Notation wends := (ends_of PP N FW w).
Local Notation wpick := (@cp_pick w l S_wn c_max).
Local Notation vdigest := (@valid_digest w S_wn).
Local Notation wcommitq := (commit_queries PP N FW w).
Local Notation wpreq := (pre_queries N).
Local Notation wtcr_dec := (tcr_decision PP N FW l w).
Local Notation wpre_dec := (pre_decision PP N FW l w).
Local Notation fsverify :=
  (HBS.Examples.FixedSumOTS.Scheme.verify_sig PP N FW l w S_wn).
Local Notation fsvalid := (valid_msg l w S_wn).
Local Notation efs := (ends_from_sig PP N FW l w).
Local Notation GM2 :=
  (Gmid2 PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation G1W :=
  (G1w PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).

Local Notation pk_loc' :=
  (g0w_pk_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation log_loc' :=
  (g0w_log_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation sig_loc' :=
  (g0w_sig_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation tpp_loc := (tcr_pp_loc TF).
Local Notation ttgts_loc := (tcr_tgts_loc TF).
Local Notation ttws_loc := (tcr_tws_loc TF).
Local Notation trev_loc := tcr_rev_loc.
Local Notation ppp_loc := (pre_pp_loc TF).
Local Notation ptgts_loc := (pre_tgts_loc TF).
Local Notation ptws_loc := (pre_tws_loc TF).
Local Notation prev_loc := pre_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the re-tagging into encoded tweaks

    The FixedSumOTS bookkeeping lists ([commit_queries],
    [pre_queries]) live over abstract (chain, position) tweaks; the
    SM-TCR/SM-PRE games on [Tf] store ENCODED addresses.  [wq]
    re-tags one committed entry; positions are untouched, so all
    indices ([q_index], [pre_index]) are consumed unchanged. *)

Local Notation qentry := ((nat * nat) * N)%type.

Definition wq (q : qentry) : adrs_sf_ch * N := (wtw q.1, q.2).

(** [unzip1] commutes with the re-tagging. *)
Lemma unzip1_wq (Q : seq qentry) :
  unzip1 [seq wq q | q <- Q] = [seq wtw t | t <- unzip1 Q].
Proof. by rewrite /unzip1 -!map_comp; apply: eq_map => q. Qed.

(** Freshness transfers along the injective re-tagging for representable
    chain coordinates. *)
Lemma wtw_notin (t : nat * nat) (ts : seq (nat * nat)) :
  anchor_bounded (zstar, istar) ->
  t.1 < l -> t.2 < w.-1 ->
  (forall t', t' \in ts -> t'.1 < l /\ t'.2 < w.-1) ->
  t \notin ts -> wtw t \notin [seq wtw t' | t' <- ts].
Proof.
move=> ha ht1 ht2 hts hnotin.
apply/negP => /mapP[t' ht' e].
have [ht'1 ht'2] := hts t' ht'.
have heq : t = t' :=
  @wotsc_tweak_inj w l zstar istar t t'
    ha ht1 ht'1 ht2 ht'2 e.
by move: ht'; rewrite -heq (negbTE hnotin).
Qed.

(** [th_eval Tf] at a re-tagged chain tweak is the wrapped chain
    hash (the canonical-tweak computation of Games.v). *)
Lemma th_eval_wtw pp (t : nat * nat) (x : N) :
  th_eval TF pp (wtw t) x = FW pp t x.
Proof. by rewrite /wotsc_tweak (th_evalE_Tf PP N F dPP dN). Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the CHAIN branch is a FixedSumOTS forgery

    In the CHAIN branch of Gmid2's KFORGE the discriminants provide:
    a VALID forged digit vector (verification), [size ystar = l]
    (verification), and completed ends that HIT the honest ones (the
    negated COMPRESS discriminant).  That is literally a verifying
    FixedSumOTS forgery at [Fw] against the honest [ends_from_sig]
    key — [verify_from_ends] — which feeds the REUSED classifier
    specs below. *)

(** Completing a forged signature against its own completion list
    passes every chain check (each check is [x == x]). *)
Lemma all_check_refl pp st n (ds : seq nat) (ys : seq N) :
  all (fun q => chain_check PP N FW w pp q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st n)
           (zip ds (zip ys
              [seq chain (cfW pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
              | q <- zip (iota st n) (zip ds ys)]))).
Proof.
elim: n st ds ys => [|n IH] st ds ys;
  first by case: ds => [|d ds]; case: ys => [|y ys].
case: ds => [|d ds]; case: ys => [|y ys] => //=.
apply/andP; split; last exact: IH.
by rewrite /chain_check eqxx.
Qed.

(** THE bridge: equal completed ends turn the WOTSC forgery data into
    a verifying FixedSumOTS forgery against the honest key. *)
Lemma verify_from_ends pp (mstar ds : seq nat) (ystar sg : seq N) :
  fsvalid mstar -> (size ystar == l)%B ->
  efs pp mstar ystar = efs pp ds sg ->
  fsverify pp (efs pp ds sg) mstar ystar.
Proof.
move=> hvm hys heq.
rewrite /HBS.Examples.FixedSumOTS.Scheme.verify_sig hvm hys /=.
rewrite -heq /ends_from_sig.
exact: all_check_refl.
Qed.

(** The classifier specs at WOTSC hypotheses (the reductions' CHAIN
    branches consume exactly these).  Hypotheses are what the KFORGE
    discriminants provide: grinding success of the signed counter,
    the stored-roots shape, the forged digest's validity and
    signature size (verification), the ends EQUALITY (negated
    COMPRESS discriminant) and the digit-vector freshness (negated
    GRIND discriminant). *)

Lemma wtcr_decisionP pp (m mstar : M) (c cstar : nat) (us ystar : seq N) :
  wgood pp m c -> size us = l ->
  vdigest (wdigest pp mstar cstar) -> (size ystar == l)%B ->
  wcends pp (wdigest pp mstar cstar) ystar
    = wcends pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us) ->
  wdigest pp mstar cstar != wdigest pp m c ->
  match wtcr_dec pp (wdigest pp m c) (wdigest pp mstar cstar)
          (wsigs pp 0 (wdigest pp m c) us) ystar with
  | Some (j, u) =>
      exists t v,
        [/\ qnth (wcommitq pp 0 (wdigest pp m c) us) j = Some (t, v),
            u != v
          & FW pp t u = FW pp t v]
  | None => True
  end.
Proof.
move=> hgood hus hvd' hys hends hned.
have hvm : fsvalid (wdigest pp m c)
  := vdigest_valid_msg PP M Hgrind S_wn zstar istar pp m c hgood.
have hvm' : fsvalid (wdigest pp mstar cstar)
  := vdigest_valid_msg PP M Hgrind S_wn zstar istar pp mstar cstar hvd'.
have hd : size (wdigest pp m c) = l
  := size_digest_of PP M Hgrind zstar istar pp m c.
have hver : fsverify pp
    (ends_of PP N FW w pp 0 (wdigest pp m c)
       (wsigs pp 0 (wdigest pp m c) us))
    (wdigest pp mstar cstar) ystar.
  rewrite (ends_of_from_sig PP N FW l w pp _ _ hd).
  by apply: verify_from_ends.
have hnin : wdigest pp mstar cstar \notin [:: wdigest pp m c].
  by rewrite inE.
exact: (tcr_decisionP PP N FW l w S_wn pp _ _ us ystar hvm hus hver hnin).
Qed.

Lemma wpre_decisionP pp (m mstar : M) (c cstar : nat) (us ystar : seq N) :
  wgood pp m c -> size us = l ->
  vdigest (wdigest pp mstar cstar) -> (size ystar == l)%B ->
  wcends pp (wdigest pp mstar cstar) ystar
    = wcends pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us) ->
  wdigest pp mstar cstar != wdigest pp m c ->
  match wpre_dec pp (wdigest pp m c) (wdigest pp mstar cstar)
          (wsigs pp 0 (wdigest pp m c) us) ystar with
  | Some (j, x) =>
      exists t u,
        qnth (wpreq 0 (wdigest pp m c) us) j = Some (t, u)
        /\ FW pp t x = FW pp t u
  | None => True
  end.
Proof.
move=> hgood hus hvd' hys hends hned.
have hvm : fsvalid (wdigest pp m c)
  := vdigest_valid_msg PP M Hgrind S_wn zstar istar pp m c hgood.
have hvm' : fsvalid (wdigest pp mstar cstar)
  := vdigest_valid_msg PP M Hgrind S_wn zstar istar pp mstar cstar hvd'.
have hver : fsverify pp
    (efs pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us))
    (wdigest pp mstar cstar) ystar.
  by apply: verify_from_ends.
have hnin : wdigest pp mstar cstar \notin [:: wdigest pp m c].
  by rewrite inE.
exact: (pre_decisionP PP N FW l w S_wn pp _ _ us ystar hvm hus hver hnin).
Qed.

(** Classifier totality on the CHAIN branch: if ChainColl declined,
    ChainMeet fires (the ideal-side dead branch of R_cpre). *)
Lemma wclassify_some pp (m mstar : M) (c cstar : nat) (us ystar : seq N) :
  wgood pp m c -> size us = l ->
  vdigest (wdigest pp mstar cstar) -> (size ystar == l)%B ->
  wcends pp (wdigest pp mstar cstar) ystar
    = wcends pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us) ->
  wdigest pp mstar cstar != wdigest pp m c ->
  wtcr_dec pp (wdigest pp m c) (wdigest pp mstar cstar)
    (wsigs pp 0 (wdigest pp m c) us) ystar = None ->
  wpre_dec pp (wdigest pp m c) (wdigest pp mstar cstar)
    (wsigs pp 0 (wdigest pp m c) us) ystar != None.
Proof.
move=> hgood hus hvd' hys hends hned.
have hvm : fsvalid (wdigest pp m c)
  := vdigest_valid_msg PP M Hgrind S_wn zstar istar pp m c hgood.
have hvm' : fsvalid (wdigest pp mstar cstar)
  := vdigest_valid_msg PP M Hgrind S_wn zstar istar pp mstar cstar hvd'.
have hver : fsverify pp
    (efs pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us))
    (wdigest pp mstar cstar) ystar.
  by apply: verify_from_ends.
have hnin : wdigest pp mstar cstar \notin [:: wdigest pp m c].
  by rewrite inE.
exact: (classify_some PP N FW l w S_wn pp _ _ us ystar hvm hus hver hnin).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Gmid3: Gmid2 with ALSO the CHAIN-COLLISION case nulled

    Same locations as G0w/G1w/Gmid1/Gmid2 (300-302); COMMIT is
    VERBATIM Gmid2's (= G1w's); KFORGE nulls GRIND, COMPRESS AND the
    ChainColl answers of the shared classifier (header). *)

Definition Gmid3 : game (I_KOTS WC) :=
  [package [fmap pk_loc' ; log_loc' ; sig_loc' ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get pk_loc' ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      #assert (isSome (wfind_ctr pp m)) ;;
      let c := odflt 0 (wfind_ctr pp m) in
      sg ← sample_sig_roots PP N FW dN pp 0 (wdigest pp m c) ;;
      #put pk_loc' := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)) ;;
      #put log_loc' := [:: m] ;;
      #put sig_loc' := Some (sg, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)), Some (sg, c))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pk ← getSome pk_loc' ;;
      log ← get log_loc' ;;
      sgo ← getSome sig_loc' ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if wverify pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if wdigest pk.1 mst sgst.2 == wdigest pk.1 m sgo.2
            then ret false
            else
              if wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wcends pk.1 (wdigest pk.1 m sgo.2) sgo.1
              then ret false
              else
                match wtcr_dec pk.1 (wdigest pk.1 m sgo.2)
                        (wdigest pk.1 mst sgst.2) sgo.1 sgst.1 with
                | Some _ => ret false
                | None => ret true
                end
          else ret false
      end
    }
  ].

(* ================================================================== *)
(** ** Part 1: the SM-TCR(F) hop (Gmid2 -> Gmid3) *)

(* ------------------------------------------------------------------ *)
(** *** The oracle-routed loops *)

(** COLLQ/TQUERY/GETPP/CHECK opsigs as committed to [I_SMTCR TF CF]. *)
Definition ct_cqo : opsig := (COLLQ, (tc_T CF × tc_M CF, tc_N CF)).
Definition ct_tqo : opsig := (TQUERY, (th_T TF × th_M TF, th_N TF)).
Definition ct_gpo : opsig := (GETPP, ('unit, th_PP TF)).
Definition ct_cko : opsig := (CHECK, ('nat × th_M TF, 'bool)).

(** The grinding loop: one COLLQ (Hgrind member, [inr]) per counter;
    returns the answer list (CompressHop's [cp_grind] at [Cf]). *)
Fixpoint ct_grind (m : M) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr ct_cqo (gtw, inr (m, c))
        (λ r,
           hs ← ct_grind m cs' ;;
           ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance ct_grind_valid (L : Locations) (m : M) (cs : seq nat) :
  ValidCode L (I_SMTCR TF CF) (ct_grind m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n]
    steps, one TQUERY per step at the encoded chain address; returns
    the value at [k + n] (TCRHop's [r_walk] at encoded tweaks). *)
Fixpoint ct_walk (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr ct_tqo (ctw i k, x) (λ y, ct_walk i k.+1 n' y)
  else ret x.

#[local] Instance ct_walk_valid (L : Locations) i k n (x : N) :
  ValidCode L (I_SMTCR TF CF) (ct_walk i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> y; exact: IH.
Qed.

(** All chains from index [st] with digits [ds]: per chain, sample
    the root LOCALLY, sigma TQUERY (positive digits), walk upward;
    returns (signature values, completed ends) — TCRHop's
    [r_chains], i.e. the targets are committed PER CHAIN in
    [commit_queries]' interleaved order. *)
Fixpoint ct_chains (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1 then opr ct_tqo (ctw st d', u) (λ y, ret y) else ret u) ;;
      e ← ct_walk st d (w.-1 - d) s ;;
      '(ss, es) ← ct_chains st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance ct_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMTCR TF CF) (ct_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by fmap_solve.
    move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: ct_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

(** R's own locations (350+, see header). *)
Definition rct_pk_loc := mkloc 350 (None : option (Pk WC)).
Definition rct_log_loc := mkloc 351 ([::] : seq (Msg WC)).
Definition rct_sig_loc := mkloc 352 (None : option (Sig WC)).

(** THE reduction: plays [I_KOTS WC] using the SM-TCR oracles. *)
Definition R_ctcr : package (I_SMTCR TF CF) (I_KOTS WC) :=
  [package [fmap rct_pk_loc ; rct_log_loc ; rct_sig_loc ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get rct_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr ct_cqo (gtw, inr (m, 0)) (λ r, ret r) ;;
      hs ← ct_grind m (iota 0 c_max) ;;
      #assert (isSome (wpick hs)) ;;
      let c := (odflt (0, 0) (wpick hs)).1 in
      let d := digits_w w l (odflt (0, 0) (wpick hs)).2 in
      '(sgs, ends) ← ct_chains 0 d ;;
      pp ← opr ct_gpo Datatypes.tt (λ p, ret p) ;;
      #put rct_pk_loc := Some (pp, Tl pp padrs ends) ;;
      #put rct_log_loc := [:: m] ;;
      #put rct_sig_loc := Some (sgs, c) ;;
      ret ((pp, Tl pp padrs ends), Some (sgs, c))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pk ← getSome rct_pk_loc ;;
      log ← get rct_log_loc ;;
      sgo ← getSome rct_sig_loc ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if wverify pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if wdigest pk.1 mst sgst.2 == wdigest pk.1 m sgo.2
            then ret false
            else
              if wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wcends pk.1 (wdigest pk.1 m sgo.2) sgo.1
              then ret false
              else
                match wtcr_dec pk.1 (wdigest pk.1 m sgo.2)
                        (wdigest pk.1 mst sgst.2) sgo.1 sgst.1 with
                | Some ju => opr ct_cko ju (λ ans, ret ans)
                | None => ret true
                end
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies (resolve equations, computed once) *)

Lemma resolve_ct_cq (b : bool) (t : tc_T CF) (x : tc_M CF) :
  resolve (SMT b) ct_cqo (t, x) =
  (ppo ← get tpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put tpp_loc := Some pp ;; ret pp
        end ;;
   ret (tc_eval CF pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ct_tq (b : bool) (t : th_T TF) (x : th_M TF) :
  resolve (SMT b) ct_tqo (t, x) =
  (revealed ← get trev_loc ;;
   #assert ~~ revealed ;;
   tws ← get ttws_loc ;;
   #assert (size tws < p_tcr l w)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get ttgts_loc ;;
   #put ttgts_loc := setm tgts (size tws) (t, x) ;;
   #put ttws_loc := rcons tws t ;;
   ppo ← get tpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put tpp_loc := Some pp ;; ret pp
        end ;;
   ret (th_eval TF pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ct_gp (b : bool) (u : unit) :
  resolve (SMT b) ct_gpo u =
  (ppo ← get tpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put tpp_loc := Some pp ;; ret pp
        end ;;
   #put trev_loc := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ct_ck (j : nat) (x : th_M TF) :
  resolve (SMT true) ct_cko (j, x) =
  (revealed ← get trev_loc ;;
   #assert revealed ;;
   tgts ← get ttgts_loc ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get tpp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put tpp_loc := Some pp ;; ret pp
            end ;;
       ret ((x != m0) && (th_eval TF pp t0 x == th_eval TF pp t0 m0))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side CHECK answers false unconditionally. *)
Lemma resolve_ct_ck_false (j : nat) (x : th_M TF) :
  resolve (SMT false) ct_cko (j, x) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the package, the resolved oracle bodies, the pure layer and
   the KFORGE discriminants folded under [simpl] from here on
   (GrindHop/CompressHop lesson). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments SMPRE_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments verify_sig : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments cp_pick : simpl never.
#[local] Arguments tcr_decision : simpl never.
#[local] Arguments pre_decision : simpl never.

(** Conversion bridge: the COLLQ answer at the grinding address,
    post-processed by the loop's [inr]-projection, IS the scheme's
    Hgrind output (canonical tweaks compute). *)
Lemma ct_collq_H_E pp (m : M) (c : nat) :
  (if tc_eval CF pp gtw (inr (m, c)) is inr h then h else 0)
  = Hgrind pp gadrs (m, c).
Proof. by rewrite /tc_eval /Cf /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** *** The invariant (header) *)

Definition IGNT : Locations :=
  [fmap pk_loc' ; log_loc' ; sig_loc' ; rct_pk_loc ; rct_log_loc ;
        rct_sig_loc ; tpp_loc ; ttgts_loc ; ttws_loc ; trev_loc ].

Definition RT (pko : option (Pk WC)) (lg : seq (Msg WC))
    (sgo : option (Sig WC))
    (pko' : option (Pk WC)) (lg' : seq (Msg WC)) (sgo' : option (Sig WC))
    (po : option PP) (tg : {fmap nat -> (th_T TF × th_M TF)})
    (tw : seq (th_T TF)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : M) (c : nat) (us : seq N),
            [/\ lg = [:: m],
                sgo = Some (wsigs pk.1 0 (wdigest pk.1 m c) us, c),
                po = Some pk.1,
                size us = l /\ wgood pk.1 m c
              & [/\ tg = qmap_from 0
                          [seq wq q | q <- wcommitq pk.1 0 (wdigest pk.1 m c) us],
                    tw = [seq wtw t | t <- unzip1 (wcommitq pk.1 0 (wdigest pk.1 m c) us)]
                  & rv = true]]
      end].

Definition ct_inv : precond :=
  heap_ignore IGNT
  ⋊ rel_app [:: (lhs, pk_loc') ; (lhs, log_loc') ; (lhs, sig_loc') ;
                (rhs, rct_pk_loc) ; (rhs, rct_log_loc) ; (rhs, rct_sig_loc) ;
                (rhs, tpp_loc) ; (rhs, ttgts_loc) ; (rhs, ttws_loc) ;
                (rhs, trev_loc) ] RT.

Arguments ct_inv : simpl never.

Lemma ct_invE s0 s1 :
  ct_inv (s0, s1) ->
  heap_ignore IGNT (s0, s1) /\
  RT (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rct_pk_loc) (get_heap s1 rct_log_loc)
     (get_heap s1 rct_sig_loc)
     (get_heap s1 tpp_loc) (get_heap s1 ttgts_loc) (get_heap s1 ttws_loc)
     (get_heap s1 trev_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma ct_invI s0 s1 :
  heap_ignore IGNT (s0, s1) ->
  RT (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rct_pk_loc) (get_heap s1 rct_log_loc)
     (get_heap s1 rct_sig_loc)
     (get_heap s1 tpp_loc) (get_heap s1 ttgts_loc) (get_heap s1 ttws_loc)
     (get_heap s1 trev_loc) ->
  ct_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** *** The block precondition (inside COMMIT, machinery dropped)

    [Q] is the committed-so-far list over ABSTRACT (chain, position)
    tweaks; the SM-TCR heap holds its re-tagged image (TCRHop's
    [blk_pre] + the [wq] re-tagging). *)

Definition tblk (po : option PP) (rv : bool) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNT (s0, s1),
      get_heap s1 tpp_loc = po,
      get_heap s1 trev_loc = rv,
      get_heap s1 ttws_loc = [seq wtw t | t <- unzip1 Q] &
      get_heap s1 ttgts_loc = qmap_from 0 [seq wq q | q <- Q]].

Arguments tblk : simpl never.

(** The lazy parameter sampling (put pp, at the COLLQ pin). *)
Lemma tblk_set_pp (pp : PP) rv Q s0 s1 :
  tblk None rv Q (s0, s1) ->
  tblk (Some pp) rv Q (s0, set_heap s1 tpp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The TQUERY state update (put tgts; put tws). *)
Lemma tblk_qupd (pp : PP) (Q : seq qentry) (t : nat * nat) (x : N) s0 s1 :
  tblk (Some pp) false Q (s0, s1) ->
  tblk (Some pp) false (rcons Q (t, x))
    (s0, set_heap (set_heap s1 ttgts_loc
            (setm (qmap_from 0 [seq wq q | q <- Q])
                  (size [seq wtw t' | t' <- unzip1 Q]) (wtw t, x)))
          ttws_loc (rcons [seq wtw t' | t' <- unzip1 Q] (wtw t))).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq /unzip1 !map_rcons.
- rewrite get_set_heap_neq // get_set_heap_eq.
  by rewrite map_rcons qmap_from_rcons add0n /unzip1 !size_map.
Qed.

(** The phase flip (GETPP's put rev). *)
Lemma tblk_set_rev (po : option PP) Q s0 s1 :
  tblk po false Q (s0, s1) ->
  tblk po true Q (s0, set_heap s1 trev_loc true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked COLLQ (pp pinned: state untouched) *)

Lemma r_ctcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CF) (x : tc_M CF) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : tc_N CF -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CF pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMT b) ct_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_ct_cq b t x).
eapply (r_get_bind_rhs tpp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: h.
Qed.

(** Grinding loop: the continuation receives the honest Hgrind answer
    list. *)
Lemma r_ctgrind_spec (b : bool) {B : choiceType} (pp : PP) (m : M)
    (cs : seq nat) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B)
    (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp gadrs (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (code_link (ct_grind m cs) (SMT b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_ctcollq_known b).
  cbv beta.
  rewrite ct_collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked TQUERY (pp pinned by the COLLQ pin) *)

Lemma r_ctquery_known (b : bool) {B : choiceType} (pp : PP)
    (i k : nat) (x : N) (Q : seq qentry)
    (c0 : raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  i < l -> k < w.-1 ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  size Q < p_tcr l w ->
  (i, k) \notin unzip1 Q ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false (rcons Q ((i, k), x)) (s0, s1) ⦄
     c0 ≈ k1 (FW pp (i, k) x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMT b) ct_tqo (ctw i k, x)) k1 ⦃ post ⦄.
Proof.
move=> hi hk hQr hbud hfresh h.
rewrite (resolve_ct_tq b (ctw i k) x).
eapply (r_get_bind_rhs trev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs ttws_loc [seq wtw t | t <- unzip1 Q]).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map /unzip1 size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  move=> s0 s1 _; apply: (wtw_notin (i, k) (unzip1 Q) Hanchor hi hk _ hfresh).
  by move=> t' /(allP hQr) /andP[h1 h2]; split.
move=> _.
eapply (r_get_bind_rhs ttgts_loc (qmap_from 0 [seq wq q | q <- Q])).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (tblk_qupd pp Q (i, k) x s0 s1 hpre).
eapply (r_get_bind_rhs tpp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
simpl.
rewrite (th_eval_wtw pp (i, k) x).
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The walk and per-chain inductions (TCRHop's, re-tagged) *)

Lemma r_ctwalk_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall n i k (x : N) (Q : seq qentry) (c0 : raw_code B)
         (k1 : N -> raw_code B),
  i < l ->
  (k + n <= w.-1)%N ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  (size Q + n <= p_tcr l w)%N ->
  all (tlt i k) (unzip1 Q) ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false
         (Q ++ walkq PP N FW pp i k n x) (s0, s1) ⦄
     c0 ≈ k1 (chain (cfW pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (code_link (ct_walk i k n x) (SMT b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x Q c0 k1 hi hkn hQr hbud hfresh h.
- by move: h; rewrite cats0.
- rewrite /= bind_assoc.
  have hk : k < w.-1 by apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
  eapply r_ctquery_known => //.
  + by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + exact: tlt_notin hfresh.
  + apply: IH => //.
    * by rewrite addSnnS.
    * rewrite /unzip1 map_rcons all_rcons hQr /=.
      by rewrite hi hk.
    * by rewrite size_rcons addSnnS.
    * rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
      -- by rewrite /tlt /= ltnn eqxx ltnSn.
      -- exact: all_tlt_widen hfresh.
    * by move: h; rewrite (walkq_cons PP N FW) cat_rcons.
Qed.

(** The per-chain induction: lhs [sample_sig_roots] at [FW] (the lhs
    games' sampling), rhs the linked [ct_chains]; the committed list
    grows by [commit_queries] and the results are [sigs_of]/[ends_of]
    of the sampled roots. *)
Lemma r_ctchains_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall ds st (Q : seq qentry) (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  (st + size ds <= l)%N ->
  all (λ d : nat, d < w) ds ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  (size Q + nqs w ds <= p_tcr l w)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false
            (Q ++ wcommitq pp st ds us) (s0, s1) ⦄
        K0 (wsigs pp st ds us)
      ≈ K1 (wsigs pp st ds us, wends pp st ds (wsigs pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false Q (s0, s1) ⦄
     bind (sample_sig_roots PP N FW dN pp st ds) K0
   ≈ bind (code_link (ct_chains st ds) (SMT b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st Q K0 K1 hst hds hQr hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- move: hst => /=; rewrite addnS => hst2.
  have hstl : st < l := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : st.+1 + size ds <= l := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /= code_link_bind.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* d = 0 : no sigma query, walk from the root itself *)
    have hkn0 : 0 + (w.-1 - 0) <= w.-1 by rewrite add0n subn0.
    rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    eapply (r_ctwalk_spec b pp post (w.-1 - 0) st 0 u Q) => //.
    * apply: leq_trans hbud.
      by rewrite leq_add2l /nqs /= /nq /= leq_addr.
    * exact: all_lt_tlt.
    * rewrite (code_link_bind (ct_chains st.+1 ds)) bind_assoc.
      eapply IH => //.
      -- rewrite unzip1_cat all_cat; apply/andP; split; first exact: hQr.
         apply/allP => t ht; apply/andP; split.
         ++ by move: (allP (walkq_tweak1 PP N FW pp st 0 (w.-1 - 0) u) t ht)
              => /eqP ->.
         ++ exact: (allP (walkq_tweak2 PP N FW pp st 0
                       (w.-1 - 0) u w.-1 hkn0) t ht).
      -- by rewrite size_cat size_walkq -addnA.
      -- rewrite unzip1_cat all_cat; apply/andP; split.
         ++ by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ apply: sub_all (walkq_tweak1 PP N FW pp st 0 _ u) => t /= /eqP ->.
            exact: ltnSn.
      -- move=> us hus.
         move: (h (u :: us)); rewrite /= hus => /(_ erefl).
         by rewrite (commit_queries_cons PP N FW) /chain_queries /= catA.
  + (* d = d'.+1 : sigma query first *)
    have hdw1 : d'.+1 <= w.-1 by rewrite -ltnS prednK.
    have hkn1 : d'.+1 + (w.-1 - d'.+1) <= w.-1 by rewrite subnKC.
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply r_ctquery_known => //.
    * apply: leq_trans hbud.
      by rewrite addnS ltnS leq_addr.
    * exact: lt_notin.
    * rewrite /= (code_link_bind (ct_walk st d'.+1 (w.-1 - d'.+1)
                    (FW pp (st, d') u))) bind_assoc.
      eapply (r_ctwalk_spec b pp post (w.-1 - d'.+1) st d'.+1
                (FW pp (st, d') u) (rcons Q ((st, d'), u))) => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstl hdw1.
      -- rewrite size_rcons addSnnS; apply: leq_trans hbud.
         by rewrite leq_add2l /nqs /= /nq /= add1n addSn ltnS leq_addr.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /tlt /= ltnn eqxx ltnSn.
         ++ exact: all_lt_tlt.
      -- rewrite /= (code_link_bind (ct_chains st.+1 ds)) bind_assoc.
         eapply IH => //.
         ++ rewrite unzip1_cat all_cat; apply/andP; split.
            ** rewrite /unzip1 map_rcons all_rcons hQr /=.
               by rewrite hstl hdw1.
            ** apply/allP => t ht; apply/andP; split.
               --- by move: (allP (walkq_tweak1 PP N FW pp st d'.+1
                             (w.-1 - d'.+1) (FW pp (st, d') u)) t ht)
                     => /eqP ->.
               --- exact: (allP (walkq_tweak2 PP N FW pp st d'.+1
                             (w.-1 - d'.+1) (FW pp (st, d') u)
                             w.-1 hkn1) t ht).
         ++ rewrite size_cat size_rcons size_walkq.
            apply: leq_trans hbud.
            by rewrite addSnnS -addnA leq_add2l /nqs /= /nq /= add1n.
         ++ rewrite unzip1_cat all_cat /unzip1 map_rcons all_rcons.
            apply/andP; split; last first.
            ** apply: sub_all (walkq_tweak1 PP N FW pp st d'.+1 _ _)
                 => t /= /eqP ->.
               exact: ltnSn.
            ** apply/andP; split; first by rewrite /= ltnSn.
               by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ move=> us hus.
            move: (h (u :: us)); rewrite /= hus => /(_ erefl).
            by rewrite (commit_queries_cons PP N FW) /chain_queries
                       cat_rcons catA.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The common COMMIT tail

    By this point all sampling and oracle interaction is over: both
    sides store key/log/signature (the same values) and return; the
    invariant is re-established from the final block state. *)

Lemma r_ct_tail (pp : PP) (m : M) (c : nat) (us : seq N) :
  wgood pp m c -> size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        tblk (Some pp) true (wcommitq pp 0 (wdigest pp m c) us) (s0, s1) ⦄
     (#put pk_loc' := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c)
        (wsigs pp 0 (wdigest pp m c) us))) ;;
      #put log_loc' := [:: m] ;;
      #put sig_loc' := Some (wsigs pp 0 (wdigest pp m c) us, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c)
             (wsigs pp 0 (wdigest pp m c) us))),
           Some (wsigs pp 0 (wdigest pp m c) us, c)))
   ≈ (#put rct_pk_loc := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c)
        (wsigs pp 0 (wdigest pp m c) us))) ;;
      #put rct_log_loc := [:: m] ;;
      #put rct_sig_loc := Some (wsigs pp 0 (wdigest pp m c) us, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c)
             (wsigs pp 0 (wdigest pp m c) us))),
           Some (wsigs pp 0 (wdigest pp m c) us, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ ct_inv (s0, s1) ⦄.
Proof.
move=> hgood hus.
eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hblk ->].
case: hblk => hign hpp hrev htws htgts.
split; first by [].
apply: ct_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists m, c, us; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_ctcr_real :
  perfect (I_KOTS WC) GM2 (R_ctcr ∘ SMTCR_game TF CF (p_tcr l w) true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ct_inv).
{ rewrite /ct_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/ct_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), tblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/ct_invE: hinv => hign hRT.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRT => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the COLLQ pin: SM-TCR's lazy pp is sampled here, against the
     lhs game's eager one *)
  rewrite (resolve_ct_cq true gtw (inr (m, 0))).
  eapply (r_get_bind_rhs tpp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (tblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  (* the grinding loop through COLLQ *)
  rewrite (code_link_bind (ct_grind m (iota 0 c_max))).
  eapply (r_ctgrind_spec true pp m).
  cbv beta.
  rewrite code_link_assertD
          (@cp_pick_map w l PP M Hgrind S_wn c_max zstar istar).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (wfind_ctr pp m). }
  move=> e1 _.
  move: e1; case E: (wfind_ctr pp m) => [c|] /= e1; last by [].
  rewrite !(digestE PP M Hgrind zstar istar).
  (* the chains: lhs re-rooted sampling, rhs TQUERY-committed walks *)
  rewrite (code_link_bind (ct_chains 0 (wdigest pp m c))).
  have hszd : size (wdigest pp m c) = l
    := size_digest_of PP M Hgrind zstar istar pp m c.
  eapply (r_ctchains_spec true pp _ (wdigest pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_ctr_good PP M Hgrind S_wn c_max
          zstar istar pp m c E; exact: hwf. }
    { by rewrite /= (nqs_le l w _ hszd). }
  move=> us hus.
  cbv beta iota.
  rewrite (wendsE PP N F zstar istar pp _ _
            (size_digest_of PP M Hgrind zstar istar pp m c)).
  simpl.
  (* GETPP: reveal pp, flip the phase; then the pure pk compression *)
  rewrite (resolve_ct_gp true Datatypes.tt).
  eapply (r_get_bind_rhs tpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (tblk_set_rev _ _ _ _ hpre). }
  apply: r_ct_tail => //.
  - exact: (find_ctr_good PP M Hgrind S_wn c_max zstar istar pp m c E).
  - by rewrite hus (size_digest_of PP M Hgrind zstar istar).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/ct_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/ct_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => sgol.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (sgov = sgol)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/ct_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/ct_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [uss [hA hB _ _ _]]].
      exists mm, cc, (wsigs pk.1 0 (wdigest pk.1 mm cc) uss); split.
      - by rewrite -h3.
      - by rewrite -h5. }
  move=> [m [c [sg [hlg hsgol]]]].
  rewrite hlg hsgol /=.
  case E0: (wverify pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[[hinv _] _] _] _] _] _].
  + case/andP: (E0) => hver hfresh.
    case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B).
    * (* GRIND: both games null it *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wcends pk.1 (wdigest pk.1 m c) sg)%B).
      -- (* COMPRESS: both games null it *)
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
      -- (* CHAIN: run the shared classifier *)
         case E3: (wtcr_dec pk.1 (wdigest pk.1 m c)
                     (wdigest pk.1 mst sgst.2) sg sgst.1) => [[j u]|];
           last first.
         ++ (* ChainMeet: both sides answer true *)
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[[[hinv _] _] _] _] _] _].
         ++ (* ChainColl: CHECK answers true = Gmid2's verdict *)
            simpl.
            rewrite (resolve_ct_ck j u).
            eapply (r_get_bind_rhs trev_loc true).
              { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch => mm [cc [uss [_ _ _ _ [_ _ hrv]]]]. }
            cbv beta.
            eapply r_bind_assertD_rhs; first by [].
            move=> _.
            eapply r_get_remember_rhs => tg.
            eapply (r_fact (exists us,
                      [/\ size us = l, wgood pk.1 m c,
                          sg = wsigs pk.1 0 (wdigest pk.1 m c) us
                        & tg = qmap_from 0
                            [seq wq q
                            | q <- wcommitq pk.1 0 (wdigest pk.1 m c) us]])).
              { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
                rewrite h1 in hmatch.
                case: hmatch
                  => mm [cc [uss [hA hB _ [husz hgood] [htg _ _]]]].
                have emm : mm = m.
                  { have : [:: mm] = [:: m] by rewrite -hA h3.
                    by case. }
                rewrite emm in hB hgood htg.
                have hsgcc : Some (wsigs pk.1 0 (wdigest pk.1 m cc) uss, cc)
                             = Some (sg, c).
                  { by rewrite -hB h5. }
                have ecc : cc = c by case: hsgcc.
                rewrite ecc in hsgcc hgood htg.
                have esg : sg = wsigs pk.1 0 (wdigest pk.1 m c) uss.
                  { by case: hsgcc. }
                by exists uss; split=> //; rewrite -h7. }
            move=> [us [husz hgood hsg htg]].
            have hned := negbT E1.
            have hends : wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                         = wcends pk.1 (wdigest pk.1 m c)
                             (wsigs pk.1 0 (wdigest pk.1 m c) us).
              { by move/negbFE/eqP: E2 => ->; rewrite hsg. }
            move: (hver); rewrite /verify_sig => /and3P[hvd' hys _].
            have hwin := wtcr_decisionP pk.1 m mst c sgst.2 us sgst.1
                           hgood husz hvd' hys hends hned.
            rewrite -hsg E3 in hwin.
            case: hwin => t [v [hqn hne hcol]].
            have hgetm : getm tg j = Some (wtw t, v).
              { rewrite htg.
                have := qmap_from_get 0
                  [seq wq q | q <- wcommitq pk.1 0 (wdigest pk.1 m c) us] j.
                rewrite add0n => ->.
                by rewrite qnth_map hqn. }
            rewrite hgetm.
            eapply (r_get_rhs_known tpp_loc (Some pk.1)).
              { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch => mm [cc [uss [_ _ hpo _ _]]]. }
            simpl.
            rewrite !th_eval_wtw.
            rewrite hne hcol eqxx /=.
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[[[[hinv _] _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence *)

Lemma R_ctcr_ideal :
  perfect (I_KOTS WC) Gmid3 (R_ctcr ∘ SMTCR_game TF CF (p_tcr l w) false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ct_inv).
{ rewrite /ct_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (all oracle bodies and loop
     specs are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/ct_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), tblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/ct_invE: hinv => hign hRT.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRT => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_ct_cq false gtw (inr (m, 0))).
  eapply (r_get_bind_rhs tpp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (tblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  rewrite (code_link_bind (ct_grind m (iota 0 c_max))).
  eapply (r_ctgrind_spec false pp m).
  cbv beta.
  rewrite code_link_assertD
          (@cp_pick_map w l PP M Hgrind S_wn c_max zstar istar).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (wfind_ctr pp m). }
  move=> e1 _.
  move: e1; case E: (wfind_ctr pp m) => [c|] /= e1; last by [].
  rewrite !(digestE PP M Hgrind zstar istar).
  rewrite (code_link_bind (ct_chains 0 (wdigest pp m c))).
  have hszd : size (wdigest pp m c) = l
    := size_digest_of PP M Hgrind zstar istar pp m c.
  eapply (r_ctchains_spec false pp _ (wdigest pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_ctr_good PP M Hgrind S_wn c_max
          zstar istar pp m c E; exact: hwf. }
    { by rewrite /= (nqs_le l w _ hszd). }
  move=> us hus.
  cbv beta iota.
  rewrite (wendsE PP N F zstar istar pp _ _
            (size_digest_of PP M Hgrind zstar istar pp m c)).
  simpl.
  rewrite (resolve_ct_gp false Datatypes.tt).
  eapply (r_get_bind_rhs tpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (tblk_set_rev _ _ _ _ hpre). }
  apply: r_ct_tail => //.
  - exact: (find_ctr_good PP M Hgrind S_wn c_max zstar istar pp m c E).
  - by rewrite hus (size_digest_of PP M Hgrind zstar istar).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/ct_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/ct_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => sgol.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (sgov = sgol)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/ct_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/ct_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [uss [hA hB _ _ _]]].
      exists mm, cc, (wsigs pk.1 0 (wdigest pk.1 mm cc) uss); split.
      - by rewrite -h3.
      - by rewrite -h5. }
  move=> [m [c [sg [hlg hsgol]]]].
  rewrite hlg hsgol /=.
  case E0: (wverify pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[[hinv _] _] _] _] _] _].
  + case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B).
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wcends pk.1 (wdigest pk.1 m c) sg)%B).
      -- apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
      -- case E3: (wtcr_dec pk.1 (wdigest pk.1 m c)
                     (wdigest pk.1 mst sgst.2) sg sgst.1) => [[j u]|];
           last first.
         ++ (* ChainMeet: both sides answer true *)
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[[[hinv _] _] _] _] _] _].
         ++ (* ChainColl: ideal CHECK answers false = Gmid3's null *)
            simpl.
            rewrite (resolve_ct_ck_false j u).
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

(* ================================================================== *)
(** ** Part 2: the SM-PRE(F) hop (Gmid3 -> G1w-ideal) *)

(* ------------------------------------------------------------------ *)
(** *** The oracle-routed loops *)

(** PQUERY/PGETPP/PCHECK/PCOLLQ opsigs as committed to
    [I_SMPRE TF CF]. *)
Definition pr_pqo : opsig := (PQUERY, (th_T TF, th_N TF)).
Definition pr_gpo : opsig := (PGETPP, ('unit, th_PP TF)).
Definition pr_cko : opsig := (PCHECK, ('nat × th_M TF, 'bool)).
Definition pr_cqo : opsig := (PCOLLQ, (tc_T CF × tc_M CF, tc_N CF)).

(** The grinding loop through PCOLLQ ([ct_grind]'s twin). *)
Fixpoint pr_grind (m : M) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr pr_cqo (gtw, inr (m, c))
        (λ r,
           hs ← pr_grind m cs' ;;
           ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance pr_grind_valid (L : Locations) (m : M) (cs : seq nat) :
  ValidCode L (I_SMPRE TF CF) (pr_grind m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** All chains from index [st] with digits [ds]: positive digits make
    the sigma PQUERY at the encoded chain address (the oracle hides
    the root and answers the signature value), zero digits sample the
    value locally; returns the signature values (PREHop's
    [rp_chains] at encoded tweaks). *)
Fixpoint pr_chains (st : nat) (ds : seq nat) : raw_code (chList N) :=
  match ds with
  | [::] => ret [::]
  | d :: ds' =>
      s ← (if d is d'.+1
           then opr pr_pqo (ctw st d') (λ y, ret y)
           else (dN : raw_code N)) ;;
      ss ← pr_chains st.+1 ds' ;;
      ret (s :: ss)
  end.

#[local] Instance pr_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMPRE TF CF) (pr_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind.
  + case: d => [|d'].
    * eapply valid_scheme, prog_valid.
    * eapply valid_opr; first by fmap_solve.
      move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: IH.
    move=> ss; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

(** R's own locations (360+, see header). *)
Definition rpr_pk_loc := mkloc 360 (None : option (Pk WC)).
Definition rpr_log_loc := mkloc 361 ([::] : seq (Msg WC)).
Definition rpr_sig_loc := mkloc 362 (None : option (Sig WC)).

(** THE reduction: plays [I_KOTS WC] using the SM-PRE oracles.  See
    the header for the PCOLLQ pin in COMMIT and the pre-commitment
    PCHECK gadget (the [n0] side condition) in KFORGE. *)
Definition R_cpre : package (I_SMPRE TF CF) (I_KOTS WC) :=
  [package [fmap rpr_pk_loc ; rpr_log_loc ; rpr_sig_loc ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get rpr_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr pr_cqo (gtw, inr (m, 0)) (λ r, ret r) ;;
      hs ← pr_grind m (iota 0 c_max) ;;
      #assert (isSome (wpick hs)) ;;
      let c := (odflt (0, 0) (wpick hs)).1 in
      let d := digits_w w l (odflt (0, 0) (wpick hs)).2 in
      sgs ← pr_chains 0 d ;;
      pp ← opr pr_gpo Datatypes.tt (λ p, ret p) ;;
      #put rpr_pk_loc := Some (pp, Tl pp padrs (wcends pp d sgs)) ;;
      #put rpr_log_loc := [:: m] ;;
      #put rpr_sig_loc := Some (sgs, c) ;;
      ret ((pp, Tl pp padrs (wcends pp d sgs)), Some (sgs, c))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pko ← get rpr_pk_loc ;;
      match pko with
      | None =>
          (* pre-commitment gadget: real PCHECK fails on the phase
             assert (mirroring Gmid3's getSome), ideal PCHECK returns
             false (mirroring G1w-ideal) *)
          opr pr_cko (0, n0) (λ ans, ret ans)
      | Some pk =>
          log ← get rpr_log_loc ;;
          sgo ← get rpr_sig_loc ;;
          match log, sgo with
          | m :: _, Some sgc =>
              if wverify pk.1 pk.2 mst sgst && (mst \notin log)
              then
                if wdigest pk.1 mst sgst.2 == wdigest pk.1 m sgc.2
                then ret false
                else
                  if wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                     != wcends pk.1 (wdigest pk.1 m sgc.2) sgc.1
                  then ret false
                  else
                    match wtcr_dec pk.1 (wdigest pk.1 m sgc.2)
                            (wdigest pk.1 mst sgst.2) sgc.1 sgst.1 with
                    | Some _ => ret false
                    | None =>
                        match wpre_dec pk.1 (wdigest pk.1 m sgc.2)
                                (wdigest pk.1 mst sgst.2) sgc.1 sgst.1 with
                        | Some jx => opr pr_cko jx (λ ans, ret ans)
                        | None => ret true
                        end
                    end
              else ret false
          | _, _ => ret false
          end
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies (resolve equations, computed once) *)

Lemma resolve_pr_cq (b : bool) (t : tc_T CF) (x : tc_M CF) :
  resolve (SMP b) pr_cqo (t, x) =
  (ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   ret (tc_eval CF pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pr_pq (b : bool) (t : th_T TF) :
  resolve (SMP b) pr_pqo t =
  (revealed ← get prev_loc ;;
   #assert ~~ revealed ;;
   tws ← get ptws_loc ;;
   #assert (size tws < l)%N ;;
   #assert (t \notin tws) ;;
   x ← dN ;;
   tgts ← get ptgts_loc ;;
   #put ptgts_loc := setm tgts (size tws) (t, x) ;;
   #put ptws_loc := rcons tws t ;;
   ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   ret (th_eval TF pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pr_gp (b : bool) (u : unit) :
  resolve (SMP b) pr_gpo u =
  (ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   #put prev_loc := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pr_ck (j : nat) (x : th_M TF) :
  resolve (SMP true) pr_cko (j, x) =
  (revealed ← get prev_loc ;;
   #assert revealed ;;
   tgts ← get ptgts_loc ;;
   match getm tgts j with
   | Some (t0, x0) =>
       ppo ← get ppp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put ppp_loc := Some pp ;; ret pp
            end ;;
       ret (th_eval TF pp t0 x == th_eval TF pp t0 x0)%B
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side PCHECK answers false unconditionally. *)
Lemma resolve_pr_ck_false (j : nat) (x : th_M TF) :
  resolve (SMP false) pr_cko (j, x) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The invariant (header) *)

Definition IGNP : Locations :=
  [fmap pk_loc' ; log_loc' ; sig_loc' ; rpr_pk_loc ; rpr_log_loc ;
        rpr_sig_loc ; ppp_loc ; ptgts_loc ; ptws_loc ; prev_loc ].

Definition RP (pko : option (Pk WC)) (lg : seq (Msg WC))
    (sgo : option (Sig WC))
    (pko' : option (Pk WC)) (lg' : seq (Msg WC)) (sgo' : option (Sig WC))
    (po : option PP) (tg : {fmap nat -> (th_T TF × th_M TF)})
    (tw : seq (th_T TF)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : M) (c : nat) (us : seq N),
            [/\ lg = [:: m],
                sgo = Some (wsigs pk.1 0 (wdigest pk.1 m c) us, c),
                po = Some pk.1,
                size us = l /\ wgood pk.1 m c
              & [/\ tg = qmap_from 0
                          [seq wq q | q <- wpreq 0 (wdigest pk.1 m c) us],
                    tw = [seq wtw t | t <- unzip1 (wpreq 0 (wdigest pk.1 m c) us)]
                  & rv = true]]
      end].

Definition pr_inv : precond :=
  heap_ignore IGNP
  ⋊ rel_app [:: (lhs, pk_loc') ; (lhs, log_loc') ; (lhs, sig_loc') ;
                (rhs, rpr_pk_loc) ; (rhs, rpr_log_loc) ; (rhs, rpr_sig_loc) ;
                (rhs, ppp_loc) ; (rhs, ptgts_loc) ; (rhs, ptws_loc) ;
                (rhs, prev_loc) ] RP.

Arguments pr_inv : simpl never.

Lemma pr_invE s0 s1 :
  pr_inv (s0, s1) ->
  heap_ignore IGNP (s0, s1) /\
  RP (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rpr_pk_loc) (get_heap s1 rpr_log_loc)
     (get_heap s1 rpr_sig_loc)
     (get_heap s1 ppp_loc) (get_heap s1 ptgts_loc) (get_heap s1 ptws_loc)
     (get_heap s1 prev_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma pr_invI s0 s1 :
  heap_ignore IGNP (s0, s1) ->
  RP (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rpr_pk_loc) (get_heap s1 rpr_log_loc)
     (get_heap s1 rpr_sig_loc)
     (get_heap s1 ppp_loc) (get_heap s1 ptgts_loc) (get_heap s1 ptws_loc)
     (get_heap s1 prev_loc) ->
  pr_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** *** The block precondition (inside COMMIT, machinery dropped) *)

Definition pblk (po : option PP) (rv : bool) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNP (s0, s1),
      get_heap s1 ppp_loc = po,
      get_heap s1 prev_loc = rv,
      get_heap s1 ptws_loc = [seq wtw t | t <- unzip1 Q] &
      get_heap s1 ptgts_loc = qmap_from 0 [seq wq q | q <- Q]].

Arguments pblk : simpl never.

(** The lazy parameter sampling (put pp, at the PCOLLQ pin). *)
Lemma pblk_set_pp (pp : PP) rv Q s0 s1 :
  pblk None rv Q (s0, s1) ->
  pblk (Some pp) rv Q (s0, set_heap s1 ppp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The PQUERY state update (put tgts; put tws). *)
Lemma pblk_qupd (pp : PP) (Q : seq qentry) (t : nat * nat) (x : N) s0 s1 :
  pblk (Some pp) false Q (s0, s1) ->
  pblk (Some pp) false (rcons Q (t, x))
    (s0, set_heap (set_heap s1 ptgts_loc
            (setm (qmap_from 0 [seq wq q | q <- Q])
                  (size [seq wtw t' | t' <- unzip1 Q]) (wtw t, x)))
          ptws_loc (rcons [seq wtw t' | t' <- unzip1 Q] (wtw t))).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq /unzip1 !map_rcons.
- rewrite get_set_heap_neq // get_set_heap_eq.
  by rewrite map_rcons qmap_from_rcons add0n /unzip1 !size_map.
Qed.

(** The phase flip (PGETPP's put rev). *)
Lemma pblk_set_rev (po : option PP) Q s0 s1 :
  pblk po false Q (s0, s1) ->
  pblk po true Q (s0, set_heap s1 prev_loc true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked PCOLLQ (pp pinned: state untouched) *)

Lemma r_prcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CF) (x : tc_M CF) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : tc_N CF -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CF pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMP b) pr_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_pr_cq b t x).
eapply (r_get_bind_rhs ppp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: h.
Qed.

(** Grinding loop through PCOLLQ. *)
Lemma r_prgrind_spec (b : bool) {B : choiceType} (pp : PP) (m : M)
    (cs : seq nat) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B)
    (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp gadrs (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (code_link (pr_grind m cs) (SMP b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_prcollq_known b).
  cbv beta.
  rewrite ct_collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked PQUERY

    Unlike TQUERY (whose input is supplied by the reduction), PQUERY
    samples the hidden input INSIDE the oracle; the rule couples the
    lhs's [dN] (the game's root sample) with the oracle's hidden one
    (PREHop's [r_pquery] at encoded tweaks). *)

Lemma r_prquery (b : bool) {B : choiceType} (pp : PP)
    (i k : nat) (Q : seq qentry)
    (k0 k1 : N -> raw_code B) (post : postcond B B) :
  i < l -> k < w.-1 ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  size Q < l ->
  (i, k) \notin unzip1 Q ->
  (forall x : N,
     ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false (rcons Q ((i, k), x)) (s0, s1) ⦄
        k0 x ≈ k1 (FW pp (i, k) x) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false Q (s0, s1) ⦄
     bind dN k0 ≈ bind (resolve (SMP b) pr_pqo (ctw i k)) k1 ⦃ post ⦄.
Proof.
move=> hi hk hQr hbud hfresh h.
rewrite (resolve_pr_pq b (ctw i k)).
eapply (r_get_bind_rhs prev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs ptws_loc [seq wtw t | t <- unzip1 Q]).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map /unzip1 size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  move=> s0 s1 _; apply: (wtw_notin (i, k) (unzip1 Q) Hanchor hi hk _ hfresh).
  by move=> t' /(allP hQr) /andP[h1 h2]; split.
move=> _.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> x; cbv beta.
eapply (r_get_bind_rhs ptgts_loc (qmap_from 0 [seq wq q | q <- Q])).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (pblk_qupd pp Q (i, k) x s0 s1 hpre).
eapply (r_get_bind_rhs ppp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
simpl.
rewrite (th_eval_wtw pp (i, k) x).
exact: (h x).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain induction

    lhs [sample_sig_roots] at [FW], rhs the linked [pr_chains]; the
    committed list grows by [pre_queries] and both results are
    [sigs_of] of the hidden inputs. *)

Lemma r_prchains_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall ds st (Q : seq qentry) (K0 K1 : chList N -> raw_code B),
  (st + size ds <= l)%N ->
  all (λ d : nat, d < w) ds ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  (size Q + npq ds <= l)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false
            (Q ++ wpreq st ds us) (s0, s1) ⦄
        K0 (wsigs pp st ds us) ≈ K1 (wsigs pp st ds us) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false Q (s0, s1) ⦄
     bind (sample_sig_roots PP N FW dN pp st ds) K0
   ≈ bind (code_link (pr_chains st ds) (SMP b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st Q K0 K1 hst hds hQr hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- move: hst => /=; rewrite addnS => hst2.
  have hstl : st < l := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : st.+1 + size ds <= l := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /= code_link_bind.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* d = 0 : both sides sample the value locally *)
    rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> u; cbv beta.
    rewrite !bind_assoc.
    rewrite (code_link_bind (pr_chains st.+1 ds)) !bind_assoc.
    eapply IH => //.
    * by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
    * move=> us hus.
      move: (h (u :: us)); rewrite /= hus => /(_ erefl).
      by [].
  + (* d = d'.+1 : the sigma PQUERY *)
    have hdw1 : d'.+1 <= w.-1 by rewrite -ltnS prednK.
    rewrite bind_assoc.
    simpl.
    rewrite !bind_assoc.
    eapply r_prquery => //.
    * by apply: leq_trans hbud; rewrite /npq /= addnS ltnS leq_addr.
    * exact: lt_notin hfresh.
    * move=> x; cbv beta.
      rewrite !bind_assoc.
      simpl.
      rewrite (code_link_bind (pr_chains st.+1 ds)) !bind_assoc.
      eapply IH => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstl hdw1.
      -- by move: hbud; rewrite size_rcons /npq /= addnS addSn.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /= ltnSn.
         ++ by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
      -- move=> us hus.
         move: (h (x :: us)); rewrite /= hus => /(_ erefl).
         by rewrite (pre_queries_cons N) /= cat_rcons.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The common COMMIT tail *)

Lemma r_pr_tail (pp : PP) (m : M) (c : nat) (us : seq N) :
  wgood pp m c -> size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        pblk (Some pp) true (wpreq 0 (wdigest pp m c) us) (s0, s1) ⦄
     (#put pk_loc' := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c)
        (wsigs pp 0 (wdigest pp m c) us))) ;;
      #put log_loc' := [:: m] ;;
      #put sig_loc' := Some (wsigs pp 0 (wdigest pp m c) us, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c)
             (wsigs pp 0 (wdigest pp m c) us))),
           Some (wsigs pp 0 (wdigest pp m c) us, c)))
   ≈ (#put rpr_pk_loc := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c)
        (wsigs pp 0 (wdigest pp m c) us))) ;;
      #put rpr_log_loc := [:: m] ;;
      #put rpr_sig_loc := Some (wsigs pp 0 (wdigest pp m c) us, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c)
             (wsigs pp 0 (wdigest pp m c) us))),
           Some (wsigs pp 0 (wdigest pp m c) us, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pr_inv (s0, s1) ⦄.
Proof.
move=> hgood hus.
eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hblk ->].
case: hblk => hign hpp hrev htws htgts.
split; first by [].
apply: pr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists m, c, us; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_cpre_real :
  perfect (I_KOTS WC) Gmid3 (R_cpre ∘ SMPRE_game TF CF l true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pr_inv).
{ rewrite /pr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), pblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/pr_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the PCOLLQ pin *)
  rewrite (resolve_pr_cq true gtw (inr (m, 0))).
  eapply (r_get_bind_rhs ppp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (pblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  (* the grinding loop through PCOLLQ *)
  rewrite (code_link_bind (pr_grind m (iota 0 c_max))).
  eapply (r_prgrind_spec true pp m).
  cbv beta.
  rewrite code_link_assertD
          (@cp_pick_map w l PP M Hgrind S_wn c_max zstar istar).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (wfind_ctr pp m). }
  move=> e1 _.
  move: e1; case E: (wfind_ctr pp m) => [c|] /= e1; last by [].
  rewrite !(digestE PP M Hgrind zstar istar).
  (* the chains: lhs re-rooted sampling, rhs hidden PQUERY samples *)
  rewrite (code_link_bind (pr_chains 0 (wdigest pp m c))).
  have hszd : size (wdigest pp m c) = l
    := size_digest_of PP M Hgrind zstar istar pp m c.
  eapply (r_prchains_spec true pp _ (wdigest pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_ctr_good PP M Hgrind S_wn c_max
          zstar istar pp m c E; exact: hwf. }
    { by rewrite /= (npq_le l _ hszd). }
  move=> us hus.
  cbv beta.
  simpl.
  (* PGETPP, then the PURE completion/compression *)
  rewrite (resolve_pr_gp true Datatypes.tt).
  eapply (r_get_bind_rhs ppp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (pblk_set_rev _ _ _ _ hpre). }
  apply: r_pr_tail => //.
  - exact: (find_ctr_good PP M Hgrind S_wn c_max zstar istar pp m c E).
  - by rewrite hus (size_digest_of PP M Hgrind zstar istar).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  case: pko => [pk|]; last first.
  + (* pre-commitment: Gmid3 fails on the getSome assert, R fails
       inside the real PCHECK's phase assert (the gadget) *)
    simpl.
    rewrite (resolve_pr_ck 0 n0).
    eapply (r_get_bind_rhs prev_loc false).
      { move=> s0 s1 [[hinv hrem0] hrem1].
        case/pr_invE: hinv => _ hRP.
        rewrite /rem_inv /= in hrem0 hrem1.
        case: hRP => _ _ _; rewrite hrem0 => -[_ _ _ _ [_ hrv]].
        exact: hrv. }
    cbv beta.
    exact: r_fail_bind_rhs.
  + (* committed: mirror Gmid3 *)
    simpl.
    eapply r_get_remember_lhs => lg.
    eapply r_get_remember_rhs => lg'.
    eapply (r_fact (lg' = lg)).
      { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
        case/pr_invE: hinv => _ [_ e2 _ _].
        rewrite /rem_inv /= in hrem0 hrem1.
        by rewrite -hrem0 -hrem1. }
    move=> e; subst lg'.
    eapply r_get_remember_lhs => sgol.
    eapply r_get_remember_rhs => sgov.
    eapply (r_fact (sgov = sgol)).
      { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
        case/pr_invE: hinv => _ [_ _ e3 _].
        rewrite /rem_inv /= in hrem0 hrem1.
        by rewrite -hrem0 -hrem1. }
    move=> e; subst sgov.
    eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
              lg = [:: m] /\ sgol = Some (sg, c))).
      { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
        case/pr_invE: hinv => _ [_ _ _ hmatch].
        rewrite /rem_inv /= in h1 h3 h5.
        rewrite h1 in hmatch.
        case: hmatch => mm [cc [uss [hA hB _ _ _]]].
        exists mm, cc, (wsigs pk.1 0 (wdigest pk.1 mm cc) uss); split.
        - by rewrite -h3.
        - by rewrite -h5. }
    move=> [m [c [sg [hlg hsgol]]]].
    rewrite hlg hsgol /=.
    case E0: (wverify pk.1 pk.2 mst sgst && (mst \notin [:: m]));
      last first.
    * (* invalid forgery: both sides answer false *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * case/andP: (E0) => hver hfresh.
      case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B).
      -- (* GRIND: both null *)
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
      -- case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                    != wcends pk.1 (wdigest pk.1 m c) sg)%B).
         ++ (* COMPRESS: both null *)
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[[[hinv _] _] _] _] _] _].
         ++ case E3: (wtcr_dec pk.1 (wdigest pk.1 m c)
                        (wdigest pk.1 mst sgst.2) sg sgst.1) => [ju|].
            ** (* ChainColl: both null *)
               apply r_ret => s0 s1 hpre; split=> //.
               by case: hpre => [[[[[[hinv _] _] _] _] _] _].
            ** case E4: (wpre_dec pk.1 (wdigest pk.1 m c)
                           (wdigest pk.1 mst sgst.2) sg sgst.1)
                 => [[j x]|]; last first.
               --- (* degenerate: both answer true *)
                   apply r_ret => s0 s1 hpre; split=> //.
                   by case: hpre => [[[[[[hinv _] _] _] _] _] _].
               --- (* ChainMeet: PCHECK answers true = Gmid3's true *)
                   simpl.
                   rewrite (resolve_pr_ck j x).
                   eapply (r_get_bind_rhs prev_loc true).
                     { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1.
                       rewrite h1 in hmatch.
                       by case: hmatch
                         => mm [cc [uss [_ _ _ _ [_ _ hrv]]]]. }
                   cbv beta.
                   eapply r_bind_assertD_rhs; first by [].
                   move=> _.
                   eapply r_get_remember_rhs => tg.
                   eapply (r_fact (exists us,
                             [/\ size us = l, wgood pk.1 m c,
                                 sg = wsigs pk.1 0 (wdigest pk.1 m c) us
                               & tg = qmap_from 0
                                   [seq wq q
                                   | q <- wpreq 0 (wdigest pk.1 m c) us]])).
                     { move=> s0 s1
                         [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
                       rewrite h1 in hmatch.
                       case: hmatch
                         => mm [cc [uss [hA hB _ [husz hgood] [htg _ _]]]].
                       have emm : mm = m.
                         { have : [:: mm] = [:: m] by rewrite -hA h3.
                           by case. }
                       rewrite emm in hB hgood htg.
                       have hsgcc :
                           Some (wsigs pk.1 0 (wdigest pk.1 m cc) uss, cc)
                           = Some (sg, c).
                         { by rewrite -hB h5. }
                       have ecc : cc = c by case: hsgcc.
                       rewrite ecc in hsgcc hgood htg.
                       have esg : sg = wsigs pk.1 0 (wdigest pk.1 m c) uss.
                         { by case: hsgcc. }
                       by exists uss; split=> //; rewrite -h7. }
                   move=> [us [husz hgood hsg htg]].
                   have hned := negbT E1.
                   have hends : wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                                = wcends pk.1 (wdigest pk.1 m c)
                                    (wsigs pk.1 0 (wdigest pk.1 m c) us).
                     { by move/negbFE/eqP: E2 => ->; rewrite hsg. }
                   move: (hver); rewrite /verify_sig => /and3P[hvd' hys _].
                   have hwin := wpre_decisionP pk.1 m mst c sgst.2 us sgst.1
                                  hgood husz hvd' hys hends hned.
                   rewrite -hsg E4 in hwin.
                   case: hwin => t [u [hqn hfeq]].
                   have hgetm : getm tg j = Some (wtw t, u).
                     { rewrite htg.
                       have := qmap_from_get 0
                         [seq wq q | q <- wpreq 0 (wdigest pk.1 m c) us] j.
                       rewrite add0n => ->.
                       by rewrite qnth_map hqn. }
                   rewrite hgetm.
                   eapply (r_get_rhs_known ppp_loc (Some pk.1)).
                     { move=> s0 s1
                         [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1.
                       rewrite h1 in hmatch.
                       by case: hmatch => mm [cc [uss [_ _ hpo _ _]]]. }
                   simpl.
                   rewrite !th_eval_wtw.
                   rewrite hfeq eqxx.
                   apply r_ret => s0 s1 hpre; split=> //.
                   by case: hpre => [[[[[[[hinv _] _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence *)

Lemma R_cpre_ideal :
  perfect (I_KOTS WC) (G1W false) (R_cpre ∘ SMPRE_game TF CF l false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pr_inv).
{ rewrite /pr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (G1w's COMMIT is verbatim
     Gmid3's; all oracle bodies and loop specs are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), pblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/pr_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_pr_cq false gtw (inr (m, 0))).
  eapply (r_get_bind_rhs ppp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (pblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  rewrite (code_link_bind (pr_grind m (iota 0 c_max))).
  eapply (r_prgrind_spec false pp m).
  cbv beta.
  rewrite code_link_assertD
          (@cp_pick_map w l PP M Hgrind S_wn c_max zstar istar).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (wfind_ctr pp m). }
  move=> e1 _.
  move: e1; case E: (wfind_ctr pp m) => [c|] /= e1; last by [].
  rewrite !(digestE PP M Hgrind zstar istar).
  rewrite (code_link_bind (pr_chains 0 (wdigest pp m c))).
  have hszd : size (wdigest pp m c) = l
    := size_digest_of PP M Hgrind zstar istar pp m c.
  eapply (r_prchains_spec false pp _ (wdigest pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_ctr_good PP M Hgrind S_wn c_max
          zstar istar pp m c E; exact: hwf. }
    { by rewrite /= (npq_le l _ hszd). }
  move=> us hus.
  cbv beta.
  simpl.
  rewrite (resolve_pr_gp false Datatypes.tt).
  eapply (r_get_bind_rhs ppp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (pblk_set_rev _ _ _ _ hpre). }
  apply: r_pr_tail => //.
  - exact: (find_ctr_good PP M Hgrind S_wn c_max zstar istar pp m c E).
  - by rewrite hus (size_digest_of PP M Hgrind zstar istar).
- (* KFORGE: lhs is [ret false]; everything on the rhs is one-sided *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_rhs => pko'.
  case: pko' => [pk|]; last first.
  + (* pre-commitment: ideal PCHECK answers false *)
    simpl.
    rewrite (resolve_pr_ck_false 0 n0).
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [hinv _].
  + simpl.
    eapply r_get_remember_rhs => lg'.
    eapply r_get_remember_rhs => sgov.
    eapply (r_fact (exists (m : M) (c : nat) (us : seq N),
              [/\ lg' = [:: m],
                  sgov = Some (wsigs pk.1 0 (wdigest pk.1 m c) us, c),
                  size us = l & wgood pk.1 m c])).
      { move=> s0 s1 [[[hinv h1] h2] h3].
        case/pr_invE: hinv => _ [e1 e2 e3 hmatch].
        rewrite /rem_inv /= in h1 h2 h3.
        rewrite -e1 h1 in hmatch.
        case: hmatch => mm [cc [uss [hA hB _ [husz hgood] _]]].
        exists mm, cc, uss; split=> //.
        - by rewrite -h2 e2.
        - by rewrite -h3 e3. }
    move=> [m [c [us [hlg hsgov husz hgood]]]].
    rewrite hlg hsgov /=.
    case E0: (wverify pk.1 pk.2 mst sgst && (mst \notin [:: m]));
      last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[hinv _] _] _].
    * case/andP: (E0) => hver hfresh.
      case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B).
      -- apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[hinv _] _] _].
      -- case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                    != wcends pk.1 (wdigest pk.1 m c)
                         (wsigs pk.1 0 (wdigest pk.1 m c) us))%B).
         ++ apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[hinv _] _] _].
         ++ case E3: (wtcr_dec pk.1 (wdigest pk.1 m c)
                        (wdigest pk.1 mst sgst.2)
                        (wsigs pk.1 0 (wdigest pk.1 m c) us) sgst.1)
              => [ju|].
            ** apply r_ret => s0 s1 hpre; split=> //.
               by case: hpre => [[[hinv _] _] _].
            ** case E4: (wpre_dec pk.1 (wdigest pk.1 m c)
                           (wdigest pk.1 mst sgst.2)
                           (wsigs pk.1 0 (wdigest pk.1 m c) us) sgst.1)
                 => [[j x]|]; last first.
               --- (* dead branch: the classifier is total on the
                      CHAIN branch (wclassify_some) *)
                   eapply (r_fact False); last by [].
                   move=> s0 s1 _.
                   have hned := negbT E1.
                   have hends : wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                                = wcends pk.1 (wdigest pk.1 m c)
                                    (wsigs pk.1 0 (wdigest pk.1 m c) us).
                     { by move/negbFE/eqP: E2. }
                   move: (hver); rewrite /verify_sig => /and3P[hvd' hys _].
                   have := wclassify_some pk.1 m mst c sgst.2 us sgst.1
                             hgood husz hvd' hys hends hned E3.
                   by rewrite E4 eqxx.
               --- (* ChainMeet: ideal PCHECK answers false, as does
                      G1w-ideal *)
                   simpl.
                   rewrite (resolve_pr_ck_false j x).
                   apply r_ret => s0 s1 hpre; split=> //.
                   by case: hpre => [[[hinv _] _] _].
Qed.

End ChainHop.
