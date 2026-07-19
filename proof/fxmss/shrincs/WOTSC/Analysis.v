(** * SHRINCS.WOTSC.Analysis

    The PURE forgery-analysis layer of the WOTS+C one-time security
    proof (P5; plan in theories/SHRINCS/WOTSC/PROOF_PLAN.md): the
    four-way forgery classifier [wotsc_forgery_classify] and the
    SM-TCR(F) target bookkeeping at encoded chain addresses.

    Counterpart: wotsc.tex, one-time security paragraph ("An
    adversary who observes a valid pair (mes, sigma) and attempts to
    forge ... if every a_i' were at least a_i, equality of sums would
    force a_i' = a_i for all i, in which case the forger must find
    [a] target collision fo[r] Hgrind ... Otherwise some a_i' < a_i
    and the forger must invert F at some position"), refined into the
    four cases the game hops consume.  Style + REUSE:
    theories/Examples/FixedSumOTS/Analysis.v — the WOTS+C chain layer
    IS that example at the address-wrapped chain hash [Fw] (defined
    in WOTSC.Games), so the per-chain classification
    ([forgery_cases]), the PRE post-processing
    ([forgery_pre_preimage]), the digit selector ([forged_digit_lt],
    [eq_sumn_exists_lt]) and the whole TCR bookkeeping
    ([tcr_targets]/[tcr_index]/...) are instantiated, not re-proved.

    ** The four cases (the disjuncts of [wotsc_forgery_classify])

    Signed: message [m], counter [c] (grinding success, [good_ctr]),
    digest [d := digest_of pp m c], per-chain signature values [sg]
    (in G1w these are [sample_sig_roots] outputs re-rooted at the
    digits of [d]), public key
    [pk := Tl pp pk_adrs (complete_ends pp d sg)].
    Forged: fresh [mstar != m] with signature [(ystar, cstar)] that
    verifies; verification forces [dstar := digest_of pp mstar cstar]
    valid ([valid_digest]), [size ystar = l], and the recompressed
    completed ends to hit [pk].

    1. GRIND ([dstar = d] as digit vectors): both digests are < w^l
       (the [Hrange] side condition), and [digits_w] is injective
       there ([digits_w_inj]), so the two Hgrind OUTPUTS collide:
       [Hgrind pp grind_adrs (mstar, cstar) = Hgrind pp grind_adrs
       (m, c)] with [mstar != m] — exactly STCRP's SCHECK win at the
       single committed grinding target (whose stored counter is [c]
       by Games.[grind_search_find_ctr]): the reduction feeds
       SCHECK (0, (mstar, cstar)).
    2. COMPRESS ([dstar != d] but the completed ends differ while
       their Tl compressions agree): SM-TCR(Tl) collision at the
       single committed target (encode_adrs pk_adrs, honest ends):
       the reduction feeds CHECK (0, complete_ends pp dstar ystar).
    3. CHAIN COLLISION ([dstar != d], completed ends EQUAL): both
       digit vectors sum to S_wn, so some chain [i] has
       [dstar_i < d_i] ([forged_digit_lt]); walking both chains
       forward ([chain_extract]) finds [k] with an F-collision
       against the honest chain value at position [k >= d_i] — the
       input the reduction committed at tweak
       [encode_adrs (chain_adrs i k)] ([wotsc_tcr_targets]): it feeds
       CHECK (tcr_index w d i k, u), recomputing [u] by re-running
       [chain_extract] (which is how it decides case 3 vs 4, exactly
       FixedSumOTS.TCRHop's [tcr_decision] pattern).
    4. CHAIN MEET (otherwise): the forged chain reaches [sg_i] at
       position [d_i] (note [0 < d_i] since [dstar_i < d_i]); one
       step earlier it is an F-preimage of [sg_i] at tweak
       [encode_adrs (chain_adrs i (d_i - 1))].  In G1w with
       [d_i > 0], [sg_i = F pp (chain_adrs i (d_i - 1)) u_i] for a
       hidden uniform [u_i] — the SM-PRE oracle's answer — so the
       reduction feeds PCHECK (index of chain i, that preimage).

    ** The Hrange side condition

    Case 1 needs equal digit VECTORS to give equal Hgrind OUTPUTS;
    [digits_w w l] is only injective below [w ^ l], so
    [wotsc_forgery_classify] takes the DATA-level side condition
    [Hrange : forall pp a x, Hgrind pp a x < w ^ l] as an explicit
    lemma argument (NOT a section hypothesis; docs/STYLE.md rule 2).
    It is discharged at instantiation: the tex's Hgrind outputs n-bit
    strings parsed as exactly l base-w digits (l = ceil(n / log w)),
    i.e. the digest space embeds into [0, w^l).

    ** TCR bookkeeping at encoded tweaks

    The SM-TCR(F) game's tweak space is [adrs_sf_ch], so the
    committed target list re-tags FixedSumOTS's [tcr_targets] with
    [wotsc_tweak (i, k) := encode_adrs (chain_adrs i k)] (injective:
    [encode_adrs_inj] + [chain_adrs_inj]); positions in the list are
    unchanged, so FixedSumOTS's [tcr_index w] IS the CHECK index
    (chosen over a nat*nat-tweaked wrapper thf so that all three
    instances of WOTSC.Games share one tweak space and the
    distinct-address lemmas of SHRINCS.Addressing apply directly). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

Section WOTSCAnalysis.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same section context as SHRINCS.WOTSC.Scheme, minus the samplers
    (this layer is pure). *)
Context (PP N M : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).
Context (S_wn c_max : nat).
Context (zstar istar : nat).

(** The address-wrapped chain hash of WOTSC.Games (the FixedSumOTS
    reuse bridge) and the section-instantiated scheme operations. *)
Local Notation FW := (Fw PP N F zstar istar).
Local Notation cf := (chainf PP N F zstar istar).
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation cadrs := (chain_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation wdigest := (digest_of PP M Hgrind zstar istar).
Local Notation wgood := (good_ctr PP M Hgrind S_wn zstar istar).
Local Notation wcends := (complete_ends PP N F zstar istar).
Local Notation wverify :=
  (verify_sig PP N M F Tl Hgrind S_wn zstar istar).
Local Notation vdigest := (@valid_digest w S_wn).

(* ------------------------------------------------------------------ *)
(** *** Bridges into the FixedSumOTS analysis

    All by conversion ([Fw] beta-reduces to [F] at [chain_adrs], and
    WOTSC's verifier-side [complete_ends] is literally FixedSumOTS's
    [ends_from_sig] at [FW]); stated once so the proofs below can
    rewrite instead of relying on implicit conversion. *)

Lemma wcendsE pp (ds : seq nat) (ys : seq N) :
  wcends pp ds ys = ends_from_sig PP N FW l w pp ds ys.
Proof. by []. Qed.

(** A grinded digest is a valid FixedSumOTS message (digit vector of
    size l, digits < w, digit sum S_wn) — the digit-selector lemmas
    [forged_digit_lt] / [valid_msg_digit] apply to digests. *)
Lemma vdigest_valid_msg pp (m : M) c :
  vdigest (wdigest pp m c) -> valid_msg l w S_wn (wdigest pp m c).
Proof.
case/andP=> h1 h2.
by rewrite /valid_msg (size_digest_of PP M Hgrind zstar istar) eqxx h1 h2.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Case 1 (GRIND): digit-vector equality lifts to Hgrind-output
    equality

    [digits_w w l] is injective below [w ^ l] ([digits_w_inj]); the
    degenerate radix [w = 0] is handled separately (then [Hrange]
    forces [l = 0] and both outputs are 0). *)

Lemma wdigest_inj pp (m1 : M) (c1 : nat) (m2 : M) (c2 : nat) :
  (0 < w)%N ->
  (forall (pp' : PP) (a : adrs_sf) (x : M * nat), Hgrind pp' a x < w ^ l) ->
  wdigest pp m1 c1 = wdigest pp m2 c2 ->
  Hgrind pp gadrs (m1, c1) = Hgrind pp gadrs (m2, c2).
Proof.
move=> hw Hr heq.
have h1 := Hr pp gadrs (m1, c1).
have h2 := Hr pp gadrs (m2, c2).
exact: (digits_w_inj hw h1 h2 heq).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Cases 3/4 (CHAINS): the per-chain classifier at WOTS+C
    addresses

    [forgery_cases] of FixedSumOTS.Analysis instantiated at [FW]; the
    statement is restated with WOTSC's [chainf] and explicit
    [chain_adrs] tweaks (convertible), so consumers never see [FW]'s
    pair tweaks. *)

Lemma wotsc_chain_cases pp i d (sigi : N) dstar (sigstar : N) :
  dstar < d -> d < w ->
  chain (cf pp i) sigstar dstar (w.-1 - dstar)
    = chain (cf pp i) sigi d (w.-1 - d) ->
  match chain_extract (cf pp i) sigstar dstar sigi d w.-1 with
  | ChainColl k u v =>
      [/\ d <= k < w.-1,
          v = chain (cf pp i) sigi d (k - d),
          u != v
        & F pp (cadrs i k) u = F pp (cadrs i k) v]
  | ChainMeet => chain (cf pp i) sigstar dstar (d - dstar) = sigi
  end.
Proof. exact: (forgery_cases PP N FW w pp i d sigi dstar sigstar). Qed.

(** Case-4 post-processing ([forgery_pre_preimage] at [FW]): a chain
    meet at position [d] yields the F-preimage of [sigi] at chain
    address (i, d-1) that wins SM-PRE's PCHECK. *)
Lemma wotsc_pre_preimage pp i d (sigi sigstar : N) (dstar : nat) :
  dstar < d ->
  chain (cf pp i) sigstar dstar (d - dstar) = sigi ->
  F pp (cadrs i d.-1) (chain (cf pp i) sigstar dstar (d.-1 - dstar)) = sigi.
Proof. exact: (forgery_pre_preimage PP N FW pp i d sigi sigstar dstar). Qed.

(** nth-form access to an equality of completed-ends lists: at every
    chain [i < l] the forged completion hits the honest one (via
    [ends_from_sig_nth] at [FW], twice). *)
Lemma wcends_nth_eq pp (ds ds' : seq nat) (ys ys' : seq N) (y0 : N) i :
  size ds = l -> size ys = l -> size ds' = l -> size ys' = l -> i < l ->
  wcends pp ds ys = wcends pp ds' ys' ->
  chain (cf pp i) (nth y0 ys i) (nth 0 ds i) (w.-1 - nth 0 ds i)
  = chain (cf pp i) (nth y0 ys' i) (nth 0 ds' i) (w.-1 - nth 0 ds' i).
Proof.
move=> h1 h2 h3 h4 hi /(congr1 (fun s => nth y0 s i)).
rewrite !wcendsE (ends_from_sig_nth PP N FW l w pp ds ys y0 i h1 h2 hi)
        (ends_from_sig_nth PP N FW l w pp ds' ys' y0 i h3 h4 hi).
exact: id.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE four-way forgery classifier

    Hypotheses are exactly what G1w's KFORGE provides on a winning
    real run: the grinding fact for the signed counter
    ([find_ctr_isSome_good] of WOTSC.Games delivers [wgood] from the
    COMMIT assert), the stored signature size (G1w samples one root
    per digit of a length-l digest), the verification of the forgery
    against the stored public key, and log-freshness ([notin_log_neq]
    below).  Each disjunct carries the data its reduction feeds to
    the corresponding check oracle (header). *)

Lemma wotsc_forgery_classify
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : M * nat),
        Hgrind pp' a x < w ^ l)
    pp (m mstar : M) (c cstar : nat) (sg ystar : seq N) (y0 : N) :
  (0 < w)%N ->
  wgood pp m c ->
  size sg = l ->
  wverify pp (Tl pp padrs (wcends pp (wdigest pp m c) sg))
    mstar (ystar, cstar) ->
  mstar != m ->
  [\/ (* 1: GRIND — SCHECK (0, (mstar, cstar)) wins STCRP(Hgrind) *)
      Hgrind pp gadrs (mstar, cstar) = Hgrind pp gadrs (m, c)
   ,  (* 2: COMPRESS — CHECK (0, forged ends) wins SM-TCR(Tl) *)
      wcends pp (wdigest pp mstar cstar) ystar
        != wcends pp (wdigest pp m c) sg
      /\ Tl pp padrs (wcends pp (wdigest pp mstar cstar) ystar)
         = Tl pp padrs (wcends pp (wdigest pp m c) sg)
   ,  (* 3: CHAIN COLLISION — CHECK (tcr_index w d i k, u) wins
         SM-TCR(F) at tweak encode_adrs (chain_adrs i k); the stored
         target input is the honest chain value u is compared to *)
      exists i k (u : N),
        [/\ i < l,
            nth 0 (wdigest pp m c) i <= k < w.-1,
            u != chain (cf pp i) (nth y0 sg i) (nth 0 (wdigest pp m c) i)
                       (k - nth 0 (wdigest pp m c) i)
          & F pp (cadrs i k) u
            = F pp (cadrs i k)
                (chain (cf pp i) (nth y0 sg i) (nth 0 (wdigest pp m c) i)
                       (k - nth 0 (wdigest pp m c) i))]
   |  (* 4: CHAIN MEET — PCHECK (pre-index of i, preimage) wins
         SM-PRE(F) at tweak encode_adrs (chain_adrs i (d_i - 1)) *)
      exists i,
        [/\ i < l,
            nth 0 (wdigest pp mstar cstar) i < nth 0 (wdigest pp m c) i
          & F pp (cadrs i (nth 0 (wdigest pp m c) i).-1)
              (chain (cf pp i) (nth y0 ystar i)
                     (nth 0 (wdigest pp mstar cstar) i)
                     ((nth 0 (wdigest pp m c) i).-1
                        - nth 0 (wdigest pp mstar cstar) i))
            = nth y0 sg i]
  ].
Proof.
move=> hw hgood hsg hver hne.
have hvd : vdigest (wdigest pp m c) := hgood.
move: hver; rewrite /verify_sig /= => /and3P[hvd' /eqP hsy /eqP hTl].
case: (altP (wdigest pp mstar cstar =P wdigest pp m c)) => [heqd|hned].
- (* 1: equal digit vectors *)
  by apply: Or41; apply: (wdigest_inj pp mstar cstar m c hw Hrange heqd).
- case: (altP (wcends pp (wdigest pp mstar cstar) ystar
                 =P wcends pp (wdigest pp m c) sg)) => [heqe|hnee]; last first.
  + (* 2: distinct ends, equal compression (from verification) *)
    by apply: Or42; split.
  + (* 3/4: equal ends; select the down-going chain and classify *)
    have hvm : valid_msg l w S_wn (wdigest pp m c)
      := vdigest_valid_msg pp m c hvd.
    have hvm' : valid_msg l w S_wn (wdigest pp mstar cstar)
      := vdigest_valid_msg pp mstar cstar hvd'.
    have [i hi hlt] := forged_digit_lt l w S_wn (wdigest pp m c)
                         (wdigest pp mstar cstar) hvm hvm' hned.
    have hdw : nth 0 (wdigest pp m c) i < w
      := valid_msg_digit l w S_wn (wdigest pp m c) i hvm hi.
    have hsz : size (wdigest pp m c) = l
      := size_digest_of PP M Hgrind zstar istar pp m c.
    have hsz' : size (wdigest pp mstar cstar) = l
      := size_digest_of PP M Hgrind zstar istar pp mstar cstar.
    have hch := wcends_nth_eq pp _ _ _ _ y0 i hsz' hsy hsz hsg hi heqe.
    have := wotsc_chain_cases pp i (nth 0 (wdigest pp m c) i) (nth y0 sg i)
              (nth 0 (wdigest pp mstar cstar) i) (nth y0 ystar i) hlt hdw hch.
    case: (chain_extract _ _ _ _ _ _) => [k u v|].
    * (* 3 *)
      case=> hk hv hneuv hcol.
      apply: Or43; exists i, k, u.
      by rewrite -hv; split.
    * (* 4 *)
      move=> hmeet.
      apply: Or44; exists i; split=> //.
      exact: (wotsc_pre_preimage pp i (nth 0 (wdigest pp m c) i)
               (nth y0 sg i) (nth y0 ystar i)
               (nth 0 (wdigest pp mstar cstar) i) hlt hmeet).
Qed.

(** KFORGE's log freshness in the form the classifier consumes (the
    log of G0w/G1w is the single signed message). *)
Lemma notin_log_neq (m mstar : M) : mstar \notin [:: m] -> mstar != m.
Proof. by rewrite inE. Qed.

(* ------------------------------------------------------------------ *)
(** *** Case-3 target bookkeeping at encoded chain addresses

    FixedSumOTS's committed-target list [tcr_targets] (one target per
    (chain, position >= signed digit), lexicographic, list position =
    CHECK index) re-tagged with encoded chain addresses; positions
    are untouched, so [tcr_index w] and [tcr_index_lt] of
    FixedSumOTS.Analysis are consumed UNCHANGED (no wrapper here). *)

Definition wotsc_tweak (ik : nat * nat) : adrs_sf_ch :=
  encode_adrs (cadrs ik.1 ik.2).

(** Distinct representable (chain, position) pairs are distinct encoded
    tweaks.  The range premises are necessary because the native address
    space is finite. *)
Lemma wotsc_tweak_inj (ik ik' : nat * nat) :
  anchor_bounded (zstar, istar) ->
  (ik.1 < l)%nat -> (ik'.1 < l)%nat ->
  (ik.2 < w.-1)%nat -> (ik'.2 < w.-1)%nat ->
  wotsc_tweak ik = wotsc_tweak ik' -> ik = ik'.
Proof.
move: ik ik' => [i k] [i' k'] /= Ha hi hi' hk hk'.
move/encode_adrs_inj=> h.
apply: (@chain_adrs_inj w l zstar istar i k i' k' Ha).
- exact: component_bounded_lt.
- exact: component_bounded_lt.
- exact: component_bounded_lt.
- exact: component_bounded_lt.
- exact: h.
Qed.

Definition wotsc_tcr_targets (pp : PP) (ds : seq nat) (sigs : seq N) :
    seq (adrs_sf_ch * N) :=
  [seq (wotsc_tweak q.1, q.2) | q <- tcr_targets PP N FW l w pp ds sigs].

Lemma size_wotsc_tcr_targets pp (ds : seq nat) (sigs : seq N) :
  size ds = l -> size sigs = l ->
  size (wotsc_tcr_targets pp ds sigs) = sumn [seq w.-1 - d | d <- ds].
Proof.
move=> h1 h2; rewrite size_map.
exact: (size_tcr_targets PP N FW l w pp ds sigs h1 h2).
Qed.

(** The SM-TCR budget [l * w] suffices for the full list. *)
Lemma size_wotsc_tcr_targets_leq pp (ds : seq nat) (sigs : seq N) :
  size ds = l -> size sigs = l ->
  size (wotsc_tcr_targets pp ds sigs) <= l * w.
Proof.
move=> h1 h2; rewrite size_map.
exact: (size_tcr_targets_leq PP N FW l w pp ds sigs h1 h2).
Qed.

(** The CHECK index of target (i, k) is in range. *)
Lemma wotsc_tcr_index_lt pp (ds : seq nat) (sigs : seq N) i k :
  size ds = l -> size sigs = l -> i < l -> nth 0 ds i <= k < w.-1 ->
  tcr_index w ds i k < size (wotsc_tcr_targets pp ds sigs).
Proof.
move=> h1 h2 hi hk.
rewrite size_wotsc_tcr_targets //.
exact: (tcr_index_lt l w ds i k h1 hi hk).
Qed.

(** THE bookkeeping lemma: at CHECK index [tcr_index w ds i k] the
    reduction committed exactly the encoded chain address (i, k) with
    input the honest chain value at [k] (recomputed from the [i]-th
    signature value) — disjunct 3 of [wotsc_forgery_classify] maps to
    a winning CHECK query against this target. *)
Lemma wotsc_tcr_targets_nth pp (ds : seq nat) (sigs : seq N) i k
    (x0 : adrs_sf_ch * N) (y0 : N) :
  size ds = l -> size sigs = l -> i < l -> nth 0 ds i <= k < w.-1 ->
  nth x0 (wotsc_tcr_targets pp ds sigs) (tcr_index w ds i k)
  = (encode_adrs (cadrs i k),
     chain (cf pp i) (nth y0 sigs i) (nth 0 ds i) (k - nth 0 ds i)).
Proof.
move=> hds hsigs hi hk.
have hlt : tcr_index w ds i k < size (tcr_targets PP N FW l w pp ds sigs).
  rewrite (size_tcr_targets PP N FW l w pp ds sigs hds hsigs).
  exact: (tcr_index_lt l w ds i k hds hi hk).
rewrite /wotsc_tcr_targets (nth_map ((0, 0), y0)) //.
by rewrite (tcr_targets_nth PP N FW l w pp ds sigs i k ((0, 0), y0) y0).
Qed.

(** Tweak distinctness of the committed list (the TQUERY freshness
    assert passes at every commit in list order). *)
Lemma wotsc_tcr_targets_tweaks_uniq pp (ds : seq nat) (sigs : seq N) :
  anchor_bounded (zstar, istar) ->
  size ds = l -> uniq (unzip1 (wotsc_tcr_targets pp ds sigs)).
Proof.
move=> Ha hds.
have he : (fst \o (fun q : (nat * nat) * N => (wotsc_tweak q.1, q.2)))
            =1 (wotsc_tweak \o fst).
  by [].
have hinj : {in unzip1 (tcr_targets PP N FW l w pp ds sigs) &,
              injective wotsc_tweak}.
  move=> x y hx hy.
  have [hx1 hx2] :=
    tcr_targets_mem_range PP N FW l w pp ds sigs x hds hx.
  have [hy1 hy2] :=
    tcr_targets_mem_range PP N FW l w pp ds sigs y hds hy.
  exact: (wotsc_tweak_inj x y Ha hx1 hy1 hx2 hy2).
rewrite /wotsc_tcr_targets /unzip1 -map_comp (eq_map he) map_comp.
rewrite (map_inj_in_uniq hinj).
exact: (tcr_targets_tweaks_uniq PP N FW l w pp ds sigs hds).
Qed.

End WOTSCAnalysis.
