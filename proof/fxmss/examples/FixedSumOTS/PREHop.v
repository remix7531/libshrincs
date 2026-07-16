(** * HBS.Examples.FixedSumOTS.PREHop

    The SM-PRE reduction package of the FixedSumOTS security proof
    (PROOF_PLAN.md, step "G1 -> SM-TCR + SM-PRE split", PRE half) and
    its perfect equivalences on BOTH sides of the SM-PRE pair:

      [R_pre_real  : perfect (I_KOTS FS) (Gmid ...)
                             (R_pre ∘ SMPRE_game Tots Cots l true)]
      [R_pre_ideal : perfect (I_KOTS FS) (G1v ... false)
                             (R_pre ∘ SMPRE_game Tots Cots l false)]

    where [Gmid] (TCRHop.v) is G1v-real with KFORGE answering false on
    the classifier's TCR case.  Together with TCRHop's lemmas this
    closes the forgery-split triangle:
      Adv (G1v true) (G1v false)
        <= AdvOf SMTCR (A ∘ R_tcr) + AdvOf SMPRE (A ∘ R_pre).

    ** Design (deviations from the obvious transliteration)

    - One PQUERY per chain with POSITIVE digit, in chain order: chain
      [i] with digit [d_i >= 1] queries tweak [(i, d_i - 1)]; the
      oracle samples the hidden uniform [u_i] and answers
      [F pp (i, d_i - 1) u_i] — EXACTLY [sample_sig_roots]' d>=1
      branch.  Chains with [d_i = 0] sample their digit locally
      (d=0 branch of [sample_sig_roots]).  The CHECK index of chain
      [i]'s query is [pre_index m i] (= number of positive digits
      before [i]); bookkeeping lemma [qnth_pre_queries].
    - PCOLLQ pin (UDHop's UCOLLQ trick): PQUERY hides [pp] and chains
      with digit 0 make no query at all (for an all-zero message there
      is NO PQUERY), so unlike TCRHop there is no query that reliably
      aligns SM-PRE's lazy [pp] with the game's eager one.  COMMIT
      therefore calls PCOLLQ (trivial collection, no phase guard)
      FIRST, pinning [pp]'s sampling to one fixed program point before
      all per-chain samples.  No sampler commutation and NO side
      conditions [0 < l] / [1 < w] are needed (the side-condition
      route of TCRHop is not taken).
    - KFORGE mirrors Gmid's: getSome pk, read log and stored sigs,
      [v := verify_sig ... && (mstar \notin log)]; if [~~v] ret false;
      then the SAME classifier [tcr_decision] (reused from TCRHop.v):
      on [Some _] (ChainColl) ret false — matching Gmid and
      G1v-false alike; on [None] the computable PRE classifier
      [pre_decision] recomputes the chain and submits
      [PCHECK (pre_index m i, chain (cf pp i) σ*_i d*_i (d_i.-1 - d*_i))]
      ([Analysis.forgery_pre_preimage]: that value is an F-preimage of
      σ_i at tweak (i, d_i.-1), and σ_i = F pp (i,d_i.-1) u_i is the
      oracle's answer on the hidden u_i, so real PCHECK answers true =
      Gmid's answer; ideal PCHECK answers false = G1v-false's answer).
      The (tcr = None ∧ pre = None) branch is DEAD on a verifying
      fresh forgery ([classify_some]); its code (ret true) is never
      related.
    - PRE-COMMIT KFORGE GADGET (deviation, documented): Gmid's KFORGE
      FAILS before a commitment (getSome assert), while G1v-false's
      KFORGE is [ret false].  R_pre must reproduce this real/ideal
      difference through the SM-PRE oracles; the only [b]-dependent
      oracle is PCHECK (real: phase assert [revealed], which FAILS
      pre-commitment; ideal: ret false).  So on [pko = None] KFORGE
      calls [PCHECK (0, n0)] and returns the answer.  Forming the
      argument needs an inhabitant [n0 : N] of the abstract hash
      domain: SIDE CONDITION [Context (n0 : N)] on this whole file
      (trivially satisfied by any instantiation; bitstring domains
      are inhabited).  Sampling [n0 ← dN] instead is unsound here: an
      abstract [dist] need not be lossless, and the ideal side would
      have to cancel a one-sided sample against G1v-false's plain
      [ret false].
    - Budget: [l] (one PQUERY per positive-digit chain;
      [npq m <= size m = l]).

    Locations 240+ ([rp_pk_loc]/[rp_log_loc]/[rp_sig_loc] = 240-242).
    The proof architecture (block precondition [pblk_pre], bind-headed
    one-sided rules, per-chain induction [rp_chains_spec], final-phase
    [pfin_pre]) reuses TCRHop.v's machinery and lessons verbatim;
    the generic rules ([r_fact], [r_get_bind_rhs], [r_put2_bind_rhs],
    [qnth]/[qmap_from], [heap_ignore_set_l/r], [lt_notin]) are
    imported from TCRHop.v. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp.experimental_reals Require Import distr.
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Games.SMPRE Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop.
From SSProve.Crypt Require Import SubDistr Couplings.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic rules missing from TCRHop's kit *)

(** A failing program is related to any bind whose head fails (the
    composite has null semantics).  Used for the pre-commitment
    KFORGE gadget: Gmid's [getSome] assert on the left, the linked
    real PCHECK's phase assert on the right (under a continuation).
    Same semantic proof as SSProve's [r_fail]. *)
Lemma r_fail_bind_rhs {A B C : choice_type} (k : B -> raw_code C)
    (pre : precond) (post : postcond A C) :
  ⊢ ⦃ pre ⦄ @fail A ≈ bind (@fail B) k ⦃ post ⦄.
Proof.
eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
intros [hpre hpost]. simpl.
exists dnull. split.
- unfold coupling. split.
  + unfold lmg. apply distr_ext.
    intro. unfold dfst. rewrite dlet_null.
    unfold SDistr_bind. rewrite dlet_null.
    reflexivity.
  + unfold rmg. apply distr_ext.
    intro. unfold dsnd. rewrite dlet_null.
    unfold SDistr_bind. rewrite dlet_null.
    reflexivity.
- intros [? ?] [? ?]. rewrite dnullE.
  rewrite Order.POrderTheory.ltxx. discriminate.
Qed.

(** [qnth] through a cons (definitional; companion to TCRHop's
    [qnth_cat_l/r]). *)
Lemma qnth_cons {X : Type} (e : X) (s : seq X) (k : nat) :
  qnth (e :: s) k.+1 = qnth s k.
Proof. by []. Qed.

Section FixedSumOTSPREHop.

(** Same section context as FixedSumOTS.Games / Analysis / TCRHop,
    plus the inhabitant [n0] of the hash domain (see header). *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (l w tsum : nat).
Context (n0 : N).

Local Notation FS := (FixedSumOTS PP N F dPP dN l w tsum).
Local Notation TT := (Tots PP N F dPP dN).
Local Notation CC := (Cots PP N F dPP dN).
Local Notation cf := (chainf PP N F).

Local Notation ppl := (pre_pp_loc TT).
Local Notation tgl := (pre_tgts_loc TT).
Local Notation twl := (pre_tws_loc TT).
Local Notation rvl := pre_rev_loc.

Local Notation g0v_pk' := (g0v_pk_loc PP N F dPP dN l w tsum).
Local Notation g0v_log' := (g0v_log_loc PP N F dPP dN l w tsum).
Local Notation gm_sig' := (gm_sig_loc N).

Local Notation SMPB b := (SMPRE_game TT CC l b).

(* ------------------------------------------------------------------ *)
(** *** Pure layer: committed PRE targets, indices *)

(** The committed (tweak, hidden input) pairs (SM-PRE's target entry
    carrier). *)
Local Notation qentry := ((nat * nat) * N)%type.

(** Queries of one chain: one PQUERY at [(i, d-1)] for positive
    digits, none for digit 0.  The stored entry is the HIDDEN input
    [u] (the game samples it; the reduction never sees it — [u] only
    appears in specs/invariants). *)
Definition pre_query (i d : nat) (u : N) : seq qentry :=
  if d is d'.+1 then [:: ((i, d'), u)] else [::].

(** Full committed list, chains [st, st+1, ...] with digits [ds] and
    hidden inputs [us]. *)
Definition pre_queries (st : nat) (ds : seq nat) (us : seq N) :
    seq qentry :=
  flatten [seq pre_query q.1 q.2.1 q.2.2
          | q <- zip (iota st (size ds)) (zip ds us)].

Lemma pre_queries_cons st d ds u us :
  pre_queries st (d :: ds) (u :: us)
  = pre_query st d u ++ pre_queries st.+1 ds us.
Proof. by []. Qed.

(** Number of PQUERYs of a digit list / budget cap. *)
Definition npq (ds : seq nat) : nat := count (λ d, 0 < d) ds.

Lemma npq_le (ds : seq nat) : size ds = l -> npq ds <= l.
Proof. by move=> h; rewrite -h; exact: count_size. Qed.

(** CHECK index of chain [i]'s PQUERY: the number of positive digits
    before it (the j-th PQUERY lands at fmap key j). *)
Definition pre_index (ds : seq nat) (i : nat) : nat :=
  npq (take i ds).

(** THE bookkeeping lemma: at index [pre_index ds i] the game stored
    exactly tweak [(st+i, d_i - 1)] with the hidden input [u_i]. *)
Lemma qnth_pre_queries st ds us i ui :
  size us = size ds -> i < size ds -> qnth us i = Some ui ->
  0 < nth 0 ds i ->
  qnth (pre_queries st ds us) (pre_index ds i)
  = Some (((st + i)%N, (nth 0 ds i).-1), ui).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu hd.
- case: hu => <-; rewrite addn0 /pre_index /npq take0 /=.
  by case: d hd => [|d'].
- have -> : pre_index (d :: ds) i.+1 = ((0 < d) + pre_index ds i)%N.
    by rewrite /pre_index /npq.
  rewrite pre_queries_cons -addSnnS.
  case: d hd => [|d'] hd /=.
  + by rewrite add0n; apply: IH.
  + by rewrite add1n qnth_cons; apply: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The PRE classifier (computable counterpart of the ChainMeet
    case; complement of TCRHop's [tcr_decision]) *)

(** Decide what the reduction submits to PCHECK for a forgery
    [(mstar, sgstar)] against signed message [m] with stored
    signature [sgs] under [pp]: [Some (j, x)] means "call
    PCHECK (j, x)" (the ChainMeet case at the first attacked chain),
    [None] means the ChainColl case (handled by [tcr_decision]) or a
    branch that cannot occur on a verifying forgery.  All scrutinees
    are SYNTACTICALLY the same terms as in [tcr_decision], so one
    case analysis drives both. *)
Definition pre_decision (pp : PP) (m mstar : seq nat)
    (sgs sgstar : seq N) : option (nat * N) :=
  match ohead [seq i <- iota 0 l | nth 0 mstar i < nth 0 m i] with
  | Some i =>
      match qnth sgs i, qnth sgstar i with
      | Some si, Some si' =>
          match chain_extract (cf pp i) si' (nth 0 mstar i) si
                  (nth 0 m i) w.-1 with
          | ChainColl _ _ _ => None
          | ChainMeet =>
              Some (pre_index m i,
                    chain (cf pp i) si' (nth 0 mstar i)
                          ((nth 0 m i).-1 - nth 0 mstar i))
          end
      | _, _ => None
      end
  | None => None
  end.

(** Specification of the [Some] case: the submitted message is an
    [F]-preimage of the stored target's image — PCHECK's win
    condition [F pp t x == F pp t u] at the committed index [j]. *)
Lemma pre_decisionP (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg l w tsum m -> size us = l ->
  verify_sig PP N F l w tsum pp
    (ends_from_sig PP N F l w pp m (sigs_of PP N F pp 0 m us))
    mstar sgstar ->
  mstar \notin [:: m] ->
  match pre_decision pp m mstar (sigs_of PP N F pp 0 m us) sgstar with
  | Some (j, x) =>
      exists t u,
        [/\ qnth (pre_queries 0 m us) j = Some (t, u)
          & F pp t x = F pp t u]
  | None => True
  end.
Proof.
move=> hvm hus hver hnin.
have hm : size m = l by case/and3P: hvm => /eqP.
have hussz : size us = size m by rewrite hus hm.
have hsgs : size (sigs_of PP N F pp 0 m us) = l.
  by rewrite size_sigs_of // hm.
rewrite /pre_decision.
case E1: (ohead _) => [i|]; last by [].
have hifacts : i \in [seq i0 <- iota 0 l | nth 0 mstar i0 < nth 0 m i0].
  by case: (filter _ _) E1 => //= a s [<-]; rewrite in_cons eqxx.
move: hifacts; rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
case E2: (qnth (sigs_of PP N F pp 0 m us) i) => [si|]; last by [].
case E3: (qnth sgstar i) => [si'|]; last by [].
case E4: (chain_extract _ _ _ _ _ _) => [k u v|]; first by [].
(* ChainMeet *)
have hdw : nth 0 m i < w := valid_msg_digit _ _ _ _ _ hvm hil.
have hends := size_ends_from_sig PP N F l w pp m _ hm hsgs.
have h1 := verify_sig_nth PP N F l w tsum pp _ mstar sgstar si' i
             hver hends hil.
rewrite (ends_from_sig_nth PP N F l w pp m _ si' i hm hsgs hil) in h1.
rewrite (qnth_nth si' _ _ _ E3) (qnth_nth si' _ _ _ E2) in h1.
have := forgery_cases PP N F w pp i (nth 0 m i) si (nth 0 mstar i) si'
          hlt hdw h1.
rewrite E4 => hmeet.
have hpim := forgery_pre_preimage PP N F pp i (nth 0 m i) si si'
               (nth 0 mstar i) hlt hmeet.
have hilm : i < size m by rewrite hm.
have [ui hui] : exists ui, qnth us i = Some ui.
  by apply: qnth_some; rewrite hus.
have hsig0 := qnth_sigs_of PP N F pp 0 m us i ui hussz hilm hui.
rewrite add0n E2 in hsig0.
case: hsig0 => hsig.
have hd0 : 0 < nth 0 m i := leq_ltn_trans (leq0n _) hlt.
have hsr : sig_of_root PP N F pp i (nth 0 m i) ui
           = F pp (i, (nth 0 m i).-1) ui.
  by case: (nth 0 m i) hd0.
exists ((i, (nth 0 m i).-1)), ui; split.
- by rewrite (qnth_pre_queries 0 m us i ui hussz hilm hui hd0).
- by rewrite hpim hsig hsr.
Qed.

(** Classifier completeness: on a verifying fresh forgery the
    degenerate branches cannot occur — if [tcr_decision] declined,
    [pre_decision] fires.  (Used for the DEAD (None, None) branch of
    KFORGE.) *)
Lemma classify_some (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg l w tsum m -> size us = l ->
  verify_sig PP N F l w tsum pp
    (ends_from_sig PP N F l w pp m (sigs_of PP N F pp 0 m us))
    mstar sgstar ->
  mstar \notin [:: m] ->
  tcr_decision PP N F l w pp m mstar (sigs_of PP N F pp 0 m us) sgstar
    = None ->
  pre_decision pp m mstar (sigs_of PP N F pp 0 m us) sgstar != None.
Proof.
move=> hvm hus hver hnin.
have hm : size m = l by case/and3P: hvm => /eqP.
have hsgs : size (sigs_of PP N F pp 0 m us) = l.
  by rewrite size_sigs_of // hus hm.
have hvm' : valid_msg l w tsum mstar by case/and3P: hver.
have hne : mstar != m by move: hnin; rewrite in_cons negb_or => /andP[].
have [i0 hi0 hlt0] := forged_digit_lt l w tsum m mstar hvm hvm' hne.
have hhas : has (fun i => nth 0 mstar i < nth 0 m i) (iota 0 l).
  by apply/hasP; exists i0; rewrite ?mem_iota //=.
rewrite /tcr_decision /pre_decision.
case E1: (ohead _) => [i|]; last first.
  move: E1; case Ef: (filter _ _) => [|a s] //= _.
  by move: hhas; rewrite has_filter Ef eqxx.
have hifacts : i \in [seq i1 <- iota 0 l | nth 0 mstar i1 < nth 0 m i1].
  by case: (filter _ _) E1 => //= a s [<-]; rewrite in_cons eqxx.
move: hifacts; rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
have [si E2] : exists si, qnth (sigs_of PP N F pp 0 m us) i = Some si.
  by apply: qnth_some; rewrite hsgs.
have hsgst : size sgstar = l.
  by case/and3P: hver => _ /eqP.
have [si' E3] : exists si', qnth sgstar i = Some si'.
  by apply: qnth_some; rewrite hsgst.
rewrite E2 E3.
by case: (chain_extract _ _ _ _ _ _).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

(** PQUERY/PGETPP/PCHECK/PCOLLQ opsigs as committed to I_SMPRE. *)
Definition pqo : opsig := (PQUERY, (th_T TT, th_N TT)).
Definition pgo : opsig := (PGETPP, ('unit, th_PP TT)).
Definition pco : opsig := (PCHECK, ('nat × th_M TT, 'bool)).
Definition pclo : opsig := (PCOLLQ, (tc_T CC × tc_M CC, tc_N CC)).

(** All chains from index [st] with digits [ds]: positive digits make
    the sigma PQUERY (the oracle hides the root and answers the
    signature digit), zero digits sample the digit locally; returns
    the signature digits. *)
Fixpoint rp_chains (st : nat) (ds : seq nat) : raw_code (chList N) :=
  match ds with
  | [::] => ret [::]
  | d :: ds' =>
      s ← (if d is d'.+1
           then opr pqo (st, d') (λ y, ret y)
           else (dN : raw_code N)) ;;
      ss ← rp_chains st.+1 ds' ;;
      ret (s :: ss)
  end.

#[local] Instance rp_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMPRE TT CC) (rp_chains st ds).
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

(** R's own locations (ids 240+ per the task). *)
Definition rp_pk_loc := mkloc 240 (None : option (Pk FS)).
Definition rp_log_loc := mkloc 241 ([::] : seq (Msg FS)).
Definition rp_sig_loc := mkloc 242 ([::] : seq N).

(** THE reduction: plays [I_KOTS FS] using the SM-PRE oracles.  See
    the header for the PCOLLQ pin in COMMIT and the pre-commitment
    PCHECK gadget in KFORGE. *)
Definition R_pre : package (I_SMPRE TT CC) (I_KOTS FS) :=
  [package [fmap rp_pk_loc ; rp_log_loc ; rp_sig_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get rp_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      _ ← opr pclo (Datatypes.tt, Datatypes.tt) (λ x, ret x) ;;
      sgs ← rp_chains 0 m ;;
      pp ← opr pgo Datatypes.tt (λ p, ret p) ;;
      #put rp_pk_loc := Some (pp, ends_from_sig PP N F l w pp m sgs) ;;
      #put rp_log_loc := [:: m] ;;
      #put rp_sig_loc := sgs ;;
      ret ((pp, ends_from_sig PP N F l w pp m sgs), Some sgs)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(mst, sgst) {
      pko ← get rp_pk_loc ;;
      match pko with
      | Some pk =>
          log ← get rp_log_loc ;;
          sgs ← get rp_sig_loc ;;
          if verify_sig PP N F l w tsum pk.1 pk.2 mst sgst
             && (mst \notin log)
          then
            match tcr_decision PP N F l w pk.1 (head [::] log) mst
                    sgs sgst with
            | Some _ => ret false
            | None =>
                match pre_decision pk.1 (head [::] log) mst sgs sgst with
                | Some ju => opr pco ju (λ ans, ret ans)
                | None => ret true
                end
            end
          else ret false
      | None =>
          (* pre-commitment gadget: real PCHECK fails on the phase
             assert (mirroring Gmid's getSome), ideal PCHECK returns
             false (mirroring G1v-false). *)
          opr pco (0, n0) (λ ans, ret ans)
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies

    [resolve] of the SM-PRE game at the four opsigs, computed once
    (TCRHop's recipe).  PQUERY/PGETPP/PCOLLQ are b-independent; PCHECK
    is resolved separately for each bit. *)

Section PREMachineryB.

Context (b : bool).

Lemma resolve_pq (t : nat * nat) :
  resolve (SMPB b) pqo t =
  (revealed ← get rvl ;;
   #assert ~~ revealed ;;
   tws ← get twl ;;
   #assert (size tws < l)%N ;;
   #assert (t \notin tws) ;;
   x ← dN ;;
   tgts ← get tgl ;;
   #put tgl := setm tgts (size tws) (t, x) ;;
   #put twl := rcons tws t ;;
   ppo ← get ppl ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppl := Some pp ;; ret pp
        end ;;
   ret (F pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pgp (u : unit) :
  resolve (SMPB b) pgo u =
  (ppo ← get ppl ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppl := Some pp ;; ret pp
        end ;;
   #put rvl := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pcq :
  resolve (SMPB b) pclo (Datatypes.tt, Datatypes.tt) =
  (ppo ← get ppl ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppl := Some pp ;; ret pp
        end ;;
   ret Datatypes.tt).
Proof.
by case: b; simplify_linking.
Qed.

End PREMachineryB.

Lemma resolve_pck (j : nat) (x : N) :
  resolve (SMPB true) pco (j, x) =
  (revealed ← get rvl ;;
   #assert revealed ;;
   tgts ← get tgl ;;
   match getm tgts j with
   | Some (t0, x0) =>
       ppo ← get ppl ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put ppl := Some pp ;; ret pp
            end ;;
       ret (F pp t0 x == F pp t0 x0)%B
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

Lemma resolve_pck_false (j : nat) (x : N) :
  resolve (SMPB false) pco (j, x) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The block precondition family and the per-chain induction

    TCRHop's COMMIT architecture, transplanted to the SM-PRE state:
    inside COMMIT the eq_rel_perf_ind invariant is dropped in favour
    of the EXPLICIT precondition [pblk_pre Φ ppo Q] (heaps satisfy
    the frame [Φ]; SM-PRE's four locations hold [ppo], [false],
    [unzip1 Q], [qmap_from 0 Q]); the committed-so-far list [Q] is
    the single induction variable. *)

Section PRECommitB.

Context (b : bool).

Definition pblk_pre (Φ : precond) (po : option PP) (Q : seq qentry) :
    precond :=
  λ '(s0, s1),
  [/\ Φ (s0, s1),
      get_heap s1 ppl = po,
      get_heap s1 rvl = false,
      get_heap s1 twl = unzip1 Q &
      get_heap s1 tgl = qmap_from 0 Q].

Arguments pblk_pre : simpl never.

(** Frames are insensitive to writes at SM-PRE's locations
    (ids 54-57). *)
Definition pphi_stable (Φ : precond) : Prop :=
  forall s0 s1 (ℓ : Location) (v : ℓ),
    ℓ.1 \in [:: 54; 55; 56; 57] -> Φ (s0, s1) -> Φ (s0, set_heap s1 ℓ v).

(** The PQUERY state update (put tgts; put tws). *)
Lemma pblk_pre_qupd (Φ : precond) (po : option PP) Q (t : nat * nat)
    (x : N) s0 s1 :
  pphi_stable Φ ->
  pblk_pre Φ po Q (s0, s1) ->
  pblk_pre Φ po (rcons Q (t, x))
    (s0, set_heap (set_heap s1 tgl
            (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, x)))
          twl (rcons (unzip1 Q) t)).
Proof.
move=> hΦ [h0 hpp hrev htws htgts]; split.
- by apply hΦ; [done | apply hΦ; [done | exact: h0]].
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq /unzip1 map_rcons.
- rewrite get_set_heap_neq // get_set_heap_eq.
  by rewrite qmap_from_rcons add0n size_map.
Qed.

(** The lazy parameter sampling (put pp), pinned by the PCOLLQ
    call. *)
Lemma pblk_pre_set_pp (Φ : precond) (pp : PP) Q s0 s1 :
  pphi_stable Φ ->
  pblk_pre Φ None Q (s0, s1) ->
  pblk_pre Φ (Some pp) Q (s0, set_heap s1 ppl (Some pp)).
Proof.
move=> hΦ [h0 hpp hrev htws htgts]; split.
- by apply: hΦ.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* Keep the package and the resolved oracle bodies folded under
   [simpl] inside this section (TCRHop's recipe). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMPRE_game : simpl never.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked PQUERY

    Unlike TCRHop's TQUERY (whose input is supplied by the
    reduction), PQUERY samples the hidden input INSIDE the oracle;
    the rule therefore couples the lhs's [dN] (the game's root
    sample) with the oracle's hidden one. *)

Lemma r_pquery {B : choiceType} (Φ : precond) (pp : PP)
    (t : nat * nat) (Q : seq qentry)
    (k0 k1 : N -> raw_code B) (post : postcond B B) :
  pphi_stable Φ ->
  size Q < l ->
  t \notin unzip1 Q ->
  (forall x : N,
     ⊢ ⦃ λ '(s0, s1), pblk_pre Φ (Some pp) (rcons Q (t, x)) (s0, s1) ⦄
        k0 x ≈ k1 (F pp t x) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk_pre Φ (Some pp) Q (s0, s1) ⦄
     bind dN k0 ≈ bind (resolve (SMPB b) pqo t) k1 ⦃ post ⦄.
Proof.
move=> hΦ hbud hfresh h.
rewrite resolve_pq.
eapply (r_get_bind_rhs rvl false).
  by move=> s0 s1 [_ _ hrev _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs twl (unzip1 Q)).
  by move=> s0 s1 [_ _ _ htws _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite hfresh.
move=> _.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> x; cbv beta.
eapply (r_get_bind_rhs tgl (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ htgts].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: pblk_pre_qupd hΦ hpre.
eapply (r_get_bind_rhs ppl (Some pp)).
  by move=> s0 s1 [_ hpp _ _ _].
exact: (h x).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The PCOLLQ pin

    SM-PRE's parameter is still unsampled when COMMIT starts; the
    PCOLLQ call forces its lazy initialisation, synchronized with the
    game's eager [pp ← dPP] (UDHop's UCOLLQ trick — no sampler
    commutation needed). *)

Lemma r_pcollq_pin {B : choiceType} (Φ : precond) (Q : seq qentry)
    (k0 : PP -> raw_code B) (k1 : 'unit -> raw_code B)
    (post : postcond B B) :
  pphi_stable Φ ->
  (forall pp : PP,
     ⊢ ⦃ λ '(s0, s1), pblk_pre Φ (Some pp) Q (s0, s1) ⦄
        k0 pp ≈ k1 Datatypes.tt ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk_pre Φ None Q (s0, s1) ⦄
     bind dPP k0
   ≈ bind (resolve (SMPB b) pclo (Datatypes.tt, Datatypes.tt)) k1
  ⦃ post ⦄.
Proof.
move=> hΦ h.
rewrite resolve_pcq.
eapply (r_get_bind_rhs ppl None).
  by move=> s0 s1 [_ hpp _ _ _].
cbv beta iota.
rewrite !bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> pp; cbv beta.
eapply r_put_bind_rhs.
  by move=> s0 s1 hpre; exact: pblk_pre_set_pp hΦ hpre.
exact: (h pp).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain induction

    lhs [sample_sig_roots], rhs the linked [rp_chains]; the committed
    list grows by [pre_queries] and both results are
    [sigs_of pp st ds us] of the hidden inputs. *)

Lemma rp_chains_spec {B : choiceType} (Φ : precond) (pp : PP)
    (post : postcond B B) :
  forall ds st (Q : seq qentry) (K0 K1 : chList N -> raw_code B),
  pphi_stable Φ ->
  (size Q + npq ds <= l)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), pblk_pre Φ (Some pp)
            (Q ++ pre_queries st ds us) (s0, s1) ⦄
        K0 (sigs_of PP N F pp st ds us)
      ≈ K1 (sigs_of PP N F pp st ds us) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk_pre Φ (Some pp) Q (s0, s1) ⦄
     bind (sample_sig_roots PP N F dN pp st ds) K0
   ≈ bind (code_link (rp_chains st ds) (SMPB b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st Q K0 K1 hΦ hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- rewrite /= code_link_bind.
  case: d hbud h => [|d'] hbud h.
  + (* d = 0 : both sides sample the digit locally *)
    rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> u; cbv beta.
    rewrite !bind_assoc.
    rewrite (code_link_bind (rp_chains st.+1 ds)) !bind_assoc.
    eapply IH => //.
    * by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
    * move=> us hus.
      move: (h (u :: us)); rewrite /= hus => /(_ erefl).
      by [].
  + (* d = d'.+1 : the sigma PQUERY *)
    rewrite bind_assoc.
    simpl.
    rewrite !bind_assoc.
    eapply r_pquery => //.
    * by apply: leq_trans hbud; rewrite /npq /= addnS ltnS leq_addr.
    * exact: lt_notin hfresh.
    * move=> x; cbv beta.
      rewrite !bind_assoc.
      simpl.
      rewrite (code_link_bind (rp_chains st.+1 ds)) !bind_assoc.
      eapply IH => //.
      -- by move: hbud; rewrite size_rcons /npq /= addnS addSn.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /= ltnSn.
         ++ by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
      -- move=> us hus.
         move: (h (x :: us)); rewrite /= hus => /(_ erefl).
         by rewrite pre_queries_cons /= cat_rcons.
Qed.

End PRECommitB.

(* [Arguments] directives do not survive section closing. *)
Arguments pblk_pre : simpl never.

(* ------------------------------------------------------------------ *)
(** *** The invariant of [R_pre_real]

    [heap_ignore] over all ten private locations, joined with ONE
    [rel_app] relation [RP]: Gmid's pk/log/sig mirror R's
    pk/log/sig, and R's pk determines the entire SM-PRE state
    (None: everything initial; Some pk: there exist [m, us] — [us]
    the HIDDEN oracle inputs — explaining the log, the stored
    signature, the key and the committed targets). *)

Definition IGNP : Locations :=
  [fmap g0v_pk' ; g0v_log' ; gm_sig' ; rp_pk_loc ; rp_log_loc ;
        rp_sig_loc ; ppl ; tgl ; twl ; rvl ].

Definition RP (pko : option (Pk FS)) (lg : seq (Msg FS)) (sgl : seq N)
    (pko' : option (Pk FS)) (lg' : seq (Msg FS)) (sgs : seq N)
    (po : option PP) (tg : {fmap nat -> (th_T TT × th_M TT)})
    (tw : seq (nat * nat)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgs = sgl &
      match pko with
      | None =>
          [/\ lg = [::], sgl = [::], po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists m us,
            [/\ lg = [:: m], valid_msg l w tsum m, size us = l,
                sgl = sigs_of PP N F pk.1 0 m us
              & [/\ pk.2 = ends_from_sig PP N F l w pk.1 m
                            (sigs_of PP N F pk.1 0 m us),
                    po = Some pk.1,
                    tg = qmap_from 0 (pre_queries 0 m us),
                    tw = unzip1 (pre_queries 0 m us)
                  & rv = true]]
      end].

Definition pre_inv : precond :=
  heap_ignore IGNP
  ⋊ rel_app [:: (lhs, g0v_pk') ; (lhs, g0v_log') ; (lhs, gm_sig') ;
                (rhs, rp_pk_loc) ; (rhs, rp_log_loc) ; (rhs, rp_sig_loc) ;
                (rhs, ppl) ; (rhs, tgl) ; (rhs, twl) ;
                (rhs, rvl) ] RP.

Arguments pre_inv : simpl never.

Lemma pre_invE s0 s1 :
  pre_inv (s0, s1) ->
  heap_ignore IGNP (s0, s1) /\
  RP (get_heap s0 g0v_pk') (get_heap s0 g0v_log') (get_heap s0 gm_sig')
     (get_heap s1 rp_pk_loc) (get_heap s1 rp_log_loc)
     (get_heap s1 rp_sig_loc) (get_heap s1 ppl)
     (get_heap s1 tgl) (get_heap s1 twl) (get_heap s1 rvl).
Proof. by move=> [h1 h2]; split. Qed.

Lemma pre_invI s0 s1 :
  heap_ignore IGNP (s0, s1) ->
  RP (get_heap s0 g0v_pk') (get_heap s0 g0v_log') (get_heap s0 gm_sig')
     (get_heap s1 rp_pk_loc) (get_heap s1 rp_log_loc)
     (get_heap s1 rp_sig_loc) (get_heap s1 ppl)
     (get_heap s1 tgl) (get_heap s1 twl) (get_heap s1 rvl) ->
  pre_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** [heap_ignore IGNP] is a frame for the block lemmas. *)
Lemma pphi_stable_ignp : pphi_stable (heap_ignore IGNP).
Proof.
move=> s0 s1 ℓ v hin h ℓ' hni.
rewrite get_set_heap_neq; first exact: h.
apply/eqP => e; move: hni; rewrite e.
by move: hin; rewrite !inE => /or4P[] /eqP ->; rewrite mem_domm.
Qed.

(** State family after PGETPP flipped the phase (end of COMMIT). *)
Definition pfin_pre (L : Locations) (pp : PP) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore L (s0, s1),
      get_heap s1 ppl = Some pp,
      get_heap s1 rvl = true,
      get_heap s1 twl = unzip1 Q &
      get_heap s1 tgl = qmap_from 0 Q].

Arguments pfin_pre : simpl never.

Lemma pblk_to_pfin (L : Locations) pp Q s0 s1 :
  57 \in domm L ->
  pblk_pre (heap_ignore L) (Some pp) Q (s0, s1) ->
  pfin_pre L pp Q (s0, set_heap s1 rvl true).
Proof.
move=> h57 [h0 hpp hrev htws htgts]; split.
- exact: heap_ignore_set_r h0.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The common ending of COMMIT against the real game: PGETPP, the
    puts, the returns, and the re-establishment of the invariant. *)
Lemma rp_commit_final (pp : PP) (m : seq nat) (us : seq N) :
  valid_msg l w tsum m -> size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        pblk_pre (heap_ignore IGNP) (Some pp) (pre_queries 0 m us)
          (s0, s1) ⦄
     (#put g0v_pk' := Some (pp,
        ends_from_sig PP N F l w pp m (sigs_of PP N F pp 0 m us)) ;;
      #put g0v_log' := [:: m] ;;
      #put gm_sig' := sigs_of PP N F pp 0 m us ;;
      ret ((pp, ends_from_sig PP N F l w pp m (sigs_of PP N F pp 0 m us)),
           Some (sigs_of PP N F pp 0 m us)))
   ≈ bind (resolve (SMPB true) pgo Datatypes.tt)
       (λ p,
        #put rp_pk_loc := Some (p,
          ends_from_sig PP N F l w p m (sigs_of PP N F pp 0 m us)) ;;
        #put rp_log_loc := [:: m] ;;
        #put rp_sig_loc := sigs_of PP N F pp 0 m us ;;
        ret ((p, ends_from_sig PP N F l w p m (sigs_of PP N F pp 0 m us)),
             Some (sigs_of PP N F pp 0 m us)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pre_inv (s0, s1) ⦄.
Proof.
move=> hvm hus.
rewrite resolve_pgp.
eapply (r_get_bind_rhs ppl (Some pp)).
  by move=> s0 s1 [_ hpp _ _ _].
cbv beta iota.
eapply (r_put_bind_rhs rvl true _
          (pfin_pre IGNP pp (pre_queries 0 m us))).
  by move=> s0 s1; apply: pblk_to_pfin; rewrite mem_domm.
eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hfin ->].
case: hfin => hign hpp hrev htws htgts.
split; first by [].
apply: pre_invI.
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
  by exists m, us; split=> //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_pre_real :
  perfect (I_KOTS FS) (Gmid PP N F dPP dN l w tsum)
          (R_pre ∘ SMPRE_game TT CC l true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pre_inv).
{ rewrite /pre_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pre_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hvm _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), pblk_pre (heap_ignore IGNP) None [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/pre_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  have hm : size m = l by case/and3P: hvm => /eqP.
  (* the PCOLLQ pin: align G1v's eager pp with SM-PRE's lazy one *)
  simpl.
  eapply (r_pcollq_pin true) => //.
  { exact: pphi_stable_ignp. }
  move=> pp.
  rewrite (code_link_bind (rp_chains 0 m)).
  eapply (rp_chains_spec true (heap_ignore IGNP) pp _ m 0 [::]) => //.
  { exact: pphi_stable_ignp. }
  { by rewrite /= npq_le. }
  move=> us hus.
  rewrite cat0s.
  eapply (rp_commit_final pp m us) => //.
  by rewrite hus hm.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pre_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  case: pko => [pk|]; last first.
  + (* pre-commitment: Gmid fails on the getSome assert, R fails
       inside the real PCHECK's phase assert (the gadget) *)
    simpl.
    rewrite resolve_pck.
    eapply (r_get_bind_rhs rvl false).
      { move=> s0 s1 [[hinv hrem0] hrem1].
        case/pre_invE: hinv => _ hRP.
        rewrite /rem_inv /= in hrem0 hrem1.
        case: hRP => _ _ _; rewrite hrem0 => -[_ _ _ _ [_ hrv]].
        exact: hrv. }
    cbv beta.
    exact: r_fail_bind_rhs.
  + (* committed: mirror Gmid *)
    simpl.
    eapply r_get_remember_lhs => lg.
    eapply r_get_remember_rhs => lg'.
    eapply (r_fact (lg' = lg)).
      { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
        case/pre_invE: hinv => _ [_ e2 _ _].
        rewrite /rem_inv /= in hrem0 hrem1.
        by rewrite -hrem0 -hrem1. }
    move=> e; subst lg'.
    eapply r_get_remember_lhs => sgl.
    eapply r_get_remember_rhs => sgs.
    eapply (r_fact (sgs = sgl)).
      { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
        case/pre_invE: hinv => _ [_ _ e3 _].
        rewrite /rem_inv /= in hrem0 hrem1.
        by rewrite -hrem0 -hrem1. }
    move=> e; subst sgs.
    eapply (r_fact (exists m, [/\ lg = [:: m], valid_msg l w tsum m
                & pk.2 = ends_from_sig PP N F l w pk.1 m sgl])).
      { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
        case/pre_invE: hinv => _ [_ _ e3 hmatch].
        rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6.
        rewrite h1 in hmatch.
        case: hmatch => mm [uss [hA hB hC hD [hE _ _ _ _]]].
        exists mm; split=> //.
        - by rewrite -h3.
        - by rewrite -h5 hD. }
    move=> [m [hlg hvm hpk2]].
    rewrite hlg.
    case E0: (verify_sig PP N F l w tsum pk.1 pk.2 mst sgst
                && (mst \notin [:: m])); last first.
    * (* invalid forgery: both sides answer false *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * (* valid fresh forgery *)
      case/andP: E0 => hver hfresh.
      case E1: (tcr_decision PP N F l w pk.1 m mst sgl sgst)
        => [ju|]; last first.
      -- (* ChainMeet: Gmid answers true; R wins PCHECK *)
         case E2: (pre_decision pk.1 m mst sgl sgst) => [[j x]|]; last first.
         ++ (* dead branch: the classifier is total on verifying
               fresh forgeries *)
            eapply (r_fact False); last by [].
            move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
            case/pre_invE: hinv => _ [_ _ e3 hmatch].
            rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6.
            rewrite h1 in hmatch.
            case: hmatch => mm [uss [hA hB hC hD [hE _ _ _ _]]].
            have emm : mm = m.
              have : [:: mm] = lg by rewrite -hA h3.
              by rewrite hlg => -[].
            rewrite emm in hC hD hE.
            have hsgl : sgl = sigs_of PP N F pk.1 0 m uss.
              by rewrite -h5 hD.
            have hver' : verify_sig PP N F l w tsum pk.1
                (ends_from_sig PP N F l w pk.1 m
                   (sigs_of PP N F pk.1 0 m uss)) mst sgst.
              by rewrite -hE.
            have := classify_some pk.1 m mst uss sgst hvm hC hver' hfresh.
            rewrite -hsgl E1 E2 => /(_ erefl).
            by rewrite eqxx.
         ++ (* PCHECK wins *)
            simpl.
            rewrite resolve_pck.
            eapply (r_get_bind_rhs rvl true).
              { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
                case/pre_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch
                  => mm [uss [_ _ _ _ [_ _ _ _ hrv]]]. }
            cbv beta.
            eapply r_bind_assertD_rhs; first by [].
            move=> _.
            eapply r_get_remember_rhs => tg.
            eapply (r_fact (exists us,
                      [/\ size us = l,
                          sgl = sigs_of PP N F pk.1 0 m us
                        & tg = qmap_from 0 (pre_queries 0 m us)])).
              { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                case/pre_invE: hinv => _ [_ _ e3 hmatch].
                rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
                rewrite h1 in hmatch.
                case: hmatch => mm [uss [hA hB hC hD [hE _ hG _ _]]].
                have emm : mm = m.
                  have : [:: mm] = lg by rewrite -hA h3.
                  by rewrite hlg => -[].
                exists uss; rewrite -emm; split=> //.
                - by rewrite -h5 hD.
                - by rewrite -h7 hG. }
            move=> [us [husz hsgs htg]].
            have hver' : verify_sig PP N F l w tsum pk.1
                (ends_from_sig PP N F l w pk.1 m
                   (sigs_of PP N F pk.1 0 m us)) mst sgst.
              by rewrite -hsgs -hpk2.
            have hwin := pre_decisionP pk.1 m mst us sgst hvm husz
                           hver' hfresh.
            rewrite -hsgs E2 in hwin.
            case: hwin => t0 [u0 [hget hfeq]].
            have hgetm : getm tg j = Some (t0, u0).
              rewrite htg.
              by have := qmap_from_get 0 (pre_queries 0 m us) j;
                 rewrite add0n => ->.
            rewrite hgetm.
            eapply (r_get_rhs_known ppl (Some pk.1)).
              { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                case/pre_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch
                  => mm [uss [_ _ _ _ [_ hpo _ _ _]]]. }
            simpl.
            rewrite hfeq eqxx.
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[[[[hinv _] _] _] _] _] _] _].
      -- (* ChainColl: both sides answer false *)
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** *** The ideal side: [R_pre_ideal]

    lhs is [G1v false] (KFORGE is literally [ret false]; no stored
    signature location), rhs the reduction linked against the IDEAL
    SM-PRE game (PCHECK answers false).  The invariant drops the
    gm_sig mirror but keeps the full [Some]-case description of R's
    state (needed to kill the dead classifier branch). *)

Definition IGNP2 : Locations :=
  [fmap g0v_pk' ; g0v_log' ; rp_pk_loc ; rp_log_loc ;
        rp_sig_loc ; ppl ; tgl ; twl ; rvl ].

Definition RP2 (pko : option (Pk FS)) (lg : seq (Msg FS))
    (pko' : option (Pk FS)) (lg' : seq (Msg FS)) (sgs : seq N)
    (po : option PP) (tg : {fmap nat -> (th_T TT × th_M TT)})
    (tw : seq (nat * nat)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg &
      match pko with
      | None =>
          [/\ lg = [::], sgs = [::], po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists m us,
            [/\ lg = [:: m], valid_msg l w tsum m, size us = l,
                sgs = sigs_of PP N F pk.1 0 m us
              & [/\ pk.2 = ends_from_sig PP N F l w pk.1 m
                            (sigs_of PP N F pk.1 0 m us),
                    po = Some pk.1,
                    tg = qmap_from 0 (pre_queries 0 m us),
                    tw = unzip1 (pre_queries 0 m us)
                  & rv = true]]
      end].

Definition pre_inv2 : precond :=
  heap_ignore IGNP2
  ⋊ rel_app [:: (lhs, g0v_pk') ; (lhs, g0v_log') ;
                (rhs, rp_pk_loc) ; (rhs, rp_log_loc) ; (rhs, rp_sig_loc) ;
                (rhs, ppl) ; (rhs, tgl) ; (rhs, twl) ;
                (rhs, rvl) ] RP2.

Arguments pre_inv2 : simpl never.

Lemma pre_inv2E s0 s1 :
  pre_inv2 (s0, s1) ->
  heap_ignore IGNP2 (s0, s1) /\
  RP2 (get_heap s0 g0v_pk') (get_heap s0 g0v_log')
     (get_heap s1 rp_pk_loc) (get_heap s1 rp_log_loc)
     (get_heap s1 rp_sig_loc) (get_heap s1 ppl)
     (get_heap s1 tgl) (get_heap s1 twl) (get_heap s1 rvl).
Proof. by move=> [h1 h2]; split. Qed.

Lemma pre_inv2I s0 s1 :
  heap_ignore IGNP2 (s0, s1) ->
  RP2 (get_heap s0 g0v_pk') (get_heap s0 g0v_log')
     (get_heap s1 rp_pk_loc) (get_heap s1 rp_log_loc)
     (get_heap s1 rp_sig_loc) (get_heap s1 ppl)
     (get_heap s1 tgl) (get_heap s1 twl) (get_heap s1 rvl) ->
  pre_inv2 (s0, s1).
Proof. by move=> h1 h2; split. Qed.

Lemma pphi_stable_ignp2 : pphi_stable (heap_ignore IGNP2).
Proof.
move=> s0 s1 ℓ v hin h ℓ' hni.
rewrite get_set_heap_neq; first exact: h.
apply/eqP => e; move: hni; rewrite e.
by move: hin; rewrite !inE => /or4P[] /eqP ->; rewrite mem_domm.
Qed.

(** Ending of G1v-false's COMMIT against the ideal game (two lhs
    puts: G1v stores no signature). *)
Lemma rp_commit_final2 (pp : PP) (m : seq nat) (us : seq N) :
  valid_msg l w tsum m -> size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        pblk_pre (heap_ignore IGNP2) (Some pp) (pre_queries 0 m us)
          (s0, s1) ⦄
     (#put g0v_pk' := Some (pp,
        ends_from_sig PP N F l w pp m (sigs_of PP N F pp 0 m us)) ;;
      #put g0v_log' := [:: m] ;;
      ret ((pp, ends_from_sig PP N F l w pp m (sigs_of PP N F pp 0 m us)),
           Some (sigs_of PP N F pp 0 m us)))
   ≈ bind (resolve (SMPB false) pgo Datatypes.tt)
       (λ p,
        #put rp_pk_loc := Some (p,
          ends_from_sig PP N F l w p m (sigs_of PP N F pp 0 m us)) ;;
        #put rp_log_loc := [:: m] ;;
        #put rp_sig_loc := sigs_of PP N F pp 0 m us ;;
        ret ((p, ends_from_sig PP N F l w p m (sigs_of PP N F pp 0 m us)),
             Some (sigs_of PP N F pp 0 m us)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pre_inv2 (s0, s1) ⦄.
Proof.
move=> hvm hus.
rewrite resolve_pgp.
eapply (r_get_bind_rhs ppl (Some pp)).
  by move=> s0 s1 [_ hpp _ _ _].
cbv beta iota.
eapply (r_put_bind_rhs rvl true _
          (pfin_pre IGNP2 pp (pre_queries 0 m us))).
  by move=> s0 s1; apply: pblk_to_pfin; rewrite mem_domm.
eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hfin ->].
case: hfin => hign hpp hrev htws htgts.
split; first by [].
apply: pre_inv2I.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists m, us; split=> //.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence *)

Lemma R_pre_ideal :
  perfect (I_KOTS FS) (G1v PP N F dPP dN l w tsum false)
          (R_pre ∘ SMPRE_game TT CC l false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pre_inv2).
{ rewrite /pre_inv2; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pre_inv2E: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hvm _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), pblk_pre (heap_ignore IGNP2) None [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/pre_inv2E: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  have hm : size m = l by case/and3P: hvm => /eqP.
  simpl.
  eapply (r_pcollq_pin false) => //.
  { exact: pphi_stable_ignp2. }
  move=> pp.
  rewrite (code_link_bind (rp_chains 0 m)).
  eapply (rp_chains_spec false (heap_ignore IGNP2) pp _ m 0 [::]) => //.
  { exact: pphi_stable_ignp2. }
  { by rewrite /= npq_le. }
  move=> us hus.
  rewrite cat0s.
  eapply (rp_commit_final2 pp m us) => //.
  by rewrite hus hm.
- (* KFORGE: lhs is [ret false]; everything on the rhs is one-sided *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_rhs => pko'.
  case: pko' => [pk|]; last first.
  + (* pre-commitment: ideal PCHECK answers false *)
    simpl.
    rewrite resolve_pck_false.
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [hinv _].
  + simpl.
    eapply r_get_remember_rhs => lg'.
    eapply r_get_remember_rhs => sgs.
    case E0: (verify_sig PP N F l w tsum pk.1 pk.2 mst sgst
                && (mst \notin lg')); last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[hinv _] _] _].
    * case E1: (tcr_decision PP N F l w pk.1 (head [::] lg') mst sgs sgst)
        => [ju|]; last first.
      -- case E2: (pre_decision pk.1 (head [::] lg') mst sgs sgst)
           => [[j x]|]; last first.
         ++ (* dead branch (classifier totality) *)
            eapply (r_fact False); last by [].
            move=> s0 s1 [[[hinv h1] h2] h3].
            case/pre_inv2E: hinv => _ [e1 e2 hmatch].
            rewrite /rem_inv /= in h1 h2 h3.
            rewrite -e1 h1 in hmatch.
            case: hmatch => mm [uss [hA hB hC hD [hE _ _ _ _]]].
            have hlg : lg' = [:: mm] by rewrite -h2 e2.
            have hsgs : sgs = sigs_of PP N F pk.1 0 mm uss.
              by rewrite -h3.
            case/andP: E0 => hver hfresh.
            rewrite hlg /= in hver hfresh E1 E2.
            have hver' : verify_sig PP N F l w tsum pk.1
                (ends_from_sig PP N F l w pk.1 mm
                   (sigs_of PP N F pk.1 0 mm uss)) mst sgst.
              by rewrite -hE.
            have := classify_some pk.1 mm mst uss sgst hB hC hver' hfresh.
            rewrite -hsgs E1 E2 => /(_ erefl).
            by rewrite eqxx.
         ++ (* PRE case: ideal PCHECK answers false, as does G1v *)
            simpl.
            rewrite resolve_pck_false.
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[hinv _] _] _].
      -- (* TCR case: both answer false *)
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[hinv _] _] _].
Qed.

End FixedSumOTSPREHop.
