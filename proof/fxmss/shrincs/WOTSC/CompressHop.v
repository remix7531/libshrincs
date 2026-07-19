(** * SHRINCS.WOTSC.CompressHop

    The SM-TCR(Theta_l) compression hop of the WOTS+C one-time
    security proof (P5; plan in theories/SHRINCS/WOTSC/PROOF_PLAN.md):
    the SECOND split of the forgery analysis, nulling the
    pk-compression-collision case (case 2 / COMPRESS of
    [Analysis.wotsc_forgery_classify]) between [Gmid1] (GrindHop.v)
    and [Gmid2].  Delivered:

      [R_cp_real  : perfect (I_KOTS WC) Gmid1
                            (R_cp ∘ SMTCR_game Tpk Cpk 1 true)]
      [R_cp_ideal : perfect (I_KOTS WC) Gmid2
                            (R_cp ∘ SMTCR_game Tpk Cpk 1 false)]

    where [Gmid2] is [Gmid1] with KFORGE ALSO answering false on the
    COMPRESS case — a verifying fresh forgery whose recomputed digest
    DIFFERS from the signed one (digit vectors) but whose completed
    chain ends differ from the honest stored ends (verification
    already forces the Theta_l compressions of the two end lists to
    coincide, so within the verified branch the single boolean
    discriminant [forged completed ends != honest completed ends]
    captures exactly the classifier's second disjunct); the next hop
    (TCRHop, chain collisions) continues from [Gmid2].  Hence
    [Adv Gmid1 Gmid2 <= AdvOf (SMTCR_game Tpk Cpk 1) (A ∘ R_cp)] by
    the standard reduction steps at the consumer.

    ** Design

    - ONE TQUERY (budget p = 1): the committed SM-TCR(Theta_l) target
      is [(encode_adrs pk_adrs, honest completed ends)].  Everything
      the reduction must compute BEFORE that query — the grinded
      digest and the per-chain re-rooted signature/completion chains
      — needs Hgrind and F under the still-hidden [pp]; [Cpk]
      (Games.v) exposes exactly those two through the COLLQ oracle
      (sum-tagged inputs/outputs).
    - COMMIT: one-shot guard; ONE unguarded COLLQ at the grinding
      address pins [pp]'s lazy sampling at a fixed program point (the
      UCOLLQ-pin trick of WOTSC/FixedSumOTS UDHop — couples SM-TCR's
      lazy [dPP] against Gmid1's eager one, no swap needed; works for
      every [c_max], including 0); the grinding queries Hgrind at
      every counter below [c_max] ([cp_grind], one COLLQ each) and
      the bounded search runs purely on the answer list ([cp_pick];
      [cp_pick_map] identifies it with the scheme's [find_ctr], so
      the [#assert] aborts exactly with Gmid1's grinding assert);
      per chain, the root is sampled LOCALLY ([dN] — hidden values
      never touch an oracle) and the signature value/completed end
      are computed through COLLQ F-calls ([cp_chains]/[cp_walk], the
      oracle-routed walk pattern of TCRHop's [r_walk]); then the ONE
      [TQUERY (encode_adrs pk_adrs, ends)] — whose answer IS
      [Tl pp pk_adrs ends] — and GETPP; store pk/log/(sigs, ctr).
    - KFORGE: getSome pk, log, getSome (sigs, ctr);
      [v := verify && freshness]; if [~~ v] ret false; if the digests
      agree as digit vectors (GRIND case) ret false (BOTH Gmid1 and
      Gmid2 null it — GrindHop absorbed that case); else if the
      forged completed ends differ from the honest ones (COMPRESS
      discriminant), call [CHECK (0, forged completed ends)] and
      return its answer; else ret true (the CHAIN cases — both games
      answer true there, the later hops absorb them).
      Real side: the discriminant gives [forged ends != honest ends],
      and the verification equation [Tl pp pk_adrs (forged ends) =
      pk.2 = Tl pp pk_adrs (honest ends)] (the invariant records
      pk.2's shape) is SM-TCR's collision — CHECK answers true =
      Gmid1's verdict.  Ideal side: CHECK answers false = Gmid2.
    - NO side conditions: no [Hrange] (the COMPRESS discriminants are
      computed directly, no digit-vector injectivity needed), no
      [0 < l] / [1 < w] / [0 < c_max] (the COLLQ pin makes the
      lazy/eager pp coupling unconditional), no [dM] (Tgr is not
      involved; Tpk's dummy input sampler is [ret [::]]).

    ** Invariant

    [heap_ignore] over all ten private locations joined with ONE
    [rel_app] relation [RC]: Gmid1's (= Gmid2's) pk/log/sig locations
    (300-302, shared with G0w/G1w) mirror R's (340-342), and R's pk
    determines the entire SM-TCR state — None: everything initial;
    Some pk: there are [m, c, sg] with log = [:: m], stored signature
    [(sg, c)], [pk.2 = Tl pk.1 pk_adrs (honest ends)], parameter
    pinned to [pk.1], ONE committed target
    [(encode_adrs pk_adrs, honest ends)] at index 0, phase revealed.

    Locations 340-342 (PROOF_PLAN.md: CompressHop at 340+). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp.experimental_reals Require Import distr.
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Games.SMTCR Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop FixedSumOTS.PREHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis
  WOTSC.GrindHop.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section CompressHop.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).

(** Same section context as WOTSC.Games minus the dummy message
    sampler [dM] (only [Tgr] needs it; this hop attacks [Tpk]). *)
Context (PP N M : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).
Context (dPP : dist PP) (dN : dist N).
Context (S_wn c_max : nat).
Context (zstar istar : nat).

Local Notation WC :=
  (WOTSC PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation TP := (Tpk PP N Tl dPP dN).
Local Notation CP := (Cpk PP N M F Tl Hgrind dPP dN).
Local Notation SMB b := (SMTCR_game TP CP 1 b).
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation cadrs := (chain_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation gtw := (encode_adrs gadrs).
Local Notation ptw := (encode_adrs padrs).
Local Notation ctw i k := (encode_adrs (cadrs i k)).
Local Notation FW := (Fw PP N F zstar istar).
Local Notation cfW := (HBS.Examples.FixedSumOTS.Scheme.chainf PP N FW).
Local Notation gprp := (@grind_prp w l S_wn).
Local Notation wdigest := (digest_of PP M Hgrind zstar istar).
Local Notation wfind_ctr :=
  (find_ctr PP M Hgrind S_wn c_max zstar istar).
Local Notation wcends := (complete_ends PP N F zstar istar).
Local Notation wverify :=
  (verify_sig PP N M F Tl Hgrind S_wn zstar istar).
Local Notation wsigs := (sigs_of PP N FW).
Local Notation wends := (ends_of PP N FW w).
Local Notation GM1 :=
  (Gmid1 PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).

Local Notation pk_loc' :=
  (g0w_pk_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation log_loc' :=
  (g0w_log_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation sig_loc' :=
  (g0w_sig_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation pp_loc' := (tcr_pp_loc TP).
Local Notation tgts_loc' := (tcr_tgts_loc TP).
Local Notation tws_loc' := (tcr_tws_loc TP).
Local Notation rev_loc' := tcr_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the COLLQ-routed grinding search

    The reduction queries Hgrind through COLLQ at every counter below
    [c_max] ([cp_grind] below) and runs the bounded search on the
    answer list: [cp_pick] returns the first (counter, digest value)
    whose decoded digits satisfy the digit-sum predicate —
    [find_ctr]'s search, re-rooted at the oracle answers
    ([cp_pick_map]; same shape as WOTSC.UDHop's [grind_pick], local
    copy since this file does not depend on UDHop). *)

Definition cp_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 c_max) hs | gprp ch.2].

Lemma cp_zip_filter (f : nat -> nat) (p : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | p ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | p (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (p (f c)) => /=; [|exact: IH].
Qed.

(** The search on the honest answer list IS the scheme's grinding
    (the predicates agree by conversion: [grind_prp] at an Hgrind
    output is [good_ctr]). *)
Lemma cp_pick_map (pp : PP) (m : M) :
  cp_pick [seq Hgrind pp gadrs (m, c) | c <- iota 0 c_max]
  = omap (fun c => (c, Hgrind pp gadrs (m, c))) (wfind_ctr pp m).
Proof. by rewrite /cp_pick cp_zip_filter. Qed.

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed loops *)

(** COLLQ/TQUERY/GETPP/CHECK opsigs as committed to [I_SMTCR TP CP]. *)
Definition cp_cqo : opsig := (COLLQ, (tc_T CP × tc_M CP, tc_N CP)).
Definition cp_tqo : opsig := (TQUERY, (th_T TP × th_M TP, th_N TP)).
Definition cp_gpo : opsig := (GETPP, ('unit, th_PP TP)).
Definition cp_cko : opsig := (CHECK, ('nat × th_M TP, 'bool)).

(** The grinding loop: one COLLQ (Hgrind member, [inr]) per counter;
    returns the answer list. *)
Fixpoint cp_grind (m : M) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr cp_cqo (gtw, inr (m, c))
        (λ r,
           hs ← cp_grind m cs' ;;
           ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance cp_grind_valid (L : Locations) (m : M) (cs : seq nat) :
  ValidCode L (I_SMTCR TP CP) (cp_grind m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n]
    steps, one COLLQ (F member, [inl]) per step; returns the value at
    [k + n]. *)
Fixpoint cp_walk (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr cp_cqo (ctw i k, inl x)
         (λ r, cp_walk i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance cp_walk_valid (L : Locations) i k n (x : N) :
  ValidCode L (I_SMTCR TP CP) (cp_walk i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; exact: IH.
Qed.

(** All chains from index [st] with digits [ds]: per chain, sample
    the root LOCALLY, one COLLQ F-step to the signature position
    (positive digits), walk upward; returns (signature values,
    completed ends). *)
Fixpoint cp_chains (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1
           then opr cp_cqo (ctw st d', inl u)
                  (λ r, ret (if r is inl y then y else u))
           else ret u) ;;
      e ← cp_walk st d (w.-1 - d) s ;;
      '(ss, es) ← cp_chains st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance cp_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMTCR TP CP) (cp_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by fmap_solve.
    move=> r; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: cp_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The reduction package *)

(** R's own locations (340+, see header). *)
Definition rcp_pk_loc := mkloc 340 (None : option (Pk WC)).
Definition rcp_log_loc := mkloc 341 ([::] : seq (Msg WC)).
Definition rcp_sig_loc := mkloc 342 (None : option (Sig WC)).

(** THE reduction: plays [I_KOTS WC] using the SM-TCR oracles. *)
Definition R_cp : package (I_SMTCR TP CP) (I_KOTS WC) :=
  [package [fmap rcp_pk_loc ; rcp_log_loc ; rcp_sig_loc ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get rcp_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr cp_cqo (gtw, inr (m, 0)) (λ r, ret r) ;;
      hs ← cp_grind m (iota 0 c_max) ;;
      #assert (isSome (cp_pick hs)) ;;
      let c := (odflt (0, 0) (cp_pick hs)).1 in
      let d := digits_w w l (odflt (0, 0) (cp_pick hs)).2 in
      '(sgs, ends) ← cp_chains 0 d ;;
      root ← opr cp_tqo (ptw, ends) (λ r, ret r) ;;
      pp ← opr cp_gpo Datatypes.tt (λ p, ret p) ;;
      #put rcp_pk_loc := Some (pp, root) ;;
      #put rcp_log_loc := [:: m] ;;
      #put rcp_sig_loc := Some (sgs, c) ;;
      ret ((pp, root), Some (sgs, c))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pk ← getSome rcp_pk_loc ;;
      log ← get rcp_log_loc ;;
      sgo ← getSome rcp_sig_loc ;;
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
              then opr cp_cko
                     (0, wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1)
                     (λ ans, ret ans)
              else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Gmid2: Gmid1 with ALSO the COMPRESS case nulled

    Same locations as G0w/G1w/Gmid1 (300-302); COMMIT is VERBATIM
    Gmid1's (= G1w's); KFORGE nulls the GRIND case AND the COMPRESS
    case (header: the second discriminant is the completed-ends
    disequality; Theta_l-coincidence is forced by verification). *)

Definition Gmid2 : game (I_KOTS WC) :=
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
              else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Linked oracle bodies (resolve equations, computed once)

    The COLLQ/TQUERY/GETPP bodies do not depend on the real/ideal
    flag, so the whole COMMIT machinery below is parametric in [b]. *)

Lemma resolve_cq (b : bool) (t : tc_T CP) (x : tc_M CP) :
  resolve (SMB b) cp_cqo (t, x) =
  (ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   ret (tc_eval CP pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_tq (b : bool) (t : th_T TP) (xs : th_M TP) :
  resolve (SMB b) cp_tqo (t, xs) =
  (revealed ← get rev_loc' ;;
   #assert ~~ revealed ;;
   tws ← get tws_loc' ;;
   #assert (size tws < 1)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get tgts_loc' ;;
   #put tgts_loc' := setm tgts (size tws) (t, xs) ;;
   #put tws_loc' := rcons tws t ;;
   ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   ret (th_eval TP pp t xs)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_gp (b : bool) (u : unit) :
  resolve (SMB b) cp_gpo u =
  (ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   #put rev_loc' := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ck (j : nat) (xs : th_M TP) :
  resolve (SMB true) cp_cko (j, xs) =
  (revealed ← get rev_loc' ;;
   #assert revealed ;;
   tgts ← get tgts_loc' ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get pp_loc' ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
            end ;;
       ret ((xs != m0) && (th_eval TP pp t0 xs == th_eval TP pp t0 m0))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side CHECK answers false unconditionally. *)
Lemma resolve_ck_false (j : nat) (xs : th_M TP) :
  resolve (SMB false) cp_cko (j, xs) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the package, the resolved oracle bodies and the pure layer
   folded under [simpl] from here on (the resolve equations above are
   proved; GrindHop lesson). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
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

(* ------------------------------------------------------------------ *)
(** ** Conversion bridges (canonical tweaks compute; [decode_tweakK]
    at closed type tags, exactly GrindHop's [digest_resE] flavor) *)

(** The COLLQ answer at the grinding address, post-processed by the
    loop's [inr]-projection, IS the scheme's Hgrind output. *)
Lemma collq_H_E (pp : PP) (m : M) (c : nat) :
  (if tc_eval CP pp gtw (inr (m, c)) is inr h then h else 0)
  = Hgrind pp gadrs (m, c).
Proof. by rewrite /tc_eval /Cpk /= decode_tweakK. Qed.

(** The COLLQ answer at a chain address, post-processed by the walk's
    [inl]-projection, IS the scheme's F-step. *)
Lemma collq_F_E (pp : PP) (i k : nat) (x : N) :
  (if tc_eval CP pp (ctw i k) (inl x) is inl y then y else x)
  = F pp (cadrs i k) x.
Proof. by rewrite /tc_eval /Cpk /= decode_tweakK. Qed.

(** Decoded digest at the picked counter (folds [digits_w] of the
    oracle answer into [digest_of]). *)
Lemma digestE (pp : PP) (m : M) (c : nat) :
  digits_w w l (Hgrind pp gadrs (m, c)) = wdigest pp m c.
Proof. by rewrite /digest_of. Qed.

(** The walk's completed ends are the verifier's [complete_ends]
    (FixedSumOTS [ends_of] at [FW], start 0, length-l digests). *)
Lemma wendsE (pp : PP) (ds : seq nat) (ys : seq N) :
  size ds = l -> wends pp 0 ds ys = wcends pp ds ys.
Proof.
move=> h.
by rewrite (ends_of_from_sig PP N FW l w pp ds ys h)
   (wcendsE PP N F zstar istar).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The invariant (header) *)

Definition IGNC : Locations :=
  [fmap pk_loc' ; log_loc' ; sig_loc' ; rcp_pk_loc ; rcp_log_loc ;
        rcp_sig_loc ; pp_loc' ; tgts_loc' ; tws_loc' ; rev_loc' ].

Definition RC (pko : option (Pk WC)) (lg : seq (Msg WC))
    (sgo : option (Sig WC))
    (pko' : option (Pk WC)) (lg' : seq (Msg WC)) (sgo' : option (Sig WC))
    (po : option PP) (tg : {fmap nat -> (th_T TP × th_M TP)})
    (tw : seq (th_T TP)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : M) (c : nat) (sg : seq N),
            [/\ lg = [:: m], sgo = Some (sg, c), po = Some pk.1,
                pk.2 = Tl pk.1 padrs (wcends pk.1 (wdigest pk.1 m c) sg)
                /\ tg = setm emptym 0 (ptw, wcends pk.1 (wdigest pk.1 m c) sg)
              & tw = [:: ptw] /\ rv = true]
      end].

Definition cp_inv : precond :=
  heap_ignore IGNC
  ⋊ rel_app [:: (lhs, pk_loc') ; (lhs, log_loc') ; (lhs, sig_loc') ;
                (rhs, rcp_pk_loc) ; (rhs, rcp_log_loc) ; (rhs, rcp_sig_loc) ;
                (rhs, pp_loc') ; (rhs, tgts_loc') ; (rhs, tws_loc') ;
                (rhs, rev_loc') ] RC.

Arguments cp_inv : simpl never.

Lemma cp_invE s0 s1 :
  cp_inv (s0, s1) ->
  heap_ignore IGNC (s0, s1) /\
  RC (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rcp_pk_loc) (get_heap s1 rcp_log_loc)
     (get_heap s1 rcp_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma cp_invI s0 s1 :
  heap_ignore IGNC (s0, s1) ->
  RC (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rcp_pk_loc) (get_heap s1 rcp_log_loc)
     (get_heap s1 rcp_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc') ->
  cp_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside COMMIT, machinery dropped) *)

Definition cblk (po : option PP) (rv : bool)
    (tw : seq (th_T TP)) (tg : {fmap nat -> (th_T TP × th_M TP)}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNC (s0, s1),
      get_heap s1 pp_loc' = po,
      get_heap s1 rev_loc' = rv,
      get_heap s1 tws_loc' = tw &
      get_heap s1 tgts_loc' = tg].

Arguments cblk : simpl never.

(** The lazy parameter sampling (put pp, at the COLLQ pin). *)
Lemma cblk_set_pp (pp : PP) rv tw tg s0 s1 :
  cblk None rv tw tg (s0, s1) ->
  cblk (Some pp) rv tw tg (s0, set_heap s1 pp_loc' (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The TQUERY state update (put tgts; put tws). *)
Lemma cblk_qupd (pp : PP) (xs : th_M TP) s0 s1 :
  cblk (Some pp) false [::] emptym (s0, s1) ->
  cblk (Some pp) false [:: ptw] (setm emptym 0 (ptw, xs))
    (s0, set_heap (set_heap s1 tgts_loc' (setm emptym 0 (ptw, xs)))
           tws_loc' [:: ptw]).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

(** The phase flip (GETPP's put rev). *)
Lemma cblk_set_rev (po : option PP) tw tg s0 s1 :
  cblk po false tw tg (s0, s1) ->
  cblk po true tw tg (s0, set_heap s1 rev_loc' true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked COLLQ (pp pinned: state untouched) *)

Lemma r_collq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CP) (x : tc_M CP) rv tw tg
    (c0 : raw_code B) (k1 : tc_N CP -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CP pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) cp_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_cq b t x).
eapply (r_get_bind_rhs pp_loc' (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The loop specs (rhs-only; pp pinned, state constant) *)

(** Grinding loop: the continuation receives the honest Hgrind answer
    list. *)
Lemma r_cgrind_spec (b : bool) {B : choiceType} (pp : PP) (m : M)
    (cs : seq nat) rv tw tg
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B)
    (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp gadrs (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (cp_grind m cs) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_collq_known b).
  cbv beta.
  rewrite collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(** Walk loop: the continuation receives the chain value [n] steps
    up. *)
Lemma r_cwalk_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall n i k (x : N) rv tw tg
         (c0 : raw_code B) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (chain (cfW pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (cp_walk i k n x) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x rv tw tg c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_collq_known b).
  cbv beta.
  rewrite collq_F_E.
  exact: IH.
Qed.

(** The per-chain spec: lhs [sample_sig_roots] at [FW] (Gmid1's
    sampling), rhs the linked [cp_chains]; the roots are coupled
    pointwise, the results are [sigs_of]/[ends_of] of the sampled
    roots. *)
Lemma r_cchains_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall ds st rv tw tg (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
        K0 (wsigs pp st ds us)
      ≈ K1 (wsigs pp st ds us, wends pp st ds (wsigs pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     bind (sample_sig_roots PP N FW dN pp st ds) K0
   ≈ bind (code_link (cp_chains st ds) (SMB b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st rv tw tg K0 K1 h.
- exact: (h [::] erefl).
- rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN))
          !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d h => [|d'] h.
  + (* d = 0: no sigma step, walk from the root itself *)
    rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    eapply (r_cwalk_spec b pp post (w.-1 - 0) st 0 u).
    rewrite (code_link_bind (cp_chains st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
  + (* d = d'.+1: one COLLQ F-step to the signature position *)
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_collq_known b).
    cbv beta.
    rewrite collq_F_E /=.
    rewrite (code_link_bind (cp_walk st d'.+1 (w.-1 - d'.+1)
              (F pp (cadrs st d') u))) bind_assoc.
    eapply (r_cwalk_spec b pp post (w.-1 - d'.+1) st d'.+1
              (F pp (cadrs st d') u)).
    rewrite /= (code_link_bind (cp_chains st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The common COMMIT tail

    By this point all sampling and all oracle interaction is over:
    both sides store key/log/signature (the same values) and return;
    the invariant is re-established from the final block state. *)

Lemma r_cp_tail (pp : PP) (m : M) (c : nat) (sg : seq N) :
  ⊢ ⦃ λ '(s0, s1),
        cblk (Some pp) true [:: ptw]
          (setm emptym 0 (ptw, wcends pp (wdigest pp m c) sg)) (s0, s1) ⦄
     (#put pk_loc' := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)) ;;
      #put log_loc' := [:: m] ;;
      #put sig_loc' := Some (sg, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)), Some (sg, c)))
   ≈ (#put rcp_pk_loc := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)) ;;
      #put rcp_log_loc := [:: m] ;;
      #put rcp_sig_loc := Some (sg, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)), Some (sg, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ cp_inv (s0, s1) ⦄.
Proof.
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
apply: cp_invI.
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
  by exists m, c, sg; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence *)

Lemma R_cp_real :
  perfect (I_KOTS WC) GM1 (R_cp ∘ SMTCR_game TP CP 1 true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ cp_inv).
{ rewrite /cp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/cp_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), cblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/cp_invE: hinv => hign hRC.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRC => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the COLLQ pin: SM-TCR's lazy pp is sampled here, against Gmid1's
     eager one *)
  rewrite (resolve_cq true gtw (inr (m, 0))).
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  (* the grinding loop through COLLQ *)
  rewrite (code_link_bind (cp_grind m (iota 0 c_max))).
  eapply (r_cgrind_spec true pp m).
  cbv beta.
  rewrite code_link_assertD cp_pick_map.
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (wfind_ctr pp m). }
  move=> e1 _.
  move: e1; case E: (wfind_ctr pp m) => [c|] /= e1; last by [].
  rewrite !digestE.
  (* the chains through COLLQ, roots sampled locally on both sides *)
  rewrite (code_link_bind (cp_chains 0 (wdigest pp m c))).
  eapply (r_cchains_spec true pp).
  move=> us hus.
  cbv beta iota.
  rewrite (wendsE pp (wdigest pp m c) _
            (size_digest_of PP M Hgrind zstar istar pp m c)).
  simpl.
  (* the ONE TQUERY: commit the honest ends *)
  rewrite (resolve_tq true ptw
            (wcends pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us))).
  eapply (r_get_bind_rhs rev_loc' false).
    { by move=> s0 s1 [_ _ h _ _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs tws_loc' [::]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs tgts_loc' emptym).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_qupd pp _ _ _ hpre). }
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  rewrite !(th_evalE_Tpk PP N Tl dPP dN).
  (* GETPP: reveal pp, flip the phase *)
  rewrite (resolve_gp true Datatypes.tt).
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (cblk_set_rev _ _ _ _ _ hpre). }
  exact: r_cp_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/cp_invE: hinv => _ [e1 _ _ _].
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
      case/cp_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => sgol.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (sgov = sgol)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/cp_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
            [/\ lg = [:: m], sgol = Some (sg, c)
              & pk.2 = Tl pk.1 padrs (wcends pk.1 (wdigest pk.1 m c) sg)])).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/cp_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ [hD _] _]]].
      exists mm, cc, sgg; split.
      - by rewrite -h3.
      - by rewrite -h5.
      - by rewrite hD. }
  move=> [m [c [sg [hlg hsgol hpk2]]]].
  rewrite hlg hsgol /=.
  case E0: (wverify pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[[hinv _] _] _] _] _] _].
  + case/andP: (E0) => hver hfresh.
    case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B).
    * (* GRIND: both games null it (GrindHop absorbed this case) *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wcends pk.1 (wdigest pk.1 m c) sg)%B); last first.
      -- (* equal ends (CHAIN cases): both sides answer true *)
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
      -- (* COMPRESS: CHECK answers true = Gmid1's verdict *)
         simpl.
         rewrite (resolve_ck 0
                   (wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1)).
         eapply (r_get_bind_rhs rev_loc' true).
           { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
             case/cp_invE: hinv => _ [_ _ _ hmatch].
             rewrite /rem_inv /= in h1.
             rewrite h1 in hmatch.
             by case: hmatch => mm [cc [sgg [_ _ _ _ [_ hrv]]]]. }
         cbv beta.
         eapply r_bind_assertD_rhs; first by [].
         move=> _.
         eapply r_get_remember_rhs => tg.
         eapply (r_fact
           (tg = setm emptym 0
                   (ptw, wcends pk.1 (wdigest pk.1 m c) sg))).
           { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
             case/cp_invE: hinv => _ [_ _ e3 hmatch].
             rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
             rewrite h1 in hmatch.
             case: hmatch => mm [cc [sgg [hA hB _ [_ hC] _]]].
             have emm : mm = m.
               { have : [:: mm] = [:: m] by rewrite -hA h3.
                 by case. }
             have hsgcc : Some (sgg, cc) = Some (sg, c).
               { by rewrite -hB h5. }
             have esgg : sgg = sg by case: hsgcc.
             have ecc : cc = c by case: hsgcc.
             by rewrite -h7 hC emm ecc esgg. }
         move=> htg.
         rewrite htg setmE /=.
         eapply (r_get_rhs_known pp_loc' (Some pk.1)).
           { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
             case/cp_invE: hinv => _ [_ _ _ hmatch].
             rewrite /rem_inv /= in h1.
             rewrite h1 in hmatch.
             by case: hmatch => mm [cc [sgg [_ _ hpo _ _]]]. }
         simpl.
         rewrite !(th_evalE_Tpk PP N Tl dPP dN).
         move: hver; rewrite /verify_sig => /and3P[_ _ /eqP hTl].
         rewrite E2 hTl hpk2 eqxx /=.
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[[hinv _] _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence *)

Lemma R_cp_ideal :
  perfect (I_KOTS WC) Gmid2 (R_cp ∘ SMTCR_game TP CP 1 false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ cp_inv).
{ rewrite /cp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (the COLLQ/TQUERY/GETPP
     bodies and the loop specs are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/cp_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), cblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/cp_invE: hinv => hign hRC.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRC => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_cq false gtw (inr (m, 0))).
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  rewrite (code_link_bind (cp_grind m (iota 0 c_max))).
  eapply (r_cgrind_spec false pp m).
  cbv beta.
  rewrite code_link_assertD cp_pick_map.
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (wfind_ctr pp m). }
  move=> e1 _.
  move: e1; case E: (wfind_ctr pp m) => [c|] /= e1; last by [].
  rewrite !digestE.
  rewrite (code_link_bind (cp_chains 0 (wdigest pp m c))).
  eapply (r_cchains_spec false pp).
  move=> us hus.
  cbv beta iota.
  rewrite (wendsE pp (wdigest pp m c) _
            (size_digest_of PP M Hgrind zstar istar pp m c)).
  simpl.
  rewrite (resolve_tq false ptw
            (wcends pp (wdigest pp m c) (wsigs pp 0 (wdigest pp m c) us))).
  eapply (r_get_bind_rhs rev_loc' false).
    { by move=> s0 s1 [_ _ h _ _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs tws_loc' [::]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs tgts_loc' emptym).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_qupd pp _ _ _ hpre). }
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  rewrite !(th_evalE_Tpk PP N Tl dPP dN).
  rewrite (resolve_gp false Datatypes.tt).
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (cblk_set_rev _ _ _ _ _ hpre). }
  exact: r_cp_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/cp_invE: hinv => _ [e1 _ _ _].
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
      case/cp_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => sgol.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (sgov = sgol)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/cp_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/cp_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ _ _]]].
      exists mm, cc, sgg; split.
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
                 != wcends pk.1 (wdigest pk.1 m c) sg)%B); last first.
      -- apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
      -- (* COMPRESS: ideal CHECK answers false = Gmid2's null *)
         simpl.
         rewrite (resolve_ck_false 0
                   (wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1)).
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

End CompressHop.
