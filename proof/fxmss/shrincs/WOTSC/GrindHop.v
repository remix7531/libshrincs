(** * SHRINCS.WOTSC.GrindHop

    The S-TCR(Prop) grinding hop of the WOTS+C one-time security
    proof (P5; plan in theories/SHRINCS/WOTSC/PROOF_PLAN.md): the
    FIRST split of the forgery analysis at [G1w], nulling the
    grinding-collision case (case 1 / GRIND of
    [Analysis.wotsc_forgery_classify]).  Delivered:

      [R_gr_real  : perfect (I_KOTS WC) (G1w ... true)
                            (R_gr ∘ STCRP_game TG CG M genc gprp c_max 1 true)]
      [R_gr_ideal : perfect (I_KOTS WC) Gmid1
                            (R_gr ∘ STCRP_game ... false)]

    where [Gmid1] is G1w-real with KFORGE answering false exactly on
    the GRIND case — i.e. when the forgery's recomputed digest equals
    the signed digest AS DIGIT VECTORS ([wdigest pp mstar cstar ==
    wdigest pp m c]); the next hop (PkHop) continues from [Gmid1].
    Hence [Adv (G1w true) Gmid1 <= AdvOf (STCRP_game ... 1) (A ∘ R_gr)]
    by the standard reduction steps at the consumer.

    ** Design

    - ONE SQUERY, in-oracle grinding: COMMIT makes the single query
      [SQUERY (encode_adrs gadrs, m)].  The STCRP oracle itself runs
      the bounded counter search and ABORTS ([#assert false]) exactly
      when the search fails — by [Games.grind_search_find_ctr] the
      oracle's search IS the scheme's [find_ctr], so the abort event
      coincides with G1w's grinding assert
      [#assert (isSome (find_ctr pp m))], and the returned counter is
      the signed one.  Budget p = 1.
    - SQUERY hides pp, so COMMIT calls SGETPP directly AFTER the
      single query (no more queries are needed; this flips the STCRP
      phase, so KFORGE makes no SGETPP call).  The digest is decoded
      from the SQUERY answer ([digits_w w l res.1] = the signed digit
      vector, [digest_resE]); the per-chain re-rooted sampling
      ([sample_sig_roots] at [Fw]) and the pk compression are then
      pure/local, exactly G1w's COMMIT tail.
    - KFORGE: getSome pk, read log, getSome the stored (sigs, ctr);
      [v := verify && freshness]; if [~~ v] ret false; otherwise the
      GRIND discriminant [wdigest pp mstar cstar == wdigest pp m c]
      (the classifier's first split): on equality call
      [SCHECK (0, (mstar, cstar))] and return its answer, else ret
      true (G1w's answer; the remaining cases are absorbed by the
      later hops, exactly FixedSumOTS.TCRHop's Gmid pattern).
      Real side: freshness gives [mstar != m] ([notin_log_neq]) and
      [wdigest_inj] (the [Hrange] side condition) lifts the digit
      equality to the Hgrind-output collision, so SCHECK answers true
      = G1w-real's answer.  Ideal side: SCHECK answers false = Gmid1.
      The signed message is recovered from the log by a match (M has
      no canonical inhabitant, so no [head] default; the nil branch
      is dead — the invariant gives [log = [:: m]] under a committed
      key).
    - [Hrange] ([forall pp a x, Hgrind pp a x < w ^ l]) is a
      DATA-level side condition of [R_gr_real] ONLY (the ideal side
      never inspects hash values), passed as an explicit lemma
      argument per the plan (docs/STYLE.md rule 2; discharged at
      instantiation, where Hgrind outputs n-bit strings parsed as
      exactly l base-w digits).
    - Section parameter [dM : dist M] is data only (it feeds [Tgr]'s
      dummy [th_dM] record field; no game ever samples it) — same
      flavor as FixedSumOTS.PREHop's [n0 : N].

    ** Invariant

    [heap_ignore] over all ten private locations joined with ONE
    [rel_app] relation [RG]: G1w's (= Gmid1's) pk/log/sig locations
    mirror R's, and R's pk determines the entire STCRP state — None:
    everything initial; Some pk: there are [m, c, sg] with
    log = [:: m], stored signature (sg, c), parameter pinned to
    pk.1, ONE committed target [(encode_adrs gadrs, (m, c))] at
    index 0, and the phase revealed.

    Locations 330-332 (the WOTSC mirror of FixedSumOTS.TCRHop's
    230-232; WOTSC.UDHop is expected at 350+). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp.experimental_reals Require Import distr.
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Games.STCRP Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop FixedSumOTS.PREHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section GrindHop.

(** Same section context as WOTSC.Games (the dummy sampler [dM] is
    consumed only by [Tgr]'s record fields, see header). *)
Context (PP N M : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).
Context (dPP : dist PP) (dN : dist N) (dM : dist M).
Context (w l S_wn c_max : nat).
Context (zstar istar : nat).

Local Notation WC :=
  (WOTSC PP N M F Tl Hgrind dPP dN w l S_wn c_max zstar istar).
Local Notation TG := (Tgr PP M Hgrind dPP dM).
Local Notation CG := (Cgr PP N M F Tl Hgrind dPP dM).
Local Notation genc := (grind_enc M).
Local Notation gprp := (grind_prp w l S_wn).
Local Notation STB b := (STCRP_game TG CG M genc gprp c_max 1 b).
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation gtw := (encode_adrs gadrs).
Local Notation FW := (Fw PP N F zstar istar).
Local Notation wdigest := (digest_of PP M Hgrind w l zstar istar).
Local Notation wfind_ctr := (find_ctr PP M Hgrind w l S_wn c_max zstar istar).
Local Notation wcends := (complete_ends PP N F w l zstar istar).
Local Notation wverify := (verify_sig PP N M F Tl Hgrind w l S_wn zstar istar).
Local Notation G1W := (G1w PP N M F Tl Hgrind dPP dN w l S_wn c_max zstar istar).

Local Notation pk_loc' :=
  (g0w_pk_loc PP N M F Tl Hgrind dPP dN w l S_wn c_max zstar istar).
Local Notation log_loc' :=
  (g0w_log_loc PP N M F Tl Hgrind dPP dN w l S_wn c_max zstar istar).
Local Notation sig_loc' :=
  (g0w_sig_loc PP N M F Tl Hgrind dPP dN w l S_wn c_max zstar istar).
Local Notation pp_loc' := (stcr_pp_loc TG).
Local Notation tgts_loc' := (stcr_tgts_loc TG M).
Local Notation tws_loc' := (stcr_tws_loc TG).
Local Notation rev_loc' := stcr_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** The reduction package *)

(** SQUERY/SGETPP/SCHECK opsigs as committed to [I_STCRP TG CG M]. *)
Definition gsqo : opsig := (SQUERY, (th_T TG × M, th_N TG × 'nat)).
Definition ggpo : opsig := (SGETPP, ('unit, th_PP TG)).
Definition gcko : opsig := (SCHECK, ('nat × (M × 'nat), 'bool)).

(** R's own locations (330+, see header). *)
Definition rg_pk_loc := mkloc 330 (None : option (Pk WC)).
Definition rg_log_loc := mkloc 331 ([::] : seq (Msg WC)).
Definition rg_sig_loc := mkloc 332 (None : option (Sig WC)).

(** THE reduction: plays [I_KOTS WC] using the STCRP oracles. *)
Definition R_gr : package (I_STCRP TG CG M) (I_KOTS WC) :=
  [package [fmap rg_pk_loc ; rg_log_loc ; rg_sig_loc ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get rg_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      res ← opr gsqo (gtw, m) (λ r, ret r) ;;
      pp ← opr ggpo Datatypes.tt (λ p, ret p) ;;
      sg ← sample_sig_roots PP N FW dN pp 0 (digits_w w l res.1) ;;
      #put rg_pk_loc := Some (pp, Tl pp padrs (wcends pp (digits_w w l res.1) sg)) ;;
      #put rg_log_loc := [:: m] ;;
      #put rg_sig_loc := Some (sg, res.2) ;;
      ret ((pp, Tl pp padrs (wcends pp (digits_w w l res.1) sg)),
           Some (sg, res.2))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pk ← getSome rg_pk_loc ;;
      log ← get rg_log_loc ;;
      sgo ← getSome rg_sig_loc ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if wverify pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if wdigest pk.1 mst sgst.2 == wdigest pk.1 m sgo.2
            then opr gcko (0, (mst, sgst.2)) (λ ans, ret ans)
            else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Gmid1: G1w-real with the GRIND case nulled

    Same locations as G0w/G1w (300-302; the games are never composed
    and sharing keeps the next hop's invariant small); COMMIT is
    VERBATIM G1w's; KFORGE reads the stored (sigs, ctr) and the log
    to recompute the signed digest. *)

Definition Gmid1 : game (I_KOTS WC) :=
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
            else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Linked oracle bodies (resolve equations, computed once) *)

(* The SQUERY/SGETPP bodies do not depend on the real/ideal flag, so
   the whole COMMIT machinery below is parametric in [b]. *)

Lemma resolve_gsq (b : bool) (t : th_T TG) (m : M) :
  resolve (STB b) gsqo (t, m) =
  (revealed ← get rev_loc' ;;
   #assert ~~ revealed ;;
   tws ← get tws_loc' ;;
   #assert (size tws < 1)%N ;;
   #assert (t \notin tws) ;;
   ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   match [seq i <- iota 0 c_max | gprp (th_eval TG pp t (genc m i))] with
   | i :: _ =>
       tgts ← get tgts_loc' ;;
       #put tgts_loc' := setm tgts (size tws) (t, (m, i)) ;;
       #put tws_loc' := rcons tws t ;;
       ret (th_eval TG pp t (genc m i), i)
   | [::] =>
       #assert false ;;
       ret (th_eval TG pp t (genc m 0), 0)
   end).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ggp (b : bool) (u : unit) :
  resolve (STB b) ggpo u =
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

Lemma resolve_gck (j : nat) (mc : M) (ctr : nat) :
  resolve (STB true) gcko (j, (mc, ctr)) =
  (revealed ← get rev_loc' ;;
   #assert revealed ;;
   tgts ← get tgts_loc' ;;
   match getm tgts j with
   | Some (t0, (m0, i0)) =>
       ppo ← get pp_loc' ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
            end ;;
       ret ((mc != m0) &&
            (th_eval TG pp t0 (genc m0 i0) == th_eval TG pp t0 (genc mc ctr)))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side SCHECK answers false unconditionally. *)
Lemma resolve_gck_false (j : nat) (mc : M) (ctr : nat) :
  resolve (STB false) gcko (j, (mc, ctr)) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the package and the resolved oracle bodies folded under
   [simpl] from here on (the resolve equations above are proved). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments STCRP_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments verify_sig : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments grind_enc : simpl never.
#[local] Arguments decode_tweak : simpl never.

(** The SQUERY answer decodes to the signed digit vector (the [Tgr]
    tweak evaluates the scheme's Hgrind at the canonical address, by
    [decode_tweakK]-computation). *)
Lemma digest_resE (pp : PP) (m : M) (c : nat) :
  digits_w w l (th_eval TG pp gtw (genc m c)) = wdigest pp m c.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** The invariant (header) *)

Definition IGNG : Locations :=
  [fmap pk_loc' ; log_loc' ; sig_loc' ; rg_pk_loc ; rg_log_loc ; rg_sig_loc ;
        pp_loc' ; tgts_loc' ; tws_loc' ; rev_loc' ].

Definition RG (pko : option (Pk WC)) (lg : seq (Msg WC))
    (sgo : option (Sig WC))
    (pko' : option (Pk WC)) (lg' : seq (Msg WC)) (sgo' : option (Sig WC))
    (po : option PP) (tg : {fmap nat -> (th_T TG × (M × 'nat))})
    (tw : seq (th_T TG)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : M) (c : nat) (sg : seq N),
            [/\ lg = [:: m], sgo = Some (sg, c), po = Some pk.1,
                tg = setm emptym 0 (gtw, (m, c))
              & tw = [:: gtw] /\ rv = true]
      end].

Definition grind_inv : precond :=
  heap_ignore IGNG
  ⋊ rel_app [:: (lhs, pk_loc') ; (lhs, log_loc') ; (lhs, sig_loc') ;
                (rhs, rg_pk_loc) ; (rhs, rg_log_loc) ; (rhs, rg_sig_loc) ;
                (rhs, pp_loc') ; (rhs, tgts_loc') ; (rhs, tws_loc') ;
                (rhs, rev_loc') ] RG.

Arguments grind_inv : simpl never.

Lemma grind_invE s0 s1 :
  grind_inv (s0, s1) ->
  heap_ignore IGNG (s0, s1) /\
  RG (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rg_pk_loc) (get_heap s1 rg_log_loc) (get_heap s1 rg_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma grind_invI s0 s1 :
  heap_ignore IGNG (s0, s1) ->
  RG (get_heap s0 pk_loc') (get_heap s0 log_loc') (get_heap s0 sig_loc')
     (get_heap s1 rg_pk_loc) (get_heap s1 rg_log_loc) (get_heap s1 rg_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc') ->
  grind_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside COMMIT, machinery dropped)

    The heaps satisfy [heap_ignore IGNG] and the four STCRP locations
    hold exactly the given values (the committed-targets history is
    [::] or the single grinding target). *)

Definition gblk (po : option PP) (rv : bool)
    (tw : seq (th_T TG)) (tg : {fmap nat -> (th_T TG × (M × 'nat))}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNG (s0, s1),
      get_heap s1 pp_loc' = po,
      get_heap s1 rev_loc' = rv,
      get_heap s1 tws_loc' = tw &
      get_heap s1 tgts_loc' = tg].

Arguments gblk : simpl never.

(** The lazy parameter sampling (put pp). *)
Lemma gblk_set_pp (pp : PP) rv tw tg s0 s1 :
  gblk None rv tw tg (s0, s1) ->
  gblk (Some pp) rv tw tg (s0, set_heap s1 pp_loc' (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The SQUERY state update (put tgts; put tws). *)
Lemma gblk_qupd (pp : PP) (m : M) (c : nat) s0 s1 :
  gblk (Some pp) false [::] emptym (s0, s1) ->
  gblk (Some pp) false [:: gtw] (setm emptym 0 (gtw, (m, c)))
    (s0, set_heap (set_heap s1 tgts_loc' (setm emptym 0 (gtw, (m, c))))
           tws_loc' [:: gtw]).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

(** The phase flip (SGETPP's put rev). *)
Lemma gblk_set_rev (po : option PP) tw tg s0 s1 :
  gblk po false tw tg (s0, s1) ->
  gblk po true tw tg (s0, set_heap s1 rev_loc' true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The common COMMIT tail

    Both sides sample the re-rooted chains at the signed digest and
    store key/log/signature; the invariant is re-established from the
    final block state.  Parametric in nothing oracle-side: by this
    point all STCRP interaction is over. *)

Lemma r_commit_tail (pp : PP) (m : M) (c : nat) :
  ⊢ ⦃ λ '(s0, s1),
        gblk (Some pp) true [:: gtw] (setm emptym 0 (gtw, (m, c)))
          (s0, s1) ⦄
     (sg ← sample_sig_roots PP N FW dN pp 0 (wdigest pp m c) ;;
      #put pk_loc' := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)) ;;
      #put log_loc' := [:: m] ;;
      #put sig_loc' := Some (sg, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)), Some (sg, c)))
   ≈ (sg ← sample_sig_roots PP N FW dN pp 0 (wdigest pp m c) ;;
      #put rg_pk_loc := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)) ;;
      #put rg_log_loc := [:: m] ;;
      #put rg_sig_loc := Some (sg, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)), Some (sg, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ grind_inv (s0, s1) ⦄.
Proof.
eapply r_scheme_bind; first exact: sample_sig_roots_valid.
move=> sg.
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
apply: grind_invI.
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
  by exists m, c, sg; split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence *)

Lemma R_gr_real
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : M * nat),
        Hgrind pp' a x < w ^ l) :
  perfect (I_KOTS WC) (G1W true)
          (R_gr ∘ STCRP_game TG CG M genc gprp c_max 1 true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ grind_inv).
{ rewrite /grind_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), gblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/grind_invE: hinv => hign hRG.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRG => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the single SQUERY: the oracle performs the grinding *)
  rewrite (resolve_gsq true gtw m).
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
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (gblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  (* the in-oracle search is find_ctr: split on its outcome *)
  have hfc := grind_search_find_ctr PP M Hgrind dPP dM w l S_wn c_max
                zstar istar pp m.
  case E: [seq i <- iota 0 c_max | gprp (th_eval TG pp gtw (genc m i))]
    => [|c crest]; rewrite E /= in hfc.
  + (* grinding failure: both sides abort *)
    rewrite -hfc /=.
    exact: r_fail_bind_rhs.
  + (* grinding success at the signed counter c *)
    rewrite -hfc /=.
    eapply (r_get_rhs_known tgts_loc' emptym).
      { by move=> s0 s1 [_ _ _ _ h]. }
    eapply r_put2_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_qupd pp m c _ _ hpre). }
    rewrite (resolve_ggp true Datatypes.tt).
    eapply (r_get_bind_rhs pp_loc' (Some pp)).
      { by move=> s0 s1 [_ h _ _ _]. }
    cbv beta iota.
    simpl.
    eapply r_put_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_set_rev _ _ _ _ _ hpre). }
    rewrite (code_link_bind (sample_sig_roots PP N FW dN pp 0
              (digits_w w l (th_eval TG pp gtw (genc m c))))).
    rewrite (code_link_scheme _ _ _ _
              (sample_sig_roots_valid PP N FW dN emptym _ pp 0 _)).
    rewrite !digest_resE.
    exact: r_commit_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
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
      case/grind_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
            lg = [:: m] /\ sgov = Some (sg, c))).
    { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
      case/grind_invE: hinv => _ [_ _ e3 hmatch].
      rewrite /rem_inv /= in h1 h2 h3 h4 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ _ _]]].
      exists mm, cc, sgg; split.
      - by rewrite -h3.
      - by rewrite -h5 e3. }
  move=> [m [c [sg [hlg hsgov]]]].
  rewrite hlg hsgov /=.
  case E0: (wverify pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[hinv _] _] _] _] _].
  + case/andP: (E0) => _ hfresh.
    case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B); last first.
    * (* non-GRIND cases: both sides answer true *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[hinv _] _] _] _] _].
    * (* GRIND: SCHECK answers true = G1w-real's verdict *)
      simpl.
      rewrite (resolve_gck 0 mst sgst.2).
      eapply (r_get_bind_rhs rev_loc' true).
        { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
          case/grind_invE: hinv => _ [_ _ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => mm [cc [sgg [_ _ _ _ [_ hrv]]]]. }
      cbv beta.
      eapply r_bind_assertD_rhs; first by [].
      move=> _.
      eapply r_get_remember_rhs => tg.
      eapply (r_fact (tg = setm emptym 0 (gtw, (m, c)))).
        { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
          case/grind_invE: hinv => _ [_ _ e3 hmatch].
          rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6.
          rewrite h1 in hmatch.
          case: hmatch => mm [cc [sgg [hA hB _ hC _]]].
          have emm : mm = m.
            { have : [:: mm] = [:: m] by rewrite -hA h3.
              by case. }
          have ecc : cc = c.
            { have : Some (sgg, cc) = Some (sg, c).
              { by rewrite -hB -e3 h5. }
              by case. }
          by rewrite -h6 hC emm ecc. }
      move=> htg.
      rewrite htg setmE /=.
      eapply (r_get_rhs_known pp_loc' (Some pk.1)).
        { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
          case/grind_invE: hinv => _ [_ _ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => mm [cc [sgg [_ _ hpo _ _]]]. }
      simpl.
      have hne : mst != m := notin_log_neq M m mst hfresh.
      have hcol := wdigest_inj PP M Hgrind w l zstar istar pk.1
                     mst sgst.2 m c Hrange (eqP E1).
      rewrite /grind_enc !th_evalE_Tgr hne hcol eqxx /=.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence *)

Lemma R_gr_ideal :
  perfect (I_KOTS WC) Gmid1
          (R_gr ∘ STCRP_game TG CG M genc gprp c_max 1 false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ grind_inv).
{ rewrite /grind_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (the SQUERY/SGETPP bodies
     and the COMMIT tail are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), gblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/grind_invE: hinv => hign hRG.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRG => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_gsq false gtw m).
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
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (gblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  have hfc := grind_search_find_ctr PP M Hgrind dPP dM w l S_wn c_max
                zstar istar pp m.
  case E: [seq i <- iota 0 c_max | gprp (th_eval TG pp gtw (genc m i))]
    => [|c crest]; rewrite E /= in hfc.
  + rewrite -hfc /=.
    exact: r_fail_bind_rhs.
  + rewrite -hfc /=.
    eapply (r_get_rhs_known tgts_loc' emptym).
      { by move=> s0 s1 [_ _ _ _ h]. }
    eapply r_put2_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_qupd pp m c _ _ hpre). }
    rewrite (resolve_ggp false Datatypes.tt).
    eapply (r_get_bind_rhs pp_loc' (Some pp)).
      { by move=> s0 s1 [_ h _ _ _]. }
    cbv beta iota.
    simpl.
    eapply r_put_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_set_rev _ _ _ _ _ hpre). }
    rewrite (code_link_bind (sample_sig_roots PP N FW dN pp 0
              (digits_w w l (th_eval TG pp gtw (genc m c))))).
    rewrite (code_link_scheme _ _ _ _
              (sample_sig_roots_valid PP N FW dN emptym _ pp 0 _)).
    rewrite !digest_resE.
    exact: r_commit_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
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
      case/grind_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => sgol.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (sgov = sgol)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/grind_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : M) (c : nat) (sg : seq N),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/grind_invE: hinv => _ [_ _ _ hmatch].
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
  + case E1: ((wdigest pk.1 mst sgst.2 == wdigest pk.1 m c)%B); last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * (* GRIND: ideal SCHECK answers false = Gmid1's null *)
      simpl.
      rewrite (resolve_gck_false 0 mst sgst.2).
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

End GrindHop.
