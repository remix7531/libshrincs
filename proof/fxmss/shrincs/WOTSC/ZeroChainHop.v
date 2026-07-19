(** * SHRINCS.WOTSC.ZeroChainHop

    The two forgery hops of the WOTS+C ZERO-QUERY bound (P6 work
    package "WOTSC_zero"; analysis in ZeroGames.v): a verifying
    forgery against the never-used instance classifies into COMPRESS
    (SM-TCR(Theta_l)) or CHAIN MEET (SM-PRE(F)) — no chain-collision
    and no grinding case (ZeroGames header).  Delivered:

      [R_zc_real  : perfect IKZ (G1z true)
                            (R_zc ∘ SMTCR_game Tpk Cpk 2 true)]
      [R_zc_ideal : perfect IKZ Gzmid
                            (R_zc ∘ SMTCR_game Tpk Cpk 2 false)]
      [R_zp_real  : perfect IKZ Gzmid
                            (R_zp ∘ SMPRE_game Tf Cf l true)]
      [R_zp_ideal (Hdeg) : perfect IKZ (G1z false)
                            (R_zp ∘ SMPRE_game Tf Cf l false)]

    so the consumer's triangle steps are
      [Adv (G1z true) Gzmid A <= AdvOf (SMTCR_game Tpk Cpk 2) (A ∘ R_zc)]
      [Adv Gzmid (G1z false) A <= AdvOf (SMPRE_game Tf Cf l) (A ∘ R_zp)].

    ** Part 1 — the COMPRESS hop (SM-TCR(Theta_l), budget 2)

    CompressHop.v's reduction with the grinding stripped and ONE
    DESIGN DEVIATION: the budget is 2, not 1.  The COLLQ-pin pattern
    is unavailable — [Cpk]'s collection inputs are [N ∐ (M × 'nat)],
    and the zero-query COMMIT has neither an [N] nor an [M] value to
    feed it (the used hop pinned with the committed message).  The
    pin aligning SM-TCR's lazy [pp] with G1z's eager one is instead a
    DUMMY FIRST TQUERY at the grinding address with the empty list
    input ([th_M Tpk = 'list N], always inhabited): it commits the
    junk target [(gtw, [::])] at index 0 — never CHECKed — and lazily
    initialises [pp] at a fixed program point before all per-chain
    sampling.  The REAL target [(ptw, honest ends)] sits at index 1
    (tweak freshness = [ptw_notin_gtw]); KFORGE's COMPRESS case calls
    [CHECK (1, forged completed ends)].

    Per chain the reduction samples the root locally and makes one
    COLLQ F-step to the END position ([zc_chains]; no walk — the
    virtual digit IS the end, ZeroGames header), then the real
    TQUERY (whose answer IS the compressed pk) and GETPP.

    ** Part 2 — the CHAIN MEET hop (SM-PRE(F), budget l)

    ChainHop.v's PRE half with the grinding stripped: COMMIT pins
    [pp] through PCOLLQ ([Cf]'s Theta_l member at [inl [::]] — here
    the collection DOES have an inhabited input), then one PQUERY per
    chain at the encoded chain address [(i, w-2)] ([pr_chains] at the
    virtual digits, REUSED from ChainHop): the oracle's hidden
    uniform IS G1z's re-rooted sample and its answer the honest end
    [sg_i] (for [w <= 1] the virtual digit is 0 and the value is
    sampled locally — no query, no target; the forgery analysis never
    reaches PCHECK there).  KFORGE mirrors Gzmid's verdict: refusals
    and the COMPRESS case answer false locally; on equal completions
    the computable selector [zsel] picks the attacked chain [i]
    (forged digit < w-1) and PCHECK gets [(i, preimage)] — the
    preimage recomputed from the forged signature ([zpre_win]
    packaging ZeroGames' [zends_nth]/[zmeet_preimage]); if NO chain
    qualifies the verdict is true on BOTH Gzmid and the real
    composition (no deadness needed), and on the IDEAL side that
    branch is dead by [zsel_dead] — THE place the [Hdeg] side
    condition is consumed.  The pre-commitment KFORGE gadget
    ([PCHECK (0, n0)] when nothing is committed) and its [n0 : N]
    data parameter are exactly ChainHop's.

    Locations 374/375 ([R_zc]), 376/377 ([R_zp]). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp.experimental_reals Require Import distr.
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Games.SMTCR Games.SMPRE Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis FixedSumOTS.TCRHop FixedSumOTS.PREHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis
  WOTSC.CompressHop WOTSC.ChainHop WOTSC.ZeroGames.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section ZeroChainHop.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same section context as WOTSC.ZeroGames, plus the SM-PRE
    pre-commitment inhabitant [n0] (data only; PREHop's documented
    side condition, consumed by the KFORGE gadget). *)
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
Local Notation FW := (Fw PP N F zstar istar).
Local Notation cf := (chainf PP N F zstar istar).
Local Notation TP := (Tpk PP N Tl dPP dN).
Local Notation CP := (Cpk PP N M F Tl Hgrind dPP dN).
Local Notation TF := (Tf PP N F dPP dN).
Local Notation CF := (Cf PP N M F Tl Hgrind dPP dN).
Local Notation SMB2 b := (SMTCR_game TP CP 2 b).
Local Notation SMP b := (SMPRE_game TF CF l b).
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation cadrs := (chain_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation gtw := (@encode_adrs l w gadrs).
Local Notation ptw := (@encode_adrs l w padrs).
Local Notation ctw i k := (@encode_adrs l w (cadrs i k)).
Local Notation wdigest := (digest_of PP M Hgrind zstar istar).
Local Notation wcends := (complete_ends PP N F zstar istar).
Local Notation wverify :=
  (verify_sig PP N M F Tl Hgrind S_wn zstar istar).
Local Notation wsigs := (sigs_of PP N FW).
Local Notation wtw := (@wotsc_tweak w l zstar istar).
Local Notation wq' := (wq N zstar istar).
Local Notation zpreq := (pre_queries N).
Local Notation zdig := (nseq l w.-1).
Local Notation zsel' := (@zsel w).
Local Notation zchains := (pr_chains PP N F dPP dN zstar istar).

Local Notation IKZ :=
  (I_KZ PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation zpk :=
  (zpk_loc PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation zsg := (zsg_loc N).
Local Notation G1Z b :=
  (G1z PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar b).
Local Notation GZM :=
  (Gzmid PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).

(** SM-TCR / SM-PRE game-internal locations. *)
Local Notation cpp_loc := (tcr_pp_loc TP).
Local Notation ctg_loc := (tcr_tgts_loc TP).
Local Notation ctws_loc := (tcr_tws_loc TP).
Local Notation crv_loc := tcr_rev_loc.
Local Notation ppp_loc := (pre_pp_loc TF).
Local Notation ptg_loc := (pre_tgts_loc TF).
Local Notation ptws_loc := (pre_tws_loc TF).
Local Notation prv_loc := pre_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** Shared pure layer *)

Lemma size_zdig : size zdig = l.
Proof. by rewrite size_nseq. Qed.

Lemma size_wsigs pp (us : seq N) :
  size us = l -> size (wsigs pp 0 zdig us) = l.
Proof.
move=> h.
by rewrite (size_sigs_of PP N FW) ?size_zdig // h size_zdig.
Qed.

(** PQUERY index of chain [i] at the virtual digits: every earlier
    chain queries exactly once (positive virtual digit). *)
Lemma zpre_indexE (i : nat) :
  0 < w.-1 -> i <= l -> pre_index zdig i = i.
Proof.
move=> hw' hi.
by rewrite /pre_index take_nseq // /npq count_nseq /= hw' mul1n.
Qed.

(** THE PRE-win packaging (ZeroGames' analysis composed for the
    reduction's PCHECK branch): a verifying forgery whose completion
    equals the honest ends, the attacked chain [i] ([zsel]) and the
    forged value [y] at chain [i] yield the committed PQUERY entry at
    index [i] and the F-preimage equation that wins PCHECK. *)
Lemma zpre_win pp (us : seq N) (mst : M) (sgst : seq N * nat)
    (i : nat) (y : N) :
  size us = l ->
  wverify pp (Tl pp padrs (wsigs pp 0 zdig us)) mst sgst ->
  wcends pp (wdigest pp mst sgst.2) sgst.1 = wsigs pp 0 zdig us ->
  zsel' (wdigest pp mst sgst.2) = Some i ->
  qnth sgst.1 i = Some y ->
  exists ui : N,
    [/\ qnth (zpreq 0 zdig us) i = Some ((i, w.-2), ui)
      & FW pp (i, w.-2)
          (chain (cf pp i) y (nth 0 (wdigest pp mst sgst.2) i)
                 (w.-2 - nth 0 (wdigest pp mst sgst.2) i))
        = FW pp (i, w.-2) ui].
Proof.
move=> hus hver hends hsel hqy.
have [hisz hlt] := @zselP w (wdigest pp mst sgst.2) i hsel.
have hszd : size (wdigest pp mst sgst.2) = l
  := size_digest_of PP M Hgrind zstar istar pp mst sgst.2.
have hil : i < l by rewrite -hszd.
have hw1 : 0 < w.-1 := leq_ltn_trans (leq0n _) hlt.
move: (hver); rewrite /verify_sig => /and3P[_ /eqP hsy _].
have hsg : size (wsigs pp 0 zdig us) = l := size_wsigs pp us hus.
have husz : size us = size zdig by rewrite hus size_zdig.
have [ui hui] : exists ui, qnth us i = Some ui.
{ by apply: qnth_some; rewrite hus. }
have hilz : i < size zdig by rewrite size_zdig.
have hdz : 0 < nth 0 zdig i by rewrite nth_nseq hil.
have hentry := qnth_pre_queries N 0 zdig us i ui husz hilz hui hdz.
rewrite add0n nth_nseq hil (zpre_indexE i hw1 (ltnW hil)) in hentry.
exists ui; split; first by [].
have hqs := qnth_sigs_of PP N FW pp 0 zdig us i ui husz hilz hui.
rewrite add0n nth_nseq hil in hqs.
have hsi : nth y (wsigs pp 0 zdig us) i = sig_of_root PP N FW pp i w.-1 ui
  := qnth_nth y _ _ _ hqs.
have hsrE : sig_of_root PP N FW pp i w.-1 ui = FW pp (i, w.-2) ui.
{ by rewrite -[w.-1](prednK hw1). }
have hch := zends_nth PP N F zstar istar pp
              (wdigest pp mst sgst.2) sgst.1 (wsigs pp 0 zdig us) y i
              hszd hsy hsg hil hends.
rewrite (qnth_nth y _ _ _ hqy) hsi hsrE in hch.
exact: (zmeet_preimage PP N F zstar istar pp i
          (nth 0 (wdigest pp mst sgst.2) i) y (FW pp (i, w.-2) ui)
          hlt hch).
Qed.

(* ================================================================== *)
(** ** Part 1: the COMPRESS hop (SM-TCR(Theta_l), budget 2) *)

(* ------------------------------------------------------------------ *)
(** *** The oracle-routed loop *)

Definition zc_cqo : opsig := (COLLQ, (tc_T CP × tc_M CP, tc_N CP)).
Definition zc_tqo : opsig := (TQUERY, (th_T TP × th_M TP, th_N TP)).
Definition zc_gpo : opsig := (GETPP, ('unit, th_PP TP)).
Definition zc_cko : opsig := (CHECK, ('nat × th_M TP, 'bool)).

(** Per chain: local root, ONE COLLQ F-step to the end position for a
    positive (virtual) digit ([cp_chains] without the walk — at the
    virtual digits the signature value IS the completed end). *)
Fixpoint zc_chains (st : nat) (ds : seq nat) : raw_code (chList N) :=
  match ds with
  | [::] => ret [::]
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1
           then opr zc_cqo (ctw st d', inl u)
                  (λ r, ret (if r is inl y then y else u))
           else ret u) ;;
      ss ← zc_chains st.+1 ds' ;;
      ret (s :: ss)
  end.

#[local] Instance zc_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMTCR TP CP) (zc_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by fmap_solve.
    move=> r; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: IH.
    move=> ss; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

Definition rzc_pk_loc := mkloc 374 (None : option (Pk WC)).
Definition rzc_sg_loc := mkloc 375 (None : option (chList N)).

Definition R_zc : package (I_SMTCR TP CP) IKZ :=
  [package [fmap rzc_pk_loc ; rzc_sg_loc ] ;
    [ COMMIT ] : { 'unit ~> Pk WC } (_) {
      pko ← get rzc_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr zc_tqo (gtw, [::]) (λ r, ret r) ;;
      sgs ← zc_chains 0 zdig ;;
      root ← opr zc_tqo (ptw, sgs) (λ r, ret r) ;;
      pp ← opr zc_gpo Datatypes.tt (λ p, ret p) ;;
      #put rzc_pk_loc := Some (pp, root) ;;
      #put rzc_sg_loc := Some sgs ;;
      ret (pp, root)
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pk ← getSome rzc_pk_loc ;;
      sgo ← get rzc_sg_loc ;;
      match sgo with
      | Some sg =>
          if wverify pk.1 pk.2 mst sgst
          then
            if wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1 != sg
            then opr zc_cko
                   (1, wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1)
                   (λ ans, ret ans)
            else ret true
          else ret false
      | None => ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies (CompressHop's resolve equations at
    budget 2) *)

Lemma resolve_zc_tq (b : bool) (t : th_T TP) (xs : th_M TP) :
  resolve (SMB2 b) zc_tqo (t, xs) =
  (revealed ← get crv_loc ;;
   #assert ~~ revealed ;;
   tws ← get ctws_loc ;;
   #assert (size tws < 2)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get ctg_loc ;;
   #put ctg_loc := setm tgts (size tws) (t, xs) ;;
   #put ctws_loc := rcons tws t ;;
   ppo ← get cpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put cpp_loc := Some pp ;; ret pp
        end ;;
   ret (th_eval TP pp t xs)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_zc_cq (b : bool) (t : tc_T CP) (x : tc_M CP) :
  resolve (SMB2 b) zc_cqo (t, x) =
  (ppo ← get cpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put cpp_loc := Some pp ;; ret pp
        end ;;
   ret (tc_eval CP pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_zc_gp (b : bool) (u : unit) :
  resolve (SMB2 b) zc_gpo u =
  (ppo ← get cpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put cpp_loc := Some pp ;; ret pp
        end ;;
   #put crv_loc := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_zc_ck (j : nat) (xs : th_M TP) :
  resolve (SMB2 true) zc_cko (j, xs) =
  (revealed ← get crv_loc ;;
   #assert revealed ;;
   tgts ← get ctg_loc ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get cpp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put cpp_loc := Some pp ;; ret pp
            end ;;
       ret ((xs != m0) && (th_eval TP pp t0 xs == th_eval TP pp t0 m0))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

Lemma resolve_zc_ck_false (j : nat) (xs : th_M TP) :
  resolve (SMB2 false) zc_cko (j, xs) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the packages, resolved bodies and the pure layer folded
   (GrindHop/CompressHop lessons). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments SMPRE_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments verify_sig : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments zsel : simpl never.
#[local] Arguments pre_queries : simpl never.
#[local] Arguments pre_index : simpl never.
#[local] Arguments qnth : simpl never.

(** Conversion bridge: the COLLQ answer at a chain address,
    post-processed by the loop's [inl]-projection, IS the scheme's
    F-step (CompressHop's [collq_F_E], local copy). *)
Lemma zc_collq_F_E (pp : PP) (i k : nat) (x : N) :
  (if tc_eval CP pp (ctw i k) (inl x) is inl y then y else x)
  = F pp (cadrs i k) x.
Proof. by rewrite /tc_eval /Cpk /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** *** The invariant *)

Definition IGNZC : Locations :=
  [fmap zpk ; zsg ; rzc_pk_loc ; rzc_sg_loc ;
        cpp_loc ; ctg_loc ; ctws_loc ; crv_loc ].

Definition RZC (pko : option (Pk WC)) (sgo : option (chList N))
    (pko' : option (Pk WC)) (sgo' : option (chList N))
    (po : option PP) (tg : {fmap nat -> (th_T TP × th_M TP)})
    (tw : seq (th_T TP)) (rv : bool) : Prop :=
  [/\ pko' = pko, sgo' = sgo &
      match pko with
      | None =>
          [/\ sgo = None, po = None, tg = emptym & tw = [::] /\ rv = false]
      | Some pk =>
          exists sg : seq N,
            [/\ sgo = Some sg, po = Some pk.1,
                pk.2 = Tl pk.1 padrs sg
                /\ tg = setm (setm emptym 0 (gtw, [::] : seq N)) 1 (ptw, sg)
              & tw = [:: gtw; ptw] /\ rv = true]
      end].

Definition zc_inv : precond :=
  heap_ignore IGNZC
  ⋊ rel_app [:: (lhs, zpk) ; (lhs, zsg) ;
                (rhs, rzc_pk_loc) ; (rhs, rzc_sg_loc) ;
                (rhs, cpp_loc) ; (rhs, ctg_loc) ; (rhs, ctws_loc) ;
                (rhs, crv_loc) ] RZC.

Arguments zc_inv : simpl never.

Lemma zc_invE s0 s1 :
  zc_inv (s0, s1) ->
  heap_ignore IGNZC (s0, s1) /\
  RZC (get_heap s0 zpk) (get_heap s0 zsg)
      (get_heap s1 rzc_pk_loc) (get_heap s1 rzc_sg_loc)
      (get_heap s1 cpp_loc) (get_heap s1 ctg_loc) (get_heap s1 ctws_loc)
      (get_heap s1 crv_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma zc_invI s0 s1 :
  heap_ignore IGNZC (s0, s1) ->
  RZC (get_heap s0 zpk) (get_heap s0 zsg)
      (get_heap s1 rzc_pk_loc) (get_heap s1 rzc_sg_loc)
      (get_heap s1 cpp_loc) (get_heap s1 ctg_loc) (get_heap s1 ctws_loc)
      (get_heap s1 crv_loc) ->
  zc_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** *** The block precondition (inside COMMIT) *)

Definition zcblk (po : option PP) (rv : bool)
    (tw : seq (th_T TP)) (tg : {fmap nat -> (th_T TP × th_M TP)}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNZC (s0, s1),
      get_heap s1 cpp_loc = po,
      get_heap s1 crv_loc = rv,
      get_heap s1 ctws_loc = tw &
      get_heap s1 ctg_loc = tg].

Arguments zcblk : simpl never.

(** The dummy first TQUERY's state update. *)
Lemma zcblk_qupd0 s0 s1 :
  zcblk None false [::] emptym (s0, s1) ->
  zcblk None false [:: gtw] (setm emptym 0 (gtw, [::] : seq N))
    (s0, set_heap (set_heap s1 ctg_loc (setm emptym 0 (gtw, [::] : seq N)))
           ctws_loc [:: gtw]).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

(** The lazy parameter sampling (inside the dummy TQUERY). *)
Lemma zcblk_set_pp (pp : PP) rv tw tg s0 s1 :
  zcblk None rv tw tg (s0, s1) ->
  zcblk (Some pp) rv tw tg (s0, set_heap s1 cpp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The REAL TQUERY's state update. *)
Lemma zcblk_qupd1 (pp : PP) (xs : th_M TP) s0 s1 :
  zcblk (Some pp) false [:: gtw] (setm emptym 0 (gtw, [::] : seq N))
    (s0, s1) ->
  zcblk (Some pp) false [:: gtw; ptw]
    (setm (setm emptym 0 (gtw, [::] : seq N)) 1 (ptw, xs))
    (s0, set_heap (set_heap s1 ctg_loc
            (setm (setm emptym 0 (gtw, [::] : seq N)) 1 (ptw, xs)))
          ctws_loc [:: gtw; ptw]).
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
Lemma zcblk_set_rev (po : option PP) tw tg s0 s1 :
  zcblk po false tw tg (s0, s1) ->
  zcblk po true tw tg (s0, set_heap s1 crv_loc true).
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

Lemma r_zccollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CP) (x : tc_M CP) rv tw tg
    (c0 : raw_code B) (k1 : tc_N CP -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), zcblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CP pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), zcblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB2 b) zc_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_zc_cq b t x).
eapply (r_get_bind_rhs cpp_loc (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain loop spec *)

(** lhs [sample_sig_roots] at [FW] (G1z's sampling at the virtual
    digits), rhs the linked [zc_chains]; the roots are coupled
    pointwise, both results are [sigs_of] of the roots
    ([r_cchains_spec] without the walk/ends component). *)
Lemma r_zcchains_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall ds st rv tw tg (K0 K1 : chList N -> raw_code B),
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), zcblk (Some pp) rv tw tg (s0, s1) ⦄
        K0 (wsigs pp st ds us) ≈ K1 (wsigs pp st ds us) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), zcblk (Some pp) rv tw tg (s0, s1) ⦄
     bind (sample_sig_roots PP N FW dN pp st ds) K0
   ≈ bind (code_link (zc_chains st ds) (SMB2 b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st rv tw tg K0 K1 h.
- exact: (h [::] erefl).
- rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN))
          !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d h => [|d'] h.
  + (* d = 0: the value is the root itself *)
    rewrite code_link_bind bind_assoc /=.
    rewrite (code_link_bind (zc_chains st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
  + (* d = d'.+1: one COLLQ F-step to the end *)
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_zccollq_known b).
    cbv beta.
    rewrite zc_collq_F_E /=.
    rewrite (code_link_bind (zc_chains st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The common COMMIT tail *)

Lemma r_zc_tail (pp : PP) (sg : seq N) :
  ⊢ ⦃ λ '(s0, s1),
        zcblk (Some pp) true [:: gtw; ptw]
          (setm (setm emptym 0 (gtw, [::] : seq N)) 1 (ptw, sg)) (s0, s1) ⦄
     (#put zpk := Some (pp, Tl pp padrs sg) ;;
      #put zsg := Some sg ;;
      ret (pp, Tl pp padrs sg))
   ≈ (#put rzc_pk_loc := Some (pp, Tl pp padrs sg) ;;
      #put rzc_sg_loc := Some sg ;;
      ret (pp, Tl pp padrs sg))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ zc_inv (s0, s1) ⦄.
Proof.
eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s0c [hpre3 ->].
case: hpre3 => s0d [hblk ->].
case: hblk => hign hpp hrev htws htgts.
split; first by [].
apply: zc_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists sg; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_zc_real :
  perfect IKZ (G1Z true) (R_zc ∘ SMTCR_game TP CP 2 true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ zc_inv).
{ rewrite /zc_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zc_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), zcblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/zc_invE: hinv => hign hRC.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRC => _ _; rewrite hrem0 => -[_ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the dummy first TQUERY: SM-TCR's lazy pp sampled here, against
     G1z's eager one *)
  eapply (r_get_rhs_known crv_loc false).
    { by move=> s0 s1 [_ _ h _ _]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs ctws_loc [::]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs ctg_loc emptym).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre; exact: (zcblk_qupd0 s0 s1 hpre). }
  eapply (r_get_bind_rhs cpp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (zcblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  (* the chains, roots sampled locally on both sides *)
  eapply (r_zcchains_spec true pp).
  move=> us hus.
  cbv beta.
  simpl.
  (* the REAL TQUERY: commit the honest ends *)
  eapply (r_get_rhs_known crv_loc false).
    { by move=> s0 s1 [_ _ h _ _]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs ctws_loc [:: gtw]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs.
    { by move=> s0 s1 _; exact: ptw_notin_gtw. }
  move=> _.
  eapply (r_get_bind_rhs ctg_loc (setm emptym 0 (gtw, [::] : seq N))).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre;
      exact: (zcblk_qupd1 pp (wsigs pp 0 zdig us) s0 s1 hpre). }
  eapply (r_get_bind_rhs cpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  rewrite !(th_evalE_Tpk PP N Tl dPP dN).
  (* GETPP: reveal pp, flip the phase *)
  eapply (r_get_rhs_known cpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (zcblk_set_rev _ _ _ _ _ hpre). }
  exact: r_zc_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zc_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (exists sg : seq N,
            sgov = Some sg /\ pk.2 = Tl pk.1 padrs sg)).
    { move=> s0 s1 [[[hinv h1] h2] h3].
      case/zc_invE: hinv => _ [_ e2 hmatch].
      rewrite /rem_inv /= in h1 h2 h3.
      rewrite h1 in hmatch.
      case: hmatch => sg [hB hpo [hpk2 _] _].
      exists sg; split; last by [].
      by rewrite -h3 e2 hB. }
  move=> [sg [hsgov hpk2]].
  rewrite hsgov /=.
  case E0: (wverify pk.1 pk.2 mst sgst); last first.
  + (* invalid forgery: both sides answer false *)
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[hinv _] _] _].
  + case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1 != sg)%B);
      last first.
    * (* equal completions (CHAIN MEET): both sides answer true *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[hinv _] _] _].
    * (* COMPRESS: CHECK (1, forged ends) answers true = G1z's
         verdict *)
      simpl.
      rewrite (resolve_zc_ck 1
                (wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1)).
      eapply (r_get_bind_rhs crv_loc true).
        { move=> s0 s1 [[[hinv h1] h2] h3].
          case/zc_invE: hinv => _ [_ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => sgg [_ _ _ [_ hrv]]. }
      cbv beta.
      eapply r_bind_assertD_rhs; first by [].
      move=> _.
      eapply r_get_remember_rhs => tg.
      eapply (r_fact
        (tg = setm (setm emptym 0 (gtw, [::] : seq N)) 1 (ptw, sg))).
        { move=> s0 s1 [[[[hinv h1] h2] h3] h4].
          case/zc_invE: hinv => _ [_ e2 hmatch].
          rewrite /rem_inv /= in h1 h3 h4.
          rewrite h1 in hmatch.
          case: hmatch => sgg [hB _ [_ hC] _].
          have esg : sgg = sg.
          { have : Some sgg = Some sg by rewrite -hB -e2 h3.
            by case. }
          by rewrite -h4 hC esg. }
      move=> htg.
      rewrite htg setmE /=.
      eapply (r_get_rhs_known cpp_loc (Some pk.1)).
        { move=> s0 s1 [[[[hinv h1] h2] h3] h4].
          case/zc_invE: hinv => _ [_ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => sgg [_ hpo _ _]. }
      simpl.
      rewrite !(th_evalE_Tpk PP N Tl dPP dN).
      have hver : wverify pk.1 pk.2 mst sgst by rewrite E0.
      move: hver; rewrite /verify_sig => /and3P[_ _ /eqP hTl].
      rewrite E2 hTl hpk2 eqxx /=.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[hinv _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence *)

Lemma R_zc_ideal :
  perfect IKZ GZM (R_zc ∘ SMTCR_game TP CP 2 false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ zc_inv).
{ rewrite /zc_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (the TQUERY/COLLQ/GETPP
     bodies and the loop spec are b-independent) *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zc_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), zcblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/zc_invE: hinv => hign hRC.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRC => _ _; rewrite hrem0 => -[_ hpo htg [htw hrv]].
    by split. }
  simpl.
  eapply (r_get_rhs_known crv_loc false).
    { by move=> s0 s1 [_ _ h _ _]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs ctws_loc [::]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs ctg_loc emptym).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre; exact: (zcblk_qupd0 s0 s1 hpre). }
  eapply (r_get_bind_rhs cpp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (zcblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  eapply (r_zcchains_spec false pp).
  move=> us hus.
  cbv beta.
  simpl.
  eapply (r_get_rhs_known crv_loc false).
    { by move=> s0 s1 [_ _ h _ _]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs ctws_loc [:: gtw]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs.
    { by move=> s0 s1 _; exact: ptw_notin_gtw. }
  move=> _.
  eapply (r_get_bind_rhs ctg_loc (setm emptym 0 (gtw, [::] : seq N))).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre;
      exact: (zcblk_qupd1 pp (wsigs pp 0 zdig us) s0 s1 hpre). }
  eapply (r_get_bind_rhs cpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  rewrite !(th_evalE_Tpk PP N Tl dPP dN).
  eapply (r_get_rhs_known cpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (zcblk_set_rev _ _ _ _ _ hpre). }
  exact: r_zc_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zc_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => sgol.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (sgov = sgol)).
    { move=> s0 s1 [[[[hinv _] _] h3] h4].
      case/zc_invE: hinv => _ [_ e2 _].
      rewrite /rem_inv /= in h3 h4.
      by rewrite -h3 -h4 e2. }
  move=> e; subst sgov.
  eapply (r_fact (exists sg : seq N,
            sgol = Some sg /\ pk.2 = Tl pk.1 padrs sg)).
    { move=> s0 s1 [[[[hinv h1] h2] h3] h4].
      case/zc_invE: hinv => _ [_ e2 hmatch].
      rewrite /rem_inv /= in h1 h3.
      rewrite h1 in hmatch.
      case: hmatch => sg [hB hpo [hpk2 _] _].
      exists sg; split; last by [].
      by rewrite -h3 hB. }
  move=> [sg [hsgol hpk2]].
  rewrite hsgol /=.
  case E0: (wverify pk.1 pk.2 mst sgst); last first.
  + apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[hinv _] _] _] _].
  + case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1 != sg)%B);
      last first.
    * (* equal completions: both sides answer true *)
      move/negbFE: E2 => E2'.
      rewrite E2' /=.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[hinv _] _] _] _].
    * (* COMPRESS: ideal CHECK answers false = Gzmid's null *)
      simpl.
      rewrite (negbTE E2).
      rewrite (resolve_zc_ck_false 1
                (wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1)).
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[hinv _] _] _] _].
Qed.

(* ================================================================== *)
(** ** Part 2: the CHAIN MEET hop (SM-PRE(F), budget l) *)

(* ------------------------------------------------------------------ *)
(** *** Opsigs and the (reused) per-chain loop *)

Definition zp_pqo : opsig := (PQUERY, (th_T TF, th_N TF)).
Definition zp_gpo : opsig := (PGETPP, ('unit, th_PP TF)).
Definition zp_cko : opsig := (PCHECK, ('nat × th_M TF, 'bool)).
Definition zp_cqo : opsig := (PCOLLQ, (tc_T CF × tc_M CF, tc_N CF)).

(** ChainHop's [pr_chains] is reused VERBATIM (its local ValidCode
    instance does not export; re-derived here). *)
#[local] Instance zp_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMPRE TF CF) (zchains st ds).
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

Definition rzp_pk_loc := mkloc 376 (None : option (Pk WC)).
Definition rzp_sg_loc := mkloc 377 (None : option (chList N)).

Definition R_zp : package (I_SMPRE TF CF) IKZ :=
  [package [fmap rzp_pk_loc ; rzp_sg_loc ] ;
    [ COMMIT ] : { 'unit ~> Pk WC } (_) {
      pko ← get rzp_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr zp_cqo (gtw, inl [::]) (λ r, ret r) ;;
      sgs ← zchains 0 zdig ;;
      pp ← opr zp_gpo Datatypes.tt (λ p, ret p) ;;
      #put rzp_pk_loc := Some (pp, Tl pp padrs sgs) ;;
      #put rzp_sg_loc := Some sgs ;;
      ret (pp, Tl pp padrs sgs)
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pko ← get rzp_pk_loc ;;
      match pko with
      | None =>
          (* pre-commitment gadget: real PCHECK fails on the phase
             assert (mirroring Gzmid's getSome), ideal PCHECK returns
             false (mirroring G1z-ideal) *)
          opr zp_cko (0, n0) (λ ans, ret ans)
      | Some pk =>
          sgo ← get rzp_sg_loc ;;
          match sgo with
          | Some sg =>
              if wverify pk.1 pk.2 mst sgst
              then
                if wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1 != sg
                then ret false
                else
                  match zsel' (wdigest pk.1 mst sgst.2) with
                  | Some i =>
                      match qnth sgst.1 i with
                      | Some y =>
                          opr zp_cko
                            (i, chain (cf pk.1 i) y
                                  (nth 0 (wdigest pk.1 mst sgst.2) i)
                                  (w.-2 - nth 0 (wdigest pk.1 mst sgst.2) i))
                            (λ ans, ret ans)
                      | None => ret false
                      end
                  | None => ret true
                  end
              else ret false
          | None => ret false
          end
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies (ChainHop's resolve equations, local) *)

Lemma resolve_zp_cq (b : bool) (t : tc_T CF) (x : tc_M CF) :
  resolve (SMP b) zp_cqo (t, x) =
  (ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   ret (tc_eval CF pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_zp_pq (b : bool) (t : th_T TF) :
  resolve (SMP b) zp_pqo t =
  (revealed ← get prv_loc ;;
   #assert ~~ revealed ;;
   tws ← get ptws_loc ;;
   #assert (size tws < l)%N ;;
   #assert (t \notin tws) ;;
   x ← dN ;;
   tgts ← get ptg_loc ;;
   #put ptg_loc := setm tgts (size tws) (t, x) ;;
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

Lemma resolve_zp_gp (b : bool) (u : unit) :
  resolve (SMP b) zp_gpo u =
  (ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   #put prv_loc := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_zp_ck (j : nat) (x : th_M TF) :
  resolve (SMP true) zp_cko (j, x) =
  (revealed ← get prv_loc ;;
   #assert revealed ;;
   tgts ← get ptg_loc ;;
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

Lemma resolve_zp_ck_false (j : nat) (x : th_M TF) :
  resolve (SMP false) zp_cko (j, x) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The invariant *)

Definition IGNZP : Locations :=
  [fmap zpk ; zsg ; rzp_pk_loc ; rzp_sg_loc ;
        ppp_loc ; ptg_loc ; ptws_loc ; prv_loc ].

Definition RZP (pko : option (Pk WC)) (sgo : option (chList N))
    (pko' : option (Pk WC)) (sgo' : option (chList N))
    (po : option PP) (tg : {fmap nat -> (th_T TF × th_M TF)})
    (tw : seq (th_T TF)) (rv : bool) : Prop :=
  [/\ pko' = pko, sgo' = sgo &
      match pko with
      | None =>
          [/\ sgo = None, po = None, tg = emptym & tw = [::] /\ rv = false]
      | Some pk =>
          exists us : seq N,
            [/\ sgo = Some (wsigs pk.1 0 zdig us), po = Some pk.1,
                size us = l /\ pk.2 = Tl pk.1 padrs (wsigs pk.1 0 zdig us)
              & [/\ tg = qmap_from 0 [seq wq' q | q <- zpreq 0 zdig us],
                    tw = [seq wtw t | t <- unzip1 (zpreq 0 zdig us)]
                  & rv = true]]
      end].

Definition zp_inv : precond :=
  heap_ignore IGNZP
  ⋊ rel_app [:: (lhs, zpk) ; (lhs, zsg) ;
                (rhs, rzp_pk_loc) ; (rhs, rzp_sg_loc) ;
                (rhs, ppp_loc) ; (rhs, ptg_loc) ; (rhs, ptws_loc) ;
                (rhs, prv_loc) ] RZP.

Arguments zp_inv : simpl never.

Lemma zp_invE s0 s1 :
  zp_inv (s0, s1) ->
  heap_ignore IGNZP (s0, s1) /\
  RZP (get_heap s0 zpk) (get_heap s0 zsg)
      (get_heap s1 rzp_pk_loc) (get_heap s1 rzp_sg_loc)
      (get_heap s1 ppp_loc) (get_heap s1 ptg_loc) (get_heap s1 ptws_loc)
      (get_heap s1 prv_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma zp_invI s0 s1 :
  heap_ignore IGNZP (s0, s1) ->
  RZP (get_heap s0 zpk) (get_heap s0 zsg)
      (get_heap s1 rzp_pk_loc) (get_heap s1 rzp_sg_loc)
      (get_heap s1 ppp_loc) (get_heap s1 ptg_loc) (get_heap s1 ptws_loc)
      (get_heap s1 prv_loc) ->
  zp_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** *** The block precondition (inside COMMIT) *)

Definition zpblk (po : option PP) (rv : bool)
    (Q : seq ((nat * nat) * N)) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNZP (s0, s1),
      get_heap s1 ppp_loc = po,
      get_heap s1 prv_loc = rv,
      get_heap s1 ptws_loc = [seq wtw t | t <- unzip1 Q] &
      get_heap s1 ptg_loc = qmap_from 0 [seq wq' q | q <- Q]].

Arguments zpblk : simpl never.

(** The lazy parameter sampling (at the PCOLLQ pin). *)
Lemma zpblk_set_pp (pp : PP) rv Q s0 s1 :
  zpblk None rv Q (s0, s1) ->
  zpblk (Some pp) rv Q (s0, set_heap s1 ppp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The PQUERY state update (put tgts; put tws). *)
Lemma zpblk_qupd (pp : PP) (Q : seq ((nat * nat) * N)) (t : nat * nat)
    (x : N) s0 s1 :
  zpblk (Some pp) false Q (s0, s1) ->
  zpblk (Some pp) false (rcons Q (t, x))
    (s0, set_heap (set_heap s1 ptg_loc
            (setm (qmap_from 0 [seq wq' q | q <- Q])
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
Lemma zpblk_set_rev (po : option PP) Q s0 s1 :
  zpblk po false Q (s0, s1) ->
  zpblk po true Q (s0, set_heap s1 prv_loc true).
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

Lemma r_zpcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CF) (x : tc_M CF) rv (Q : seq ((nat * nat) * N))
    (c0 : raw_code B) (k1 : tc_N CF -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), zpblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CF pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), zpblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMP b) zp_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_zp_cq b t x).
eapply (r_get_bind_rhs ppp_loc (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked PQUERY (ChainHop's [r_prquery]) *)

Lemma r_zpquery (b : bool) {B : choiceType} (pp : PP)
    (i k : nat) (Q : seq ((nat * nat) * N))
    (k0 k1 : N -> raw_code B) (post : postcond B B) :
  i < l -> k < w.-1 ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  size Q < l ->
  (i, k) \notin unzip1 Q ->
  (forall x : N,
     ⊢ ⦃ λ '(s0, s1), zpblk (Some pp) false (rcons Q ((i, k), x)) (s0, s1) ⦄
        k0 x ≈ k1 (FW pp (i, k) x) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), zpblk (Some pp) false Q (s0, s1) ⦄
     bind dN k0 ≈ bind (resolve (SMP b) zp_pqo (ctw i k)) k1 ⦃ post ⦄.
Proof.
move=> hi hk hQr hbud hfresh h.
rewrite (resolve_zp_pq b (ctw i k)).
eapply (r_get_bind_rhs prv_loc false).
  { by move=> s0 s1 [_ _ h' _ _]. }
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs ptws_loc [seq wtw t | t <- unzip1 Q]).
  { by move=> s0 s1 [_ _ _ h' _]. }
cbv beta.
eapply r_bind_assertD_rhs.
  { by move=> s0 s1 _; rewrite size_map /unzip1 size_map hbud. }
move=> _.
eapply r_bind_assertD_rhs.
  move=> s0 s1 _; apply: (@wtw_notin w l zstar istar
    (i, k) (unzip1 Q) Hanchor hi hk _ hfresh).
  by move=> t' /(allP hQr) /andP[h1 h2]; split.
move=> _.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> x; cbv beta.
eapply (r_get_bind_rhs ptg_loc (qmap_from 0 [seq wq' q | q <- Q])).
  { by move=> s0 s1 [_ _ _ _ h']. }
cbv beta.
eapply r_put2_bind_rhs.
  { by move=> s0 s1 hpre; exact: (zpblk_qupd pp Q (i, k) x s0 s1 hpre). }
eapply (r_get_bind_rhs ppp_loc (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
simpl.
rewrite (@th_eval_wtw w l PP N F dPP dN zstar istar pp (i, k) x).
exact: (h x).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain induction (ChainHop's [r_prchains_spec]) *)

Lemma r_zpchains_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall ds st (Q : seq ((nat * nat) * N)) (K0 K1 : chList N -> raw_code B),
  (st + size ds <= l)%N ->
  all (λ d : nat, d < w) ds ->
  all (λ t : nat * nat, (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  (size Q + npq ds <= l)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), zpblk (Some pp) false
            (Q ++ zpreq st ds us) (s0, s1) ⦄
        K0 (wsigs pp st ds us) ≈ K1 (wsigs pp st ds us) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), zpblk (Some pp) false Q (s0, s1) ⦄
     bind (sample_sig_roots PP N FW dN pp st ds) K0
   ≈ bind (code_link (zchains st ds) (SMP b)) K1 ⦃ post ⦄.
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
    rewrite (code_link_bind (zchains st.+1 ds)) !bind_assoc.
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
    eapply r_zpquery => //.
    * by apply: leq_trans hbud; rewrite /npq /= addnS ltnS leq_addr.
    * exact: lt_notin hfresh.
    * move=> x; cbv beta.
      rewrite !bind_assoc.
      simpl.
      rewrite (code_link_bind (zchains st.+1 ds)) !bind_assoc.
      eapply IH => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstl hdw1.
      -- by move: hbud; rewrite size_rcons /npq /= addnS addSn.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /= ltnSn.
         ++ by apply: sub_all hfresh => t ht;
              exact: leq_trans ht (leqnSn st).
      -- move=> us hus.
         move: (h (x :: us)); rewrite /= hus => /(_ erefl).
         by rewrite (pre_queries_cons N) /= cat_rcons.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The common COMMIT tail *)

Lemma r_zp_tail (pp : PP) (us : seq N) :
  size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        zpblk (Some pp) true (zpreq 0 zdig us) (s0, s1) ⦄
     (#put zpk := Some (pp, Tl pp padrs (wsigs pp 0 zdig us)) ;;
      #put zsg := Some (wsigs pp 0 zdig us) ;;
      ret (pp, Tl pp padrs (wsigs pp 0 zdig us)))
   ≈ (#put rzp_pk_loc := Some (pp, Tl pp padrs (wsigs pp 0 zdig us)) ;;
      #put rzp_sg_loc := Some (wsigs pp 0 zdig us) ;;
      ret (pp, Tl pp padrs (wsigs pp 0 zdig us)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ zp_inv (s0, s1) ⦄.
Proof.
move=> hus.
eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s0c [hpre3 ->].
case: hpre3 => s0d [hblk ->].
case: hblk => hign hpp hrev htws htgts.
split; first by [].
apply: zp_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists us; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_zp_real :
  perfect IKZ GZM (R_zp ∘ SMPRE_game TF CF l true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ zp_inv).
{ rewrite /zp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zp_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), zpblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/zp_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _; rewrite hrem0 => -[_ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the PCOLLQ pin: SM-PRE's lazy pp sampled here, against G1z's
     eager one *)
  eapply (r_get_rhs_known ppp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv iota.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (zpblk_set_pp pp _ _ _ _ hpre). }
  (* the chains: lhs re-rooted sampling, rhs hidden PQUERY samples *)
  eapply (r_zpchains_spec true pp _ zdig 0 [::]).
  - by rewrite add0n size_zdig.
  - by rewrite all_nseq ltn_predL hw orbT.
  - by [].
  - by rewrite /= (npq_le l zdig size_zdig).
  - by [].
  move=> us hus.
  cbv beta.
  simpl.
  (* PGETPP, then the tail *)
  eapply (r_get_rhs_known ppp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (zpblk_set_rev _ _ _ _ hpre). }
  apply: r_zp_tail.
  by rewrite hus size_zdig.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zp_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  case: pko => [pk|]; last first.
  + (* pre-commitment: Gzmid fails on the getSome assert, R fails
       inside the real PCHECK's phase assert (the gadget) *)
    simpl.
    rewrite (resolve_zp_ck 0 n0).
    eapply (r_get_bind_rhs prv_loc false).
      { move=> s0 s1 [[hinv hrem0] hrem1].
        case/zp_invE: hinv => _ hRP.
        rewrite /rem_inv /= in hrem0 hrem1.
        case: hRP => _ _; rewrite hrem0 => -[_ _ _ [_ hrv]].
        exact: hrv. }
    cbv beta.
    exact: r_fail_bind_rhs.
  + (* committed: mirror Gzmid *)
    simpl.
    eapply r_get_remember_lhs => sgol.
    eapply r_get_remember_rhs => sgov.
    eapply (r_fact (sgov = sgol)).
      { move=> s0 s1 [[[[hinv _] _] h3] h4].
        case/zp_invE: hinv => _ [_ e2 _].
        rewrite /rem_inv /= in h3 h4.
        by rewrite -h3 -h4 e2. }
    move=> e; subst sgov.
    eapply (r_fact (exists us : seq N,
              [/\ sgol = Some (wsigs pk.1 0 zdig us), size us = l
                & pk.2 = Tl pk.1 padrs (wsigs pk.1 0 zdig us)])).
      { move=> s0 s1 [[[[hinv h1] h2] h3] h4].
        case/zp_invE: hinv => _ [_ e2 hmatch].
        rewrite /rem_inv /= in h1 h3.
        rewrite h1 in hmatch.
        case: hmatch => us [hB hpo [husz hpk2] _].
        exists us; split=> //.
        by rewrite -h3 hB. }
    move=> [us [hsgol husz hpk2]].
    rewrite hsgol /=.
    case E0: (wverify pk.1 pk.2 mst sgst); last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[hinv _] _] _] _].
    * case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wsigs pk.1 0 zdig us)%B).
      -- (* COMPRESS: both null *)
         rewrite (negbTE E2).
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[hinv _] _] _] _].
      -- move/negbFE: E2 => E2'.
         rewrite E2' andbT.
         case E3: (zsel' (wdigest pk.1 mst sgst.2)) => [i|]; last first.
         ++ (* no attacked chain: both sides answer true *)
            apply r_ret => s0 s1 hpre; split=> //.
            by case: hpre => [[[[hinv _] _] _] _].
         ++ case E4: (qnth sgst.1 i) => [y|]; last first.
            ** (* dead: the forged signature has l chain values *)
               eapply (r_fact False); last by [].
               move=> s0 s1 _.
               have [hisz _] := @zselP w (wdigest pk.1 mst sgst.2) i E3.
               have hszd : size (wdigest pk.1 mst sgst.2) = l
                 := size_digest_of PP M Hgrind zstar istar
                      pk.1 mst sgst.2.
               have hver : wverify pk.1 pk.2 mst sgst by rewrite E0.
               move: hver; rewrite /verify_sig => /and3P[_ /eqP hsy _].
               have [yy hyy] : exists yy, qnth sgst.1 i = Some yy.
               { by apply: qnth_some; rewrite hsy -hszd. }
               by rewrite hyy in E4.
            ** (* CHAIN MEET: PCHECK answers true = Gzmid's true *)
               simpl.
               rewrite (resolve_zp_ck i
                 (chain (cf pk.1 i) y
                    (nth 0 (wdigest pk.1 mst sgst.2) i)
                    (w.-2 - nth 0 (wdigest pk.1 mst sgst.2) i))).
               eapply (r_get_bind_rhs prv_loc true).
                 { move=> s0 s1 [[[[hinv h1] h2] h3] h4].
                   case/zp_invE: hinv => _ [_ _ hmatch].
                   rewrite /rem_inv /= in h1.
                   rewrite h1 in hmatch.
                   by case: hmatch => uss [_ _ _ [_ _ hrv]]. }
               cbv beta.
               eapply r_bind_assertD_rhs; first by [].
               move=> _.
               eapply r_get_remember_rhs => tg.
               eapply (r_fact (exists us2 : seq N,
                 [/\ wsigs pk.1 0 zdig us2 = wsigs pk.1 0 zdig us,
                     size us2 = l
                   & tg = qmap_from 0
                       [seq wq' q | q <- zpreq 0 zdig us2]])).
                 { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
                   case/zp_invE: hinv => _ [_ e2 hmatch].
                   rewrite /rem_inv /= in h1 h3 h5.
                   rewrite h1 in hmatch.
                   case: hmatch => us2 [hB _ [husz2 _] [htg _ _]].
                   exists us2; split=> //; last by rewrite -h5 htg.
                   have : Some (wsigs pk.1 0 zdig us2)
                          = Some (wsigs pk.1 0 zdig us).
                   { by rewrite -hB h3. }
                   by case. }
               move=> [us2 [hsgEq husz2 htg]].
               have hver : wverify pk.1 pk.2 mst sgst by rewrite E0.
               rewrite hpk2 -hsgEq in hver.
               have hends : wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                            = wsigs pk.1 0 zdig us2.
               { by rewrite hsgEq; apply/eqP. }
               have [ui [hqn hfeq]] :=
                 zpre_win pk.1 us2 mst sgst i y husz2 hver hends E3 E4.
               have hgetm : getm tg i = Some (wtw (i, w.-2), ui).
               { rewrite htg.
                 have := qmap_from_get 0
                   [seq wq' q | q <- zpreq 0 zdig us2] i.
                 rewrite add0n => ->.
                 by rewrite qnth_map hqn. }
               rewrite hgetm.
               eapply (r_get_rhs_known ppp_loc (Some pk.1)).
                 { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
                   case/zp_invE: hinv => _ [_ _ hmatch].
                   rewrite /rem_inv /= in h1.
                   rewrite h1 in hmatch.
                   by case: hmatch => uss [_ hpo _ _]. }
               simpl.
               rewrite !(th_eval_wtw PP N F dPP dN zstar istar).
               rewrite hfeq eqxx.
               apply r_ret => s0 s1 hpre; split=> //.
               by case: hpre => [[[[[hinv _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence (consumes [Hdeg]) *)

Lemma R_zp_ideal (Hdeg : S_wn != (l * w.-1)%N) :
  perfect IKZ (G1Z false) (R_zp ∘ SMPRE_game TF CF l false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ zp_inv).
{ rewrite /zp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (G1z's COMMIT is verbatim
     Gzmid's; the oracle bodies and loop specs are b-independent) *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/zp_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), zpblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/zp_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _; rewrite hrem0 => -[_ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the PCOLLQ pin: SM-PRE's lazy pp sampled here, against G1z's
     eager one *)
  eapply (r_get_rhs_known ppp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv iota.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (zpblk_set_pp pp _ _ _ _ hpre). }
  (* the chains: lhs re-rooted sampling, rhs hidden PQUERY samples *)
  eapply (r_zpchains_spec false pp _ zdig 0 [::]).
  - by rewrite add0n size_zdig.
  - by rewrite all_nseq ltn_predL hw orbT.
  - by [].
  - by rewrite /= (npq_le l zdig size_zdig).
  - by [].
  move=> us hus.
  cbv beta.
  simpl.
  (* PGETPP, then the tail *)
  eapply (r_get_rhs_known ppp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (zpblk_set_rev _ _ _ _ hpre). }
  apply: r_zp_tail.
  by rewrite hus size_zdig.
- (* KFORGE: lhs is [ret false]; everything on the rhs is
     one-sided *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_rhs => pko'.
  case: pko' => [pk|]; last first.
  + (* pre-commitment: ideal PCHECK answers false *)
    simpl.
    rewrite (resolve_zp_ck_false 0 n0).
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [hinv _].
  + simpl.
    eapply r_get_remember_rhs => sgov.
    eapply (r_fact (exists us : seq N,
              sgov = Some (wsigs pk.1 0 zdig us))).
      { move=> s0 s1 [[hinv h1] h2].
        case/zp_invE: hinv => _ [e1 e2 hmatch].
        rewrite /rem_inv /= in h1 h2.
        rewrite -e1 h1 in hmatch.
        case: hmatch => us [hB _ _ _].
        exists us.
        by rewrite -h2 e2 hB. }
    move=> [us hsgov].
    rewrite hsgov /=.
    case E0: (wverify pk.1 pk.2 mst sgst); last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[hinv _] _].
    * case E2: ((wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1
                 != wsigs pk.1 0 zdig us)%B).
      -- apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[hinv _] _].
      -- case E3: (zsel' (wdigest pk.1 mst sgst.2)) => [i|]; last first.
         ++ (* dead branch: a valid digest has an attacked chain
               (zsel_dead + Hdeg) *)
            eapply (r_fact False); last by [].
            move=> s0 s1 _.
            have hver : wverify pk.1 pk.2 mst sgst by rewrite E0.
            move: hver; rewrite /verify_sig => /and3P[hvd _ _].
            exact: (@zsel_dead w l S_wn (wdigest pk.1 mst sgst.2)
                      Hdeg hvd
                      (size_digest_of PP M Hgrind zstar istar
                         pk.1 mst sgst.2) E3).
         ++ case E4: (qnth sgst.1 i) => [y|]; last first.
            ** apply r_ret => s0 s1 hpre; split=> //.
               by case: hpre => [[hinv _] _].
            ** (* CHAIN MEET: ideal PCHECK answers false, as does
                  G1z-ideal *)
               simpl.
               rewrite (resolve_zp_ck_false i
                 (chain (cf pk.1 i) y
                    (nth 0 (wdigest pk.1 mst sgst.2) i)
                    (w.-2 - nth 0 (wdigest pk.1 mst sgst.2) i))).
               apply r_ret => s0 s1 hpre; split=> //.
               by case: hpre => [[hinv _] _].
Qed.

End ZeroChainHop.
