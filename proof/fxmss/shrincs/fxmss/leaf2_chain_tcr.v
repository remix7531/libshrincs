(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.leaf2_chain_tcr

    The SM-TCR(F) sub-bound [Glmid2 -> Glmid3] in the second FXMSS leaf
    hop. It lifts the single-instance WOTS chain reduction to all leaves
    and follows the compression-hop simulation with these substitutions:
      - target THF  : Tf (chain F)  instead of Tpk (pk compression);
      - collection  : {Tl, Htree, Hgrind} (the pk is now a COLLQ-Tl, the chains
        are TQUERY targets);
      - null        : tcr_decision (the chain-TCR F-collision) instead of the
        compress collision;
      - target set  : the per-leaf chains, concatenated over all leaves
        (qmap_from re-indexing); budget qF = n_max * tcr_budget l w.

    The reduction [R_ctcr_leaf] uses the static gate [lct_v], the
    slot-keyed digit [l_rrdigS], and a budget-guarded LSIGN. Its
    F1-augmented collection [CFl_leaf], resolve/conversion bridges,
    CHAIN-TCR-specific bridges ([th_eval_chtw], [lcoord_chtw],
    [chtw_neq_of_coord], ...), and the state-preserving loop specs
    ([r_lctcollq_known], [r_lctgrind_spec]) support its real and ideal
    perfect simulations. Virtual leaves commit no F-chain targets, and
    [tcr_allmax_none] shows that the classifier does not fire on them, so
    the multi-target invariant tracks only signed-population blocks. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From Sec.lib Require Import prelude math.bin_tree math.merkle math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme games.thf games.smtcr toolkit.sample_seq.
From Sec.lib Require Import toolkit.relational_rules chain.core wots.games wots.analysis wots.tcr_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games wotsc.analysis
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop
  fxmss.leaf_reduction fxmss.leaf_km fxmss.leaf2_common fxmss.leaf2_games.
From mathcomp Require Import all_boot all_order reals.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section leaf2_chain_tcr.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same data-only section context as [fxmss.leaf2_games]. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (Hh : (h_sf <= 255)%N).
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (n0 : N) (d0 : D).

(* ------------------------------------------------------------------ *)
(** ** Shorthands.  [lcoord] (= adrs_keypair o decode) from leaf2_games. *)

Local Notation lcoord t := (@leaf_km.lcoord w l t).
Local Notation IKM  := (@I_MIW_km w l PP N D).

(** The leaf SM-TCR(F) target THF: F at the chain address (decoded tweak). *)
Local Notation TFl := (Tf PP N F dPP dN).

(** The CHAIN-TCR collection (mirror of CPl_leaf with the target swapped to
    [TFl] and the [inl] member being the pk-compression [Tl] -- so the pk is a
    COLLQ-Tl call rather than a TQUERY target).  Exposes Tl ([inl]), Htree
    ([inr (inl _)], LCOLLQ.inl), Hgrind ([inr (inr _)], grind + LCOLLQ.inr). *)
Definition CFl_leaf : thf_coll TFl :=
  Build_thf_coll TFl adrs_sf_ch
    (('list N) ∐ ((N × N) ∐ (D × 'nat)))
    (N ∐ (N ∐ 'nat))
    (fun pp t x =>
       match x with
       | inl xs => inl (Tl pp (decode_tweak t) xs)
       | inr (inl xy) => inr (inl (Htree pp (decode_tweak t) xy))
       | inr (inr dc) => inr (inr (Hgrind pp (decode_tweak t) dc))
       end).

Local Notation IMP := (I_SMTCR TFl CFl_leaf).

(** qF = n_max committed leaves, each with up to [tcr_budget l w] chain targets. *)
Local Notation qF := (n_max * tcr_budget l w)%N.

(** Coordinate-level tweaks. *)
Local Notation gtw_of t :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (lcoord t))).
Local Notation grtw_of t :=
  (@encode_adrs l w (@shrincs_fxmss_wots_grind_adrs l w (lcoord t))).
Local Notation chtw_of zi i k :=
  (@encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w zi i k)).

Local Notation gprp := (@grind_prp w l S_wn).

(** Inlined re-root digit / pk (= leaf2_games.rr_digit / rr_pk at zi = lcoord t). *)
Definition l_rrdig (zi : nat * nat) (pp : PP) (md : D) : seq nat :=
  match find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md with
  | Some c => digest_of PP D Hgrind zi.1 zi.2 pp md c
  | None => nseq l w.-1
  end.

Definition l_rrpk (zi : nat * nat) (pp : PP) (md : D) (sg : seq N) : N :=
  Tl pp (shrincs_fxmss_wots_pk_adrs zi)
     (complete_ends PP N F zi.1 zi.2 pp (l_rrdig zi pp md) sg).

(** The SLOT-KEYED static digit / pk (= leaf2_games.rr_digitS / rr_pkS at
    zi = lcoord t). The [j < q_s] budget wrapper is absent (every
    committed leaf carries a real find_ctr-conditional digest at EVERY slot);
    the [j] parameter is kept for interface stability but is vestigial. *)
Definition l_rrdigS (zi : nat * nat) (pp : PP) (md : D) (j : nat) : seq nat :=
  l_rrdig zi pp md.

Definition l_rrpkS (zi : nat * nat) (pp : PP) (md : D) (j : nat)
    (sg : seq N) : N :=
  Tl pp (shrincs_fxmss_wots_pk_adrs zi)
     (complete_ends PP N F zi.1 zi.2 pp (l_rrdigS zi pp md j) sg).

(* ------------------------------------------------------------------ *)
(** ** Import opsigs. *)

Definition lct_cqo : opsig := (COLLQ, (tc_T CFl_leaf × tc_M CFl_leaf, tc_N CFl_leaf)).
Definition lct_tqo : opsig := (TQUERY, (th_T TFl × th_M TFl, th_N TFl)).
Definition lct_gpo : opsig := (GETPP, ('unit, th_PP TFl)).
Definition lct_cko : opsig := (CHECK, ('nat × th_M TFl, 'bool)).

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed loops (grind via COLLQ-Hgrind; chains via
    TQUERY-F; pk via COLLQ-Tl). *)

(** Grinding loop: one COLLQ (Hgrind member, [inr (inr _)]) per counter. *)
Fixpoint lct_grind (zi : nat * nat) (md : D) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lct_cqo (encode_adrs (shrincs_fxmss_wots_grind_adrs zi), inr (inr (md, c)))
        (λ r, hs ← lct_grind zi md cs' ;;
              ret ((if r is inr (inr h) then h else 0) :: hs))
  end.

#[local] Instance lct_grind_valid (L : Locations) zi md cs :
  ValidCode L IMP (lct_grind zi md cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lct_cqo; fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n] steps,
    one TQUERY (F target) per step. *)
Fixpoint lct_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr lct_tqo (encode_adrs (shrincs_fxmss_wots_chain_adrs zi i k), x)
         (λ y, lct_walk zi i k.+1 n' y)
  else ret x.

#[local] Instance lct_walk_valid (L : Locations) zi i k n x :
  ValidCode L IMP (lct_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lct_tqo; fmap_solve.
  move=> y; exact: IH.
Qed.

(** All chains: per chain, sample root LOCALLY, one TQUERY F-step to the
    signature position (positive digit), walk upward; returns (sig values,
    completed ends). *)
Fixpoint lct_chains (zi : nat * nat) (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1
           then opr lct_tqo (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st d'), u) (λ y, ret y)
           else ret u) ;;
      e ← lct_walk zi st d (w.-1 - d) s ;;
      '(ss, es) ← lct_chains zi st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance lct_chains_valid (L : Locations) zi st ds :
  ValidCode L IMP (lct_chains zi st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by rewrite /lct_tqo; fmap_solve.
    move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: lct_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(** The bounded grind search on the answer list (= scheme [find_ctr]). *)
Definition lct_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 c_max) hs | gprp ch.2].

(** The re-root digit vector reconstructed from the grind answers. *)
Definition lct_digit (hs : seq nat) : seq nat :=
  match lct_pick hs with
  | Some ch => digits_w w l ch.2
  | None => nseq l w.-1
  end.

(** The slot-keyed commit digit (= rr_digitS reconstructed at slot [j]).
    The [j < q_s] budget wrapper is absent. *)
Definition lct_digitS (j : nat) (hs : seq nat) : seq nat :=
  lct_digit hs.

(* ------------------------------------------------------------------ *)
(** ** The reduction package R_ctcr_leaf : package IMP IKM. *)

Definition rct_rev_loc  := mkloc 600 (false : bool).
Definition rct_tws_loc  := mkloc 601 ([::] : seq adrs_sf_ch).
Definition rct_tgts_loc :=
  mkloc 602 (emptym :
    {fmap nat -> (adrs_sf_ch × (('list N × D) × (('option 'nat) × 'nat)))}).
Definition rct_slog_loc := mkloc 603 ([::] : seq nat).
Definition rct_pp_loc   := mkloc 604 (None : option PP).
Definition rct_cnt_loc  := mkloc 605 (0 : nat).

Local Notation RCTLocs :=
  [fmap rct_rev_loc ; rct_tws_loc ; rct_tgts_loc ; rct_slog_loc ;
        rct_pp_loc ; rct_cnt_loc ].

(** The LCHECK pure decision (M1a S-form, slog-FREE): the common Glmid2 prefix
    [v] (verokS && gateS && ~grind_hitS && fcv==rcvS); the CHAIN-TCR
    discriminant is [isSome (tcr_decision ...)]. *)
Definition lct_v (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (copt : 'option 'nat) (j : nat)
    (mw : D × (('list N) × 'nat)) : bool :=
  let fdv := digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2 in
  let rdg := l_rrdigS (lcoord t0) pp md0 j in
  let vchecks := shrincs_fxmss_wots_checks PP N D Hgrind S_wn pp (lcoord t0) mw.1 mw.2 in
  let verok := (vchecks
                && (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind pp (lcoord t0) mw.1 mw.2
                    == l_rrpkS (lcoord t0) pp md0 j sg))%B in
  let gate := (~~ isSome copt || (mw.1 != md0))%B in
  let ghit := (isSome copt && (fdv == rdg))%B in
  let fcv := complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp fdv mw.2.1 in
  let rcv := complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp rdg sg in
  (verok && gate && ~~ ghit && (fcv == rcv))%B.

(** The chain-TCR decision at the leaf coordinate (= P_gm3S's null
    discriminant, at the slot-keyed digit). *)
Definition lct_dec (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) : option (nat * N) :=
  let fdv := digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2 in
  let rdg := l_rrdigS (lcoord t0) pp md0 j in
  tcr_decision PP N (Fw PP N F (lcoord t0).1 (lcoord t0).2) l w pp rdg fdv sg mw.2.1.

Definition R_ctcr_leaf : package IMP IKM.
Proof.
notypeclasses refine [package RCTLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) {
      revealed ← get rct_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get rct_tws_loc ;;
      #assert (size tws < n_max)%N ;;
      #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
      _ ← opr lct_cqo (grtw_of t, inr (inr (md, 0))) (λ r, ret r) ;;
      hs ← lct_grind (lcoord t) md (iota 0 c_max) ;;
      cnt ← get rct_cnt_loc ;;
      '(sg, ends) ← lct_chains (lcoord t) 0 (lct_digitS (size tws) hs) ;;
      root ← opr lct_cqo (gtw_of t, inl ends)
               (λ r, ret (match r with inl y => y | _ => n0 end)) ;;
      tgts ← get rct_tgts_loc ;;
      #put rct_tgts_loc := setm tgts (size tws)
                             (t, ((sg, md), (omap fst (lct_pick hs), cnt))) ;;
      #put rct_tws_loc := rcons tws t ;;
      #put rct_cnt_loc := (cnt + total_query_count w (lct_digitS (size tws) hs))%N ;;
      ret root
    } ;
    [ LGETPP ] : { 'unit ~> PP } (_) {
      pp ← opr lct_gpo Datatypes.tt (λ p, ret p) ;;
      #put rct_pp_loc := Some pp ;;
      #put rct_rev_loc := true ;;
      ret pp
    } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      revealed ← get rct_rev_loc ;;
      #assert revealed ;;
      tgts ← get rct_tgts_loc ;;
      match getm tgts j with
      | Some (t0, ((sg, md0), (copt, base))) =>
          ppo ← get rct_pp_loc ;;
          pp ← match ppo with
               | Some pp => ret pp
               | None => pp ← dPP ;; #put rct_pp_loc := Some pp ;; ret pp
               end ;;
          match lct_dec pp t0 sg md0 j mw with
          | Some (jc, u) =>
              if lct_v pp t0 sg md0 copt j mw
              then opr lct_cko ((base + jc)%N, u) (λ ans, ret ans)
              else ret false
          | None => ret (lct_v pp t0 sg md0 copt j mw)
          end
      | None => ret false
      end
    } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) {
      slog ← get rct_slog_loc ;;
      #assert (j \notin slog) ;;
      tgts ← get rct_tgts_loc ;;
      match getm tgts j with
      | Some (t0, ((sg, md0), (copt, base))) =>
          match copt with
          | Some c => #put rct_slog_loc := rcons slog j ;; ret (Some (sg, c))
          | None => ret None
          end
      | None => ret None
      end
    } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      match x with
      | inl xy =>
          opr lct_cqo (t, inr (inl xy))
            (λ r, ret (match r with inr (inl h) => inl h | _ => inl n0 end))
      | inr dc =>
          opr lct_cqo (t, inr (inr dc))
            (λ r, ret (match r with inr (inr g) => inr g | _ => inr 0 end))
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
          - eapply valid_opr; first by rewrite /lct_cqo; fmap_solve.
            move=> r; apply valid_ret.
          - eapply valid_opr; first by rewrite /lct_cqo; fmap_solve.
            move=> r; apply valid_ret. } }
      { (* LSIGN *)
        intro j.
        eapply valid_getr; first by fmap_solve. move=> slog.
        eapply valid_assertD => _.
        eapply valid_getr; first by fmap_solve. move=> tgts.
        case: (getm tgts j) => [[t0 [[sg md0] [copt base]]]|]; last by apply valid_ret.
        case: copt => [c|]; last by apply valid_ret.
        eapply valid_putr; first by fmap_solve. apply valid_ret. } }
    { (* LCHECK *)
      intros [j mw].
      eapply valid_getr; first by fmap_solve. move=> revealed.
      eapply valid_assertD => _.
      eapply valid_getr; first by fmap_solve. move=> tgts.
      case: (getm tgts j) => [[t0 [[sg md0] [copt base]]]|]; last by apply valid_ret.
      eapply valid_getr; first by fmap_solve. move=> ppo.
      eapply valid_bind.
        case: ppo => [pp|]; first by apply valid_ret.
        eapply valid_bind; first by eapply valid_scheme, prog_valid.
        move=> pp; eapply valid_putr; first by fmap_solve.
        apply valid_ret.
      move=> pp.
      case: (lct_dec pp t0 sg md0 j mw) => [[jc u]|]; last by apply valid_ret.
      case: ifP => _; last by apply valid_ret.
      eapply valid_opr; first by rewrite /lct_cko; fmap_solve.
      move=> ans; apply valid_ret. } }
  { (* LGETPP *)
    intro u.
    eapply valid_opr; first by rewrite /lct_gpo; fmap_solve.
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
    eapply valid_opr; first by rewrite /lct_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> _.
  eapply valid_bind; first exact: lct_grind_valid. move=> hs.
  eapply valid_getr; first by fmap_solve. move=> cnt.
  eapply valid_bind; first exact: lct_chains_valid. move=> [sg ends].
  eapply valid_bind.
    eapply valid_opr; first by rewrite /lct_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> root.
  eapply valid_getr; first by fmap_solve. move=> tgts.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve. apply valid_ret. }
Defined.


(* ------------------------------------------------------------------ *)
(** ** The CHAIN-TCR sub-bound (ladder step Glmid2 -> Glmid3). *)

Local Notation GM2 := (Glmid2 PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation GM3 := (Glmid3 PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation SMB b := (SMTCR_game TFl CFl_leaf qF b).

Local Notation Lpp := (miw_pp_loc PP).
Local Notation Ltg := (@mkm_tgts_loc w l N D).
Local Notation Ltw := (@miw_tws_loc w l).
Local Notation Lrv := miw_rev_loc.
Local Notation Lsl := miw_slog_loc.
Local Notation Spp := (tcr_pp_loc TFl).
Local Notation Stg := (tcr_tgts_loc TFl).
Local Notation Stw := (tcr_tws_loc TFl).
Local Notation Srv := tcr_rev_loc.

Local Notation FWl zi := (Fw PP N F zi.1 zi.2).
Local Notation cfWl zi := (Sec.lib.chain.core.chainf PP N (FWl zi)).
Local Notation wsigs zi := (sigs_of PP N (FWl zi)).
Local Notation wends zi := (ends_of PP N (FWl zi) w).
Local Notation lfind zi pp md :=
  (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md).
Local Notation lcompl zi pp ds sg := (complete_ends PP N F zi.1 zi.2 pp ds sg).
Local Notation lcq zi pp ds sg := (commit_queries PP N (FWl zi) w pp 0 ds sg).

(* ================================================================== *)
(** ** Resolve equations for the SM-TCR(F) oracles. *)

Lemma resolve_lct_cq (b : bool) (t : tc_T CFl_leaf) (x : tc_M CFl_leaf) :
  resolve (SMB b) lct_cqo (t, x) =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   ret (tc_eval CFl_leaf pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lct_tq (b : bool) (t : th_T TFl) (x : th_M TFl) :
  resolve (SMB b) lct_tqo (t, x) =
  (revealed ← get Srv ;;
   #assert ~~ revealed ;;
   tws ← get Stw ;;
   #assert (size tws < qF)%N ;;
   #assert (t \notin tws) ;;
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

Lemma resolve_lct_gp (b : bool) (u : unit) :
  resolve (SMB b) lct_gpo u =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   #put Srv := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lct_ck (j : nat) (x : th_M TFl) :
  resolve (SMB true) lct_cko (j, x) =
  (revealed ← get Srv ;;
   #assert revealed ;;
   tgts ← get Stg ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get Spp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
            end ;;
       ret ((x != m0) && (th_eval TFl pp t0 x == th_eval TFl pp t0 m0))
   | None => ret false
   end).
Proof. by simplify_linking. Qed.

Lemma resolve_lct_ck_false (j : nat) (x : th_M TFl) :
  resolve (SMB false) lct_cko (j, x) = ret false.
Proof. by simplify_linking. Qed.

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
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments lct_pick : simpl never.
#[local] Arguments l_rrdig : simpl never.
#[local] Arguments tcr_decision : simpl never.
#[local] Arguments commit_queries : simpl never.

(* ================================================================== *)
(** ** Conversion bridges (canonical tweaks compute). *)

Lemma collq_H_E (pp : PP) (zi : nat * nat) (md : D) (c : nat) :
  (if tc_eval CFl_leaf pp (encode_adrs (shrincs_fxmss_wots_grind_adrs zi)) (inr (inr (md, c)))
      is inr (inr h) then h else 0)
  = Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c).
Proof. by rewrite /tc_eval /CFl_leaf decode_tweakK. Qed.

Lemma collq_Tl_E (pp : PP) (zi : nat * nat) (ys : seq N) :
  (match tc_eval CFl_leaf pp (encode_adrs (shrincs_fxmss_wots_pk_adrs zi)) (inl ys)
      with inl y => y | _ => n0 end)
  = Tl pp (shrincs_fxmss_wots_pk_adrs zi) ys.
Proof. by rewrite /tc_eval /CFl_leaf decode_tweakK. Qed.

(** The picked grinding result on the honest answer list IS the scheme's
    [find_ctr] re-rooted at the answers. *)
Lemma lct_zip_filter (f : nat -> nat) (P : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | P ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | P (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (P (f c)) => /=; [|exact: IH].
Qed.

Lemma lct_pick_map (pp : PP) (zi : nat * nat) (md : D) :
  lct_pick [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = omap (fun c => (c, Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c))) (lfind zi pp md).
Proof.
rewrite /lct_pick lct_zip_filter /find_ctr.
have hf :
  [seq c <- iota 0 c_max
   | @grind_prp w l S_wn (Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c))]
  = [seq c <- iota 0 c_max | good_ctr PP D Hgrind S_wn zi.1 zi.2 pp md c].
  by apply: eq_filter => c;
     rewrite /grind_prp /good_ctr /valid_digest /digest_of.
by rewrite hf.
Qed.

Lemma lct_digit_E (pp : PP) (zi : nat * nat) (md : D) :
  lct_digit [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = l_rrdig zi pp md.
Proof.
rewrite /lct_digit lct_pick_map /l_rrdig.
by case: (lfind zi pp md) => [c|].
Qed.

Lemma lct_copt_E (pp : PP) (zi : nat * nat) (md : D) :
  omap fst (lct_pick [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max])
  = lfind zi pp md.
Proof. by rewrite lct_pick_map; case: (lfind zi pp md) => [c|]. Qed.

(* ================================================================== *)
(** ** Reusable bridges for the multi-target chain commit (NEW, shared).

    These are the CHAIN-TCR-specific analogues of Leaf2Compress's [collq_F_E]:
    the F-chain evaluations now flow through TQUERY (F is the SM-TCR target),
    so the bridge is on [th_eval TFl] (not [tc_eval]).  The coordinate helpers
    turn the game's coordinate-level LCOMMIT freshness [gtw_of t \notin map
    gtw_of tws] into cross-leaf chain-tweak distinctness (F2 at the chain
    level; [l2_chain_inj] is the leaf-PATH version, this is the generic-B
    coordinate version). *)

(** TQUERY answer at a chain tweak IS the leaf's chain hash [FWl]. *)
Lemma th_eval_chtw (pp : PP) (zi : nat * nat) (i k : nat) (x : N) :
  th_eval TFl pp (chtw_of zi i k) x = FWl zi pp (i, k) x.
Proof. by rewrite (th_evalE_Tf PP N F dPP dN). Qed.

(** The leaf coordinate of an encoded chain tweak is its anchor. *)
Lemma lcoord_chtw (zi : nat * nat) (i k : nat) :
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  lcoord (chtw_of zi i k) = zi.
Proof. exact: l2_lcoord_chain. Qed.

(** The leaf coordinate of an encoded pk-anchor tweak is its anchor. *)
Lemma lcoord_pkadr (zi : nat * nat) :
  anchor_bounded zi -> lcoord (encode_adrs (shrincs_fxmss_wots_pk_adrs zi)) = zi.
Proof. exact: l2_lcoord_pk. Qed.

(** Cross-leaf chain-tweak distinctness from coordinate distinctness: if two
    leaf coordinates differ, all their chain tweaks differ. *)
Lemma chtw_neq_of_coord (zi zj : nat * nat) (i k i' k' : nat) :
  anchor_bounded zi -> anchor_bounded zj ->
  component_bounded l i -> component_bounded w.-1 k ->
  component_bounded l i' -> component_bounded w.-1 k' ->
  zi <> zj -> chtw_of zi i k <> chtw_of zj i' k'.
Proof.
move=> hzi hzj hi hk hi' hk' hne /encode_adrs_inj he.
have [e1 e2 _ _] :=
  @shrincs_fxmss_wots_chain_adrs_inj l w zi.1 zi.2 i k zj.1 zj.2 i' k'
    hzi hzj hi hk hi' hk' he.
by apply: hne; rewrite [zi]surjective_pairing [zj]surjective_pairing e1 e2.
Qed.

(** A chain tweak at coordinate [zi] is fresh w.r.t. any tweak list all of
    whose entries have a coordinate different from [zi] (cross-leaf freshness). *)
Lemma chtw_notin_coord (zi : nat * nat) (i k : nat) (tws : seq adrs_sf_ch) :
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  all (fun tw => lcoord tw != zi) tws -> chtw_of zi i k \notin tws.
Proof.
move=> hzi hi hk /allP h; apply/negP => hin.
by move: (h _ hin); rewrite (lcoord_chtw zi i k hzi hi hk) eqxx.
Qed.

(* ================================================================== *)
(** ** Stepping one linked COLLQ (pp pinned) + the grind loop (state-
    preserving, so generic over [pre]; ported verbatim from
    leaf2_compress.r_lcollq_known / r_lcgrind_spec at the CHAIN-TCR collection). *)

Lemma r_lctcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CFl_leaf) (x : tc_M CFl_leaf) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : tc_N CFl_leaf -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CFl_leaf pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) lct_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lct_cq b t x).
eapply (r_get_bind_rhs Spp (Some pp)); first exact: hpp.
cbv beta iota.
exact: h.
Qed.

Lemma r_lctgrind_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (md : D) (cs : seq nat) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lct_grind zi md cs) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lctcollq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(* ================================================================== *)
(** ** Pure layer: the per-leaf chain re-tagging.

    Each leaf commits [total_query_count w ds] CHAIN targets (F is the SM-TCR target);
    the abstract [commit_queries] entries (over (chain,position) pairs) are
    re-tagged into ENCODED chain tweaks [chtw_of] at the leaf coordinate. *)

Local Notation ptcr := (tcr_budget l w).

Definition lwq (zi : nat * nat) (q : (nat * nat) * N) : (adrs_sf_ch × N) :=
  (chtw_of zi q.1.1 q.1.2, q.2).

Definition absQ_bounded (Q : seq ((nat * nat) * N)) : bool :=
  all (fun ik => ((ik.1 < l)%N && (ik.2 < w.-1)%N)) (unzip1 Q).

Lemma absQ_bounded_rcons (Q : seq ((nat * nat) * N)) i k x :
  absQ_bounded Q -> (i < l)%N -> (k < w.-1)%N ->
  absQ_bounded (rcons Q ((i, k), x)).
Proof.
by rewrite /absQ_bounded /unzip1 map_rcons all_rcons => -> -> ->.
Qed.

Lemma absQ_bounded_walk (pp : PP) (zi : nat * nat) i k n x :
  (i < l)%N -> (k + n <= w.-1)%N ->
  absQ_bounded (walkq PP N (FWl zi) pp i k n x).
Proof.
move=> hi hkn; rewrite /absQ_bounded; apply/allP => ik hik.
apply/andP; split.
- move: (allP (walkq_tweak1 PP N (FWl zi) pp i k n x) _ hik).
  by move/eqP=> ->.
- exact: (allP (walkq_tweak2 PP N (FWl zi) pp i k n x w.-1 hkn) _ hik).
Qed.

Lemma absQ_bounded_cat (Q Q' : seq ((nat * nat) * N)) :
  absQ_bounded Q -> absQ_bounded Q' -> absQ_bounded (Q ++ Q').
Proof.
by rewrite /absQ_bounded /unzip1 map_cat all_cat => -> ->.
Qed.

Lemma absQ_bounded_chain (pp : PP) (zi : nat * nat) i d u :
  (i < l)%N -> (d < w)%N ->
  absQ_bounded (chain_queries PP N (FWl zi) w pp i d u).
Proof.
move=> hi; case: d => [|d'] hd.
- have hkn0 : (0 + (w.-1 - 0) <= w.-1)%N by rewrite add0n subn0.
  rewrite /chain_queries /=.
  exact: (absQ_bounded_walk pp zi i 0 (w.-1 - 0) u hi hkn0).
- have hw0 : (0 < w)%N := leq_trans (ltn0Sn d') (ltnW hd).
  have hdw1 : (d'.+1 <= w.-1)%N by rewrite -ltnS (prednK hw0).
  have hkn1 : (d'.+1 + (w.-1 - d'.+1) <= w.-1)%N by rewrite subnKC.
  apply: absQ_bounded_cat.
  + by rewrite /absQ_bounded /= hi hdw1.
  + exact: (absQ_bounded_walk pp zi i d'.+1 (w.-1 - d'.+1)
      (FWl zi pp (i, d') u) hi hkn1).
Qed.

Lemma absQ_bounded_commit (pp : PP) (zi : nat * nat) ds :
  forall st us,
  (st + size ds <= l)%N ->
  all (fun d => (d < w)%N) ds ->
  size us = size ds ->
  absQ_bounded (commit_queries PP N (FWl zi) w pp st ds us).
Proof.
elim: ds => [|d ds IH] st [|u us] //= hst /andP[hd hds] [hus].
rewrite (commit_queries_cons PP N (FWl zi)); apply: absQ_bounded_cat.
- apply: absQ_bounded_chain => //.
  by apply: leq_trans hst; rewrite addnS ltnS leq_addr.
- apply: IH => //.
  by move: hst; rewrite addnS.
Qed.

Lemma unzip1_lwq (zi : nat * nat) (Q : seq ((nat * nat) * N)) :
  unzip1 [seq lwq zi q | q <- Q] = [seq chtw_of zi q.1.1 q.1.2 | q <- Q].
Proof. by rewrite /unzip1 -map_comp. Qed.

Lemma th_eval_lwq (pp : PP) (zi : nat * nat) (q : (nat * nat) * N) :
  th_eval TFl pp (lwq zi q).1 (lwq zi q).2 = FWl zi pp q.1 q.2.
Proof. by rewrite /lwq /= th_eval_chtw -surjective_pairing. Qed.

(** Within-leaf freshness: a new (i,k) target distinct from the leaf's own
    committed chain positions. *)
Lemma lwq_notin_self (zi : nat * nat) (i k : nat)
    (absQ : seq ((nat * nat) * N)) :
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  absQ_bounded absQ ->
  (i, k) \notin unzip1 absQ ->
  chtw_of zi i k \notin unzip1 [seq lwq zi q | q <- absQ].
Proof.
rewrite unzip1_lwq => hzi hi hk /allP hbounds hni; apply/negP => /mapP[q hq].
have hqmem : q.1 \in unzip1 absQ.
  by apply/mapP; exists q.
case/andP: (hbounds _ hqmem) => hqi hqk.
move/encode_adrs_inj => he.
have [_ _ ei ek] :=
  @shrincs_fxmss_wots_chain_adrs_inj l w zi.1 zi.2 i k zi.1 zi.2 q.1.1 q.1.2
    hzi hzi hi hk (component_bounded_lt l q.1.1 hqi)
    (component_bounded_lt w.-1 q.1.2 hqk) he.
move/negP: hni; apply; apply/mapP; exists q => //.
by rewrite [q.1]surjective_pairing -ei -ek.
Qed.

(** Cross-leaf + within-leaf freshness of a new chain tweak. *)
Lemma lwq_notin (zi : nat * nat) (i k : nat) (Qpre : seq (adrs_sf_ch × N))
    (absQ : seq ((nat * nat) * N)) :
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  absQ_bounded absQ ->
  all (fun tw => lcoord tw != zi) (unzip1 Qpre) ->
  (i, k) \notin unzip1 absQ ->
  chtw_of zi i k \notin unzip1 (Qpre ++ [seq lwq zi q | q <- absQ]).
Proof.
move=> hzi hi hk hb hpre hself.
rewrite /unzip1 map_cat mem_cat negb_or; apply/andP; split.
- exact: (chtw_notin_coord zi i k _ hzi hi hk hpre).
- exact: (lwq_notin_self zi i k absQ hzi hi hk hb hself).
Qed.

(** Size of the chain commit list of one leaf. *)
Lemma size_lcq (zi : nat * nat) pp (st : nat) (ds : seq nat) (us : seq N) :
  size us = size ds ->
  size (commit_queries PP N (FWl zi) w pp st ds us) = total_query_count w ds.
Proof.
elim: ds st us => [|d ds IH] st [|u us] //= [hsz].
by rewrite commit_queries_cons size_cat size_chain_queries IH.
Qed.

Lemma size_lwqQ (zi : nat * nat) (Qpre : seq (adrs_sf_ch × N))
    (absQ : seq ((nat * nat) * N)) :
  size (Qpre ++ [seq lwq zi q | q <- absQ]) = size Qpre + size absQ.
Proof. by rewrite size_cat size_map. Qed.

(** [gtw_of] is injective on the leaf coordinate. *)
Lemma gtw_lcoord (t x : adrs_sf_ch) : gtw_of t = gtw_of x -> lcoord t = lcoord x.
Proof.
move/encode_adrs_inj => he.
have [e1 e2] := @shrincs_fxmss_wots_pk_adrs_inj l w (lcoord t).1 (lcoord t).2
  (lcoord x).1 (lcoord x).2 (l2_lcoord_bounded t) (l2_lcoord_bounded x) he.
by rewrite [lcoord t]surjective_pairing [lcoord x]surjective_pairing e1 e2.
Qed.

Lemma gtw_notin_coord (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) :
  gtw_of t \notin [seq gtw_of x | x <- ltw] ->
  lcoord t \notin [seq lcoord x | x <- ltw].
Proof.
move=> H; apply: (contra _ H) => /mapP[x hx hlc]; apply/mapP; exists x => //=.
by rewrite hlc.
Qed.

(* ================================================================== *)
(** ** The multi-target per-leaf relation (base-offset chain blocks). *)

(** For each committed leaf [j], the SM-TCR(F) table holds that leaf's
    [total_query_count w ds] chain targets at absolute indices [base_j + jc] (jc the
    per-leaf chain index); [base_j] is the accumulated chain count of
    prior leaves (the stored counter [cnt]).  [us] is the leaf's sampled
    roots ([sg = wsigs] their signature digits). *)
Definition RCTrel (pp : PP)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × (('option 'nat) × 'nat)))})
    (Q : seq (adrs_sf_ch × N)) : Prop :=
  forall j,
    match getm ltg j with
    | Some (t0, (sg, md0)) =>
        exists (base : nat) (us : seq N),
          [/\ size us = l,
              sg = wsigs (lcoord t0) pp 0 (l_rrdigS (lcoord t0) pp md0 j) us,
              getm rtg j = Some (t0, ((sg, md0),
                 (lfind (lcoord t0) pp md0, base))),
              (base + total_query_count w (l_rrdigS (lcoord t0) pp md0 j) <= size Q)%N
            & forall jc, (jc < total_query_count w (l_rrdigS (lcoord t0) pp md0 j))%N ->
                qnth Q (base + jc)
                = qnth [seq lwq (lcoord t0) q
                       | q <- lcq (lcoord t0) pp (l_rrdigS (lcoord t0) pp md0 j) us]
                    jc]
    | None => getm rtg j = None
    end.

Lemma RCTrel_empty (pp : PP) : RCTrel pp emptym emptym [::].
Proof. by move=> j; rewrite emptymE. Qed.

(** Every SM-TCR tweak's coordinate is a committed-leaf coordinate. *)
Definition Qcoord_ok (ltw : seq adrs_sf_ch) (Q : seq (adrs_sf_ch × N)) : bool :=
  all (fun tw => lcoord tw \in [seq lcoord x | x <- ltw]) (unzip1 Q).

Lemma Qcoord_ok_nil (ltw : seq adrs_sf_ch) : Qcoord_ok ltw [::].
Proof. by []. Qed.

(** Cross-leaf freshness of the committing leaf's coordinate. *)
Lemma coord_fresh (ltw : seq adrs_sf_ch) (Q : seq (adrs_sf_ch × N))
    (t : adrs_sf_ch) :
  Qcoord_ok ltw Q ->
  gtw_of t \notin [seq gtw_of x | x <- ltw] ->
  all (fun tw => lcoord tw != lcoord t) (unzip1 Q).
Proof.
move=> /allP hQ /gtw_notin_coord hnt; apply/allP => tw htw.
apply/negP => /eqP e; move/negP: hnt; apply.
by rewrite -e; exact: hQ.
Qed.

(* ================================================================== *)
(** ** The all-private location set + the top-level invariant. *)

Definition IGNCT : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rct_pp_loc ; rct_tgts_loc ; rct_tws_loc ; rct_rev_loc ; rct_slog_loc ;
        rct_cnt_loc ; Spp ; Stg ; Stw ; Srv ].

Definition RCT
    (lpp : option PP)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (ltw : seq adrs_sf_ch) (lrv : bool) (lsl : seq nat)
    (rpp : option PP)
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × (('option 'nat) × 'nat)))})
    (rtw : seq adrs_sf_ch) (rrv : bool) (rsl : seq nat) (rcnt : nat)
    (spp : option (th_PP TFl)) (stg : {fmap nat -> (th_T TFl × th_M TFl)})
    (stw : seq (th_T TFl)) (srv : bool) : Prop :=
  [/\ rtw = ltw, rrv = lrv, rsl = lsl, rpp = (if lrv then lpp else None)
    & [/\ spp = lpp, srv = lrv
      & match lpp with
        | None => [/\ ltg = emptym, rtg = emptym, stg = emptym, stw = [::]
                    & rcnt = 0 /\ lrv = false]
        | Some pp => exists Q,
            [/\ stg = qmap_from 0 Q, stw = unzip1 Q, rcnt = size Q,
                (size Q <= size ltw * ptcr)%N
              & Qcoord_ok ltw Q /\ RCTrel pp ltg rtg Q]
        end]].

Definition ct_inv : precond :=
  heap_ignore IGNCT
  ⋊ rel_app [:: (lhs, Lpp) ; (lhs, Ltg) ; (lhs, Ltw) ; (lhs, Lrv) ; (lhs, Lsl) ;
                (rhs, rct_pp_loc) ; (rhs, rct_tgts_loc) ; (rhs, rct_tws_loc) ;
                (rhs, rct_rev_loc) ; (rhs, rct_slog_loc) ; (rhs, rct_cnt_loc) ;
                (rhs, Spp) ; (rhs, Stg) ; (rhs, Stw) ; (rhs, Srv) ] RCT.

Arguments ct_inv : simpl never.

Lemma ct_invE s0 s1 :
  ct_inv (s0, s1) ->
  heap_ignore IGNCT (s0, s1) /\
  RCT (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
      (get_heap s0 Lsl)
      (get_heap s1 rct_pp_loc) (get_heap s1 rct_tgts_loc) (get_heap s1 rct_tws_loc)
      (get_heap s1 rct_rev_loc) (get_heap s1 rct_slog_loc) (get_heap s1 rct_cnt_loc)
      (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv).
Proof. by move=> [h1 h2]; split. Qed.

Lemma ct_invI s0 s1 :
  heap_ignore IGNCT (s0, s1) ->
  RCT (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
      (get_heap s0 Lsl)
      (get_heap s1 rct_pp_loc) (get_heap s1 rct_tgts_loc) (get_heap s1 rct_tws_loc)
      (get_heap s1 rct_rev_loc) (get_heap s1 rct_slog_loc) (get_heap s1 rct_cnt_loc)
      (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv) ->
  ct_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** Pin [pp] on [Lpp] & [Spp] (from [None]); preserves the invariant. *)
Lemma ct_inv_pin (pp : PP) s0 s1 :
  ct_inv (s0, s1) -> get_heap s0 Lpp = None ->
  ct_inv (set_heap s0 Lpp (Some pp), set_heap s1 Spp (Some pp)).
Proof.
move=> hinv hL.
case/ct_invE: hinv => hign hRCT.
move: hRCT; rewrite hL => -[hrtw hrrv hrsl hrpp [hspp hsrv hm]].
case: hm => hltg hrtg hstg hstw [hrcnt hlrv].
apply: ct_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RCT; get_heap_simpl.
  rewrite hltg hrtg hstg hstw hrcnt hlrv hrtw hrrv hrsl.
  move: hrpp; rewrite hlrv /= => hrpp; rewrite hrpp.
  rewrite hsrv hlrv; split=> //; split=> //.
  exists [::]; split=> //=; exact: RCTrel_empty.
Qed.

(** GETPP: reveal pp (rev false -> true), R copies pp into its own pp loc. *)
Lemma ct_inv_reveal (pp : PP) s0 s1 :
  ct_inv (s0, s1) -> get_heap s0 Lpp = Some pp ->
  ct_inv (set_heap s0 Lrv true,
          set_heap (set_heap (set_heap s1 Srv true) rct_pp_loc (Some pp))
            rct_rev_loc true).
Proof.
move=> hinv hL.
case/ct_invE: hinv => hign hRCT.
move: hRCT; rewrite hL => -[hrtw hrrv hrsl hrpp [hspp hsrv hm]].
apply: ct_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RCT; get_heap_simpl.
  rewrite hL hrtw hrsl hspp; split=> //; split=> //; exact: hm.
Qed.

(** LSIGN: set [Lsl] and [rct_slog] to the same value; preserves the invariant. *)
Lemma ct_inv_setsl (vw : seq nat) s0 s1 :
  ct_inv (s0, s1) ->
  ct_inv (set_heap s0 Lsl vw, set_heap s1 rct_slog_loc vw).
Proof.
move=> hinv.
case/ct_invE: hinv => hign hRCT.
move: hRCT => [hrtw hrrv hrsl hrpp [hspp hsrv hm]].
apply: ct_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RCT; get_heap_simpl.
  rewrite hrtw hrrv hrpp hspp hsrv.
  by split=> //; split=> //.
Qed.

(** The pinned invariant as a single applied atom. *)
Definition ctL (pp : PP) : precond :=
  λ '(s0, s1), ct_inv (s0, s1) /\ get_heap s0 Lpp = Some pp.

Arguments ctL : simpl never.

Lemma bind_put_ret {A B : choiceType} (ℓ : Location) (v : ℓ) (a : A)
    (k : A -> raw_code B) :
  bind (#put ℓ := v ;; ret a) k = (#put ℓ := v ;; k a).
Proof. by []. Qed.

Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

(** Couple the two lazy [pp] reads (game [Lpp] vs SM-TCR [Spp]). *)
Lemma r_pp2 {B : choiceType} (k0 k1 : PP -> raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), ctL pp (s0, s1) ⦄ k0 pp ≈ k1 pp ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), ct_inv (s0, s1) ⦄
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
    case/ct_invE: hinv => _ [_ _ _ _ [hsp _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hsp hr0. }
move=> e; subst spp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv hr0] hr1].
  rewrite /rem_inv /= in hr0.
  by rewrite /ctL /=; split; [exact: hinv | exact: hr0].
- cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite !bind_put_ret.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [[[hinv hr0] hr1] e0]] e1]].
  rewrite /rem_inv /= in hr0.
  subst s0 s1; rewrite /ctL /=; split.
  + exact: (ct_inv_pin pp s0' s1' hinv hr0).
  + by rewrite get_set_heap_eq.
Qed.

(* ================================================================== *)
(** ** The COMMIT block precondition (positional; [Q] grows as chain
    targets are committed, [cnt0] frozen; the game/R tables frozen). *)

Definition lctblk (po : option PP) (lsl : seq nat) (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × (('option 'nat) × 'nat)))})
    (cnt0 : nat) (Q : seq (adrs_sf_ch × N)) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNCT (s0, s1),
      [/\ get_heap s0 Lpp = po, get_heap s0 Lrv = false, get_heap s0 Lsl = lsl,
          get_heap s0 Ltw = ltw & get_heap s0 Ltg = ltg],
      [/\ get_heap s1 rct_pp_loc = None, get_heap s1 rct_rev_loc = false,
          get_heap s1 rct_slog_loc = lsl, get_heap s1 rct_tws_loc = ltw
        & get_heap s1 rct_tgts_loc = rtg /\ get_heap s1 rct_cnt_loc = cnt0]
    & [/\ get_heap s1 Spp = po, get_heap s1 Srv = false,
          get_heap s1 Stw = unzip1 Q & get_heap s1 Stg = qmap_from 0 Q]].

Arguments lctblk : simpl never.

Lemma lctblk_Spp po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s1 Spp = po.
Proof. by case=> _ _ _ [? _ _ _]. Qed.

Lemma lctblk_Srv po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s1 Srv = false.
Proof. by case=> _ _ _ [_ ? _ _]. Qed.

Lemma lctblk_Stw po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s1 Stw = unzip1 Q.
Proof. by case=> _ _ _ [_ _ ? _]. Qed.

Lemma lctblk_Stg po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s1 Stg = qmap_from 0 Q.
Proof. by case=> _ _ _ [_ _ _ ?]. Qed.

Lemma lctblk_cnt po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s1 rct_cnt_loc = cnt0.
Proof. by case=> _ _ [_ _ _ _ [_ ?]] _. Qed.

(** The TQUERY state update: append one chain target to [Q]. *)
Lemma lctblk_qupd (pp : PP) lsl ltw ltg rtg cnt0 Q (tw : adrs_sf_ch) (x : N)
    s0 s1 :
  lctblk (Some pp) lsl ltw ltg rtg cnt0 Q (s0, s1) ->
  lctblk (Some pp) lsl ltw ltg rtg cnt0 (rcons Q (tw, x))
    (s0, set_heap (set_heap s1 Stg (setm (qmap_from 0 Q) (size (unzip1 Q)) (tw, x)))
           Stw (rcons (unzip1 Q) tw)).
Proof.
case=> hign hG hR hSM; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- exact: hG.
- case: hR => hrpp hrrv hrsl hrtw [hrtg hrcnt]; get_heap_simpl.
  by rewrite hrpp hrrv hrsl hrtw hrtg hrcnt.
- case: hSM => hspp hsrv hstw hstg; get_heap_simpl.
  rewrite hspp hsrv; split=> //.
  + by rewrite /unzip1 map_rcons.
  + by move: (qmap_from_rcons 0 Q (tw, x)) => HH; rewrite HH add0n size_map.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked TQUERY (pp pinned by the COLLQ pin). *)

Lemma r_lctquery_known (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    lsl ltw ltg rtg cnt0 (i k : nat) (x : N) (Qpre : seq (adrs_sf_ch × N))
    (absQ : seq ((nat * nat) * N))
    (c0 : raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size (Qpre ++ [seq lwq zi q | q <- absQ]) < qF)%N ->
  anchor_bounded zi ->
  component_bounded l i ->
  component_bounded w.-1 k ->
  absQ_bounded absQ ->
  all (fun tw => lcoord tw != zi) (unzip1 Qpre) ->
  (i, k) \notin unzip1 absQ ->
  ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltw ltg rtg cnt0
         (Qpre ++ [seq lwq zi q | q <- rcons absQ ((i, k), x)]) (s0, s1) ⦄
     c0 ≈ k1 (FWl zi pp (i, k) x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltw ltg rtg cnt0
         (Qpre ++ [seq lwq zi q | q <- absQ]) (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) lct_tqo (chtw_of zi i k, x)) k1 ⦃ post ⦄.
Proof.
move=> hbud hzi hi hk hqb hpre hself h.
rewrite (resolve_lct_tq b (chtw_of zi i k) x).
eapply (r_get_bind_rhs Srv false).
  by move=> s0 s1; exact: lctblk_Srv.
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs Stw (unzip1 (Qpre ++ [seq lwq zi q | q <- absQ]))).
  by move=> s0 s1; exact: lctblk_Stw.
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: (lwq_notin zi i k Qpre absQ hzi hi hk hqb hpre hself).
move=> _.
eapply (r_get_bind_rhs Stg (qmap_from 0 (Qpre ++ [seq lwq zi q | q <- absQ]))).
  by move=> s0 s1; exact: lctblk_Stg.
cbv beta.
eapply (@r_put2_bind_rhs _ _ _ _ _ _ _ _ (λ '(s0, s1),
          lctblk (Some pp) lsl ltw ltg rtg cnt0
            (Qpre ++ [seq lwq zi q | q <- rcons absQ ((i, k), x)]) (s0, s1))).
  move=> s0 s1 hb.
  have E : Qpre ++ [seq lwq zi q | q <- rcons absQ ((i, k), x)]
         = rcons (Qpre ++ [seq lwq zi q | q <- absQ]) (chtw_of zi i k, x).
    by rewrite map_rcons rcons_cat.
  rewrite E.
  exact: (lctblk_qupd pp lsl ltw ltg rtg cnt0
            (Qpre ++ [seq lwq zi q | q <- absQ]) (chtw_of zi i k) x s0 s1 hb).
eapply (r_get_bind_rhs Spp (Some pp)).
  by move=> s0 s1; exact: lctblk_Spp.
cbv beta iota.
rewrite !bind_ret_l th_eval_chtw.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The walk and per-chain inductions (ChainHop's, at the leaf coord). *)

Lemma r_lctwalk_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    lsl ltw ltg rtg cnt0 (post : postcond B B) :
  forall n i k (x : N) (Qpre : seq (adrs_sf_ch × N))
         (absQ : seq ((nat * nat) * N)) (c0 : raw_code B) (k1 : N -> raw_code B),
  anchor_bounded zi ->
  (i < l)%N ->
  (k + n <= w.-1)%N ->
  absQ_bounded absQ ->
  (size (Qpre ++ [seq lwq zi q | q <- absQ]) + n <= qF)%N ->
  all (fun tw => lcoord tw != zi) (unzip1 Qpre) ->
  all (tweak_lt i k) (unzip1 absQ) ->
  ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltw ltg rtg cnt0
         (Qpre ++ [seq lwq zi q | q <- absQ ++ walkq PP N (FWl zi) pp i k n x])
         (s0, s1) ⦄
     c0 ≈ k1 (chain (cfWl zi pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltw ltg rtg cnt0
         (Qpre ++ [seq lwq zi q | q <- absQ]) (s0, s1) ⦄
     c0 ≈ bind (code_link (lct_walk zi i k n x) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x Qpre absQ c0 k1 hzi hi hkn hb hbud hpre hfresh h.
- by move: h; rewrite cats0.
- rewrite /= bind_assoc.
  eapply (r_lctquery_known b pp zi lsl ltw ltg rtg cnt0 i k x Qpre absQ) => //.
  + by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + exact: component_bounded_lt.
  + apply: component_bounded_lt.
    by apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
  + exact: tlt_notin hfresh.
  + apply: IH => //.
    * by move: hkn; rewrite addnS addSn.
    * apply: absQ_bounded_rcons => //.
      by apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
    * by move: hbud; rewrite map_rcons -rcons_cat size_rcons addSn -addnS.
    * rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
      -- by rewrite /tweak_lt /= ltnn eqxx ltnSn.
      -- exact: all_tlt_widen hfresh.
    * by move: h; rewrite (walkq_cons PP N (FWl zi)) cat_rcons.
Qed.

Lemma r_lctchains_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    lsl ltw ltg rtg cnt0 (post : postcond B B) :
  forall ds st (Qpre : seq (adrs_sf_ch × N)) (absQ : seq ((nat * nat) * N))
         (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  anchor_bounded zi ->
  (st + size ds <= l)%N ->
  all (λ d : nat, (d < w)%N) ds ->
  absQ_bounded absQ ->
  (size (Qpre ++ [seq lwq zi q | q <- absQ]) + total_query_count w ds <= qF)%N ->
  all (fun tw => lcoord tw != zi) (unzip1 Qpre) ->
  all (λ t : nat * nat, (t.1 < st)%N) (unzip1 absQ) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltw ltg rtg cnt0
            (Qpre ++ [seq lwq zi q
                     | q <- absQ ++ commit_queries PP N (FWl zi) w pp st ds us])
            (s0, s1) ⦄
        K0 (wsigs zi pp st ds us)
      ≈ K1 (wsigs zi pp st ds us, wends zi pp st ds (wsigs zi pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltw ltg rtg cnt0
         (Qpre ++ [seq lwq zi q | q <- absQ]) (s0, s1) ⦄
     bind (sample_sig_roots PP N (FWl zi) dN pp st ds) K0
   ≈ bind (code_link (lct_chains zi st ds) (SMB b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st Qpre absQ K0 K1 hzi hst hds hQr hbud hpre hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- move: hst => /=; rewrite addnS => hst2.
  have hstl : (st < l)%N := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : (st.+1 + size ds <= l)%N := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)) !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    have hkn0 : (0 + (w.-1 - 0) <= w.-1)%N by rewrite add0n subn0.
    eapply (r_lctwalk_spec b pp zi lsl ltw ltg rtg cnt0 post
              (w.-1 - 0) st 0 u Qpre absQ) => //.
    * apply: leq_trans hbud.
      by rewrite leq_add2l /total_query_count /= /chain_query_count /= leq_addr.
    * exact: all_lt_tlt.
    * rewrite (code_link_bind (lct_chains zi st.+1 ds)) bind_assoc.
      eapply IH => //.
      -- apply: absQ_bounded_cat; first exact: hQr.
         exact: (absQ_bounded_walk pp zi st 0 (w.-1 - 0) u hstl hkn0).
      -- by move: hbud; rewrite !size_lwqQ size_cat size_walkq
           /total_query_count /= /chain_query_count /= -!addnA.
      -- rewrite /unzip1 map_cat all_cat; apply/andP; split.
         ++ by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ apply: sub_all (walkq_tweak1 PP N (FWl zi) pp st 0 _ u)
              => t /= /eqP ->; exact: ltnSn.
      -- move=> us hus.
         move: (h (u :: us)); rewrite /= hus => /(_ erefl).
         by rewrite (commit_queries_cons PP N (FWl zi)) /chain_queries /= catA.
  + rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    have hw0 : (0 < w)%N := leq_trans (ltn0Sn d') (ltnW hd0).
    have hdw1 : (d'.+1 <= w.-1)%N by rewrite -ltnS (prednK hw0).
    have hkn1 : (d'.+1 + (w.-1 - d'.+1) <= w.-1)%N by rewrite subnKC.
    eapply (r_lctquery_known b pp zi lsl ltw ltg rtg cnt0 st d' u Qpre absQ) => //.
    * apply: leq_trans hbud.
      by rewrite -addn1 leq_add2l /total_query_count /= /chain_query_count /=.
    * exact: component_bounded_lt.
    * exact: component_bounded_lt.
    * exact: lt_notin.
    * rewrite /= (code_link_bind (lct_walk zi st d'.+1 (w.-1 - d'.+1)
                    (FWl zi pp (st, d') u))) bind_assoc.
      eapply (r_lctwalk_spec b pp zi lsl ltw ltg rtg cnt0 post
                (w.-1 - d'.+1) st d'.+1 (FWl zi pp (st, d') u) Qpre
                (rcons absQ ((st, d'), u))) => //.
      -- apply: absQ_bounded_rcons => //.
      -- apply: leq_trans _ hbud.
         rewrite !size_lwqQ size_rcons /total_query_count /= /chain_query_count /= add1n -!addnA.
         by rewrite leq_add2l addSn ltn_add2l leq_addr.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /tweak_lt /= ltnn eqxx ltnSn.
         ++ exact: all_lt_tlt.
      -- rewrite (code_link_bind (lct_chains zi st.+1 ds)) bind_assoc.
         eapply IH => //.
         ++ apply: absQ_bounded_cat.
            ** apply: absQ_bounded_rcons => //.
            ** exact: (absQ_bounded_walk pp zi st d'.+1
                  (w.-1 - d'.+1) (FWl zi pp (st, d') u) hstl hkn1).
         ++ by move: hbud; rewrite !size_lwqQ size_cat size_rcons size_walkq
              /total_query_count /= /chain_query_count /= add1n addSn -!addnA addnS.
         ++ rewrite /unzip1 map_cat all_cat; apply/andP; split.
            ** rewrite map_rcons all_rcons; apply/andP; split.
               --- by rewrite /= ltnSn.
               --- by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
            ** apply: sub_all (walkq_tweak1 PP N (FWl zi) pp st d'.+1 _ _)
                 => t /= /eqP ->; exact: ltnSn.
         ++ move=> us hus.
            move: (h (u :: us)); rewrite /= hus => /(_ erefl).
            by rewrite (commit_queries_cons PP N (FWl zi)) /chain_queries
                       catA cat_rcons.
Qed.

(* ================================================================== *)
(** ** Stage-1 helpers: size, invariant extension, win-predicate bridges. *)

Lemma size_l_rrdigS (zi : nat * nat) pp md j : size (l_rrdigS zi pp md j) = l.
Proof.
rewrite /l_rrdigS /l_rrdig;
  case: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md)
  => [c|]; [exact: size_digest_of | exact: size_nseq].
Qed.

Lemma wf_l_rrdigS (hw : (0 < w)%N) (zi : nat * nat) pp md j :
  wf_digits w (l_rrdigS zi pp md j).
Proof.
rewrite /l_rrdigS /l_rrdig.
case E: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md) => [c|].
- by move: (find_ctr_good PP D Hgrind S_wn c_max zi.1 zi.2 pp md c E)
    => /andP[h1 _].
- by rewrite /wf_digits all_nseq ltn_predL hw orbT.
Qed.

Lemma wendsEl (zi : nat * nat) pp (ds : seq nat) (ys : seq N) :
  size ds = l -> wends zi pp 0 ds ys = lcompl zi pp ds ys.
Proof.
move=> h.
by rewrite (ends_of_from_sig PP N (FWl zi) l w pp ds ys h)
   (wcendsE PP N F zi.1 zi.2).
Qed.

(** Qcoord_ok extends to a new leaf whose block sits entirely at its
    coordinate. *)
Lemma Qcoord_ok_rcons (ltw : seq adrs_sf_ch) (Q : seq (adrs_sf_ch × N))
    (t : adrs_sf_ch) (blk : seq (adrs_sf_ch × N)) :
  Qcoord_ok ltw Q ->
  all (fun tw => lcoord tw == lcoord t) (unzip1 blk) ->
  Qcoord_ok (rcons ltw t) (Q ++ blk).
Proof.
move=> hQ hblk; rewrite /Qcoord_ok /unzip1 map_cat all_cat; apply/andP; split.
- apply: sub_all hQ => tw hin; rewrite map_rcons mem_rcons in_cons hin orbT //.
- apply/allP => tw htw; move: (allP hblk tw htw) => /eqP ->.
  by rewrite map_rcons mem_rcons in_cons eqxx.
Qed.

(** The re-tagged commit list of one leaf sits entirely at its coordinate. *)
Lemma all_lcoord_blk (zi : nat * nat) (Q : seq ((nat * nat) * N)) :
  anchor_bounded zi ->
  absQ_bounded Q ->
  all (fun tw => lcoord tw == zi) (unzip1 [seq lwq zi q | q <- Q]).
Proof.
move=> hzi /allP hb; rewrite unzip1_lwq; apply/allP => tw /mapP[q hq ->].
have hqmem : q.1 \in unzip1 Q by apply/mapP; exists q.
case/andP: (hb _ hqmem) => hqi hqk.
rewrite /= (lcoord_chtw zi q.1.1 q.1.2 hzi
  (component_bounded_lt l q.1.1 hqi)
  (component_bounded_lt w.-1 q.1.2 hqk)) eqxx.
by [].
Qed.

(** The multi-target invariant extends by one leaf: block at absolute
    base [size Q], old leaves preserved in the prefix. *)
Lemma RCTrel_qupd (pp : PP) (t : adrs_sf_ch) (md : D) (us : seq N) (k : nat)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × (('option 'nat) × 'nat)))})
    (Q : seq (adrs_sf_ch × N)) :
  size us = l ->
  RCTrel pp ltg rtg Q ->
  RCTrel pp
    (setm ltg k (t, (wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md k) us, md)))
    (setm rtg k (t, ((wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md k) us, md),
                     (lfind (lcoord t) pp md, size Q))))
    (Q ++ [seq lwq (lcoord t) q
          | q <- lcq (lcoord t) pp (l_rrdigS (lcoord t) pp md k) us]).
Proof.
move=> hus hRC j.
have [->|hjk] := eqVneq j k.
- rewrite setmE eqxx /=.
  exists (size Q), us; split=> //.
  + by rewrite setmE eqxx.
  + rewrite size_cat size_map (size_lcq (lcoord t) pp 0 _ us);
      last by rewrite hus size_l_rrdigS.
    exact: leqnn.
  + move=> jc hjc; exact: qnth_cat_r.
- rewrite setmE (negbTE hjk).
  move: (hRC j); case: (getm ltg j) => [[t0 [sg0 md0]]|]; last first.
    by rewrite setmE (negbTE hjk).
  move=> [base [us0 [hsz0 hsg0 hrtg0 hbud0 hplace0]]].
  exists base, us0; split=> //.
  + by rewrite setmE (negbTE hjk).
  + rewrite size_cat; exact: (leq_trans hbud0 (leq_addr _ _)).
  + move=> jc hjc; rewrite qnth_cat_l; first exact: hplace0.
    apply: (leq_trans _ hbud0); by rewrite ltn_add2l.
Qed.

(** The Glmid2 win predicate IS [lct_v] at the stored [find_ctr]. *)
Lemma P_gm2_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_gm2S PP N D F Tl Hgrind S_wn c_max pp t0 sg md0 j mw
  = lct_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw.
Proof.
rewrite /P_gm2S /lct_v /grind_hitS /leaf_km.gateL /l_rrpkS /l_rrdigS /l_rrdig
        /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c.
by rewrite !andbA.
Qed.

(** The Glmid3 win predicate is [lct_v] AND-ed with the negated TCR
    discriminant. *)
Lemma P_gm3_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_gm3S PP N D F Tl Hgrind S_wn c_max pp t0 sg md0 j mw
  = lct_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw
    && ~~ isSome (lct_dec pp t0 sg md0 j mw).
Proof.
rewrite /P_gm3S /lct_v /lct_dec /grind_hitS /leaf_km.gateL /l_rrpkS /l_rrdigS
        /l_rrdig /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c.
by rewrite !andbA.
Qed.

(** The CHAIN-TCR classifier never fires at the virtual (all-max) digit. *)
Lemma tcr_allmax_none (Fc : PP -> nat * nat -> N -> N) (pp : PP)
    (mstar : seq nat) (sgs sgstar : seq N) :
  tcr_decision PP N Fc l w pp (nseq l w.-1) mstar sgs sgstar = None.
Proof.
rewrite /tcr_decision.
case E: (ohead _) => [i|]; last by [].
have hil : (i < l)%N.
  have : i \in [seq i0 <- iota 0 l
               | (nth 0 mstar i0 < nth 0 (nseq l w.-1) i0)%N].
    by case: (filter _ _) E => //= a s [<-]; rewrite in_cons eqxx.
  by rewrite mem_filter mem_iota /= add0n => /andP[_ ->].
case: (qnth sgs i) => [si|]; last by [].
case: (qnth sgstar i) => [si'|]; last by [].
by rewrite nth_nseq hil /chain_extract subnn /=.
Qed.

(* ================================================================== *)
(** ** Stage-2 helpers: COMMIT-block extraction, pin, tail. *)

Lemma lctblk_Ltg po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s0 Ltg = ltg.
Proof. by case=> _ [_ _ _ _ ?] _ _. Qed.

Lemma lctblk_rtgts po lsl ltw ltg rtg cnt0 Q s0 s1 :
  lctblk po lsl ltw ltg rtg cnt0 Q (s0, s1) -> get_heap s1 rct_tgts_loc = rtg.
Proof. by case=> _ _ [_ _ _ _ [? _]] _. Qed.

(** The invariant gives the COMMIT block (with the existential [Q] and its
    facts) once [pp] is pinned and [rev = false]. *)
Lemma ct_inv_lctblk (pp : PP) s0 s1 :
  ct_inv (s0, s1) -> get_heap s0 Lpp = Some pp -> get_heap s0 Lrv = false ->
  exists Q,
    [/\ lctblk (Some pp) (get_heap s0 Lsl) (get_heap s0 Ltw) (get_heap s0 Ltg)
          (get_heap s1 rct_tgts_loc) (size Q) Q (s0, s1),
        (size Q <= size (get_heap s0 Ltw) * ptcr)%N,
        Qcoord_ok (get_heap s0 Ltw) Q
      & RCTrel pp (get_heap s0 Ltg) (get_heap s1 rct_tgts_loc) Q].
Proof.
move=> hinv hLpp hLrv.
case/ct_invE: hinv => hign hRC.
move: hRC; rewrite hLpp hLrv => -[hrtw hrrv hrsl hrpp [hspp hsrv hm]].
case: hm => Q [hstg hstw hrcnt hsize [hQcoord hRCT]].
exists Q; split.
- rewrite /lctblk; split.
  + exact: hign.
  + rewrite hLpp hLrv; split=> //.
  + rewrite hrpp hrrv hrsl hrtw hrcnt; split=> //.
  + rewrite hspp hsrv hstw hstg; split=> //.
- exact: hsize.
- exact: hQcoord.
- exact: hRCT.
Qed.

(** The COMMIT pre-pin / pinned block preconditions. *)
Definition bcmT (pp : PP) (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  ct_inv (s0, s1) /\ get_heap s0 Lpp = Some pp /\ get_heap s0 Lrv = false /\
  (size ltw < n_max)%N /\ get_heap s0 Ltw = ltw /\
  gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments bcmT : simpl never.

Definition bpreT (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  ct_inv (s0, s1) /\ get_heap s0 Lrv = false /\ (size ltw < n_max)%N /\
  get_heap s0 Ltw = ltw /\ gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments bpreT : simpl never.

Lemma bcmT_Spp (pp : PP) t ltw s0 s1 :
  bcmT pp t ltw (s0, s1) -> get_heap s1 Spp = Some pp.
Proof.
move=> [hinv [hlpp _]]; case/ct_invE: hinv => _ [_ _ _ _ [hspp _ _]].
by rewrite hspp hlpp.
Qed.

(** The COMMIT pin: couple the game's lazy [Lpp] with the leading grind
    COLLQ's lazy [Spp], landing in [bcmT pp t ltw]. *)
Lemma r_lct_pin_commit {B : choiceType} (t : adrs_sf_ch)
    (ltw : seq adrs_sf_ch)
    (k0 : PP -> raw_code B) (k1 : raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), bcmT pp t ltw (s0, s1) ⦄ k0 pp ≈ k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), bpreT t ltw (s0, s1) ⦄
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
    case/ct_invE: hinv => _ [_ _ _ _ [hsp _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hsp hr0. }
move=> e; subst spp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[[hinv [hrv [hsz [hltw hfr]]]] hr0] hr1].
  rewrite /rem_inv /= in hr0.
  rewrite /bcmT /=.
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
  subst s0 s1; rewrite /bcmT /=; split.
  + exact: (ct_inv_pin pp s0' s1' hinv hr0).
  + split; first by rewrite get_set_heap_eq.
    split; first by rewrite get_set_heap_neq.
    split; first exact: hsz.
    split; first by rewrite get_set_heap_neq.
    exact: hfr.
Qed.

(** The COMMIT tail: store on both sides (root already = [rr_pkS]); the
    invariant is re-established with the extended target list [Q']. *)
Lemma r_lct_tail (hw : (0 < w)%N) (pp : PP) (t : adrs_sf_ch) (md : D)
    (ltws : seq adrs_sf_ch) (us : seq N) (lsl : seq nat)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × (('option 'nat) × 'nat)))})
    (Q : seq (adrs_sf_ch × N)) :
  size us = l ->
  Qcoord_ok ltws Q ->
  RCTrel pp ltg rtg Q ->
  (size Q <= size ltws * ptcr)%N ->
  (size ltws < n_max)%N ->
  gtw_of t \notin [seq gtw_of x | x <- ltws] ->
  ⊢ ⦃ λ '(s0, s1), lctblk (Some pp) lsl ltws ltg rtg (size Q)
         (Q ++ [seq lwq (lcoord t) q
               | q <- lcq (lcoord t) pp (l_rrdigS (lcoord t) pp md (size ltws)) us])
         (s0, s1) ⦄
     (tgts ← get Ltg ;;
      #put Ltg := setm tgts (size ltws)
                    (t, (wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size ltws)) us,
                         md)) ;;
      #put Ltw := rcons ltws t ;;
      ret (l_rrpkS (lcoord t) pp md (size ltws)
             (wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size ltws)) us)))
   ≈ (tgts ← get rct_tgts_loc ;;
      #put rct_tgts_loc := setm tgts (size ltws)
             (t, ((wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size ltws)) us,
                   md), (lfind (lcoord t) pp md, size Q))) ;;
      #put rct_tws_loc := rcons ltws t ;;
      #put rct_cnt_loc :=
        (size Q + total_query_count w (l_rrdigS (lcoord t) pp md (size ltws)))%N ;;
      ret (l_rrpkS (lcoord t) pp md (size ltws)
             (wsigs (lcoord t) pp 0 (l_rrdigS (lcoord t) pp md (size ltws)) us)))
   ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ ct_inv (s0, s1) ⦄.
Proof.
move=> hus hQcoord hRCT hsize hsz hfr.
eapply (r_get_lhs_known Ltg ltg).
  { move=> s0 s1; exact: lctblk_Ltg. }
eapply (r_get_rhs_known rct_tgts_loc rtg).
  { move=> s0 s1; exact: lctblk_rtgts. }
apply r_put_lhs; apply r_put_lhs.
apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => sA [hpre4 es1].
case: hpre4 => sB [hpre3 esA].
case: hpre3 => sC [hpre2 esB].
case: hpre2 => sD [hpre1 es0].
case: hpre1 => sE [hblk esD].
case: hblk => hign [hLpp hLrv hLsl hLtw hLtg]
              [hrpp hrrv hrsl hrtw [hrtg hrcnt]] [hSpp hSrv hStw hStg].
subst s1 sA sB s0 sD.
split; first by [].
apply: ct_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RCT; get_heap_simpl.
  rewrite hLpp hLrv hLsl hrpp hrrv hrsl hSpp hSrv hStg hStw.
  split=> //; split=> //.
  exists (Q ++ [seq lwq (lcoord t) q
               | q <- lcq (lcoord t) pp (l_rrdigS (lcoord t) pp md (size ltws)) us]).
  split.
  + by [].
  + by [].
  + rewrite size_cat size_map (size_lcq (lcoord t) pp 0 _ us);
      last by rewrite hus size_l_rrdigS. by [].
  + rewrite size_cat size_map (size_lcq (lcoord t) pp 0 _ us);
      last by rewrite hus size_l_rrdigS.
    rewrite size_rcons mulSn addnC; apply: leq_add=> //.
    exact: (nqs_le l w _ (size_l_rrdigS (lcoord t) pp md (size ltws))).
  + split.
    * apply: Qcoord_ok_rcons; first exact: hQcoord.
      apply: all_lcoord_blk; first exact: l2_lcoord_bounded.
      apply: absQ_bounded_commit.
      -- by rewrite add0n size_l_rrdigS.
      -- exact: wf_l_rrdigS.
      -- by rewrite hus size_l_rrdigS.
    * exact: (RCTrel_qupd pp t md us (size ltws) ltg rtg Q hus hRCT).
Qed.

(** The multi-leaf SM-TCR(F) classifier win, corresponding to the
    single-instance chain hop's
    [wtcr_decisionP] at the arbitrary leaf coordinate [zi]. *)
Lemma l2_tcr_win (zi : nat * nat) (pp : PP) (md0 : D) (c : nat) (us : seq N)
    (mdf : D) (cf : nat) (sgstar : seq N) (jc : nat) (u : N) :
  find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md0 = Some c ->
  size us = l ->
  @valid_digest w S_wn (digest_of PP D Hgrind zi.1 zi.2 pp mdf cf) ->
  (size sgstar == l)%B ->
  lcompl zi pp (digest_of PP D Hgrind zi.1 zi.2 pp mdf cf) sgstar
  = lcompl zi pp (digest_of PP D Hgrind zi.1 zi.2 pp md0 c)
      (wsigs zi pp 0 (digest_of PP D Hgrind zi.1 zi.2 pp md0 c) us) ->
  digest_of PP D Hgrind zi.1 zi.2 pp mdf cf
    != digest_of PP D Hgrind zi.1 zi.2 pp md0 c ->
  tcr_decision PP N (FWl zi) l w pp
    (digest_of PP D Hgrind zi.1 zi.2 pp md0 c)
    (digest_of PP D Hgrind zi.1 zi.2 pp mdf cf)
    (wsigs zi pp 0 (digest_of PP D Hgrind zi.1 zi.2 pp md0 c) us)
    sgstar = Some (jc, u) ->
  exists t v,
    [/\ qnth (lcq zi pp (digest_of PP D Hgrind zi.1 zi.2 pp md0 c) us) jc
        = Some (t, v),
        u != v & FWl zi pp t u = FWl zi pp t v].
Proof.
move=> hfc hus hvd hsz hends hne hdec.
have hAC : forall (n st : nat) (ds : seq nat) (ys : seq N),
  all (fun q => Sec.lib.chain.core.chain_check PP N (FWl zi) w pp
                  q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st n)
           (zip ds (zip ys
              [seq chain (cfWl zi pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
              | q <- zip (iota st n) (zip ds ys)]))).
  elim=> [|n IH] st ds ys; first by case: ds => [|d ds]; case: ys => [|y ys].
  case: ds => [|d ds]; case: ys => [|y ys] => //=.
  apply/andP; split; last exact: IH.
  by rewrite /Sec.lib.chain.core.chain_check eqxx.
have hvmr : valid_msg l w S_wn (digest_of PP D Hgrind zi.1 zi.2 pp md0 c).
  apply: (vdigest_valid_msg PP D Hgrind S_wn zi.1 zi.2 pp md0 c).
  exact: (find_ctr_good PP D Hgrind S_wn c_max zi.1 zi.2 pp md0 c hfc).
have hvmf : valid_msg l w S_wn (digest_of PP D Hgrind zi.1 zi.2 pp mdf cf).
  exact: (vdigest_valid_msg PP D Hgrind S_wn zi.1 zi.2 pp mdf cf hvd).
have hverify : Sec.lib.chain.core.verify_sig PP N (FWl zi) l w S_wn pp
    (ends_of PP N (FWl zi) w pp 0
       (digest_of PP D Hgrind zi.1 zi.2 pp md0 c)
       (wsigs zi pp 0 (digest_of PP D Hgrind zi.1 zi.2 pp md0 c) us))
    (digest_of PP D Hgrind zi.1 zi.2 pp mdf cf) sgstar.
  rewrite (ends_of_from_sig PP N (FWl zi) l w pp _ _
             (size_digest_of PP D Hgrind zi.1 zi.2 pp md0 c)).
  rewrite -(wcendsE PP N F zi.1 zi.2).
  rewrite -hends (wcendsE PP N F zi.1 zi.2).
  rewrite /Sec.lib.chain.core.verify_sig hvmf hsz /=
          /Sec.lib.chain.core.ends_from_sig.
  exact: (hAC l 0 _ sgstar).
have hnin : digest_of PP D Hgrind zi.1 zi.2 pp mdf cf \notin
              [:: digest_of PP D Hgrind zi.1 zi.2 pp md0 c].
  by rewrite inE hne.
have H := tcr_decisionP PP N (FWl zi) l w S_wn pp
          (digest_of PP D Hgrind zi.1 zi.2 pp md0 c)
          (digest_of PP D Hgrind zi.1 zi.2 pp mdf cf) us sgstar
          hvmr hus hverify hnin.
rewrite hdec in H.
exact: H.
Qed.

(** If the null classifier [lct_dec] fires, the leaf is pop-1: in-budget
    ([j < q_s]) AND grindable ([find_ctr = Some c]), so its slot-keyed digit
    is the REAL signed digit [digest_of md0 c] (NOT the virtual all-max digit
    -- which the classifier structurally ignores, [tcr_allmax_none]). *)
Lemma lct_dec_digit (pp : PP) (t0 : adrs_sf_ch) (sg : seq N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) (jc : nat) (u : N) :
  lct_dec pp t0 sg md0 j mw = Some (jc, u) ->
  exists c,
    find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0 = Some c
    /\ l_rrdigS (lcoord t0) pp md0 j
      = digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c.
Proof.
rewrite /lct_dec /l_rrdigS /l_rrdig.
case: (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0)
  => [c|]; last by rewrite tcr_allmax_none.
by move=> _; exists c.
Qed.

(** [lct_v] true (with the stored [copt = lfind]) at a pop-1 leaf delivers
    exactly the SM-TCR(F) forgery preconditions: valid forged digest, l chain
    values, the completed-ends coincidence, and forged-vs-committed digit
    distinctness (the guarded [~~ grind_hitS]). *)
Lemma lct_v_true_facts (pp : PP) (t0 : adrs_sf_ch) (sg : seq N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) (c : nat) :
  find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0 = Some c ->
  lct_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw ->
  [/\ @valid_digest w S_wn
        (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2),
      (size mw.2.1 == l)%B,
      complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp
        (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2) mw.2.1
      = complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp
        (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c) sg
    & digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2
      != digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c].
Proof.
move=> hfc.
have hrdg : l_rrdigS (lcoord t0) pp md0 j
          = digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c.
  by rewrite /l_rrdigS /l_rrdig hfc.
rewrite /lct_v hrdg.
have hlf : isSome (lfind (lcoord t0) pp md0) by rewrite hfc.
move=> /andP[/andP[/andP[hverok _] hnghit] /eqP hfcv].
move: hverok; rewrite /shrincs_fxmss_wots_checks => /andP[/andP[hvd hsz] _].
split=> //.
by move: hnghit; rewrite hlf /=.
Qed.

Lemma R_ctcr_leaf_real (hw : (0 < w)%N) :
  perfect IKM GM2 (R_ctcr_leaf ∘ SMB true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ct_inv).
{ rewrite /ct_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *)
  rewrite /rr_commit. ssprove_code_simpl; simpl. destruct arg as [t md].
  eapply r_get_remember_lhs => lrev. eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1]. case/ct_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1. by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev. eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws. eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1]. case/ct_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1. by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws. eapply r_assertD_same => hsz. eapply r_assertD_same => hfr.
  eapply rpre_weaken_rule with (pre := λ '(s0, s1), bpreT t ltws (s0, s1)).
  2:{ move=> s0 s1 H. case: H => [[[[hinv hrL] _] hr0] _].
      rewrite /rem_inv /= in hrL hr0. rewrite /bpreT; split; first exact: hinv.
      split; first by rewrite hrL (negbTE erev). split; first exact: hsz.
      split; first exact: hr0. exact: hfr. }
  eapply r_lct_pin_commit => pp. apply rpre_hypothesis_rule => s0 s1 hbcm.
  move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
  have [Q [hblk hsizeb hQcoord hRCT]] := ct_inv_lctblk pp s0 s1 hinv hlpp hrv.
  rewrite hltw in hblk hsizeb hQcoord.
  eapply rpre_weaken_rule with (pre := λ '(a, b),
     lctblk (Some pp) (get_heap s0 Lsl) ltws (get_heap s0 Ltg)
       (get_heap s1 rct_tgts_loc) (size Q)
       (Q ++ [seq lwq (lcoord t) q | q <- [::]]) (a, b)).
  2:{ move=> a b [ha hb]; move: ha hb => /= -> ->; rewrite cats0; exact: hblk. }
  eapply (r_lctgrind_spec true pp (lcoord t) md (iota 0 c_max) _).
    { move=> a b; exact: lctblk_Spp. }
  set hs := [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max].
  have hds : lct_digitS (size ltws) hs = l_rrdigS (lcoord t) pp md (size ltws).
    by rewrite /lct_digitS /l_rrdigS /hs lct_digit_E.
  have hcopt : omap fst (lct_pick hs) = lfind (lcoord t) pp md.
    by rewrite /hs lct_copt_E.
  rewrite hds hcopt.
  eapply (r_get_rhs_known rct_cnt_loc (size Q)). { move=> a b; exact: lctblk_cnt. }
  cbv beta.
  eapply (r_lctchains_spec true pp (lcoord t) (get_heap s0 Lsl) ltws
            (get_heap s0 Ltg) (get_heap s1 rct_tgts_loc) (size Q) _
            (l_rrdigS (lcoord t) pp md (size ltws)) 0 Q [::]).
  { exact: l2_lcoord_bounded. }
  { by rewrite add0n size_l_rrdigS. }
  { exact: wf_l_rrdigS. }
  { by []. }
  { rewrite cats0.
    apply: (leq_trans (leq_add hsizeb
              (nqs_le l w _ (size_l_rrdigS (lcoord t) pp md (size ltws))))).
    by rewrite -mulSnr; exact: leq_mul. }
  { exact: (coord_fresh ltws Q t hQcoord hfr'). }
  { by []. }
  move=> us hus. cbv beta iota.
  eapply (r_get_rhs_known Spp (Some pp)). { move=> a b; exact: lctblk_Spp. }
  cbv beta iota. rewrite decode_tweakK.
  rewrite (wendsEl (lcoord t) pp _ _ (size_l_rrdigS (lcoord t) pp md (size ltws))).
  apply: (r_lct_tail hw pp t md ltws us (get_heap s0 Lsl) (get_heap s0 Ltg)
            (get_heap s1 rct_tgts_loc) Q).
  { by rewrite hus size_l_rrdigS. }
  { exact: hQcoord. } { exact: hRCT. } { exact: hsizeb. }
  { exact: hsz'. } { exact: hfr'. }
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rct_pp_loc := Some b ;; #put rct_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (ct_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK *)
  destruct arg as [j mw].
  rewrite /rr_winbody.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ct_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  + eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          by move: (hRCT j); rewrite hr2 E /= -hr3.
        - by case: hm => he1 hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  + eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp base, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), (lfind (lcoord t0) pp md0, base))))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          move: (hRCT j); rewrite hr2 E => -[base [us [_ _ hrtgj0 _ _]]].
          exists pp, base; split; [by rewrite -hr4 El | by rewrite -hr3].
        - case: hm => _ _ _ _ [_ hlrvF].
          by move: hlrvF; rewrite hr0 erev. }
    move=> [pp [base [hlpp hrtgj]]].
    rewrite hlpp hrtgj /=.
    eapply (r_get_rhs_known rct_pp_loc (Some pp)).
      { move=> s0 s1 [[[[[hinv hrev] _] _] _] hpp].
        rewrite /rem_inv /= in hrev hpp.
        case/ct_invE: hinv => _ [_ _ _ hrpp _].
        by rewrite hrpp hrev erev /= hpp. }
    cbv beta iota.
    rewrite bind_ret_l.
    rewrite P_gm2_E.
    case Edec: (lct_dec pp t0 sg md0 j mw) => [[jc u]|]; last first.
    * (* CHAIN classifier absent: both = lct_v *)
      apply r_ret => s0 s1 hpre; split; first by [].
      by case: hpre => [[[[[hinv _] _] _] _] _].
    * case: ifP => hv; last first.
      -- (* verify fails: reduction = false = lct_v (false) *)
         apply r_ret => s0 s1 hpre; split; first by [].
         by case: hpre => [[[[[hinv _] _] _] _] _].
      -- (* CHAIN-TCR collision: SM-TCR CHECK answers true = lct_v (true) *)
         have [c [hfc hrdg]] := lct_dec_digit pp t0 sg md0 j mw jc u Edec.
         have [hvd hsz hends hne] := lct_v_true_facts pp t0 sg md0 j mw c hfc hv.
         ssprove_code_simpl; simplify_linking.
         eapply (r_get_rhs_known Srv true).
           { move=> s0 s1 [[[[[hinv hr0] _] _] _] _].
             rewrite /rem_inv /= in hr0.
             case/ct_invE: hinv => _ [_ _ _ _ [_ hsrv _]].
             by rewrite hsrv hr0 erev. }
         eapply r_bind_assertD_rhs; first by [].
         move=> _.
         eapply r_get_remember_rhs => tg.
         eapply (r_fact (exists (tw : nat * nat) (v : N),
                   [/\ getm tg (base + jc)%N
                       = Some (chtw_of (lcoord t0) tw.1 tw.2, v),
                       u != v
                     & FWl (lcoord t0) pp tw u = FWl (lcoord t0) pp tw v])).
           { move=> s0 s1 [[[[[[hinv hr0] hr1] hr2] hr3] hr4] hr5].
             rewrite /rem_inv /= in hr2 hr3 hr4 hr5.
             case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
             have hLpp0 : get_heap s0 Lpp = Some pp by rewrite hr4.
             rewrite hLpp0 in hm.
             case: hm => Qc [hstg _ _ _ [_ hRCT]].
             have htg : tg = qmap_from 0 Qc by rewrite -hr5.
             move: (hRCT j); rewrite hr2 E => -[base' [us [hus hsgus hrtgj0 _ hplace]]].
             have hbase : base' = base.
               { have h2 : getm rtg j
                         = Some (t0, (sg, md0, (lfind (lcoord t0) pp md0, base'))).
                   by rewrite -hr3.
                 move: hrtgj h2 => H1 H2; congruence. }
             rewrite hbase hrdg in hplace.
             rewrite hrdg in hsgus.
             have hsgc := hsgus.
             move: Edec; rewrite /lct_dec hrdg hsgc => Edec2.
             have hends' : lcompl (lcoord t0) pp
                 (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2)
                 mw.2.1
               = lcompl (lcoord t0) pp
                 (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c)
                 (wsigs (lcoord t0) pp 0
                    (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c) us).
               by rewrite hends hsgc.
             have [tw [v [hqn hnev hcol]]] :=
               l2_tcr_win (lcoord t0) pp md0 c us mw.1 mw.2.2 mw.2.1 jc u
                 hfc hus hvd hsz hends' hne Edec2.
             have hszlcq : size (lcq (lcoord t0) pp
                 (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c) us)
               = total_query_count w (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c).
               apply: size_lcq.
               by rewrite hus (size_digest_of PP D Hgrind
                    (lcoord t0).1 (lcoord t0).2 pp md0 c).
             have hjcbound : (jc < total_query_count w
                 (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp md0 c))%N.
               rewrite -hszlcq; exact: (qnth_size _ _ _ hqn).
             exists tw, v; split=> //.
             rewrite htg.
             have hq := qmap_from_get 0 Qc (base + jc)%N.
             rewrite add0n in hq; rewrite hq.
             rewrite (hplace jc hjcbound) qnth_map hqn /=.
             by rewrite /lwq. }
         move=> [tw [v [hgetm hnev hcol]]].
         rewrite hgetm.
         eapply (r_get_rhs_known Spp (Some pp)).
           { move=> s0 s1 [[[[[[hinv _] _] _] _] hpp] _].
             rewrite /rem_inv /= in hpp.
             case/ct_invE: hinv => _ [_ _ _ _ [hspp _ _]].
             by rewrite hspp hpp. }
         cbv beta iota.
         rewrite !th_eval_chtw -!surjective_pairing hnev hcol eqxx /=.
         apply r_ret => s0 s1 hpre; split; first by [].
         by case: hpre => [[[[[[hinv _] _] _] _] _] _].
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ct_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  rewrite ?code_link_assertD.
  eapply r_assertD_same => _.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  + eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          by move: (hRCT j); rewrite hr2 E /= -hr3.
        - by case: hm => he1 hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  + eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp base, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), (lfind (lcoord t0) pp md0, base))))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          move: (hRCT j); rewrite hr2 E => -[base [us [_ _ hrtgj0 _ _]]].
          exists pp, base; split; [by rewrite -hr4 El | by rewrite -hr3].
        - by case: hm => he1 _ _ _ _; move: E; rewrite -hr2 he1 emptymE. }
    move=> [pp [base [hlpp hrtgj]]].
    rewrite hlpp hrtgj /=.
    case E2: (find_ctr PP D Hgrind S_wn c_max
               (lcoord t0).1 (lcoord t0).2 pp md0) => [c|].
    * apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
      rewrite /rem_inv /= in hr0 hr1.
      subst s0 s1; split=> //.
      exact: (ct_inv_setsl (rcons slog j) s0' s1' hinv).
    * apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inl xy)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inr dc)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
Qed.

Lemma R_ctcr_leaf_ideal (hw : (0 < w)%N) :
  perfect IKM GM3 (R_ctcr_leaf ∘ SMB false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ct_inv).
{ rewrite /ct_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *)
  rewrite /rr_commit. ssprove_code_simpl; simpl. destruct arg as [t md].
  eapply r_get_remember_lhs => lrev. eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1]. case/ct_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1. by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev. eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws. eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1]. case/ct_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1. by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws. eapply r_assertD_same => hsz. eapply r_assertD_same => hfr.
  eapply rpre_weaken_rule with (pre := λ '(s0, s1), bpreT t ltws (s0, s1)).
  2:{ move=> s0 s1 H. case: H => [[[[hinv hrL] _] hr0] _].
      rewrite /rem_inv /= in hrL hr0. rewrite /bpreT; split; first exact: hinv.
      split; first by rewrite hrL (negbTE erev). split; first exact: hsz.
      split; first exact: hr0. exact: hfr. }
  eapply r_lct_pin_commit => pp. apply rpre_hypothesis_rule => s0 s1 hbcm.
  move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
  have [Q [hblk hsizeb hQcoord hRCT]] := ct_inv_lctblk pp s0 s1 hinv hlpp hrv.
  rewrite hltw in hblk hsizeb hQcoord.
  eapply rpre_weaken_rule with (pre := λ '(a, b),
     lctblk (Some pp) (get_heap s0 Lsl) ltws (get_heap s0 Ltg)
       (get_heap s1 rct_tgts_loc) (size Q)
       (Q ++ [seq lwq (lcoord t) q | q <- [::]]) (a, b)).
  2:{ move=> a b [ha hb]; move: ha hb => /= -> ->; rewrite cats0; exact: hblk. }
  eapply (r_lctgrind_spec false pp (lcoord t) md (iota 0 c_max) _).
    { move=> a b; exact: lctblk_Spp. }
  set hs := [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max].
  have hds : lct_digitS (size ltws) hs = l_rrdigS (lcoord t) pp md (size ltws).
    by rewrite /lct_digitS /l_rrdigS /hs lct_digit_E.
  have hcopt : omap fst (lct_pick hs) = lfind (lcoord t) pp md.
    by rewrite /hs lct_copt_E.
  rewrite hds hcopt.
  eapply (r_get_rhs_known rct_cnt_loc (size Q)). { move=> a b; exact: lctblk_cnt. }
  cbv beta.
  eapply (r_lctchains_spec false pp (lcoord t) (get_heap s0 Lsl) ltws
            (get_heap s0 Ltg) (get_heap s1 rct_tgts_loc) (size Q) _
            (l_rrdigS (lcoord t) pp md (size ltws)) 0 Q [::]).
  { exact: l2_lcoord_bounded. }
  { by rewrite add0n size_l_rrdigS. }
  { exact: wf_l_rrdigS. }
  { by []. }
  { rewrite cats0.
    apply: (leq_trans (leq_add hsizeb
              (nqs_le l w _ (size_l_rrdigS (lcoord t) pp md (size ltws))))).
    by rewrite -mulSnr; exact: leq_mul. }
  { exact: (coord_fresh ltws Q t hQcoord hfr'). }
  { by []. }
  move=> us hus. cbv beta iota.
  eapply (r_get_rhs_known Spp (Some pp)). { move=> a b; exact: lctblk_Spp. }
  cbv beta iota. rewrite decode_tweakK.
  rewrite (wendsEl (lcoord t) pp _ _ (size_l_rrdigS (lcoord t) pp md (size ltws))).
  apply: (r_lct_tail hw pp t md ltws us (get_heap s0 Lsl) (get_heap s0 Ltg)
            (get_heap s1 rct_tgts_loc) Q).
  { by rewrite hus size_l_rrdigS. }
  { exact: hQcoord. } { exact: hRCT. } { exact: hsizeb. }
  { exact: hsz'. } { exact: hfr'. }
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rct_pp_loc := Some b ;; #put rct_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (ct_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK *)
  destruct arg as [j mw].
  rewrite /rr_winbody.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ct_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  + eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          by move: (hRCT j); rewrite hr2 E /= -hr3.
        - by case: hm => he1 hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  + eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp base, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), (lfind (lcoord t0) pp md0, base))))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          move: (hRCT j); rewrite hr2 E => -[base [us [_ _ hrtgj0 _ _]]].
          exists pp, base; split; [by rewrite -hr4 El | by rewrite -hr3].
        - case: hm => _ _ _ _ [_ hlrvF].
          by move: hlrvF; rewrite hr0 erev. }
    move=> [pp [base [hlpp hrtgj]]].
    rewrite hlpp hrtgj /=.
    eapply (r_get_rhs_known rct_pp_loc (Some pp)).
      { move=> s0 s1 [[[[[hinv hrev] _] _] _] hpp].
        rewrite /rem_inv /= in hrev hpp.
        case/ct_invE: hinv => _ [_ _ _ hrpp _].
        by rewrite hrpp hrev erev /= hpp. }
    cbv beta iota.
    rewrite bind_ret_l.
    rewrite P_gm3_E.
    case Edec: (lct_dec pp t0 sg md0 j mw) => [[jc u]|]; last first.
    * (* CHAIN classifier absent: game [&& true], reduction = lct_v *)
      apply r_ret => s0 s1 hpre; split; first by rewrite andbT.
      by case: hpre => [[[[[hinv _] _] _] _] _].
    * case: ifP => hv.
      -- (* lct_v true: SMB-false CHECK = false; game = lct_v && false = false *)
         ssprove_code_simpl; simplify_linking.
         apply r_ret => s0 s1 hpre; split; first by [].
         by case: hpre => [[[[[hinv _] _] _] _] _].
      -- (* lct_v false: reduction = false; game = false && _ = false *)
         apply r_ret => s0 s1 hpre; split; first by [].
         by case: hpre => [[[[[hinv _] _] _] _] _].
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ct_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  rewrite ?code_link_assertD.
  eapply r_assertD_same => _.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  + eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          by move: (hRCT j); rewrite hr2 E /= -hr3.
        - by case: hm => he1 hre _ _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  + eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp base, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), (lfind (lcoord t0) pp md0, base))))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
        case/ct_invE: hinv => _ [_ _ _ _ [_ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - case: hm => Q [_ _ _ _ [_ hRCT]].
          move: (hRCT j); rewrite hr2 E => -[base [us [_ _ hrtgj0 _ _]]].
          exists pp, base; split; [by rewrite -hr4 El | by rewrite -hr3].
        - by case: hm => he1 _ _ _ _; move: E; rewrite -hr2 he1 emptymE. }
    move=> [pp [base [hlpp hrtgj]]].
    rewrite hlpp hrtgj /=.
    case E2: (find_ctr PP D Hgrind S_wn c_max
               (lcoord t0).1 (lcoord t0).2 pp md0) => [c|].
    * apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
      rewrite /rem_inv /= in hr0 hr1.
      subst s0 s1; split=> //.
      exact: (ct_inv_setsl (rcons slog j) s0' s1' hinv).
    * apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inl xy)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CFl_leaf pp t (inr (inr dc)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CFl_leaf.
Qed.

Lemma sub_ctcr (hw : (0 < w)%N) (B : nom_package)
    (VB : ValidPackage (loc B) IKM A_export B) :
  Adv GM2 GM3 B = AdvOf (SMTCR_game TFl CFl_leaf qF) (B ∘ R_ctcr_leaf).
Proof.
rewrite (Adv_perfect_l (R_ctcr_leaf_real hw)).
rewrite (Adv_perfect_r (R_ctcr_leaf_ideal hw)).
by rewrite Adv_reduction.
Qed.

End leaf2_chain_tcr.
