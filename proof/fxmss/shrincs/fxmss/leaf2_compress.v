(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.leaf2_compress

    The SM-TCR(Theta_l) compression sub-bound [Glmid1 -> Glmid2] in the
    second FXMSS leaf hop. It lifts the single-instance WOTS+C compression
    reduction to all leaves under the static gate [leaf_km.gateS] and the
    slot-keyed re-root digit [rr_digitS].

    The reduction requires the collection [CPl_leaf] to expose [F],
    [Htree], and [Hgrind]: LCOLLQ.inl computes Merkle nodes, while chain
    walks and grinding are also evaluated under the hidden [pp]. Its
    multi-target freshness invariant is stated over encoded public-key
    tweaks, because full structured-tweak inequality alone does not imply
    inequality after projecting to the leaf coordinate. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From HBS Require Import prelude math.bin_tree math.merkle math.chain math.encoding
  sig.scheme games.thf games.smtcr toolkit.sample_seq.
From HBS Require Import wots.scheme wots.games
  wots.analysis wots.tcr_hop.
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

Section leaf2_compress.

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
(** ** Shorthands.  [lcoord] (= adrs_keypair o decode) is imported from
    Leaf2Games (no section args). *)

Local Notation lcoord t := (@leaf_km.lcoord w l t).
Local Notation IKM  := (@I_MIW_km w l PP N D).

(** The leaf SM-TCR(Theta_l) target THF: Theta_l = Tl at the pk address. *)
Local Notation TPl := (Tpk PP N Tl dPP dN).

(** The collection needed by the compression reduction. It exposes
    F (internal chain walks), Htree (LCOLLQ.inl), Hgrind (grinding +
    LCOLLQ.inr) — all under the hidden pp.  [Cpk] (F + Hgrind only) cannot
    serve the exported LCOLLQ.inl (Htree). *)
Definition CPl_leaf : thf_coll TPl :=
  Build_thf_coll TPl adrs_sf_ch
    (N ∐ ((N × N) ∐ (D × 'nat)))
    (N ∐ (N ∐ 'nat))
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr (inl xy) => inr (inl (Htree pp (decode_tweak t) xy))
       | inr (inr dc) => inr (inr (Hgrind pp (decode_tweak t) dc))
       end).

Local Notation IMP := (I_SMTCR TPl CPl_leaf).

(** q1 = n_max committed leaf targets. *)
Local Notation q1 := n_max.

(** The pk-compression target tweak for leaf [t]: decodes to the pk address
    [shrincs_fxmss_wots_pk_adrs (lcoord t)], so [th_eval TPl pp (gtw_of t) xs = rr_pk]'s Tl
    call. *)
Local Notation gtw_of t :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (lcoord t))).
Local Notation grtw_of t :=
  (@encode_adrs l w (@shrincs_fxmss_wots_grind_adrs l w (lcoord t))).
Local Notation chtw_of t i k :=
  (@encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w (lcoord t) i k)).

Local Notation gprp := (@grind_prp w l S_wn).

(** Inlined re-root digit / pk (= leaf2_games.rr_digit / rr_pk at zi = lcoord t;
    inlined to avoid depending on the section-discharge signatures). *)
Definition l_rrdig (zi : nat * nat) (pp : PP) (md : D) : seq nat :=
  match find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md with
  | Some c => digest_of PP D Hgrind zi.1 zi.2 pp md c
  | None => nseq l w.-1
  end.

Definition l_rrpk (zi : nat * nat) (pp : PP) (md : D) (sg : seq N) : N :=
  Tl pp (shrincs_fxmss_wots_pk_adrs zi)
     (complete_ends PP N F zi.1 zi.2 pp (l_rrdig zi pp md) sg).

(** The SLOT-KEYED static digit / pk (= leaf2_games.rr_digitS / rr_pkS at
    zi = lcoord t): virtual [nseq l w.-1] for out-of-budget slots. *)
Definition l_rrdigS (zi : nat * nat) (pp : PP) (md : D) (j : nat) : seq nat :=
  l_rrdig zi pp md.

Definition l_rrpkS (zi : nat * nat) (pp : PP) (md : D) (j : nat)
    (sg : seq N) : N :=
  Tl pp (shrincs_fxmss_wots_pk_adrs zi)
     (complete_ends PP N F zi.1 zi.2 pp (l_rrdigS zi pp md j) sg).

(* ------------------------------------------------------------------ *)
(** ** Import opsigs. *)

Definition lcp_cqo : opsig := (COLLQ, (tc_T CPl_leaf × tc_M CPl_leaf, tc_N CPl_leaf)).
Definition lcp_tqo : opsig := (TQUERY, (th_T TPl × th_M TPl, th_N TPl)).
Definition lcp_gpo : opsig := (GETPP, ('unit, th_PP TPl)).
Definition lcp_cko : opsig := (CHECK, ('nat × th_M TPl, 'bool)).

(* ------------------------------------------------------------------ *)
(** ** The COLLQ-routed loops (mirror CompressHop's cp_grind/cp_walk/cp_chains
    at the leaf coordinate). *)

(** Grinding loop: one COLLQ (Hgrind member, [inr (inr _)]) per counter. *)
Fixpoint lcp_grind (zi : nat * nat) (md : D) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lcp_cqo (encode_adrs (shrincs_fxmss_wots_grind_adrs zi), inr (inr (md, c)))
        (λ r, hs ← lcp_grind zi md cs' ;;
              ret ((if r is inr (inr h) then h else 0) :: hs))
  end.

#[local] Instance lcp_grind_valid (L : Locations) zi md cs :
  ValidCode L IMP (lcp_grind zi md cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lcp_cqo; fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n] steps,
    one COLLQ (F member, [inl]) per step. *)
Fixpoint lcp_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr lcp_cqo (encode_adrs (shrincs_fxmss_wots_chain_adrs zi i k), inl x)
         (λ r, lcp_walk zi i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance lcp_walk_valid (L : Locations) zi i k n x :
  ValidCode L IMP (lcp_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lcp_cqo; fmap_solve.
  move=> r; exact: IH.
Qed.

(** All chains: per chain, sample root LOCALLY, one COLLQ F-step to the
    signature position (positive digit), walk upward; returns (sig values,
    completed ends). *)
Fixpoint lcp_chains (zi : nat * nat) (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1
           then opr lcp_cqo (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st d'), inl u)
                  (λ r, ret (if r is inl y then y else u))
           else ret u) ;;
      e ← lcp_walk zi st d (w.-1 - d) s ;;
      '(ss, es) ← lcp_chains zi st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance lcp_chains_valid (L : Locations) zi st ds :
  ValidCode L IMP (lcp_chains zi st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by rewrite /lcp_cqo; fmap_solve.
    move=> r; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: lcp_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(** The bounded grind search on the answer list (= scheme [find_ctr],
    re-rooted at the oracle answers). *)
Definition lcp_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 c_max) hs | gprp ch.2].

(** The re-root digit vector reconstructed from the grind answers. *)
Definition lcp_digit (hs : seq nat) : seq nat :=
  match lcp_pick hs with
  | Some ch => digits_w w l ch.2
  | None => nseq l w.-1
  end.

(** The SLOT-KEYED commit digit (= rr_digitS reconstructed at slot [j]). *)
Definition lcp_digitS (j : nat) (hs : seq nat) : seq nat :=
  lcp_digit hs.

(* ------------------------------------------------------------------ *)
(** ** The reduction package R_cp_leaf : package IMP IKM. *)

(** R's own state (610+, not 600+: 600-604 collide with leaf2_chain_tcr.v's
    rct_* at 600-605, see proof/LOCATIONS.md).  Mirrors Glmid1's
    (rev/tws/tgts/slog/pp); the tgts map additionally stores the find_ctr
    counter option [copt] (so LSIGN reveals it and LCHECK reads
    grindability). *)
Definition rcp_rev_loc  := mkloc 610 (false : bool).
Definition rcp_tws_loc  := mkloc 611 ([::] : seq adrs_sf_ch).
Definition rcp_tgts_loc :=
  mkloc 612 (emptym : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))}).
Definition rcp_slog_loc := mkloc 613 ([::] : seq nat).
Definition rcp_pp_loc   := mkloc 614 (None : option PP).

Local Notation RCPLocs :=
  [fmap rcp_rev_loc ; rcp_tws_loc ; rcp_tgts_loc ; rcp_slog_loc ; rcp_pp_loc ].

(** The LCHECK pure decision (the common P_gm1S/P_gm2S prefix [v] + the
    COMPRESS discriminant).  SLOG-FREE (M1a): the gate is the STATIC
    [leaf_km.gateS] read off the stored counter [copt] (= [find_ctr] at the
    committed digest, RCrel), the GRIND null is the simple [grind_hitS], and
    the re-root digit is slot-keyed on the map key [j]. *)
Definition lcp_v (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
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
  (verok && gate && ~~ ghit)%B.

Definition lcp_fcv (pp : PP) (t0 : adrs_sf_ch)
    (mw : D × (('list N) × 'nat)) : 'list N :=
  complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp
    (digest_of PP D Hgrind (lcoord t0).1 (lcoord t0).2 pp mw.1 mw.2.2) mw.2.1.

Definition lcp_rcv (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) : 'list N :=
  complete_ends PP N F (lcoord t0).1 (lcoord t0).2 pp
    (l_rrdigS (lcoord t0) pp md0 j) sg.

Definition R_cp_leaf : package IMP IKM.
Proof.
notypeclasses refine [package RCPLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) {
      revealed ← get rcp_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get rcp_tws_loc ;;
      #assert (size tws < n_max)%N ;;
      #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
      _ ← opr lcp_cqo (encode_adrs (shrincs_fxmss_wots_grind_adrs (lcoord t)), inr (inr (md, 0))) (λ r, ret r) ;;
      hs ← lcp_grind (lcoord t) md (iota 0 c_max) ;;
      '(sg, ends) ← lcp_chains (lcoord t) 0 (lcp_digitS (size tws) hs) ;;
      root ← opr lcp_tqo (gtw_of t, ends) (λ r, ret r) ;;
      tgts ← get rcp_tgts_loc ;;
      #put rcp_tgts_loc := setm tgts (size tws) (t, ((sg, md), omap fst (lcp_pick hs))) ;;
      #put rcp_tws_loc := rcons tws t ;;
      ret root
    } ;
    [ LGETPP ] : { 'unit ~> PP } (_) {
      pp ← opr lcp_gpo Datatypes.tt (λ p, ret p) ;;
      #put rcp_pp_loc := Some pp ;;
      #put rcp_rev_loc := true ;;
      ret pp
    } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      revealed ← get rcp_rev_loc ;;
      #assert revealed ;;
      tgts ← get rcp_tgts_loc ;;
      match getm tgts j with
      | Some (t0, ((sg, md0), copt)) =>
          ppo ← get rcp_pp_loc ;;
          pp ← match ppo with
               | Some pp => ret pp
               | None => pp ← dPP ;; #put rcp_pp_loc := Some pp ;; ret pp
               end ;;
          if lcp_v pp t0 sg md0 copt j mw
             && (lcp_fcv pp t0 mw != lcp_rcv pp t0 sg md0 j)
          then opr lcp_cko (j, lcp_fcv pp t0 mw) (λ ans, ret ans)
          else ret (lcp_v pp t0 sg md0 copt j mw)
      | None => ret false
      end
    } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) {
      slog ← get rcp_slog_loc ;;
      #assert (j \notin slog) ;;
      tgts ← get rcp_tgts_loc ;;
      match getm tgts j with
      | Some (t0, ((sg, md0), copt)) =>
          match copt with
          | Some c => #put rcp_slog_loc := rcons slog j ;; ret (Some (sg, c))
          | None => ret None
          end
      | None => ret None
      end
    } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      match x with
      | inl xy =>
          opr lcp_cqo (t, inr (inl xy))
            (λ r, ret (match r with inr (inl h) => inl h | _ => inl n0 end))
      | inr dc =>
          opr lcp_cqo (t, inr (inr dc))
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
          - eapply valid_opr; first by rewrite /lcp_cqo; fmap_solve.
            move=> r; apply valid_ret.
          - eapply valid_opr; first by rewrite /lcp_cqo; fmap_solve.
            move=> r; apply valid_ret. } }
      { (* LSIGN *)
        intro j.
        eapply valid_getr; first by fmap_solve. move=> slog.
        eapply valid_assertD => _.
        eapply valid_getr; first by fmap_solve. move=> tgts.
        case: (getm tgts j) => [[t0 [[sg md0] copt]]|]; last by apply valid_ret.
        case: copt => [c|]; last by apply valid_ret.
        eapply valid_putr; first by fmap_solve. apply valid_ret. } }
    { (* LCHECK *)
      intros [j mw].
      eapply valid_getr; first by fmap_solve. move=> revealed.
      eapply valid_assertD => _.
      eapply valid_getr; first by fmap_solve. move=> tgts.
      case: (getm tgts j) => [[t0 [[sg md0] copt]]|]; last by apply valid_ret.
      eapply valid_getr; first by fmap_solve. move=> ppo.
      eapply valid_bind.
        case: ppo => [pp|]; first by apply valid_ret.
        eapply valid_bind; first by eapply valid_scheme, prog_valid.
        move=> pp; eapply valid_putr; first by fmap_solve.
        apply valid_ret.
      move=> pp.
      case: ifP => _.
      - eapply valid_opr; first by rewrite /lcp_cko; fmap_solve.
        move=> ans; apply valid_ret.
      - apply valid_ret. } }
  { (* LGETPP *)
    intro u.
    eapply valid_opr; first by rewrite /lcp_gpo; fmap_solve.
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
    eapply valid_opr; first by rewrite /lcp_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> _.
  eapply valid_bind; first exact: lcp_grind_valid. move=> hs.
  eapply valid_bind; first exact: lcp_chains_valid. move=> [sg ends].
  eapply valid_bind.
    eapply valid_opr; first by rewrite /lcp_tqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> root.
  eapply valid_getr; first by fmap_solve. move=> tgts.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve. apply valid_ret. }
Defined.

(** Sanity: the reduction-build recipe lands — correct type, composes with an
    [I_MIW_km] adversary into a valid SM-TCR(Theta_l) adversary. *)

(* ------------------------------------------------------------------ *)
(** ** The COMPRESS sub-bound (ladder step Glmid1 -> Glmid2). *)

Local Notation GM1 := (Glmid1 PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation GM2 := (Glmid2 PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation SMB b := (SMTCR_game TPl CPl_leaf q1 b).

(* ================================================================== *)
(** ** Location shorthands (game / R / SM-TCR sides). *)

Local Notation Lpp := (miw_pp_loc PP).
Local Notation Ltg := (@mkm_tgts_loc w l N D).
Local Notation Ltw := (@miw_tws_loc w l).
Local Notation Lrv := miw_rev_loc.
Local Notation Lsl := miw_slog_loc.
Local Notation Spp := (tcr_pp_loc TPl).
Local Notation Stg := (tcr_tgts_loc TPl).
Local Notation Stw := (tcr_tws_loc TPl).
Local Notation Srv := tcr_rev_loc.

(** Leaf-coordinate chain shorthands (fixed_sum_scheme at the leaf [Fw]). *)
Local Notation FWl zi := (Fw PP N F zi.1 zi.2).
Local Notation cfWl zi := (HBS.wots.scheme.chainf PP N (FWl zi)).
Local Notation wsigs zi := (sigs_of PP N (FWl zi)).
Local Notation wends zi := (ends_of PP N (FWl zi) w).
Local Notation lfind zi pp md :=
  (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md).
Local Notation lcompl zi pp ds sg := (complete_ends PP N F zi.1 zi.2 pp ds sg).

(* ================================================================== *)
(** ** Resolve equations for the SM-TCR(Theta_l) oracles. *)

Lemma resolve_lcq (b : bool) (t : tc_T CPl_leaf) (x : tc_M CPl_leaf) :
  resolve (SMB b) lcp_cqo (t, x) =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   ret (tc_eval CPl_leaf pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_ltq (b : bool) (t : th_T TPl) (xs : th_M TPl) :
  resolve (SMB b) lcp_tqo (t, xs) =
  (revealed ← get Srv ;;
   #assert ~~ revealed ;;
   tws ← get Stw ;;
   #assert (size tws < q1)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get Stg ;;
   #put Stg := setm tgts (size tws) (t, xs) ;;
   #put Stw := rcons tws t ;;
   ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   ret (th_eval TPl pp t xs)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgp (b : bool) (u : unit) :
  resolve (SMB b) lcp_gpo u =
  (ppo ← get Spp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Spp := Some pp ;; ret pp
        end ;;
   #put Srv := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lck (j : nat) (xs : th_M TPl) :
  resolve (SMB true) lcp_cko (j, xs) =
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
       ret ((xs != m0) && (th_eval TPl pp t0 xs == th_eval TPl pp t0 m0))
   | None => ret false
   end).
Proof. by simplify_linking. Qed.

Lemma resolve_lck_false (j : nat) (xs : th_M TPl) :
  resolve (SMB false) lcp_cko (j, xs) = ret false.
Proof. by simplify_linking. Qed.

Lemma bind_getr {A B C : choiceType} (ℓ : Location) (f : ℓ -> raw_code A)
    (k : A -> raw_code B) :
  bind (x ← get ℓ ;; f x) k = (x ← get ℓ ;; bind (f x) k).
Proof. by []. Qed.

(** Push a continuation through the [Spp] lazy-read prefix (monad laws). *)
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
rewrite bind_getr. unshelve setoid_rewrite bind_assoc.
2: exact: A.
exact: erefl.
Qed.

(** Push the COLLQ post-projection through the lazy read (the linked SM-TCR
    COLLQ leaves [get Spp ;; b ← (lazy ;; ret (a pp)) ;; k b]). *)
Lemma collq_rhs_E {B : choiceType} (a : PP -> tc_N CPl_leaf)
    (k : tc_N CPl_leaf -> raw_code B) :
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

(** General bind-push through the [Spp] lazy read (covers LGETPP's embedded
    [put Srv]). *)
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
#[local] Arguments lcp_pick : simpl never.
#[local] Arguments l_rrdig : simpl never.
#[local] Arguments l_rrdigS : simpl never.
#[local] Arguments lcp_digitS : simpl never.

(* ================================================================== *)
(** ** Conversion bridges (canonical tweaks compute). *)

Lemma collq_H_E (pp : PP) (zi : nat * nat) (md : D) (c : nat) :
  (if tc_eval CPl_leaf pp (encode_adrs (shrincs_fxmss_wots_grind_adrs zi)) (inr (inr (md, c)))
      is inr (inr h) then h else 0)
  = Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c).
Proof. by rewrite /tc_eval /CPl_leaf decode_tweakK. Qed.

Lemma collq_F_E (pp : PP) (zi : nat * nat) (i k : nat) (x : N) :
  (if tc_eval CPl_leaf pp (encode_adrs (shrincs_fxmss_wots_chain_adrs zi i k)) (inl x)
      is inl y then y else x)
  = F pp (shrincs_fxmss_wots_chain_adrs zi i k) x.
Proof. by rewrite /tc_eval /CPl_leaf decode_tweakK. Qed.

(** The picked grinding result on the honest answer list IS the scheme's
    [find_ctr] re-rooted at the answers. *)
Lemma lcp_zip_filter (f : nat -> nat) (P : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | P ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | P (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (P (f c)) => /=; [|exact: IH].
Qed.

Lemma lcp_pick_map (pp : PP) (zi : nat * nat) (md : D) :
  lcp_pick [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = omap (fun c => (c, Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c))) (lfind zi pp md).
Proof.
rewrite /lcp_pick lcp_zip_filter /find_ctr.
have hf :
  [seq c <- iota 0 c_max
   | @grind_prp w l S_wn (Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c))]
  = [seq c <- iota 0 c_max | good_ctr PP D Hgrind S_wn zi.1 zi.2 pp md c].
  by apply: eq_filter => c;
     rewrite /grind_prp /good_ctr /valid_digest /digest_of.
by rewrite hf.
Qed.

Lemma lcp_digit_E (pp : PP) (zi : nat * nat) (md : D) :
  lcp_digit [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = (match lfind zi pp md with
     | Some c => digest_of PP D Hgrind zi.1 zi.2 pp md c
     | None => nseq l w.-1
     end).
Proof.
rewrite /lcp_digit lcp_pick_map.
by case: (lfind zi pp md) => [c|].
Qed.

Lemma lcp_copt_E (pp : PP) (zi : nat * nat) (md : D) :
  omap fst (lcp_pick [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max])
  = lfind zi pp md.
Proof. by rewrite lcp_pick_map; case: (lfind zi pp md) => [c|]. Qed.

(* ================================================================== *)
(** ** The all-private location set + the per-target relation. *)

Definition IGNC : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rcp_pp_loc ; rcp_tgts_loc ; rcp_tws_loc ; rcp_rev_loc ; rcp_slog_loc ;
        Spp ; Stg ; Stw ; Srv ].

(** The per-index coherence of the three target tables (game / R / SM-TCR). *)
Definition RCrel (pp : PP)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (stg : {fmap nat -> (th_T TPl × th_M TPl)}) : Prop :=
  forall j,
    match getm ltg j with
    | Some (t0, (sg, md0)) =>
        getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0))
        /\ getm stg j
           = Some (encode_adrs (shrincs_fxmss_wots_pk_adrs (lcoord t0)),
                   lcompl (lcoord t0) pp (l_rrdigS (lcoord t0) pp md0 j) sg)
    | None => getm rtg j = None /\ getm stg j = None
    end.

Lemma RCrel_empty (pp : PP) : RCrel pp emptym emptym emptym.
Proof. by move=> j; rewrite !emptymE. Qed.

(** Extend all three tables at a common index [k] (the COMMIT update). *)
Lemma RCrel_qupd (pp : PP) (t : adrs_sf_ch) (md : D) (sg : seq N)
    (k : nat) ltg rtg stg :
  RCrel pp ltg rtg stg ->
  RCrel pp (setm ltg k (t, (sg, md)))
           (setm rtg k (t, ((sg, md), lfind (lcoord t) pp md)))
           (setm stg k (encode_adrs (shrincs_fxmss_wots_pk_adrs (lcoord t)),
                        lcompl (lcoord t) pp (l_rrdigS (lcoord t) pp md k) sg)).
Proof.
move=> H j.
have [->|hjk] := eqVneq j k.
- rewrite setmE eqxx /=; split; by rewrite setmE eqxx.
- rewrite setmE (negbTE hjk) !setmE (negbTE hjk).
  exact: H j.
Qed.

(* ================================================================== *)
(** ** The block precondition (inside an oracle, machinery dropped). *)

Definition lcblk (po : option PP) (lrv : bool) (lsl : seq nat)
    (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (stg : {fmap nat -> (th_T TPl × th_M TPl)}) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNC (s0, s1),
      [/\ get_heap s0 Lpp = po, get_heap s0 Lrv = lrv, get_heap s0 Lsl = lsl,
          get_heap s0 Ltw = ltw & get_heap s0 Ltg = ltg],
      [/\ get_heap s1 rcp_pp_loc = (if lrv then po else None),
          get_heap s1 rcp_rev_loc = lrv, get_heap s1 rcp_slog_loc = lsl,
          get_heap s1 rcp_tws_loc = ltw & get_heap s1 rcp_tgts_loc = rtg],
      [/\ get_heap s1 Spp = po, get_heap s1 Srv = lrv,
          get_heap s1 Stw = [seq gtw_of x | x <- ltw] & get_heap s1 Stg = stg]
    & match po with
      | None => [/\ ltg = emptym, rtg = emptym & stg = emptym]
      | Some pp => RCrel pp ltg rtg stg
      end].

Arguments lcblk : simpl never.
(* ================================================================== *)
(** ** The top-level invariant (heap_ignore + rel_app RC). *)

Definition RC
    (lpp : option PP) (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (ltw : seq adrs_sf_ch) (lrv : bool) (lsl : seq nat)
    (rpp : option PP)
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (rtw : seq adrs_sf_ch) (rrv : bool) (rsl : seq nat)
    (spp : option (th_PP TPl)) (stg : {fmap nat -> (th_T TPl × th_M TPl)})
    (stw : seq (th_T TPl)) (srv : bool) : Prop :=
  [/\ rtw = ltw, rrv = lrv, rsl = lsl, rpp = (if lrv then lpp else None)
    & [/\ spp = lpp, srv = lrv, stw = [seq gtw_of x | x <- ltw]
      & match lpp with
        | None => [/\ ltg = emptym, rtg = emptym, stg = emptym & lrv = false]
        | Some pp => RCrel pp ltg rtg stg
        end]].

Definition cp_inv : precond :=
  heap_ignore IGNC
  ⋊ rel_app [:: (lhs, Lpp) ; (lhs, Ltg) ; (lhs, Ltw) ; (lhs, Lrv) ; (lhs, Lsl) ;
                (rhs, rcp_pp_loc) ; (rhs, rcp_tgts_loc) ; (rhs, rcp_tws_loc) ;
                (rhs, rcp_rev_loc) ; (rhs, rcp_slog_loc) ;
                (rhs, Spp) ; (rhs, Stg) ; (rhs, Stw) ; (rhs, Srv) ] RC.

Arguments cp_inv : simpl never.

Lemma cp_invE s0 s1 :
  cp_inv (s0, s1) ->
  heap_ignore IGNC (s0, s1) /\
  RC (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rcp_pp_loc) (get_heap s1 rcp_tgts_loc) (get_heap s1 rcp_tws_loc)
     (get_heap s1 rcp_rev_loc) (get_heap s1 rcp_slog_loc)
     (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv).
Proof. by move=> [h1 h2]; split. Qed.

Lemma cp_invI s0 s1 :
  heap_ignore IGNC (s0, s1) ->
  RC (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rcp_pp_loc) (get_heap s1 rcp_tgts_loc) (get_heap s1 rcp_tws_loc)
     (get_heap s1 rcp_rev_loc) (get_heap s1 rcp_slog_loc)
     (get_heap s1 Spp) (get_heap s1 Stg) (get_heap s1 Stw) (get_heap s1 Srv) ->
  cp_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** The pinned invariant, as a SINGLE applied atom (so generic rules like
    [r_put_lhs] unify the precond first-order). *)
Definition cp_invL (pp : PP) : precond :=
  λ '(s0, s1), cp_inv (s0, s1) /\ get_heap s0 Lpp = Some pp.

Arguments cp_invL : simpl never.


(* ================================================================== *)
(** ** Stepping one linked COLLQ (pp pinned). *)

Lemma r_lcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CPl_leaf) (x : tc_M CPl_leaf) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : tc_N CPl_leaf -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CPl_leaf pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) lcp_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lcq b t x).
eapply (r_get_bind_rhs Spp (Some pp)); first exact: hpp.
cbv beta iota.
exact: h.
Qed.

(* ================================================================== *)
(** ** The loop specs (rhs-only grind/walk; two-sided chains). *)

Lemma r_lcgrind_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (md : D) (cs : seq nat) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lcp_grind zi md cs) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lcollq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

Lemma r_lcwalk_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Spp = Some pp)
    (post : postcond B B) :
  forall n i k (x : N)
         (c0 : raw_code B) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (chain (cfWl zi pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lcp_walk zi i k n x) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lcollq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_F_E.
  exact: IH.
Qed.

Lemma r_lcchains_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
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
   ≈ bind (code_link (lcp_chains zi st ds) (SMB b)) K1 ⦃ post ⦄.
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
    eapply (r_lcwalk_spec b pp zi pre hpp post (w.-1 - 0) st 0 u).
    rewrite (code_link_bind (lcp_chains zi st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
  + rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_lcollq_known b pp _ _ pre hpp).
    cbv beta.
    rewrite collq_F_E /=.
    rewrite (code_link_bind (lcp_walk zi st d'.+1 (w.-1 - d'.+1)
              (F pp (shrincs_fxmss_wots_chain_adrs zi st d') u))) bind_assoc.
    eapply (r_lcwalk_spec b pp zi pre hpp post (w.-1 - d'.+1) st d'.+1
              (F pp (shrincs_fxmss_wots_chain_adrs zi st d') u)).
    rewrite /= (code_link_bind (lcp_chains zi st.+1 ds)) bind_assoc.
    eapply IH => us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
Qed.

Lemma wendsEl (zi : nat * nat) pp (ds : seq nat) (ys : seq N) :
  size ds = l -> wends zi pp 0 ds ys = lcompl zi pp ds ys.
Proof.
move=> h.
by rewrite (ends_of_from_sig PP N (FWl zi) l w pp ds ys h)
   (wcendsE PP N F zi.1 zi.2).
Qed.


(* ================================================================== *)
(** ** Block-precondition updates. *)

Lemma bind_put_ret {A B : choiceType} (ℓ : Location) (v : ℓ) (a : A)
    (k : A -> raw_code B) :
  bind (#put ℓ := v ;; ret a) k = (#put ℓ := v ;; k a).
Proof. by []. Qed.

Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

Lemma lcblk_set_both_pp (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk None false lsl ltw ltg rtg stg (s0, s1) ->
  lcblk (Some pp) false lsl ltw ltg rtg stg
    (set_heap s0 Lpp (Some pp), set_heap s1 Spp (Some pp)).
Proof.
move=> [h0 [h1 h2 h3 h4 h5] [h6 h7 h8 h9 h10] [h11 h12 h13 h14] hm].
case: hm => he1 he2 he3; split.
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
         | by rewrite get_set_heap_neq | by rewrite get_set_heap_neq].
- by rewrite he1 he2 he3; exact: RCrel_empty.
Qed.

(** A [Some pp] block precondition IS the invariant. *)
Lemma lcblk_cp_inv (pp : PP) lrv lsl ltw ltg rtg stg s0 s1 :
  lcblk (Some pp) lrv lsl ltw ltg rtg stg (s0, s1) -> cp_inv (s0, s1).
Proof.
move=> [hign [hLpp hLrv hLsl hLtw hLtg] [hrpp hrrv hrsl hrtw hrtg]
        [hSpp hSrv hStw hStg] hm].
apply: cp_invI; first exact: hign.
rewrite /RC hLpp hLrv hLsl hLtw hLtg hrpp hrrv hrsl hrtw hrtg
        hSpp hSrv hStw hStg.
by split=> //; split=> //.
Qed.

(** The invariant gives the block precondition (any [po]) once [rev = false]. *)
Lemma cp_inv_lcblk s0 s1 :
  cp_inv (s0, s1) -> get_heap s0 Lrv = false ->
  lcblk (get_heap s0 Lpp) false (get_heap s0 Lsl) (get_heap s0 Ltw)
        (get_heap s0 Ltg) (get_heap s1 rcp_tgts_loc) (get_heap s1 Stg) (s0, s1).
Proof.
move=> hinv hrv.
case/cp_invE: hinv => hign hRC.
case: hRC => hrtw hrrv hrsl hrpp [hspp hsrv hstw hm].
split.
- exact: hign.
- by [].
- by split=> //; rewrite ?hrpp ?hrrv hrv.
- by split=> //; rewrite ?hsrv hrv.
- move: hm; case: (get_heap s0 Lpp) => [pp|] hm; first exact: hm.
  by case: hm => he1 he2 he3 _; split.
Qed.

(** Pin [pp] on both [Lpp] and [Spp] (from [None]); preserves the invariant. *)
Lemma cp_inv_pin (pp : PP) s0 s1 :
  cp_inv (s0, s1) -> get_heap s0 Lpp = None ->
  cp_inv (set_heap s0 Lpp (Some pp), set_heap s1 Spp (Some pp)).
Proof.
move=> hinv hL.
have hrv : get_heap s0 Lrv = false.
  case/cp_invE: hinv => _ hRC.
  by move: hRC; rewrite hL => -[_ _ _ _ [_ _ _ [_ _ _ ->]]].
have hblk := cp_inv_lcblk s0 s1 hinv hrv.
move: hblk; rewrite hL => hblk.
apply: (lcblk_cp_inv pp false (get_heap s0 Lsl) (get_heap s0 Ltw)
          (get_heap s0 Ltg) (get_heap s1 rcp_tgts_loc) (get_heap s1 Stg)).
exact: (lcblk_set_both_pp pp _ _ _ _ _ s0 s1 hblk).
Qed.

(** GETPP: reveal pp (rev false -> true), R copies pp into its own pp loc. *)
Lemma cp_inv_reveal (pp : PP) s0 s1 :
  cp_inv (s0, s1) -> get_heap s0 Lpp = Some pp ->
  cp_inv (set_heap s0 Lrv true,
          set_heap (set_heap (set_heap s1 Srv true) rcp_pp_loc (Some pp))
            rcp_rev_loc true).
Proof.
move=> hinv hL.
case/cp_invE: hinv => hign hRC.
move: hRC; rewrite hL => -[hrtw hrrv hrsl hrpp [hspp hsrv hstw hm]].
apply: cp_invI.
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
  set S1 := set_heap (set_heap (set_heap s1 Srv true) rcp_pp_loc (Some pp))
                     rcp_rev_loc true.
  have e_rpp : get_heap S1 rcp_pp_loc = Some pp
    by rewrite /S1 get_set_heap_neq // get_set_heap_eq.
  have e_rtg : get_heap S1 rcp_tgts_loc = get_heap s1 rcp_tgts_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_rtw : get_heap S1 rcp_tws_loc = get_heap s1 rcp_tws_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_rrv : get_heap S1 rcp_rev_loc = true
    by rewrite /S1 get_set_heap_eq.
  have e_rsl : get_heap S1 rcp_slog_loc = get_heap s1 rcp_slog_loc
    by rewrite /S1 !get_set_heap_neq.
  have e_Spp : get_heap S1 Spp = get_heap s1 Spp
    by rewrite /S1 !get_set_heap_neq.
  have e_Stg : get_heap S1 Stg = get_heap s1 Stg
    by rewrite /S1 !get_set_heap_neq.
  have e_Stw : get_heap S1 Stw = get_heap s1 Stw
    by rewrite /S1 !get_set_heap_neq.
  have e_Srv : get_heap S1 Srv = true
    by rewrite /S1 get_set_heap_neq // get_set_heap_neq // get_set_heap_eq.
  rewrite /RC -/S1 e_Lpp e_Ltg e_Ltw e_Lrv e_Lsl
    e_rpp e_rtg e_rtw e_rrv e_rsl e_Spp e_Stg e_Stw e_Srv.
  by rewrite hrtw hrsl hstw hspp; split=> //; split.
Qed.

(** LSIGN: set [Lsl] and [rcp_slog] to the same value; preserves the invariant. *)
Lemma cp_inv_setsl (vw : seq nat) s0 s1 :
  cp_inv (s0, s1) ->
  cp_inv (set_heap s0 Lsl vw, set_heap s1 rcp_slog_loc vw).
Proof.
move=> hinv.
case/cp_invE: hinv => hign hRC.
case: hRC => hrtw hrrv hrsl hrpp [hspp hsrv hstw hm].
apply: cp_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RC
    [get_heap (set_heap s0 Lsl vw) Lpp]get_set_heap_neq //
    [get_heap (set_heap s0 Lsl vw) Ltg]get_set_heap_neq //
    [get_heap (set_heap s0 Lsl vw) Ltw]get_set_heap_neq //
    [get_heap (set_heap s0 Lsl vw) Lrv]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) rcp_pp_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) rcp_tgts_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) rcp_tws_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) rcp_rev_loc]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) Spp]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) Stg]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) Stw]get_set_heap_neq //
    [get_heap (set_heap s1 rcp_slog_loc vw) Srv]get_set_heap_neq //
    !get_set_heap_eq.
  by rewrite hrtw hrrv hrpp hspp hsrv hstw; split=> //; split.
Qed.


(** Couple the two lazy [pp] reads (game [Lpp] vs SM-TCR [Spp]); land in a
    per-[pp] goal under the invariant with [Lpp] pinned. *)
Lemma r_pp2 {B : choiceType} (k0 k1 : PP -> raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), cp_invL pp (s0, s1) ⦄
                 k0 pp ≈ k1 pp ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), cp_inv (s0, s1) ⦄
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
    case/cp_invE: hinv => _ [_ _ _ _ [hsp _ _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hsp hr0. }
move=> e; subst spp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv hr0] hr1].
  rewrite /rem_inv /= in hr0.
  rewrite /cp_invL /=.
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
  subst s0 s1; rewrite /cp_invL /=; split.
  + exact: (cp_inv_pin pp s0' s1' hinv hr0).
  + by rewrite get_set_heap_eq.
Qed.

(* ================================================================== *)
(** ** The pin: couple the game's lazy [pp] with SM-TCR's at the COLLQ pin. *)

Lemma r_lpin (b : bool) {B : choiceType} (po : option PP) lsl ltw ltg rtg stg
    (zi : nat * nat) (md : D)
    (k0 : PP -> raw_code B) (k1 : raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), lcblk (Some pp) false lsl ltw ltg rtg stg (s0, s1) ⦄
                 k0 pp ≈ k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lcblk po false lsl ltw ltg rtg stg (s0, s1) ⦄
     (ppo ← get Lpp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
           end ;;
      k0 pp)
   ≈ bind (resolve (SMB b) lcp_cqo
             (encode_adrs (shrincs_fxmss_wots_grind_adrs zi), inr (inr (md, 0)))) (fun=> k1)
  ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lcq b _ _).
case: po h => [pp0|] h.
- eapply (r_get_lhs_known Lpp (Some pp0)).
    { by move=> s0 s1 [_ [hh _ _ _ _] _ _ _]. }
  eapply (r_get_bind_rhs Spp (Some pp0)).
    { by move=> s0 s1 [_ _ _ [hh _ _ _] _]. }
  cbv beta iota.
  exact: (h pp0).
- eapply (r_get_lhs_known Lpp None).
    { by move=> s0 s1 [_ [hh _ _ _ _] _ _ _]. }
  eapply (r_get_bind_rhs Spp None).
    { by move=> s0 s1 [_ _ _ [hh _ _ _] _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite !bind_put_ret.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [hpre e0]] e1]]; subst s0 s1.
  exact: (lcblk_set_both_pp pp lsl ltw ltg rtg stg s0' s1' hpre).
Qed.

(* ================================================================== *)
(** ** The COMMIT block (carry pp + Ltw + the SM-TCR freshness). *)

Definition bcm (pp : PP) (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  cp_inv (s0, s1) /\ get_heap s0 Lpp = Some pp /\ get_heap s0 Lrv = false /\
  (size ltw < n_max)%N /\ get_heap s0 Ltw = ltw /\
  gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments bcm : simpl never.

(** The pre-pin atom (before [Lpp] is read). *)
Definition bpre (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  cp_inv (s0, s1) /\ get_heap s0 Lrv = false /\ (size ltw < n_max)%N /\
  get_heap s0 Ltw = ltw /\ gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments bpre : simpl never.

Lemma bcm_Spp (pp : PP) t ltw s0 s1 :
  bcm pp t ltw (s0, s1) -> get_heap s1 Spp = Some pp.
Proof.
move=> [hinv [hlpp _]]; case/cp_invE: hinv => _ [_ _ _ _ [hspp _ _ _]].
by rewrite hspp hlpp.
Qed.

(** The COMMIT pin: couple the game's lazy [Lpp] with the leading COLLQ pin's
    lazy [Spp] (in the [ssprove_code_simpl]-inlined form), landing in
    [bcm pp t ltw]. *)
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
    case/cp_invE: hinv => _ [_ _ _ _ [hsp _ _ _]].
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
  + exact: (cp_inv_pin pp s0' s1' hinv hr0).
  + split; first by rewrite get_set_heap_eq.
    split; first by rewrite get_set_heap_neq.
    split; first exact: hsz.
    split; first by rewrite get_set_heap_neq.
    exact: hfr.
Qed.

(** The Glmid1 win predicate IS [lcp_v] at the stored counter [find_ctr]:
    [grind_hitS]/[ghit], [gateS]/[gate], [verokS], [rr_pkS]/[l_rrpkS],
    [rr_digitS]/[l_rrdigS] all agree by conversion. *)
Lemma P_gm1_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_gm1S PP N D F Tl Hgrind S_wn c_max pp t0 sg md0 j mw
  = lcp_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw.
Proof.
rewrite /P_gm1S /lcp_v /grind_hitS /leaf_km.gateL /l_rrpkS /l_rrdigS /l_rrdig
        /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c.
by rewrite andbA.
Qed.

(** The Glmid2 win predicate is [lcp_v] AND-ed with the COMPRESS conjunct
    [fcv == rcv] (so the COMPRESS route — where [fcv != rcv] — is nulled). *)
Lemma P_gm2_E (pp : PP) (t0 : adrs_sf_ch) (sg : 'list N) (md0 : D)
    (j : nat) (mw : D × (('list N) × 'nat)) :
  P_gm2S PP N D F Tl Hgrind S_wn c_max pp t0 sg md0 j mw
  = lcp_v pp t0 sg md0 (lfind (lcoord t0) pp md0) j mw
    && (lcp_fcv pp t0 mw == lcp_rcv pp t0 sg md0 j).
Proof.
rewrite /P_gm2S /lcp_v /grind_hitS /leaf_km.gateL /l_rrpkS /l_rrdigS /l_rrdig
        /rr_pkS /rr_digitS /rr_digit /rr_F /leaf_rec_c /lcp_fcv /lcp_rcv.
by rewrite !andbA.
Qed.

(** Projections from a [Some pp] block precondition (standalone, so the
    honesty gate's no-[Hypothesis] rule is respected). *)
Notation lcblk_pre pp lsl ltw ltg rtg stg s0 s1 :=
  (lcblk (Some pp) false lsl ltw ltg rtg stg (s0, s1)).

Lemma lcblk_ign (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> heap_ignore IGNC (s0, s1).
Proof. by case. Qed.
Lemma lcblk_Ltg (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> get_heap s0 Ltg = ltg.
Proof. by case=> _ [_ _ _ _ ?]. Qed.
Lemma lcblk_Srv (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> get_heap s1 Srv = false.
Proof. by case=> _ _ _ [_ ? _ _] _. Qed.
Lemma lcblk_Stw (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 ->
  get_heap s1 Stw = [seq gtw_of x | x <- ltw].
Proof. by case=> _ _ _ [_ _ ? _] _. Qed.
Lemma lcblk_Stg (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> get_heap s1 Stg = stg.
Proof. by case=> _ _ _ [_ _ _ ?] _. Qed.
Lemma lcblk_Spp (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> get_heap s1 Spp = Some pp.
Proof. by case=> _ _ _ [? _ _ _] _. Qed.
Lemma lcblk_rtg (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> get_heap s1 rcp_tgts_loc = rtg.
Proof. by case=> _ _ [_ _ _ _ ?] _ _. Qed.
Lemma lcblk_RC (pp : PP) lsl ltw ltg rtg stg s0 s1 :
  lcblk_pre pp lsl ltw ltg rtg stg s0 s1 -> RCrel pp ltg rtg stg.
Proof. by case=> _ _ _ _. Qed.

(** The COMMIT tail: store on both sides + the ONE inlined TQUERY; the
    invariant is re-established from the final block. *)
Lemma r_lcp_tail (pp : PP) (t : adrs_sf_ch) (md : D)
    (ltws : seq adrs_sf_ch) (sg : seq N) (lsl : seq nat)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (stg : {fmap nat -> (th_T TPl × th_M TPl)}) :
  (size ltws < n_max)%N ->
  gtw_of t \notin [seq gtw_of x | x <- ltws] ->
  RCrel pp ltg rtg stg ->
  ⊢ ⦃ λ '(s0, s1), lcblk (Some pp) false lsl ltws ltg rtg stg (s0, s1) ⦄
     (tgts ← get Ltg ;;
      #put Ltg := setm tgts (size ltws) (t, (sg, md)) ;;
      #put Ltw := rcons ltws t ;;
      ret (rr_pkS PP N D F Tl Hgrind S_wn c_max pp t md (size ltws) sg))
   ≈ (v ← get Srv ;;
      b ← (#assert ~~ v ;;
           tws ← get Stw ;;
           #assert (size tws < n_max)%N ;;
           #assert (gtw_of t \notin tws) ;;
           tgts ← get Stg ;;
           #put Stg := setm tgts (size tws)
                         (gtw_of t,
                          lcompl (lcoord t) pp
                            (rr_digitS PP D Hgrind S_wn c_max pp t md
                               (size ltws)) sg) ;;
           #put Stw := rcons tws (gtw_of t) ;;
           ppo ← get Spp ;;
           match ppo with
           | Some s => ret (th_eval TPl s (gtw_of t)
                             (lcompl (lcoord t) pp
                               (rr_digitS PP D Hgrind S_wn c_max pp t md
                                  (size ltws)) sg))
           | None => x ← dPP ;; #put Spp := Some x ;;
                     ret (th_eval TPl x (gtw_of t)
                            (lcompl (lcoord t) pp
                              (rr_digitS PP D Hgrind S_wn c_max pp t md
                                 (size ltws)) sg))
           end) ;;
      x6 ← get rcp_tgts_loc ;;
      #put rcp_tgts_loc := setm x6 (size ltws)
                             (t, (sg, md, lfind (lcoord t) pp md)) ;;
      #put rcp_tws_loc := rcons ltws t ;;
      ret b)
   ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ cp_inv (s0, s1) ⦄.
Proof.
move=> hsz hfr hRC.
pose B0 := λ '(s0, s1), lcblk (Some pp) false lsl ltws ltg rtg stg (s0, s1).
eapply (r_get_rhs_known Srv false B0).
  { move=> s0 s1; exact: lcblk_Srv. }
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs Stw [seq gtw_of x | x <- ltws] B0).
  { move=> s0 s1; exact: lcblk_Stw. }
cbv beta.
eapply r_bind_assertD_rhs.
  { move=> s0 s1 _; by rewrite size_map. }
move=> _.
eapply r_bind_assertD_rhs.
  { move=> s0 s1 _; exact: hfr. }
move=> _.
eapply (r_get_bind_rhs Stg stg B0).
  { move=> s0 s1; exact: lcblk_Stg. }
cbv beta.
(* the two SM-TCR puts: thread the original block via a set_rhs wrapper *)
pose B1 := λ '(s0, s1),
  exists s1o,
    B0 (s0, s1o) /\
    s1 = set_heap (set_heap s1o Stg
            (setm stg (size [seq gtw_of x | x <- ltws])
               (gtw_of t,
                lcompl (lcoord t) pp
                  (rr_digitS PP D Hgrind S_wn c_max pp t md
                     (size ltws)) sg)))
            Stw (rcons [seq gtw_of x | x <- ltws] (gtw_of t)).
eapply (r_put2_bind_rhs Stg _ Stw _ B0 B1).
  { move=> s0 s1 hb; rewrite /B1 /=; exists s1; split=> //. }
eapply (r_get_bind_rhs Spp (Some pp) B1).
  { move=> s0 s1 [s1o [hb ->]].
    rewrite get_set_heap_neq // get_set_heap_neq //.
    exact: (lcblk_Spp _ _ _ _ _ _ _ _ hb). }
cbv beta iota.
rewrite bind_ret_l.
eapply (r_get_rhs_known rcp_tgts_loc rtg B1).
  { move=> s0 s1 [s1o [hb ->]].
    rewrite get_set_heap_neq // get_set_heap_neq //.
    exact: (lcblk_rtg _ _ _ _ _ _ _ _ hb). }
apply r_put_rhs; apply r_put_rhs.
eapply (r_get_lhs_known Ltg ltg).
  { move=> s0 s1 [s1a [[s1b [[s1o [hb _]] _]] _]].
    exact: (lcblk_Ltg _ _ _ _ _ _ _ _ hb). }
apply r_put_lhs; apply r_put_lhs.
apply r_ret => s0 s1 hpre.
move: hpre =>
  [s0a [[s0b [[s1a [[s1b [[s1o [hb e4]] e3]] e2]] e1]] e0]].
subst s0 s0a s1 s1a s1b.
case: hb => hign [hLpp hLrv hLsl hLtw hLtg]
              [hrpp hrrv hrsl hrtw hrtg] [hSpp hSrv hStw hStg] _.
split.
- by rewrite /rr_pkS (th_evalE_Tpk PP N Tl dPP dN).
- apply: cp_invI.
  + apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign.
  + rewrite /RC.
    get_heap_simpl.
    rewrite hLpp hLrv hLsl hrpp hrrv hrsl hSpp hSrv.
    split=> //; split=> //.
    * by rewrite map_rcons.
    * rewrite (_ : size [seq gtw_of x | x <- ltws] = size ltws);
        last by rewrite size_map.
      exact: (RCrel_qupd pp t md sg (size ltws) ltg rtg stg hRC).
Qed.

(** The two perfect equivalences (perfect-routing recipe). *)
Lemma R_cp_leaf_real : perfect IKM GM1 (R_cp_leaf ∘ SMB true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ cp_inv).
{ rewrite /cp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *) rewrite /rr_commit.
  ssprove_code_simpl; simpl.
  destruct arg as [t md].
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/cp_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws.
  eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/cp_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws.
  eapply r_assertD_same => hsz.
  eapply r_assertD_same => hfr.
  eapply rpre_weaken_rule with (pre := λ '(s0, s1), bpre t ltws (s0, s1)).
  + eapply r_pin_commit => pp.
    eapply (r_lcgrind_spec true pp (lcoord t) md (iota 0 c_max)
              (bcm pp t ltws) (bcm_Spp pp t ltws)).
    set hs := [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max].
    have hds : lcp_digitS (size ltws) hs
             = rr_digitS PP D Hgrind S_wn c_max pp t md (size ltws).
      rewrite /lcp_digitS /rr_digitS.
      by rewrite /hs lcp_digit_E /rr_digit.
    have hcopt : omap fst (lcp_pick hs) = lfind (lcoord t) pp md.
      by rewrite /hs lcp_copt_E.
    rewrite hds hcopt.
    rewrite /rr_F.
    eapply (r_lcchains_spec true pp (lcoord t)
              (bcm pp t ltws) (bcm_Spp pp t ltws)).
    move=> us hus.
    cbv beta iota.
    set sg := wsigs (lcoord t) pp 0
                (rr_digitS PP D Hgrind S_wn c_max pp t md (size ltws)) us.
    have hszl : size (rr_digitS PP D Hgrind S_wn c_max pp t md
                        (size ltws)) = l.
      rewrite /rr_digitS /rr_digit;
      case: (find_ctr PP D Hgrind S_wn c_max
               (lcoord t).1 (lcoord t).2 pp md) => [c|];
        [exact: (size_digest_of PP D Hgrind (lcoord t).1 (lcoord t).2 pp md c)
        | exact: size_nseq].
    rewrite (wendsEl (lcoord t) pp _ sg hszl).
    apply rpre_hypothesis_rule => s0 s1 hbcm.
    move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
    eapply rpre_weaken_rule.
    { apply: (r_lcp_tail pp t md ltws sg (get_heap s0 Lsl)
                (get_heap s0 Ltg) (get_heap s1 rcp_tgts_loc) (get_heap s1 Stg)).
      - exact: hsz'.
      - exact: hfr'.
      - have hblk := cp_inv_lcblk s0 s1 hinv hrv.
        rewrite hlpp hltw in hblk.
        exact: (lcblk_RC pp (get_heap s0 Lsl) ltws _ _ _ s0 s1 hblk). }
    move=> s0' s1' /= [-> ->].
    have hblk := cp_inv_lcblk s0 s1 hinv hrv.
    rewrite hlpp hltw in hblk.
    exact: hblk.
  + move=> s0 s1 H.
    case: H => [[[[hinv hrL] _] hr0] _].
    rewrite /rem_inv /= in hrL hr0.
    rewrite /bpre; split; first exact: hinv.
    split; first by rewrite hrL (negbTE erev).
    split; first exact: hsz.
    split; first exact: hr0.
    exact: hfr.
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rcp_pp_loc := Some b ;; #put rcp_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (cp_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK *)
  destruct arg as [j mw].
  rewrite /rr_winbody.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/cp_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  - eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - by case: hm => he1 hre _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
        case/cp_invE: hinv => _ [_ hrrv _ _ [_ _ _ hm]].
        have hlrv : get_heap s0 Lrv = true by rewrite hr0.
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - exists pp; split; first by rewrite -hr4.
          by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - case: hm => _ _ _ habs; rewrite habs in hlrv; discriminate hlrv. }
    move=> [pp [hlpp hrtgj]].
    rewrite hlpp hrtgj /=.
    (* step RHS rcp_pp = Some pp *)
    eapply (r_get_rhs_known rcp_pp_loc (Some pp)).
      { move=> s0 s1 [[[[[hinv hrev] _] _] _] hpp].
        rewrite /rem_inv /= in hrev hpp.
        case/cp_invE: hinv => _ [_ _ _ hrpp _].
        by rewrite hrpp hrev erev /= hpp. }
    cbv beta iota.
    rewrite bind_ret_l.
    rewrite P_gm1_E.
    case Ev: (lcp_v pp t0 sg md0
                (find_ctr PP D Hgrind S_wn c_max (adrs_height (decode_tweak t0))
                   (adrs_index (decode_tweak t0)) pp md0) j mw
              && (lcp_fcv pp t0 mw != lcp_rcv pp t0 sg md0 j)).
    + (* COMPRESS route: SM-TCR CHECK returns true (verok) *)
      ssprove_code_simpl; simplify_linking.
      eapply (r_get_rhs_known Srv true).
        { move=> s0 s1 [[[[[hinv hrev] _] _] _] _].
          rewrite /rem_inv /= in hrev.
          case/cp_invE: hinv => _ [_ _ _ _ [_ hsrv _ _]].
          by rewrite hsrv hrev erev. }
      eapply r_bind_assertD_rhs; first by [].
      move=> _.
      eapply r_get_remember_rhs => stgv.
      eapply (r_fact (getm stgv j
                = Some (encode_adrs (shrincs_fxmss_wots_pk_adrs (lcoord t0)),
                        lcp_rcv pp t0 sg md0 j))).
        { move=> s0 s1 [[[[[[hinv _] _] hltg] _] hpp] hstg].
          rewrite /rem_inv /= in hltg hpp hstg.
          case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
          move: hm; rewrite hpp /= => hm.
          move: (hm j); rewrite hltg E /= => -[_ h].
          by rewrite -hstg. }
      move=> hstgj.
      rewrite hstgj /=.
      eapply (r_get_rhs_known Spp (Some pp)).
        { move=> s0 s1 [[[[[[hinv _] _] _] _] hpp] _].
          rewrite /rem_inv /= in hpp.
          case/cp_invE: hinv => _ [_ _ _ _ [hspp _ _ _]].
          by rewrite hspp hpp. }
      apply r_ret => s0 s1 hpre.
      have hcp : cp_inv (s0, s1)
        by case: hpre => [[[[[[hinv _] _] _] _] _] _].
      split; last exact: hcp.
      rewrite !(th_evalE_Tpk PP N Tl dPP dN).
      move: (Ev) => /andP[hv hne].
      rewrite hv hne /=.
      move: hv; rewrite /lcp_v => /andP[/andP[/andP[_ hverok] _] _].
      move: hverok; rewrite /lcp_fcv /lcp_rcv /shrincs_fxmss_recover_anchor /l_rrpkS => /eqP ->.
      by rewrite eqxx.
    + (* no route: both sides = lcp_v *)
      ssprove_code_simpl; simpl.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[hinv _] _] _] _] _].
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/cp_invE: hinv => _ [_ _ hrsl _ _].
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
        case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - by case: hm => he1 hre _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr2 hr3 hr4.
        case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - exists pp; split; first by rewrite -hr4.
          by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - case: hm => he1 _ _ _; move: E; rewrite -hr2 he1 emptymE.
          by move=> H; discriminate H. }
    move=> [pp [hlpp hrtgj]].
    rewrite hlpp hrtgj /=.
    case E2: (find_ctr PP D Hgrind S_wn c_max (adrs_height (decode_tweak t0))
               (adrs_index (decode_tweak t0)) pp md0) => [c|].
    + apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
      rewrite /rem_inv /= in hr0 hr1.
      subst s0 s1; split=> //.
      exact: (cp_inv_setsl (rcons slog j) s0' s1' hinv).
    + apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CPl_leaf pp t (inr (inl xy)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CPl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CPl_leaf pp t (inr (inr dc)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CPl_leaf.
Qed.

Lemma R_cp_leaf_ideal : perfect IKM GM2 (R_cp_leaf ∘ SMB false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ cp_inv).
{ rewrite /cp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *) rewrite /rr_commit.
  ssprove_code_simpl; simpl.
  destruct arg as [t md].
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/cp_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltws.
  eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/cp_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws.
  eapply r_assertD_same => hsz.
  eapply r_assertD_same => hfr.
  eapply rpre_weaken_rule with (pre := λ '(s0, s1), bpre t ltws (s0, s1)).
  + eapply r_pin_commit => pp.
    eapply (r_lcgrind_spec false pp (lcoord t) md (iota 0 c_max)
              (bcm pp t ltws) (bcm_Spp pp t ltws)).
    set hs := [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max].
    have hds : lcp_digitS (size ltws) hs
             = rr_digitS PP D Hgrind S_wn c_max pp t md (size ltws).
      rewrite /lcp_digitS /rr_digitS.
      by rewrite /hs lcp_digit_E /rr_digit.
    have hcopt : omap fst (lcp_pick hs) = lfind (lcoord t) pp md.
      by rewrite /hs lcp_copt_E.
    rewrite hds hcopt.
    rewrite /rr_F.
    eapply (r_lcchains_spec false pp (lcoord t)
              (bcm pp t ltws) (bcm_Spp pp t ltws)).
    move=> us hus.
    cbv beta iota.
    set sg := wsigs (lcoord t) pp 0
                (rr_digitS PP D Hgrind S_wn c_max pp t md (size ltws)) us.
    have hszl : size (rr_digitS PP D Hgrind S_wn c_max pp t md
                        (size ltws)) = l.
      rewrite /rr_digitS /rr_digit;
      case: (find_ctr PP D Hgrind S_wn c_max
               (lcoord t).1 (lcoord t).2 pp md) => [c|];
        [exact: (size_digest_of PP D Hgrind (lcoord t).1 (lcoord t).2 pp md c)
        | exact: size_nseq].
    rewrite (wendsEl (lcoord t) pp _ sg hszl).
    apply rpre_hypothesis_rule => s0 s1 hbcm.
    move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
    eapply rpre_weaken_rule.
    { apply: (r_lcp_tail pp t md ltws sg (get_heap s0 Lsl)
                (get_heap s0 Ltg) (get_heap s1 rcp_tgts_loc) (get_heap s1 Stg)).
      - exact: hsz'.
      - exact: hfr'.
      - have hblk := cp_inv_lcblk s0 s1 hinv hrv.
        rewrite hlpp hltw in hblk.
        exact: (lcblk_RC pp (get_heap s0 Lsl) ltws _ _ _ s0 s1 hblk). }
    move=> s0' s1' /= [-> ->].
    have hblk := cp_inv_lcblk s0 s1 hinv hrv.
    rewrite hlpp hltw in hblk.
    exact: hblk.
  + move=> s0 s1 H.
    case: H => [[[[hinv hrL] _] hr0] _].
    rewrite /rem_inv /= in hrL hr0.
    rewrite /bpre; split; first exact: hinv.
    split; first by rewrite hrL (negbTE erev).
    split; first exact: hsz.
    split; first exact: hr0.
    exact: hfr.
- (* LGETPP *)
  destruct arg as [].
  rewrite /mkm_getpp.
  simplify_linking.
  rewrite (push_getSpp (fun pp => #put Srv := true ;; ret pp)
             (fun b => #put rcp_pp_loc := Some b ;; #put rcp_rev_loc := true ;; ret b)).
  eapply r_pp2 => pp.
  rewrite bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst s0 s1 s1a s1b; split=> //.
  exact: (cp_inv_reveal pp s0' s1c hinv hL).
- (* LCHECK *)
  destruct arg as [j mw].
  rewrite /rr_winbody.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/cp_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
  - eapply (r_fact (getm rtg j = None)).
      { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
        rewrite /rem_inv /= in hr2 hr3.
        case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - by case: hm => he1 hre _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
        case/cp_invE: hinv => _ [_ hrrv _ _ [_ _ _ hm]].
        have hlrv : get_heap s0 Lrv = true by rewrite hr0.
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - exists pp; split; first by rewrite -hr4.
          by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - case: hm => _ _ _ habs; rewrite habs in hlrv; discriminate hlrv. }
    move=> [pp [hlpp hrtgj]].
    rewrite hlpp hrtgj /=.
    (* step RHS rcp_pp = Some pp *)
    eapply (r_get_rhs_known rcp_pp_loc (Some pp)).
      { move=> s0 s1 [[[[[hinv hrev] _] _] _] hpp].
        rewrite /rem_inv /= in hrev hpp.
        case/cp_invE: hinv => _ [_ _ _ hrpp _].
        by rewrite hrpp hrev erev /= hpp. }
    cbv beta iota.
    rewrite bind_ret_l.
    rewrite P_gm2_E.
    case Ev: (lcp_v pp t0 sg md0
                (find_ctr PP D Hgrind S_wn c_max (adrs_height (decode_tweak t0))
                   (adrs_index (decode_tweak t0)) pp md0) j mw
              && (lcp_fcv pp t0 mw != lcp_rcv pp t0 sg md0 j)).
    + (* COMPRESS route: SMB false CHECK = false; GM2 nulls (fcv != rcv) *)
      ssprove_code_simpl; simpl.
      apply r_ret => s0 s1 hpre.
      have hcp : cp_inv (s0, s1)
        by case: hpre => [[[[[hinv _] _] _] _] _].
      split; last exact: hcp.
      move: (Ev) => /andP[_ hne].
      by rewrite (negbTE hne) andbF.
    + (* no route: GM2 = lcp_v && (fcv == rcv) = lcp_v *)
      ssprove_code_simpl; simpl.
      apply r_ret => s0 s1 hpre.
      have hcp : cp_inv (s0, s1)
        by case: hpre => [[[[[hinv _] _] _] _] _].
      split; last exact: hcp.
      move: Ev => /negbT; rewrite negb_and negbK => /orP[hnv|hfe].
      * by rewrite (negbTE hnv).
      * by rewrite hfe andbT.
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/cp_invE: hinv => _ [_ _ hrsl _ _].
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
        case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - by case: hm => he1 hre _ _; rewrite -hr3 hre emptymE. }
    move=> hrtgj.
    rewrite hrtgj.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split.
  - eapply r_get_remember_lhs => lpp.
    eapply (r_fact (exists pp, lpp = Some pp /\
              getm rtg j = Some (t0, ((sg, md0), lfind (lcoord t0) pp md0)))).
      { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
        rewrite /rem_inv /= in hr2 hr3 hr4.
        case/cp_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
        move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
        - exists pp; split; first by rewrite -hr4.
          by move: (hm j); rewrite hr2 E /= -hr3 => -[h _].
        - case: hm => he1 _ _ _; move: E; rewrite -hr2 he1 emptymE.
          by move=> H; discriminate H. }
    move=> [pp [hlpp hrtgj]].
    rewrite hlpp hrtgj /=.
    case E2: (find_ctr PP D Hgrind S_wn c_max (adrs_height (decode_tweak t0))
               (adrs_index (decode_tweak t0)) pp md0) => [c|].
    + apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [[[[[[hinv hr0] hr1] hr2] hr3] hr4] e0]] e1]].
      rewrite /rem_inv /= in hr0 hr1.
      subst s0 s1; split=> //.
      exact: (cp_inv_setsl (rcons slog j) s0' s1' hinv).
    + apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x].
  rewrite /mkm_collq.
  case: x => [xy|dc].
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CPl_leaf pp t (inr (inl xy)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CPl_leaf.
  + simplify_linking.
    rewrite (collq_rhs_E (fun pp => tc_eval CPl_leaf pp t (inr (inr dc)))).
    eapply r_pp2 => pp.
    apply r_ret => s0 s1 [hinv hL]; split; last exact: hinv.
    by rewrite /tc_eval /CPl_leaf.
Qed.

(** sub_cp : the COMPRESS step of the ladder.  Derivation = the perfect-routing
    recipe (Adv_perfect_l/r + Adv_reduction), validated to TYPECHECK + Qed
    given the two perfects. *)
Lemma sub_cp (B : nom_package) (VB : ValidPackage (loc B) IKM A_export B) :
  Adv GM1 GM2 B = AdvOf (SMTCR_game TPl CPl_leaf q1) (B ∘ R_cp_leaf).
Proof.
rewrite (Adv_perfect_l R_cp_leaf_real).
rewrite (Adv_perfect_r R_cp_leaf_ideal).
by rewrite Adv_reduction.
Qed.

End leaf2_compress.
