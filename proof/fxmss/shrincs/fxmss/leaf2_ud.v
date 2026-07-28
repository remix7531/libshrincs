(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.leaf2_ud

    Proves the two SM-UD telescope legs of the multi-leaf FXMSS leaf hop.
    The reduction uses [CUD_leaf], which exposes F, Htree, Hgrind, and Tl:
    while the public parameter is hidden, LCOMMIT must complete known chain
    values, evaluate the Merkle tree, grind the digest, and compress the leaf
    key. The SM-UD UQUERY oracle only hashes a fresh hidden input and therefore
    cannot implement those computations. The collection queries use address
    classes disjoint from the challenged depth-s chain tweaks.

    The file constructs [R_ud_leaf], proves its real and ideal per-step
    equivalences, and telescopes them into [sub_ud_up] and [sub_ud_down]. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From HBS Require Import prelude math.bin_tree math.merkle math.chain math.encoding
  sig.scheme games.thf games.smtcr games.smud toolkit.sample_seq.
From HBS Require Import wots.games wots.tcr_hop
  wots.ud_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop
  fxmss.leaf_reduction fxmss.leaf_km fxmss.leaf2_common fxmss.leaf2_games.
From mathcomp Require Import all_boot all_order reals.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section leaf2_ud.

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
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (n0 : N) (d0 : D).

Local Notation IKM := (@I_MIW_km w l PP N D).

(** The SM-UD challenge THF (F, the chain hash) and the skeleton's
    (INSUFFICIENT) collection [Cf] = { Tl , Hgrind }. *)
Local Notation TF := (Tf PP N F dPP dN).
Local Notation CF := (Cf PP N D F Tl Hgrind dPP dN).

Local Notation lcoord t := (@leaf_km.lcoord w l t).

(* ================================================================== *)
(** ** The UD collection [CUD_leaf]

    The collection contains F for chain completion, Htree for node hashing,
    Hgrind for counter search, and Tl for public-key compression. These are
    exactly the known-input computations required before UGETPP reveals the
    public parameter. *)

Definition CUD_leaf : thf_coll TF :=
  Build_thf_coll TF adrs_sf_ch
    (N ∐ ((N × N) ∐ ((D × 'nat) ∐ ('list N))))
    (N ∐ (N ∐ ('nat ∐ N)))
    (fun pp t x =>
       match x with
       | inl y              => inl (F pp (decode_tweak t) y)                   (* completion walks *)
       | inr (inl xy)       => inr (inl (Htree pp (decode_tweak t) xy))        (* LCOLLQ.inl routing *)
       | inr (inr (inl dc)) => inr (inr (inl (Hgrind pp (decode_tweak t) dc))) (* grinding + LCOLLQ.inr *)
       | inr (inr (inr xs)) => inr (inr (inr (Tl pp (decode_tweak t) xs)))     (* pk compression   *)
       end).

(** Sanity: the corrected challenger type-checks, and the reduction the
    fixed design enables has the recorded interface. *)

(* ================================================================== *)
(** ** Coordinate/tweak shorthands (mirror Leaf2Compress). *)

Local Notation gtw_of t :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (lcoord t))).
Local Notation grtw_of t :=
  (@encode_adrs l w (@shrincs_fxmss_wots_grind_adrs l w (lcoord t))).
Local Notation chtw_of t i k :=
  (@encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w (lcoord t) i k)).

(** The fixed_sum_scheme chain layer at the leaf coordinate [lcoord t]
    (= shrincs_fxmss_wots_scheme's [Fw]); the UD re-root maps live over it. *)
Local Notation FWl t := (leaf2_games.rr_F PP N F t).
Local Notation lroots t := (roots_map PP N (FWl t)).
Local Notation lrudsig t := (rud_sig PP N (FWl t)).
Local Notation luqreal t := (uq_real_map PP N (FWl t)).

(** Reused re-root digit / pk from Leaf2Games (slot-keyed static digit). *)
Local Notation rrdigS := (rr_digitS PP D Hgrind S_wn c_max).
Local Notation rrpkS := (rr_pkS PP N D F Tl Hgrind S_wn c_max).
Local Notation lPg1l := (P_g1lS PP N D F Tl Hgrind S_wn c_max).
Local Notation lfind t pp md :=
  (find_ctr PP D Hgrind S_wn c_max (lcoord t).1 (lcoord t).2 pp md).
Local Notation lcompl t pp ds sg :=
  (complete_ends PP N F (lcoord t).1 (lcoord t).2 pp ds sg).

(** SM-UD opsigs (UQUERY = the F challenge; UGETPP; UCOLLQ = the
    corrected 4-member collection). *)
Definition lud_qyo : opsig := (UQUERY, (th_T TF, th_N TF)).
Definition lud_gpo : opsig := (UGETPP, ('unit, th_PP TF)).
Definition lud_cqo : opsig := (UCOLLQ, (tc_T CUD_leaf × tc_M CUD_leaf, tc_N CUD_leaf)).

(* ================================================================== *)
(** ** The UCOLLQ-routed loops (mirror Leaf2Compress's lcp_grind/walk,
    at the corrected member positions of [CUD_leaf]). *)

(** Grinding: one UCOLLQ (Hgrind member [inr (inr (inl _))]) per counter. *)
Fixpoint lud_grind (zi : nat * nat) (md : D) (cs : seq nat) :
    raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lud_cqo (encode_adrs (shrincs_fxmss_wots_grind_adrs zi), inr (inr (inl (md, c))))
        (λ r, hs ← lud_grind zi md cs' ;;
              ret ((if r is inr (inr (inl h)) then h else 0) :: hs))
  end.

#[local] Instance lud_grind_valid (L : Locations) zi md cs :
  ValidCode L (I_SMUD TF CUD_leaf) (lud_grind zi md cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lud_cqo; fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k], [n] steps
    ([F] completion member [inl]) — routes through UCOLLQ, NOT the
    challenge. *)
Fixpoint lud_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr lud_cqo (encode_adrs (shrincs_fxmss_wots_chain_adrs zi i k), inl x)
         (λ r, lud_walk zi i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance lud_walk_valid (L : Locations) zi i k n x :
  ValidCode L (I_SMUD TF CUD_leaf) (lud_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lud_cqo; fmap_solve.
  move=> r; exact: IH.
Qed.

(** All chains, hybrid step [s]: per chain with digit [d], obtain the
    re-root value at position [minn s d.-1] — via the SM-UD CHALLENGE
    [UQUERY] at position [s] (chains that DIFFER between neighbouring
    hybrids, [s.+2 <= d]) or a LOCAL sample (the others) — walk it up to
    the signature position [d], then COMPLETE the end up to [w.-1] (all
    via UCOLLQ.F).  Returns (signature values, completed ends).  This is
    the multi-leaf mirror of UDHop's [rud_loop] fused with Leaf2Compress's
    [lcp_chains] completion. *)
Fixpoint lud_chains (zi : nat * nat) (s st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      sv ← (if (s.+2 <= d)%N
            then opr lud_qyo (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))
                   (λ y, lud_walk zi st s.+1 (d - s.+1) y)
            else u ← dN ;;
                 lud_walk zi st (minn s d.-1) (d - minn s d.-1) u) ;;
      e ← lud_walk zi st d (w.-1 - d) sv ;;
      '(ss, es) ← lud_chains zi s st.+1 ds' ;;
      ret (sv :: ss, e :: es)
  end.

#[local] Instance lud_chains_valid (L : Locations) zi s st ds :
  ValidCode L (I_SMUD TF CUD_leaf) (lud_chains zi s st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind.
  + case: (s.+2 <= d)%N.
    * eapply valid_opr; first by rewrite /lud_qyo; fmap_solve.
      move=> y; exact: lud_walk_valid.
    * eapply valid_bind; first by eapply valid_scheme, prog_valid.
      move=> u; exact: lud_walk_valid.
  + move=> sv; eapply valid_bind; first exact: lud_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(** The bounded grind search on the answer list (= scheme [find_ctr]
    re-rooted at the oracle answers). *)
Definition lud_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 c_max) hs | @grind_prp w l S_wn ch.2].

Definition lud_digit (hs : seq nat) : seq nat :=
  match lud_pick hs with
  | Some ch => digits_w w l ch.2
  | None => nseq l w.-1
  end.

(** The slot-keyed commit digit (= [rr_digitS] reconstructed at slot [j]).
    The [j < q_s] budget wrapper is absent (as in [rr_digitS], which
    now ignores its vestigial [j] argument: every leaf carries a real
    committed re-root digit, [lud_digit] already virtualizing the
    non-grindable case).  [j] is kept for interface stability. *)
Definition lud_digitS (j : nat) (hs : seq nat) : seq nat :=
  lud_digit hs.

(* ================================================================== *)
(** ** The reduction [R_ud_leaf : package (I_SMUD TF CUD_leaf) IKM]. *)

(* ids 710+, not 700+: 700-704 collide with leaf2_chain_pre.v's rpr_* at
   700-705 (see proof/LOCATIONS.md). *)
Definition rud_rev_loc  := mkloc 710 (false : bool).
Definition rud_tws_loc  := mkloc 711 ([::] : seq adrs_sf_ch).
Definition rud_tgts_loc :=
  mkloc 712 (emptym : {fmap nat -> (adrs_sf_ch × ((('list N) × D) × 'option 'nat))}).
Definition rud_slog_loc := mkloc 713 ([::] : seq nat).
Definition rud_pp_loc   := mkloc 714 (None : option PP).

Local Notation RUDLocs :=
  [fmap rud_rev_loc ; rud_tws_loc ; rud_tgts_loc ; rud_slog_loc ; rud_pp_loc ].

Definition R_ud_leaf (b : bool) (s : nat) : package (I_SMUD TF CUD_leaf) IKM.
Proof.
notypeclasses refine [package RUDLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) {
      revealed ← get rud_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get rud_tws_loc ;;
      #assert (size tws < n_max)%N ;;
      #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
      _ ← opr lud_cqo (grtw_of t, inr (inr (inl (md, 0)))) (λ r, ret r) ;;
      hs ← lud_grind (lcoord t) md (iota 0 c_max) ;;
      '(sg, ends) ← lud_chains (lcoord t) s 0 (lud_digitS (size tws) hs) ;;
      root ← opr lud_cqo (gtw_of t, inr (inr (inr ends)))
               (λ r, ret (if r is inr (inr (inr h)) then h else n0)) ;;
      tgts ← get rud_tgts_loc ;;
      #put rud_tgts_loc := setm tgts (size tws) (t, ((sg, md), omap fst (lud_pick hs))) ;;
      #put rud_tws_loc := rcons tws t ;;
      ret root
    } ;
    [ LGETPP ] : { 'unit ~> PP } (_) {
      pp ← opr lud_gpo Datatypes.tt (λ p, ret p) ;;
      #put rud_pp_loc := Some pp ;;
      #put rud_rev_loc := true ;;
      ret pp
    } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      if b then
        (revealed ← get rud_rev_loc ;;
         #assert revealed ;;
         tgts ← get rud_tgts_loc ;;
         match getm tgts j with
         | Some (t0, ((sg, md0), _)) =>
             ppo ← get rud_pp_loc ;;
             pp ← match ppo with
                  | Some pp => ret pp
                  | None => pp ← dPP ;; #put rud_pp_loc := Some pp ;; ret pp
                  end ;;
             ret (lPg1l pp t0 sg md0 j mw)
         | None => ret false
         end)
      else ret false
    } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) {
      (slog ← get rud_slog_loc ;;
       #assert (j \notin slog) ;;
       tgts ← get rud_tgts_loc ;;
       match getm tgts j with
       | Some (t0, ((sg, md0), copt)) =>
           match copt with
           | Some c => #put rud_slog_loc := rcons slog j ;; ret (Some (sg, c))
           | None => ret None
           end
       | None => ret None
       end)
    } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      match x with
      | inl xy =>
          opr lud_cqo (t, inr (inl xy))
            (λ r, ret (match r with inr (inl h) => inl h | _ => inl n0 end))
      | inr dc =>
          opr lud_cqo (t, inr (inr (inl dc)))
            (λ r, ret (match r with inr (inr (inl g)) => inr g | _ => inr 0 end))
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
          - eapply valid_opr; first by rewrite /lud_cqo; fmap_solve.
            move=> r; apply valid_ret.
          - eapply valid_opr; first by rewrite /lud_cqo; fmap_solve.
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
      case: ifP => _; last by apply valid_ret.
      eapply valid_getr; first by fmap_solve. move=> revealed.
      eapply valid_assertD => _.
      eapply valid_getr; first by fmap_solve. move=> tgts.
      case: (getm tgts j) => [[t0 [[sg md0] _]]|]; last by apply valid_ret.
      eapply valid_getr; first by fmap_solve. move=> ppo.
      eapply valid_bind.
        case: ppo => [pp|]; first by apply valid_ret.
        eapply valid_bind; first by eapply valid_scheme, prog_valid.
        move=> pp; eapply valid_putr; first by fmap_solve.
        apply valid_ret.
      move=> pp; apply valid_ret. } }
  { (* LGETPP *)
    intro u.
    eapply valid_opr; first by rewrite /lud_gpo; fmap_solve.
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
    eapply valid_opr; first by rewrite /lud_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> _.
  eapply valid_bind; first exact: lud_grind_valid. move=> hs.
  eapply valid_bind; first exact: lud_chains_valid. move=> [sg ends].
  eapply valid_bind.
    eapply valid_opr; first by rewrite /lud_cqo; fmap_solve.
    move=> r; apply valid_ret.
  move=> root.
  eapply valid_getr; first by fmap_solve. move=> tgts.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve. apply valid_ret. }
Defined.

(** VALIDATION (structural): the reduction lands as
    [package (I_SMUD TF CUD_leaf) IKM] — i.e. ALL four routings
    (F completion walks, Htree LCOLLQ.inl, Hgrind grind + LCOLLQ.inr,
    Tl pk-compression, plus the UQUERY re-root challenge) type-check
    over the SM-UD interface with the corrected collection.  This is the
    structural half of the M2 validation gate: the completion walks DO
    route through UCOLLQ. *)

(* ================================================================== *)
(** ** SM-UD oracle resolve equations + collection conversions. *)

Local Notation Upp := (ud_pp_loc TF).
Local Notation Utw := (ud_tws_loc TF).
Local Notation Urv := ud_rev_loc.
Local Notation SMU b := (SMUD_game TF CUD_leaf (n_max * l) b).

Lemma resolve_ud_cq (b : bool) (t : tc_T CUD_leaf) (x : tc_M CUD_leaf) :
  resolve (SMU b) lud_cqo (t, x) =
  (ppo ← get Upp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Upp := Some pp ;; ret pp
        end ;;
   ret (tc_eval CUD_leaf pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_ud_gp (b : bool) (u : unit) :
  resolve (SMU b) lud_gpo u =
  (ppo ← get Upp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Upp := Some pp ;; ret pp
        end ;;
   #put Urv := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_ud_qy_true (t : th_T TF) :
  resolve (SMU true) lud_qyo t =
  (revealed ← get Urv ;;
   #assert ~~ revealed ;;
   tws ← get Utw ;;
   #assert (size tws < n_max * l)%N ;;
   #assert (t \notin tws) ;;
   #put Utw := rcons tws t ;;
   ppo ← get Upp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Upp := Some pp ;; ret pp
        end ;;
   x ← dN ;;
   ret (F pp (decode_tweak t) x)).
Proof. by simplify_linking. Qed.

Lemma resolve_ud_qy_false (t : th_T TF) :
  resolve (SMU false) lud_qyo t =
  (revealed ← get Urv ;;
   #assert ~~ revealed ;;
   tws ← get Utw ;;
   #assert (size tws < n_max * l)%N ;;
   #assert (t \notin tws) ;;
   #put Utw := rcons tws t ;;
   y ← dN ;;
   ret y).
Proof. by simplify_linking. Qed.

(** Collection member extractions at canonical tweaks (compute by
    [decode_tweakK]). *)
Lemma collq_udF_E (pp : PP) (zi : nat * nat) (i k : nat) (x : N) :
  (if tc_eval CUD_leaf pp (encode_adrs (shrincs_fxmss_wots_chain_adrs zi i k)) (inl x)
      is inl y then y else x)
  = F pp (shrincs_fxmss_wots_chain_adrs zi i k) x.
Proof. by rewrite /tc_eval /CUD_leaf decode_tweakK. Qed.

Lemma collq_udH_E (pp : PP) (zi : nat * nat) (md : D) (c : nat) :
  (if tc_eval CUD_leaf pp (encode_adrs (shrincs_fxmss_wots_grind_adrs zi))
      (inr (inr (inl (md, c)))) is inr (inr (inl h)) then h else 0)
  = Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c).
Proof. by rewrite /tc_eval /CUD_leaf decode_tweakK. Qed.

Lemma collq_udT_E (pp : PP) (zi : nat * nat) (ends : seq N) :
  (if tc_eval CUD_leaf pp (encode_adrs (shrincs_fxmss_wots_pk_adrs zi)) (inr (inr (inr ends)))
      is inr (inr (inr h)) then h else n0)
  = Tl pp (shrincs_fxmss_wots_pk_adrs zi) ends.
Proof. by rewrite /tc_eval /CUD_leaf decode_tweakK. Qed.

#[local] Arguments resolve : simpl never.
#[local] Arguments SMUD_game : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_ctr : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments decode_tweak : simpl never.

(* ================================================================== *)
(** ** One linked UCOLLQ with [pp] pinned. *)

Lemma r_ud_collq_known (b : bool) {A B : choiceType} (pp : PP)
    (t : tc_T CUD_leaf) (x : tc_M CUD_leaf) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Upp = Some pp)
    (c0 : raw_code A) (k1 : tc_N CUD_leaf -> raw_code B) (post : postcond A B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CUD_leaf pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (resolve (SMU b) lud_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_ud_cq b t x).
eapply (r_get_bind_rhs Upp (Some pp)); first exact: hpp.
cbv beta iota.
exact: h.
Qed.

(** The grinding loop (rhs-only; [pp] pinned): every UCOLLQ reads the
    initialised [Upp] and returns an [Hgrind] evaluation. *)
Lemma r_ud_grind_spec (b : bool) {B : choiceType} (pp : PP) (zi : nat * nat)
    (md : D) (cs : seq nat) (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Upp = Some pp)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lud_grind zi md cs) (SMU b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_ud_collq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_udH_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(** THE completion-walk routing lemma (rhs-only; [pp] pinned): walking
    chain [i] upward via UCOLLQ.F IS the pure chain [chain (F …) x k n].
    This is the semantic half of the M2 validation gate — the completion
    walks route through UCOLLQ and COMPUTE CORRECTLY (over the corrected
    [CUD_leaf], for any leaf, any position, any length). *)
Lemma r_ud_walk_spec (b : bool) {A B : choiceType} (pp : PP) (zi : nat * nat)
    (pre : precond)
    (hpp : forall s0 s1, pre (s0, s1) -> get_heap s1 Upp = Some pp)
    (post : postcond A B) :
  forall n i k (x : N) (c0 : raw_code A) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ k1 (chain (HBS.wots.scheme.chainf PP N
                       (Fw PP N F zi.1 zi.2) pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (code_link (lud_walk zi i k n x) (SMU b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_ud_collq_known b pp _ _ pre hpp).
  cbv beta.
  rewrite collq_udF_E.
  exact: IH.
Qed.

(* ================================================================== *)
(** ** The hybrid game [Hl b s] (the telescope's rungs).

    [Hl b s] is the multi-leaf mirror of UDHop's [Hud s b] over the
    STATIC-gate leaf endpoint: it re-roots EVERY leaf's chains at the
    hybrid position [s] (capped at [d.-1] per chain), stores the
    re-rooted signature roots [roots_map … s …] in the tgts map, and
    returns the (digit-INDEPENDENT) leaf pk [rr_pkS].  All FOUR non-COMMIT
    oracles are REUSED verbatim from Leaf2Games / LeafKM (so [Hl true
    w.-2] shares 4/5 oracles with [G1l], and the win predicate matches
    [R_ud_leaf]'s [lPg1l] exactly).  Only LCOMMIT ([hl_commit s]) is new.

    Endpoints (to be proved): [Hl b 0 ≈ MIW_kmS b] (roots at position 0 =
    honest keygen, [roots_map_sign]/[ends_from_roots_map0]) and
    [Hl true w.-2 = G1l] / [Hl false w.-2 = G1l'] ([sig_map_roots]:
    [roots_map w.-2 = sig_map = sample_sig_roots]'s post-processing). *)

Local Notation Lpp := (miw_pp_loc PP).
Local Notation Ltg := (@mkm_tgts_loc w l N D).
Local Notation Ltw := (@miw_tws_loc w l).
Local Notation Lrv := miw_rev_loc.
Local Notation Lsl := miw_slog_loc.
Local Notation MKMLocs := [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl].
Local Notation lpk := (leaf_pk_c PP N F Tl).

(** The per-leaf re-root map at hybrid position [s] (= what the game
    stores and the reduction reproduces via [r_ud_chains_real]). *)
Local Notation lrrmap t pp s md j xs :=
  (roots_map PP N (rr_F PP N F t) pp s 0 (rrdigS pp t md j) xs).

(** LCOMMIT of [Hl s]: pin [pp] (the re-root digit needs it), sample one
    hidden root per chain, re-root at [s] via [roots_map], store the
    re-rooted roots in the tgts map, return the compressed leaf pk. *)
Definition hl_commit (s : nat) (t : adrs_sf_ch) (md : D) : raw_code N :=
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
   xs ← sample_seq dN l ;;
   tgts ← get Ltg ;;
   #put Ltg := setm tgts (size tws) (t, (lrrmap t pp s md (size tws) xs, md)) ;;
   #put Ltw := rcons tws t ;;
   ret (rrpkS pp t md (size tws) (lrrmap t pp s md (size tws) xs))).

#[local] Instance hl_commit_valid (I : Interface) (s : nat)
    (t : adrs_sf_ch) (md : D) :
  ValidCode MKMLocs I (hl_commit s t md).
Proof.
rewrite /hl_commit.
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
eapply valid_bind; first by apply sample_seq_valid. move=> xs.
eapply valid_getr; first by fmap_solve. move=> tgts.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[local] Arguments hl_commit : simpl never.

(** The hybrid game.  LCOMMIT = [hl_commit s]; the rest REUSED from
    Leaf2Games/LeafKM (win = [lPg1l] under the [b] guard, exactly
    [R_ud_leaf]'s LCHECK). *)
Definition Hl (b : bool) (s : nat) : game IKM.
Proof.
notypeclasses refine [package MKMLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) { hl_commit s t md } ;
    [ LGETPP ] : { 'unit ~> PP } (_) { mkm_getpp PP dPP } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      if b then rr_winbody PP N D dPP lPg1l j mw else ret false } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) {
      rr_sign PP N D Hgrind dPP S_wn c_max j } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      mkm_collq PP N D Hgrind Htree dPP t x }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { eapply valid_package_cons.
        { apply: valid_empty_package. }
        { intros [t x]; exact: (mkm_collq_valid PP N D Hgrind Htree dPP _ t x). } }
      { intro j; exact: (rr_sign_valid PP N D Hgrind dPP S_wn c_max _ j). } }
    { intros [j mw]; case: ifP => _;
        [exact: (rr_winbody_valid PP N D dPP _ lPg1l j mw) | apply valid_ret]. } }
  { intro u; exact: (mkm_getpp_valid PP N D dPP _). } }
{ intros [t md]; exact: (hl_commit_valid _ s t md). }
Defined.


(* ================================================================== *)
(** ** The two UD telescope legs [sub_ud_up] / [sub_ud_down].

    The endpoint games (all over the SHARED [MKMLocs], [IKM]-typed). *)

Local Notation MIWkm b :=
  (MIW_kmS PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max b).
Local Notation G1lg  :=
  (G1l  PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation G1lg' :=
  (G1l' PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).

(** The [b]-selected [w.-2] endpoint (= [G1l] for [b], [G1l'] for [~b]). *)
Local Notation Hlend b := (if b then G1lg else G1lg').

(* ------------------------------------------------------------------ *)
(** *** Perfect facts feeding the telescope *)

(** The LCOMMIT coupling of the [w.-2] endpoint: the ladder game's
    [rr_commit] (sample [sample_sig_roots] = [sig_map] of raw roots) vs
    the hybrid's [hl_commit w.-2] ([sample_seq];[roots_map w.-2]).  The
    byte-identical get/assert prefix + lazy-[pp] read sync under state
    equality; the sampler is coupled by [r_sample_sig_roots], and the
    stored/returned values coincide by [sig_map_roots] (=[roots_map w.-2]),
    whose [wf_digits w (rr_digitS …)] side-condition needs [0 < w] (the
    virtual all-max digit [nseq l w.-1]; the grind digit is [wf] via
    [find_ctr_good]).  For [w = 0] the identity is FALSE (all chains
    collapse); the endpoints, hence the telescope, carry [0 < w]. *)
Lemma hl_endw_commit (hw : (0 < w)%N) (t : adrs_sf_ch) (md : D) :
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     rr_commit PP N D F Tl Hgrind dPP dN S_wn c_max n_max t md
   ≈ hl_commit w.-2 t md
   ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ s0 = s1 ⦄.
Proof.
rewrite /rr_commit /hl_commit /=.
ssprove_sync_eq => revealed.
ssprove_sync_eq => hrev.
ssprove_sync_eq => tws.
ssprove_sync_eq => hsz.
ssprove_sync_eq => hfr.
ssprove_sync_eq => ppo.
have Hcoup : forall pp : PP,
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     (sg ← sample_sig_roots PP N (FWl t) dN pp 0 (rrdigS pp t md (size tws)) ;;
      tgts ← get Ltg ;;
      #put Ltg := setm tgts (size tws) (t, (sg, md)) ;;
      #put Ltw := rcons tws t ;;
      ret (rrpkS pp t md (size tws) sg))
   ≈ (xs ← sample_seq dN l ;;
      tgts ← get Ltg ;;
      #put Ltg := setm tgts (size tws)
                    (t, (lrrmap t pp w.-2 md (size tws) xs, md)) ;;
      #put Ltw := rcons tws t ;;
      ret (rrpkS pp t md (size tws) (lrrmap t pp w.-2 md (size tws) xs)))
   ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ s0 = s1 ⦄.
{ move=> pp.
  have hszl : size (rrdigS pp t md (size tws)) = l.
  { rewrite /rrdigS /rr_digitS /rr_digit;
      case: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
               (leaf_km.lcoord t).2 pp md) => [c|];
      [exact: (size_digest_of PP D Hgrind (leaf_km.lcoord t).1
                 (leaf_km.lcoord t).2 pp md c) | exact: size_nseq]. }
  have hwf : wf_digits w (rrdigS pp t md (size tws)).
  { rewrite /rrdigS /rr_digitS /rr_digit.
    case E: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
               (leaf_km.lcoord t).2 pp md) => [c|].
    + by move: (find_ctr_good PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
                 (leaf_km.lcoord t).2 pp md c E) => /andP[h1 _].
    + by rewrite /wf_digits all_nseq ltn_predL hw orbT. }
  have hss : sample_seq dN l = sample_seq dN (size (rrdigS pp t md (size tws)))
    by rewrite hszl.
  rewrite hss.
  eapply r_sample_sig_roots => xs hxs.
  rewrite (sig_map_roots PP N (FWl t) w pp 0 (rrdigS pp t md (size tws)) xs hwf).
  eapply rpost_weaken_rule;
    [exact: rreflexivity_rule | by move=> [a0 s0] [a1 s1] [] -> ->]. }
case: ppo => [pp|].
- simpl. exact: (Hcoup pp).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact _|] => x.
  ssprove_code_simpl; simpl.
  ssprove_sync_eq.
  exact: (Hcoup x).
Qed.

(** ENDPOINT (s = w.-2): re-rooting EVERY chain at [w.-2] is exactly the
    ladder-endpoint game's [rr_commit] ([sig_map_roots]: [roots_map w.-2 =
    sig_map]; the other four oracles are byte-identical).  [b] selects the
    LCHECK win ([rr_winbody P_g1lS] vs [ret false]), matched by [Hlend].
    Needs [0 < w] (see [hl_endw_commit]). *)
Lemma Hl_endw (hw : (0 < w)%N) (b : bool) :
  perfect IKM (Hlend b) (Hl b w.-2).
Proof.
case: b.
- ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (λ '(h0, h1), h0 = h1)). { ssprove_invariant. }
  simplify_eq_rel arg.
  all: try (eapply rpost_weaken_rule;
    [exact: rreflexivity_rule | by move=> [a0 s0] [a1 s1] [] -> ->]).
  case: arg => t md. exact: (hl_endw_commit hw t md).
- ssprove_share. eapply prove_perfect.
  eapply (eq_rel_perf_ind _ _ (λ '(h0, h1), h0 = h1)). { ssprove_invariant. }
  simplify_eq_rel arg.
  all: try (eapply rpost_weaken_rule;
    [exact: rreflexivity_rule | by move=> [a0 s0] [a1 s1] [] -> ->]).
  case: arg => t md. exact: (hl_endw_commit hw t md).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Content bridges for the s=0 endpoint [Hl0_MIW]

    The public-key and signature identities below connect the fixed_sum_scheme
    endpoint to the embedded FXMSS WOTS instance at [lcoord t]. They follow
    from [ends_from_roots_map0], [roots_map_sign], and [chainf_Fw]. *)

(** (A) pk-identity: the re-rooted-at-0 compressed pk over the STORED
    roots [roots_map … 0 0 (rr_digitS …) xs] is the honest leaf pk
    [leaf_pk_c pp t xs].  This is the [rr_pkS] return of [hl_commit 0]
    (= [lpk], the LCOMMIT coupling) AND the [P_g1lS]<->[mkm_winSG]
    anchor equality (the LCHECK coupling).  Needs [0<w] (the virtual
    all-max digit [nseq l w.-1] is [wf_digits] only then) + [size xs = l]. *)
Lemma hl0_pk_E (hw : (0 < w)%N) (pp : PP) (t : adrs_sf_ch) (md : D)
    (j : nat) (xs : seq N) :
  size xs = l ->
  rr_pkS PP N D F Tl Hgrind S_wn c_max pp t md j
    (roots_map PP N (leaf2_games.rr_F PP N F t) pp 0 0
       (rr_digitS PP D Hgrind S_wn c_max pp t md j) xs)
  = leaf_pk_c PP N F Tl pp t xs.
Proof.
move=> hxs.
have hszd : size (rr_digitS PP D Hgrind S_wn c_max pp t md j) = l.
{ rewrite /rr_digitS /rr_digit;
    case: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
             (leaf_km.lcoord t).2 pp md) => [c|];
    [exact: (size_digest_of PP D Hgrind (leaf_km.lcoord t).1
               (leaf_km.lcoord t).2 pp md c) | exact: size_nseq]. }
have hwf : wf_digits w (rr_digitS PP D Hgrind S_wn c_max pp t md j).
{ rewrite /rr_digitS /rr_digit.
  case E: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
             (leaf_km.lcoord t).2 pp md) => [c|].
  + by move: (find_ctr_good PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
               (leaf_km.lcoord t).2 pp md c E) => /andP[h1 _].
  + by rewrite /wf_digits all_nseq ltn_predL hw orbT. }
rewrite /rr_pkS /leaf_pk_c /shrincs_fxmss_wots_public_key /pk_adrs.
congr (Tl pp _ _).
exact: (ends_from_roots_map0 PP N (leaf2_games.rr_F PP N F t) l w pp
          (rr_digitS PP D Hgrind S_wn c_max pp t md j) xs hszd hwf).
Qed.

(** (B) lsg-opening: for an IN-BUDGET GRINDABLE leaf ([j<q_s],
    [find_ctr = Some c]) the used-instance signer [leaf_sign_c pp t xs md]
    (= [mkm_signS]'s [lsg]) reveals EXACTLY the STORED re-rooted roots
    [roots_map … 0 0 (rr_digitS …) xs] with the grind counter [c]
    ([rr_digitS = digest_of md c] here, so [roots_map 0 (digest_of) =
    sign_digits] by [roots_map_sign]).  This is the LSIGN coupling core
    ([mkm_signS]'s [lsg] = [rr_sign]'s direct stored reveal). *)
Lemma hl0_lsg_E (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat)
    (xs : seq N) (c : nat) :
  size xs = l ->
  find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
    (leaf_km.lcoord t).2 pp md = Some c ->
  leaf_sign_c PP N D F Hgrind S_wn c_max pp t xs md
  = Some (roots_map PP N (leaf2_games.rr_F PP N F t) pp 0 0
            (rr_digitS PP D Hgrind S_wn c_max pp t md j) xs, c).
Proof.
move=> hxs hfc.
rewrite /leaf_sign_c.
rewrite (shrincs_fxmss_wots_sign_Some PP N D F Hgrind S_wn c_max (leaf_km.lcoord t).1
          (leaf_km.lcoord t).2 pp xs md c hfc).
have hrr : rr_digitS PP D Hgrind S_wn c_max pp t md j
  = digest_of PP D Hgrind (leaf_km.lcoord t).1 (leaf_km.lcoord t).2 pp md c.
{ by rewrite /rr_digitS /rr_digit hfc. }
rewrite hrr.
rewrite (roots_map_sign PP N (leaf2_games.rr_F PP N F t) l pp _ xs
           (size_digest_of PP D Hgrind (leaf_km.lcoord t).1
              (leaf_km.lcoord t).2 pp md c)).
by [].
Qed.

(* ================================================================== *)
(** ** Infrastructure for the s=0 endpoint [Hl0_MIW] (game-vs-game).

    Both games are over the SHARED [MKMLocs]; the ONLY location whose
    content differs is [Ltg] (MIW stores RAW roots [xs]; [Hl 0] stores
    the position-0 re-rooted [roots_map 0]).  So the invariant is
    [heap_ignore [fmap Ltg]] (all other locs — incl. adversary — EQUAL)
    ⋊ a [rel_app] carrying the per-index [roots_map]-at-0 transform,
    keyed by the SHARED lazy [Lpp]. *)

Local Notation IGN0 := [fmap Ltg].

(** The per-index coherence of the two target tables (MIW raw / Hl
    re-rooted-at-0), at the shared committed [pp]. *)
Definition RU0 (lpp : option PP)
    (ltgL : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (ltgR : {fmap nat -> (adrs_sf_ch × ('list N × D))}) : Prop :=
  match lpp with
  | None => ltgL = emptym /\ ltgR = emptym
  | Some pp =>
      forall j,
        match getm ltgL j with
        | Some (t0, (xs, md0)) =>
            size xs = l /\
            getm ltgR j = Some (t0, (lrrmap t0 pp 0 md0 j xs, md0))
        | None => getm ltgR j = None
        end
  end.

Definition ud0_inv : precond :=
  heap_ignore IGN0
  ⋊ rel_app [:: (lhs, Lpp) ; (lhs, Ltg) ; (rhs, Ltg) ] RU0.

Arguments ud0_inv : simpl never.

Lemma ud0_invE s0 s1 :
  ud0_inv (s0, s1) ->
  heap_ignore IGN0 (s0, s1) /\
  RU0 (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s1 Ltg).
Proof. by move=> [h1 h2]; split. Qed.

Lemma ud0_invI s0 s1 :
  heap_ignore IGN0 (s0, s1) ->
  RU0 (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s1 Ltg) ->
  ud0_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** Parallel same-value put preserves [heap_ignore] (any location). *)
Lemma heap_ignore_set_both (L : Locations) (l0 : Location) (v : l0) s0 s1 :
  heap_ignore L (s0, s1) ->
  heap_ignore L (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h l' hl'.
have [e|hne] := eqVneq l'.1 l0.1.
- by rewrite /get_heap /set_heap !setmE e eqxx.
- by rewrite !(get_set_heap_neq _ _ _ _ hne); apply: h.
Qed.

(** The identical-sampler coupler (local copy of [r_sample_seq_size_l]). *)
Lemma r_ss_size {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k0 k1 : chList N -> raw_code B) :
  (forall xs : seq N, size xs = n -> ⊢ ⦃ pre ⦄ k0 xs ≈ k1 xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xs ← sample_seq dN n ;; k0 xs ≈ xs ← sample_seq dN n ;; k1 xs
  ⦃ post ⦄.
Proof.
elim: n k0 k1 => [|n IH] k0 k1 hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact: prog_valid|] => x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

(** A location-free scheme [s] (possibly STATEFUL) commutes past a head
    sample [o] under ANY continuation [f] (sampling is state-independent;
    [rswap_ruleR] lifts the bare-pair swap [rsamplerC] through [f]). *)
Lemma swap_sk {A C : choiceType} (s : raw_code A) (o : Op)
    (f : A -> Arit o -> raw_code C) :
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     (x ← s ;; a ← sample o ;; f x a)
     ≈
     (a ← sample o ;; x ← s ;; f x a)
  ⦃ eq ⦄.
Proof.
eapply (rswap_ruleR s (z ← sample o ;; ret z) f).
- by move=> b b' ->.
- by move=> a0 a1; apply: rsym_pre; [|exact: rreflexivity_rule].
- exact: (rsamplerC o s).
Qed.

(** An arbitrary (possibly stateful) code [s] commutes to the RIGHT of a
    STATELESS block [t] (pair form; structural induction on [t]). *)
Lemma swap_code_seq {A B : choiceType} (s : raw_code A) (t : raw_code B) :
  ValidCode emptym [interface] t ->
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     (x ← s ;; y ← t ;; ret (x, y))
     ≈
     (y ← t ;; x ← s ;; ret (x, y))
  ⦃ eq ⦄.
Proof.
move=> ht; move: t ht; fix IH 1 => t ht.
destruct t as [v | o x k | ℓ k | ℓ v k | o k].
- by simpl; apply: rreflexivity_rule.
- by move/inversion_valid_opr: ht => [hin _]; exfalso; apply: (fhas_empty _ hin).
- by move/inversion_valid_getr: ht => [hin _]; exfalso; apply: (fhas_empty _ hin).
- by move/inversion_valid_putr: ht => [hin _]; exfalso; apply: (fhas_empty _ hin).
- have hk : forall a, ValidCode emptym [interface] (k a)
    by move/inversion_valid_sampler: ht.
  simpl.
  eapply (r_transL
            (a ← sample o ;; x ← s ;; y ← k a ;; ret (x, y))
            (x ← s ;; a ← sample o ;; y ← k a ;; ret (x, y))).
  + eapply rsymmetry; eapply rsym_pre; first by [].
    eapply rpost_weaken_rule.
    * apply: (swap_sk s o (fun x a => y ← k a ;; ret (x, y))).
    * by move=> [??] [??] ->.
  + eapply (rsame_head_cmd (cmd_sample o)) => a.
    exact: (IH (k a) (hk a)).
Qed.

(** Bind congruence under [eq]: two [eq]-related heads splice a shared
    continuation, staying [eq]-related. *)
Lemma r_bind_feq {A C : choiceType} (m0 m1 : raw_code A) (f : A -> raw_code C) :
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄ m0 ≈ m1 ⦃ eq ⦄ ->
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄ (x ← m0 ;; f x) ≈ (x ← m1 ;; f x) ⦃ eq ⦄.
Proof.
move=> h; eapply r_bind; first exact: h.
move=> a0 a1; eapply rpre_hypothesis_rule => s0 s1 heq.
move: heq => [] -> ->.
eapply rpre_weaken_rule; first exact: rreflexivity_rule.
by move=> ?? /= [-> ->].
Qed.

(** [sample_seq] (stateless) commutes to the RIGHT of an arbitrary code
    [s] under any continuation [k].  (Pair-lift of [swap_code_seq].) *)
Lemma r_ss_pull {B C : choiceType} (s : raw_code B) (n : nat)
    (k : B -> chList N -> raw_code C) :
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     (x ← s ;; xs ← sample_seq dN n ;; k x xs)
   ≈ (xs ← sample_seq dN n ;; x ← s ;; k x xs)
   ⦃ eq ⦄.
Proof.
have E1 : (x ← s ;; xs ← sample_seq dN n ;; k x xs)
        = bind (x ← s ;; xs ← sample_seq dN n ;; ret (x, xs))
               (fun p => k p.1 p.2).
{ rewrite !bind_assoc; apply: bind_cong => //.
  apply: functional_extensionality => x; by rewrite bind_assoc. }
have E2 : (xs ← sample_seq dN n ;; x ← s ;; k x xs)
        = bind (xs ← sample_seq dN n ;; x ← s ;; ret (x, xs))
               (fun p => k p.1 p.2).
{ rewrite !bind_assoc; apply: bind_cong => //.
  apply: functional_extensionality => xs; by rewrite bind_assoc. }
rewrite E1 E2.
apply: r_bind_feq.
apply: (swap_code_seq s (sample_seq dN n)); exact _.
Qed.

(** Generic version of [r_ss_pull]: any STATELESS block [t] commutes to the
    FRONT of an arbitrary code [s], under any continuation [k]. *)
Lemma r_code_pull {A B C : choiceType} (s : raw_code B) (t : raw_code A)
    (k : B -> A -> raw_code C) :
  ValidCode emptym [interface] t ->
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
     (x ← s ;; y ← t ;; k x y)
   ≈ (y ← t ;; x ← s ;; k x y)
   ⦃ eq ⦄.
Proof.
move=> ht.
have E1 : (x ← s ;; y ← t ;; k x y)
        = bind (x ← s ;; y ← t ;; ret (x, y)) (fun p => k p.1 p.2).
{ rewrite !bind_assoc; apply: bind_cong => //.
  apply: functional_extensionality => x; by rewrite bind_assoc. }
have E2 : (y ← t ;; x ← s ;; k x y)
        = bind (y ← t ;; x ← s ;; ret (x, y)) (fun p => k p.1 p.2).
{ rewrite !bind_assoc; apply: bind_cong => //.
  apply: functional_extensionality => y; by rewrite bind_assoc. }
rewrite E1 E2.
apply: r_bind_feq.
exact: (swap_code_seq s t ht).
Qed.

Lemma Lpp_notin_IGN0 : Lpp.1 \notin domm IGN0.
Proof. by rewrite domm_set domm0 in_fsetU1 in_fset0 orbF; apply/negP => /eqP. Qed.

Lemma Ltg_Lpp_neq : Ltg.1 != Lpp.1.
Proof.
by apply/eqP => H; move: Lpp_notin_IGN0;
   rewrite domm_set domm0 in_fsetU1 -H eqxx.
Qed.

Lemma loc_notin_IGN0 (l0 : Location) : l0.1 != Ltg.1 -> l0.1 \notin domm IGN0.
Proof. by move=> h; rewrite domm_set domm0 in_fsetU1 in_fset0 orbF. Qed.

(** Pin [pp] on [Lpp] (both sides, from [None]); preserves [ud0_inv]. *)
Lemma ud0_inv_pin (pp : PP) s0 s1 :
  ud0_inv (s0, s1) -> get_heap s0 Lpp = None ->
  ud0_inv (set_heap s0 Lpp (Some pp), set_heap s1 Lpp (Some pp)).
Proof.
move=> hinv hL.
case/ud0_invE: hinv => hign hRU.
have hL1 : get_heap s1 Lpp = None by rewrite -(hign _ Lpp_notin_IGN0).
move: hRU; rewrite hL => -[heL heR].
apply: ud0_invI; first exact: heap_ignore_set_both.
rewrite get_set_heap_eq.
rewrite (get_set_heap_neq _ _ _ _ Ltg_Lpp_neq).
rewrite (get_set_heap_neq _ _ _ _ Ltg_Lpp_neq).
by rewrite heL heR /=; move=> j; rewrite emptymE.
Qed.

(** Parallel same-value put at any location off [{Lpp, Ltg}] preserves
    [ud0_inv]. *)
Lemma ud0_inv_setboth (l0 : Location) (v : l0) s0 s1 :
  l0.1 != Lpp.1 -> l0.1 != Ltg.1 ->
  ud0_inv (s0, s1) ->
  ud0_inv (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> hpp htg hinv.
case/ud0_invE: hinv => hign hRU.
apply: ud0_invI; first exact: heap_ignore_set_both.
rewrite get_set_heap_neq; last by rewrite eq_sym.
rewrite get_set_heap_neq; last by rewrite eq_sym.
rewrite get_set_heap_neq; last by rewrite eq_sym.
exact: hRU.
Qed.

(** The LCOMMIT store update (both sides): [#put Ltg]; [#put Ltw], with the
    per-index [roots_map]-at-0 transform on the stored value; preserves
    [ud0_inv] (needs [Lpp = Some pp] committed on both sides, [size xs=l]). *)
Lemma ud0_inv_commit (pp : PP) (t : adrs_sf_ch) (md : D) (xs : seq N)
    (k : nat) (v : Ltw) s0 s1 :
  size xs = l ->
  get_heap s0 Lpp = Some pp -> get_heap s1 Lpp = Some pp ->
  ud0_inv (s0, s1) ->
  ud0_inv
    (set_heap (set_heap s0 Ltg (setm (get_heap s0 Ltg) k (t, (xs, md)))) Ltw v,
     set_heap (set_heap s1 Ltg
       (setm (get_heap s1 Ltg) k (t, (lrrmap t pp 0 md k xs, md)))) Ltw v).
Proof.
move=> hxs hpp0 hpp1 hinv.
case/ud0_invE: hinv => hign hRU.
move: hRU; rewrite hpp0 => hRU.
apply: ud0_invI.
- apply: heap_ignore_set_both.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- have hLppLtw : Lpp.1 != Ltw.1 by [].
  have hLppLtg : Lpp.1 != Ltg.1 by rewrite eq_sym; exact: Ltg_Lpp_neq.
  have hLtgLtw : Ltg.1 != Ltw.1 by [].
  rewrite (get_set_heap_neq _ _ _ _ hLppLtw) (get_set_heap_neq _ _ _ _ hLppLtg)
          hpp0.
  rewrite (get_set_heap_neq _ _ _ _ hLtgLtw) get_set_heap_eq.
  rewrite (get_set_heap_neq _ _ _ _ hLtgLtw) get_set_heap_eq.
  move=> j.
  have [->|hjk] := eqVneq j k.
  + rewrite setmE eqxx /=; split; first exact: hxs.
    by rewrite setmE eqxx.
  + rewrite !setmE (negbTE hjk).
    exact: hRU j.
Qed.

(** The pinned invariant, as a SINGLE applied atom (so [r_put_lhs] /
    [r_ret] unify the precond first-order). *)
Definition ud0_pin (pp : PP) : precond :=
  λ '(s0, s1),
    ud0_inv (s0, s1) /\ get_heap s0 Lpp = Some pp /\ get_heap s1 Lpp = Some pp.

Arguments ud0_pin : simpl never.

(** Couple the two lazy [Lpp] reads (both from the SHARED [Lpp]); land
    in a per-[pp] goal with [Lpp] pinned [Some pp] on both sides.  The
    game-vs-game analog of Compress's [r_pp2]. *)
Lemma r_ud0_pp2 {B : choiceType} (k0 k1 : PP -> raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), ud0_pin pp (s0, s1) ⦄
                 k0 pp ≈ k1 pp ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), ud0_inv (s0, s1) ⦄
     (ppo ← get Lpp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
           end ;; k0 pp)
   ≈ (ppo ← get Lpp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
           end ;; k1 pp) ⦃ post ⦄.
Proof.
move=> h.
eapply r_get_remember_lhs => lpp.
eapply r_get_remember_rhs => rpp.
eapply (r_fact (rpp = lpp)).
{ move=> s0 s1 [[hinv hr0] hr1].
  case/ud0_invE: hinv => hign _.
  rewrite /rem_inv /= in hr0 hr1.
  by rewrite -hr1 -(hign _ Lpp_notin_IGN0) hr0. }
move=> e; subst rpp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv hr0] hr1].
  rewrite /rem_inv /= in hr0 hr1.
  by rewrite /ud0_pin; split; [exact: hinv | split; [exact: hr0 | exact: hr1]].
- cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [[[hinv hr0] hr1] e0]] e1]].
  rewrite /rem_inv /= in hr0 hr1.
  subst s0 s1; rewrite /ud0_pin; split.
  + exact: (ud0_inv_pin pp s0' s1' hinv hr0).
  + by split; rewrite get_set_heap_eq.
Qed.

(** ENDPOINT (s = 0): re-rooting at position 0 is honest keygen
    ([roots_map 0 = sign_digits], [ends_from_roots_map0]); the pk is
    digit-independent ([rr_pkS = lpk], now [hl0_pk_E]); LSIGN/LCHECK
    couple [rr_sign]/[P_g1lS] with [mkm_signS]/[mkm_winSG] under the
    re-rooted store (the sign coupling is [hl0_lsg_E]). *)
Lemma Hl0_MIW (hw : (0 < w)%N) (b : bool) : perfect IKM (MIWkm b) (Hl b 0).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ud0_inv).
{ rewrite /ud0_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* LCOMMIT *)
  (* Align key sampling across the lazy public-parameter branch. *)
  destruct arg as [t md]. rewrite /mkm_commit /hl_commit.
  eapply r_get_remember_lhs => rvL.
  eapply r_get_remember_rhs => rvR.
  eapply (r_fact (rvR = rvL)).
  { move=> s0 s1 [[hinv hr0] hr1].
    have hd : Lrv.1 \notin domm IGN0 by apply: loc_notin_IGN0.
    case/ud0_invE: hinv => hign _.
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 -(hign _ hd) hr0. }
  move=> e; subst rvR.
  eapply r_assertD_same => hrev.
  eapply r_get_remember_lhs => twL.
  eapply r_get_remember_rhs => twR.
  eapply (r_fact (twR = twL)).
  { move=> s0 s1 [[[[hinv _] _] hC] hD].
    have hd : Ltw.1 \notin domm IGN0 by apply: loc_notin_IGN0.
    case/ud0_invE: hinv => hign _.
    rewrite /rem_inv /= in hC hD.
    by rewrite -hD -(hign _ hd) hC. }
  move=> e; subst twR.
  eapply r_assertD_same => hsz.
  eapply r_assertD_same => hfr.
  (* Pull the RHS's [sample_seq] to the front, past the lazy [Lpp] read. *)
  eapply r_get_remember_rhs => rppo.
  eapply r_transR.
  { eapply rsymmetry. eapply rsym_pre; first by [].
    eapply rpost_weaken_rule; first by apply: r_ss_pull.
    by move=> [??] [??] ->. }
  cbv beta. apply: r_ss_size => xs hxs.
  case Erp: rppo => [pp|].
  { (* SOME committed pp: the LHS's trailing [get Lpp] reads it (no reorder). *)
    simpl.
    eapply r_get_remember_lhs => ltgL.
    eapply r_get_remember_rhs => ltgR.
    eapply r_put_lhs; eapply r_put_rhs.
    eapply r_put_lhs; eapply r_put_rhs.
    eapply (r_get_lhs_known Lpp (Some pp)).
    { move=> s0 s1 [s1' [[s0' [[s1'' [[s0'' [Hb Es0']] Es1']] Es0]] Es1]].
      subst s0 s1 s0' s1'.
      move: Hb => [[[[[[ [hinv _] _] _] _] hLppR] _] _].
      rewrite /rem_inv /= in hLppR.
      have hpw : Lpp.1 != Ltw.1 by [].
      have hpg : Lpp.1 != Ltg.1 by rewrite eq_sym; exact: Ltg_Lpp_neq.
      rewrite (get_set_heap_neq _ _ _ _ hpw) (get_set_heap_neq _ _ _ _ hpg).
      case/ud0_invE: hinv => hign _.
      by rewrite (hign _ Lpp_notin_IGN0) hLppR. }
    simpl.
    apply r_ret => s0 s1 hpre; split;
      first by rewrite (hl0_pk_E hw pp t md (size twL) xs hxs).
    move: hpre => [s1' [[s0' [[s1'' [[s0'' [Hb Es0']] Es1']] Es0]] Es1]].
    subst s0 s1 s0' s1'.
    move: Hb => [[[[[[ [hinv _] _] _] _] hLppR] hLtgL] hLtgR].
    rewrite /rem_inv /= in hLppR hLtgL hLtgR.
    have hLppL : get_heap s0'' Lpp = Some pp.
    { case/ud0_invE: hinv => hign _; by rewrite (hign _ Lpp_notin_IGN0) hLppR. }
    rewrite -hLtgL -hLtgR.
    exact: (ud0_inv_commit pp t md xs (size twL) (rcons twL t) s0'' s1'' hxs
              hLppL hLppR hinv). }
  (* NONE: both draw a fresh pp; align the two [dPP] samples.  Bubble the LHS's
     [get Lpp]=None to the head, resolve it, then move the fresh [dPP] draw to
     the front past the pp-free stores ([r_swap_scheme_cmd] justifies each
     scheme/cmd swap), couple [dPP], pin [Lpp] ([ud0_inv_pin]), store. *)
  ssprove_swap_lhs 2%N. ssprove_swap_lhs 1%N. ssprove_swap_lhs 0%N.
  eapply (r_get_lhs_known Lpp None).
  { move=> s0 s1 [[[[[hinv _] _] _] _] hLppR].
    rewrite /rem_inv /= in hLppR.
    case/ud0_invE: hinv => hign _.
    by rewrite (hign _ Lpp_notin_IGN0) hLppR. }
  simpl.
  rewrite !bind_assoc /=.
  ssprove_swap_lhs 2%N; first by apply: (r_swap_scheme_cmd dPP); exact _.
  ssprove_swap_lhs 1%N; first by apply: (r_swap_scheme_cmd dPP); exact _.
  ssprove_swap_lhs 0%N; first by apply: (r_swap_scheme_cmd dPP); exact _.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp.
  ssprove_swap_lhs 2%N. ssprove_swap_lhs 1%N. ssprove_swap_lhs 0%N.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply r_get_remember_lhs => ltgL.
  eapply r_get_remember_rhs => ltgR.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply r_put_lhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre; split;
    first by rewrite (hl0_pk_E hw pp t md (size twL) xs hxs).
  move: hpre => [s1a [[s0a [[s1b [[s0b [Hb Es0b]] Es1b]] Es0a]] Es1a]].
  move: Hb => [[[s1c [[s0c [Hbase0 Es0c]] Es1c]] hLtgL] hLtgR].
  move: Hbase0 => [[[[[hinv _] _] _] _] hLppNone].
  rewrite /rem_inv /= in hLtgL hLtgR hLppNone.
  subst s0 s1 s0a s1a s0b s1b.
  have hLppN0 : get_heap s0c Lpp = None.
  { case/ud0_invE: hinv => hign _. by rewrite (hign _ Lpp_notin_IGN0) hLppNone. }
  rewrite -hLtgL -hLtgR.
  apply: (ud0_inv_commit pp t md xs (size twL) (rcons twL t)
            (set_heap s0c Lpp (Some pp)) (set_heap s1c Lpp (Some pp)) hxs);
    [ by rewrite get_set_heap_eq
    | by rewrite get_set_heap_eq
    | exact: (ud0_inv_pin pp s0c s1c hinv hLppN0) ].
- (* LGETPP *)
  rewrite /mkm_getpp.
  apply: r_ud0_pp2 => pp.
  eapply r_put_lhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  move: hpre => [s1' [[s0' [[hinv _] e0]] e1]]; subst s0 s1.
  split=> //.
  apply: ud0_inv_setboth; [ by [] | by [] | exact: hinv ].
- (* LCHECK *)
  destruct arg as [j mw].
  case: b; last by apply r_ret => s0 s1 hinv; split.
  rewrite /mkm_winSG /rr_winbody.
  eapply r_get_remember_lhs => rvL.
  eapply r_get_remember_rhs => rvR.
  eapply (r_fact (rvR = rvL)).
  { move=> s0 s1 [[hinv hr0] hr1].
    have hd : Lrv.1 \notin domm IGN0 by apply: loc_notin_IGN0.
    case/ud0_invE: hinv => hign _.
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 -(hign _ hd) hr0. }
  move=> e; subst rvR.
  eapply r_assertD_same => hrev.
  eapply r_get_remember_lhs => ltgL.
  eapply r_get_remember_rhs => ltgR.
  case E: (getm ltgL j) => [[t0 [xs md0]]|]; last first.
  { eapply (r_fact (ltgR j = None)).
    { move=> s0 s1 [[[[hinv _] _] hC] hD].
      rewrite /rem_inv /= in hC hD.
      case/ud0_invE: hinv => _ hRU.
      move: hRU; rewrite hC hD => hRU.
      case Ep: (get_heap s0 Lpp) hRU => [pp|] hRU.
      - by move: (hRU j); rewrite E.
      - by move: hRU => [_ ->]; rewrite emptymE. }
    move=> hR; rewrite hR.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split. }
  eapply r_get_remember_lhs => lpp.
  eapply (r_fact (exists pp, lpp = Some pp /\ size xs = l /\
                  ltgR j = Some (t0, (lrrmap t0 pp 0 md0 j xs, md0)))).
  { move=> s0 s1 [[[[[hinv _] _] hC] hD] hLpp].
    rewrite /rem_inv /= in hC hD hLpp.
    case/ud0_invE: hinv => _ hRU.
    move: hRU; rewrite hC hD => hRU.
    case Ep: (get_heap s0 Lpp) hRU => [pp|] hRU.
    - move: (hRU j); rewrite E => -[hsz hRj].
      exists pp; split; first by rewrite -hLpp.
      split; [exact: hsz | exact: hRj].
    - by move: hRU => [heL _]; rewrite heL emptymE in E. }
  move=> [pp [hlpp [hsz hRj]]].
  rewrite hlpp hRj /=.
  eapply (r_get_rhs_known Lpp (Some pp)).
  { move=> s0 s1 [[[[[hinv _] _] _] _] hLpp].
    rewrite /rem_inv /= in hLpp.
    case/ud0_invE: hinv => hign _.
    by rewrite -(hign _ Lpp_notin_IGN0) hLpp. }
  rewrite /=.
  rewrite /lPg1l /P_g1lS (hl0_pk_E hw pp t0 md0 j xs hsz).
  apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[[hinv _] _] _] _] _].
- (* LSIGN *)
  move: arg => j. rewrite /mkm_signS /rr_sign.
  eapply r_get_remember_lhs => slogL.
  eapply r_get_remember_rhs => slogR.
  eapply (r_fact (slogR = slogL)).
  { move=> s0 s1 [[hinv hr0] hr1].
    have hd : Lsl.1 \notin domm IGN0 by apply: loc_notin_IGN0.
    case/ud0_invE: hinv => hign _.
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 -(hign _ hd) hr0. }
  move=> e; subst slogR.
  eapply r_assertD_same => hns.
  eapply r_get_remember_lhs => ltgL.
  eapply r_get_remember_rhs => ltgR.
  case E: (getm ltgL j) => [[t0 [xs md0]]|]; last first.
  { eapply (r_fact (ltgR j = None)).
    { move=> s0 s1 [[[[hinv _] _] hC] hD].
      rewrite /rem_inv /= in hC hD.
      case/ud0_invE: hinv => _ hRU.
      move: hRU; rewrite hC hD => hRU.
      case Ep: (get_heap s0 Lpp) hRU => [pp|] hRU.
      - by move: (hRU j); rewrite E.
      - by move: hRU => [_ ->]; rewrite emptymE. }
    move=> hR; rewrite hR.
    apply r_ret => s0 s1 [[[[hinv _] _] _] _]; by split. }
  eapply r_get_remember_lhs => lpp.
  eapply (r_fact (exists pp, lpp = Some pp /\ size xs = l /\
                  ltgR j = Some (t0, (lrrmap t0 pp 0 md0 j xs, md0)))).
  { move=> s0 s1 [[[[[hinv _] _] hC] hD] hLpp].
    rewrite /rem_inv /= in hC hD hLpp.
    case/ud0_invE: hinv => _ hRU.
    move: hRU; rewrite hC hD => hRU.
    case Ep: (get_heap s0 Lpp) hRU => [pp|] hRU.
    - move: (hRU j); rewrite E => -[hsz hRj].
      exists pp; split; first by rewrite -hLpp.
      split; [exact: hsz | exact: hRj].
    - by move: hRU => [heL _]; rewrite heL emptymE in E. }
  move=> [pp [hlpp [hsz hRj]]].
  rewrite hlpp hRj /=.
  eapply (r_get_rhs_known Lpp (Some pp)).
  { move=> s0 s1 [[[[[hinv _] _] _] _] hLpp].
    rewrite /rem_inv /= in hLpp.
    case/ud0_invE: hinv => hign _.
    by rewrite -(hign _ Lpp_notin_IGN0) hLpp. }
  rewrite /=.
  case Ec: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t0).1
             (leaf_km.lcoord t0).2 pp md0) => [c|].
  + rewrite (hl0_lsg_E pp t0 md0 j xs c hsz Ec).
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre; split=> //.
    move: hpre => [s1' [[s0' [hpre0 e0]] e1]]; subst s0 s1.
    have hinv : ud0_inv (s0', s1') by move: hpre0 => [[[[[hinv _] _] _] _] _].
    apply: ud0_inv_setboth; [ by [] | by [] | exact: hinv ].
  + have -> : leaf_sign_c PP N D F Hgrind S_wn c_max pp t0 xs md0 = None.
    { rewrite /leaf_sign_c.
      exact: (shrincs_fxmss_wots_sign_None PP N D F Hgrind S_wn c_max
                (leaf_km.lcoord t0).1 (leaf_km.lcoord t0).2 pp xs md0 Ec). }
    apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; by split.
- (* LCOLLQ *)
  destruct arg as [t x]. rewrite /mkm_collq.
  apply: r_ud0_pp2 => pp. apply r_ret => s0 s1 [hinv _]; by split.
Qed.

(* ================================================================== *)
(** ** Infrastructure for the per-step perfects.

    [ud_inv] = Compress's [cp_inv] transposed to SM-UD locations, plus the
    ONE new component: a size/subset bound on the growing SM-UD tweak list
    [Utw].  The chain coupling grows [Utw]; the block-threaded chain lemmas
    [r_ud_chains_blk_real]/[_ideal] report the exact grown list, and the
    tail re-establishes [ud_inv] with the fresh leaf added. *)

(* ------------------------------------------------------------------ *)
(** *** Grind/digit reconstruction (mirror Compress lcp_pick_map/_digit_E). *)

Lemma lud_zip_filter (f : nat -> nat) (P : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | P ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | P (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (P (f c)) => /=; [|exact: IH].
Qed.

Lemma lud_pick_map (pp : PP) (zi : nat * nat) (md : D) :
  lud_pick [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = omap (fun c => (c, Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c)))
      (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md).
Proof.
rewrite /lud_pick lud_zip_filter /find_ctr.
have hf :
  [seq c <- iota 0 c_max
   | @grind_prp w l S_wn (Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c))]
  = [seq c <- iota 0 c_max | good_ctr PP D Hgrind S_wn zi.1 zi.2 pp md c].
  by apply: eq_filter => c;
     rewrite /grind_prp /good_ctr /valid_digest /digest_of.
by rewrite hf.
Qed.

Lemma lud_digit_E (pp : PP) (zi : nat * nat) (md : D) :
  lud_digit [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max]
  = (match find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md with
     | Some c => digest_of PP D Hgrind zi.1 zi.2 pp md c
     | None => nseq l w.-1
     end).
Proof.
rewrite /lud_digit lud_pick_map.
by case: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md) => [c|].
Qed.

Lemma lud_copt_E (pp : PP) (zi : nat * nat) (md : D) :
  omap fst (lud_pick [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs zi) (md, c) | c <- iota 0 c_max])
  = find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md.
Proof.
by rewrite lud_pick_map;
   case: (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp md) => [c|].
Qed.

(** [lud_digitS] at the honest grind list IS the slot-keyed re-root digit. *)
Lemma lud_digitS_E (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat) :
  lud_digitS j [seq Hgrind pp (shrincs_fxmss_wots_grind_adrs (lcoord t)) (md, c) | c <- iota 0 c_max]
  = rrdigS pp t md j.
Proof.
rewrite /lud_digitS /rrdigS /rr_digitS.
by rewrite lud_digit_E /rr_digit.
Qed.

Lemma size_lud_digitS (j : nat) (hs : seq nat) : size (lud_digitS j hs) = l.
Proof.
rewrite /lud_digitS /lud_digit; case: (lud_pick hs) => [ch|]; last by rewrite size_nseq.
exact: size_digits_w.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The tweaks queried by [lud_chains] (drive the [Utw] growth). *)

Fixpoint qtws (zi : nat * nat) (s st : nat) (ds : seq nat) : seq adrs_sf_ch :=
  match ds with
  | [::] => [::]
  | d :: ds' =>
      (if (s.+2 <= d)%N then [:: encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)] else [::])
      ++ qtws zi s st.+1 ds'
  end.

Lemma size_qtws (zi : nat * nat) (s st : nat) (ds : seq nat) :
  (size (qtws zi s st ds) <= size ds)%N.
Proof.
elim: ds st => [|d ds IH] st //=.
rewrite size_cat; case: (s.+2 <= d)%N => /=.
- by rewrite add1n ltnS.
- by rewrite add0n; apply: leqW.
Qed.

Lemma count_qtws (zi : nat * nat) (s st : nat) (ds : seq nat) :
  size (qtws zi s st ds) = count [pred d | (s.+2 <= d)%N] ds.
Proof.
elim: ds st => [|d ds IH] st //=.
rewrite size_cat IH /=; by case: (s.+2 <= d)%N.
Qed.

(** Every queried tweak is a chain tweak of [zi] at position [s], with a
    chain index in [iota st (size ds)]. *)
Lemma qtws_sub (zi : nat * nat) (s st : nat) (ds : seq nat) :
  {subset qtws zi s st ds
    <= [seq encode_adrs (shrincs_fxmss_wots_chain_adrs zi i s) | i <- iota st (size ds)]}.
Proof.
elim: ds st => [|d ds IH] st /=; first by move=> x.
move=> x; rewrite mem_cat in_cons => /orP[].
- case: (s.+2 <= d)%N; last by rewrite in_nil.
  by rewrite mem_seq1 => /eqP ->; rewrite eqxx.
- by move=> /IH ->; rewrite orbT.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The [Utw] budget/freshness structure. *)

(** All chain tweaks (positions [s], indices [< l]) of the committed leaves. *)
Definition utwset (s : nat) (ltw : seq adrs_sf_ch) : seq adrs_sf_ch :=
  flatten [seq [seq encode_adrs (shrincs_fxmss_wots_chain_adrs (lcoord x) i s) | i <- iota 0 l]
          | x <- ltw].

Definition utw_ok (s : nat) (ltw utw : seq adrs_sf_ch) : Prop :=
  (size utw <= (size ltw) * l)%N /\ {subset utw <= utwset s ltw}.

Lemma utwset_rcons (s : nat) (ltw : seq adrs_sf_ch) (t : adrs_sf_ch) :
  utwset s (rcons ltw t)
  = utwset s ltw
    ++ [seq encode_adrs (shrincs_fxmss_wots_chain_adrs (lcoord t) i s) | i <- iota 0 l].
Proof. by rewrite /utwset map_rcons -cats1 flatten_cat /= cats0. Qed.

Lemma utw_ok0 (s : nat) : utw_ok s [::] [::].
Proof. by split=> // x; rewrite in_nil. Qed.

(** The [Utw] structure re-establishes at a fresh leaf: the queried tweaks
    of the new leaf [t] (fresh coordinate) extend both bounds. *)
Lemma utw_ok_step (s : nat) (ltw : seq adrs_sf_ch) (utw : seq adrs_sf_ch)
    (t : adrs_sf_ch) (ds : seq nat) :
  size ds = l ->
  utw_ok s ltw utw ->
  utw_ok s (rcons ltw t) (utw ++ qtws (lcoord t) s 0 ds).
Proof.
move=> hds [hsz hsub]; split.
- rewrite size_cat size_rcons mulSn (addnC l (size ltw * l)).
  apply: leq_add; first exact: hsz.
  have hq := size_qtws (lcoord t) s 0 ds.
  have hle : (size ds <= l)%N by rewrite hds.
  exact: leq_trans hq hle.
- move=> x; rewrite mem_cat utwset_rcons mem_cat => /orP[hx|hx].
  + by rewrite (hsub x hx).
  + move: (qtws_sub (lcoord t) s 0 ds x hx); rewrite hds => ->; by rewrite orbT.
Qed.

(** Freshness of the new leaf's queried tweaks from [utw] (the invariant
    [subset]): a fresh leaf coordinate never collides with a committed
    leaf's chain tweaks. *)
Lemma chain_tweak_inj (zi zi' : nat * nat) (c c' pos : nat) :
  anchor_bounded zi -> anchor_bounded zi' ->
  (c < l)%N -> (c' < l)%N -> (pos < w.-1)%N ->
  @encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w zi c pos) =
    @encode_adrs l w (@shrincs_fxmss_wots_chain_adrs l w zi' c' pos) ->
  zi = zi' /\ c = c'.
Proof.
case: zi => z i; case: zi' => z' i' /=.
move=> hzi hzi' hc hc' hpos /encode_adrs_inj he.
have [ez ei ec _] := @shrincs_fxmss_wots_chain_adrs_inj l w z i c pos z' i' c' pos
  hzi hzi' (component_bounded_lt l c hc)
  (component_bounded_lt w.-1 pos hpos)
  (component_bounded_lt l c' hc')
  (component_bounded_lt w.-1 pos hpos) he.
split; [by rewrite ez ei | exact: ec].
Qed.

Lemma utw_fresh (s : nat) (ltw : seq adrs_sf_ch) (utw : seq adrs_sf_ch)
    (t : adrs_sf_ch) (j : nat) :
  (j < l)%N -> (s < w.-1)%N ->
  {subset utw <= utwset s ltw} ->
  gtw_of t \notin [seq gtw_of x | x <- ltw] ->
  encode_adrs (shrincs_fxmss_wots_chain_adrs (lcoord t) j s) \notin utw.
Proof.
move=> hj hs hsub hfr; apply/negP => /hsub.
rewrite /utwset => /flatten_mapP[x hx].
move=> /mapP[i hi he].
have hil : (i < l)%N by move: hi; rewrite mem_iota add0n.
have [hlc _] := chain_tweak_inj (lcoord t) (lcoord x) j i s
  (l2_lcoord_bounded t) (l2_lcoord_bounded x) hj hil hs he.
move: hfr => /negP; apply; apply/mapP; exists x; first exact: hx.
by rewrite hlc.
Qed.

(** The [ends_of] the reduction returns IS the WOTS+C completion (needed for
    the [Tl] pk identity), when the digit has length [l]. *)
Lemma ud_wendsE (pp : PP) (t : adrs_sf_ch) (ds : seq nat) (ys : seq N) :
  size ds = l ->
  ends_of PP N (Fw PP N F (lcoord t).1 (lcoord t).2) w pp 0 ds ys
  = complete_ends PP N F (lcoord t).1 (lcoord t).2 pp ds ys.
Proof. by move=> hds; rewrite /ends_of /complete_ends hds. Qed.

(* ------------------------------------------------------------------ *)
(** *** The invariant [ud_inv] (mirror Compress [cp_inv], transposed). *)

(** [IGNU] lists every cell of BOTH sides that the two runs may disagree
    on: the game's [Lpp ; Ltg ; Ltw ; Lrv ; Lsl], the reduction's [rud_*],
    and all three SM-UD cells [Upp ; Utw ; Urv].

    NB (history): [Upp] and [Urv] used to be omitted here, because [Upp]
    shared id [64] with [Lpp] and [Urv] shared id [66] with [Ltw], and
    [heap_ignore] ignores by ID — so they were ignored for free, and a
    literal listing would have made [IGNU] type-inconsistent (one key, two
    types) with the composite location union.  Those ids are now disjoint
    (see proof/LOCATIONS.md), so the two cells are listed honestly. *)
Definition IGNU : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rud_pp_loc ; rud_tgts_loc ; rud_tws_loc ; rud_rev_loc ; rud_slog_loc ;
        Upp ; Utw ; Urv ].

(** Per-index coherence of the game / reduction target tables (no third
    table, unlike Compress; the reduction's [copt] IS [find_ctr]). *)
Definition RUCrel (pp : PP)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))}) : Prop :=
  forall j,
    match getm ltg j with
    | Some (t0, (sg, md0)) =>
        getm rtg j = Some (t0, ((sg, md0), lfind t0 pp md0))
    | None => getm rtg j = None
    end.

Lemma RUCrel_empty (pp : PP) : RUCrel pp emptym emptym.
Proof. by move=> j; rewrite !emptymE. Qed.

Lemma RUCrel_qupd (pp : PP) (t : adrs_sf_ch) (md : D) (sg : seq N)
    (k : nat) ltg rtg :
  RUCrel pp ltg rtg ->
  RUCrel pp (setm ltg k (t, (sg, md)))
            (setm rtg k (t, ((sg, md), lfind t pp md))).
Proof.
move=> H j.
have [->|hjk] := eqVneq j k.
- by rewrite !setmE eqxx.
- rewrite setmE (negbTE hjk) setmE (negbTE hjk); exact: H j.
Qed.

(** The block precondition inside a COMMIT (no [utw_ok]: it fails mid chain
    recursion because the new leaf's tweaks are not yet in [ltw]; [utw_ok] is
    re-established at the tail via [utw_ok_step]). *)
Definition udpin (po : option PP) (lrv : bool) (lsl : seq nat)
    (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (utw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNU (s0, s1),
      [/\ get_heap s0 Lpp = po, get_heap s0 Lrv = lrv, get_heap s0 Lsl = lsl,
          get_heap s0 Ltw = ltw & get_heap s0 Ltg = ltg],
      [/\ get_heap s1 rud_pp_loc = (if lrv then po else None),
          get_heap s1 rud_rev_loc = lrv, get_heap s1 rud_slog_loc = lsl,
          get_heap s1 rud_tws_loc = ltw & get_heap s1 rud_tgts_loc = rtg],
      [/\ get_heap s1 Upp = po, get_heap s1 Urv = lrv & get_heap s1 Utw = utw]
    & match po with
      | None => [/\ ltg = emptym, rtg = emptym & lrv = false]
      | Some pp => RUCrel pp ltg rtg
      end].

Arguments udpin : simpl never.

(** The top-level relation (adds [utw_ok] to [udpin]-style pins). *)
Definition RU (s : nat)
    (lpp : option PP) (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (ltw : seq adrs_sf_ch) (lrv : bool) (lsl : seq nat)
    (rpp : option PP)
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (rtw : seq adrs_sf_ch) (rrv : bool) (rsl : seq nat)
    (upp : option PP) (utw : seq adrs_sf_ch) (urv : bool) : Prop :=
  [/\ rtw = ltw, rrv = lrv, rsl = lsl, rpp = (if lrv then lpp else None)
    & [/\ upp = lpp, urv = lrv, utw_ok s ltw utw
      & match lpp with
        | None => [/\ ltg = emptym, rtg = emptym & lrv = false]
        | Some pp => RUCrel pp ltg rtg
        end]].

Definition ud_inv (s : nat) : precond :=
  heap_ignore IGNU
  ⋊ rel_app [:: (lhs, Lpp) ; (lhs, Ltg) ; (lhs, Ltw) ; (lhs, Lrv) ; (lhs, Lsl) ;
                (rhs, rud_pp_loc) ; (rhs, rud_tgts_loc) ; (rhs, rud_tws_loc) ;
                (rhs, rud_rev_loc) ; (rhs, rud_slog_loc) ;
                (rhs, Upp) ; (rhs, Utw) ; (rhs, Urv) ] (RU s).

Arguments ud_inv : simpl never.

Lemma ud_invE (s : nat) s0 s1 :
  ud_inv s (s0, s1) ->
  heap_ignore IGNU (s0, s1) /\
  RU s (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rud_pp_loc) (get_heap s1 rud_tgts_loc) (get_heap s1 rud_tws_loc)
     (get_heap s1 rud_rev_loc) (get_heap s1 rud_slog_loc)
     (get_heap s1 Upp) (get_heap s1 Utw) (get_heap s1 Urv).
Proof. by move=> [h1 h2]; split. Qed.

Lemma ud_invI (s : nat) s0 s1 :
  heap_ignore IGNU (s0, s1) ->
  RU s (get_heap s0 Lpp) (get_heap s0 Ltg) (get_heap s0 Ltw) (get_heap s0 Lrv)
     (get_heap s0 Lsl)
     (get_heap s1 rud_pp_loc) (get_heap s1 rud_tgts_loc) (get_heap s1 rud_tws_loc)
     (get_heap s1 rud_rev_loc) (get_heap s1 rud_slog_loc)
     (get_heap s1 Upp) (get_heap s1 Utw) (get_heap s1 Urv) ->
  ud_inv s (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** The pinned invariant, as a SINGLE applied atom. *)
Definition ud_invL (s : nat) (pp : PP) : precond :=
  λ '(s0, s1), ud_inv s (s0, s1) /\ get_heap s0 Lpp = Some pp.

Arguments ud_invL : simpl never.

(* ------------------------------------------------------------------ *)
(** *** Block <-> invariant conversions (mirror Compress lcblk / cp_inv). *)

(** Put on [Utw] (rhs only) preserves the block (new [utw]). *)
Lemma udpin_set_utw (po : option PP) (lrv : bool) lsl ltw ltg rtg utw
    (v : Utw) s0 s1 :
  udpin po lrv lsl ltw ltg rtg utw (s0, s1) ->
  udpin po lrv lsl ltw ltg rtg v (s0, set_heap s1 Utw v).
Proof.
move=> [hign hL [hr1 hr2 hr3 hr4 hr5] [hu1 hu2 hu3] hm]; split.
- apply: heap_ignore_set_r; last exact: hign. by rewrite mem_domm.
- exact: hL.
- by split; rewrite get_set_heap_neq //.
- by split; [rewrite get_set_heap_neq // | rewrite get_set_heap_neq //
           | rewrite get_set_heap_eq].
- exact: hm.
Qed.

(** A [Some pp] block IS the invariant (given [utw_ok]). *)
Lemma udpin_ud_inv (s : nat) (pp : PP) lrv lsl ltw ltg rtg utw s0 s1 :
  udpin (Some pp) lrv lsl ltw ltg rtg utw (s0, s1) ->
  utw_ok s ltw utw ->
  ud_inv s (s0, s1).
Proof.
move=> [hign [hLpp hLrv hLsl hLtw hLtg] [hrpp hrrv hrsl hrtw hrtg]
        [hUpp hUrv hUtw] hm] hutw.
apply: ud_invI; first exact: hign.
rewrite /RU hLpp hLrv hLsl hLtw hLtg hrpp hrrv hrsl hrtw hrtg hUpp hUrv hUtw.
by split=> //; split=> //.
Qed.

(** The invariant gives the block (any [po]) once [rev = false]. *)
Lemma ud_inv_udpin (s : nat) s0 s1 :
  ud_inv s (s0, s1) -> get_heap s0 Lrv = false ->
  udpin (get_heap s0 Lpp) false (get_heap s0 Lsl) (get_heap s0 Ltw)
        (get_heap s0 Ltg) (get_heap s1 rud_tgts_loc) (get_heap s1 Utw) (s0, s1).
Proof.
move=> hinv hrv.
case/ud_invE: hinv => hign hRU.
case: hRU => hrtw hrrv hrsl hrpp [hupp hurv hutwok hm].
split.
- exact: hign.
- by [].
- by split=> //; rewrite ?hrpp ?hrrv hrv.
- by split=> //; rewrite ?hupp ?hurv hrv.
- move: hm; case: (get_heap s0 Lpp) => [pp|] hm; first exact: hm.
  by case: hm => he1 he2 he3; split.
Qed.

(** Extract [utw_ok] from the invariant. *)
Lemma ud_inv_utwok (s : nat) s0 s1 :
  ud_inv s (s0, s1) -> utw_ok s (get_heap s0 Ltw) (get_heap s1 Utw).
Proof.
by move=> hinv; case/ud_invE: hinv => _ [_ _ _ _ [_ _ ? _]].
Qed.

(** Pin [pp] on both [Lpp] (lhs) and [Upp] (rhs) from [None]. *)
Lemma udpin_set_both_pp (pp : PP) lsl ltw ltg rtg utw s0 s1 :
  udpin None false lsl ltw ltg rtg utw (s0, s1) ->
  udpin (Some pp) false lsl ltw ltg rtg utw
    (set_heap s0 Lpp (Some pp), set_heap s1 Upp (Some pp)).
Proof.
move=> [hign [hL1 hL2 hL3 hL4 hL5] [hr1 hr2 hr3 hr4 hr5] [hu1 hu2 hu3] hm].
case: hm => he1 he2 he3; split.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- by split; rewrite ?get_set_heap_eq ?get_set_heap_neq //.
- by split; rewrite get_set_heap_neq //.
- by split; rewrite ?get_set_heap_eq ?get_set_heap_neq //.
- by rewrite he1 he2; exact: RUCrel_empty.
Qed.

Lemma ud_inv_pin (s : nat) (pp : PP) s0 s1 :
  ud_inv s (s0, s1) -> get_heap s0 Lpp = None ->
  ud_inv s (set_heap s0 Lpp (Some pp), set_heap s1 Upp (Some pp)).
Proof.
move=> hinv hL.
have hrv : get_heap s0 Lrv = false.
  case/ud_invE: hinv => _ hRU.
  by move: hRU; rewrite hL => -[_ _ _ _ [_ _ _ [_ _ ->]]].
have hutw : utw_ok s (get_heap s0 Ltw) (get_heap s1 Utw) := ud_inv_utwok s s0 s1 hinv.
have hblk := ud_inv_udpin s s0 s1 hinv hrv.
move: hblk; rewrite hL => hblk.
apply: (udpin_ud_inv s pp false (get_heap s0 Lsl) (get_heap s0 Ltw)
          (get_heap s0 Ltg) (get_heap s1 rud_tgts_loc) (get_heap s1 Utw)).
- exact: (udpin_set_both_pp pp _ _ _ _ _ s0 s1 hblk).
- exact: hutw.
Qed.

(** GETPP reveal: [Lrv:=true] (lhs); [Urv:=true],[rud_pp:=Some pp],[rud_rev:=true]
    (rhs). *)
Lemma ud_inv_reveal (s : nat) (pp : PP) s0 s1 :
  ud_inv s (s0, s1) -> get_heap s0 Lpp = Some pp ->
  ud_inv s (set_heap s0 Lrv true,
            set_heap (set_heap (set_heap s1 Urv true) rud_pp_loc (Some pp))
              rud_rev_loc true).
Proof.
move=> hinv hL.
case/ud_invE: hinv => hign hRU.
move: hRU; rewrite hL => -[hrtw hrrv hrsl hrpp [hupp hurv hutwok hm]].
apply: ud_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RU. get_heap_simpl.
  split; [ exact: hrtw | by [] | exact: hrsl | by rewrite hL | ].
  split; [ by rewrite hupp hL | by [] | exact: hutwok | by rewrite hL; exact: hm ].
Qed.

(** LSIGN: set [Lsl] and [rud_slog] to the same value. *)
Lemma ud_inv_setsl (s : nat) (vw : seq nat) s0 s1 :
  ud_inv s (s0, s1) ->
  ud_inv s (set_heap s0 Lsl vw, set_heap s1 rud_slog_loc vw).
Proof.
move=> hinv.
case/ud_invE: hinv => hign hRU.
case: hRU => hrtw hrrv hrsl hrpp [hupp hurv hutwok hm].
apply: ud_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- rewrite /RU. get_heap_simpl.
  split; [ exact: hrtw | exact: hrrv | by [] | exact: hrpp | ].
  split; [ exact: hupp | exact: hurv | exact: hutwok | exact: hm ].
Qed.

(* ------------------------------------------------------------------ *)
(** *** Lazy-pp couplers (mirror Compress r_pp2 / r_lpin). *)

Lemma ud_bind_put_ret {A B : choiceType} (ℓ : Location) (v : ℓ) (a : A)
    (k : A -> raw_code B) :
  bind (#put ℓ := v ;; ret a) k = (#put ℓ := v ;; k a).
Proof. by []. Qed.

(** Couple the game's lazy [Lpp] read with SM-UD's lazy [Upp] read; land in a
    per-[pp] goal with the invariant, [Lpp] pinned. *)
Lemma r_ud_pp2 (s : nat) {B : choiceType} (k0 k1 : PP -> raw_code B)
    (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), ud_invL s pp (s0, s1) ⦄
                 k0 pp ≈ k1 pp ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), ud_inv s (s0, s1) ⦄
     (ppo ← get Lpp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
           end ;; k0 pp)
   ≈ (ppo ← get Upp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Upp := Some pp ;; ret pp
           end ;; k1 pp) ⦃ post ⦄.
Proof.
move=> h.
eapply r_get_remember_lhs => lpp.
eapply r_get_remember_rhs => upp.
eapply (r_fact (upp = lpp)).
  { move=> s0 s1 [[hinv hr0] hr1].
    case/ud_invE: hinv => _ [_ _ _ _ [hup _ _ _]].
    rewrite /rem_inv /= in hr0 hr1.
    by rewrite -hr1 hup hr0. }
move=> e; subst upp.
case: lpp h => [pp0|] h.
- eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv hr0] hr1].
  rewrite /rem_inv /= in hr0.
  by rewrite /ud_invL /=; split; [exact: hinv | exact: hr0].
- cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite !ud_bind_put_ret.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [[[hinv hr0] hr1] e0]] e1]].
  rewrite /rem_inv /= in hr0.
  subst s0 s1; rewrite /ud_invL /=; split.
  + exact: (ud_inv_pin s pp s0' s1' hinv hr0).
  + by rewrite get_set_heap_eq.
Qed.

(** The COMMIT pin: couple the game's lazy [Lpp] with the leading UCOLLQ pin's
    lazy [Upp] (grind member), landing in the [Some pp] block. *)
Lemma r_ud_lpin (b : bool) {B : choiceType} (po : option PP) lsl ltw ltg rtg utw
    (zi : nat * nat) (md : D)
    (k0 : PP -> raw_code B) (k1 : raw_code B) (post : postcond B B) :
  (forall pp,
     ⊢ ⦃ λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg utw (s0, s1) ⦄
        k0 pp ≈ k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), udpin po false lsl ltw ltg rtg utw (s0, s1) ⦄
     (ppo ← get Lpp ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
           end ;;
      k0 pp)
   ≈ bind (resolve (SMU b) lud_cqo
             (encode_adrs (shrincs_fxmss_wots_grind_adrs zi), inr (inr (inl (md, 0))))) (fun=> k1)
  ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_ud_cq b _ _).
case: po h => [pp0|] h.
- eapply (r_get_lhs_known Lpp (Some pp0)).
    { by move=> s0 s1 [_ [hh _ _ _ _] _ _ _]. }
  eapply (r_get_bind_rhs Upp (Some pp0)).
    { by move=> s0 s1 [_ _ _ [hh _ _] _]. }
  cbv beta iota.
  exact: (h pp0).
- eapply (r_get_lhs_known Lpp None).
    { by move=> s0 s1 [_ [hh _ _ _ _] _ _ _]. }
  eapply (r_get_bind_rhs Upp None).
    { by move=> s0 s1 [_ _ _ [hh _ _] _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite !ud_bind_put_ret.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [hpre e0]] e1]]; subst s0 s1.
  exact: (udpin_set_both_pp pp lsl ltw ltg rtg utw s0' s1' hpre).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The block-threaded chain couplings (grow [Utw] through the block). *)

Lemma udpin_Upp (po : option PP) lrv lsl ltw ltg rtg utw s0 s1 :
  udpin po lrv lsl ltw ltg rtg utw (s0, s1) -> get_heap s1 Upp = po.
Proof. by case=> _ _ _ [? _ _] _. Qed.
Lemma udpin_Urv (po : option PP) lrv lsl ltw ltg rtg utw s0 s1 :
  udpin po lrv lsl ltw ltg rtg utw (s0, s1) -> get_heap s1 Urv = lrv.
Proof. by case=> _ _ _ [_ ? _] _. Qed.
Lemma udpin_Utw (po : option PP) lrv lsl ltw ltg rtg utw s0 s1 :
  udpin po lrv lsl ltw ltg rtg utw (s0, s1) -> get_heap s1 Utw = utw.
Proof. by case=> _ _ _ [_ _ ?] _. Qed.

(** The REAL block chain coupling: [sample_seq] IS the linked [lud_chains]
    (SMU true), growing [Utw] by exactly [qtws]; produces the [roots_map] /
    completed [ends_of].  Adaptation of [r_ud_chains_real] with the full
    invariant block threaded. *)
Lemma r_ud_chains_blk_real {B : choiceType} (pp : PP) (zi : nat * nat)
    (s st : nat) (ds : seq nat)
    (lsl : seq nat) (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (utw : seq adrs_sf_ch)
    (K0 : chList N -> raw_code B) (K1 : chList N × chList N -> raw_code B)
    (post : postcond B B) :
  anchor_bounded zi ->
  (st + size ds <= l)%N ->
  wf_digits w ds ->
  (size utw + count [pred d | (s.+2 <= d)%N] ds <= n_max * l)%N ->
  (forall j : nat, (st <= j)%N -> (j < l)%N -> (s < w.-1)%N ->
     (encode_adrs (shrincs_fxmss_wots_chain_adrs zi j s) \notin utw)) ->
  (forall us : seq N,
     ⊢ ⦃ λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg
                        (utw ++ qtws zi s st ds) (s0, s1) ⦄
        K0 (roots_map PP N (Fw PP N F zi.1 zi.2) pp s st ds us)
      ≈ K1 (roots_map PP N (Fw PP N F zi.1 zi.2) pp s st ds us,
            ends_of PP N (Fw PP N F zi.1 zi.2) w pp st ds
              (roots_map PP N (Fw PP N F zi.1 zi.2) pp s st ds us)) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg utw (s0, s1) ⦄
     (xs ← sample_seq dN (size ds) ;;
      K0 (roots_map PP N (Fw PP N F zi.1 zi.2) pp s st ds xs))
   ≈ bind (code_link (lud_chains zi s st ds) (SMU true)) K1
  ⦃ post ⦄.
Proof.
move=> hzi hlen hwf.
elim: ds st utw K0 K1 hlen hwf => [|d ds IH] st utw K0 K1
  hlen hwf hcnt hfresh h /=.
- eapply (rpre_weaken_rule
    (λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg (utw ++ [::]) (s0, s1)));
    last by move=> s0 s1 hb; rewrite cats0.
  exact: (h [::]).
- move/andP: hwf => [hdw hwf].
  have hlen' : (st.+1 + size ds <= l)%N.
    by move: hlen; rewrite /= addnS addSn.
  have hstl : (st < l)%N := leq_trans (leq_addr (size ds) st.+1) hlen'.
  case: (boolP (s.+2 <= d)%N) => hd.
  + (* queried chain: inlined real UQUERY, then walk *)
    have hspos : (s < w.-1)%N.
      by rewrite ltn_predRL; exact: ltn_trans hd hdw.
    rewrite /= !bind_assoc.
    rewrite (resolve_ud_qy_true (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))).
    eapply (r_get_rhs_pin Urv false);
      first by move=> s0 s1; exact: udpin_Urv.
    simpl.
    eapply (r_get_rhs_pin Utw utw);
      first by move=> s0 s1; exact: udpin_Utw.
    have hlt : (size utw < n_max * l)%N.
    { apply: leq_trans hcnt; rewrite /= hd add1n addnS ltnS.
      exact: leq_addr. }
    have hni : (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s) \notin utw)
      := hfresh st (leqnn st) hstl hspos.
    rewrite hlt hni; simpl.
    eapply (r_put_rhs_pre Utw
      (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))) _
      (udpin (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))))).
    { move=> s0 s1 hpre; exact: (udpin_set_utw _ _ _ _ _ _ _ _ s0 s1 hpre). }
    eapply (r_get_rhs_pin Upp (Some pp));
      first by move=> s0 s1; exact: udpin_Upp.
    rewrite bind_ret_l.
    ssprove_code_simpl.
    rewrite -/bind bind_assoc.
    eapply r_scheme_bind; [exact _|] => x.
    rewrite bind_ret_l.
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec true pp zi
      (udpin (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))))
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)))) post).
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec true pp zi
      (udpin (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))))
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)))) post).
    rewrite code_link_bind bind_assoc.
    apply: (IH st.+1 (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)))
      (fun rm => K0 (chain (wots.scheme.chainf PP N
                       (Fw PP N F zi.1 zi.2) pp st) x
                       (minn s d.-1) (d - minn s d.-1) :: rm))).
    { exact: hlen'. }
    { exact: hwf. }
    { by move: hcnt; rewrite size_rcons /= hd add1n addSnnS. }
    { move=> j hj hjl hs; rewrite mem_rcons in_cons negb_or; apply/andP; split.
      - apply/eqP => he.
        have [_ ej] := chain_tweak_inj zi zi j st s hzi hzi hjl hstl hspos he.
        by move: hj; rewrite ej ltnn.
      - exact: hfresh (ltnW hj) hjl hs. }
    move=> us.
    rewrite code_link_ret_bind.
    have h0d : (0 < d)%N by apply: leq_trans (ltn0Sn s.+1) hd.
    have hsd1 : (s.+1 <= d.-1)%N by rewrite -ltnS (ltn_predK h0d).
    have hmin : minn s d.-1 = s by apply/minn_idPl; apply: ltnW hsd1.
    have hsd : (s < d)%N by apply: ltnW.
    have hds : (d - s = (d - s.+1).+1)%N by rewrite subnS prednK // subn_gt0.
    have esv : chain (wots.scheme.chainf PP N (Fw PP N F zi.1 zi.2) pp st)
                 x (minn s d.-1) (d - minn s d.-1)
               = chain (wots.scheme.chainf PP N (Fw PP N F zi.1 zi.2) pp st)
                   (F pp (decode_tweak (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))) x)
                   s.+1 (d - s.+1)
      by rewrite hmin hds decode_tweakK chainS.
    have hpre_eq : rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))
                     ++ qtws zi s st.+1 ds
                 = utw ++ qtws zi s st (d :: ds)
      by rewrite /= hd cat_rcons.
    rewrite hpre_eq -esv.
    exact: (h (x :: us)).
  + (* unqueried chain: local sample coupled with [sample_seq], then walks *)
    rewrite !bind_assoc; ssprove_code_simpl.
    rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
    rewrite bind_assoc.
    eapply r_scheme_bind; [exact _|] => x.
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec true pp zi (udpin (Some pp) false lsl ltw ltg rtg utw)
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg utw) post).
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec true pp zi (udpin (Some pp) false lsl ltw ltg rtg utw)
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg utw) post).
    rewrite code_link_bind bind_assoc.
    apply: (IH st.+1 utw
      (fun rm => K0 (chain (wots.scheme.chainf PP N
                       (Fw PP N F zi.1 zi.2) pp st) x
                       (minn s d.-1) (d - minn s d.-1) :: rm))).
    { exact: hlen'. }
    { exact: hwf. }
    { by move: hcnt; rewrite /= (negbTE hd) add0n. }
    { by move=> j hj hjl hs; exact: hfresh (ltnW hj) hjl hs. }
    move=> us; rewrite code_link_ret_bind.
    have hpre_eq : utw ++ qtws zi s st.+1 ds = utw ++ qtws zi s st (d :: ds)
      by rewrite /= (negbTE hd).
    rewrite hpre_eq; exact: (h (x :: us)).
Qed.

(** The IDEAL block chain coupling (SMU false: fresh [y<-dN], no F/pp),
    landing in [roots_map (s.+1)].  Adaptation of [r_ud_chains_ideal]. *)
Lemma r_ud_chains_blk_ideal {B : choiceType} (pp : PP) (zi : nat * nat)
    (s st : nat) (ds : seq nat)
    (lsl : seq nat) (ltw : seq adrs_sf_ch)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (utw : seq adrs_sf_ch)
    (K0 : chList N -> raw_code B) (K1 : chList N × chList N -> raw_code B)
    (post : postcond B B) :
  anchor_bounded zi ->
  (st + size ds <= l)%N ->
  wf_digits w ds ->
  (size utw + count [pred d | (s.+2 <= d)%N] ds <= n_max * l)%N ->
  (forall j : nat, (st <= j)%N -> (j < l)%N -> (s < w.-1)%N ->
     (encode_adrs (shrincs_fxmss_wots_chain_adrs zi j s) \notin utw)) ->
  (forall us : seq N,
     ⊢ ⦃ λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg
                        (utw ++ qtws zi s st ds) (s0, s1) ⦄
        K0 (roots_map PP N (Fw PP N F zi.1 zi.2) pp s.+1 st ds us)
      ≈ K1 (roots_map PP N (Fw PP N F zi.1 zi.2) pp s.+1 st ds us,
            ends_of PP N (Fw PP N F zi.1 zi.2) w pp st ds
              (roots_map PP N (Fw PP N F zi.1 zi.2) pp s.+1 st ds us)) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg utw (s0, s1) ⦄
     (xs ← sample_seq dN (size ds) ;;
      K0 (roots_map PP N (Fw PP N F zi.1 zi.2) pp s.+1 st ds xs))
   ≈ bind (code_link (lud_chains zi s st ds) (SMU false)) K1
  ⦃ post ⦄.
Proof.
move=> hzi hlen hwf.
elim: ds st utw K0 K1 hlen hwf => [|d ds IH] st utw K0 K1
  hlen hwf hcnt hfresh h /=.
- eapply (rpre_weaken_rule
    (λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg (utw ++ [::]) (s0, s1)));
    last by move=> s0 s1 hb; rewrite cats0.
  exact: (h [::]).
- move/andP: hwf => [hdw hwf].
  have hlen' : (st.+1 + size ds <= l)%N.
    by move: hlen; rewrite /= addnS addSn.
  have hstl : (st < l)%N := leq_trans (leq_addr (size ds) st.+1) hlen'.
  case: (boolP (s.+2 <= d)%N) => hd.
  + (* queried chain: inlined ideal UQUERY (fresh y), then walk *)
    have hspos : (s < w.-1)%N.
      by rewrite ltn_predRL; exact: ltn_trans hd hdw.
    rewrite /= !bind_assoc.
    rewrite (resolve_ud_qy_false (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))).
    eapply (r_get_rhs_pin Urv false);
      first by move=> s0 s1; exact: udpin_Urv.
    simpl.
    eapply (r_get_rhs_pin Utw utw);
      first by move=> s0 s1; exact: udpin_Utw.
    have hlt : (size utw < n_max * l)%N.
    { apply: leq_trans hcnt; rewrite /= hd add1n addnS ltnS.
      exact: leq_addr. }
    have hni : (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s) \notin utw)
      := hfresh st (leqnn st) hstl hspos.
    rewrite hlt hni; simpl.
    eapply (r_put_rhs_pre Utw
      (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))) _
      (udpin (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))))).
    { move=> s0 s1 hpre; exact: (udpin_set_utw _ _ _ _ _ _ _ _ s0 s1 hpre). }
    ssprove_code_simpl.
    rewrite -/bind bind_assoc.
    eapply r_scheme_bind; [exact _|] => x.
    rewrite bind_ret_l.
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec false pp zi
      (udpin (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))))
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)))) post).
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec false pp zi
      (udpin (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))))
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg
        (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)))) post).
    rewrite code_link_bind bind_assoc.
    apply: (IH st.+1 (rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s)))
      (fun rm => K0 (chain (wots.scheme.chainf PP N
                       (Fw PP N F zi.1 zi.2) pp st) x
                       (minn s.+1 d.-1) (d - minn s.+1 d.-1) :: rm))).
    { exact: hlen'. }
    { exact: hwf. }
    { by move: hcnt; rewrite size_rcons /= hd add1n addSnnS. }
    { move=> j hj hjl hs; rewrite mem_rcons in_cons negb_or; apply/andP; split.
      - apply/eqP => he.
        have [_ ej] := chain_tweak_inj zi zi j st s hzi hzi hjl hstl hspos he.
        by move: hj; rewrite ej ltnn.
      - exact: hfresh (ltnW hj) hjl hs. }
    move=> us.
    rewrite code_link_ret_bind.
    have hs1 : (s.+1 <= d.-1)%N
      by rewrite -ltnS (ltn_predK (leq_trans (ltn0Sn s.+1) hd)).
    have hmin : minn s.+1 d.-1 = s.+1 by apply/minn_idPl.
    have esv : chain (wots.scheme.chainf PP N (Fw PP N F zi.1 zi.2) pp st)
                 x (minn s.+1 d.-1) (d - minn s.+1 d.-1)
               = chain (wots.scheme.chainf PP N (Fw PP N F zi.1 zi.2) pp st)
                   x s.+1 (d - s.+1)
      by rewrite hmin.
    have hpre_eq : rcons utw (encode_adrs (shrincs_fxmss_wots_chain_adrs zi st s))
                     ++ qtws zi s st.+1 ds
                 = utw ++ qtws zi s st (d :: ds)
      by rewrite /= hd cat_rcons.
    rewrite hpre_eq -esv.
    exact: (h (x :: us)).
  + (* unqueried chain: local sample, then two walks; [minn s d.-1 =
       minn s.+1 d.-1 = d.-1] *)
    have hle : (d <= s.+1)%N by move: hd; rewrite -ltnNge ltnS.
    have hds : (d.-1 <= s)%N by rewrite -subn1 leq_subLR add1n.
    have hmin : minn s d.-1 = minn s.+1 d.-1
      by rewrite (minn_idPr hds) (minn_idPr (leq_trans hds (leqnSn s))).
    rewrite hmin.
    rewrite !bind_assoc; ssprove_code_simpl.
    rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
    rewrite bind_assoc.
    eapply r_scheme_bind; [exact _|] => x.
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec false pp zi (udpin (Some pp) false lsl ltw ltg rtg utw)
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg utw) post).
    rewrite code_link_bind bind_assoc.
    eapply (r_ud_walk_spec false pp zi (udpin (Some pp) false lsl ltw ltg rtg utw)
      (@udpin_Upp (Some pp) false lsl ltw ltg rtg utw) post).
    rewrite code_link_bind bind_assoc.
    apply: (IH st.+1 utw
      (fun rm => K0 (chain (wots.scheme.chainf PP N
                       (Fw PP N F zi.1 zi.2) pp st) x
                       (minn s.+1 d.-1) (d - minn s.+1 d.-1) :: rm))).
    { exact: hlen'. }
    { exact: hwf. }
    { by move: hcnt; rewrite /= (negbTE hd) add0n. }
    { by move=> j hj hjl hs; exact: hfresh (ltnW hj) hjl hs. }
    move=> us; rewrite code_link_ret_bind.
    have hpre_eq : utw ++ qtws zi s st.+1 ds = utw ++ qtws zi s st (d :: ds)
      by rewrite /= (negbTE hd).
    rewrite hpre_eq; exact: (h (x :: us)).
Qed.

Lemma size_rrdigS (pp : PP) (t : adrs_sf_ch) (md : D) (j : nat) :
  size (rrdigS pp t md j) = l.
Proof.
rewrite /rrdigS /rr_digitS /rr_digit;
  case: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
           (leaf_km.lcoord t).2 pp md) => [c|];
  [exact: (size_digest_of PP D Hgrind (leaf_km.lcoord t).1
             (leaf_km.lcoord t).2 pp md c) | exact: size_nseq].
Qed.

Lemma wf_rrdigS (hw : (0 < w)%N) (pp : PP) (t : adrs_sf_ch)
    (md : D) (j : nat) :
  wf_digits w (rrdigS pp t md j).
Proof.
rewrite /rrdigS /rr_digitS /rr_digit.
case E: (find_ctr PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
           (leaf_km.lcoord t).2 pp md) => [c|].
- by move: (find_ctr_good PP D Hgrind S_wn c_max (leaf_km.lcoord t).1
             (leaf_km.lcoord t).2 pp md c E) => /andP[h1 _].
- by rewrite /wf_digits all_nseq ltn_predL hw orbT.
Qed.

(** The COMMIT tail (real/ideal shared): UCOLLQ.Tl compression + dual store,
    re-establishing [ud_inv].  This is the [h]-obligation of the block chain
    lemma, after the leaf's chains have been coupled. *)
Lemma r_ud_tail (b : bool) (s : nat) (pp : PP) (t : adrs_sf_ch) (md : D)
    (ltw : seq adrs_sf_ch) (sg ends : seq N) (lsl : seq nat)
    (ltg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (rtg : {fmap nat -> (adrs_sf_ch × (('list N × D) × 'option 'nat))})
    (utw' : seq adrs_sf_ch) :
  (size ltw < n_max)%N ->
  gtw_of t \notin [seq gtw_of x | x <- ltw] ->
  RUCrel pp ltg rtg ->
  utw_ok s (rcons ltw t) utw' ->
  Tl pp (shrincs_fxmss_wots_pk_adrs (lcoord t)) ends = rrpkS pp t md (size ltw) sg ->
  ⊢ ⦃ λ '(s0, s1), udpin (Some pp) false lsl ltw ltg rtg utw' (s0, s1) ⦄
     (tgts ← get Ltg ;;
      #put Ltg := setm tgts (size ltw) (t, (sg, md)) ;;
      #put Ltw := rcons ltw t ;;
      ret (rrpkS pp t md (size ltw) sg))
   ≈ bind (resolve (SMU b) lud_cqo (gtw_of t, inr (inr (inr ends))))
       (fun r =>
          tgts ← get rud_tgts_loc ;;
          #put rud_tgts_loc := setm tgts (size ltw) (t, ((sg, md), lfind t pp md)) ;;
          #put rud_tws_loc := rcons ltw t ;;
          ret (if r is inr (inr (inr h)) then h else n0))
   ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ ud_inv s (s0, s1) ⦄.
Proof.
move=> hsz hfr hRC hutw hpk.
eapply (r_ud_collq_known b pp (gtw_of t) (inr (inr (inr ends)))
          (udpin (Some pp) false lsl ltw ltg rtg utw')
          (fun s0 s1 h => udpin_Upp _ _ _ _ _ _ _ s0 s1 h)).
cbv beta.
rewrite collq_udT_E.
eapply (r_get_lhs_known Ltg ltg).
  { by move=> s0 s1; case=> _ [_ _ _ _ ?] _ _ _. }
eapply (r_get_rhs_known rud_tgts_loc rtg).
  { by move=> s0 s1; case=> _ _ [_ _ _ _ ?] _ _. }
apply r_put_lhs; apply r_put_rhs.
apply r_put_lhs; apply r_put_rhs.
apply r_ret => s0 s1 hpre.
move: hpre =>
  [s1' [[s0' [[s1'' [[s0'' [hb E_s0']] E_s1']] E_s0]] E_s1]].
subst s0 s1 s0' s1'.
case: hb => hign [hLpp hLrv hLsl hLtw hLtg] [hrpp hrrv hrsl hrtw hrtg]
              [hUpp hUrv hUtw] _.
split.
- by rewrite hpk.
- apply: ud_invI.
  + apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign.
  + rewrite /RU. get_heap_simpl.
    rewrite hLpp hLrv hLsl hrrv hrsl hrpp hUpp hUrv hUtw.
    split; [ by [] | by [] | by [] | by [] | ].
    split; [ by [] | by [] | exact: hutw | ].
    exact: (RUCrel_qupd pp t md sg (size ltw) ltg rtg hRC).
Qed.

(* ------------------------------------------------------------------ *)
(** *** code_link push helpers (keep [code_link] FOLDED past a get / op, so
    [code_link_assertD] can subsequently fire — the getr/opr iota-reduction
    otherwise unfolds [code_link] to its [fix]). *)

Lemma code_link_getr {B : choiceType} (ll : Location) (kk : ll -> raw_code B)
    (pp : raw_package) :
  code_link (x ← get ll ;; kk x) pp = (x ← get ll ;; code_link (kk x) pp).
Proof. by []. Qed.

Lemma code_link_opr {B : choiceType} (o : opsig) (m : src o)
    (kk : tgt o -> raw_code B) (pp : raw_package) :
  code_link (x ← op o ⋅ m ;; kk x) pp = (r ← resolve pp o m ;; code_link (kk r) pp).
Proof. by []. Qed.

(** [get]-push through an outer [bind] (mirror [code_link_getr] for plain
    [bind]): commutes a leading lazy read to the front so a subsequent
    [bind_assoc] can fire (used to reshape the resolved UCOLLQ into the
    [r_ud_pp2] shape in the LCOLLQ arm). *)
Lemma bind_getr {A2 B2 : choiceType} (ll : Location) (kk0 : ll -> raw_code A2)
    (gg : A2 -> raw_code B2) :
  bind (y ← get ll ;; kk0 y) gg = (y ← get ll ;; bind (kk0 y) gg).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** *** The COMMIT pin (mirror Compress r_pin_commit). *)

Definition ud_bpre (s : nat) (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  ud_inv s (s0, s1) /\ get_heap s0 Lrv = false /\ (size ltw < n_max)%N /\
  get_heap s0 Ltw = ltw /\ gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments ud_bpre : simpl never.

Definition ud_bcm (s : nat) (pp : PP) (t : adrs_sf_ch) (ltw : seq adrs_sf_ch) : precond :=
  λ '(s0, s1),
  ud_inv s (s0, s1) /\ get_heap s0 Lpp = Some pp /\ get_heap s0 Lrv = false /\
  (size ltw < n_max)%N /\ get_heap s0 Ltw = ltw /\
  gtw_of t \notin [seq gtw_of x | x <- ltw].

Arguments ud_bcm : simpl never.

Lemma ud_bcm_Upp (s : nat) (pp : PP) t ltw s0 s1 :
  ud_bcm s pp t ltw (s0, s1) -> get_heap s1 Upp = Some pp.
Proof.
move=> [hinv [hlpp _]]; case/ud_invE: hinv => _ [_ _ _ _ [hup _ _ _]].
by rewrite hup hlpp.
Qed.

(** Couple the game's lazy [Lpp] with the leading UCOLLQ pin's [Upp] (via
    [resolve]); land in [ud_bcm pp t ltw]. *)
Lemma r_ud_pin_commit (b : bool) (s : nat) {B : choiceType} (t : adrs_sf_ch)
    (ltw : seq adrs_sf_ch) (md : D)
    (k0 : PP -> raw_code B) (k1 : raw_code B) (post : postcond B B) :
  (forall pp, ⊢ ⦃ λ '(s0, s1), ud_bcm s pp t ltw (s0, s1) ⦄ k0 pp ≈ k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), ud_bpre s t ltw (s0, s1) ⦄
     (ppo ← get Lpp ;;
      match ppo with
      | Some pp => k0 pp
      | None => pp ← dPP ;; #put Lpp := Some pp ;; k0 pp
      end)
   ≈ bind (resolve (SMU b) lud_cqo
             (encode_adrs (shrincs_fxmss_wots_grind_adrs (lcoord t)), inr (inr (inl (md, 0)))))
       (fun=> k1)
  ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_ud_cq b _ _).
eapply r_get_remember_lhs => lpp.
case: lpp h => [pp0|] h.
- (* Some pp0: the game's [Lpp] already holds [pp0], so (by [RU]) does [Upp];
     [r_get_bind_rhs] peels the pin's [get Upp] KNOWING [pp0] (keeping [bind]
     folded, unlike [r_get_remember_rhs] which unfolds to a [fix]). *)
  eapply (r_get_bind_rhs Upp (Some pp0)).
  { move=> s0 s1 [[hinv _] hr0].
    case/ud_invE: hinv => _ [_ _ _ _ [hup _ _ _]].
    rewrite /rem_inv /= in hr0. by rewrite hup hr0. }
  cbv beta iota.
  eapply rpre_weaken_rule; first exact: (h pp0).
  move=> s0 s1 [[hinv [hrv [hsz [hltw hfr]]]] hr0].
  rewrite /rem_inv /= in hr0.
  rewrite /ud_bcm /=.
  by split; [exact: hinv | split; [exact: hr0|split; [exact: hrv|
     split; [exact: hsz|split; [exact: hltw|exact: hfr]]]]].
- (* None (pin-before-first-commit): [Lpp = None] ⟹ (by [RU]) [Upp = None];
     peel both fresh reads with [r_get_bind_rhs] (folded [bind]), then couple
     the two [dPP] draws and pin.  Mirrors [r_ud_lpin]'s None branch. *)
  eapply (r_get_bind_rhs Upp None).
  { move=> s0 s1 [[hinv _] hr0].
    case/ud_invE: hinv => _ [_ _ _ _ [hup _ _ _]].
    rewrite /rem_inv /= in hr0. by rewrite hup hr0. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply rpre_weaken_rule; first exact: (h pp).
  move=> s0 s1 [s1' [[s0' [[[hinv [hrv [hsz [hltw hfr]]]] hr0] e0]] e1]].
  rewrite /rem_inv /= in hr0.
  subst s0 s1.
  rewrite /ud_bcm.
  split; first exact: (ud_inv_pin s pp s0' s1' hinv hr0).
  get_heap_simpl.
  rewrite hrv hltw.
  split; first by [].
  split; first by [].
  split; first exact: hsz.
  split; first by [].
  exact: hfr.
Qed.

(** The real per-step perfect: LCOMMIT = [r_ud_grind_spec] (grind, pure
    [lud_digitS = rrdigS]) fused with [r_ud_chains_real] (chains ->
    roots_map/ends_of) + the [rr_pkS = Tl
    ends] pk identity; the other arms mirror [R_cp_leaf_real].  NB: the
    reduction's LSIGN now reads the STORED grind counter [copt] (mirroring
    [R_cp_leaf] — see [rud_tgts_loc]/LSIGN), so no pp is needed
    before reveal; the invariant's RCrel decorates [rud_tgts_loc] with
    [copt = omap fst (lud_pick hs) = find_ctr(committed pp)] exactly like
    Compress's [RCrel]. *)
Lemma Hl_real_perfect (hw : (0 < w)%N) (b : bool) (s : nat) :
  perfect IKM (Hl b s) (R_ud_leaf b s ∘ SMU true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (ud_inv s)).
apply: Invariant_inv_conj; first (apply: Invariant_heap_ignore; by fmap_solve).
apply: SemiInvariant_relApp; first by rewrite /rel_in /=.
by rewrite /rel_empty /RU /=.
simplify_eq_rel arg.
- (* LCOMMIT *)
  case: arg => t md.
  rewrite /hl_commit.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ud_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  rewrite code_link_getr.
  eapply r_get_remember_lhs => ltws.
  eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/ud_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws.
  rewrite code_link_assertD.
  eapply r_assertD_same => hsz.
  rewrite code_link_assertD.
  eapply r_assertD_same => hfr.
  rewrite code_link_opr.
  eapply rpre_weaken_rule with (pre := λ '(s0,s1), ud_bpre s t ltws (s0,s1)); last first.
    { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
      rewrite /rem_inv /= in hr0 hr2.
      rewrite /ud_bpre; split; first exact: hinv.
      split; first by rewrite hr0 (negbTE erev).
      split; first exact: hsz.
      split; first exact: hr2.
      exact: hfr. }
  eapply (r_ud_pin_commit true) => pp.
  rewrite code_link_bind.
  eapply (r_ud_grind_spec true pp (lcoord t) md (iota 0 c_max) (ud_bcm s pp t ltws)
            (fun s0 s1 hh => ud_bcm_Upp s pp t ltws s0 s1 hh)).
  cbv beta.
  rewrite lud_digitS_E code_link_bind.
  rewrite -[l in sample_seq dN l](size_rrdigS pp t md (size ltws)).
  apply rpre_hypothesis_rule => s0 s1 hbcm.
  move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
  have hutwok := ud_inv_utwok s s0 s1 hinv.
  have hRC : RUCrel pp (get_heap s0 Ltg) (get_heap s1 rud_tgts_loc).
    { case/ud_invE: hinv => _ hRU; move: hRU; rewrite hlpp => -[_ _ _ _ [_ _ _ hm]].
      exact: hm. }
  rewrite /rr_F.
  eapply rpre_weaken_rule; last first.
    { move=> s2 s3 /= [-> ->].
      have hblk := ud_inv_udpin s s0 s1 hinv hrv; rewrite hlpp hltw in hblk.
      exact: hblk. }
  eapply (r_ud_chains_blk_real pp (lcoord t) s 0 (rrdigS pp t md (size ltws))
    (get_heap s0 Lsl) ltws (get_heap s0 Ltg) (get_heap s1 rud_tgts_loc) (get_heap s1 Utw)
    (fun rm => tgts ← get Ltg ;;
       #put Ltg := setm tgts (size ltws) (t, (rm, md)) ;;
       #put Ltw := rcons ltws t ;;
       ret (rrpkS pp t md (size ltws) rm))).
    { exact: l2_lcoord_bounded. }
    { by rewrite add0n size_rrdigS. }
    { exact: wf_rrdigS. }
    { apply: (@leq_trans ((size ltws).+1 * l)).
      { rewrite mulSn (addnC l); apply: leq_add.
        { by move: hutwok; rewrite hltw => -[hh _]. }
        { have hc := count_size [pred d | (s.+2 <= d)%N]
              (rrdigS pp t md (size ltws)).
          by move: hc; rewrite size_rrdigS. } }
      { rewrite leq_mul2r; apply/orP; right; exact: hsz'. } }
    { move=> j _ hj hs; move: hutwok; rewrite hltw => -[_ hsub].
      exact: (utw_fresh s ltws (get_heap s1 Utw) t j hj hs hsub hfr'). }
    { move=> us.
      rewrite (lud_copt_E pp (lcoord t) md).
      rewrite code_link_opr.
      eapply (r_ud_tail true s pp t md ltws _ _ (get_heap s0 Lsl) (get_heap s0 Ltg)
        (get_heap s1 rud_tgts_loc)
        (get_heap s1 Utw ++ qtws (lcoord t) s 0 (rrdigS pp t md (size ltws)))).
        { exact: hsz'. }
        { exact: hfr'. }
        { exact: hRC. }
        { apply: utw_ok_step; [exact: size_rrdigS | by move: hutwok; rewrite hltw]. }
        { rewrite (ud_wendsE pp t (rrdigS pp t md (size ltws)) _
                    (size_rrdigS pp t md (size ltws))).
          by rewrite /rrpkS. } }
- (* LGETPP *)
  rewrite /mkm_getpp; setoid_rewrite bind_assoc; eapply r_ud_pp2 => pp.
  rewrite ud_bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  move: hpre => [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst.
  rewrite /ud_invL /= in hinv hL.
  split=> //.
  exact: (ud_inv_reveal s pp s0' _ hinv hL).
- (* LCHECK *)
  case: arg => j mw.
  case: b; last first.
    { apply r_ret => s0 s1 hinv; split; [by [] | exact: hinv]. }
  rewrite /rr_winbody.
  eapply r_get_remember_lhs => lrev.
  rewrite code_link_getr.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ud_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  rewrite code_link_getr.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
    { eapply (r_fact (getm rtg j = None)).
        { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
          rewrite /rem_inv /= in hr2 hr3.
          case/ud_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
          move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
          { by move: (hm j); rewrite hr2 E /= -hr3 => ->. }
          { by case: hm => _ hre _; rewrite -hr3 hre emptymE. } }
      move=> hrtgj.
      rewrite hrtgj.
      apply r_ret => s0 s1 [[[[hinv _] _] _] _]; split; [by [] | exact: hinv]. }
  eapply r_get_remember_lhs => lpp'.
  eapply (r_fact (exists pp, lpp' = Some pp /\
            getm rtg j = Some (t0, ((sg, md0), lfind t0 pp md0)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
      have hlrv : get_heap s0 Lrv = true by rewrite hr0 erev.
      case/ud_invE: hinv => _ hRU.
      move: hRU; case El: (get_heap s0 Lpp) => [pp|] hRU.
      { exists pp; split; first by rewrite -hr4.
        case: hRU => _ _ _ _ [_ _ _ hm].
        by move: (hm j); rewrite hr2 E /= -hr3. }
      { case: hRU => _ _ _ _ [_ _ _ hm].
        case: hm => _ _ habs; rewrite habs in hlrv; discriminate hlrv. } }
  move=> [pp [hlpp hrtgj]].
  rewrite hlpp hrtgj /=.
  eapply (r_get_rhs_known rud_pp_loc (Some pp)).
    { move=> s0 s1 [[[[[hinv hrev] _] _] _] hpp].
      rewrite /rem_inv /= in hrev hpp.
      case/ud_invE: hinv => _ hRU.
      case: hRU => _ _ _ hrpp _.
      by rewrite hrpp hrev erev /= hpp. }
  cbv beta iota.
  apply r_ret => s0 s1 hpre.
  split; first by [].
  by case: hpre => [[[[[hinv _] _] _] _] _].
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ud_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  rewrite code_link_assertD.
  eapply r_assertD_same => _.
  rewrite code_link_getr.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
    { eapply (r_fact (getm rtg j = None)).
        { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
          rewrite /rem_inv /= in hr2 hr3.
          case/ud_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
          move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
          { by move: (hm j); rewrite hr2 E /= -hr3 => ->. }
          { by case: hm => _ hre _; rewrite -hr3 hre emptymE. } }
      move=> hrtgj; rewrite hrtgj.
      apply r_ret => s0 s1 [[[[hinv _] _] _] _]; split; [by [] | exact: hinv]. }
  eapply r_get_remember_lhs => lpp'.
  eapply (r_fact (exists pp, lpp' = Some pp /\
            getm rtg j = Some (t0, ((sg, md0), lfind t0 pp md0)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr2 hr3 hr4.
      case/ud_invE: hinv => _ hRU.
      move: hRU; case El: (get_heap s0 Lpp) => [pp|] hRU.
      { exists pp; split; first by rewrite -hr4.
        case: hRU => _ _ _ _ [_ _ _ hm].
        by move: (hm j); rewrite hr2 E /= -hr3. }
      { case: hRU => _ _ _ _ [_ _ _ hm].
        case: hm => he1 _ _; move: E; rewrite -hr2 he1 emptymE => Hd; discriminate Hd. } }
  move=> [pp [hlpp hrtgj]].
  rewrite hlpp hrtgj /=.
  case E2: (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0)
    => [c|].
    { apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [hpre e0]] e1]]; subst s0 s1.
      move: hpre => [[[[[hinv _] _] _] _] _].
      split=> //.
      exact: (ud_inv_setsl s (rcons slog j) s0' s1' hinv). }
  apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; split; [by [] | exact: hinv].
- (* LCOLLQ *)
  case: arg => t x.
  have HE : forall (xx : tc_M CUD_leaf) (kk : tc_N CUD_leaf -> raw_code (N ∐ 'nat)),
    bind (resolve (SMU true) lud_cqo (t, xx)) kk
    = (ppo ← get Upp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Upp := Some pp ;; ret pp
            end ;;
       kk (tc_eval CUD_leaf pp t xx)).
    { move=> xx kk. rewrite (resolve_ud_cq true t xx) bind_getr.
      setoid_rewrite bind_assoc. by []. }
  rewrite /mkm_collq.
  case: x => [xy|dc].
    { rewrite code_link_opr HE.
      eapply r_ud_pp2 => pp.
      apply r_ret => s0 s1 [hinv hL].
      split; last exact: hinv.
      by rewrite /tc_eval /CUD_leaf. }
  rewrite code_link_opr HE.
  eapply r_ud_pp2 => pp.
  apply r_ret => s0 s1 [hinv hL].
  split; last exact: hinv.
  by rewrite /tc_eval /CUD_leaf.
Qed.

(** The ideal per-step perfect mirrors [Hl_real_perfect] with [SMU false].
    The fresh [y <- dN] branch lands in [roots_map s.+1]. *)
Lemma Hl_ideal_perfect (hw : (0 < w)%N) (b : bool) (s : nat) :
  perfect IKM (Hl b s.+1) (R_ud_leaf b s ∘ SMU false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (ud_inv s)).
apply: Invariant_inv_conj; first (apply: Invariant_heap_ignore; by fmap_solve).
apply: SemiInvariant_relApp; first by rewrite /rel_in /=.
by rewrite /rel_empty /RU /=.
simplify_eq_rel arg.
- (* LCOMMIT *)
  case: arg => t md.
  rewrite /hl_commit.
  ssprove_code_simpl; simpl.
  eapply r_get_remember_lhs => lrev.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ud_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  rewrite code_link_getr.
  eapply r_get_remember_lhs => ltws.
  eapply r_get_remember_rhs => rtws.
  eapply (r_fact (rtws = ltws)).
    { move=> s0 s1 [[[[hinv _] _] hr0] hr1].
      case/ud_invE: hinv => _ [hrtw _ _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrtw hr0. }
  move=> e; subst rtws.
  rewrite code_link_assertD.
  eapply r_assertD_same => hsz.
  rewrite code_link_assertD.
  eapply r_assertD_same => hfr.
  rewrite code_link_opr.
  eapply rpre_weaken_rule with (pre := λ '(s0,s1), ud_bpre s t ltws (s0,s1)); last first.
    { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
      rewrite /rem_inv /= in hr0 hr2.
      rewrite /ud_bpre; split; first exact: hinv.
      split; first by rewrite hr0 (negbTE erev).
      split; first exact: hsz.
      split; first exact: hr2.
      exact: hfr. }
  eapply (r_ud_pin_commit false) => pp.
  rewrite code_link_bind.
  eapply (r_ud_grind_spec false pp (lcoord t) md (iota 0 c_max) (ud_bcm s pp t ltws)
            (fun s0 s1 hh => ud_bcm_Upp s pp t ltws s0 s1 hh)).
  cbv beta.
  rewrite lud_digitS_E code_link_bind.
  rewrite -[l in sample_seq dN l](size_rrdigS pp t md (size ltws)).
  apply rpre_hypothesis_rule => s0 s1 hbcm.
  move: (hbcm) => [hinv [hlpp [hrv [hsz' [hltw hfr']]]]].
  have hutwok := ud_inv_utwok s s0 s1 hinv.
  have hRC : RUCrel pp (get_heap s0 Ltg) (get_heap s1 rud_tgts_loc).
    { case/ud_invE: hinv => _ hRU; move: hRU; rewrite hlpp => -[_ _ _ _ [_ _ _ hm]].
      exact: hm. }
  rewrite /rr_F.
  eapply rpre_weaken_rule; last first.
    { move=> s2 s3 /= [-> ->].
      have hblk := ud_inv_udpin s s0 s1 hinv hrv; rewrite hlpp hltw in hblk.
      exact: hblk. }
  eapply (r_ud_chains_blk_ideal pp (lcoord t) s 0 (rrdigS pp t md (size ltws))
    (get_heap s0 Lsl) ltws (get_heap s0 Ltg) (get_heap s1 rud_tgts_loc) (get_heap s1 Utw)
    (fun rm => tgts ← get Ltg ;;
       #put Ltg := setm tgts (size ltws) (t, (rm, md)) ;;
       #put Ltw := rcons ltws t ;;
       ret (rrpkS pp t md (size ltws) rm))).
    { exact: l2_lcoord_bounded. }
    { by rewrite add0n size_rrdigS. }
    { exact: wf_rrdigS. }
    { apply: (@leq_trans ((size ltws).+1 * l)).
      { rewrite mulSn (addnC l); apply: leq_add.
        { by move: hutwok; rewrite hltw => -[hh _]. }
        { have hc := count_size [pred d | (s.+2 <= d)%N]
              (rrdigS pp t md (size ltws)).
          by move: hc; rewrite size_rrdigS. } }
      { rewrite leq_mul2r; apply/orP; right; exact: hsz'. } }
    { move=> j _ hj hs; move: hutwok; rewrite hltw => -[_ hsub].
      exact: (utw_fresh s ltws (get_heap s1 Utw) t j hj hs hsub hfr'). }
    { move=> us.
      rewrite (lud_copt_E pp (lcoord t) md).
      rewrite code_link_opr.
      eapply (r_ud_tail false s pp t md ltws _ _ (get_heap s0 Lsl) (get_heap s0 Ltg)
        (get_heap s1 rud_tgts_loc)
        (get_heap s1 Utw ++ qtws (lcoord t) s 0 (rrdigS pp t md (size ltws)))).
        { exact: hsz'. }
        { exact: hfr'. }
        { exact: hRC. }
        { apply: utw_ok_step; [exact: size_rrdigS | by move: hutwok; rewrite hltw]. }
        { rewrite (ud_wendsE pp t (rrdigS pp t md (size ltws)) _
                    (size_rrdigS pp t md (size ltws))).
          by rewrite /rrpkS. } }
- (* LGETPP *)
  rewrite /mkm_getpp; setoid_rewrite bind_assoc; eapply r_ud_pp2 => pp.
  rewrite ud_bind_put_ret.
  apply r_put_lhs; apply r_put_rhs; apply r_put_rhs; apply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  move: hpre => [s1a [[s1b [[s1c [[s0' [[hinv hL] e0]] e1]] e2]] e3]].
  subst.
  rewrite /ud_invL /= in hinv hL.
  split=> //.
  exact: (ud_inv_reveal s pp s0' _ hinv hL).
- (* LCHECK *)
  case: arg => j mw.
  case: b; last first.
    { apply r_ret => s0 s1 hinv; split; [by [] | exact: hinv]. }
  rewrite /rr_winbody.
  eapply r_get_remember_lhs => lrev.
  rewrite code_link_getr.
  eapply r_get_remember_rhs => rrev.
  eapply (r_fact (rrev = lrev)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ud_invE: hinv => _ [_ hrrv _ _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrrv hr0. }
  move=> e; subst rrev.
  rewrite code_link_assertD.
  eapply r_assertD_same => erev.
  rewrite code_link_getr.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
    { eapply (r_fact (getm rtg j = None)).
        { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
          rewrite /rem_inv /= in hr2 hr3.
          case/ud_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
          move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
          { by move: (hm j); rewrite hr2 E /= -hr3 => ->. }
          { by case: hm => _ hre _; rewrite -hr3 hre emptymE. } }
      move=> hrtgj.
      rewrite hrtgj.
      apply r_ret => s0 s1 [[[[hinv _] _] _] _]; split; [by [] | exact: hinv]. }
  eapply r_get_remember_lhs => lpp'.
  eapply (r_fact (exists pp, lpp' = Some pp /\
            getm rtg j = Some (t0, ((sg, md0), lfind t0 pp md0)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr0 hr2 hr3 hr4.
      have hlrv : get_heap s0 Lrv = true by rewrite hr0 erev.
      case/ud_invE: hinv => _ hRU.
      move: hRU; case El: (get_heap s0 Lpp) => [pp|] hRU.
      { exists pp; split; first by rewrite -hr4.
        case: hRU => _ _ _ _ [_ _ _ hm].
        by move: (hm j); rewrite hr2 E /= -hr3. }
      { case: hRU => _ _ _ _ [_ _ _ hm].
        case: hm => _ _ habs; rewrite habs in hlrv; discriminate hlrv. } }
  move=> [pp [hlpp hrtgj]].
  rewrite hlpp hrtgj /=.
  eapply (r_get_rhs_known rud_pp_loc (Some pp)).
    { move=> s0 s1 [[[[[hinv hrev] _] _] _] hpp].
      rewrite /rem_inv /= in hrev hpp.
      case/ud_invE: hinv => _ hRU.
      case: hRU => _ _ _ hrpp _.
      by rewrite hrpp hrev erev /= hpp. }
  cbv beta iota.
  apply r_ret => s0 s1 hpre.
  split; first by [].
  by case: hpre => [[[[[hinv _] _] _] _] _].
- (* LSIGN *)
  move: arg => j.
  rewrite /rr_sign.
  eapply r_get_remember_lhs => slog.
  eapply r_get_remember_rhs => rslog.
  eapply (r_fact (rslog = slog)).
    { move=> s0 s1 [[hinv hr0] hr1].
      case/ud_invE: hinv => _ [_ _ hrsl _ _].
      rewrite /rem_inv /= in hr0 hr1.
      by rewrite -hr1 hrsl hr0. }
  move=> e; subst rslog.
  rewrite code_link_assertD.
  eapply r_assertD_same => _.
  rewrite code_link_getr.
  eapply r_get_remember_lhs => ltg.
  eapply r_get_remember_rhs => rtg.
  case E: (getm ltg j) => [[t0 [sg md0]]|]; last first.
    { eapply (r_fact (getm rtg j = None)).
        { move=> s0 s1 [[[[hinv hr0] hr1] hr2] hr3].
          rewrite /rem_inv /= in hr2 hr3.
          case/ud_invE: hinv => _ [_ _ _ _ [_ _ _ hm]].
          move: hm; case El: (get_heap s0 Lpp) => [pp|] hm.
          { by move: (hm j); rewrite hr2 E /= -hr3 => ->. }
          { by case: hm => _ hre _; rewrite -hr3 hre emptymE. } }
      move=> hrtgj; rewrite hrtgj.
      apply r_ret => s0 s1 [[[[hinv _] _] _] _]; split; [by [] | exact: hinv]. }
  eapply r_get_remember_lhs => lpp'.
  eapply (r_fact (exists pp, lpp' = Some pp /\
            getm rtg j = Some (t0, ((sg, md0), lfind t0 pp md0)))).
    { move=> s0 s1 [[[[[hinv hr0] hr1] hr2] hr3] hr4].
      rewrite /rem_inv /= in hr2 hr3 hr4.
      case/ud_invE: hinv => _ hRU.
      move: hRU; case El: (get_heap s0 Lpp) => [pp|] hRU.
      { exists pp; split; first by rewrite -hr4.
        case: hRU => _ _ _ _ [_ _ _ hm].
        by move: (hm j); rewrite hr2 E /= -hr3. }
      { case: hRU => _ _ _ _ [_ _ _ hm].
        case: hm => he1 _ _; move: E; rewrite -hr2 he1 emptymE => Hd; discriminate Hd. } }
  move=> [pp [hlpp hrtgj]].
  rewrite hlpp hrtgj /=.
  case E2: (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0)
    => [c|].
    { apply r_put_lhs; apply r_put_rhs.
      apply r_ret => s0 s1 [s1' [[s0' [hpre e0]] e1]]; subst s0 s1.
      move: hpre => [[[[[hinv _] _] _] _] _].
      split=> //.
      exact: (ud_inv_setsl s (rcons slog j) s0' s1' hinv). }
  apply r_ret => s0 s1 [[[[[hinv _] _] _] _] _]; split; [by [] | exact: hinv].
- (* LCOLLQ *)
  case: arg => t x.
  have HE : forall (xx : tc_M CUD_leaf) (kk : tc_N CUD_leaf -> raw_code (N ∐ 'nat)),
    bind (resolve (SMU false) lud_cqo (t, xx)) kk
    = (ppo ← get Upp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Upp := Some pp ;; ret pp
            end ;;
       kk (tc_eval CUD_leaf pp t xx)).
    { move=> xx kk. rewrite (resolve_ud_cq false t xx) bind_getr.
      setoid_rewrite bind_assoc. by []. }
  rewrite /mkm_collq.
  case: x => [xy|dc].
    { rewrite code_link_opr HE.
      eapply r_ud_pp2 => pp.
      apply r_ret => s0 s1 [hinv hL].
      split; last exact: hinv.
      by rewrite /tc_eval /CUD_leaf. }
  rewrite code_link_opr HE.
  eapply r_ud_pp2 => pp.
  apply r_ret => s0 s1 [hinv hL].
  split; last exact: hinv.
  by rewrite /tc_eval /CUD_leaf.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The telescope (both legs by [b]; mirror UDHop.UD_telescope). *)

Lemma ud_telescope (hw : (0 < w)%N) (b : bool) (B : nom_package)
    (VB : ValidPackage (loc B) IKM A_export B) :
  (Adv (MIWkm b) (Hlend b) B
     <= \sum_(0 <= s < w.-2)
          AdvOf (SMUD_game TF CUD_leaf (n_max * l)) (B ∘ R_ud_leaf b s))%R.
Proof.
have hperf0 : perfect IKM (MIWkm b) ((R_ud_leaf b 0 ∘ SMU true)%sep).
{ exact: perfect_trans (Hl0_MIW hw b) (Hl_real_perfect hw b 0). }
have hperfw : perfect IKM (Hlend b) ((R_ud_leaf b w.-2 ∘ SMU true)%sep).
{ exact: perfect_trans (Hl_endw hw b) (Hl_real_perfect hw b w.-2). }
have hadj : forall s : nat, (s < w.-2)%N ->
    perfect IKM ((R_ud_leaf b s ∘ SMU false)%sep)
               ((R_ud_leaf b s.+1 ∘ SMU true)%sep).
{ move=> s _.
  exact: perfect_trans (perfect_sym (Hl_ideal_perfect hw b s))
           (Hl_real_perfect hw b s.+1). }
have h := Adv_hybrid_dep (n := w.-2)
  (Multi := fun b' => if b' then as_nom (MIWkm b) else as_nom (Hlend b))
  (Game := fun s b' => (R_ud_leaf b s ∘ SMU b')%sep)
  (A := B) hperf0 hperfw hadj.
have -> : (\sum_(0 <= s < w.-2)
    AdvOf (SMUD_game TF CUD_leaf (n_max * l)) (B ∘ R_ud_leaf b s)
  = \sum_(0 <= s < w.-2)
      AdvOf (fun b' : bool => (R_ud_leaf b s ∘ SMU b')%sep) B)%R.
{ by apply: eq_big_nat => s _; rewrite Adv_reduction. }
exact: h.
Qed.

(** [sub_ud_up]: the b=true leg ([MIW_kmS true] -> [G1l]).  [0 < w] is
    the non-degeneracy side-condition of the re-rooting endpoints
    ([hl_endw_commit]); it is supplied by the master (WOTS+C needs
    [w >= 2]). *)
Lemma sub_ud_up (hw : (0 < w)%N) (B : nom_package)
    (VB : ValidPackage (loc B) IKM A_export B) :
  (Adv (MIWkm true) G1lg B
     <= \sum_(0 <= s < w.-2)
          AdvOf (SMUD_game TF CUD_leaf (n_max * l)) (B ∘ R_ud_leaf true s))%R.
Proof. exact: (ud_telescope hw true B VB). Qed.

(** [sub_ud_down]: the b=false leg ([G1l'] -> [MIW_kmS false]); [Adv_sym]
    flips the endpoints to the [ud_telescope]'s orientation. *)
Lemma sub_ud_down (hw : (0 < w)%N) (B : nom_package)
    (VB : ValidPackage (loc B) IKM A_export B) :
  (Adv G1lg' (MIWkm false) B
     <= \sum_(0 <= s < w.-2)
          AdvOf (SMUD_game TF CUD_leaf (n_max * l)) (B ∘ R_ud_leaf false s))%R.
Proof. rewrite Adv_sym. exact: (ud_telescope hw false B VB). Qed.

End leaf2_ud.
