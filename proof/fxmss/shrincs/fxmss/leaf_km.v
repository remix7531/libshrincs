(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.leaf_km

    Concrete digest-at-commit leaf game [MIW_km], its re-targeted layer-(i)
    reduction [R_leaf_km], and the WLOG-strengthened endpoint [MIW_kmS] with
    the hop [Leaf_to_MIW_kmS]: the digest-at-COMMIT counterpart of the
    layer-(i) hop in [fxmss.leaf_reduction]. The perfect simulations
    [R_leaf_kmS_real] and [R_leaf_kmS_ideal] yield the premise-free
    [Leaf_to_MIW_kmS] bound. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From Sec.lib Require Import prelude math.bin_tree math.merkle math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme games.thf games.smtcr toolkit.sample_seq.
From Sec.lib Require Import toolkit.relational_rules chain.core wots.games wots.tcr_hop.
From Model Require Import fin.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop
  fxmss.leaf_reduction.
From mathcomp Require Import all_boot all_order.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section leaf_km.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same data-only section context as [fxmss.leaf_reduction], plus a default digest
    [d0] for the never-signed leaves' (signing-budget-exhausted) commit. *)
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
(** Shorthands (LeafReduction's). *)
Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation posok := (shrincs_fxmss_pos_ok h_sf).
Local Notation subposok := (shrincs_fxmss_sub_pos_ok h_sf).
Local Notation panchor p :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (posid p))).

(** The pk-compression (coordinate-level) tweak of [t]: collapses every
    address sharing the leaf coordinate [lcoord t = adrs_keypair (decode t)]
    onto the same [shrincs_fxmss_adr_pk] tweak.  This is the multi-target freshness the
    layer-(ii) SM-* reductions match against ([gtw_of t \notin map gtw_of tws]).
    On a pk-anchor tweak [gtw_of] is the IDENTITY ([gtw_AdrPk]), so for the
    real protocol (which commits only distinct leaf pk-anchors) coordinate
    freshness coincides with full-tweak freshness. *)
Local Notation gtw_of t :=
  (@encode_adrs l w
     (@shrincs_fxmss_wots_pk_adrs l w (@adrs_keypair l w (decode_tweak t)))).

Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation FXST := (shrincs_fxmss_game_state PP N).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).

Local Notation Lst := (shrincs_fxmss_st_loc PP N).
Local Notation Llog := (shrincs_fxmss_log_loc M).
Local Notation Lrom := (shrincs_fxmss_rom_loc PP N D M R).
Local Notation Lrt := (shrincs_fxmss_rt_loc M R).
Local Notation Lsd := (shrincs_fxmss_sd_loc D).
Local Notation fillc := (fill_code D dD).
Local Notation skeys := (@sample_keys l N dN).

Local Notation G5 b :=
  (G5f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).
Local Notation G6 b :=
  (G6f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).

(** The concrete leaf evals (LeafReduction's). *)
Local Notation lpk := (leaf_pk_c PP N F Tl).
Local Notation lrc := (leaf_rec_c PP N D F Tl Hgrind).
Local Notation lsg := (leaf_sign_c PP N D F Hgrind S_wn c_max).

(** M5 lift (adversary-chosen-leaf-id SIGN): the leaf-id validation +
    slot selector, EXPORTED from fxmss.games; keep them folded under
    [simpl] so the SIGN-bullet [case:] scrutinees match verbatim. *)
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).
Arguments leaf_okP : simpl never.
Arguments lidx : simpl never.

(** M5 lift, used↔slog bijection support (mirror of LeafReduction's).
    A valid, fresh id's slot [flidx] is absent from the [flidx]-image of
    the used-set (injectivity of [flidx] on valid ids). *)
Lemma flidx_notin_image (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  flok sp zi -> zi \notin domm us ->
  (forall zi', zi' \in domm us -> flok sp zi') ->
  flidx sp zi \notin [seq flidx sp zi' | zi' <- domm us].
Proof.
move=> hzi hfresh hval; apply/negP => /mapP [zi' hzi' heq].
have hv' := hval zi' hzi'.
have hzz := leafid_index_inj h_sf sp zi zi' hzi hv' heq.
by move: hfresh; rewrite hzz => /negP hn; exact: (hn hzi').
Qed.

(** The [flidx]-image is monotone in the used-set. *)
Lemma image_subset_setm (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  {subset [seq flidx sp zi' | zi' <- domm us]
       <= [seq flidx sp zi' | zi' <- domm (setm us zi Datatypes.tt)]}.
Proof.
move=> x /mapP [zi' hzi' ->]; apply/mapP; exists zi'; last by [].
by rewrite domm_set in_fsetU1 hzi' orbT.
Qed.

(** The fresh id's slot is in the grown image. *)
Lemma flidx_in_image_setm (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  flidx sp zi \in [seq flidx sp zi' | zi' <- domm (setm us zi Datatypes.tt)].
Proof. by apply/mapP; exists zi; rewrite // domm_set in_fsetU1 eqxx. Qed.

(** All ids in the grown used-set are valid, given the fresh id is. *)
Lemma used_valid_setm (sp : seq bool)
    (us : chMap ('nat × 'nat) 'unit) (zi : nat * nat) :
  flok sp zi -> (forall zi', zi' \in domm us -> flok sp zi') ->
  forall zi', zi' \in domm (setm us zi Datatypes.tt) -> flok sp zi'.
Proof.
move=> hzi hval zi'; rewrite domm_set in_fsetU1.
by case/orP=> [/eqP -> // | ]; exact: hval.
Qed.

(* ================================================================== *)
(** ** The corrected digest-AT-COMMIT interface (multi-instance lift of
    shrincs_fxmss_wots_scheme's valid-commit known-message game G0w). *)

Definition I_MIW_km :=
  [interface
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } ;
    [ LGETPP ] : { 'unit ~> PP } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) }
  ].

(** The km tgts map stores (tweak, key, committed-digest). *)
Definition mkm_tgts_loc :=
  mkloc 470 (emptym : {fmap nat -> (adrs_sf_ch × (('list N) × D))}).

Local Notation Lpp  := (miw_pp_loc PP).
Local Notation Ltw  := (@miw_tws_loc w l).
Local Notation Lrv  := miw_rev_loc.
Local Notation Lsl  := miw_slog_loc.

Local Notation MKMLocs :=
  [fmap Lpp ; mkm_tgts_loc ; Ltw ; Lrv ; Lsl ].

(** Reuse decode helpers via the same lcoll shape as LeafReduction's. *)
Local Notation lcoll pp t x :=
  (match x with
   | inl xy => (inl (Htree pp (decode_tweak t) xy) : (N ∐ 'nat))
   | inr dc => (inr (Hgrind pp (decode_tweak t) dc : 'nat) : (N ∐ 'nat))
   end).

Definition mkm_commit (t : adrs_sf_ch) (md : D) : raw_code N :=
  (revealed ← get Lrv ;;
   #assert ~~ revealed ;;
   tws ← get Ltw ;;
   #assert (size tws < n_max)%N ;;
   #assert (gtw_of t \notin [seq gtw_of x | x <- tws]) ;;
   xs ← sample_seq dN l ;;
   tgts ← get mkm_tgts_loc ;;
   #put mkm_tgts_loc := setm tgts (size tws) (t, (xs, md)) ;;
   #put Ltw := rcons tws t ;;
   ppo ← get Lpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
        end ;;
   ret (lpk pp t xs)).

Definition mkm_getpp : raw_code PP :=
  (ppo ← get Lpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
        end ;;
   #put Lrv := true ;;
   ret pp).

Definition mkm_win (j : nat) (mw : D × (('list N) × 'nat)) : raw_code 'bool :=
  (revealed ← get Lrv ;;
   #assert revealed ;;
   tgts ← get mkm_tgts_loc ;;
   match getm tgts j with
   | Some (t0, (m0, md0)) =>
       slog ← get Lsl ;;
       ppo ← get Lpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
            end ;;
       ret ((lrc pp t0 mw.1 mw.2 == lpk pp t0 m0)
            && ((j \notin slog) || (mw.1 != md0)))
   | None => ret false
   end).

Definition mkm_sign (j : nat) : raw_code ('option (('list N) × 'nat)) :=
  (slog ← get Lsl ;;
   #assert (j \notin slog) ;;
   tgts ← get mkm_tgts_loc ;;
   match getm tgts j with
   | Some (t0, (xs, md)) =>
       ppo ← get Lpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
            end ;;
       match lsg pp t0 xs md with
       | Some ws => #put Lsl := rcons slog j ;; ret (Some ws)
       | None => ret None
       end
   | None => ret None
   end).

Definition mkm_collq (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) :
    raw_code (N ∐ 'nat) :=
  (ppo ← get Lpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
        end ;;
   ret (lcoll pp t x)).

(** Validity of each oracle body over MKMLocs. *)
#[local] Instance mkm_commit_valid (I : Interface) (t : adrs_sf_ch) (md : D) :
  ValidCode MKMLocs I (mkm_commit t md).
Proof.
rewrite /mkm_commit.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tws.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by apply sample_seq_valid. move=> xs.
eapply valid_getr; first by fmap_solve. move=> tgts.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Instance mkm_getpp_valid (I : Interface) :
  ValidCode MKMLocs I mkm_getpp.
Proof.
rewrite /mkm_getpp.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[local] Instance mkm_win_valid (I : Interface) (j : nat)
    (mw : D × (('list N) × 'nat)) :
  ValidCode MKMLocs I (mkm_win j mw).
Proof.
rewrite /mkm_win.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 [m0 md0]]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> slog.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Instance mkm_sign_valid (I : Interface) (j : nat) :
  ValidCode MKMLocs I (mkm_sign j).
Proof.
rewrite /mkm_sign.
eapply valid_getr; first by fmap_solve. move=> slog.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 [xs md]]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; case: (lsg pp t0 xs md) => [ws|]; last by apply valid_ret.
eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[local] Instance mkm_collq_valid (I : Interface) (t : adrs_sf_ch)
    (x : (N × N) ∐ (D × 'nat)) :
  ValidCode MKMLocs I (mkm_collq t x).
Proof.
rewrite /mkm_collq.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Arguments mkm_commit : simpl never.
#[local] Arguments mkm_sign : simpl never.

Definition MIW_km (b : bool) : game I_MIW_km.
Proof.
notypeclasses refine [package MKMLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) { mkm_commit t md } ;
    [ LGETPP ] : { 'unit ~> PP } (_) { mkm_getpp } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      if b then mkm_win j mw else ret false } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) { mkm_sign j } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      mkm_collq t x }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { eapply valid_package_cons.
        { apply: valid_empty_package. }
        { intros [t x]; exact: mkm_collq_valid. } }
      { intro j; exact: mkm_sign_valid. } }
    { intros [j mw]; case: ifP => _; [exact: mkm_win_valid|apply valid_ret]. } }
  { intro u; exact: mkm_getpp_valid. } }
{ intros [t md]; exact: mkm_commit_valid. }
Defined.

(* ================================================================== *)
(** ** The re-targeted reduction [R_leaf_km] : package I_MIW_km IG.
    Differs from the shared [R_leaf''] in exactly: (1) the tree build feeds
    the presampled digest [sd[index]] to LCOMMIT; (2) GEN samples digests
    (fillc) BEFORE the tree build (so the digest is available at commit);
    (3) SIGN routes the WOTS sig via the digest-less LSIGN (the digest is
    already committed).  FORGE/HASH are the shared bodies (LCHECK/LCOLLQ
    unchanged), re-typed over I_MIW_km. *)

Local Notation Lpks := (rl_pks_loc N).
Local Notation tnode := (tnode_tw h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation gadrs zi := (shrincs_fxmss_wots_grind_adrs zi).
Local Notation fanchoridx := (fanchor_idx h_sf).
Local Notation fxvermd := (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation keepA := (keepAnchor N).
Local Notation gprp := (@grind_prp w l S_wn).

Local Notation RLLocs_km :=
  [fmap Lst ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ; shrincs_fxmss_hcnt_loc ; Lrt ;
        shrincs_fxmss_fcnt_loc ; Lsd ; rl_pks_loc N ].

Definition lf_cmo_km : opsig := (LCOMMIT, (adrs_sf_ch × D, N)).
Definition lf_sgo_km : opsig := (LSIGN, ('nat, 'option (('list N) × 'nat))).
Definition lf_cqo_km : opsig :=
  (LCOLLQ, (adrs_sf_ch × ((N × N) ∐ (D × 'nat)), (N ∐ 'nat))).
Definition lf_gpo_km : opsig := (LGETPP, ('unit, PP)).
Definition lf_cko_km : opsig :=
  (LCHECK, ('nat × (D × (('list N) × 'nat)), 'bool)).

(** The digest-passing tree build. *)
Fixpoint lf_tree_km (sp : seq bool) (sd : chMap 'nat D)
    (pos : seq bool) (t : bt unit) : raw_code N :=
  match t with
  | BLeaf _ =>
      opr lf_cmo_km
        (panchor pos, odflt d0 (getm sd (index pos (leaf_paths (tshape sp)))))
        (λ pk, pkm ← get Lpks ;;
               #put Lpks := setm pkm pos pk ;;
               ret pk)
  | BNode tl tr =>
      lv ← lf_tree_km sp sd (rcons pos false) tl ;;
      rv ← lf_tree_km sp sd (rcons pos true) tr ;;
      opr lf_cqo_km (tnode pos, inl (lv, rv))
        (λ y, ret (if y is inl z then z else n0))
  end.

#[local] Instance lf_tree_km_valid sp sd pos t :
  ValidCode RLLocs_km I_MIW_km (lf_tree_km sp sd pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- eapply valid_opr; first by rewrite /lf_cmo_km; fmap_solve.
  move=> pk; eapply valid_getr; first by fmap_solve. move=> pkm.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
- eapply valid_bind; first exact: IHl.
  move=> lv; eapply valid_bind; first exact: IHr.
  move=> rv; eapply valid_opr; first by rewrite /lf_cqo_km; fmap_solve.
  move=> y; apply valid_ret.
Qed.

(** km grind helpers (use lf_cqo_km; bodies = shared lf_grind''/etc.). *)
Fixpoint lf_grind_km (zi : nat * nat) (d : D) (cs : seq nat) :
    raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr lf_cqo_km (encode_adrs (gadrs zi), inr (d, c))
        (λ r, hs ← lf_grind_km zi d cs' ;;
              ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance lf_grind_km_valid zi d cs :
  ValidCode RLLocs_km I_MIW_km (lf_grind_km zi d cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by rewrite /lf_cqo_km; fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|]. move=> hs; apply valid_ret.
Qed.

Definition lf_slot_grind_km (sp : seq bool) (sd : chMap 'nat D) (j : nat) :
    raw_code 'bool :=
  match getm sd j with
  | Some d =>
      hs ← lf_grind_km (posid (spath sp j)) d (iota 0 c_max) ;;
      ret (has gprp hs)
  | None => ret true
  end.

#[local] Instance lf_slot_grind_km_valid sp sd j :
  ValidCode RLLocs_km I_MIW_km (lf_slot_grind_km sp sd j).
Proof.
rewrite /lf_slot_grind_km; case: (getm sd j) => [d|]; last by apply valid_ret.
eapply valid_bind; first exact: lf_grind_km_valid. move=> hs; apply valid_ret.
Qed.

Fixpoint lf_gcheck_km (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) :
    raw_code 'bool :=
  match js with
  | [::] => ret true
  | j :: js' =>
      bb ← lf_slot_grind_km sp sd j ;;
      bs ← lf_gcheck_km sp sd js' ;;
      ret (bb && bs)
  end.

#[local] Instance lf_gcheck_km_valid sp sd js :
  ValidCode RLLocs_km I_MIW_km (lf_gcheck_km sp sd js).
Proof.
elim: js => [|j js IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: lf_slot_grind_km_valid.
  move=> bb; eapply valid_bind; first exact: IH.
  move=> bs; apply valid_ret.
Qed.

Definition gen_redL_km (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   _ ← opr lf_cqo_km (encode_adrs (gadrs (0, 0)), inl (n0, n0)) (λ r, ret r) ;;
   _ ← dN ;;
   _ ← dR ;;
   sd ← fillc (iota 0 n_max) emptym ;;
   root ← lf_tree_km sp sd [::] (tshape sp) ;;
   gok ← lf_gcheck_km sp sd (iota 0 (size (leaf_paths (tshape sp)))) ;;
   #assert gok ;;
   pp ← opr lf_gpo_km Datatypes.tt (λ p, ret p) ;;
   #put Lst := Some ((pp, root), (sp, @dummy_xss N)) ;;
   #put Lsd := sd ;;
   ret (pp, root)).

Definition sign_redL_km (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   pkm ← get Lpks ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     r ← dR ;;
     md ← (match getm sd (flidx st.2.1 mz.2) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
     #put Lrt := setm tb (mz.2, mz.1) r ;;
     #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
     wso ← opr lf_sgo_km
             (index (spath st.2.1 (flidx st.2.1 mz.2)) (leaf_paths (tshape st.2.1)))
             (λ wo, ret wo) ;;
     match wso with
     | Some ws =>
         #put Llog := rcons lg mz.1 ;;
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret (Some ((posid (spath st.2.1 (flidx st.2.1 mz.2)), r),
                    (ws, leaf_ap PP N Htree h_sf n0 st.1.1 st.2.1 pkm
                           (flidx st.2.1 mz.2))))
     | None =>
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

Definition forge_redL_km (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get shrincs_fxmss_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   pkm ← get Lpks ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put shrincs_fxmss_fcnt_loc := fc.+1 ;;
   if b then
     let P := (fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
               && (m \notin lg))
              && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 md in
     match shrincs_fxmss_forgery_case_pks PP N D F Tl Hgrind Htree h_sf n0
             st.1.1 st.2.1 pkm sg.1.1 md sg.2.1 sg.2.2 with
     | merkle.FAnchor =>
         ans ← opr lf_cko_km (fanchoridx st.2.1 sg.1.1, (md, sg.2.1)) (λ a, ret a) ;;
         ret (P && ans)
     | fc' => ret (P && keepA fc')
     end
   else ret false).

#[local] Instance gen_redL_km_valid (sp : 'list 'bool) :
  ValidCode RLLocs_km I_MIW_km (gen_redL_km sp).
Proof.
rewrite /gen_redL_km.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind.
  eapply valid_opr; first by rewrite /lf_cqo_km; fmap_solve. move=> r; apply valid_ret.
move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply fill_code_valid. move=> sd.
eapply valid_bind; first exact: lf_tree_km_valid. move=> root.
eapply valid_bind; first exact: lf_gcheck_km_valid. move=> gok.
eapply valid_assertD => _.
eapply valid_bind.
  eapply valid_opr; first by rewrite /lf_gpo_km; fmap_solve. move=> p; apply valid_ret.
move=> pp.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[local] Instance sign_redL_km_valid (mz : M × ('nat × 'nat)) :
  ValidCode RLLocs_km I_MIW_km (sign_redL_km mz).
Proof.
rewrite /sign_redL_km.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_getr; first by fmap_solve. move=> pkm.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> r.
eapply valid_bind.
  case: (getm sd _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_bind.
  eapply valid_opr; first by rewrite /lf_sgo_km; fmap_solve. move=> wo; apply valid_ret.
move=> wso.
case: wso => [ws|]; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[local] Instance hash_redL_km_valid (x : ROIN) :
  ValidCode RLLocs_km I_MIW_km (hash5_body PP N D M R dD q_h x).
Proof.
rewrite /hash5_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[local] Instance forge_redL_km_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode RLLocs_km I_MIW_km (forge_redL_km b m sg).
Proof.
rewrite /forge_redL_km.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_getr; first by fmap_solve. move=> pkm.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: b; last by apply valid_ret.
case: (shrincs_fxmss_forgery_case_pks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [q x y|q x a0|q a|].
- apply valid_ret.
- apply valid_ret.
- apply valid_ret.
- eapply valid_bind.
    eapply valid_opr; first by rewrite /lf_cko_km; fmap_solve. move=> a; apply valid_ret.
  move=> ans; apply valid_ret.
Qed.

#[local] Arguments gen_redL_km : simpl never.
#[local] Arguments sign_redL_km : simpl never.
#[local] Arguments forge_redL_km : simpl never.

Definition R_leaf_km (b : bool) : package I_MIW_km IG.
Proof.
notypeclasses refine [package RLLocs_km ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { gen_redL_km sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) { sign_redL_km mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { hash5_body PP N D M R dD q_h x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { forge_redL_km b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge_redL_km_valid. } }
    { intro x; exact: hash_redL_km_valid. } }
  { intro mz; exact: sign_redL_km_valid. } }
{ intro sp; exact: gen_redL_km_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Resolve equations for [MIW_km]'s oracles (the linking machinery the
    perfect's [simplify_eq_rel] needs). *)

Lemma resolve_lcm_km (b : bool) (t : adrs_sf_ch) (md : D) :
  resolve (MIW_km b) lf_cmo_km (t, md) = mkm_commit t md.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lsg_km (b : bool) (j : nat) :
  resolve (MIW_km b) lf_sgo_km j = mkm_sign j.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lcq_km (b : bool) (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) :
  resolve (MIW_km b) lf_cqo_km (t, x) = mkm_collq t x.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgp_km (b : bool) (u : unit) :
  resolve (MIW_km b) lf_gpo_km u = mkm_getpp.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lck_km_true (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_km true) lf_cko_km (j, mw) = mkm_win j mw.
Proof. by simplify_linking. Qed.

Lemma resolve_lck_km_false (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_km false) lf_cko_km (j, mw) = ret false.
Proof. by simplify_linking. Qed.

(* ================================================================== *)
(** ** Coordinate-level freshness backbone (F2).  [gtw_of] is the IDENTITY on
    pk-anchor tweaks, and the GEN commit list is all-panchor, so the refined
    LCOMMIT assert [gtw_of t \notin map gtw_of tws] coincides with [t \notin tws]
    on the committed leaves. *)

Lemma anchor_height_finK (z : fin (BinInt.Z.of_nat 256)) :
  anchor_height (BinInt.Z.to_nat (fin_val z)) = z.
Proof.
apply: fin_val_inj.
have [hz0 hz256] := fin_range z.
have hz : BinInt.Z.lt
    (BinInt.Z.of_nat (BinInt.Z.to_nat (fin_val z)))
    (BinInt.Z.of_nat 256).
  by rewrite Znat.Z2Nat.id.
rewrite /anchor_height (fin_of_nat_or_zeroE _ _ _ hz) fin_val_of_nat.
exact: Znat.Z2Nat.id hz0.
Qed.

Lemma anchor_index_finK
    (i : fin (BinInt.Z.pow (BinInt.Z.of_nat 2) (BinInt.Z.of_nat 64))) :
  anchor_index (BinInt.Z.to_nat (fin_val i)) = i.
Proof.
apply: fin_val_inj.
have [hi0 hi64] := fin_range i.
have hi : BinInt.Z.lt
    (BinInt.Z.of_nat (BinInt.Z.to_nat (fin_val i)))
    (BinInt.Z.pow (BinInt.Z.of_nat 2) (BinInt.Z.of_nat 64)).
  by rewrite Znat.Z2Nat.id.
rewrite /anchor_index (fin_of_nat_or_zeroE _ _ _ hi) fin_val_of_nat.
exact: Znat.Z2Nat.id hi0.
Qed.

Lemma gtw_AdrPk (zi : nat * nat) :
  gtw_of (@encode_adrs l w (@shrincs_fxmss_adr_pk l w zi)) =
  @encode_adrs l w (@shrincs_fxmss_adr_pk l w zi).
Proof.
rewrite decode_tweakK.
case: zi => z i.
rewrite /shrincs_fxmss_wots_pk_adrs /adrs_keypair /adrs_height /adrs_index /=.
by rewrite anchor_height_finK anchor_index_finK.
Qed.

Lemma map_gtw_leaf_tws_under pos t :
  [seq gtw_of x | x <- leaf_tws_under h_sf pos t] = leaf_tws_under h_sf pos t.
Proof.
rewrite /leaf_tws_under -map_comp.
by apply/eq_map => q /=; rewrite gtw_AdrPk.
Qed.

(** ** STEP 1: the digest-bearing GEN block [lblk_km] + the LCOMMIT-with-digest
    coupling [r_lcommit_sample_km] (analog of shared [lblk'']/[r_lcommit_sample'']).
    The km tgts carries [(tweak, (key, digest))]; the block additionally pins
    [shrincs_fxmss_scnt = 0] (the lockstep base, alongside the shared [shrincs_fxmss_q = 0]). *)

Definition IGN_km : Locations :=
  [fmap Lst ; Lpp ; mkm_tgts_loc ; Ltw ; Lrv ; rl_pks_loc N ; Lsl ].

Definition lblk_km (po : option PP) (rv : bool)
    (tw : seq adrs_sf_ch) (tg : {fmap nat -> (adrs_sf_ch × ('list N × D))})
    (pkm : {fmap (seq bool) -> N}) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGN_km (s0, s1),
      get_heap s1 Lpp = po,
      get_heap s1 Lrv = rv,
      get_heap s1 Ltw = tw &
      [/\ get_heap s1 mkm_tgts_loc = tg, get_heap s1 (rl_pks_loc N) = pkm,
          get_heap s0 shrincs_fxmss_used_loc = emptym, get_heap s0 shrincs_fxmss_scnt_loc = 0%N
        & (get_heap s1 Lsl = [::] /\ get_heap s0 Lrt = emptym)]].

Arguments lblk_km : simpl never.

Local Notation lblkQ_km po rv Q pkm :=
  (lblk_km po rv (unzip1 Q) (qmap_from 0 Q) pkm).

Lemma lblk_km_set_pp (pp : PP) rv tw tg pkm s0 s1 :
  lblk_km None rv tw tg pkm (s0, s1) ->
  lblk_km (Some pp) rv tw tg pkm (s0, set_heap s1 Lpp (Some pp)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7 [h8 h9]]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by split; [rewrite get_set_heap_neq | rewrite get_set_heap_neq
            | exact: h6 | exact: h7
            | split; [rewrite get_set_heap_neq | exact: h9]].
Qed.

Lemma lblk_km_qupd (pp : PP) (t : adrs_sf_ch) (e : 'list N × D) tw tg pkm s0 s1 :
  lblk_km (Some pp) false tw tg pkm (s0, s1) ->
  lblk_km (Some pp) false (rcons tw t) (setm tg (size tw) (t, e)) pkm
    (s0, set_heap (set_heap s1 mkm_tgts_loc (setm tg (size tw) (t, e)))
           Ltw (rcons tw t)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7 [h8 h9]]]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- split; [ by rewrite get_set_heap_neq // get_set_heap_eq
         | by rewrite !get_set_heap_neq | exact: h6 | exact: h7
         | (split; [by rewrite !get_set_heap_neq | exact: h9]) ].
Qed.

Lemma lblk_km_pks_upd (po : option PP) rv tw tg pkm (p : seq bool) (v : N) s0 s1 :
  lblk_km po rv tw tg pkm (s0, s1) ->
  lblk_km po rv tw tg (setm pkm p v)
    (s0, set_heap s1 (rl_pks_loc N) (setm pkm p v)).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7 [h8 h9]]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by split; [rewrite get_set_heap_neq | rewrite get_set_heap_eq
            | exact: h6 | exact: h7
            | split; [rewrite get_set_heap_neq | exact: h9]].
Qed.

Lemma lblk_km_set_rev (po : option PP) tw tg pkm s0 s1 :
  lblk_km po false tw tg pkm (s0, s1) ->
  lblk_km po true tw tg pkm (s0, set_heap s1 Lrv true).
Proof.
move=> [h0 h1 h2 h3 [h4 h5 h6 h7 [h8 h9]]]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by split; [rewrite get_set_heap_neq | rewrite get_set_heap_neq
            | exact: h6 | exact: h7
            | split; [rewrite get_set_heap_neq | exact: h9]].
Qed.

Lemma lblkQ_km_upd (pp : PP) (Q : seq (adrs_sf_ch * ('list N × D)))
    (t : adrs_sf_ch) (e : 'list N × D) pkm s0 s1 :
  lblkQ_km (Some pp) false Q pkm (s0, s1) ->
  lblkQ_km (Some pp) false (rcons Q (t, e)) pkm (s0,
     set_heap (set_heap s1 mkm_tgts_loc
                 (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, e)))
       Ltw (rcons (unzip1 Q) t)).
Proof.
move=> hpre.
have hsz : size (unzip1 Q) = size Q by rewrite /unzip1 size_map.
rewrite /unzip1 map_rcons -/(unzip1 Q) qmap_from_rcons add0n -hsz.
exact: (lblk_km_qupd pp t e (unzip1 Q) (qmap_from 0 Q) pkm s0 s1 hpre).
Qed.

Lemma r_lcommit_sample_km (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (md : D) (Q : seq (adrs_sf_ch * ('list N × D)))
    (pkm : {fmap (seq bool) -> N})
    (k0 : 'list N -> raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < n_max)%N ->
  gtw_of t \notin [seq gtw_of x | x <- unzip1 Q] ->
  (forall xs : 'list N, size xs = l ->
     ⊢ ⦃ λ '(s0, s1), lblkQ_km (Some pp) false (rcons Q (t, (xs, md))) pkm (s0, s1) ⦄
        k0 xs ≈ k1 (lpk pp t xs) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ_km (Some pp) false Q pkm (s0, s1) ⦄
     (xs ← sample_seq dN l ;; k0 xs)
     ≈ bind (resolve (MIW_km b) lf_cmo_km (t, md)) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh h.
rewrite (resolve_lcm_km b t md) /mkm_commit.
eapply (r_get_bind_rhs Lrv false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs Ltw (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
rewrite bind_assoc.
apply: (r_sample_seq_size_l N dN l) => xs hxs.
eapply (r_get_bind_rhs mkm_tgts_loc (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ [h' _ _ _ _]].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (lblkQ_km_upd pp Q t (xs, md) pkm s0 s1 hpre).
eapply (r_get_bind_rhs Lpp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: (h xs hxs).
Qed.

(* ================================================================== *)
(** ** STEP 2: the digest-bearing tree coupling [lf_tree_km_spec] (analog of
    shared [lf_tree''_spec]).  Reuses shared [tvalL]/[pkm_of] (pk-only,
    digest-independent); the new [lf_commitsL_km] carries the per-leaf
    committed digest [sd[index leaf]]. *)

Local Notation kmdg sp sd pos :=
  (odflt d0 (getm sd (index pos (leaf_paths (tshape sp))))).
Local Notation tvalLk := (tvalL PP N Htree h_sf lpk).
Local Notation pkmofk := (pkm_of PP N h_sf lpk).

Fixpoint lf_commitsL_km (sp : seq bool) (sd : chMap 'nat D) (pos : seq bool)
    (xss : seq (seq N)) (t : bt unit) : seq (adrs_sf_ch * ('list N × D)) :=
  match t with
  | BLeaf _ => [:: (panchor pos, (nth [::] xss 0, kmdg sp sd pos))]
  | BNode tl tr =>
      lf_commitsL_km sp sd (rcons pos false) (take (size (leaf_paths tl)) xss) tl
      ++ lf_commitsL_km sp sd (rcons pos true) (drop (size (leaf_paths tl)) xss) tr
  end.

(** Local [unzip1_cat] (name-resolution bypass: the in-scope [unzip1_cat] does
    not match the goal's mathcomp [unzip1]). *)
Lemma unzip1_cat_km (s t : seq (adrs_sf_ch * ('list N × D))) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
Proof. by rewrite /unzip1 map_cat. Qed.

Lemma unzip1_lf_commitsL_km sp sd pos xss t :
  unzip1 (lf_commitsL_km sp sd pos xss t) = leaf_tws_under h_sf pos t.
Proof.
elim: t pos xss => [[]|tl IHl tr IHr] pos xss.
- by rewrite /= /leaf_tws_under /= cats0.
- rewrite [lf_commitsL_km sp sd pos xss (BNode tl tr)]/=.
  by rewrite unzip1_cat_km IHl IHr leaf_tws_under_node.
Qed.

Lemma size_lf_commitsL_km sp sd pos xss t :
  size (lf_commitsL_km sp sd pos xss t) = size (leaf_paths t).
Proof.
elim: t pos xss => [[]|tl IHl tr IHr] pos xss //.
rewrite [lf_commitsL_km sp sd pos xss (BNode tl tr)]/=.
by rewrite size_cat IHl IHr [in RHS]/= [in RHS]size_cat !size_map.
Qed.

Lemma r_lcollq_known_km (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) rv tw tg pkm
    (c0 : raw_code B) (k1 : (N ∐ 'nat) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (lcoll pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (resolve (MIW_km b) lf_cqo_km (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lcq_km b t x) /mkm_collq.
eapply (r_get_bind_rhs Lpp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: h.
Qed.

Lemma lf_tree_km_spec (b : bool) {B : choiceType} (pp : PP)
    (sp : seq bool) (sd : chMap 'nat D) (post : postcond B B) :
  forall (pos : seq bool) (t : bt unit)
         (Q : seq (adrs_sf_ch * ('list N × D))) (pkm : {fmap (seq bool) -> N})
         (k0 : seq (seq N) -> raw_code B) (k1 : N -> raw_code B),
  uniq (leaf_tws_under h_sf pos t ++ unzip1 Q) ->
  (size Q + size (leaf_paths t) <= n_max)%N ->
  [seq gtw_of x | x <- unzip1 Q] = unzip1 Q ->
  (forall xss_t, size xss_t = size (leaf_paths t) ->
     (forall x, x \in xss_t -> size x = l) ->
     ⊢ ⦃ λ '(s0, s1),
           lblkQ_km (Some pp) false (Q ++ lf_commitsL_km sp sd pos xss_t t)
             (pkmofk pp pos xss_t t pkm) (s0, s1) ⦄
        k0 xss_t ≈ k1 (tvalLk pp pos xss_t t) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ_km (Some pp) false Q pkm (s0, s1) ⦄
     (xss_t ← skeys (size (leaf_paths t)) ;; k0 xss_t)
     ≈ bind (code_link (lf_tree_km sp sd pos t) (MIW_km b)) k1 ⦃ post ⦄.
Proof.
move=> pos t; move: pos.
elim: t => [[]|tl IHl tr IHr].
- (* leaf: one sampling LCOMMIT-with-digest, then record the pk *)
  move=> pos Q pkm k0 k1 huniq hbud hpanQ h.
  rewrite [lf_tree_km sp sd pos (BLeaf tt)]/= code_link_opr_bind.
  rewrite [skeys (size (leaf_paths (BLeaf tt)))]/= bind_assoc.
  apply: (r_lcommit_sample_km b pp (panchor pos) (kmdg sp sd pos) Q pkm
            (fun xs => k0 (xs :: [::]))
            (fun pk => pkm0 ← get Lpks ;;
                       #put Lpks := setm pkm0 pos pk ;; k1 pk)).
  + by move: hbud; rewrite /= addn1.
  + rewrite hpanQ gtw_AdrPk.
    by move: huniq; rewrite /leaf_tws_under /= cats0 => /andP[h1 _].
  + move=> xs hxs.
    eapply (r_get_rhs_known Lpks pkm).
      by move=> s0 s1 [_ _ _ _ [_ h' _ _ _]].
    eapply (r_put_rhs_weak Lpks (setm pkm pos (lpk pp (panchor pos) xs))
              (lblkQ_km (Some pp) false (rcons Q (panchor pos, (xs, kmdg sp sd pos))) pkm)
              (lblkQ_km (Some pp) false (rcons Q (panchor pos, (xs, kmdg sp sd pos)))
                 (setm pkm pos (lpk pp (panchor pos) xs)))).
      by move=> s0 s1 hpre;
         exact: (lblk_km_pks_upd (Some pp) false
                   (unzip1 (rcons Q (panchor pos, (xs, kmdg sp sd pos))))
                   (qmap_from 0 (rcons Q (panchor pos, (xs, kmdg sp sd pos)))) pkm pos
                   (lpk pp (panchor pos) xs) s0 s1 hpre).
    have E1 : lf_commitsL_km sp sd pos [:: xs] (BLeaf tt)
            = [:: (panchor pos, (xs, kmdg sp sd pos))] by [].
    have E2 : pkmofk pp pos [:: xs] (BLeaf tt) pkm
            = setm pkm pos (lpk pp (panchor pos) xs) by [].
    have E3 : tvalLk pp pos [:: xs] (BLeaf tt) = lpk pp (panchor pos) xs by [].
    have hs : size ([:: xs] : seq (seq N)) = size (leaf_paths (BLeaf tt)) by [].
    have hl : forall y, y \in ([:: xs] : seq (seq N)) -> size y = l.
      by move=> y; rewrite inE => /eqP ->.
    have hh := h [:: xs] hs hl.
    rewrite E1 E2 E3 cats1 in hh.
    exact: hh.
- exact: B.
- (* node: split the key draw, recurse left/right, hash the node *)
  move=> pos Q pkm k0 k1 huniq hbud hpanQ h.
  have Esz : size (leaf_paths (BNode tl tr))
             = (size (leaf_paths tl) + size (leaf_paths tr))%N.
    by rewrite /= size_cat !size_map.
  rewrite Esz sample_keys_cat !bind_assoc.
  rewrite code_link_bind bind_assoc.
  set Lt := @leaf_tws_under w l h_sf (rcons pos false) tl.
  set Rt := @leaf_tws_under w l h_sf (rcons pos true) tr.
  have hbud' : (size Q + size (leaf_paths tl) + size (leaf_paths tr) <= n_max)%N.
    by move: hbud; rewrite Esz addnA.
  move: huniq; rewrite leaf_tws_under_node -/Lt -/Rt -catA => huniq.
  eapply (IHl (rcons pos false) Q pkm).
  + apply: (subseq_uniq _ huniq).
    apply: cat_subseq; first exact: subseq_refl.
    exact: suffix_subseq.
  + apply: leq_trans hbud'; exact: leq_addr.
  + (* hpanQ for the left recursion: Q unchanged *)
    exact: hpanQ.
  + move=> a hsza hsla.
    rewrite bind_assoc code_link_bind bind_assoc.
    eapply (IHr (rcons pos true) (Q ++ lf_commitsL_km sp sd (rcons pos false) a tl)
              (pkmofk pp (rcons pos false) a tl pkm)).
    * rewrite unzip1_cat_km unzip1_lf_commitsL_km -/Lt -/Rt.
      have hperm : perm_eq (Rt ++ unzip1 Q ++ Lt) (Lt ++ Rt ++ unzip1 Q).
        by rewrite (catA Rt) perm_catC.
      rewrite (perm_uniq hperm); exact: huniq.
    * rewrite size_cat size_lf_commitsL_km.
      exact: hbud'.
    * (* hpanQ for the right recursion: Q ++ left-commits, all pk-anchors *)
      rewrite unzip1_cat_km unzip1_lf_commitsL_km map_cat hpanQ
              map_gtw_leaf_tws_under.
      by [].
    * move=> bb hszb hslb.
      rewrite code_link_opr_bind.
      eapply (r_lcollq_known_km b pp (tnode pos)
                (inl (tvalLk pp (rcons pos false) a tl,
                      tvalLk pp (rcons pos true) bb tr) : (N × N) ∐ (D × 'nat))).
      have hnh : forall x y, Htree pp (decode_tweak (tnode pos)) (x, y)
                             = nhash pp pos x y.
        by move=> x y; rewrite -(lcollq_node_E PP N D Hgrind Htree h_sf n0 pp pos x y).
      rewrite hnh.
      have hsz_ab : size (a ++ bb) = size (leaf_paths (BNode tl tr)).
        by rewrite size_cat hsza hszb Esz.
      have hall_ab : forall x, x \in a ++ bb -> size x = l.
        by move=> x; rewrite mem_cat => /orP[]; [exact: hsla|exact: hslb].
      have := h (a ++ bb) hsz_ab hall_ab.
      rewrite /lf_commitsL_km -/lf_commitsL_km /pkm_of -/pkm_of /tvalL -/tvalL.
      by rewrite -hsza take_size_cat // drop_size_cat // catA.
Unshelve. all: try exact: B.
Qed.

#[local] Arguments lf_tree_km : simpl never.

(* ================================================================== *)
(** ** STEP 3 (pure): [leafcommitq_km] + root bridge + SIGN lookup.  Mirrors
    shared [lf_commits]/[lf_commits_E]/[lf_commitsL_sub]/[lf_commitsL_root] +
    [getm_leafcommitq_at], with the digest [kmdg sp sd pos] carried verbatim. *)

Fixpoint lf_commits_km (sp : seq bool) (sd : chMap 'nat D) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : seq (adrs_sf_ch * ('list N × D)) :=
  match t with
  | BLeaf _ =>
      [:: (panchor pos, (nth [::] xss (index pos (leaf_paths (tshape sp))),
                         kmdg sp sd pos))]
  | BNode tl tr =>
      lf_commits_km sp sd xss (rcons pos false) tl
      ++ lf_commits_km sp sd xss (rcons pos true) tr
  end.

Lemma lf_commits_km_E sp sd xss pos t :
  lf_commits_km sp sd xss pos t
  = [seq (panchor (pos ++ q),
          (nth [::] xss (index (pos ++ q) (leaf_paths (tshape sp))),
           kmdg sp sd (pos ++ q))) | q <- leaf_paths t].
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos.
- by rewrite /lf_commits_km /= cats0.
- rewrite /= IHl IHr map_cat.
  congr (_ ++ _); rewrite -map_comp; apply/eq_map => q /=; by rewrite cat_rcons.
Qed.

Definition leafcommitq_km (sp : seq bool) (sd : chMap 'nat D)
    (xss : seq (seq N)) : seq (adrs_sf_ch * ('list N × D)) :=
  lf_commits_km sp sd xss [::] (tshape sp).

Lemma leafcommitq_km_E sp sd xss :
  leafcommitq_km sp sd xss
  = [seq (panchor q,
          (nth [::] xss (index q (leaf_paths (tshape sp))), kmdg sp sd q))
    | q <- leaf_paths (tshape sp)].
Proof.
rewrite /leafcommitq_km lf_commits_km_E; apply: eq_map => q.
by rewrite cat0s.
Qed.

Lemma getm_leafcommitq_km sp sd xss p :
  p \in leaf_paths (tshape sp) ->
  getm (qmap_from 0 (leafcommitq_km sp sd xss)) (index p (leaf_paths (tshape sp)))
  = Some (panchor p, (nth [::] xss (index p (leaf_paths (tshape sp))),
                      kmdg sp sd p)).
Proof.
move=> hp.
have := qmap_from_get 0 (leafcommitq_km sp sd xss)
          (index p (leaf_paths (tshape sp))).
rewrite add0n => ->.
rewrite leafcommitq_km_E qnth_map /qnth.
rewrite (drop_nth [::]); last by rewrite index_mem.
by rewrite nth_index.
Qed.

Lemma getm_leafcommitq_km_at sp sd xss q :
  (q < size (leaf_paths (tshape sp)))%N ->
  getm (qmap_from 0 (leafcommitq_km sp sd xss)) q
  = Some (panchor (spath sp q), (nth [::] xss q, odflt d0 (getm sd q))).
Proof.
move=> hq.
rewrite -{1}(index_sign_path h_sf sp q hq).
rewrite (getm_leafcommitq_km sp sd xss (spath sp q) (mem_nth [::] hq)).
by rewrite (index_sign_path h_sf sp q hq).
Qed.

Lemma lf_commitsL_km_sub sp sd xss pos t :
  lf_commitsL_km sp sd pos
    [seq nth [::] xss (index (pos ++ p) (leaf_paths (tshape sp))) | p <- leaf_paths t] t
  = lf_commits_km sp sd xss pos t.
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- by rewrite cats0.
- rewrite map_cat take_size_cat ?size_map // drop_size_cat ?size_map //.
  rewrite -!map_comp; congr (_ ++ _).
  + rewrite (eq_map (g := fun q => nth [::] xss
                (index (rcons pos false ++ q) (leaf_paths (tshape sp)))));
      last by move=> q /=; rewrite cat_rcons.
    exact: IHl.
  + rewrite (eq_map (g := fun q => nth [::] xss
                (index (rcons pos true ++ q) (leaf_paths (tshape sp)))));
      last by move=> q /=; rewrite cat_rcons.
    exact: IHr.
Qed.

Lemma lf_commitsL_km_root sp sd xss :
  size xss = size (leaf_paths (tshape sp)) ->
  lf_commitsL_km sp sd [::] xss (tshape sp) = leafcommitq_km sp sd xss.
Proof.
move=> hsz.
have huniq : uniq (leaf_paths (tshape sp)).
  have hu := @gen_uniq w l N h_sf Hh sp.
  by move: hu; rewrite cats0 /leaf_tws_under => /map_uniq.
rewrite /leafcommitq_km -(lf_commitsL_km_sub sp sd xss [::] (tshape sp)).
congr lf_commitsL_km.
rewrite (eq_map (g := fun p => nth [::] xss (index p (leaf_paths (tshape sp)))));
  last by move=> p; rewrite cat0s.
by rewrite (map_nth_index_self N (leaf_paths (tshape sp)) xss huniq hsz).
Qed.

(* ================================================================== *)
(** ** STEP 3b: the two-sided GEN/SIGN/FORGE invariant [lf_inv2_km].  = shared
    [lf_inv2]/[RLf2] with: digest-bearing [tg = qmap_from 0 (leafcommitq_km ..
    sdL ..)]; tracked [(lhs,shrincs_fxmss_scnt_loc)] + [(lhs,shrincs_fxmss_sd_loc)]; the lockstep
    [scL = qL \/ qL = size LP]; and carried [sd_grindable]. *)

Definition IGN2_km : Locations := IGN_km.

Definition RLf2_km (sto_L sto_R : option FXST) (po : option PP)
    (tg : {fmap nat -> (adrs_sf_ch × ('list N × D))}) (tw : seq adrs_sf_ch)
    (rv : bool) (pkm : {fmap (seq bool) -> N})
    (us : chMap ('nat × 'nat) 'unit) (scL : nat)
    (sdL : chMap 'nat D) (slog : seq nat) : Prop :=
  match sto_L with
  | None =>
      [/\ sto_R = None, po = None, tg = emptym, tw = [::]
        & [/\ rv = false, pkm = emptym, us = emptym, scL = 0 & slog = [::]]]
  | Some st =>
      [/\ sto_R = Some (st.1, (st.2.1, @dummy_xss N)),
          po = Some st.1.1, rv = true,
          tg = qmap_from 0 (leafcommitq_km st.2.1 sdL st.2.2)
        & [/\ tw = leaf_tws h_sf st.2.1,
              (forall p, p \in leaf_paths (tshape st.2.1) ->
                 getm pkm p = Some (anchor_val PP N F Tl h_sf
                                      st.1.1 st.2.1 st.2.2 p)),
              [/\ {subset slog <= [seq flidx st.2.1 zi | zi <- domm us]}
                & forall zi, zi \in domm us -> flok st.2.1 zi],
              st.1.2 = shrincs_fxmss_root_x PP N F Tl Htree h_sf st.1.1 st.2.1 st.2.2
            & [/\ (size (leaf_paths (tshape st.2.1)) <= n_max)%N,
                sd_grindable PP D Hgrind S_wn c_max h_sf
                    st.1.1 st.2.1 sdL
                & (forall j, (j < n_max)%N -> isSome (getm sdL j))]]]
  end.

(** The 9th-subtlety clause: tb-domain link to the message log (A) plus the
    signing budget (B).  Read off the LHS only; established at GEN, preserved at
    SIGN.  In the None (pre-GEN) state the log/table are empty, so clause (A)
    holds vacuously; in the Some state every signing-table key's message is
    logged and the leaf-signing counter is bounded by [q_s]. *)
Definition R_tblog (sto : option FXST)
    (tb : {fmap (('nat × 'nat) × M) -> R}) (lg : seq M) : Prop :=
  match sto with
  | None => tb = emptym /\ lg = [::]
  | Some _ =>
      forall (k : ('nat × 'nat) × M) (rr : R), getm tb k = Some rr -> k.2 \in lg
  end.

Definition lf_inv2_km : precond :=
  heap_ignore IGN2_km
  ⋊ rel_app [:: (lhs, shrincs_fxmss_st_loc PP N) ; (rhs, shrincs_fxmss_st_loc PP N) ;
                (rhs, Lpp) ; (rhs, mkm_tgts_loc) ; (rhs, Ltw) ;
                (rhs, Lrv) ; (rhs, rl_pks_loc N) ;
                (lhs, shrincs_fxmss_used_loc) ; (lhs, shrincs_fxmss_scnt_loc) ; (lhs, shrincs_fxmss_sd_loc D) ;
                (rhs, Lsl) ] RLf2_km
  ⋊ rel_app [:: (lhs, shrincs_fxmss_st_loc PP N) ; (lhs, Lrt) ; (lhs, Llog) ] R_tblog.

Arguments lf_inv2_km : simpl never.

Lemma lf_inv2_kmE s0 s1 :
  lf_inv2_km (s0, s1) ->
  heap_ignore IGN2_km (s0, s1) /\
  RLf2_km (get_heap s0 (shrincs_fxmss_st_loc PP N)) (get_heap s1 (shrincs_fxmss_st_loc PP N))
       (get_heap s1 Lpp) (get_heap s1 mkm_tgts_loc)
       (get_heap s1 Ltw) (get_heap s1 Lrv)
       (get_heap s1 (rl_pks_loc N)) (get_heap s0 shrincs_fxmss_used_loc)
       (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 (shrincs_fxmss_sd_loc D))
       (get_heap s1 Lsl).
Proof. by move=> [[h1 h2] _]; split. Qed.

Lemma lf_inv2_km_tblogE s0 s1 :
  lf_inv2_km (s0, s1) ->
  R_tblog (get_heap s0 (shrincs_fxmss_st_loc PP N)) (get_heap s0 Lrt)
          (get_heap s0 Llog).
Proof. by move=> [_ h3]. Qed.

Lemma lf_inv2_kmI s0 s1 :
  heap_ignore IGN2_km (s0, s1) ->
  RLf2_km (get_heap s0 (shrincs_fxmss_st_loc PP N)) (get_heap s1 (shrincs_fxmss_st_loc PP N))
       (get_heap s1 Lpp) (get_heap s1 mkm_tgts_loc)
       (get_heap s1 Ltw) (get_heap s1 Lrv)
       (get_heap s1 (rl_pks_loc N)) (get_heap s0 shrincs_fxmss_used_loc)
       (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 (shrincs_fxmss_sd_loc D))
       (get_heap s1 Lsl) ->
  R_tblog (get_heap s0 (shrincs_fxmss_st_loc PP N)) (get_heap s0 Lrt)
          (get_heap s0 Llog) ->
  lf_inv2_km (s0, s1).
Proof. by move=> h1 h2 h3; split; [split|]. Qed.

Lemma lfinv2_km_init s0 s1 :
  lf_inv2_km (s0, s1) ->
  get_heap s0 (shrincs_fxmss_st_loc PP N) = None ->
  lblk_km None false [::] emptym emptym (s0, s1).
Proof.
move=> hpre hst.
move/lf_inv2_kmE: (hpre) => [hign hR].
move/lf_inv2_km_tblogE: hpre => hT.
rewrite hst in hR hT.
case: hR => hsoR hpp htg htw [hrv hpkm hus hscL hslog].
case: hT => htb _.
split; [exact: hign | exact: hpp | exact: hrv | exact: htw |].
by split; [exact: htg | exact: hpkm | exact: hus | exact: hscL
          | (split; [exact: hslog | exact: htb])].
Qed.

(** SIGN/FORGE sync helpers over [lf_inv2_km] (synced get/put of a loc disjoint
    from all RLf2_km-tracked locs). *)
Lemma lf_inv2_km_get_pre (l0 : Location) :
  l0.1 \notin domm IGN2_km -> get_pre_cond l0 lf_inv2_km.
Proof. by move=> hl0 s0 s1 [[hign _] _]; exact: hign. Qed.

Ltac lf_get2_km_pre := apply: lf_inv2_km_get_pre; rewrite /IGN2_km /IGN_km; fmap_solve.

Ltac lf_getr_km :=
  first [ apply: lf_inv2_km_get_pre; rewrite /IGN2_km /IGN_km; fmap_solve
        | apply: get_pre_cond_conj; lf_getr_km ].

Lemma lf_inv2_km_set_fx (l0 : Location) (v : l0) s0 s1 :
  l0.1 != (shrincs_fxmss_st_loc PP N).1 ->
  l0.1 != Lpp.1 ->
  l0.1 != mkm_tgts_loc.1 ->
  l0.1 != Ltw.1 ->
  l0.1 != Lrv.1 ->
  l0.1 != (rl_pks_loc N).1 ->
  l0.1 != shrincs_fxmss_used_loc.1 ->
  l0.1 != shrincs_fxmss_scnt_loc.1 ->
  l0.1 != (shrincs_fxmss_sd_loc D).1 ->
  l0.1 != Lsl.1 ->
  l0.1 != Lrt.1 ->
  l0.1 != Llog.1 ->
  lf_inv2_km (s0, s1) ->
  lf_inv2_km (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hpre.
move/lf_inv2_kmE: (hpre) => [hign hR].
move/lf_inv2_km_tblogE: hpre => hT.
apply: lf_inv2_kmI.
- by apply: heap_ignore_set_both.
- rewrite !get_set_heap_neq //; by rewrite eq_sym.
- rewrite !get_set_heap_neq //; by rewrite eq_sym.
Qed.

Ltac lf_put2_km_tr :=
  let s0 := fresh "s0" in let s1 := fresh "s1" in let hp := fresh "hp" in
  rewrite /put_pre_cond; move=> s0 s1 hp;
  refine (lf_inv2_km_set_fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp); by [].

Ltac lf_put2_km_pre :=
  repeat (apply: put_pre_cond_conj; last (apply: put_pre_cond_rem; by []));
  lf_put2_km_tr.

(* ================================================================== *)
(** ** STEP 4 prereq: the independent-sample block SWAP (re-derived from
    SPX/WTW_TCRHop.v).  [skeys]/[fillc] are stateless schemes, so they
    commute; [r_swap_blocks] commutes them on the LHS (RHS arbitrary). *)

Lemma r_swap_scheme_scheme {A B C : choiceType}
    (c0 : raw_code A) (c1 : raw_code B) (r : A -> B -> raw_code C) :
  ValidCode emptym [interface] c0 ->
  ValidCode emptym [interface] c1 ->
  ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄
    x ← c0 ;; y ← c1 ;; r x y ≈ y ← c1 ;; x ← c0 ;; r x y ⦃ eq ⦄.
Proof.
move=> h0 h1.
elim: h0 r
  => [a r|o x' k ho hk IH r|ℓ k hℓ hk IH r|ℓ v' k hℓ hk IH r|op k hk IH r].
- exact: rreflexivity_rule.
- by destruct o; discriminate.
- by destruct ℓ; discriminate.
- by destruct ℓ; discriminate.
- eapply r_transR.
  + eapply (rswap_cmd_bind_eq (cmd_sample op) c1
              (λ v y, x ← k v ;; r x y)).
    eapply r_swap_cmd_scheme. exact h1.
  + simpl. eapply (rsame_head_cmd (cmd_sample op)) => a.
    exact: IH.
Qed.

Lemma r_swap_eager_lazy {A B C Dt : choiceType}
    (c0 : raw_code A) (c1 : raw_code B)
    (g : A -> B -> raw_code C) (K : A -> C -> raw_code Dt)
    (c1' : raw_code Dt) (pre : precond) (post : postcond Dt Dt) :
  ValidCode emptym [interface] c0 ->
  ValidCode emptym [interface] c1 ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     y ← c1 ;; x ← c0 ;; bind (g x y) (K x) ≈ c1' ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     x ← c0 ;; bind (bind c1 (g x)) (K x) ≈ c1' ⦃ post ⦄.
Proof.
move=> h0 h1 h.
eapply r_transL; last exact: h.
eapply r_transR.
- eapply (rsame_head (f₀ := λ x, y ← c1 ;; bind (g x y) (K x))
                     (f₁ := λ x, bind (bind c1 (g x)) (K x))) => x.
  rewrite bind_assoc.
  exact: rreflexivity_rule.
- exact: (r_swap_scheme_scheme c1 c0 (λ y x, bind (g x y) (K x)) h1 h0).
Qed.

Lemma r_swap_blocks {A B C : choiceType}
    (c0 : raw_code A) (c1 : raw_code B) (k : A -> B -> raw_code C)
    (c1' : raw_code C) (pre : precond) (post : postcond C C) :
  ValidCode emptym [interface] c0 ->
  ValidCode emptym [interface] c1 ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     y ← c1 ;; x ← c0 ;; k x y ≈ c1' ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     x ← c0 ;; y ← c1 ;; k x y ≈ c1' ⦃ post ⦄.
Proof.
move=> h0 h1 h.
have H := r_swap_eager_lazy c0 c1 (fun x y => ret y) (fun x y => k x y)
            c1' pre post h0 h1 h.
eapply r_transL; last exact: H.
eapply rsame_head => x.
rewrite bind_ret.
exact: rreflexivity_rule.
Qed.

(* ================================================================== *)
(** ** STEP 4 prereq: the km grind/gcheck relational specs (mirror shared
    [r_grind'']/[r_slot_grind'']/[r_gcheck'']_spec, over [lf_*_km]/[MIW_km]/
    [lblk_km]). *)

Lemma r_grind_km_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (zi : nat * nat) (d : D) (cs : seq nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : chList 'nat -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (gadrs zi) (d, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_grind_km zi d cs) (MIW_km b)) k1 ⦃ post ⦄.
Proof.
move=> zi d cs; elim: cs => [|c cs IH] rv tw tg pkm c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lcollq_known_km b).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite (lcollq_grind_E PP N D Hgrind Htree) /= in h *.
Qed.

Lemma r_slot_grind_km_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (j : nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (match getm sd j with
              | Some d => slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d
              | None => true
              end) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_slot_grind_km sp sd j) (MIW_km b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd j rv tw tg pkm c0 k1 h.
rewrite /lf_slot_grind_km.
case E: (getm sd j) => [d|]; rewrite E /= in h.
- rewrite code_link_bind bind_assoc.
  eapply (r_grind_km_spec b pp post (posid (spath sp j)) d (iota 0 c_max)).
  rewrite code_link_ret_bind has_grind_find_ctr.
  rewrite -/(slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d).
  exact: h.
- by rewrite code_link_ret_bind; exact: h.
Qed.

Lemma r_gcheck_km_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (all (fun j => match getm sd j with
                | Some d => slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d
                | None => true
                end) js) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_gcheck_km sp sd js) (MIW_km b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd js; elim: js => [|j js IH] rv tw tg pkm c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_slot_grind_km_spec b pp post sp sd j).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite code_link_ret_bind.
Qed.

(* ================================================================== *)
(** ** The re-targeted layer-(i) hop.  PROVABLE because G5f's signing digest
    [md = sd[sc]] is presampled-random (DigestHop done before G5f): the GEN
    coupling feeds the presampled [sd[index leaf]] to LCOMMIT (digest at
    commit), SIGN routes via the digest-less LSIGN, and the slot<->leaf
    reindex is sound by the lockstep [shrincs_fxmss_scnt = shrincs_fxmss_q] (maintained by the GEN
    grindability assert).  REUSES the shared re-bank machinery
    (lf_tree''_spec digest-independent, the GEN/SIGN/FORGE perfects). *)

(** fillc-totality coupling: couple two identical [fillc js m0] and hand the
    continuation the structural fact that every committed key is set.  Used at
    GEN to establish the [lf_inv2_km] sd-totality clause (so SIGN's None digest
    branch is dead for signed leaves). *)
Lemma r_fillc_dom {B : choiceType} (post : postcond B B) :
  forall (js : seq nat) (m0 : chMap 'nat D) (pre : precond)
         (kL kR : chMap 'nat D -> raw_code B),
  (forall sd, (forall j, j \in js -> isSome (getm sd j)) ->
              (forall k, isSome (getm m0 k) -> isSome (getm sd k)) ->
              ⊢ ⦃ pre ⦄ kL sd ≈ kR sd ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄ sd ← fillc js m0 ;; kL sd ≈ sd ← fillc js m0 ;; kR sd ⦃ post ⦄.
Proof.
elim => [|j js' IH] m0 pre kL kR h.
- simpl. apply: (h m0); by [].
- simpl. rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> y.
  apply: (IH (setm m0 j y) pre kL kR).
  move=> sd hjs' hsetm.
  apply: (h sd).
  + move=> jj; rewrite in_cons => /orP[/eqP ->|hin].
    * by apply: hsetm; rewrite setmE eqxx.
    * exact: hjs' jj hin.
  + move=> k hk; apply: hsetm; rewrite setmE.
    by case: (k == j); [ | exact: hk ].
Qed.

(** FORGE verdict bridge (port of shared r_leaf_forge_verdict''): the G5f
    [fverd (fun _ => true)] equals the [shrincs_fxmss_forgery_case_pks] classify-and-LCHECK verdict.
    The digest-bearing tgts is sdL-independent (mkm_win ignores it). *)
Lemma r_leaf_forge_verdict_km (st : FXST) (pkm : {fmap (seq bool) -> N})
    (lg : seq M) (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (dd : D) :
  (forall p, p \in leaf_paths (tshape st.2.1) ->
     getm pkm p = Some (anchor_val PP N F Tl h_sf st.1.1 st.2.1 st.2.2 p)) ->
  (forall (k : ('nat × 'nat) × M) (rr : R), getm tb k = Some rr -> k.2 \in lg) ->
  (forall jj, (jj < n_max)%N -> odflt d0 (getm sd jj) \in codomm sd) ->
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv2_km ⋊ rem_lhs Lst (Some st)
              ⋊ rem_rhs Lst (Some (st.1, (st.2.1, @dummy_xss N)))
              ⋊ rem_lhs (shrincs_fxmss_sd_loc D) sd
              ⋊ rem_rhs (rl_pks_loc N) pkm) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            (fun _ => true) st st.2.2 st.2.1 lg sd tb m sg dd)
     ≈ (match shrincs_fxmss_forgery_case_pks PP N D F Tl Hgrind Htree h_sf n0
               st.1.1 st.2.1 pkm sg.1.1 dd sg.2.1 sg.2.2 with
          | merkle.FAnchor =>
              v ← get Lrv ;;
              ans ← (#assert v ;;
                     tgts ← get mkm_tgts_loc ;;
                     match getm tgts (fanchoridx st.2.1 sg.1.1) with
                     | Some (t0, (m0, md0)) =>
                         slog ← get Lsl ;;
                         ppo ← get Lpp ;;
                         match ppo with
                         | Some pp =>
                             ret ((lrc pp t0 dd sg.2.1 == lpk pp t0 m0)
                                  && ((fanchoridx st.2.1 sg.1.1 \notin slog)
                                      || (dd != md0)))
                         | None => pp ← dPP ;; #put Lpp := Some pp ;;
                             ret ((lrc pp t0 dd sg.2.1 == lpk pp t0 m0)
                                  && ((fanchoridx st.2.1 sg.1.1 \notin slog)
                                      || (dd != md0)))
                         end
                     | None => ret false
                     end) ;;
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd) && ans)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv2_km (s0, s1) ⦄.
Proof.
move=> hpkm HtbA Hcod.
rewrite (shrincs_fxmss_forgery_case_pks_bridge PP N D F Tl Hgrind Htree h_sf n0
           st.1.1 st.2.1 st.2.2 pkm sg.1.1 dd sg.2.1 sg.2.2 hpkm).
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd).
rewrite /fverd -/P.
eapply (r_fact (st.1.2 = shrincs_fxmss_root_x PP N F Tl Htree h_sf st.1.1 st.2.1 st.2.2)).
  { move=> s0 s1 [[[[hinv hr] _] _] _].
    move/lf_inv2_kmE: hinv => [_ hRLf].
    rewrite /rem_lhs /= in hr.
    rewrite hr in hRLf.
    by case: hRLf => _ _ _ _ [_ _ _ hroot _]; exact: hroot. }
move=> hroot.
case E: (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf
           st.1.1 st.2.1 st.2.2 sg.1.1 dd sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|].
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[hinv _] _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[hinv _] _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[hinv _] _] _] _]; exact: hinv.
- (* FAnchor *)
  eapply (r_get_rhs_known Lrv true).
    { move=> s0 s1 [[[[hinv hr] _] _] _].
      move/lf_inv2_kmE: hinv => [_ hRLf].
      rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
      by case: hRLf => _ _ hrv _ _. }
  rewrite [assertD true _]/=.
  eapply r_get_remember_rhs => tgtsv.
  case Eans: P; last first.
  + (* P = false: verdict masked *)
    case Eg: (getm tgtsv (fanchoridx st.2.1 sg.1.1)) => [[t0 [m0 md0]]|].
    * eapply r_get_remember_rhs => slogv.
      eapply (r_get_rhs_known Lpp (Some st.1.1)).
        { move=> s0 s1 [[[[[[hinv hr] _] _] _] _] _].
          move/lf_inv2_kmE: hinv => [_ hRLf].
          rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
          by case: hRLf => _ hpo _ _ _. }
      apply r_ret => s0 s1 hpre.
      split; first by [].
      by move: hpre => [[[[[[hinv _] _] _] _] _] _]; exact: hinv.
    * apply r_ret => s0 s1 hpre.
      split; first by [].
      by move: hpre => [[[[[hinv _] _] _] _] _]; exact: hinv.
  + (* P = true: the real LCHECK wins (slog-gated freshness discharge) *)
    have hvm : fxvermd st.1.1 (shrincs_fxmss_root_x PP N F Tl Htree h_sf st.1.1 st.2.1 st.2.2)
                 sg.1.1 dd sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [hin hpos hrec] :=
      shrincs_fxmss_forgery_case_FAnchor PP N D F Tl Hgrind Htree S_wn h_sf
        st.1.1 st.2.1 st.2.2 sg.1.1 dd sg.2.1 sg.2.2 hvm E.
    have Eidx : fanchoridx st.2.1 sg.1.1
              = index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                      (leaf_paths (tshape st.2.1))
      by rewrite /fanchor_idx.
    eapply (r_fact (exists md0,
              getm tgtsv (fanchoridx st.2.1 sg.1.1)
              = Some (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2),
                      (nth [::] st.2.2
                         (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                                (leaf_paths (tshape st.2.1))), md0))
              /\ md0 = odflt d0 (getm sd (fanchoridx st.2.1 sg.1.1)))).
      { move=> s0 s1 [[[[[hinv hr] _] hsdr] _] htg].
        move/lf_inv2_kmE: hinv => [_ hRLf].
        rewrite /rem_lhs /rem_rhs /= in hr hsdr htg.
        rewrite hr in hRLf.
        case: hRLf => _ _ _ htgv _.
        exists (odflt d0 (getm sd (fanchoridx st.2.1 sg.1.1))).
        split; last by [].
        rewrite -htg htgv Eidx.
        rewrite (getm_leafcommitq_km st.2.1 (get_heap s0 (shrincs_fxmss_sd_loc D)) st.2.2 _ hin).
        by rewrite hsdr. }
    move=> [md0 [Etg Emd0]].
    rewrite Etg /=.
    eapply r_get_remember_rhs => slogv.
    eapply (r_fact (((fanchoridx st.2.1 sg.1.1 \notin slogv) || (dd != md0))%bool)).
      { move=> s0 s1 hpre.
        move: hpre => [hpre hslogvr].
        move: hpre => [hpre _].
        move: hpre => [hpre _].
        move: hpre => [hpre _].
        move: hpre => [hpre _].
        move: hpre => [hinv hr].
        move/lf_inv2_kmE: (hinv) => [_ hRLf].
        rewrite /rem_lhs /rem_rhs /= in hslogvr hr.
        rewrite hr in hRLf.
        case: hRLf => _ _ _ _ [_ _ _ _ [hsz _ _]].
        apply/orP.
        case Hj: (fanchoridx st.2.1 sg.1.1 \in slogv); [right | by left].
        apply/negP => /eqP Hdd.
        have hlt : (fanchoridx st.2.1 sg.1.1 < n_max)%N.
          apply: (leq_trans _ hsz). rewrite Eidx index_mem. exact: hin.
        have hmd0cod : md0 \in codomm sd by rewrite Emd0; exact: (Hcod _ hlt).
        move: Eans; rewrite /P => /andP[/andP[_ hmnl] hncoll].
        move: hncoll; rewrite /coll_ev Hdd hmd0cod /= negbK => /eqP hget.
        move: (HtbA (sg.1.1, m) sg.1.2 hget) => /= hin'.
        by rewrite (negbTE hmnl) in hin'. }
    move=> hgate.
    eapply (r_get_rhs_known Lpp (Some st.1.1)).
      { move=> s0 s1 [[[[[[hinv hr] _] _] _] _] _].
        move/lf_inv2_kmE: hinv => [_ hRLf].
        rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
        by case: hRLf => _ hpo _ _ _. }
    have hwin : (lrc st.1.1 (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2))
                   dd sg.2.1
                 == lpk st.1.1 (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2))
                      (nth [::] st.2.2
                         (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                                (leaf_paths (tshape st.2.1))))) = true.
      rewrite -/(leaf_win PP N D (leaf_pk_c PP N F Tl)
                   (leaf_rec_c PP N D F Tl Hgrind) st.1.1
                   (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)) dd sg.2.1
                   (nth [::] st.2.2
                      (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                             (leaf_paths (tshape st.2.1))))).
      rewrite (leaf_win_panchor PP N D F Tl Hgrind h_sf Hh
                 (leaf_pk_c PP N F Tl) (leaf_rec_c PP N D F Tl Hgrind)
                 (leaf_pkE_c PP N F Tl) (leaf_recE_c PP N D F Tl Hgrind)
                 st.1.1 (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2) dd sg.2.1
                 (nth [::] st.2.2
                    (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                           (leaf_paths (tshape st.2.1))))
                 (leaf_path_pos_ok h_sf st.2.1 _ hin)).
      apply/eqP.
      by rewrite {1}hpos; exact: hrec.
    apply r_ret => s0 s1 hpre; split.
    * by rewrite hwin hgate !andbT.
    * by move: hpre => [[[[[[hinv _] _] _] _] _] _]; exact: hinv.
Qed.

(** FORGE verdict bridge (IDEAL): G6f's [fverd keepA] equals the
    [shrincs_fxmss_forgery_case_pks] classify-and-LCHECK verdict under [MIW_km false]
    (LCHECK = false = keepAnchor on FAnchor).  The km mirror of
    [r_leaf_forge_verdict''_ideal]. *)
Lemma r_leaf_forge_verdict_km_ideal (st : FXST) (pkm : {fmap (seq bool) -> N})
    (lg : seq M) (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (dd : D) :
  (forall p, p \in leaf_paths (tshape st.2.1) ->
     getm pkm p = Some (anchor_val PP N F Tl h_sf st.1.1 st.2.1 st.2.2 p)) ->
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv2_km ⋊ rem_lhs Lst (Some st)
              ⋊ rem_rhs Lst (Some (st.1, (st.2.1, @dummy_xss N)))
              ⋊ rem_rhs (rl_pks_loc N) pkm) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            keepA st st.2.2 st.2.1 lg sd tb m sg dd)
     ≈ (match shrincs_fxmss_forgery_case_pks PP N D F Tl Hgrind Htree h_sf n0
               st.1.1 st.2.1 pkm sg.1.1 dd sg.2.1 sg.2.2 with
          | merkle.FAnchor =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd) && false)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv2_km (s0, s1) ⦄.
Proof.
move=> hpkm.
rewrite (shrincs_fxmss_forgery_case_pks_bridge PP N D F Tl Hgrind Htree h_sf n0
           st.1.1 st.2.1 st.2.2 pkm sg.1.1 dd sg.2.1 sg.2.2 hpkm).
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd).
rewrite /fverd -/P.
case E: (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf
           st.1.1 st.2.1 st.2.2 sg.1.1 dd sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[hinv _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split.
  + by rewrite andbF.
  + by move: hpre => [[[hinv _] _] _]; exact: hinv.
Qed.

(* ================================================================== *)
(** ** The WLOG "all leaves signed" fix (the all-leaves-signed argument + the leaf-hop architecture
    M0): the strengthened endpoint game [MIW_kmS].  The adaptive slog-gate of
    [mkm_win] is replaced by the STATIC population gate [gateS], the win
    acquires the Section-1.4 [shrincs_fxmss_wots_checks] guard (skeptic GAP-1 repair:
    [mkm_winSG]), and LSIGN acquires the budget guard [j < q_s]
    ([mkm_signS]).  Interface [I_MIW_km] and locations [MKMLocs] UNCHANGED;
    [R_leaf_km] reused byte-identical. *)

(** The leaf coordinate of a tweak (also defined downstream in Leaf2Games;
    duplicated here so the WLOG gate lives with the endpoint game). *)
Definition lcoord (t : adrs_sf_ch) : nat * nat := adrs_keypair (decode_tweak t).

Local Notation lfind t0 pp md0 :=
  (find_ctr PP D Hgrind S_wn c_max (lcoord t0).1 (lcoord t0).2 pp md0).

(** The lifted STATIC population gate: NO budget disjunct.  Under per-leaf
    presampling EVERY leaf has a real committed digest, so the shared
    [gateS]'s [(q_s <= j)] disjunct is simply DELETED: pop-1 = "committed
    digest grindable at the committed coordinate" (commit-static), pop-2 =
    the rest (bare opening, virtual re-root).  No slog read, no budget. *)
Definition gateL (pp : PP) (t0 : adrs_sf_ch) (md0 : D) (dd : D) : bool :=
  ~~ isSome (lfind t0 pp md0) || (dd != md0).

#[local] Arguments gateL : simpl never.

(** codomm membership of any committed slot from sd-totality (under per-leaf
    presampling EVERY leaf slot is committed = [isSome]). *)
Lemma sd_total_cod (sd : chMap 'nat D) (j : nat) :
  isSome (getm sd j) -> odflt d0 (getm sd j) \in codomm sd.
Proof.
case E: (getm sd j) => [d|] // _. apply/codommP. by exists j.
Qed.

(** Probe B (M5_lift_probe.v), budget-free: the shared verdict lemma's own
    hypothesis set discharges the gate at EVERY committed slot -- signed or
    not.  (The shared [gateS_discharge] needed the [(q_s <= j)] case split
    only because out-of-budget leaves committed [d0 \notin codomm sd]; with
    per-leaf presampling that case is gone.) *)
Lemma gateL_discharge (pp : PP) (t0 : adrs_sf_ch)
    (sd : chMap 'nat D) (tb : chMap (('nat × 'nat) × M) R)
    (lg : seq M) (m : M) (zi : 'nat × 'nat) (r : R) (dd : D) (j : nat) :
  (forall (k : ('nat × 'nat) × M) (rr : R), getm tb k = Some rr -> k.2 \in lg) ->
  m \notin lg ->
  ~~ coll_ev D M R sd tb (zi, m) r dd ->
  isSome (getm sd j) ->
  gateL pp t0 (odflt d0 (getm sd j)) dd.
Proof.
move=> HtbA Hlg Hcoll Hj.
rewrite /gateL.
have hdd : dd \notin codomm sd.
  move: Hcoll; rewrite /coll_ev negb_and negbK.
  case/orP => [//|/eqP htb].
  by have := HtbA (zi, m) r htb; rewrite /= (negbTE Hlg).
apply/orP; right.
apply/eqP => hddmd.
by move: hdd; rewrite hddmd (sd_total_cod sd j Hj).
Qed.

(** Skeptic GAP 2 (WLOG_skeptic_probe.v): the coordinate identification. *)
Lemma lcoord_panchor (p : seq bool) :
  anchor_bounded (posid p) -> lcoord (panchor p) = posid p.
Proof.
move=> hp; rewrite /lcoord decode_tweakK.
exact: (shrincs_fxmss_wots_pk_adrs_keypair l w (posid p) hp).
Qed.

(** Skeptic SK1 (SKEPTIC_WLOG_attack.v): the shrincs_fxmss_wots_checks transport to the
    committed coordinate, self-contained (derives the FAnchor coordinate
    identification from fxvermd's range conjuncts). *)
Lemma wots_checks_transport (pp : PP) (rt : N) (zi : nat * nat) (md : D)
    (ws : seq N * nat) (ap : seq N) :
  fxvermd pp rt zi md ws ap ->
  shrincs_fxmss_wots_checks PP N D Hgrind S_wn pp
    (lcoord (panchor (path_of_idx (h_sf - zi.1) zi.2))) md ws.
Proof.
move=> /and4P[hz1 /andP[hz2 hrepr] hchecks _].
have hzi := shrincs_fxmss_anchor_bounded h_sf zi.1 zi.2 Hh hz1
              (index_boundedP zi.2 hrepr).
have hposid : posid (path_of_idx (h_sf - zi.1) zi.2) = zi.
  rewrite /shrincs_fxmss_pos_id size_path_of_idx idx_of_path_of_idx // subKn //.
  by case: (zi).
rewrite /lcoord decode_tweakK hposid.
rewrite (shrincs_fxmss_wots_pk_adrs_keypair l w zi hzi).
exact: hchecks.
Qed.

(** Skeptic GAP 2 (WLOG_skeptic_probe.v): the transport at a GIVEN
    coordinate identification (shrincs_fxmss_forgery_case_FAnchor's hpos). *)
Lemma shrincs_fxmss_verify_md_wots_checks_transport (pp : PP) (rt : N) (zi : nat * nat)
    (md : D) (ws : seq N * nat) (ap : seq N) (p : seq bool) :
  posid p = zi ->
  fxvermd pp rt zi md ws ap ->
  shrincs_fxmss_wots_checks PP N D Hgrind S_wn pp (lcoord (panchor p)) md ws.
Proof.
move=> hpos /and4P[hz1 /andP[hz2 hrepr] hwc _].
have hzi := shrincs_fxmss_anchor_bounded h_sf zi.1 zi.2 Hh hz1
              (index_boundedP zi.2 hrepr).
have hp : anchor_bounded (posid p) by rewrite hpos.
by rewrite (lcoord_panchor p hp) hpos.
Qed.

(** Skeptic SK3 lift (M5_lift_probe.v): STCRP enc-pair freshness is FORCED by
    [gateL] on ALL grindable leaves (the shared [stcrp_fresh_forced]'s
    [(j < q_s)] hypothesis DROPS). *)
Lemma stcrp_fresh_forcedL (pp : PP) (t0 : adrs_sf_ch) (md0 : D)
    (mw : D × (('list N) × 'nat)) (c : nat) :
  lfind t0 pp md0 = Some c ->
  gateL pp t0 md0 mw.1 ->
  (mw.1, mw.2.2) != (md0, c).
Proof.
move=> hfc; rewrite /gateL hfc /= => hne.
by apply/eqP => -[h1 _]; move: hne; rewrite h1 eqxx.
Qed.

(** Probe D (M5_lift_probe.v): the same-digest gate is DEAD at ANY grindable
    leaf -- signed, unsigned, in or out of budget -- killing the obstruction
    input at the top of the ladder, budget-free. *)
Lemma gateL_same_digest_dead (pp : PP) (t0 : adrs_sf_ch) (md0 : D) (c : nat) :
  lfind t0 pp md0 = Some c ->
  gateL pp t0 md0 md0 = false.
Proof. by move=> hfc; rewrite /gateL hfc eqxx orbF. Qed.

(** Probe helper (WLOG_probe.v): a valid digest is never all-max under
    Hdeg (zsel_dead's counting, standalone; consumed by layer (ii)). *)
Lemma valid_not_allmax (ds : seq nat) :
  S_wn != (l * w.-1)%N ->
  @valid_digest w S_wn ds ->
  size ds = l ->
  has (fun d => (d < w.-1)%N) ds.
Proof.
move=> hdeg /andP[hwf /eqP hsum] hsz.
apply/negbNE/negP => /hasPn hall.
have hall1 : all (pred1 w.-1) ds.
  apply/allP => d hd.
  have h1 : (d < w)%N := allP hwf d hd.
  have h2 : (w.-1 <= d)%N by rewrite leqNgt; exact: hall.
  by rewrite /= eqn_leq h2 andbT -ltnS (ltn_predK h1).
move/eqP: hdeg; apply.
by rewrite -hsum (all_pred1P _ _ hall1) sumn_nseq hsz mulnC.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The strengthened win/sign bodies and the game [MIW_kmS]
    (skeptic-repaired GAP-1 form: the win carries the shrincs_fxmss_wots_checks guard). *)

Definition mkm_winSG (j : nat) (mw : D × (('list N) × 'nat)) : raw_code 'bool :=
  (revealed ← get Lrv ;;
   #assert revealed ;;
   tgts ← get mkm_tgts_loc ;;
   match getm tgts j with
   | Some (t0, (m0, md0)) =>
       ppo ← get Lpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
            end ;;
       ret (shrincs_fxmss_wots_checks PP N D Hgrind S_wn pp (lcoord t0) mw.1 mw.2
            && (lrc pp t0 mw.1 mw.2 == lpk pp t0 m0)
            && gateL pp t0 md0 mw.1)
   | None => ret false
   end).

(** LSIGN with the budget guard: out-of-budget slots never reveal
    (they are the virtual/zero-query population by CONSTRUCTION). *)
(** LSIGN is budget-free: the [(j < q_s)] guard is absent; only the
    one-time [j \notin slog] guard remains.  Byte-identical to [mkm_sign]. *)
Definition mkm_signS (j : nat) : raw_code ('option (('list N) × 'nat)) :=
  (slog ← get Lsl ;;
   #assert (j \notin slog) ;;
   tgts ← get mkm_tgts_loc ;;
   match getm tgts j with
   | Some (t0, (xs, md)) =>
       ppo ← get Lpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put Lpp := Some pp ;; ret pp
            end ;;
       match lsg pp t0 xs md with
       | Some ws => #put Lsl := rcons slog j ;; ret (Some ws)
       | None => ret None
       end
   | None => ret None
   end).

#[local] Instance mkm_winSG_valid (I : Interface) (j : nat)
    (mw : D × (('list N) × 'nat)) :
  ValidCode MKMLocs I (mkm_winSG j mw).
Proof.
rewrite /mkm_winSG.
eapply valid_getr; first by fmap_solve. move=> revealed.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 [m0 md0]]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; apply valid_ret.
Qed.

#[local] Instance mkm_signS_valid (I : Interface) (j : nat) :
  ValidCode MKMLocs I (mkm_signS j).
Proof.
rewrite /mkm_signS.
eapply valid_getr; first by fmap_solve. move=> slog.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> tgts.
case: (getm tgts j) => [[t0 [xs md]]|]; last by apply valid_ret.
eapply valid_getr; first by fmap_solve. move=> ppo.
eapply valid_bind.
  case: ppo => [pp|]; first by apply valid_ret.
  eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> pp; eapply valid_putr; first by fmap_solve.
  apply valid_ret.
move=> pp; case: (lsg pp t0 xs md) => [ws|]; last by apply valid_ret.
eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

Definition MIW_kmS (b : bool) : game I_MIW_km.
Proof.
notypeclasses refine [package MKMLocs ;
    [ LCOMMIT ] : { adrs_sf_ch × D ~> N } '(t, md) { mkm_commit t md } ;
    [ LGETPP ] : { 'unit ~> PP } (_) { mkm_getpp } ;
    [ LCHECK ] : { 'nat × (D × (('list N) × 'nat)) ~> 'bool } '(j, mw) {
      if b then mkm_winSG j mw else ret false } ;
    [ LSIGN ] : { 'nat ~> 'option (('list N) × 'nat) } (j) { mkm_signS j } ;
    [ LCOLLQ ] : { adrs_sf_ch × ((N × N) ∐ (D × 'nat)) ~> (N ∐ 'nat) } '(t, x) {
      mkm_collq t x }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { eapply valid_package_cons.
        { apply: valid_empty_package. }
        { intros [t x]; exact: mkm_collq_valid. } }
      { intro j; exact: mkm_signS_valid. } }
    { intros [j mw]; case: ifP => _; [exact: mkm_winSG_valid|apply valid_ret]. } }
  { intro u; exact: mkm_getpp_valid. } }
{ intros [t md]; exact: mkm_commit_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Resolve equations for [MIW_kmS]'s oracles. *)

Lemma resolve_lcm_kmS (b : bool) (t : adrs_sf_ch) (md : D) :
  resolve (MIW_kmS b) lf_cmo_km (t, md) = mkm_commit t md.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lsg_kmS (b : bool) (j : nat) :
  resolve (MIW_kmS b) lf_sgo_km j = mkm_signS j.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lcq_kmS (b : bool) (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) :
  resolve (MIW_kmS b) lf_cqo_km (t, x) = mkm_collq t x.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lgp_kmS (b : bool) (u : unit) :
  resolve (MIW_kmS b) lf_gpo_km u = mkm_getpp.
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_lck_kmS_true (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_kmS true) lf_cko_km (j, mw) = mkm_winSG j mw.
Proof. by simplify_linking. Qed.

Lemma resolve_lck_kmS_false (j : nat) (mw : D × (('list N) × 'nat)) :
  resolve (MIW_kmS false) lf_cko_km (j, mw) = ret false.
Proof. by simplify_linking. Qed.

#[local] Arguments mkm_signS : simpl never.

(* ------------------------------------------------------------------ *)
(** ** Stepping twins against [MIW_kmS] (byte-identical to the shared
    [MIW_km] versions -- LCOMMIT/LGETPP/LCOLLQ bodies are unchanged, so
    only the resolve names differ). *)

Lemma r_lcommit_sample_kmS (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (md : D) (Q : seq (adrs_sf_ch * ('list N × D)))
    (pkm : {fmap (seq bool) -> N})
    (k0 : 'list N -> raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < n_max)%N ->
  gtw_of t \notin [seq gtw_of x | x <- unzip1 Q] ->
  (forall xs : 'list N, size xs = l ->
     ⊢ ⦃ λ '(s0, s1), lblkQ_km (Some pp) false (rcons Q (t, (xs, md))) pkm (s0, s1) ⦄
        k0 xs ≈ k1 (lpk pp t xs) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ_km (Some pp) false Q pkm (s0, s1) ⦄
     (xs ← sample_seq dN l ;; k0 xs)
     ≈ bind (resolve (MIW_kmS b) lf_cmo_km (t, md)) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh h.
rewrite (resolve_lcm_kmS b t md) /mkm_commit.
eapply (r_get_bind_rhs Lrv false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs Ltw (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
rewrite bind_assoc.
apply: (r_sample_seq_size_l N dN l) => xs hxs.
eapply (r_get_bind_rhs mkm_tgts_loc (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ [h' _ _ _ _]].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (lblkQ_km_upd pp Q t (xs, md) pkm s0 s1 hpre).
eapply (r_get_bind_rhs Lpp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: (h xs hxs).
Qed.

Lemma r_lcollq_known_kmS (b : bool) {B : choiceType} (pp : PP)
    (t : adrs_sf_ch) (x : (N × N) ∐ (D × 'nat)) rv tw tg pkm
    (c0 : raw_code B) (k1 : (N ∐ 'nat) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (lcoll pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (resolve (MIW_kmS b) lf_cqo_km (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_lcq_kmS b t x) /mkm_collq.
eapply (r_get_bind_rhs Lpp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: h.
Qed.

Lemma lf_tree_kmS_spec (b : bool) {B : choiceType} (pp : PP)
    (sp : seq bool) (sd : chMap 'nat D) (post : postcond B B) :
  forall (pos : seq bool) (t : bt unit)
         (Q : seq (adrs_sf_ch * ('list N × D))) (pkm : {fmap (seq bool) -> N})
         (k0 : seq (seq N) -> raw_code B) (k1 : N -> raw_code B),
  uniq (leaf_tws_under h_sf pos t ++ unzip1 Q) ->
  (size Q + size (leaf_paths t) <= n_max)%N ->
  [seq gtw_of x | x <- unzip1 Q] = unzip1 Q ->
  (forall xss_t, size xss_t = size (leaf_paths t) ->
     (forall x, x \in xss_t -> size x = l) ->
     ⊢ ⦃ λ '(s0, s1),
           lblkQ_km (Some pp) false (Q ++ lf_commitsL_km sp sd pos xss_t t)
             (pkmofk pp pos xss_t t pkm) (s0, s1) ⦄
        k0 xss_t ≈ k1 (tvalLk pp pos xss_t t) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), lblkQ_km (Some pp) false Q pkm (s0, s1) ⦄
     (xss_t ← skeys (size (leaf_paths t)) ;; k0 xss_t)
     ≈ bind (code_link (lf_tree_km sp sd pos t) (MIW_kmS b)) k1 ⦃ post ⦄.
Proof.
move=> pos t; move: pos.
elim: t => [[]|tl IHl tr IHr].
- (* leaf: one sampling LCOMMIT-with-digest, then record the pk *)
  move=> pos Q pkm k0 k1 huniq hbud hpanQ h.
  rewrite [lf_tree_km sp sd pos (BLeaf tt)]/= code_link_opr_bind.
  rewrite [skeys (size (leaf_paths (BLeaf tt)))]/= bind_assoc.
  apply: (r_lcommit_sample_kmS b pp (panchor pos) (kmdg sp sd pos) Q pkm
            (fun xs => k0 (xs :: [::]))
            (fun pk => pkm0 ← get Lpks ;;
                       #put Lpks := setm pkm0 pos pk ;; k1 pk)).
  + by move: hbud; rewrite /= addn1.
  + rewrite hpanQ gtw_AdrPk.
    by move: huniq; rewrite /leaf_tws_under /= cats0 => /andP[h1 _].
  + move=> xs hxs.
    eapply (r_get_rhs_known Lpks pkm).
      by move=> s0 s1 [_ _ _ _ [_ h' _ _ _]].
    eapply (r_put_rhs_weak Lpks (setm pkm pos (lpk pp (panchor pos) xs))
              (lblkQ_km (Some pp) false (rcons Q (panchor pos, (xs, kmdg sp sd pos))) pkm)
              (lblkQ_km (Some pp) false (rcons Q (panchor pos, (xs, kmdg sp sd pos)))
                 (setm pkm pos (lpk pp (panchor pos) xs)))).
      by move=> s0 s1 hpre;
         exact: (lblk_km_pks_upd (Some pp) false
                   (unzip1 (rcons Q (panchor pos, (xs, kmdg sp sd pos))))
                   (qmap_from 0 (rcons Q (panchor pos, (xs, kmdg sp sd pos)))) pkm pos
                   (lpk pp (panchor pos) xs) s0 s1 hpre).
    have E1 : lf_commitsL_km sp sd pos [:: xs] (BLeaf tt)
            = [:: (panchor pos, (xs, kmdg sp sd pos))] by [].
    have E2 : pkmofk pp pos [:: xs] (BLeaf tt) pkm
            = setm pkm pos (lpk pp (panchor pos) xs) by [].
    have E3 : tvalLk pp pos [:: xs] (BLeaf tt) = lpk pp (panchor pos) xs by [].
    have hs : size ([:: xs] : seq (seq N)) = size (leaf_paths (BLeaf tt)) by [].
    have hl : forall y, y \in ([:: xs] : seq (seq N)) -> size y = l.
      by move=> y; rewrite inE => /eqP ->.
    have hh := h [:: xs] hs hl.
    rewrite E1 E2 E3 cats1 in hh.
    exact: hh.
- exact: B.
- (* node: split the key draw, recurse left/right, hash the node *)
  move=> pos Q pkm k0 k1 huniq hbud hpanQ h.
  have Esz : size (leaf_paths (BNode tl tr))
             = (size (leaf_paths tl) + size (leaf_paths tr))%N.
    by rewrite /= size_cat !size_map.
  rewrite Esz sample_keys_cat !bind_assoc.
  rewrite code_link_bind bind_assoc.
  set Lt := @leaf_tws_under w l h_sf (rcons pos false) tl.
  set Rt := @leaf_tws_under w l h_sf (rcons pos true) tr.
  have hbud' : (size Q + size (leaf_paths tl) + size (leaf_paths tr) <= n_max)%N.
    by move: hbud; rewrite Esz addnA.
  move: huniq; rewrite leaf_tws_under_node -/Lt -/Rt -catA => huniq.
  eapply (IHl (rcons pos false) Q pkm).
  + apply: (subseq_uniq _ huniq).
    apply: cat_subseq; first exact: subseq_refl.
    exact: suffix_subseq.
  + apply: leq_trans hbud'; exact: leq_addr.
  + (* hpanQ for the left recursion: Q unchanged *)
    exact: hpanQ.
  + move=> a hsza hsla.
    rewrite bind_assoc code_link_bind bind_assoc.
    eapply (IHr (rcons pos true) (Q ++ lf_commitsL_km sp sd (rcons pos false) a tl)
              (pkmofk pp (rcons pos false) a tl pkm)).
    * rewrite unzip1_cat_km unzip1_lf_commitsL_km -/Lt -/Rt.
      have hperm : perm_eq (Rt ++ unzip1 Q ++ Lt) (Lt ++ Rt ++ unzip1 Q).
        by rewrite (catA Rt) perm_catC.
      rewrite (perm_uniq hperm); exact: huniq.
    * rewrite size_cat size_lf_commitsL_km.
      exact: hbud'.
    * (* hpanQ for the right recursion: Q ++ left-commits, all pk-anchors *)
      rewrite unzip1_cat_km unzip1_lf_commitsL_km map_cat hpanQ
              map_gtw_leaf_tws_under.
      by [].
    * move=> bb hszb hslb.
      rewrite code_link_opr_bind.
      eapply (r_lcollq_known_kmS b pp (tnode pos)
                (inl (tvalLk pp (rcons pos false) a tl,
                      tvalLk pp (rcons pos true) bb tr) : (N × N) ∐ (D × 'nat))).
      have hnh : forall x y, Htree pp (decode_tweak (tnode pos)) (x, y)
                             = nhash pp pos x y.
        by move=> x y; rewrite -(lcollq_node_E PP N D Hgrind Htree h_sf n0 pp pos x y).
      rewrite hnh.
      have hsz_ab : size (a ++ bb) = size (leaf_paths (BNode tl tr)).
        by rewrite size_cat hsza hszb Esz.
      have hall_ab : forall x, x \in a ++ bb -> size x = l.
        by move=> x; rewrite mem_cat => /orP[]; [exact: hsla|exact: hslb].
      have := h (a ++ bb) hsz_ab hall_ab.
      rewrite /lf_commitsL_km -/lf_commitsL_km /pkm_of -/pkm_of /tvalL -/tvalL.
      by rewrite -hsza take_size_cat // drop_size_cat // catA.
Unshelve. all: try exact: B.
Qed.

Lemma r_grind_kmS_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (zi : nat * nat) (d : D) (cs : seq nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : chList 'nat -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (gadrs zi) (d, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_grind_km zi d cs) (MIW_kmS b)) k1 ⦃ post ⦄.
Proof.
move=> zi d cs; elim: cs => [|c cs IH] rv tw tg pkm c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_lcollq_known_kmS b).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite (lcollq_grind_E PP N D Hgrind Htree) /= in h *.
Qed.

Lemma r_slot_grind_kmS_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (j : nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (match getm sd j with
              | Some d => slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d
              | None => true
              end) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_slot_grind_km sp sd j) (MIW_kmS b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd j rv tw tg pkm c0 k1 h.
rewrite /lf_slot_grind_km.
case E: (getm sd j) => [d|]; rewrite E /= in h.
- rewrite code_link_bind bind_assoc.
  eapply (r_grind_kmS_spec b pp post (posid (spath sp j)) d (iota 0 c_max)).
  rewrite code_link_ret_bind has_grind_find_ctr.
  rewrite -/(slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d).
  exact: h.
- by rewrite code_link_ret_bind; exact: h.
Qed.

Lemma r_gcheck_kmS_spec (b : bool) {B : choiceType} (pp : PP) (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) rv tw tg pkm
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ k1 (all (fun j => match getm sd j with
                | Some d => slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d
                | None => true
                end) js) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), lblk_km (Some pp) rv tw tg pkm (s0, s1) ⦄
     c0 ≈ bind (code_link (lf_gcheck_km sp sd js) (MIW_kmS b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd js; elim: js => [|j js IH] rv tw tg pkm c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_slot_grind_kmS_spec b pp post sp sd j).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite code_link_ret_bind.
Qed.

(** FORGE verdict bridge for the STRENGTHENED win (the WLOG re-link core):
    G5f's [fverd (fun _ => true)] equals the [shrincs_fxmss_forgery_case_pks] classify-and-LCHECK
    verdict under [MIW_kmS true].  Vs the shared [r_leaf_forge_verdict_km]:
    the slog read and its slog-gate sub-derivation are DELETED; the two NEW
    conjuncts ([shrincs_fxmss_wots_checks] at the committed coordinate, [gateS]) are
    discharged from the SAME hypothesis set via [shrincs_fxmss_verify_md_wots_checks_transport]
    (skeptic GAP 2) and [gateS_discharge] (probe B). *)
Lemma r_leaf_forge_verdict_kmS (st : FXST) (pkm : {fmap (seq bool) -> N})
    (lg : seq M) (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (dd : D) :
  (forall p, p \in leaf_paths (tshape st.2.1) ->
     getm pkm p = Some (anchor_val PP N F Tl h_sf st.1.1 st.2.1 st.2.2 p)) ->
  (forall (k : ('nat × 'nat) × M) (rr : R), getm tb k = Some rr -> k.2 \in lg) ->
  (forall jj, (jj < n_max)%N -> odflt d0 (getm sd jj) \in codomm sd) ->
  ⊢ ⦃ λ '(s0, s1),
        (lf_inv2_km ⋊ rem_lhs Lst (Some st)
              ⋊ rem_rhs Lst (Some (st.1, (st.2.1, @dummy_xss N)))
              ⋊ rem_lhs (shrincs_fxmss_sd_loc D) sd
              ⋊ rem_rhs (rl_pks_loc N) pkm) (s0, s1) ⦄
     ret (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf
            (fun _ => true) st st.2.2 st.2.1 lg sd tb m sg dd)
     ≈ (match shrincs_fxmss_forgery_case_pks PP N D F Tl Hgrind Htree h_sf n0
               st.1.1 st.2.1 pkm sg.1.1 dd sg.2.1 sg.2.2 with
          | merkle.FAnchor =>
              v ← get Lrv ;;
              ans ← (#assert v ;;
                     tgts ← get mkm_tgts_loc ;;
                     match getm tgts (fanchoridx st.2.1 sg.1.1) with
                     | Some (t0, (m0, md0)) =>
                         ppo ← get Lpp ;;
                         match ppo with
                         | Some pp =>
                             ret (shrincs_fxmss_wots_checks PP N D Hgrind S_wn pp
                                    (lcoord t0) dd sg.2.1
                                  && (lrc pp t0 dd sg.2.1 == lpk pp t0 m0)
                                  && gateL pp t0 md0 dd)
                         | None => pp ← dPP ;; #put Lpp := Some pp ;;
                             ret (shrincs_fxmss_wots_checks PP N D Hgrind S_wn pp
                                    (lcoord t0) dd sg.2.1
                                  && (lrc pp t0 dd sg.2.1 == lpk pp t0 m0)
                                  && gateL pp t0 md0 dd)
                         end
                     | None => ret false
                     end) ;;
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd) && ans)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ lf_inv2_km (s0, s1) ⦄.
Proof.
move=> hpkm HtbA Hcod.
rewrite (shrincs_fxmss_forgery_case_pks_bridge PP N D F Tl Hgrind Htree h_sf n0
           st.1.1 st.2.1 st.2.2 pkm sg.1.1 dd sg.2.1 sg.2.2 hpkm).
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 dd sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd).
rewrite /fverd -/P.
eapply (r_fact (st.1.2 = shrincs_fxmss_root_x PP N F Tl Htree h_sf st.1.1 st.2.1 st.2.2)).
  { move=> s0 s1 [[[[hinv hr] _] _] _].
    move/lf_inv2_kmE: hinv => [_ hRLf].
    rewrite /rem_lhs /= in hr.
    rewrite hr in hRLf.
    by case: hRLf => _ _ _ _ [_ _ _ hroot _]; exact: hroot. }
move=> hroot.
case E: (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf
           st.1.1 st.2.1 st.2.2 sg.1.1 dd sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|].
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[hinv _] _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[hinv _] _] _] _]; exact: hinv.
- apply r_ret => s0 s1 hpre; split; first by [].
  by move: hpre => [[[[hinv _] _] _] _]; exact: hinv.
- (* FAnchor *)
  eapply (r_get_rhs_known Lrv true).
    { move=> s0 s1 [[[[hinv hr] _] _] _].
      move/lf_inv2_kmE: hinv => [_ hRLf].
      rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
      by case: hRLf => _ _ hrv _ _. }
  rewrite [assertD true _]/=.
  eapply r_get_remember_rhs => tgtsv.
  case Eans: P; last first.
  + (* P = false: verdict masked *)
    case Eg: (getm tgtsv (fanchoridx st.2.1 sg.1.1)) => [[t0 [m0 md0]]|].
    * eapply (r_get_rhs_known Lpp (Some st.1.1)).
        { move=> s0 s1 [[[[[hinv hr] _] _] _] _].
          move/lf_inv2_kmE: hinv => [_ hRLf].
          rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
          by case: hRLf => _ hpo _ _ _. }
      apply r_ret => s0 s1 hpre.
      split; first by [].
      by move: hpre => [[[[[hinv _] _] _] _] _]; exact: hinv.
    * apply r_ret => s0 s1 hpre.
      split; first by [].
      by move: hpre => [[[[[hinv _] _] _] _] _]; exact: hinv.
  + (* P = true: the real LCHECK wins (STATIC gate + guard discharge) *)
    have hvm : fxvermd st.1.1 (shrincs_fxmss_root_x PP N F Tl Htree h_sf st.1.1 st.2.1 st.2.2)
                 sg.1.1 dd sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [hin hpos hrec] :=
      shrincs_fxmss_forgery_case_FAnchor PP N D F Tl Hgrind Htree S_wn h_sf
        st.1.1 st.2.1 st.2.2 sg.1.1 dd sg.2.1 sg.2.2 hvm E.
    have Eidx : fanchoridx st.2.1 sg.1.1
              = index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                      (leaf_paths (tshape st.2.1))
      by rewrite /fanchor_idx.
    (* the two P-mask conjuncts feeding the discharges *)
    have [hmnl hncoll] : (m \notin lg) /\
        ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 dd.
      by move: Eans; rewrite /P => /andP[/andP[_ h1] h2]; split.
    eapply (r_fact (exists md0,
              getm tgtsv (fanchoridx st.2.1 sg.1.1)
              = Some (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2),
                      (nth [::] st.2.2
                         (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                                (leaf_paths (tshape st.2.1))), md0))
              /\ md0 = odflt d0 (getm sd (fanchoridx st.2.1 sg.1.1))
              /\ isSome (getm sd (fanchoridx st.2.1 sg.1.1)))).
      { move=> s0 s1 [[[[[hinv hr] _] hsdr] _] htg].
        move/lf_inv2_kmE: hinv => [_ hRLf].
        rewrite /rem_lhs /rem_rhs /= in hr hsdr htg.
        rewrite hr in hRLf.
        case: hRLf => _ _ _ htgv [_ _ _ _ [hsz _ hK]].
        have hlt : (fanchoridx st.2.1 sg.1.1 < n_max)%N.
          apply: (leq_trans _ hsz). rewrite Eidx index_mem. exact: hin.
        exists (odflt d0 (getm sd (fanchoridx st.2.1 sg.1.1))).
        split; last split.
        - rewrite -htg htgv Eidx.
          rewrite (getm_leafcommitq_km st.2.1 (get_heap s0 (shrincs_fxmss_sd_loc D)) st.2.2 _ hin).
          by rewrite hsdr.
        - by [].
        - by rewrite -hsdr; exact: (hK _ hlt). }
    move=> [md0 [Etg [Emd0 Hsome]]].
    rewrite Etg /=.
    (* NEW conjunct 1: shrincs_fxmss_wots_checks at the committed coordinate (GAP 2). *)
    have hvch : shrincs_fxmss_wots_checks PP N D Hgrind S_wn st.1.1
                  (lcoord (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)))
                  dd sg.2.1.
      exact: shrincs_fxmss_verify_md_wots_checks_transport hpos hvm.
    (* NEW conjunct 3: the STATIC lifted gate (probe B; budget-free). *)
    have hgate : gateL st.1.1
                   (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2))
                   md0 dd.
      rewrite Emd0.
      exact: gateL_discharge HtbA hmnl hncoll Hsome.
    eapply (r_get_rhs_known Lpp (Some st.1.1)).
      { move=> s0 s1 [[[[[hinv hr] _] _] _] _].
        move/lf_inv2_kmE: hinv => [_ hRLf].
        rewrite /rem_lhs /= in hr. rewrite hr in hRLf.
        by case: hRLf => _ hpo _ _ _. }
    have hwin : (lrc st.1.1 (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2))
                   dd sg.2.1
                 == lpk st.1.1 (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2))
                      (nth [::] st.2.2
                         (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                                (leaf_paths (tshape st.2.1))))) = true.
      rewrite -/(leaf_win PP N D (leaf_pk_c PP N F Tl)
                   (leaf_rec_c PP N D F Tl Hgrind) st.1.1
                   (panchor (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)) dd sg.2.1
                   (nth [::] st.2.2
                      (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                             (leaf_paths (tshape st.2.1))))).
      rewrite (leaf_win_panchor PP N D F Tl Hgrind h_sf Hh
                 (leaf_pk_c PP N F Tl) (leaf_rec_c PP N D F Tl Hgrind)
                 (leaf_pkE_c PP N F Tl) (leaf_recE_c PP N D F Tl Hgrind)
                 st.1.1 (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2) dd sg.2.1
                 (nth [::] st.2.2
                    (index (path_of_idx (h_sf - sg.1.1.1) sg.1.1.2)
                           (leaf_paths (tshape st.2.1))))
                 (leaf_path_pos_ok h_sf st.2.1 _ hin)).
      apply/eqP.
      by rewrite {1}hpos; exact: hrec.
    apply r_ret => s0 s1 hpre; split.
    * by rewrite hvch hwin hgate !andbT.
    * by move: hpre => [[[[[hinv _] _] _] _] _]; exact: hinv.
Qed.

Lemma R_leaf_kmS_real (b : bool) :
  perfect IG (G5 b) (R_leaf_km b ∘ MIW_kmS true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ lf_inv2_km).
{ rewrite /lf_inv2_km. ssprove_invariant.
  - by rewrite /rel_empty /RLf2_km.
  - by rewrite /rel_empty /R_tblog. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5_body /gen_redL_km.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (isSome sto = isSome sto')).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  rewrite code_link_assertD.
  eapply r_assertD; first by rewrite eIS.
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 eIS => [pk|] e0 eIS; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), lblk_km None false [::] emptym emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    rewrite /rem_lhs /= in hrem0.
    exact: (lfinv2_km_init s0 s1 hinv hrem0). }
  simpl.
  rewrite (resolve_lcq_kmS true (encode_adrs (gadrs (0, 0)))
             (inl (n0, n0) : (N × N) ∐ (D × 'nat))) /mkm_collq.
  eapply (r_get_bind_rhs Lpp None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (lblk_km_set_pp pp _ _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  (* RHS next is fillc; expose it as a scheme. *)
  rewrite code_link_bind
    (code_link_scheme _ _ _ _ (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  (* SWAP the LHS [skeys; fillc] -> [fillc; skeys]. *)
  apply: (r_swap_blocks (skeys (size (leaf_paths (tshape arg))))
            (fillc (iota 0 n_max) emptym)).
  (* couple fillc <-> fillc, obtaining the sd-totality fact *)
  apply: (r_fillc_dom _ (iota 0 n_max) emptym).
  move=> sd hsdtot _; cbv beta.
  (* couple skeys <-> lf_tree_km *)
  rewrite code_link_bind.
  eapply (lf_tree_kmS_spec true pp arg sd _ [::] (tshape arg) [::] emptym).
  + exact: (@gen_uniq w l N h_sf Hh arg).
  + exact: hcap.
  + by [].
  move=> xss hxsz hkeys.
  cbv beta.
  rewrite cat0s.
  rewrite code_link_bind.
  eapply (r_gcheck_kmS_spec true pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sd_grindable PP D Hgrind S_wn c_max h_sf pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  simpl.
  rewrite (resolve_lgp_kmS true Datatypes.tt) /mkm_getpp.
  eapply (r_get_bind_rhs Lpp (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (lblk_km_set_rev _ _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrv htws [htgts hpkm hus hscL [hslog htbE]].
  split;
    first by rewrite (tvalL_root PP N F Tl Htree h_sf Hh
                        (leaf_pk_c PP N F Tl) (leaf_pkE_c PP N F Tl)
                        pp arg xss hxsz).
  apply: lf_inv2_kmI.
  + apply: heap_ignore_set_both.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign.
  + get_heap_simpl.
    rewrite hpp hrv htws htgts hpkm hus hscL hslog.
    rewrite (tvalL_root PP N F Tl Htree h_sf Hh
               (leaf_pk_c PP N F Tl) (leaf_pkE_c PP N F Tl) pp arg xss hxsz).
    rewrite unzip1_lf_commitsL_km (lf_commitsL_km_root arg sd xss hxsz).
    split; [ by [] | by [] | by [] | by [] |].
    split; [ by [] | | | by [] | ].
    * by move=> p hp;
        rewrite (getm_pkm_of PP N F Tl h_sf Hh (leaf_pk_c PP N F Tl)
                   (leaf_pkE_c PP N F Tl) pp arg xss hxsz p hp).
    * split; [ by move=> x; rewrite in_nil | by move=> zi; rewrite domm0 in_fset0 ].
    * split; [ exact: hcap | exact: e1 | ].
      by move=> jj hjj; apply: hsdtot; rewrite mem_iota add0n;
         apply/andP; split; [exact: leq0n | exact: hjj].
  + get_heap_simpl. rewrite htbE.
    by move=> k rr; rewrite emptymE.
- (* SIGN *)
  rewrite /sign5_body /sign_redL_km.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_km_pre. } move=> sc.
  ssprove_sync => hsc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  eapply (r_fact (stR = (stL.1, (stL.2.1, @dummy_xss N)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => usr.
  eapply (r_fact (us = usr)).
    { move=> s0 s1 [[[[hinv _] _] hrq] hrqr].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hrq hrqr.
      rewrite -hrq -hrqr.
      apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst usr.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lgr.
  eapply (r_fact (lg = lgr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hlgr]. move: hpre => [hpre hlg].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hlg hlgr.
      rewrite -hlg -hlgr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst lgr.
  ssprove_sync. { lf_getr_km. } move=> mp.
  eapply r_get_remember_lhs => tb.
  eapply r_get_remember_rhs => tbr.
  eapply (r_fact (tb = tbr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre htbr]. move: hpre => [hpre htb].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in htb htbr.
      rewrite -htb -htbr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst tbr.
  eapply (r_fact (forall (k : ('nat × 'nat) × M) (rr : R),
                    getm tb k = Some rr -> k.2 \in lg)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre htb].
      move: hpre => [hpre _]. move: hpre => [hpre hlg].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv hstoL].
      move/lf_inv2_km_tblogE: hinv => hT.
      rewrite /rem_lhs /= in htb hlg hstoL.
      rewrite hstoL htb hlg in hT.
      exact: hT. }
  move=> hAold.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1),
      (lf_inv2_km ⋊ rem_lhs Lst (Some stL)
         ⋊ rem_rhs Lst (Some (stL.1, (stL.2.1, @dummy_xss N)))
         ⋊ rem_lhs shrincs_fxmss_used_loc us ⋊ rem_rhs shrincs_fxmss_used_loc us) (s0, s1)); last first.
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      exact: hpre. }
  eapply r_get_remember_lhs => sd.
  eapply r_get_remember_rhs => sdr.
  eapply (r_fact (sd = sdr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hsdr]. move: hpre => [hpre hsd].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hsd hsdr.
      rewrite -hsd -hsdr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst sdr.
  eapply r_get_remember_rhs => pkm.
  case Hg: (flok stL.2.1 arg.2 && (arg.2 \notin domm us)); last first.
  { eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    split; first by [].
    case: hpre => s1a [hpre ->].
    case: hpre => s0a [hpre ->].
    move: hpre => [hpre _]. move: hpre => [hpre _].
    move: hpre => [hpre _]. move: hpre => [hpre _].
    move: hpre => [hpre _]. move: hpre => [hpre hstoR].
    move: hpre => [hinv hstoL].
    move/lf_inv2_kmE: (hinv) => [hign hR].
    move/lf_inv2_km_tblogE: hinv => hT.
    rewrite /rem_lhs /rem_rhs /= in hstoL hstoR.
    rewrite hstoL in hR hT.
    case: hR => hsoR hpo hrv htg [htw hpk [hsub hval] hroot [hsz hgrind hK]].
    apply: lf_inv2_kmI.
    - by apply: heap_ignore_set_both.
    - get_heap_simpl.
      rewrite hstoL.
      split; [ exact: hsoR | exact: hpo | exact: hrv | exact: htg |].
      split; [ exact: htw | exact: hpk | split; [exact: hsub|exact: hval] | exact: hroot |].
      split; [ exact: hsz | exact: hgrind | exact: hK ].
    - by get_heap_simpl; rewrite hstoL; exact: hT. }
  move: Hg => /andP [hfok hfresh].
  have Hli := leafid_index_lt h_sf stL.2.1 arg.2 hfok.
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val PP N F Tl h_sf stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hpkmr]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre hstoR].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ hpk _ _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  eapply (r_fact (isSome (getm sd (flidx stL.2.1 arg.2)))).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre hsd]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hsd hstoL.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ _ _ _ [hsz _ hK]].
      rewrite hsd in hK. apply: hK; exact: (leq_trans Hli hsz). }
  move=> hsdq.
  move: hsdq; case Esd: (getm sd (flidx stL.2.1 arg.2)) => [md|] hsdq; last by [].
  eapply (r_fact (isSome (lsg stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
                            (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md))).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre hsd]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hsd hstoL.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ _ _ _ [_ hgrind _]].
      rewrite hsd in hgrind.
      move: hgrind; rewrite /sd_grindable => /allP hall.
      have hin : (flidx stL.2.1 arg.2) \in iota 0 (size (leaf_paths (tshape stL.2.1)))
        by rewrite mem_iota add0n; apply/andP; split; [exact: leq0n | exact: Hli].
      move: (hall (flidx stL.2.1 arg.2) hin); rewrite Esd /slot_grindable => hsg.
      rewrite (leaf_signE_c PP N D F Hgrind S_wn c_max)
              (lsign_panchor PP N D F Hgrind S_wn c_max h_sf Hh
                 stL.1.1 (spath stL.2.1 (flidx stL.2.1 arg.2))
                 (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md
                 (shrincs_fxmss_sign_path_pos_ok h_sf stL.2.1
                    (flidx stL.2.1 arg.2) Hli)) /shrincs_fxmss_wots_sign.
      by move: hsg; case: (find_ctr _ _ _ _ _ _ _ _ _). }
  move=> hls.
  ssprove_code_simpl. simpl.
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs.
  rewrite (shrincs_fxmss_sign_x_eq_redsign PP N D R F Tl Hgrind Htree S_wn c_max h_sf Hh n0
             lsg (leaf_signE_c PP N D F Hgrind S_wn c_max)
             stL.1.1 stL.2.1 stL.2.2 pkm (flidx stL.2.1 arg.2) r md Hli hpkm).
  rewrite !(index_sign_path h_sf stL.2.1 (flidx stL.2.1 arg.2) Hli).
  eapply r_get_remember_rhs => slogv.
  eapply r_bind_assertD_rhs.
    { move=> s0 s1 [hpre hslogv].
      destruct hpre as [s1a [hpre E1]]; subst s1.
      destruct hpre as [s0a [hpre E2]]; subst s0.
      destruct hpre as [s1b [hpre E3]]; subst s1a.
      destruct hpre as [s0b [hpre E4]]; subst s0a.
      destruct hpre as [s1c [hpre E5]]; subst s1b.
      destruct hpre as [s0c [hpre E6]]; subst s0b.
      destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
      rewrite /rem_lhs /rem_rhs /= in hstoL husL hslogv.
      rewrite !get_set_heap_neq // in hslogv.
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite hstoL husL hslogv in hR.
      case: hR => _ _ _ _ [_ _ [hsub hval] _ _].
      have hni := flidx_notin_image stL.2.1 us arg.2 hfok hfresh hval.
      exact: (contra (hsub (flidx stL.2.1 arg.2)) hni). }
  move=> _.
  eapply (r_get_bind_rhs mkm_tgts_loc (qmap_from 0 (leafcommitq_km stL.2.1 sd stL.2.2))).
    { move=> s0 s1 hpre.
      destruct hpre as [hpre hslogv].
      destruct hpre as [s1a [hpre E1]]; subst s1.
      destruct hpre as [s0a [hpre E2]]; subst s0.
      destruct hpre as [s1b [hpre E3]]; subst s1a.
      destruct hpre as [s0b [hpre E4]]; subst s0a.
      destruct hpre as [s1c [hpre E5]]; subst s1b.
      destruct hpre as [s0c [hpre E6]]; subst s0b.
      destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
      rewrite /rem_lhs /rem_rhs /= in hstoL hsdL.
      rewrite !get_set_heap_neq //.
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite hstoL in hR.
      case: hR => _ _ _ htg _.
      by rewrite htg hsdL. }
  rewrite (getm_leafcommitq_km_at stL.2.1 sd stL.2.2 (flidx stL.2.1 arg.2) Hli).
  rewrite Esd /=.
  eapply (r_get_bind_rhs Lpp (Some stL.1.1)).
    { move=> s0 s1 hpre.
      destruct hpre as [hpre hslogv].
      destruct hpre as [s1a [hpre E1]]; subst s1.
      destruct hpre as [s0a [hpre E2]]; subst s0.
      destruct hpre as [s1b [hpre E3]]; subst s1a.
      destruct hpre as [s0b [hpre E4]]; subst s0a.
      destruct hpre as [s1c [hpre E5]]; subst s1b.
      destruct hpre as [s0c [hpre E6]]; subst s0b.
      destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
      rewrite /rem_lhs /rem_rhs /= in hstoL.
      rewrite !get_set_heap_neq //.
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite hstoL in hR.
      by case: hR => _ hpo _ _ _; rewrite hpo. }
  simpl.
  move: hls; case: (lsg stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
                      (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md) => [ws|] hls; last by [].
  eapply r_put_rhs.
  simpl.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply r_put_lhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  split; first by [].
  destruct hpre as [s1a [hpre E1]]; subst s1.
  destruct hpre as [s0a [hpre E2]]; subst s0.
  destruct hpre as [s1b [hpre E3]]; subst s1a.
  destruct hpre as [s0b [hpre E4]]; subst s0a.
  destruct hpre as [s1c [hpre E5]]; subst s1b.
  destruct hpre as [hpre hslogv].
  destruct hpre as [s1d [hpre E6]]; subst s1c.
  destruct hpre as [s0c [hpre E7]]; subst s0b.
  destruct hpre as [s1e [hpre E8]]; subst s1d.
  destruct hpre as [s0d [hpre E9]]; subst s0c.
  destruct hpre as [s1f [hpre E10]]; subst s1e.
  destruct hpre as [s0e [hpre E11]]; subst s0d.
  destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
  move/lf_inv2_kmE: (hinv) => [hign hR].
  move/lf_inv2_km_tblogE: hinv => hT.
  rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL hsdL hslogv.
  rewrite !get_set_heap_neq // in hslogv.
  apply: lf_inv2_kmI.
  - apply: heap_ignore_set_both; apply: heap_ignore_set_both;
    (apply: heap_ignore_set_r; first by rewrite mem_domm /IGN2_km /IGN_km; fmap_solve);
    apply: heap_ignore_set_both; apply: heap_ignore_set_both; apply: heap_ignore_set_both;
    exact: hign.
  - get_heap_simpl.
    rewrite hstoL hstoR.
    revert hR; rewrite hstoL hstoR husL hslogv; intro hR.
    destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot [hsz hgrind hK]]].
    split; [ by [] | exact: hpo | exact: hrv | exact: htg |].
    split; [ exact: htw | exact: hpk | | exact: hroot | split; [exact: hsz|exact: hgrind|exact: hK] ].
    split;
    [ move=> x; rewrite mem_rcons in_cons => /orP[/eqP -> | hx];
      [ exact: flidx_in_image_setm
      | exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx)) ]
    | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ].
  - get_heap_simpl.
    rewrite hstoL.
    move=> k rr; rewrite setmE.
    case: eqP => [hk|hk].
    + by move=> _; rewrite hk /= mem_rcons in_cons eqxx.
    + by move=> /hAold hin; rewrite mem_rcons in_cons hin orbT.
- (* HASH *)
  rewrite /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_km_pre. } move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { lf_get2_km_pre. } move=> mp.
  case: (getm mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_km_pre. }
    ssprove_sync. { lf_put2_km_pre. }
    apply r_ret => s0 s1 hpre. split; first by []. exact: hpre. }
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_km_pre. }
  ssprove_sync. { lf_put2_km_pre. }
  apply r_ret => s0 s1 hpre. split; first by []. exact: hpre.
- (* FORGE *)
  destruct arg as [m sg].
  rewrite /forge_keep_body /forge_redL_km.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_km_pre. } move=> fc.
  ssprove_code_simpl. simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite -hr0 -hr1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  eapply (r_fact (stR = (stL.1, (stL.2.1, @dummy_xss N)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  ssprove_code_simpl. simpl.
  (* lg, tb, sd: REMEMBER (for clause A + the codomm side condition). *)
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lgr.
  eapply (r_fact (lg = lgr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hlgr].
      move: hpre => [hpre hlg].
      move: hpre => [hpre _].
      move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hlg hlgr.
      rewrite -hlg -hlgr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst lgr.
  ssprove_sync. { lf_getr_km. } move=> mp.
  eapply r_get_remember_lhs => tb.
  eapply r_get_remember_rhs => tbr.
  eapply (r_fact (tb = tbr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre htbr].
      move: hpre => [hpre htb].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in htb htbr.
      rewrite -htb -htbr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst tbr.
  eapply r_get_remember_lhs => sd.
  eapply r_get_remember_rhs => sdr.
  eapply (r_fact (sd = sdr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hsdr].
      move: hpre => [hpre hsd].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hsd hsdr.
      rewrite -hsd -hsdr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst sdr.
  eapply (r_fact (forall (k : ('nat × 'nat) × M) (rr : R),
                    getm tb k = Some rr -> k.2 \in lg)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre htb].
      move: hpre => [hpre _].
      move: hpre => [hpre hlg].
      move: hpre => [hpre _].
      move: hpre => [hinv hstoL].
      move/lf_inv2_km_tblogE: hinv => hT.
      rewrite /rem_lhs /= in htb hlg hstoL.
      rewrite hstoL htb hlg in hT.
      exact: hT. }
  move=> HtbA.
  eapply (r_fact (forall jj, (jj < n_max)%N ->
                    odflt d0 (getm sd jj) \in codomm sd)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _].
      move: hpre => [hpre hsd].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /= in hsd hstoL.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ _ _ _ [_ _ hK]].
      move=> jj hjj.
      move: (hK jj hjj); rewrite hsd.
      case Egsd: (getm sd jj) => [d|]; last by [].
      by move=> _; apply/codommP; exists jj; rewrite Egsd. }
  move=> Hcod.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1),
      (lf_inv2_km ⋊ rem_lhs Lst (Some stL)
         ⋊ rem_rhs Lst (Some (stL.1, (stL.2.1, @dummy_xss N)))
         ⋊ rem_lhs (shrincs_fxmss_sd_loc D) sd) (s0, s1)); last first.
    { move=> s0 s1 hpre.
      move: hpre => [hpre _].
      move: hpre => [hpre hsdl].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      move: hpre => [hpre _].
      by split; [exact: hpre | exact: hsdl]. }
  eapply r_get_remember_rhs => pkm.
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val PP N F Tl h_sf
                                         stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 [[[[hinv hstoL] hstoR] _] hpkmr].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ hpk _ _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  case Emd: (getm mp (sg.1.2, (stL.1, (sg.1.1, m)))) => [md|]; last first.
  { rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    eapply r_scheme_bind; first exact: prog_valid. move=> md.
    ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_km_pre. }
    ssprove_sync. { lf_put2_km_pre. }
    case: b; last first.
    { apply r_ret => s0 s1 hpre. split; first by [].
      by move: hpre => [[[[hinv _] _] _] _]; exact: hinv. }
    exact: (r_leaf_forge_verdict_kmS stL pkm lg tb sd m sg md hpkm HtbA Hcod). }
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_km_pre. }
  ssprove_sync. { lf_put2_km_pre. }
  case: b; last first.
  { apply r_ret => s0 s1 hpre. split; first by [].
    by move: hpre => [[[[hinv _] _] _] _]; exact: hinv. }
  exact: (r_leaf_forge_verdict_kmS stL pkm lg tb sd m sg md hpkm HtbA Hcod).
Qed.

Lemma R_leaf_kmS_ideal (b : bool) :
  perfect IG (G6 b) (R_leaf_km b ∘ MIW_kmS false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ lf_inv2_km).
{ rewrite /lf_inv2_km. ssprove_invariant.
  - by rewrite /rel_empty /RLf2_km.
  - by rewrite /rel_empty /R_tblog. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5_body /gen_redL_km.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (isSome sto = isSome sto')).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  rewrite code_link_assertD.
  eapply r_assertD; first by rewrite eIS.
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 eIS => [pk|] e0 eIS; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), lblk_km None false [::] emptym emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    rewrite /rem_lhs /= in hrem0.
    exact: (lfinv2_km_init s0 s1 hinv hrem0). }
  simpl.
  rewrite (resolve_lcq_kmS false (encode_adrs (gadrs (0, 0)))
             (inl (n0, n0) : (N × N) ∐ (D × 'nat))) /mkm_collq.
  eapply (r_get_bind_rhs Lpp None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (lblk_km_set_pp pp _ _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  (* RHS next is fillc; expose it as a scheme. *)
  rewrite code_link_bind
    (code_link_scheme _ _ _ _ (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  (* SWAP the LHS [skeys; fillc] -> [fillc; skeys]. *)
  apply: (r_swap_blocks (skeys (size (leaf_paths (tshape arg))))
            (fillc (iota 0 n_max) emptym)).
  (* couple fillc <-> fillc, obtaining the sd-totality fact *)
  apply: (r_fillc_dom _ (iota 0 n_max) emptym).
  move=> sd hsdtot _; cbv beta.
  (* couple skeys <-> lf_tree_km *)
  rewrite code_link_bind.
  eapply (lf_tree_kmS_spec false pp arg sd _ [::] (tshape arg) [::] emptym).
  + exact: (@gen_uniq w l N h_sf Hh arg).
  + exact: hcap.
  + by [].
  move=> xss hxsz hkeys.
  cbv beta.
  rewrite cat0s.
  rewrite code_link_bind.
  eapply (r_gcheck_kmS_spec false pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sd_grindable PP D Hgrind S_wn c_max h_sf pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  simpl.
  rewrite (resolve_lgp_kmS false Datatypes.tt) /mkm_getpp.
  eapply (r_get_bind_rhs Lpp (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (lblk_km_set_rev _ _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrv htws [htgts hpkm hus hscL [hslog htbE]].
  split;
    first by rewrite (tvalL_root PP N F Tl Htree h_sf Hh
                        (leaf_pk_c PP N F Tl) (leaf_pkE_c PP N F Tl)
                        pp arg xss hxsz).
  apply: lf_inv2_kmI.
  + apply: heap_ignore_set_both.
    apply: heap_ignore_set_l; first by rewrite mem_domm.
    apply: heap_ignore_set_r; first by rewrite mem_domm.
    exact: hign.
  + get_heap_simpl.
    rewrite hpp hrv htws htgts hpkm hus hscL hslog.
    rewrite (tvalL_root PP N F Tl Htree h_sf Hh
               (leaf_pk_c PP N F Tl) (leaf_pkE_c PP N F Tl) pp arg xss hxsz).
    rewrite unzip1_lf_commitsL_km (lf_commitsL_km_root arg sd xss hxsz).
    split; [ by [] | by [] | by [] | by [] |].
    split; [ by [] | | | by [] | ].
    * by move=> p hp;
        rewrite (getm_pkm_of PP N F Tl h_sf Hh (leaf_pk_c PP N F Tl)
                   (leaf_pkE_c PP N F Tl) pp arg xss hxsz p hp).
    * split; [ by move=> x; rewrite in_nil | by move=> zi; rewrite domm0 in_fset0 ].
    * split; [ exact: hcap | exact: e1 | ].
      by move=> jj hjj; apply: hsdtot; rewrite mem_iota add0n;
         apply/andP; split; [exact: leq0n | exact: hjj].
  + get_heap_simpl. rewrite htbE.
    by move=> k rr; rewrite emptymE.
- (* SIGN *)
  rewrite /sign5_body /sign_redL_km.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_km_pre. } move=> sc.
  ssprove_sync => hsc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hrem0 hrem1.
      rewrite -hrem0 -hrem1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  eapply (r_fact (stR = (stL.1, (stL.2.1, @dummy_xss N)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => usr.
  eapply (r_fact (us = usr)).
    { move=> s0 s1 [[[[hinv _] _] hrq] hrqr].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hrq hrqr.
      rewrite -hrq -hrqr.
      apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst usr.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lgr.
  eapply (r_fact (lg = lgr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hlgr]. move: hpre => [hpre hlg].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hlg hlgr.
      rewrite -hlg -hlgr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst lgr.
  ssprove_sync. { lf_getr_km. } move=> mp.
  eapply r_get_remember_lhs => tb.
  eapply r_get_remember_rhs => tbr.
  eapply (r_fact (tb = tbr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre htbr]. move: hpre => [hpre htb].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in htb htbr.
      rewrite -htb -htbr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst tbr.
  eapply (r_fact (forall (k : ('nat × 'nat) × M) (rr : R),
                    getm tb k = Some rr -> k.2 \in lg)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre htb].
      move: hpre => [hpre _]. move: hpre => [hpre hlg].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv hstoL].
      move/lf_inv2_km_tblogE: hinv => hT.
      rewrite /rem_lhs /= in htb hlg hstoL.
      rewrite hstoL htb hlg in hT.
      exact: hT. }
  move=> hAold.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1),
      (lf_inv2_km ⋊ rem_lhs Lst (Some stL)
         ⋊ rem_rhs Lst (Some (stL.1, (stL.2.1, @dummy_xss N)))
         ⋊ rem_lhs shrincs_fxmss_used_loc us ⋊ rem_rhs shrincs_fxmss_used_loc us) (s0, s1)); last first.
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      exact: hpre. }
  eapply r_get_remember_lhs => sd.
  eapply r_get_remember_rhs => sdr.
  eapply (r_fact (sd = sdr)).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hsdr]. move: hpre => [hpre hsd].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hinv _].
      move/lf_inv2_kmE: hinv => [hign _].
      rewrite /rem_lhs /rem_rhs /= in hsd hsdr.
      rewrite -hsd -hsdr; apply: hign; rewrite /IGN2_km /IGN_km; fmap_solve. }
  move=> ?; subst sdr.
  eapply r_get_remember_rhs => pkm.
  case Hg: (flok stL.2.1 arg.2 && (arg.2 \notin domm us)); last first.
  { eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    split; first by [].
    case: hpre => s1a [hpre ->].
    case: hpre => s0a [hpre ->].
    move: hpre => [hpre _]. move: hpre => [hpre _].
    move: hpre => [hpre _]. move: hpre => [hpre _].
    move: hpre => [hpre _]. move: hpre => [hpre hstoR].
    move: hpre => [hinv hstoL].
    move/lf_inv2_kmE: (hinv) => [hign hR].
    move/lf_inv2_km_tblogE: hinv => hT.
    rewrite /rem_lhs /rem_rhs /= in hstoL hstoR.
    rewrite hstoL in hR hT.
    case: hR => hsoR hpo hrv htg [htw hpk [hsub hval] hroot [hsz hgrind hK]].
    apply: lf_inv2_kmI.
    - by apply: heap_ignore_set_both.
    - get_heap_simpl.
      rewrite hstoL.
      split; [ exact: hsoR | exact: hpo | exact: hrv | exact: htg |].
      split; [ exact: htw | exact: hpk | split; [exact: hsub|exact: hval] | exact: hroot |].
      split; [ exact: hsz | exact: hgrind | exact: hK ].
    - by get_heap_simpl; rewrite hstoL; exact: hT. }
  move: Hg => /andP [hfok hfresh].
  have Hli := leafid_index_lt h_sf stL.2.1 arg.2 hfok.
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val PP N F Tl h_sf stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 hpre.
      move: hpre => [hpre hpkmr]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre hstoR].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ hpk _ _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  eapply (r_fact (isSome (getm sd (flidx stL.2.1 arg.2)))).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre hsd]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hsd hstoL.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ _ _ _ [hsz _ hK]].
      rewrite hsd in hK. apply: hK; exact: (leq_trans Hli hsz). }
  move=> hsdq.
  move: hsdq; case Esd: (getm sd (flidx stL.2.1 arg.2)) => [md|] hsdq; last by [].
  eapply (r_fact (isSome (lsg stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
                            (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md))).
    { move=> s0 s1 hpre.
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hpre hsd]. move: hpre => [hpre _].
      move: hpre => [hpre _]. move: hpre => [hpre _].
      move: hpre => [hinv hstoL].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hsd hstoL.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ _ _ _ [_ hgrind _]].
      rewrite hsd in hgrind.
      move: hgrind; rewrite /sd_grindable => /allP hall.
      have hin : (flidx stL.2.1 arg.2) \in iota 0 (size (leaf_paths (tshape stL.2.1)))
        by rewrite mem_iota add0n; apply/andP; split; [exact: leq0n | exact: Hli].
      move: (hall (flidx stL.2.1 arg.2) hin); rewrite Esd /slot_grindable => hsg.
      rewrite (leaf_signE_c PP N D F Hgrind S_wn c_max)
              (lsign_panchor PP N D F Hgrind S_wn c_max h_sf Hh
                 stL.1.1 (spath stL.2.1 (flidx stL.2.1 arg.2))
                 (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md
                 (shrincs_fxmss_sign_path_pos_ok h_sf stL.2.1
                    (flidx stL.2.1 arg.2) Hli)) /shrincs_fxmss_wots_sign.
      by move: hsg; case: (find_ctr _ _ _ _ _ _ _ _ _). }
  move=> hls.
  ssprove_code_simpl. simpl.
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs;
  eapply r_put_lhs; eapply r_put_rhs.
  rewrite (shrincs_fxmss_sign_x_eq_redsign PP N D R F Tl Hgrind Htree S_wn c_max h_sf Hh n0
             lsg (leaf_signE_c PP N D F Hgrind S_wn c_max)
             stL.1.1 stL.2.1 stL.2.2 pkm (flidx stL.2.1 arg.2) r md Hli hpkm).
  rewrite !(index_sign_path h_sf stL.2.1 (flidx stL.2.1 arg.2) Hli).
  eapply r_get_remember_rhs => slogv.
  eapply r_bind_assertD_rhs.
    { move=> s0 s1 [hpre hslogv].
      destruct hpre as [s1a [hpre E1]]; subst s1.
      destruct hpre as [s0a [hpre E2]]; subst s0.
      destruct hpre as [s1b [hpre E3]]; subst s1a.
      destruct hpre as [s0b [hpre E4]]; subst s0a.
      destruct hpre as [s1c [hpre E5]]; subst s1b.
      destruct hpre as [s0c [hpre E6]]; subst s0b.
      destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
      rewrite /rem_lhs /rem_rhs /= in hstoL husL hslogv.
      rewrite !get_set_heap_neq // in hslogv.
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite hstoL husL hslogv in hR.
      case: hR => _ _ _ _ [_ _ [hsub hval] _ _].
      have hni := flidx_notin_image stL.2.1 us arg.2 hfok hfresh hval.
      exact: (contra (hsub (flidx stL.2.1 arg.2)) hni). }
  move=> _.
  eapply (r_get_bind_rhs mkm_tgts_loc (qmap_from 0 (leafcommitq_km stL.2.1 sd stL.2.2))).
    { move=> s0 s1 hpre.
      destruct hpre as [hpre hslogv].
      destruct hpre as [s1a [hpre E1]]; subst s1.
      destruct hpre as [s0a [hpre E2]]; subst s0.
      destruct hpre as [s1b [hpre E3]]; subst s1a.
      destruct hpre as [s0b [hpre E4]]; subst s0a.
      destruct hpre as [s1c [hpre E5]]; subst s1b.
      destruct hpre as [s0c [hpre E6]]; subst s0b.
      destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
      rewrite /rem_lhs /rem_rhs /= in hstoL hsdL.
      rewrite !get_set_heap_neq //.
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite hstoL in hR.
      case: hR => _ _ _ htg _.
      by rewrite htg hsdL. }
  rewrite (getm_leafcommitq_km_at stL.2.1 sd stL.2.2 (flidx stL.2.1 arg.2) Hli).
  rewrite Esd /=.
  eapply (r_get_bind_rhs Lpp (Some stL.1.1)).
    { move=> s0 s1 hpre.
      destruct hpre as [hpre hslogv].
      destruct hpre as [s1a [hpre E1]]; subst s1.
      destruct hpre as [s0a [hpre E2]]; subst s0.
      destruct hpre as [s1b [hpre E3]]; subst s1a.
      destruct hpre as [s0b [hpre E4]]; subst s0a.
      destruct hpre as [s1c [hpre E5]]; subst s1b.
      destruct hpre as [s0c [hpre E6]]; subst s0b.
      destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
      rewrite /rem_lhs /rem_rhs /= in hstoL.
      rewrite !get_set_heap_neq //.
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite hstoL in hR.
      by case: hR => _ hpo _ _ _; rewrite hpo. }
  simpl.
  move: hls; case: (lsg stL.1.1 (panchor (spath stL.2.1 (flidx stL.2.1 arg.2)))
                      (nth [::] stL.2.2 (flidx stL.2.1 arg.2)) md) => [ws|] hls; last by [].
  eapply r_put_rhs.
  simpl.
  eapply r_put_lhs; eapply r_put_rhs.
  eapply r_put_lhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  split; first by [].
  destruct hpre as [s1a [hpre E1]]; subst s1.
  destruct hpre as [s0a [hpre E2]]; subst s0.
  destruct hpre as [s1b [hpre E3]]; subst s1a.
  destruct hpre as [s0b [hpre E4]]; subst s0a.
  destruct hpre as [s1c [hpre E5]]; subst s1b.
  destruct hpre as [hpre hslogv].
  destruct hpre as [s1d [hpre E6]]; subst s1c.
  destruct hpre as [s0c [hpre E7]]; subst s0b.
  destruct hpre as [s1e [hpre E8]]; subst s1d.
  destruct hpre as [s0d [hpre E9]]; subst s0c.
  destruct hpre as [s1f [hpre E10]]; subst s1e.
  destruct hpre as [s0e [hpre E11]]; subst s0d.
  destruct hpre as [[[[[[[hinv hstoL] hstoR] husL] husR] hsdL] hsdR] hpkmr].
  move/lf_inv2_kmE: (hinv) => [hign hR].
  move/lf_inv2_km_tblogE: hinv => hT.
  rewrite /rem_lhs /rem_rhs /= in hstoL hstoR husL hsdL hslogv.
  rewrite !get_set_heap_neq // in hslogv.
  apply: lf_inv2_kmI.
  - apply: heap_ignore_set_both; apply: heap_ignore_set_both;
    (apply: heap_ignore_set_r; first by rewrite mem_domm /IGN2_km /IGN_km; fmap_solve);
    apply: heap_ignore_set_both; apply: heap_ignore_set_both; apply: heap_ignore_set_both;
    exact: hign.
  - get_heap_simpl.
    rewrite hstoL hstoR.
    revert hR; rewrite hstoL hstoR husL hslogv; intro hR.
    destruct hR as [_ hpo hrv htg [htw hpk [hsub hval] hroot [hsz hgrind hK]]].
    split; [ by [] | exact: hpo | exact: hrv | exact: htg |].
    split; [ exact: htw | exact: hpk | | exact: hroot | split; [exact: hsz|exact: hgrind|exact: hK] ].
    split;
    [ move=> x; rewrite mem_rcons in_cons => /orP[/eqP -> | hx];
      [ exact: flidx_in_image_setm
      | exact: (image_subset_setm stL.2.1 us arg.2 _ (hsub x hx)) ]
    | exact: (used_valid_setm stL.2.1 us arg.2 hfok hval) ].
  - get_heap_simpl.
    rewrite hstoL.
    move=> k rr; rewrite setmE.
    case: eqP => [hk|hk].
    + by move=> _; rewrite hk /= mem_rcons in_cons eqxx.
    + by move=> /hAold hin; rewrite mem_rcons in_cons hin orbT.
- (* HASH *)
  rewrite /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_km_pre. } move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { lf_get2_km_pre. } move=> mp.
  case: (getm mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_km_pre. }
    ssprove_sync. { lf_put2_km_pre. }
    apply r_ret => s0 s1 hpre. split; first by []. exact: hpre. }
  rewrite ?(code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_km_pre. }
  ssprove_sync. { lf_put2_km_pre. }
  apply r_ret => s0 s1 hpre. split; first by []. exact: hpre.
- (* FORGE *)
  destruct arg as [m sg].
  rewrite /forge_keep_body /forge_redL_km.
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_get2_km_pre. } move=> fc.
  ssprove_code_simpl. simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => stoL.
  eapply r_get_remember_rhs => stoR.
  eapply (r_fact (isSome stoL = isSome stoR)).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite -hr0 -hr1.
      case E0: (get_heap s0 (shrincs_fxmss_st_loc PP N)) => [st|]; rewrite E0 in hR;
        by case: hR => hsoR _ _ _ _; rewrite hsoR. }
  move=> eIS.
  eapply r_assertD; first by move=> *; exact: eIS.
  move=> vSomeL vSomeR.
  case: stoL eIS vSomeL => [stL|] eIS vSomeL; last by [].
  case: stoR eIS vSomeR => [stR|] eIS vSomeR; last by [].
  rewrite !(getSomeE stL vSomeL) !(getSomeE stR vSomeR).
  eapply (r_fact (stR = (stL.1, (stL.2.1, @dummy_xss N)))).
    { move=> s0 s1 [[hinv hr0] hr1].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hr0 hr1.
      rewrite hr0 hr1 in hR.
      by case: hR => /Some_inj h _ _ _ _; exact: h. }
  move=> hstR; subst stR.
  cbn [fst snd].
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_getr_km. } move=> lg.
  ssprove_sync. { lf_getr_km. } move=> mp.
  ssprove_sync. { lf_getr_km. } move=> tb.
  ssprove_sync. { lf_getr_km. } move=> sd.
  eapply r_get_remember_rhs => pkm.
  eapply (r_fact (forall p, p \in leaf_paths (tshape stL.2.1) ->
                    getm pkm p = Some (anchor_val PP N F Tl h_sf
                                         stL.1.1 stL.2.1 stL.2.2 p))).
    { move=> s0 s1 [[[hinv hstoL] hstoR] hpkmr].
      move/lf_inv2_kmE: hinv => [_ hR].
      rewrite /rem_lhs /rem_rhs /= in hstoL hstoR hpkmr.
      rewrite hstoL in hR.
      case: hR => _ _ _ _ [_ hpk _ _ _].
      move=> p hp; rewrite -hpkmr; exact: (hpk p hp). }
  move=> hpkm.
  case Emd: (getm mp (sg.1.2, (stL.1, (sg.1.1, m)))) => [md|]; last first.
  { rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    eapply r_scheme_bind; first exact: prog_valid. move=> md.
    ssprove_code_simpl. simpl.
    ssprove_sync. { lf_put2_km_pre. }
    ssprove_sync. { lf_put2_km_pre. }
    case: b; last first.
    { apply r_ret => s0 s1 hpre. split; first by [].
      by move: hpre => [[[hinv _] _] _]; exact: hinv. }
    exact: (r_leaf_forge_verdict_km_ideal stL pkm lg tb sd m sg md hpkm). }
  ssprove_code_simpl. simpl.
  ssprove_sync. { lf_put2_km_pre. }
  ssprove_sync. { lf_put2_km_pre. }
  case: b; last first.
  { apply r_ret => s0 s1 hpre. split; first by [].
    by move: hpre => [[[hinv _] _] _]; exact: hinv. }
  exact: (r_leaf_forge_verdict_km_ideal stL pkm lg tb sd m sg md hpkm).
Qed.


Lemma Leaf_to_MIW_kmS (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G5 b) (G6 b) A = AdvOf MIW_kmS (A ∘ R_leaf_km b).
Proof.
rewrite (Adv_perfect_l (R_leaf_kmS_real b)) (Adv_perfect_r (R_leaf_kmS_ideal b)).
by rewrite Adv_reduction.
Qed.

End leaf_km.
