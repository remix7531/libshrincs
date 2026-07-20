(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.prf_hop

    Hops 1 and 2 of the FXMSS EU-CMA chain:

      hop 1 (tex F.1 -> F.2, claim:fxmss-prf):
        [R_prf_real  b : perfect I_G0f (G0f b)
                                 (R_prf b ∘ PRF_game Kf q_prf true)]
        [R_prf_ideal b : perfect I_G0f (G1f b)
                                 (R_prf b ∘ PRF_game Kf q_prf false)]
        [PRFf_hop b : Adv (G0f b) (G1f b) A
                      = AdvOf (PRF_game Kf q_prf) (A ∘ R_prf b)]
      hop 2 (PRFmsg; the tex absorbs it, F.0 -> F.1 note):
        [R_prfm_real / R_prfm_ideal / PRFmsg_hop] likewise between
        [G1f] and [G2f] against [PRF_game Kpm q_prfm].

    Budgets: [q_prf = (n_max * l).+1] (the GEN pin + one EVAL per
    chain of each anchor, anchor count capped by GEN's [n_max]
    assert); [q_prfm = q_s.+1] (the GEN pin + at most one EVAL per
    SIGN call — the per-call SIGN budget of G0f is what makes this
    finite, see Games.v header).

    ** THE PRF-SWAP RECIPE (first PRF hop of the development; P3a's
       reusable pattern for subsequent PRF swaps)

    To replace scheme-internal [PRF k ...] evaluations (key sampled
    in GEN) by fresh randomness:

    1. REDUCTION = the game with (a) the key sample REPLACED by one
       unconditional PIN call [EVAL pin_pt] at the same program
       point, where [pin_pt] is an input DISJOINT from every honest
       query point (here: an address of a different type tag for
       PRF_f; a leaf id above the tree height, [(h_sf.+1, 0)], for
       PRFmsg — the pin needs an inhabitant of the residual input
       space, whence the data parameter [m0 : M]); and (b) every
       scheme call site [PRF k x] replaced by [EVAL x] (sites that
       re-evaluate a previous input must either be served from own
       storage — G0f precomputes [xss] at GEN for exactly this
       reason — or repeat the EVAL, which table semantics also
       allows on the ideal side).
    2. REAL side is perfect: the pin's lazy key sample couples with
       the game's key sample (same program point, same sampler —
       no losslessness needed, THE point of the pin); afterwards
       EVAL is deterministic ([kh_eval]), and the invariant carries
       [prf_key = Some k] mirrored against the game's stored key.
    3. IDEAL side is perfect AGAINST THE GAME WHOSE RANDOMNESS IS
       (i) a lazily sampled table at the same query keys when
       inputs can repeat (PRFmsg: [G2f]'s [shrincs_fxmss_rt_loc]; the coupling
       invariant is POINTWISE map agreement off the pin point —
       [getm T p = getm t p] for honest [p] — which absorbs both
       the pin entry and re-stored hits with no existentials), or
       (ii) independent [sample_seq] draws when the query points
       are pairwise distinct (PRF_f: [G1f]'s [sample_keys]) — the
       LAZY-TABLE BRIDGE: the loop couplings [r_eval_chain_ideal] /
       [r_eval_anchors_ideal] below prove the n-fold
       "fresh-points lazy table = eager independent samples"
       statement by one induction carrying [uniq]ness of the
       remaining points and a domain-freshness transfer fact;
       promote to Toolkit/LazyTable.v in a session allowed to
       touch Toolkit/ (plan).
    4. The swapped game keeps a DEAD sample in the key slot
       ([_ ← dN] / [_ ← dR]) mirroring the pin's ideal-side lazy
       table entry — again the no-losslessness price (Games.v
       header).
    5. Bound: one [Adv_reduction] per hop;
       [Adv (G b) (G' b) A = AdvOf (PRF_game K q) (A ∘ R b)].

    ** Proof architecture

    Mirrored-oracle proofs (everything except the EVAL sites): get
    pairs remembered + [r_fact] against the one-[rel_app] invariant
    ([inv1]/[inv2r]/[inv2i], GrindHop pattern), asserts synced,
    then [rpre_weaken_rule] to an explicit block precondition (the
    [B*] families) and small-step rules through the branch; leaf
    put-chains restored manually ([inv*I] + [heap_ignore_set_*] +
    [get_heap_simpl]).  The reads-then-writes oracle normal form of
    Games.v is what keeps every oracle to ONE such pass.

    Locations: R_prf 440-447, R_prfm 460-466 (the PRF game's own
    are 31-33, HBS.games.PRF).

    FORGE budget: the games carry the [q_f] FORGE budget (counter
    [shrincs_fxmss_fcnt_loc] 408; Games.v header, ReproHop reconciliation) —
    the reductions mirror it ([rp_fcnt_loc] 447 / [rm_fcnt_loc] 466)
    and the invariants carry the counter equality, exactly like the
    other mirrored counters.

    Data parameter: [m0 : M] (the PRFmsg pin inhabitant; same
    flavor as shrincs_fxmss_wots_scheme's [n0]/[dM], discharged at instantiation where
    M is a bit-string type). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp.experimental_reals Require Import distr.
From HBS Require Import prelude math.bin_tree math.merkle sig.scheme
  games.thf games.prf toolkit.sample_seq.
From HBS Require Import wots.games wots.ud_hop
  wots.tcr_hop wots.pre_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(** Non-dependent corollary of [code_link_assertD]: the [#assert b ;;
    c] form hides the binder, and vanilla rewrite cannot match the
    higher-order [(λ _, c)] instance (ReproHop lesson; needed for the
    FORGE budget assert). *)
Lemma code_link_assert {A : choice_type} (b : bool) (c : raw_code A) p :
  code_link (#assert b ;; c) p = (#assert b ;; code_link c p).
Proof. exact: (code_link_assertD A b (λ _, c) p). Qed.

Section FXMSSPRFHop.

(** Same section context as fxmss.games, plus the pin inhabitant
    [m0] (header). *)
Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

Context (PP N D M R Ks Kp : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (PRFf : PP -> Ks -> adrs_sf -> N).
Context (PRFmsg : Kp -> nat * nat -> M -> R).
Context (dPP : dist PP) (dKs : dist Ks) (dKp : dist Kp).
Context (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (m0 : M).
Context (Hh : (h_sf <= 64)%N).

(* ------------------------------------------------------------------ *)
(** ** Shorthands *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation enc := (@encode_adrs l w).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation KF := (Kf PP N Ks PRFf dKs dN).
Local Notation KM := (Kpm M R Kp PRFmsg dKp dR).
Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).
(** M5 lift: the leaf-id validator and slot selector (Games.v). *)
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).
Local Notation fxsignx := (shrincs_fxmss_sign_x PP N D R F Tl Hgrind Htree S_wn c_max h_sf).
Local Notation fxvermd := (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation fleaf_sks := (leaf_sks PP N Ks PRFf h_sf).
Local Notation fleaf_sk := (shrincs_fxmss_leaf_secret PP N Ks PRFf).
Local Notation skeys := (@sample_keys l N dN).
Local Notation G0F b :=
  (G0f PP N D M R Ks Kp F Tl Hgrind Htree PRFf PRFmsg dPP dKs dKp dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G1F b :=
  (G1f PP N D M R Kp F Tl Hgrind Htree PRFmsg dPP dKp dN dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G2F b :=
  (G2f PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).

Local Notation Lst := (shrincs_fxmss_st_loc PP N).
Local Notation Lkp := (shrincs_fxmss_kp_loc Kp).
Local Notation Llog := (shrincs_fxmss_log_loc M).
Local Notation Lrom := (shrincs_fxmss_rom_loc PP N D M R).
Local Notation Lrt := (shrincs_fxmss_rt_loc M R).

(** Budgets (header). *)
Definition q_prf : nat := (n_max * l).+1.
Definition q_prfm : nat := q_s.+1.

Local Notation PGF b := (PRF_game KF q_prf b).
Local Notation PGM b := (PRF_game KM q_prfm b).

(* ------------------------------------------------------------------ *)
(** ** Pure facts about the query points *)

(** Leaf identifiers of honest signing queries stay at height
    <= h_sf; the PRFmsg pin lives at h_sf.+1. *)
Lemma posid_le (p : seq bool) : ((posid p).1 <= h_sf)%N.
Proof. by rewrite /shrincs_fxmss_pos_id /= leq_subr. Qed.

(** The pin's table entry is invisible at honest (low) keys. *)
Lemma setm_pin_low (T : {fmap kh_M KM -> kh_N KM}) (r0 : R)
    (pt : (nat * nat) * M) :
  (pt.1.1 <= h_sf)%N ->
  getm (setm T ((h_sf.+1, 0), m0) r0) pt = getm T pt.
Proof.
move=> h; rewrite setmE; case: eqP => // e.
by move: h; rewrite e /= ltnn.
Qed.

(** The PRF_f pin (a GRIND-type address) differs from every honest
    PRF_f query point (PRF-type addresses). *)
Lemma pin_pt_neqf (pp pp' : PP) (zi : nat * nat) (j : nat) :
  (((pp, enc (shrincs_fxmss_wots_prf_adrs zi j))
     == (pp', enc (shrincs_fxmss_wots_grind_adrs (0, 0))))%B) = false.
Proof.
apply/eqP => e.
move/encode_adrs_inj: (congr1 snd e).
rewrite /shrincs_fxmss_wots_prf_adrs.
case: Stdlib.ZArith.ZArith_dec.Z_lt_dec => Hcount; by [].
Qed.

(** Honest PRF_f query points are pairwise distinct (the
    distinct-inputs side of the lazy-table bridge). *)
Lemma prf_pt_inj (pp : PP) (p p' : seq bool) (j j' : nat) :
  size p <= h_sf -> size p' <= h_sf -> j < l -> j' < l ->
  (pp, enc (shrincs_fxmss_wots_prf_adrs (posid p) j))
    = (pp, enc (shrincs_fxmss_wots_prf_adrs (posid p') j')) ->
  p = p' /\ j = j'.
Proof.
move=> hp hp' hj hj' epp.
move/encode_adrs_inj: (congr1 snd epp) => he.
have [e1 e2 e3] := @shrincs_fxmss_wots_prf_adrs_inj l w
  (posid p).1 (posid p).2 j (posid p').1 (posid p').2 j'
  (shrincs_fxmss_pos_id_bounded h_sf p Hh hp) (shrincs_fxmss_pos_id_bounded h_sf p' Hh hp')
  (component_bounded_lt l j hj) (component_bounded_lt l j' hj') he.
have e : posid p = posid p'.
  by rewrite (surjective_pairing (posid p)) (surjective_pairing (posid p'))
       e1 e2.
by split=> //; exact: shrincs_fxmss_pos_id_inj e.
Qed.

(** Every leaf path of a normalized shape fits the declared
    height. *)
Lemma leaf_paths_depth (sp : seq bool) :
  all (fun p => size p <= h_sf) (leaf_paths (tshape sp)).
Proof.
apply/allP => p hp.
have hsub := leaf_paths_subtree hp.
have hleaf : leaf_at (tshape sp) p = Some tt by rewrite /leaf_at hsub.
exact: leq_trans (leaf_at_size hleaf) (shrincs_fxmss_shape_wf h_sf sp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The reductions *)

Definition rp_st_loc := mkloc 440 (None : option (shrincs_fxmss_game_state PP N)).
Definition rp_kp_loc := mkloc 441 (None : option Kp).
Definition rp_used_loc := mkloc 442 (emptym : chMap ('nat × 'nat) 'unit).
Definition rp_scnt_loc := mkloc 443 (0 : 'nat).
Definition rp_log_loc := mkloc 444 ([::] : seq M).
Definition rp_rom_loc := mkloc 445 (emptym : chMap ROIN D).
Definition rp_hcnt_loc := mkloc 446 (0 : 'nat).
Definition rp_fcnt_loc := mkloc 447 (0 : 'nat).

Definition rm_st_loc := mkloc 460 (None : option (shrincs_fxmss_game_state PP N)).
Definition rm_used_loc := mkloc 461 (emptym : chMap ('nat × 'nat) 'unit).
Definition rm_scnt_loc := mkloc 462 (0 : 'nat).
Definition rm_log_loc := mkloc 463 ([::] : seq M).
Definition rm_rom_loc := mkloc 464 (emptym : chMap ROIN D).
Definition rm_hcnt_loc := mkloc 465 (0 : 'nat).
Definition rm_fcnt_loc := mkloc 466 (0 : 'nat).

(** The PRF_f evaluation loops: one EVAL per chain index of one
    anchor ([eval_chain]), iterated over the anchors
    ([eval_anchors]). *)
Fixpoint eval_chain (pp : PP) (zi : nat * nat) (js : seq nat) :
    raw_code (chList N) :=
  match js with
  | [::] => ret [::]
  | j :: js' =>
      x ← (call [ EVAL ] : { (PP × adrs_sf_ch) ~> N }
             (pp, enc (shrincs_fxmss_wots_prf_adrs zi j))) ;;
      xs ← eval_chain pp zi js' ;;
      ret (x :: xs)
  end.

#[export] Instance eval_chain_valid (L : Locations) (pp : PP)
    (zi : nat * nat) (js : seq nat) :
  ValidCode L (I_PRF KF) (eval_chain pp zi js).
Proof.
elim: js => [|j js IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> x; eapply valid_bind; [exact: IH|].
  move=> xs; apply valid_ret.
Qed.

Fixpoint eval_anchors (pp : PP) (ps : seq (seq bool)) :
    raw_code (chList (chList N)) :=
  match ps with
  | [::] => ret [::]
  | p :: ps' =>
      xs ← eval_chain pp (posid p) (iota 0 l) ;;
      xss ← eval_anchors pp ps' ;;
      ret (xs :: xss)
  end.

#[export] Instance eval_anchors_valid (L : Locations) (pp : PP)
    (ps : seq (seq bool)) :
  ValidCode L (I_PRF KF) (eval_anchors pp ps).
Proof.
elim: ps => [|p ps IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: eval_chain_valid.
  move=> xs; eapply valid_bind; [exact: IH|].
  move=> xss; apply valid_ret.
Qed.

(** M5: the two reductions are assembled by the DIRECTED
    [valid_package_cons] idiom (like the games in Games.v): the lifted
    used-set SIGN body defeats the plain [package] TC search.  Each
    oracle body is a named definition with a hand-proved [ValidCode]
    instance. *)

Definition Rp_locs : Locations :=
  [fmap rp_st_loc ; rp_kp_loc ; rp_used_loc ; rp_scnt_loc ;
        rp_log_loc ; rp_rom_loc ; rp_hcnt_loc ; rp_fcnt_loc ].

Definition Rm_locs : Locations :=
  [fmap rm_st_loc ; rm_used_loc ; rm_scnt_loc ;
        rm_log_loc ; rm_rom_loc ; rm_hcnt_loc ; rm_fcnt_loc ].

(* ---- R_prf (hop 1) oracle bodies ---- *)

Definition rp_gen_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get rp_st_loc ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← (call [ EVAL ] : { (PP × adrs_sf_ch) ~> N }
          (pp, enc (shrincs_fxmss_wots_grind_adrs (0, 0)))) ;;
   kp ← dKp ;;
   xss ← eval_anchors pp (leaf_paths (tshape sp)) ;;
   #put rp_kp_loc := Some kp ;;
   #put rp_st_loc := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   ret (pp, fxroot pp sp xss)).

Definition rp_sign_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get rp_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome rp_st_loc ;;
   kp ← getSome rp_kp_loc ;;
   us ← get rp_used_loc ;;
   lg ← get rp_log_loc ;;
   mp ← get rp_rom_loc ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     md ← (match getm mp (PRFmsg kp mz.2 mz.1, (st.1, (mz.2, mz.1))) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put rp_used_loc := setm us mz.2 Datatypes.tt ;;
     #put rp_rom_loc :=
       setm mp (PRFmsg kp mz.2 mz.1, (st.1, (mz.2, mz.1))) md ;;
     match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2)
             (PRFmsg kp mz.2 mz.1) md with
     | Some sg =>
         #put rp_log_loc := rcons lg mz.1 ;;
         #put rp_scnt_loc := sc.+1 ;;
         ret (Some sg)
     | None =>
         #put rp_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put rp_scnt_loc := sc.+1 ;;
     ret None).

Definition rp_hash_body (x : ROIN) : raw_code D :=
  (hc ← get rp_hcnt_loc ;;
   #assert (hc < q_h)%N ;;
   mp ← get rp_rom_loc ;;
   md ← (match getm mp x with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put rp_rom_loc := setm mp x md ;;
   #put rp_hcnt_loc := hc.+1 ;;
   ret md).

Definition rp_forge_body (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get rp_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome rp_st_loc ;;
   lg ← get rp_log_loc ;;
   mp ← get rp_rom_loc ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put rp_rom_loc := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put rp_fcnt_loc := fc.+1 ;;
   ret (if b then
          fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
          && (m \notin lg)
        else false)).

#[export] Instance rp_gen_body_valid (sp : 'list 'bool) :
  ValidCode Rp_locs (I_PRF KF) (rp_gen_body sp).
Proof.
rewrite /rp_gen_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_opr; first by fmap_solve. move=> x0.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> kp.
eapply valid_bind; first by apply eval_anchors_valid. move=> xss.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rp_sign_body_valid (mz : M × ('nat × 'nat)) :
  ValidCode Rp_locs (I_PRF KF) (rp_sign_body mz).
Proof.
rewrite /rp_sign_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> kpo.
eapply valid_assertD => hKp.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: (fxsignx _ _ _ _ _ _) => [sg|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  apply valid_ret.
- eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance rp_hash_body_valid (x : ROIN) :
  ValidCode Rp_locs (I_PRF KF) (rp_hash_body x).
Proof.
rewrite /rp_hash_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rp_forge_body_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode Rp_locs (I_PRF KF) (rp_forge_body b m sg).
Proof.
rewrite /rp_forge_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

(** THE PRF_f reduction (hop 1): GEN pins the key sample with one
    EVAL at a GRIND-type address (never queried honestly), then
    derives all per-anchor chain-start lists through EVAL;
    SIGN/HASH/FORGE are the lifted G0f/G1f bodies over the stored
    list (no further EVALs). *)
Definition R_prf (b : bool) : package (I_PRF KF) IG.
Proof.
notypeclasses refine [package Rp_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { rp_gen_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      rp_sign_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { rp_hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { rp_forge_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: rp_forge_body_valid. } }
    { intros x; exact: rp_hash_body_valid. } }
  { intro mz; exact: rp_sign_body_valid. } }
{ intro sp; exact: rp_gen_body_valid. }
Defined.

(* ---- R_prfm (hop 2) oracle bodies ---- *)

Definition rm_gen_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get rm_st_loc ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← (call [ EVAL ] : { (('nat × 'nat) × M) ~> R }
          ((h_sf.+1, 0), m0)) ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   #put rm_st_loc := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   ret (pp, fxroot pp sp xss)).

Definition rm_sign_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get rm_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome rm_st_loc ;;
   us ← get rm_used_loc ;;
   lg ← get rm_log_loc ;;
   mp ← get rm_rom_loc ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     r ← (call [ EVAL ] : { (('nat × 'nat) × M) ~> R } (mz.2, mz.1)) ;;
     md ← (match getm mp (r, (st.1, (mz.2, mz.1))) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put rm_used_loc := setm us mz.2 Datatypes.tt ;;
     #put rm_rom_loc := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
     match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
     | Some sg =>
         #put rm_log_loc := rcons lg mz.1 ;;
         #put rm_scnt_loc := sc.+1 ;;
         ret (Some sg)
     | None =>
         #put rm_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put rm_scnt_loc := sc.+1 ;;
     ret None).

Definition rm_hash_body (x : ROIN) : raw_code D :=
  (hc ← get rm_hcnt_loc ;;
   #assert (hc < q_h)%N ;;
   mp ← get rm_rom_loc ;;
   md ← (match getm mp x with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put rm_rom_loc := setm mp x md ;;
   #put rm_hcnt_loc := hc.+1 ;;
   ret md).

Definition rm_forge_body (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get rm_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome rm_st_loc ;;
   lg ← get rm_log_loc ;;
   mp ← get rm_rom_loc ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put rm_rom_loc := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put rm_fcnt_loc := fc.+1 ;;
   ret (if b then
          fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
          && (m \notin lg)
        else false)).

#[export] Instance rm_gen_body_valid (sp : 'list 'bool) :
  ValidCode Rm_locs (I_PRF KM) (rm_gen_body sp).
Proof.
rewrite /rm_gen_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> x0.
eapply valid_opr; first by fmap_solve. move=> x1.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rm_sign_body_valid (mz : M × ('nat × 'nat)) :
  ValidCode Rm_locs (I_PRF KM) (rm_sign_body mz).
Proof.
rewrite /rm_sign_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_opr; first by fmap_solve. move=> r.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: (fxsignx _ _ _ _ _ _) => [sg|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  apply valid_ret.
- eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance rm_hash_body_valid (x : ROIN) :
  ValidCode Rm_locs (I_PRF KM) (rm_hash_body x).
Proof.
rewrite /rm_hash_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rm_forge_body_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode Rm_locs (I_PRF KM) (rm_forge_body b m sg).
Proof.
rewrite /rm_forge_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

(** THE PRFmsg reduction (hop 2): GEN pins the key sample with one
    EVAL at the leaf id (h_sf.+1, 0) (above every honest leaf);
    SIGN derives the signature randomness through EVAL at the
    adversary-chosen id (at most one per call); HASH/FORGE lifted. *)
Definition R_prfm (b : bool) : package (I_PRF KM) IG.
Proof.
notypeclasses refine [package Rm_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { rm_gen_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      rm_sign_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { rm_hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { rm_forge_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: rm_forge_body_valid. } }
    { intros x; exact: rm_hash_body_valid. } }
  { intro mz; exact: rm_sign_body_valid. } }
{ intro sp; exact: rm_gen_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Resolved EVAL bodies (computed once; GrindHop pattern) *)

Definition evfo : opsig := (EVAL, (PP × adrs_sf_ch, N)).
Definition evmo : opsig := (EVAL, (('nat × 'nat) × M, R)).

Lemma resolve_evf_t (x : PP × adrs_sf_ch) :
  resolve (PGF true) evfo x =
  (cnt ← get prf_cnt_loc ;;
   #assert (cnt < q_prf)%N ;;
   #put prf_cnt_loc := cnt.+1 ;;
   ko ← get (prf_key_loc KF) ;;
   match ko with
   | Some k => ret (kh_eval KF k x)
   | None =>
       k ← kh_dK KF ;;
       #put (prf_key_loc KF) := Some k ;;
       ret (kh_eval KF k x)
   end).
Proof. simplify_linking. reflexivity. Qed.

Lemma resolve_evf_f (x : PP × adrs_sf_ch) :
  resolve (PGF false) evfo x =
  (cnt ← get prf_cnt_loc ;;
   #assert (cnt < q_prf)%N ;;
   #put prf_cnt_loc := cnt.+1 ;;
   t ← get (prf_tab_loc KF) ;;
   match getm t x with
   | Some y => ret y
   | None =>
       y ← kh_dN KF ;;
       #put (prf_tab_loc KF) := setm t x y ;;
       ret y
   end).
Proof. simplify_linking. reflexivity. Qed.

Lemma resolve_evm_t (x : ('nat × 'nat) × M) :
  resolve (PGM true) evmo x =
  (cnt ← get prf_cnt_loc ;;
   #assert (cnt < q_prfm)%N ;;
   #put prf_cnt_loc := cnt.+1 ;;
   ko ← get (prf_key_loc KM) ;;
   match ko with
   | Some k => ret (kh_eval KM k x)
   | None =>
       k ← kh_dK KM ;;
       #put (prf_key_loc KM) := Some k ;;
       ret (kh_eval KM k x)
   end).
Proof. simplify_linking. reflexivity. Qed.

Lemma resolve_evm_f (x : ('nat × 'nat) × M) :
  resolve (PGM false) evmo x =
  (cnt ← get prf_cnt_loc ;;
   #assert (cnt < q_prfm)%N ;;
   #put prf_cnt_loc := cnt.+1 ;;
   t ← get (prf_tab_loc KM) ;;
   match getm t x with
   | Some y => ret y
   | None =>
       y ← kh_dN KM ;;
       #put (prf_tab_loc KM) := setm t x y ;;
       ret y
   end).
Proof. simplify_linking. reflexivity. Qed.

(* Keep the packages and the pure layer folded under [simpl] from
   here on. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments PRF_game : simpl never.
#[local] Arguments shrincs_fxmss_sign_x : simpl never.
#[local] Arguments shrincs_fxmss_verify_md : simpl never.
#[local] Arguments shrincs_fxmss_root_x : simpl never.
#[local] Arguments leaf_sks : simpl never.
#[local] Arguments shrincs_fxmss_shape : simpl never.
#[local] Arguments shrincs_fxmss_sign_path : simpl never.
#[local] Arguments shrincs_fxmss_pos_id : simpl never.
#[local] Arguments leaf_paths : simpl never.
#[local] Arguments encode_adrs : simpl never.
#[local] Arguments setm : simpl never.
#[local] Arguments getm : simpl never.
#[local] Arguments emptym : simpl never.

(* ================================================================== *)
(** ** Hop 2: the PRFmsg swap (G1f -> G2f) *)

(* ------------------------------------------------------------------ *)
(** ** Invariants *)

Definition L2r : Locations :=
  [fmap Lst ; Lkp ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ; shrincs_fxmss_hcnt_loc ;
        shrincs_fxmss_fcnt_loc ;
        rm_st_loc ; rm_used_loc ; rm_scnt_loc ; rm_log_loc ; rm_rom_loc ;
        rm_hcnt_loc ; rm_fcnt_loc ;
        prf_key_loc KM ; prf_tab_loc KM ; prf_cnt_loc ].

Definition L2i : Locations :=
  [fmap Lst ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ; shrincs_fxmss_hcnt_loc ; Lrt ;
        shrincs_fxmss_fcnt_loc ;
        rm_st_loc ; rm_used_loc ; rm_scnt_loc ; rm_log_loc ; rm_rom_loc ;
        rm_hcnt_loc ; rm_fcnt_loc ;
        prf_key_loc KM ; prf_tab_loc KM ; prf_cnt_loc ].

(** Real side: rhs PRF key mirrors the lhs stored kp; the EVAL
    budget counter is bounded by the SIGN budget counter (+1 for
    the pin). *)
Definition R2r (sto : option (shrincs_fxmss_game_state PP N)) (kpo : option Kp)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (rm : {fmap ROIN -> D}) (hc : nat)
    (sto' : option (shrincs_fxmss_game_state PP N)) (usv' : chMap ('nat × 'nat) 'unit) (sc' : nat)
    (lg' : seq M) (rm' : {fmap ROIN -> D}) (hc' : nat)
    (ko : option Kp) (cnt : nat) (fc fc' : nat) : Prop :=
  [/\ [/\ sto' = sto, usv' = usv, sc' = sc, lg' = lg & rm' = rm],
      [/\ hc' = hc, ko = kpo & isSome kpo = isSome sto],
      [/\ (cnt <= sc.+1)%N & (sto = None -> cnt = 0)]
    & fc' = fc].

Definition inv2r : precond :=
  heap_ignore L2r
  ⋊ rel_app [:: (lhs, Lst) ; (lhs, Lkp) ; (lhs, shrincs_fxmss_used_loc) ;
                (lhs, shrincs_fxmss_scnt_loc) ; (lhs, Llog) ; (lhs, Lrom) ;
                (lhs, shrincs_fxmss_hcnt_loc) ;
                (rhs, rm_st_loc) ; (rhs, rm_used_loc) ; (rhs, rm_scnt_loc) ;
                (rhs, rm_log_loc) ; (rhs, rm_rom_loc) ; (rhs, rm_hcnt_loc) ;
                (rhs, prf_key_loc KM) ; (rhs, prf_cnt_loc) ;
                (lhs, shrincs_fxmss_fcnt_loc) ; (rhs, rm_fcnt_loc) ] R2r.

Arguments inv2r : simpl never.

Lemma inv2rE s0 s1 :
  inv2r (s0, s1) ->
  heap_ignore L2r (s0, s1) /\
  R2r (get_heap s0 Lst) (get_heap s0 Lkp) (get_heap s0 shrincs_fxmss_used_loc)
      (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 Llog) (get_heap s0 Lrom)
      (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s1 rm_st_loc) (get_heap s1 rm_used_loc)
      (get_heap s1 rm_scnt_loc) (get_heap s1 rm_log_loc)
      (get_heap s1 rm_rom_loc) (get_heap s1 rm_hcnt_loc)
      (get_heap s1 (prf_key_loc KM)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rm_fcnt_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma inv2rI s0 s1 :
  heap_ignore L2r (s0, s1) ->
  R2r (get_heap s0 Lst) (get_heap s0 Lkp) (get_heap s0 shrincs_fxmss_used_loc)
      (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 Llog) (get_heap s0 Lrom)
      (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s1 rm_st_loc) (get_heap s1 rm_used_loc)
      (get_heap s1 rm_scnt_loc) (get_heap s1 rm_log_loc)
      (get_heap s1 rm_rom_loc) (get_heap s1 rm_hcnt_loc)
      (get_heap s1 (prf_key_loc KM)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rm_fcnt_loc) ->
  inv2r (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** Ideal side: the rhs PRF table agrees with the lhs randomness
    table at every honest (low) key — the pointwise reading of "the
    table plus the pin entry" (header). *)
Definition R2i (sto : option (shrincs_fxmss_game_state PP N))
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (rm : {fmap ROIN -> D}) (hc : nat)
    (tb : {fmap kh_M KM -> kh_N KM})
    (sto' : option (shrincs_fxmss_game_state PP N)) (usv' : chMap ('nat × 'nat) 'unit) (sc' : nat)
    (lg' : seq M) (rm' : {fmap ROIN -> D}) (hc' : nat)
    (T : {fmap kh_M KM -> kh_N KM}) (cnt : nat) (fc fc' : nat) : Prop :=
  [/\ [/\ sto' = sto, usv' = usv, sc' = sc, lg' = lg & rm' = rm],
      [/\ hc' = hc
        & forall pt : (nat * nat) * M,
            (pt.1.1 <= h_sf)%N -> getm T pt = getm tb pt],
      [/\ (cnt <= sc.+1)%N
        & (sto = None -> T = emptym /\ cnt = 0)]
    & fc' = fc].

Definition inv2i : precond :=
  heap_ignore L2i
  ⋊ rel_app [:: (lhs, Lst) ; (lhs, shrincs_fxmss_used_loc) ; (lhs, shrincs_fxmss_scnt_loc) ;
                (lhs, Llog) ; (lhs, Lrom) ; (lhs, shrincs_fxmss_hcnt_loc) ;
                (lhs, Lrt) ;
                (rhs, rm_st_loc) ; (rhs, rm_used_loc) ; (rhs, rm_scnt_loc) ;
                (rhs, rm_log_loc) ; (rhs, rm_rom_loc) ; (rhs, rm_hcnt_loc) ;
                (rhs, prf_tab_loc KM) ; (rhs, prf_cnt_loc) ;
                (lhs, shrincs_fxmss_fcnt_loc) ; (rhs, rm_fcnt_loc) ] R2i.

Arguments inv2i : simpl never.

Lemma inv2iE s0 s1 :
  inv2i (s0, s1) ->
  heap_ignore L2i (s0, s1) /\
  R2i (get_heap s0 Lst) (get_heap s0 shrincs_fxmss_used_loc) (get_heap s0 shrincs_fxmss_scnt_loc)
      (get_heap s0 Llog) (get_heap s0 Lrom) (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s0 Lrt)
      (get_heap s1 rm_st_loc) (get_heap s1 rm_used_loc)
      (get_heap s1 rm_scnt_loc) (get_heap s1 rm_log_loc)
      (get_heap s1 rm_rom_loc) (get_heap s1 rm_hcnt_loc)
      (get_heap s1 (prf_tab_loc KM)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rm_fcnt_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma inv2iI s0 s1 :
  heap_ignore L2i (s0, s1) ->
  R2i (get_heap s0 Lst) (get_heap s0 shrincs_fxmss_used_loc) (get_heap s0 shrincs_fxmss_scnt_loc)
      (get_heap s0 Llog) (get_heap s0 Lrom) (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s0 Lrt)
      (get_heap s1 rm_st_loc) (get_heap s1 rm_used_loc)
      (get_heap s1 rm_scnt_loc) (get_heap s1 rm_log_loc)
      (get_heap s1 rm_rom_loc) (get_heap s1 rm_hcnt_loc)
      (get_heap s1 (prf_tab_loc KM)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rm_fcnt_loc) ->
  inv2i (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** Block preconditions (hop 2)

    Explicit Prop preconditions for the segments after the
    get/assert preamble of each oracle (the invariant machinery is
    dropped by [rpre_weaken_rule]; the leaves restore [inv2r]/[inv2i]
    manually).  Naming: G/S/H/F for the oracle, 2r/2i for the hop
    side. *)

(** GEN (hop 2, both sides): values of the not-yet-written mirrored
    locations agree; the PRF key/cnt (real) resp. tab/cnt (ideal)
    hold the given values. *)
Definition G2r (ko : option Kp) (c : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2r (s0, s1),
          get_heap s1 rm_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rm_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc,
          get_heap s1 rm_log_loc = get_heap s0 Llog &
          get_heap s1 rm_rom_loc = get_heap s0 Lrom],
      [/\ get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc
        & get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      get_heap s1 (prf_key_loc KM) = ko
    & get_heap s1 prf_cnt_loc = c].

Arguments G2r : simpl never.

Definition G2i (T : {fmap kh_M KM -> kh_N KM}) (c : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2i (s0, s1),
          get_heap s1 rm_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rm_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc,
          get_heap s1 rm_log_loc = get_heap s0 Llog &
          get_heap s1 rm_rom_loc = get_heap s0 Lrom],
      [/\ get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc,
          (forall pt : (nat * nat) * M,
            (pt.1.1 <= h_sf)%N -> getm T pt = getm (get_heap s0 Lrt) pt)
        & get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      get_heap s1 (prf_tab_loc KM) = T
    & get_heap s1 prf_cnt_loc = c].

Arguments G2i : simpl never.

(** SIGN (hop 2 real): everything read is pinned on both sides; the
    PRF counter is bounded by [cb]. *)
Definition S2r (stv : shrincs_fxmss_game_state PP N) (kpv : Kp)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) (cb : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2r (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rm_st_loc = Some stv,
          get_heap s0 Lkp = Some kpv &
          get_heap s1 (prf_key_loc KM) = Some kpv],
      [/\ get_heap s0 shrincs_fxmss_used_loc = usv,
          get_heap s1 rm_used_loc = usv,
          get_heap s0 shrincs_fxmss_scnt_loc = sc,
          get_heap s1 rm_scnt_loc = sc &
          get_heap s0 Llog = lg],
      [/\ get_heap s1 rm_log_loc = lg,
          get_heap s0 Lrom = mp &
          get_heap s1 rm_rom_loc = mp]
    & [/\ get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc,
          get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc
        & (get_heap s1 prf_cnt_loc <= cb)%N]].

Arguments S2r : simpl never.

(** SIGN (hop 2 ideal): the lhs randomness table is pinned (it was
    read); the rhs PRF table is related to it pointwise at low
    keys. *)
Definition S2i (stv : shrincs_fxmss_game_state PP N)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) (tb : {fmap kh_M KM -> kh_N KM})
    (cb : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2i (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rm_st_loc = Some stv,
          get_heap s0 Lrt = tb &
          (forall pt : (nat * nat) * M,
              (pt.1.1 <= h_sf)%N ->
              getm (get_heap s1 (prf_tab_loc KM)) pt = getm tb pt)],
      [/\ get_heap s0 shrincs_fxmss_used_loc = usv,
          get_heap s1 rm_used_loc = usv,
          get_heap s0 shrincs_fxmss_scnt_loc = sc,
          get_heap s1 rm_scnt_loc = sc &
          get_heap s0 Llog = lg],
      [/\ get_heap s1 rm_log_loc = lg,
          get_heap s0 Lrom = mp &
          get_heap s1 rm_rom_loc = mp]
    & [/\ get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc,
          get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc
        & (get_heap s1 prf_cnt_loc <= cb)%N]].

Arguments S2i : simpl never.

(** HASH (hop 2): only the RO map and the budget counter are read;
    the residual invariant facts are carried as heap relations. *)
Definition H2r (hcv : nat) (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2r (s0, s1),
          get_heap s1 rm_st_loc = get_heap s0 Lst,
          get_heap s1 rm_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rm_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rm_log_loc = get_heap s0 Llog],
      [/\ get_heap s0 shrincs_fxmss_hcnt_loc = hcv,
          get_heap s1 rm_hcnt_loc = hcv,
          get_heap s0 Lrom = mp,
          get_heap s1 rm_rom_loc = mp &
          get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      [/\ get_heap s1 (prf_key_loc KM) = get_heap s0 Lkp &
          isSome (get_heap s0 Lkp) = isSome (get_heap s0 Lst)]
    & [/\ (get_heap s1 prf_cnt_loc <= (get_heap s0 shrincs_fxmss_scnt_loc).+1)%N
        & (get_heap s0 Lst = None -> get_heap s1 prf_cnt_loc = 0)]].

Arguments H2r : simpl never.

Definition H2i (hcv : nat) (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2i (s0, s1),
          get_heap s1 rm_st_loc = get_heap s0 Lst,
          get_heap s1 rm_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rm_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rm_log_loc = get_heap s0 Llog],
      [/\ get_heap s0 shrincs_fxmss_hcnt_loc = hcv,
          get_heap s1 rm_hcnt_loc = hcv,
          get_heap s0 Lrom = mp,
          get_heap s1 rm_rom_loc = mp &
          get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      (forall pt : (nat * nat) * M,
          (pt.1.1 <= h_sf)%N ->
          getm (get_heap s1 (prf_tab_loc KM)) pt
          = getm (get_heap s0 Lrt) pt)
    & [/\ (get_heap s1 prf_cnt_loc <= (get_heap s0 shrincs_fxmss_scnt_loc).+1)%N
        & (get_heap s0 Lst = None ->
           get_heap s1 (prf_tab_loc KM) = emptym /\
           get_heap s1 prf_cnt_loc = 0)]].

Arguments H2i : simpl never.

(** FORGE (hop 2 real/ideal): st/log/RO map pinned (st committed). *)
Definition F2r (stv : shrincs_fxmss_game_state PP N) (lg : seq M)
    (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2r (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rm_st_loc = Some stv,
          get_heap s0 Llog = lg &
          get_heap s1 rm_log_loc = lg],
      [/\ get_heap s0 Lrom = mp,
          get_heap s1 rm_rom_loc = mp,
          get_heap s1 rm_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rm_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc],
      [/\ get_heap s1 (prf_key_loc KM) = get_heap s0 Lkp &
          isSome (get_heap s0 Lkp) = isSome (get_heap s0 Lst)]
    & (get_heap s1 prf_cnt_loc <= (get_heap s0 shrincs_fxmss_scnt_loc).+1)%N].

Arguments F2r : simpl never.

Definition F2i (stv : shrincs_fxmss_game_state PP N) (lg : seq M)
    (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2i (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rm_st_loc = Some stv,
          get_heap s0 Llog = lg &
          get_heap s1 rm_log_loc = lg],
      [/\ get_heap s0 Lrom = mp,
          get_heap s1 rm_rom_loc = mp,
          get_heap s1 rm_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rm_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc],
      (forall pt : (nat * nat) * M,
          (pt.1.1 <= h_sf)%N ->
          getm (get_heap s1 (prf_tab_loc KM)) pt
          = getm (get_heap s0 Lrt) pt)
    & (get_heap s1 prf_cnt_loc <= (get_heap s0 shrincs_fxmss_scnt_loc).+1)%N].

Arguments F2i : simpl never.

(** Transformers for the GEN blocks (the pin's counter bump and key
    write). *)
Lemma G2r_set_cnt (ko : option Kp) (c c' : nat) s0 s1 :
  G2r ko c (s0, s1) -> G2r ko c' (s0, set_heap s1 prf_cnt_loc c').
Proof.
case=> -[hig m1 m2 m3 m4] [m5 m5f] hk hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
Qed.

Lemma G2r_set_key (c : nat) (k : Kp) s0 s1 :
  G2r None c (s0, s1) ->
  G2r (Some k) c (s0, set_heap s1 (prf_key_loc KM) (Some k)).
Proof.
case=> -[hig m1 m2 m3 m4] [m5 m5f] hk hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
Qed.

(** Transformer for the in-SIGN EVAL counter bump. *)
Lemma S2r_set_cnt (stv : shrincs_fxmss_game_state PP N) (kpv : Kp)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) (c : nat) s0 s1 :
  (c <= sc.+1)%N ->
  get_heap s1 prf_cnt_loc = c ->
  S2r stv kpv usv sc lg mp sc.+1 (s0, s1) ->
  S2r stv kpv usv sc lg mp sc.+2 (s0, set_heap s1 prf_cnt_loc c.+1).
Proof.
move=> hc hval [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12]
                [p13 p13f p14]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq ltnS.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence of hop 2 *)

Lemma R_prfm_real (b : bool) :
  perfect IG (G1F b) (R_prfm b ∘ PGM true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv2r).
{ rewrite /inv2r; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* FXGEN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2rE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: sto e0 => [stv|] e0; first by discriminate e0.
  eapply r_assertD; first by [].
  move=> hcap _.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), G2r None 0 (s0, s1)); last first.
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2rE: hinv => hig [[e1 e2 e3 e4 e5] [e6 e7 e8] [e9 e10] efc].
    rewrite /rem_inv /= in h0 h1.
    split.
    - by split.
    - by split.
    - rewrite e7; move: e8; rewrite h0 /=.
      by case: (get_heap s0 Lkp).
    - exact: (e10 h0). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dPP)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  (* the pin EVAL: real side samples the PRF key = G1f's kp *)
  eapply (r_get_rhs_known prf_cnt_loc 0).
  { by move=> s0 s1 [_ _ _ h]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_put_bind_rhs prf_cnt_loc 1 _
            (λ '(s0, s1), G2r None 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G2r_set_cnt h. }
  eapply (r_get_bind_rhs (prf_key_loc KM) None).
  { by move=> s0 s1 [_ _ h _]. }
  cbv beta iota.
  rewrite bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> kp; cbv beta.
  eapply (r_put_bind_rhs (prf_key_loc KM) (Some kp) _
            (λ '(s0, s1), G2r (Some kp) 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G2r_set_key h. }
  simpl.
  rewrite (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_scheme_bind (skeys (size (leaf_paths (tshape arg)))));
    first exact: sample_keys_valid.
  move=> xss; cbv beta.
  eapply r_put_lhs. eapply r_put_lhs. eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hpre1 g1].
  case: hpre1 => s0a [hpre2 g2].
  case: hpre2 => s0b [hblk g3].
  subst.
  split; first by [].
  case: hblk => -[hig m1 m2 m3 m4] [m5 m5f] hk hc.
  apply: inv2rI.
  - apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  - get_heap_simpl.
    rewrite m1 m2 m3 m4 m5 m5f hk hc.
    split.
    + by split.
    + by split.
    + by split.
    + by [].
- (* FXSIGN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sc.
  eapply r_get_remember_rhs => sc'.
  eapply (r_fact (sc' = sc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2rE: hinv => _ [[_ _ e3 _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sc'.
  eapply r_assertD; first by [].
  move=> hsc _.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2rE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => kpo.
  eapply (r_fact (exists kpv, kpo = Some kpv)).
  { move=> s0 s1 [[[[[hinv h0] h1] h2] h3] h4].
    case/inv2rE: hinv => _ [_ [_ _ e8] _ _].
    rewrite /rem_inv /= in h2 h4.
    move: e8; rewrite h2 h4 /= => e8.
    case: kpo h4 e8 => [kpv|] //= _ _.
    by exists kpv. }
  move=> [kpv ekp]; subst kpo.
  simpl.
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => us'.
  eapply (r_fact (us' = us)).
  { move=> s0 s1 [[[[[[[hinv h0] h1] h2] h3] h4] h5] h6].
    case/inv2rE: hinv => _ [[_ e2 _ _ _] _ _ _].
    rewrite /rem_inv /= in h5 h6.
    by rewrite -h5 -h6. }
  move=> e; subst us'.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8].
    case/inv2rE: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h7 h8.
    by rewrite -h7 -h8. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv2rE: hinv => _ [[_ _ _ _ e5] _ _ _].
    rewrite /rem_inv /= in h9 h10.
    by rewrite -h9 -h10. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), S2r stv kpv us sc lg mp sc.+1 (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv2rE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
    split.
    - split=> //.
      by rewrite f7 h4.
    - by split.
    - by split.
    - split; [by [] | by [] | ].
      by rewrite -h0. }
  case E: ([&& flok stv.2.1 arg.2 & arg.2 \notin domm us]); last first.
  + (* refusal: invalid or re-used leaf id (no slot consumed) *)
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hpre1 g1].
    case: hpre1 => s0a [hblk g2].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12]
                  [p13 p13f p14].
    apply: inv2rI.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
      split.
      - by split.
      - by split.
      - by split; first exact: (leqW p14).
      - by [].
  + (* in budget, valid fresh id: the EVAL derives the randomness *)
    eapply r_get_remember_rhs => cnt.
    eapply (r_fact ((cnt <= sc.+1)%N)).
    { move=> s0 s1 [hblk hrem].
      rewrite /rem_inv /= in hrem.
      case: hblk => _ _ _ [_ _ hcb].
      by rewrite -hrem. }
    move=> hcnt.
    eapply r_bind_assertD_rhs.
    { move=> _ _ _.
      by rewrite /q_prfm ltnS (leq_trans hcnt hsc). }
    move=> _.
    eapply (r_put_bind_rhs prf_cnt_loc cnt.+1 _
              (λ '(s0, s1), S2r stv kpv us sc lg mp sc.+2 (s0, s1))).
    { move=> s0 s1 [hblk hrem].
      rewrite /rem_inv /= in hrem.
      exact: S2r_set_cnt hcnt hrem hblk. }
    eapply (r_get_bind_rhs (prf_key_loc KM) (Some kpv)).
    { by move=> s0 s1 [[_ _ _ _ h] _ _ _]. }
    cbv beta iota.
    simpl.
    case Emd: (getm mp (PRFmsg kpv arg.2 arg.1,
                        (stv.1, (arg.2, arg.1)))) => [d|].
    * (* RO hit *)
      simpl.
      case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 arg.2)
                    (PRFmsg kpv arg.2 arg.1) d) => [sg|].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s1d [hp4 g4].
         case: hp4 => s0a [hp5 g5].
         case: hp5 => s0b [hp6 g6].
         case: hp6 => s0c [hp7 g7].
         case: hp7 => s0d [hblk g8].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
         apply: inv2rI.
         -- do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 4 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by split.
            ++ by [].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s0a [hp4 g4].
         case: hp4 => s0b [hp5 g5].
         case: hp5 => s0c [hblk g6].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
         apply: inv2rI.
         -- do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by split.
            ++ by [].
    * (* RO miss: couple the digest samples *)
      rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
      rewrite !bind_assoc.
      simpl.
      eapply (r_scheme_bind dD); first exact: prog_valid.
      move=> d; cbv beta.
      case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 arg.2)
                    (PRFmsg kpv arg.2 arg.1) d) => [sg|].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s1d [hp4 g4].
         case: hp4 => s0a [hp5 g5].
         case: hp5 => s0b [hp6 g6].
         case: hp6 => s0c [hp7 g7].
         case: hp7 => s0d [hblk g8].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
         apply: inv2rI.
         -- do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 4 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by split.
            ++ by [].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s0a [hp4 g4].
         case: hp4 => s0b [hp5 g5].
         case: hp5 => s0c [hblk g6].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
         apply: inv2rI.
         -- do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by split.
            ++ by [].
- (* FXHASH *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => hc.
  eapply r_get_remember_rhs => hc'.
  eapply (r_fact (hc' = hc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2rE: hinv => _ [_ [f6 _ _] _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst hc'.
  eapply r_assertD; first by [].
  move=> hhc _.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2rE: hinv => _ [[_ _ _ _ f5] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), H2r hc mp (s0, s1)); last first.
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2rE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] efc].
    rewrite /rem_inv /= in h0 h1 h2 h3.
    split.
    - by split.
    - by split.
    - by split.
    - split.
      + exact: f9.
      + by move=> hnone; case: (f10 hnone). }
  case Emd: (getm mp arg) => [d|].
  + simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 qf] [q9 q10] [q11 q12].
    apply: inv2rI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10 ?qf.
      split.
      -- by split.
      -- by split.
      -- split; first exact: q11.
         by move=> hnone; exact: q12 hnone.
      -- by [].
  + rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 qf] [q9 q10] [q11 q12].
    apply: inv2rI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10 ?qf.
      split.
      -- by split.
      -- by split.
      -- split; first exact: q11.
         by move=> hnone; exact: q12 hnone.
      -- by [].
- (* FXFORGE: bookkeeping is now b-unconditional; the [if b] rides on
     the returned verdict, identical on both sides — a pure sync. *)
  case: arg => [m sg].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => fc.
  eapply r_get_remember_rhs => fc'.
  eapply (r_fact (fc' = fc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2rE: hinv => _ [_ _ _ ffc].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst fc'.
  rewrite code_link_assert.
  eapply r_assertD; first by [].
  move=> hfc _.
  simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2rE: hinv => _ [[f1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv2rE: hinv => _ [[_ _ _ f4 _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv2rE: hinv => _ [[_ _ _ _ f5] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), F2r stv lg mp (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv2rE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7.
    split.
    - by split.
    - by split.
    - by split.
    - exact: f9. }
  case Emd: (getm mp (sg.1.2, (stv.1, (sg.1.1, m)))) => [d|].
  * simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] [q10 q11] q12.
    apply: inv2rI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10 ?q11.
       split.
       ++ by split.
       ++ split=> //.
          by rewrite q11 q1.
       ++ by split.
       ++ by [].
  * rewrite !code_link_bind.
    rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] [q10 q11] q12.
    apply: inv2rI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10 ?q11.
       split.
       ++ by split.
       ++ split=> //.
          by rewrite q11 q1.
       ++ by split.
       ++ by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence of hop 2 *)

(** Transformers for the ideal GEN/SIGN blocks. *)
Lemma G2i_set_cnt (T : {fmap kh_M KM -> kh_N KM}) (c c' : nat) s0 s1 :
  G2i T c (s0, s1) -> G2i T c' (s0, set_heap s1 prf_cnt_loc c').
Proof.
case=> -[hig m1 m2 m3 m4] [m5 hrel m5f] ht hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
Qed.

Lemma G2i_set_tab_pin (y : R) (c : nat) s0 s1 :
  G2i emptym c (s0, s1) ->
  G2i (setm emptym ((h_sf.+1, 0), m0) y) c
    (s0, set_heap s1 (prf_tab_loc KM) (setm emptym ((h_sf.+1, 0), m0) y)).
Proof.
case=> -[hig m1 m2 m3 m4] [m5 hrel m5f] ht hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- split.
  + by rewrite get_set_heap_neq.
  + move=> pt hlow.
    rewrite setm_pin_low //.
    exact: hrel.
  + by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
Qed.

Lemma S2i_set_cnt (stv : shrincs_fxmss_game_state PP N)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) (tb : {fmap kh_M KM -> kh_N KM})
    (c : nat) s0 s1 :
  (c <= sc.+1)%N ->
  get_heap s1 prf_cnt_loc = c ->
  S2i stv usv sc lg mp tb sc.+1 (s0, s1) ->
  S2i stv usv sc lg mp tb sc.+2 (s0, set_heap s1 prf_cnt_loc c.+1).
Proof.
move=> hc hval [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12]
                [p13 p13f p14]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + move=> pt hlow; rewrite get_set_heap_neq //.
    exact: p4.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq ltnS.
Qed.

(** M5 asymmetric SIGN precond (ideal side): G2f writes the used-set
    BEFORE its RO read (right after the table read), whereas the shared
    reduction body [rm_sign_body] writes it AFTER (matching G1f, for
    R_prfm_real).  So at the digest tail the lhs used-set is one step
    ahead ([setm us0 zi tt]) while the rhs still holds [us0]; the rhs
    used-put inside the tail restores equality.  [S2iA] is [S2i] with
    that single decoupled clause. *)
Definition S2iA (stv : shrincs_fxmss_game_state PP N) (us0 : chMap ('nat × 'nat) 'unit)
    (zi : nat * nat) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) (tb : {fmap kh_M KM -> kh_N KM})
    (cb : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L2i (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rm_st_loc = Some stv,
          get_heap s0 Lrt = tb &
          (forall pt : (nat * nat) * M,
              (pt.1.1 <= h_sf)%N ->
              getm (get_heap s1 (prf_tab_loc KM)) pt = getm tb pt)],
      [/\ get_heap s0 shrincs_fxmss_used_loc = setm us0 zi Datatypes.tt,
          get_heap s1 rm_used_loc = us0,
          get_heap s0 shrincs_fxmss_scnt_loc = sc,
          get_heap s1 rm_scnt_loc = sc &
          get_heap s0 Llog = lg],
      [/\ get_heap s1 rm_log_loc = lg,
          get_heap s0 Lrom = mp &
          get_heap s1 rm_rom_loc = mp]
    & [/\ get_heap s1 rm_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc,
          get_heap s1 rm_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc
        & (get_heap s1 prf_cnt_loc <= cb)%N]].

Arguments S2iA : simpl never.

(** rhs get-remember under a bind: the bind-headed variant of
    [r_get_remember_rhs] (matching
    a constructor-headed rule against a [bind]-wrapped goal makes the
    unifier unfold [bind] into its raw fix, after which equation
    rewriting ([bind_assoc], [code_link_bind]) stops matching; this
    rule keeps the spine folded).  Candidate for the fixed_sum_scheme
    SemanticRules section when a session may touch that tree. *)
Lemma r_get_remember_bind_rhs {A B C : choiceType} (ℓ : Location)
    (pre : precond) (c0 : raw_code A)
    (f : ℓ -> raw_code B) (k1 : B -> raw_code C) (post : postcond A C) :
  (forall v, ⊢ ⦃ λ '(s0, s1), (pre ⋊ rem_rhs ℓ v) (s0, s1) ⦄
       c0 ≈ bind (f v) k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ bind (getr ℓ f) k1 ⦃ post ⦄.
Proof.
move=> h.
eapply r_get_remember_rhs => v.
exact: h.
Qed.

(** The shared digest tail of the ideal SIGN (both r-branches land
    here after the randomness is coupled and the used/tables updated).
    M5: keyed by the adversary id [zi], signs at slot [flidx]; the
    used-set is written BEFORE the tail, so the tail has no counter
    put (Some = rom/log/scnt). *)
Lemma r_sign_tail2i (stv : shrincs_fxmss_game_state PP N)
    (us0 : chMap ('nat × 'nat) 'unit) (zi : nat * nat) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) (tb' : {fmap kh_M KM -> kh_N KM})
    (m : M) (rv : R) :
  ⊢ ⦃ λ '(s0, s1), S2iA stv us0 zi sc lg mp tb' sc.+2 (s0, s1) ⦄
     (md ← (match getm mp (rv, (stv.1, (zi, m))) with
            | Some d => ret d
            | None => d ← dD ;; ret d
            end) ;;
      #put Lrom :=
        setm mp (rv, (stv.1, (zi, m))) md ;;
      match fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 zi) rv md with
      | Some sg =>
          #put Llog := rcons lg m ;;
          #put shrincs_fxmss_scnt_loc := sc.+1 ;;
          ret (Some sg)
      | None =>
          #put shrincs_fxmss_scnt_loc := sc.+1 ;;
          ret None
      end)
   ≈ (md ← (match getm mp (rv, (stv.1, (zi, m))) with
            | Some d => ret d
            | None => d ← dD ;; ret d
            end) ;;
      #put rm_used_loc := setm us0 zi Datatypes.tt ;;
      #put rm_rom_loc :=
        setm mp (rv, (stv.1, (zi, m))) md ;;
      match fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 zi) rv md with
      | Some sg =>
          #put rm_log_loc := rcons lg m ;;
          #put rm_scnt_loc := sc.+1 ;;
          ret (Some sg)
      | None =>
          #put rm_scnt_loc := sc.+1 ;;
          ret None
      end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ inv2i (s0, s1) ⦄.
Proof.
case Emd: (getm mp (rv, (stv.1, (zi, m)))) => [d|].
- simpl.
  case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 zi) rv d) => [sg|].
  + eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s1c [hp3 g3].
    case: hp3 => s1d [hp4 g4].
    case: hp4 => s0a [hp5 g5].
    case: hp5 => s0b [hp6 g6].
    case: hp6 => s0c [hblk g7].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
    apply: inv2iI.
    * do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p5 ?p13 ?p13f.
      split.
      -- by split.
      -- split; first by [].
         move=> pt hlow.
         exact: p4.
      -- by split.
      -- by [].
  + eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s1c [hp3 g3].
    case: hp3 => s0a [hp4 g4].
    case: hp4 => s0b [hblk g5].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
    apply: inv2iI.
    * do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p5 ?p9 ?p10 ?p13 ?p13f.
      split.
      -- by split.
      -- split; first by [].
         move=> pt hlow.
         exact: p4.
      -- by split.
      -- by [].
- rewrite !bind_assoc.
  simpl.
  eapply (r_scheme_bind dD); first exact: prog_valid.
  move=> d; cbv beta.
  case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 zi) rv d) => [sg|].
  + eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s1c [hp3 g3].
    case: hp3 => s1d [hp4 g4].
    case: hp4 => s0a [hp5 g5].
    case: hp5 => s0b [hp6 g6].
    case: hp6 => s0c [hblk g7].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
    apply: inv2iI.
    * do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p5 ?p13 ?p13f.
      split.
      -- by split.
      -- split; first by [].
         move=> pt hlow.
         exact: p4.
      -- by split.
      -- by [].
  + eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s1c [hp3 g3].
    case: hp3 => s0a [hp4 g4].
    case: hp4 => s0b [hblk g5].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
    apply: inv2iI.
    * do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p5 ?p9 ?p10 ?p13 ?p13f.
      split.
      -- by split.
      -- split; first by [].
         move=> pt hlow.
         exact: p4.
      -- by split.
      -- by [].
Qed.

Lemma R_prfm_ideal (b : bool) :
  perfect IG (G2F b) (R_prfm b ∘ PGM false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv2i).
{ rewrite /inv2i; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* FXGEN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2iE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: sto e0 => [stv|] e0; first by discriminate e0.
  eapply r_assertD; first by [].
  move=> hcap _.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), G2i emptym 0 (s0, s1)); last first.
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2iE: hinv => hig [[e1 e2 e3 e4 e5] [e6 erel] [e9 e10] efc].
    rewrite /rem_inv /= in h0 h1.
    case: (e10 h0) => eT ec.
    split.
    - by split.
    - split; [by [] | | by []].
      move=> pt hlow.
      by rewrite -eT; exact: erel.
    - exact: eT.
    - exact: ec. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dPP)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  (* the pin EVAL: ideal side lazily samples the dead table entry *)
  eapply (r_get_rhs_known prf_cnt_loc 0).
  { by move=> s0 s1 [_ _ _ h]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_put_bind_rhs prf_cnt_loc 1 _
            (λ '(s0, s1), G2i emptym 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G2i_set_cnt h. }
  eapply (r_get_bind_rhs (prf_tab_loc KM) emptym).
  { by move=> s0 s1 [_ _ h _]. }
  rewrite emptymE.
  cbv beta iota.
  rewrite bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> y0; cbv beta.
  eapply (r_put_bind_rhs (prf_tab_loc KM)
            (setm emptym ((h_sf.+1, 0), m0) y0) _
            (λ '(s0, s1),
               G2i (setm emptym ((h_sf.+1, 0), m0) y0) 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G2i_set_tab_pin h. }
  simpl.
  rewrite (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_scheme_bind (skeys (size (leaf_paths (tshape arg)))));
    first exact: sample_keys_valid.
  move=> xss; cbv beta.
  eapply r_put_lhs. eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hpre1 g1].
  case: hpre1 => s0a [hblk g2].
  subst.
  split; first by [].
  case: hblk => -[hig m1 m2 m3 m4] [m5 hrel m5f] ht hc.
  apply: inv2iI.
  + apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  + get_heap_simpl.
    rewrite ?m1 ?m2 ?m3 ?m4 ?m5 ?ht ?hc ?m5f.
    split.
    * by split.
    * split; first by [].
      move=> pt hlow.
      exact: hrel.
    * by split.
    * by [].
- (* FXSIGN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sc.
  eapply r_get_remember_rhs => sc'.
  eapply (r_fact (sc' = sc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2iE: hinv => _ [[_ _ e3 _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sc'.
  eapply r_assertD; first by [].
  move=> hsc _.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2iE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => us'.
  eapply (r_fact (us' = us)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv2iE: hinv => _ [[_ e2 _ _ _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst us'.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv2iE: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9].
    case/inv2iE: hinv => _ [[_ _ _ _ e5] _ _ _].
    rewrite /rem_inv /= in h8 h9.
    by rewrite -h8 -h9. }
  move=> e; subst mp'.
  eapply r_get_remember_lhs => tb.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), S2i stv us sc lg mp tb sc.+1 (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv2iE: hinv => hig [[f1 f2 f3 f4 f5] [f6 frel] [f9 f10] efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
    split.
    - split=> //.
      move=> pt hlow.
      by rewrite -h10; exact: frel.
    - by split.
    - by split.
    - split; [by [] | by [] | ].
      by rewrite -h0. }
  case E: ([&& flok stv.2.1 arg.2 & arg.2 \notin domm us]); last first.
  + (* refusal: invalid or re-used leaf id (no slot consumed) *)
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hpre1 g1].
    case: hpre1 => s0a [hblk g2].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
    apply: inv2iI.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
      split.
      - by split.
      - split; first by [].
        move=> pt hlow.
        exact: p4.
      - by split; first exact: (leqW p14).
      - by [].
  + (* in budget, valid fresh id *)
    have hle : ((arg.2, arg.1).1.1 <= h_sf)%N.
    { by move: E => /andP[/and3P[hh _ _] _]. }
    eapply r_get_remember_rhs => cnt.
    eapply (r_fact ((cnt <= sc.+1)%N)).
    { move=> s0 s1 [hblk hrem].
      rewrite /rem_inv /= in hrem.
      case: hblk => _ _ _ [_ _ hcb].
      by rewrite -hrem. }
    move=> hcnt.
    eapply r_bind_assertD_rhs.
    { move=> _ _ _.
      by rewrite /q_prfm ltnS (leq_trans hcnt hsc). }
    move=> _.
    eapply (r_put_bind_rhs prf_cnt_loc cnt.+1 _
              (λ '(s0, s1), S2i stv us sc lg mp tb sc.+2 (s0, s1))).
    { move=> s0 s1 [hblk hrem].
      rewrite /rem_inv /= in hrem.
      exact: S2i_set_cnt hcnt hrem hblk. }
    eapply r_get_remember_bind_rhs => T.
    cbv beta.
    eapply (r_fact (forall pt : (nat * nat) * M,
                      (pt.1.1 <= h_sf)%N -> getm T pt = getm tb pt)).
    { move=> s0 s1 [hblk hrem].
      rewrite /rem_inv /= in hrem.
      case: hblk => -[_ _ _ _ hrel] _ _ _ pt hlow.
      by rewrite -hrem; exact: hrel. }
    move=> hT.
    rewrite (hT (arg.2, arg.1) hle).
    case Ert: (getm tb (arg.2, arg.1)) => [r|].
    * (* table hit: deterministic on both sides *)
      simpl.
      eapply r_put_lhs; eapply r_put_lhs.
      eapply rpre_weaken_rule with
        (pre := λ '(s0, s1),
           S2iA stv us arg.2 sc lg mp
             (setm tb (arg.2, arg.1) r) sc.+2 (s0, s1));
        last first.
      { move=> s0 s1 [s0b [[s0a [[hblk hrem] g1]] g2]].
        subst.
        rewrite /rem_inv /= in hrem.
        case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
        split.
        - split.
          + do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
          + by get_heap_simpl.
          + exact: p2.
          + by get_heap_simpl.
          + move=> pt hlow.
            get_heap_simpl.
            rewrite setmE.
            case: eqP => [-> | _].
            * by rewrite (p4 (arg.2, arg.1) hle) Ert.
            * by apply: p4.
        - split.
          + by get_heap_simpl.
          + exact: p6.
          + by get_heap_simpl.
          + exact: p8.
          + by get_heap_simpl.
        - split.
          + exact: p10.
          + by get_heap_simpl.
          + exact: p12.
        - split.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + exact: p14. }
      rewrite !(code_link_scheme _ _ _ _ (prog_valid dD)).
      exact: r_sign_tail2i.
    * (* table miss: couple the fresh randomness *)
      (* M5: the lifted G2f SIGN body's rt-miss branch is
         [r ← (r ← dR ;; ret r) ;; #put shrincs_fxmss_used_loc ;; ...], a nested
         bind on the LHS that a single [rewrite bind_assoc] consumes,
         leaving the RHS EVAL bind unflattened; [!bind_assoc] flattens
         both so [r_scheme_bind dR] can couple the two [dR] draws. *)
      rewrite !bind_assoc.
      simpl.
      eapply (r_scheme_bind dR); first exact: prog_valid.
      move=> r; cbv beta.
      eapply r_put_rhs.
      eapply r_put_lhs; eapply r_put_lhs.
      eapply rpre_weaken_rule with
        (pre := λ '(s0, s1),
           S2iA stv us arg.2 sc lg mp
             (setm tb (arg.2, arg.1) r) sc.+2 (s0, s1));
        last first.
      { move=> s0 s1 [s0b [[s0a [[s1a [[hblk hrem] g1]] g2]] g3]].
        subst.
        rewrite /rem_inv /= in hrem.
        case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f p14].
        split.
        - split.
          + do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            apply: heap_ignore_set_rhs hig; first by apply: fhas_in; fmap_solve.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + move=> pt hlow.
            get_heap_simpl.
            rewrite !setmE.
            case: eqP => [_ | _] //.
            (* M5: after the prf_tab put the get resolves to [setm T ..];
               the residual is [getm T pt = getm tb pt], discharged by the
               remembered relation [hT] (the abstract [T] is not [p4]'s
               [get_heap _ prf_tab], so [p4] would need [-hrem] first). *)
            by rewrite (hT pt hlow).
        - split.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + by get_heap_simpl.
        - split.
          (* M5: the miss branch's extra [r_put_rhs] (prf_tab) sits over
             s1, so the s1-reads [rm_log]/[prf_cnt] need [get_heap_simpl]
             to strip the set before the remembered fact discharges them
             (the HIT branch had no prf_tab put, hence bare [exact]). *)
          + by get_heap_simpl.
          + by get_heap_simpl.
          + by get_heap_simpl.
        - split.
          + by get_heap_simpl.
          + by get_heap_simpl.
          + by get_heap_simpl. }
      rewrite !(code_link_scheme _ _ _ _ (prog_valid dD)).
      exact: r_sign_tail2i.
- (* FXHASH *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => hc.
  eapply r_get_remember_rhs => hc'.
  eapply (r_fact (hc' = hc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2iE: hinv => _ [_ [f6 _] _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst hc'.
  eapply r_assertD; first by [].
  move=> hhc _.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2iE: hinv => _ [[_ _ _ _ f5] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), H2i hc mp (s0, s1)); last first.
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2iE: hinv => hig [[f1 f2 f3 f4 f5] [f6 frel] [f9 f10] efc].
    rewrite /rem_inv /= in h0 h1 h2 h3.
    split.
    - by split.
    - by split.
    - exact: frel.
    - split.
      + exact: f9.
      + by move=> hnone; case: (f10 hnone) => -> ->. }
  case Emd: (getm mp arg) => [d|].
  + simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 qf] qrel [q11 q12].
    apply: inv2iI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?qf.
      split.
      -- by split.
      -- split; first by [].
         move=> pt hlow.
         exact: qrel.
      -- split; first exact: q11.
         by move=> hnone; exact: q12 hnone.
      -- by [].
  + rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 qf] qrel [q11 q12].
    apply: inv2iI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?qf.
      split.
      -- by split.
      -- split; first by [].
         move=> pt hlow.
         exact: qrel.
      -- split; first exact: q11.
         by move=> hnone; exact: q12 hnone.
      -- by [].
- (* FXFORGE: bookkeeping is now b-unconditional; the [if b] rides on
     the returned verdict, identical on both sides — a pure sync. *)
  case: arg => [m sg].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => fc.
  eapply r_get_remember_rhs => fc'.
  eapply (r_fact (fc' = fc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv2iE: hinv => _ [_ _ _ ffc].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst fc'.
  rewrite code_link_assert.
  eapply r_assertD; first by [].
  move=> hfc _.
  simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv2iE: hinv => _ [[f1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv2iE: hinv => _ [[_ _ _ f4 _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv2iE: hinv => _ [[_ _ _ _ f5] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), F2i stv lg mp (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv2iE: hinv => hig [[f1 f2 f3 f4 f5] [f6 frel] [f9 f10] efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7.
    split.
    - by split.
    - by split.
    - exact: frel.
    - exact: f9. }
  case Emd: (getm mp (sg.1.2, (stv.1, (sg.1.1, m)))) => [d|].
  * simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] qrel q12.
    apply: inv2iI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9.
       split.
       ++ by split.
       ++ split; first by [].
          move=> pt hlow.
          exact: qrel.
       ++ by split.
       ++ by [].
  * rewrite !code_link_bind.
    rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] qrel q12.
    apply: inv2iI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9.
       split.
       ++ by split.
       ++ split; first by [].
          move=> pt hlow.
          exact: qrel.
       ++ by split.
       ++ by [].
Qed.

(* ================================================================== *)
(** ** Hop 2, assembled *)

Lemma PRFmsg_hop (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G1F b) (G2F b) A = Adv (PGM true) (PGM false) (A ∘ R_prfm b).
Proof.
rewrite (Adv_perfect_l (R_prfm_real b)) (Adv_perfect_r (R_prfm_ideal b)).
by rewrite Adv_reduction.
Qed.

(* ================================================================== *)
(** ** Hop 1: the PRF_f swap (G0f -> G1f) *)

(* ------------------------------------------------------------------ *)
(** ** Invariants *)

Definition L1 : Locations :=
  [fmap Lst ; Lkp ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ; shrincs_fxmss_hcnt_loc ;
        shrincs_fxmss_fcnt_loc ;
        rp_st_loc ; rp_kp_loc ; rp_used_loc ; rp_scnt_loc ; rp_log_loc ;
        rp_rom_loc ; rp_hcnt_loc ; rp_fcnt_loc ;
        prf_key_loc KF ; prf_tab_loc KF ; prf_cnt_loc ].

(** Real side: the PRF key/budget are dead state after GEN — the rel
    only pins their initial (pre-GEN) values. *)
Definition R1r (sto : option (shrincs_fxmss_game_state PP N)) (kpo : option Kp)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (rm : {fmap ROIN -> D}) (hc : nat)
    (sto' : option (shrincs_fxmss_game_state PP N)) (kpo' : option Kp)
    (usv' : chMap ('nat × 'nat) 'unit) (sc' : nat)
    (lg' : seq M) (rm' : {fmap ROIN -> D}) (hc' : nat)
    (ko : option Ks) (cnt : nat) (fc fc' : nat) : Prop :=
  [/\ [/\ sto' = sto, kpo' = kpo, usv' = usv, sc' = sc & lg' = lg],
      [/\ rm' = rm & hc' = hc],
      (sto = None -> ko = None /\ cnt = 0)
    & fc' = fc].

Definition inv1r : precond :=
  heap_ignore L1
  ⋊ rel_app [:: (lhs, Lst) ; (lhs, Lkp) ; (lhs, shrincs_fxmss_used_loc) ;
                (lhs, shrincs_fxmss_scnt_loc) ; (lhs, Llog) ; (lhs, Lrom) ;
                (lhs, shrincs_fxmss_hcnt_loc) ;
                (rhs, rp_st_loc) ; (rhs, rp_kp_loc) ; (rhs, rp_used_loc) ;
                (rhs, rp_scnt_loc) ; (rhs, rp_log_loc) ; (rhs, rp_rom_loc) ;
                (rhs, rp_hcnt_loc) ;
                (rhs, prf_key_loc KF) ; (rhs, prf_cnt_loc) ;
                (lhs, shrincs_fxmss_fcnt_loc) ; (rhs, rp_fcnt_loc) ] R1r.

Arguments inv1r : simpl never.

Lemma inv1rE s0 s1 :
  inv1r (s0, s1) ->
  heap_ignore L1 (s0, s1) /\
  R1r (get_heap s0 Lst) (get_heap s0 Lkp) (get_heap s0 shrincs_fxmss_used_loc)
      (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 Llog) (get_heap s0 Lrom)
      (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s1 rp_st_loc) (get_heap s1 rp_kp_loc)
      (get_heap s1 rp_used_loc) (get_heap s1 rp_scnt_loc)
      (get_heap s1 rp_log_loc) (get_heap s1 rp_rom_loc)
      (get_heap s1 rp_hcnt_loc)
      (get_heap s1 (prf_key_loc KF)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rp_fcnt_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma inv1rI s0 s1 :
  heap_ignore L1 (s0, s1) ->
  R1r (get_heap s0 Lst) (get_heap s0 Lkp) (get_heap s0 shrincs_fxmss_used_loc)
      (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 Llog) (get_heap s0 Lrom)
      (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s1 rp_st_loc) (get_heap s1 rp_kp_loc)
      (get_heap s1 rp_used_loc) (get_heap s1 rp_scnt_loc)
      (get_heap s1 rp_log_loc) (get_heap s1 rp_rom_loc)
      (get_heap s1 rp_hcnt_loc)
      (get_heap s1 (prf_key_loc KF)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rp_fcnt_loc) ->
  inv1r (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** Ideal side: the PRF table replaces the key. *)
Definition R1i (sto : option (shrincs_fxmss_game_state PP N)) (kpo : option Kp)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (rm : {fmap ROIN -> D}) (hc : nat)
    (sto' : option (shrincs_fxmss_game_state PP N)) (kpo' : option Kp)
    (usv' : chMap ('nat × 'nat) 'unit) (sc' : nat)
    (lg' : seq M) (rm' : {fmap ROIN -> D}) (hc' : nat)
    (T : {fmap kh_M KF -> kh_N KF}) (cnt : nat) (fc fc' : nat) : Prop :=
  [/\ [/\ sto' = sto, kpo' = kpo, usv' = usv, sc' = sc & lg' = lg],
      [/\ rm' = rm & hc' = hc],
      (sto = None -> T = emptym /\ cnt = 0)
    & fc' = fc].

Definition inv1i : precond :=
  heap_ignore L1
  ⋊ rel_app [:: (lhs, Lst) ; (lhs, Lkp) ; (lhs, shrincs_fxmss_used_loc) ;
                (lhs, shrincs_fxmss_scnt_loc) ; (lhs, Llog) ; (lhs, Lrom) ;
                (lhs, shrincs_fxmss_hcnt_loc) ;
                (rhs, rp_st_loc) ; (rhs, rp_kp_loc) ; (rhs, rp_used_loc) ;
                (rhs, rp_scnt_loc) ; (rhs, rp_log_loc) ; (rhs, rp_rom_loc) ;
                (rhs, rp_hcnt_loc) ;
                (rhs, prf_tab_loc KF) ; (rhs, prf_cnt_loc) ;
                (lhs, shrincs_fxmss_fcnt_loc) ; (rhs, rp_fcnt_loc) ] R1i.

Arguments inv1i : simpl never.

Lemma inv1iE s0 s1 :
  inv1i (s0, s1) ->
  heap_ignore L1 (s0, s1) /\
  R1i (get_heap s0 Lst) (get_heap s0 Lkp) (get_heap s0 shrincs_fxmss_used_loc)
      (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 Llog) (get_heap s0 Lrom)
      (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s1 rp_st_loc) (get_heap s1 rp_kp_loc)
      (get_heap s1 rp_used_loc) (get_heap s1 rp_scnt_loc)
      (get_heap s1 rp_log_loc) (get_heap s1 rp_rom_loc)
      (get_heap s1 rp_hcnt_loc)
      (get_heap s1 (prf_tab_loc KF)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rp_fcnt_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma inv1iI s0 s1 :
  heap_ignore L1 (s0, s1) ->
  R1i (get_heap s0 Lst) (get_heap s0 Lkp) (get_heap s0 shrincs_fxmss_used_loc)
      (get_heap s0 shrincs_fxmss_scnt_loc) (get_heap s0 Llog) (get_heap s0 Lrom)
      (get_heap s0 shrincs_fxmss_hcnt_loc)
      (get_heap s1 rp_st_loc) (get_heap s1 rp_kp_loc)
      (get_heap s1 rp_used_loc) (get_heap s1 rp_scnt_loc)
      (get_heap s1 rp_log_loc) (get_heap s1 rp_rom_loc)
      (get_heap s1 rp_hcnt_loc)
      (get_heap s1 (prf_tab_loc KF)) (get_heap s1 prf_cnt_loc)
      (get_heap s0 shrincs_fxmss_fcnt_loc) (get_heap s1 rp_fcnt_loc) ->
  inv1i (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** Block preconditions (hop 1) *)

(** GEN blocks: mirrored not-yet-written locations + the PRF game
    state (key/cnt real, tab/cnt ideal — the table is tracked
    EXACTLY here, not pointwise: post-GEN it is dead state). *)
Definition G1r (ko : option Ks) (c : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L1 (s0, s1),
          get_heap s1 rp_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rp_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc,
          get_heap s1 rp_log_loc = get_heap s0 Llog &
          get_heap s1 rp_rom_loc = get_heap s0 Lrom],
      [/\ get_heap s1 rp_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc,
          get_heap s1 rp_kp_loc = get_heap s0 Lkp
        & get_heap s1 rp_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      get_heap s1 (prf_key_loc KF) = ko
    & get_heap s1 prf_cnt_loc = c].

Arguments G1r : simpl never.

Definition G1i (T : {fmap kh_M KF -> kh_N KF}) (c : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L1 (s0, s1),
          get_heap s1 rp_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rp_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc,
          get_heap s1 rp_log_loc = get_heap s0 Llog &
          get_heap s1 rp_rom_loc = get_heap s0 Lrom],
      [/\ get_heap s1 rp_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc,
          get_heap s1 rp_kp_loc = get_heap s0 Lkp
        & get_heap s1 rp_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      get_heap s1 (prf_tab_loc KF) = T
    & get_heap s1 prf_cnt_loc = c].

Arguments G1i : simpl never.

(** SIGN block (shared real/ideal: the PRF state is dead here). *)
Definition S1 (stv : shrincs_fxmss_game_state PP N) (kpv : Kp)
    (usv : chMap ('nat × 'nat) 'unit) (sc : nat) (lg : seq M)
    (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L1 (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rp_st_loc = Some stv,
          get_heap s0 Lkp = Some kpv &
          get_heap s1 rp_kp_loc = Some kpv],
      [/\ get_heap s0 shrincs_fxmss_used_loc = usv,
          get_heap s1 rp_used_loc = usv,
          get_heap s0 shrincs_fxmss_scnt_loc = sc,
          get_heap s1 rp_scnt_loc = sc &
          get_heap s0 Llog = lg],
      [/\ get_heap s1 rp_log_loc = lg,
          get_heap s0 Lrom = mp &
          get_heap s1 rp_rom_loc = mp]
    & [/\ get_heap s1 rp_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc
        & get_heap s1 rp_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc]].

Arguments S1 : simpl never.

(** HASH blocks: carry the (sto = None -> initial PRF state) clause
    as a heap relation (HASH does not read the state location). *)
Definition H1r (hcv : nat) (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L1 (s0, s1),
          get_heap s1 rp_st_loc = get_heap s0 Lst,
          get_heap s1 rp_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rp_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rp_log_loc = get_heap s0 Llog],
      [/\ get_heap s0 shrincs_fxmss_hcnt_loc = hcv,
          get_heap s1 rp_hcnt_loc = hcv,
          get_heap s0 Lrom = mp &
          get_heap s1 rp_rom_loc = mp],
      [/\ get_heap s1 rp_kp_loc = get_heap s0 Lkp
        & get_heap s1 rp_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc]
    & (get_heap s0 Lst = None ->
       get_heap s1 (prf_key_loc KF) = None /\
       get_heap s1 prf_cnt_loc = 0)].

Arguments H1r : simpl never.

Definition H1i (hcv : nat) (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L1 (s0, s1),
          get_heap s1 rp_st_loc = get_heap s0 Lst,
          get_heap s1 rp_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rp_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rp_log_loc = get_heap s0 Llog],
      [/\ get_heap s0 shrincs_fxmss_hcnt_loc = hcv,
          get_heap s1 rp_hcnt_loc = hcv,
          get_heap s0 Lrom = mp &
          get_heap s1 rp_rom_loc = mp],
      [/\ get_heap s1 rp_kp_loc = get_heap s0 Lkp
        & get_heap s1 rp_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc]
    & (get_heap s0 Lst = None ->
       get_heap s1 (prf_tab_loc KF) = emptym /\
       get_heap s1 prf_cnt_loc = 0)].

Arguments H1i : simpl never.

(** FORGE block (shared: st committed, so the initial-state clause
    is vacuous). *)
Definition F1 (stv : shrincs_fxmss_game_state PP N) (lg : seq M)
    (mp : {fmap ROIN -> D}) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L1 (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rp_st_loc = Some stv,
          get_heap s0 Llog = lg &
          get_heap s1 rp_log_loc = lg],
      [/\ get_heap s0 Lrom = mp,
          get_heap s1 rp_rom_loc = mp,
          get_heap s1 rp_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rp_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rp_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc]
    & get_heap s1 rp_kp_loc = get_heap s0 Lkp].

Arguments F1 : simpl never.

(** Transformers for the GEN blocks. *)
Lemma G1r_set_cnt (ko : option Ks) (c c' : nat) s0 s1 :
  G1r ko c (s0, s1) -> G1r ko c' (s0, set_heap s1 prf_cnt_loc c').
Proof.
case=> -[hig m1 m2 m3 m4] [m5 m6 m7] hk hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
Qed.

Lemma G1r_set_key (c : nat) (k : Ks) s0 s1 :
  G1r None c (s0, s1) ->
  G1r (Some k) c (s0, set_heap s1 (prf_key_loc KF) (Some k)).
Proof.
case=> -[hig m1 m2 m3 m4] [m5 m6 m7] hk hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
Qed.

Lemma G1i_set_cnt (T : {fmap kh_M KF -> kh_N KF}) (c c' : nat) s0 s1 :
  G1i T c (s0, s1) -> G1i T c' (s0, set_heap s1 prf_cnt_loc c').
Proof.
case=> -[hig m1 m2 m3 m4] [m5 m6 m7] ht hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
Qed.

Lemma G1i_set_tab (T T' : {fmap kh_M KF -> kh_N KF}) (c : nat) s0 s1 :
  G1i T c (s0, s1) ->
  G1i T' c (s0, set_heap s1 (prf_tab_loc KF) T').
Proof.
case=> -[hig m1 m2 m3 m4] [m5 m6 m7] ht hc; split.
- split.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer for the loops *)

(** Chain-index injectivity of the PRF_f query points. *)
Lemma prf_pt_inj_j (pp pp' : PP) (zi zi' : nat * nat) (j j' : nat) :
  j < l -> j' < l ->
  (pp, enc (shrincs_fxmss_wots_prf_adrs zi j))
    = (pp', enc (shrincs_fxmss_wots_prf_adrs zi' j')) -> j = j'.
Proof.
move=> hj hj' e.
move/encode_adrs_inj: (congr1 snd e) => ea.
move: (congr1 (@adrs_chain l w) ea).
rewrite (shrincs_fxmss_wots_prf_adrs_chain l w zi j (component_bounded_lt l j hj))
  (shrincs_fxmss_wots_prf_adrs_chain l w zi' j' (component_bounded_lt l j' hj')).
exact: id.
Qed.

(** The real-side chain value: one anchor's EVAL images are the
    scheme's [shrincs_fxmss_leaf_secret]. *)
Lemma eval_chain_valueE (pp : PP) (k : Ks) (zi : nat * nat) :
  [seq kh_eval KF k (pp, enc (shrincs_fxmss_wots_prf_adrs zi j)) | j <- iota 0 l]
  = fleaf_sk pp k zi.
Proof.
rewrite /shrincs_fxmss_leaf_secret.
by apply: eq_map => j /=; rewrite decode_tweakK.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The EVAL-loop couplings (the lazy-table bridge; header)

    Real side: with the key pinned the loop is deterministic — only
    the budget counter moves.  Ideal side: each EVAL lazily samples a
    FRESH table point (pairwise-distinct addresses), perfectly
    coupled with G1f's independent [sample_seq]/[sample_keys] draws.
    Promote to Toolkit/LazyTable.v in a session allowed to touch
    Toolkit/ (plan). *)

Lemma r_eval_chain_real {A B : choiceType} (c0 : raw_code A)
    (k1 : chList N -> raw_code B) (post : postcond A B)
    (pp : PP) (k : Ks) (zi : nat * nat) (js : seq nat) (c : nat) :
  (c + size js <= q_prf)%N ->
  (⊢ ⦃ λ '(s0, s1), G1r (Some k) (c + size js) (s0, s1) ⦄
     c0
   ≈ k1 [seq kh_eval KF k (pp, enc (shrincs_fxmss_wots_prf_adrs zi j)) | j <- js]
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), G1r (Some k) c (s0, s1) ⦄
     c0 ≈ bind (code_link (eval_chain pp zi js) (PGF true)) k1 ⦃ post ⦄.
Proof.
elim: js c k1 => [|j js IH] c k1 hb hk.
- rewrite addn0 in hk. exact: hk.
- simpl.
  rewrite bind_assoc.
  rewrite resolve_evf_t.
  eapply (r_get_bind_rhs prf_cnt_loc c).
  { by move=> s0 s1 [_ _ _ h]. }
  eapply r_bind_assertD_rhs.
  { move=> s0 s1 _.
    apply: (leq_trans _ hb).
    by rewrite /= addnS ltnS leq_addr. }
  move=> _.
  eapply (r_put_bind_rhs prf_cnt_loc c.+1 _
            (λ '(s0, s1), G1r (Some k) c.+1 (s0, s1))).
  { by move=> s0 s1 h; exact: G1r_set_cnt h. }
  eapply (r_get_bind_rhs (prf_key_loc KF) (Some k)).
  { by move=> s0 s1 [_ _ h _]. }
  cbv beta iota.
  simpl.
  rewrite code_link_bind bind_assoc.
  rewrite /= -addSnnS in hb hk.
  eapply IH; first exact: hb.
  exact: hk.
Qed.

Lemma r_eval_anchors_real {A B : choiceType} (c0 : raw_code A)
    (k1 : chList (chList N) -> raw_code B) (post : postcond A B)
    (pp : PP) (k : Ks) (ps : seq (seq bool)) (c : nat) :
  (c + size ps * l <= q_prf)%N ->
  (⊢ ⦃ λ '(s0, s1), G1r (Some k) (c + size ps * l) (s0, s1) ⦄
     c0 ≈ k1 [seq fleaf_sk pp k (posid p) | p <- ps] ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), G1r (Some k) c (s0, s1) ⦄
     c0 ≈ bind (code_link (eval_anchors pp ps) (PGF true)) k1 ⦃ post ⦄.
Proof.
elim: ps c k1 => [|p ps IH] c k1 hb hk.
- rewrite /= mul0n addn0 in hk. exact: hk.
- simpl.
  rewrite code_link_bind bind_assoc.
  rewrite /= mulSn addnA in hb hk.
  eapply r_eval_chain_real.
  + rewrite size_iota.
    apply: (leq_trans _ hb).
    exact: leq_addr.
  + rewrite size_iota eval_chain_valueE.
    cbv beta.
    rewrite code_link_bind bind_assoc.
    eapply IH; first exact: hb.
    exact: hk.
Qed.

Lemma r_eval_chain_ideal {B : choiceType}
    (k0 k1 : chList N -> raw_code B)
    (post : postcond B B)
    (pp : PP) (zi : nat * nat) (n : nat) (js : seq nat)
    (T : {fmap kh_M KF -> kh_N KF}) (c : nat) :
  size js = n ->
  uniq js ->
  all (fun j => j < l) js ->
  (c + size js <= q_prf)%N ->
  (forall j, j \in js ->
     getm T (pp, enc (shrincs_fxmss_wots_prf_adrs zi j)) = None) ->
  (forall (xs : seq N) (T' : {fmap kh_M KF -> kh_N KF}),
     (forall pt, pt \notin
        [seq (pp, enc (shrincs_fxmss_wots_prf_adrs zi j)) | j <- js] ->
        getm T' pt = getm T pt) ->
     ⊢ ⦃ λ '(s0, s1), G1i T' (c + size js) (s0, s1) ⦄
        k0 xs ≈ k1 xs ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), G1i T c (s0, s1) ⦄
     bind (sample_seq dN n) k0
   ≈ bind (code_link (eval_chain pp zi js) (PGF false)) k1 ⦃ post ⦄.
Proof.
elim: js n T c k0 k1 => [|j js IH] n T c k0 k1 hn hu hall hb hfresh hk.
- case: n hn => [|n] // _.
  rewrite /= addn0 in hk.
  by apply: (hk [::] T).
- case: n hn => [|n] // [hn].
  case/andP: hu => hj hu.
  case/andP: hall => hjl hall.
  simpl.
  rewrite !bind_assoc.
  rewrite resolve_evf_f.
  eapply (r_get_bind_rhs prf_cnt_loc c).
  { by move=> s0 s1 [_ _ _ h]. }
  eapply r_bind_assertD_rhs.
  { move=> s0 s1 _.
    apply: (leq_trans _ hb).
    by rewrite /= addnS ltnS leq_addr. }
  move=> _.
  eapply (r_put_bind_rhs prf_cnt_loc c.+1 _
            (λ '(s0, s1), G1i T c.+1 (s0, s1))).
  { by move=> s0 s1 h; exact: G1i_set_cnt h. }
  eapply (r_get_bind_rhs (prf_tab_loc KF) T).
  { by move=> s0 s1 [_ _ h _]. }
  cbv beta.
  rewrite (hfresh j (mem_head j js)).
  cbv iota.
  rewrite bind_assoc.
  simpl.
  eapply (r_scheme_bind dN); first exact: prog_valid.
  move=> x; cbv beta.
  eapply (r_put_bind_rhs (prf_tab_loc KF)
            (setm T (pp, enc (shrincs_fxmss_wots_prf_adrs zi j)) x) _
            (λ '(s0, s1),
               G1i (setm T (pp, enc (shrincs_fxmss_wots_prf_adrs zi j)) x)
                 c.+1 (s0, s1))).
  { by move=> s0 s1 h; exact: G1i_set_tab h. }
  simpl.
  rewrite bind_assoc.
  rewrite code_link_bind bind_assoc.
  rewrite /= -addSnnS in hb hk.
  eapply IH.
  + exact: hn.
  + exact: hu.
  + exact: hall.
  + exact: hb.
  + move=> j' hj'.
    rewrite setmE.
	    case: eqP => [e | _].
	    * have hj'l : j' < l := allP hall j' hj'.
	      have ej := prf_pt_inj_j pp pp zi zi j' j hj'l hjl e.
	      by rewrite -ej hj' in hj.
    * by apply: hfresh; rewrite in_cons hj' orbT.
  + move=> xs T' hoff.
    apply: (hk (x :: xs) T').
    move=> pt hpt.
    move: hpt; rewrite /= in_cons negb_or => /andP[hne hpt].
    rewrite (hoff pt hpt) setmE.
    by case: eqP => [e | _] //; rewrite e eqxx in hne.
Qed.

Lemma r_eval_anchors_ideal {B : choiceType}
    (k0 k1 : chList (chList N) -> raw_code B)
    (post : postcond B B)
    (pp : PP) (ps : seq (seq bool))
    (T : {fmap kh_M KF -> kh_N KF}) (c : nat) :
  uniq ps ->
  all (fun p => size p <= h_sf) ps ->
  (c + size ps * l <= q_prf)%N ->
  (forall p j, p \in ps -> (j < l)%N ->
     getm T (pp, enc (shrincs_fxmss_wots_prf_adrs (posid p) j)) = None) ->
  (forall (xss : seq (seq N)) (T' : {fmap kh_M KF -> kh_N KF}),
     ⊢ ⦃ λ '(s0, s1), G1i T' (c + size ps * l) (s0, s1) ⦄
        k0 xss ≈ k1 xss ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), G1i T c (s0, s1) ⦄
     bind (skeys (size ps)) k0
   ≈ bind (code_link (eval_anchors pp ps) (PGF false)) k1 ⦃ post ⦄.
Proof.
elim: ps T c k0 k1 => [|p ps IH] T c k0 k1 hu hall hb hfresh hk.
- rewrite /= mul0n addn0 in hk.
  exact: (hk [::] T).
- case/andP: hu => hp hu.
  case/andP: hall => hszp hall.
  simpl.
  rewrite !bind_assoc.
  rewrite code_link_bind bind_assoc.
  rewrite /= mulSn addnA in hb hk.
  eapply (r_eval_chain_ideal _ _ _ pp (posid p) l (iota 0 l) T c).
  + exact: size_iota.
  + exact: iota_uniq.
  + apply/allP => j.
    by rewrite mem_iota add0n => /andP[].
  + rewrite size_iota.
    apply: (leq_trans _ hb).
    exact: leq_addr.
  + move=> j hj.
    apply: hfresh (mem_head p ps) _.
    by move: hj; rewrite mem_iota add0n => /andP[].
  + move=> xs T' hoff.
    rewrite size_iota.
    cbv beta.
    rewrite bind_assoc.
    rewrite code_link_bind bind_assoc.
    eapply IH.
    * exact: hu.
    * exact: hall.
    * exact: hb.
    * move=> p' j' hp' hjl.
      rewrite hoff.
      + by apply: hfresh hjl; rewrite in_cons hp' orbT.
      + apply/negP => /mapP[j0 hj0 e].
        have hszp' : size p' <= h_sf by move/allP: hall; apply.
        have hj0l : j0 < l.
          by move: hj0; rewrite mem_iota add0n => /andP[].
        case: (prf_pt_inj pp p' p j' j0 hszp' hszp hjl hj0l e) => ep _.
        rewrite ep in hp'.
        by rewrite hp' in hp.
    * move=> xss T''.
      exact: (hk (xs :: xss) T'').
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence of hop 1 *)

Lemma R_prf_real (b : bool) :
  perfect IG (G0F b) (R_prf b ∘ PGF true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv1r).
{ rewrite /inv1r; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* FXGEN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1rE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: sto e0 => [stv|] e0; first by discriminate e0.
  eapply r_assertD; first by [].
  move=> hcap _.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), G1r None 0 (s0, s1)); last first.
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1rE: hinv => hig [[e1 e2 e3 e4 e5] [e6 e7] e8 efc].
    rewrite /rem_inv /= in h0 h1.
    case: (e8 h0) => ek ec.
    split.
    - by split.
    - by split.
    - exact: ek.
    - exact: ec. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dPP)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  (* the pin EVAL: real side samples the PRF key = G0f's ks *)
  eapply (r_get_rhs_known prf_cnt_loc 0).
  { by move=> s0 s1 [_ _ _ h]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_put_bind_rhs prf_cnt_loc 1 _
            (λ '(s0, s1), G1r None 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G1r_set_cnt h. }
  eapply (r_get_bind_rhs (prf_key_loc KF) None).
  { by move=> s0 s1 [_ _ h _]. }
  cbv beta iota.
  rewrite bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> k; cbv beta.
  eapply (r_put_bind_rhs (prf_key_loc KF) (Some k) _
            (λ '(s0, s1), G1r (Some k) 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G1r_set_key h. }
  simpl.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dKp)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> kp; cbv beta.
  (* the EVAL loop computes [leaf_sks pp k arg] *)
  eapply r_eval_anchors_real.
  { rewrite /q_prf add1n ltnS.
    by apply: leq_mul; [exact: hcap | exact: leqnn]. }
  have -> : [seq fleaf_sk pp k (posid p) | p <- leaf_paths (tshape arg)]
            = fleaf_sks pp k arg by [].
  cbv beta.
  eapply r_put_lhs. eapply r_put_lhs. eapply r_put_rhs. eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hp1 g1].
  case: hp1 => s1b [hp2 g2].
  case: hp2 => s0a [hp3 g3].
  case: hp3 => s0b [hblk g4].
  subst.
  split; first by [].
  case: hblk => -[hig m1 m2 m3 m4] [m5 m6 m7] hk hc.
  apply: inv1rI.
  - do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
    do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
    exact: hig.
  - get_heap_simpl.
    rewrite m1 m2 m3 m4 m5 m7.
    split.
    + by split.
    + by split.
    + by [].
    + by [].
- (* FXSIGN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sc.
  eapply r_get_remember_rhs => sc'.
  eapply (r_fact (sc' = sc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1rE: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sc'.
  eapply r_assertD; first by [].
  move=> hsc _.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1rE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => kpo.
  eapply r_get_remember_rhs => kpo'.
  eapply (r_fact (kpo' = kpo)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv1rE: hinv => _ [[_ e2 _ _ _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst kpo'.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e2 e3.
  case: kpo e2 e3 => [kpv|] e2 e3; last by discriminate e2.
  simpl.
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => us'.
  eapply (r_fact (us' = us)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv1rE: hinv => _ [[_ _ e3' _ _] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst us'.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9].
    case/inv1rE: hinv => _ [[_ _ _ _ e5] _ _ _].
    rewrite /rem_inv /= in h8 h9.
    by rewrite -h8 -h9. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10] h11].
    case/inv1rE: hinv => _ [_ [e6 _] _ _].
    rewrite /rem_inv /= in h10 h11.
    by rewrite -h10 -h11. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), S1 stv kpv us sc lg mp (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10] h11].
    case/inv1rE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7] f8 efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11.
    split.
    - by split.
    - by split.
    - by split.
    - by split; rewrite ?f7 ?efc. }
  case E: ([&& flok stv.2.1 arg.2 & arg.2 \notin domm us]); last first.
  + (* refusal: counter exhausted *)
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hpre1 g1].
    case: hpre1 => s0a [hblk g2].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
    apply: inv1rI.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
      split.
      - by split.
      - by split.
      - by [].
      - by [].
  + case Emd: (getm mp (PRFmsg kpv arg.2 arg.1,
                        (stv.1, (arg.2, arg.1)))) => [d|].
    * (* RO hit *)
      simpl.
      case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 arg.2)
                    (PRFmsg kpv arg.2 arg.1) d) => [sg|].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s1d [hp4 g4].
         case: hp4 => s0a [hp5 g5].
         case: hp5 => s0b [hp6 g6].
         case: hp6 => s0c [hp7 g7].
         case: hp7 => s0d [hblk g8].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1rI.
         -- do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 4 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s0a [hp4 g4].
         case: hp4 => s0b [hp5 g5].
         case: hp5 => s0c [hblk g6].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1rI.
         -- do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
    * (* RO miss: couple the digest samples *)
      rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
      (* M5: shared [case Emd] leaves both sides [md ← (d ← dD ;; ret d)];
         a single [rewrite bind_assoc] flattens only one keyed occurrence
         (like the hop-2 real RO-miss, which already uses [!bind_assoc]),
         so [!bind_assoc] is needed to couple the two [dD] draws. *)
      rewrite !bind_assoc.
      simpl.
      eapply (r_scheme_bind dD); first exact: prog_valid.
      move=> d; cbv beta.
      case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 arg.2)
                    (PRFmsg kpv arg.2 arg.1) d) => [sg|].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s1d [hp4 g4].
         case: hp4 => s0a [hp5 g5].
         case: hp5 => s0b [hp6 g6].
         case: hp6 => s0c [hp7 g7].
         case: hp7 => s0d [hblk g8].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1rI.
         -- do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 4 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s0a [hp4 g4].
         case: hp4 => s0b [hp5 g5].
         case: hp5 => s0c [hblk g6].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1rI.
         -- do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
- (* FXHASH *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => hc.
  eapply r_get_remember_rhs => hc'.
  eapply (r_fact (hc' = hc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1rE: hinv => _ [_ [_ f7] _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst hc'.
  eapply r_assertD; first by [].
  move=> hhc _.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1rE: hinv => _ [_ [f6 _] _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), H1r hc mp (s0, s1)); last first.
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1rE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7] f8 efc].
    rewrite /rem_inv /= in h0 h1 h2 h3.
    split.
    - by split.
    - by split.
    - by split.
    - by move=> hnone; case: (f8 hnone). }
  case Emd: (getm mp arg) => [d|].
  + simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8] [q9 qf] q10.
    apply: inv1rI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?qf.
      split.
      -- by split.
      -- by split.
      -- by move=> hnone; exact: q10 hnone.
      -- by [].
  + rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8] [q9 qf] q10.
    apply: inv1rI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?qf.
      split.
      -- by split.
      -- by split.
      -- by move=> hnone; exact: q10 hnone.
      -- by [].
- (* FXFORGE: bookkeeping is now b-unconditional; the [if b] rides on
     the returned verdict, identical on both sides — a pure sync. *)
  case: arg => [m sg].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => fc.
  eapply r_get_remember_rhs => fc'.
  eapply (r_fact (fc' = fc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1rE: hinv => _ [_ _ _ ffc].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst fc'.
  rewrite code_link_assert.
  eapply r_assertD; first by [].
  move=> hfc _.
  simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1rE: hinv => _ [[f1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv1rE: hinv => _ [[_ _ _ _ f5] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv1rE: hinv => _ [_ [f6 _] _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), F1 stv lg mp (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv1rE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7] f8 efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7.
    split.
    - by split.
    - by split.
    - by []. }
  case Emd: (getm mp (sg.1.2, (stv.1, (sg.1.1, m)))) => [d|].
  * simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] q10.
    apply: inv1rI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10.
       split.
       ++ by split.
       ++ by split.
       ++ by [].
       ++ by [].
  * rewrite !code_link_bind.
    rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] q10.
    apply: inv1rI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10.
       split.
       ++ by split.
       ++ by split.
       ++ by [].
       ++ by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence of hop 1 *)

Lemma R_prf_ideal (b : bool) :
  perfect IG (G1F b) (R_prf b ∘ PGF false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv1i).
{ rewrite /inv1i; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* FXGEN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1iE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: sto e0 => [stv|] e0; first by discriminate e0.
  eapply r_assertD; first by [].
  move=> hcap _.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), G1i emptym 0 (s0, s1)); last first.
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1iE: hinv => hig [[e1 e2 e3 e4 e5] [e6 e7] e8 efc].
    rewrite /rem_inv /= in h0 h1.
    case: (e8 h0) => et ec.
    split.
    - by split.
    - by split.
    - exact: et.
    - exact: ec. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dPP)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  (* the pin EVAL: ideal side lazily samples the dead table entry *)
  eapply (r_get_rhs_known prf_cnt_loc 0).
  { by move=> s0 s1 [_ _ _ h]. }
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_put_bind_rhs prf_cnt_loc 1 _
            (λ '(s0, s1), G1i emptym 1 (s0, s1))).
  { by move=> s0 s1 h; exact: G1i_set_cnt h. }
  eapply (r_get_bind_rhs (prf_tab_loc KF) emptym).
  { by move=> s0 s1 [_ _ h _]. }
  rewrite emptymE.
  cbv beta iota.
  rewrite bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> y0; cbv beta.
  eapply (r_put_bind_rhs (prf_tab_loc KF)
            (setm emptym (pp, enc (shrincs_fxmss_wots_grind_adrs (0, 0))) y0) _
            (λ '(s0, s1),
               G1i (setm emptym (pp, enc (shrincs_fxmss_wots_grind_adrs (0, 0))) y0) 1
                 (s0, s1))).
  { by move=> s0 s1 h; exact: G1i_set_tab h. }
  simpl.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dKp)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> kp; cbv beta.
  (* the lazy-table bridge: the EVAL loop = [sample_keys] *)
  eapply r_eval_anchors_ideal.
  + exact: leaf_paths_uniq.
  + exact: leaf_paths_depth.
  + rewrite /q_prf add1n ltnS.
    by apply: leq_mul; [exact: hcap | exact: leqnn].
  + move=> p j hp hj.
    by rewrite setmE pin_pt_neqf emptymE.
  + move=> xss T'.
    cbv beta.
    eapply r_put_lhs. eapply r_put_lhs. eapply r_put_rhs. eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig m1 m2 m3 m4] [m5 m6 m7] ht hc.
    apply: inv1iI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite m1 m2 m3 m4 m5 m7.
      split.
      -- by split.
      -- by split.
      -- by [].
      -- by [].
- (* FXSIGN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sc.
  eapply r_get_remember_rhs => sc'.
  eapply (r_fact (sc' = sc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1iE: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sc'.
  eapply r_assertD; first by [].
  move=> hsc _.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1iE: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => kpo.
  eapply r_get_remember_rhs => kpo'.
  eapply (r_fact (kpo' = kpo)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv1iE: hinv => _ [[_ e2 _ _ _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst kpo'.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e2 e3.
  case: kpo e2 e3 => [kpv|] e2 e3; last by discriminate e2.
  simpl.
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => us'.
  eapply (r_fact (us' = us)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv1iE: hinv => _ [[_ _ e3' _ _] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst us'.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9].
    case/inv1iE: hinv => _ [[_ _ _ _ e5] _ _ _].
    rewrite /rem_inv /= in h8 h9.
    by rewrite -h8 -h9. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10] h11].
    case/inv1iE: hinv => _ [_ [e6 _] _ _].
    rewrite /rem_inv /= in h10 h11.
    by rewrite -h10 -h11. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), S1 stv kpv us sc lg mp (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10] h11].
    case/inv1iE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7] f8 efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11.
    split.
    - by split.
    - by split.
    - by split.
    - by split; rewrite ?f7 ?efc. }
  case E: ([&& flok stv.2.1 arg.2 & arg.2 \notin domm us]); last first.
  + (* refusal: counter exhausted *)
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hpre1 g1].
    case: hpre1 => s0a [hblk g2].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
    apply: inv1iI.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
      split.
      - by split.
      - by split.
      - by [].
      - by [].
  + case Emd: (getm mp (PRFmsg kpv arg.2 arg.1,
                        (stv.1, (arg.2, arg.1)))) => [d|].
    * (* RO hit *)
      simpl.
      case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 arg.2)
                    (PRFmsg kpv arg.2 arg.1) d) => [sg|].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s1d [hp4 g4].
         case: hp4 => s0a [hp5 g5].
         case: hp5 => s0b [hp6 g6].
         case: hp6 => s0c [hp7 g7].
         case: hp7 => s0d [hblk g8].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1iI.
         -- do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 4 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s0a [hp4 g4].
         case: hp4 => s0b [hp5 g5].
         case: hp5 => s0c [hblk g6].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1iI.
         -- do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
    * (* RO miss: couple the digest samples *)
      rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
      (* M5: shared [case Emd] leaves both sides [md ← (d ← dD ;; ret d)];
         a single [rewrite bind_assoc] flattens only one keyed occurrence
         (like the hop-2 real RO-miss, which already uses [!bind_assoc]),
         so [!bind_assoc] is needed to couple the two [dD] draws. *)
      rewrite !bind_assoc.
      simpl.
      eapply (r_scheme_bind dD); first exact: prog_valid.
      move=> d; cbv beta.
      case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 (flidx stv.2.1 arg.2)
                    (PRFmsg kpv arg.2 arg.1) d) => [sg|].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s1d [hp4 g4].
         case: hp4 => s0a [hp5 g5].
         case: hp5 => s0b [hp6 g6].
         case: hp6 => s0c [hp7 g7].
         case: hp7 => s0d [hblk g8].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1iI.
         -- do 4 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 4 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
      ** eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
         eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
         apply r_ret => s0 s1 hpre.
         case: hpre => s1a [hp1 g1].
         case: hp1 => s1b [hp2 g2].
         case: hp2 => s1c [hp3 g3].
         case: hp3 => s0a [hp4 g4].
         case: hp4 => s0b [hp5 g5].
         case: hp5 => s0c [hblk g6].
         subst.
         split; first by [].
         case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12] [p13 p13f].
         apply: inv1iI.
         -- do 3 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
            do 3 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
            exact: hig.
         -- get_heap_simpl.
            rewrite ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p9 ?p10 ?p11 ?p12 ?p13 ?p13f.
            split.
            ++ by split.
            ++ by split.
            ++ by [].
            ++ by [].
- (* FXHASH *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => hc.
  eapply r_get_remember_rhs => hc'.
  eapply (r_fact (hc' = hc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1iE: hinv => _ [_ [_ f7] _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst hc'.
  eapply r_assertD; first by [].
  move=> hhc _.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1iE: hinv => _ [_ [f6 _] _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), H1i hc mp (s0, s1)); last first.
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1iE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7] f8 efc].
    rewrite /rem_inv /= in h0 h1 h2 h3.
    split.
    - by split.
    - by split.
    - by split.
    - by move=> hnone; case: (f8 hnone). }
  case Emd: (getm mp arg) => [d|].
  + simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8] [q9 qf] q10.
    apply: inv1iI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?qf.
      split.
      -- by split.
      -- by split.
      -- by move=> hnone; exact: q10 hnone.
      -- by [].
  + rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8] [q9 qf] q10.
    apply: inv1iI.
    * do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?qf.
      split.
      -- by split.
      -- by split.
      -- by move=> hnone; exact: q10 hnone.
      -- by [].
- (* FXFORGE: bookkeeping is now b-unconditional; the [if b] rides on
     the returned verdict, identical on both sides — a pure sync. *)
  case: arg => [m sg].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => fc.
  eapply r_get_remember_rhs => fc'.
  eapply (r_fact (fc' = fc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv1iE: hinv => _ [_ _ _ ffc].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst fc'.
  rewrite code_link_assert.
  eapply r_assertD; first by [].
  move=> hfc _.
  simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv1iE: hinv => _ [[f1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv1iE: hinv => _ [[_ _ _ _ f5] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_rhs => mp'.
  eapply (r_fact (mp' = mp)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv1iE: hinv => _ [_ [f6 _] _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst mp'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), F1 stv lg mp (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv1iE: hinv => hig [[f1 f2 f3 f4 f5] [f6 f7] f8 efc].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7.
    split.
    - by split.
    - by split.
    - by []. }
  case Emd: (getm mp (sg.1.2, (stv.1, (sg.1.1, m)))) => [d|].
  * simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] q10.
    apply: inv1iI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10.
       split.
       ++ by split.
       ++ by split.
       ++ by [].
       ++ by [].
  * rewrite !code_link_bind.
    rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
    rewrite !bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s1b [hp2 g2].
    case: hp2 => s0a [hp3 g3].
    case: hp3 => s0b [hblk g4].
    subst.
    split; first by [].
    case: hblk => -[hig q1 q2 q3 q4] [q5 q6 q7 q8 q9] q10.
    apply: inv1iI.
    -- do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
       do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?q1 ?q2 ?q3 ?q4 ?q5 ?q6 ?q7 ?q8 ?q9 ?q10.
       split.
       ++ by split.
       ++ by split.
       ++ by [].
       ++ by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Hop 1, assembled *)

Lemma PRFf_hop (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G0F b) (G1F b) A = Adv (PGF true) (PGF false) (A ∘ R_prf b).
Proof.
rewrite (Adv_perfect_l (R_prf_real b)) (Adv_perfect_r (R_prf_ideal b)).
by rewrite Adv_reduction.
Qed.

End FXMSSPRFHop.
