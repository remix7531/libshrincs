(** * SHRINCS.FXMSS.GrindAssertHop  (M5 lifted)

    Grind-assert hop G4c -> G5f over the adversary-chosen-leaf-id
    interface.  [G5f] (LateGames.v) is [G4c] (DigestHop.v) with
    REFUSALS REMOVED: GEN additionally [#assert]s that every presampled
    slot digest is grindable at its committed anchor
    ([sd_grindable], now ranging over the committed leaves
    [iota 0 (size (leaf_paths (tshape sp)))]).

    M5 lift.  GEN presamples over [iota 0 n_max]; the used-set
    [fx_used_loc] replaces the [fx_q_loc] counter; SIGN validates the
    adversary id ([leaf_okP]) and refuses re-used ids.  The whole
    post-GEN difference is a signing-table cache that G4c keeps and G5f
    drops: the invariant [G_inv] records that every signing-table key's
    leaf id sits in the used-set, so a query on a FRESH id (the guard
    [mz.2 \notin domm us]) never hits the cache and G4c's tb-miss body
    IS G5f's body.  No grindability or counter bookkeeping survives into
    SIGN (the signed slot is now [flidx st.2.1 mz.2], deterministic in
    the id), so the lockstep is strictly simpler than the counter one.

    The charge is the GEN bad-event mass: some presampled slot is
    ungrindable at its anchor.  Filling [n_max] i.i.d. slots, a
    per-anchor counting bound [Hug] gives by union bound

      eps_grind := n_max * (n_ug / d_n.+1).

    Style + perf: DigestHopBound_diff.v and DIGEST_OPT_NOTES.md. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq Toolkit.ROPlus Toolkit.Reprogram.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.PRFHop FXMSS.ReproHop FXMSS.DigestHop
  FXMSS.DigestHopBound_diff FXMSS.LateGames.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FXMSSGrindAssert.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).
Context (PP N M R : choice_type) (d_n : nat).
Context (F : PP -> adrs_sf -> N -> N) (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> (chFin d_n.+1) * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R).
Context (S_wn c_max h_sf q_s q_h n_max q_f : nat).
Local Notation Dfin := (chFin d_n.+1).
Local Notation dDu := (rp_dPfx d_n).

Local Notation G4M b := (G4m PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4C b := (G4c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G5F b := (LateGames.G5f PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).

Local Notation IG := (I_G0fL PP N Dfin M R).
Local Notation FXSIG := (FxSig N R).
Local Notation FXST := (FxSt PP N).
Local Notation ROIN := (RoIn PP N M R).
Local Notation RTK := (('nat × 'nat) × M).

Local Notation tshape := (shape_of h_sf).
Local Notation spath := (sign_path h_sf).
Local Notation posid := (pos_id h_sf).
Local Notation skeys := (@sample_keys l N dN).
Local Notation fxroot := (fx_root_x PP N F Tl Htree h_sf).
Local Notation fxsignx :=
  (fx_sign_x PP N Dfin R F Tl Hgrind Htree S_wn c_max h_sf).
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).

Local Notation sgrind :=
  (LateGames.slot_grindable PP Dfin Hgrind S_wn c_max h_sf).
Local Notation sdgrind :=
  (LateGames.sd_grindable PP Dfin Hgrind S_wn c_max h_sf).

Local Notation Lst := (fx_st_loc PP N).
Local Notation Llog := (fx_log_loc M).
Local Notation Lrom := (fx_rom_loc PP N Dfin M R).
Local Notation Lrt := (fx_rt_loc M R).
Local Notation Lsd := (DigestHop.fx_sd_loc Dfin).

Local Notation fill4 := (DigestHop.fill_code Dfin dDu).
Local Notation fill5 := (LateGames.fill_code Dfin dDu).

(* Heap accessors. *)
Local Notation hcc h := (get_heap h fx_hcnt_loc).
Local Notation fcc h := (get_heap h fx_fcnt_loc).
Local Notation scv h := (get_heap h fx_scnt_loc).
Local Notation usv h := (get_heap h fx_used_loc).
Local Notation lgv h := (get_heap h Llog).
Local Notation rom h := (get_heap h Lrom).
Local Notation tbl h := (get_heap h Lrt).
Local Notation sdm h := (get_heap h Lsd).

(* Pure finishers / points. *)
Local Notation sfin h st qv sc us lg mp tb mz r md :=
  (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
     h st qv sc us lg mp tb mz r md).
Local Notation fgptx st m sg := (fgpt PP N M R st m sg).
Local Notation fgverdx :=
  (fgverd PP N Dfin M R F Tl Hgrind Htree S_wn h_sf).
Local Notation collev := (DigestHop.coll_ev Dfin M R).
Local Notation Fvrd :=
  (LateGames.fverd PP N Dfin M R F Tl Hgrind Htree S_wn h_sf).

(* ------------------------------------------------------------------ *)
(** ** Pure layer: grindable-slot closure *)

(** [sd_grindable] closure under a good-slot write. *)
Lemma sd_grindable_set (pp : PP) (sp : seq bool) (m0 : chMap 'nat Dfin)
    (j : nat) (y : Dfin) :
  sdgrind pp sp m0 -> sgrind pp sp j y -> sdgrind pp sp (setm m0 j y).
Proof.
move=> /allP hall hy; apply/allP => j' hj'.
rewrite setmE; case: (eqVneq j' j) => [-> // | hne].
by have := hall j' hj'.
Qed.

(** [fill5] (LateGames' sampler) is [fill4] (DigestHop's): identical
    fixpoints, bridged so the GEN charge over [fill4] applies to the
    G5f side. *)
Lemma fill_lg (js : seq nat) (m0 : chMap 'nat Dfin) :
  fill5 js m0 = fill4 js m0.
Proof. by elim: js m0 => [|j js IH] m0 //=. Qed.

(* Keep the kernel from normalising the scheme internals. *)
Opaque fx_root_x fx_sign_x fx_verify_md sample_keys leaf_paths shape_of
  sign_path pos_id.

(* ------------------------------------------------------------------ *)
(** ** Resolve equations for G5f (via [Gkeep]/[G5f] unfolding) *)

Lemma resolve_g5_gen (b : bool) (sp : 'list 'bool) :
  resolve (G5F b) (DigestHop.geno PP N) sp
  = LateGames.gen5_body PP N Dfin R F Tl Hgrind Htree dPP dN dR dDu
      S_wn c_max h_sf n_max sp.
Proof. by rewrite /LateGames.G5f /LateGames.Gkeep /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g5_sign (b : bool) (mz : M × ('nat × 'nat)) :
  resolve (G5F b) (DigestHop.sgo N M R) mz
  = LateGames.sign5_body PP N Dfin M R F Tl Hgrind Htree dR dDu
      S_wn c_max h_sf q_s mz.
Proof. by rewrite /LateGames.G5f /LateGames.Gkeep /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g5_hash (b : bool) (x : ROIN) :
  resolve (G5F b) (DigestHop.hho PP N Dfin M R) x
  = DigestHop.hash_body PP N Dfin M R dDu q_h x.
Proof. by rewrite /LateGames.G5f /LateGames.Gkeep /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g5_forge (b : bool) (m : M) (sg : FXSIG) :
  resolve (G5F b) (DigestHop.fgo N M R) (m, sg)
  = LateGames.forge_keep_body PP N Dfin M R F Tl Hgrind Htree dDu
      S_wn h_sf q_f (fun _ => true) b m sg.
Proof. by rewrite /LateGames.G5f /LateGames.Gkeep /resolve /= coerce_kleisliE. Qed.

(* ------------------------------------------------------------------ *)
(** ** Oracle-level stepping lemmas for the G5f bodies *)

Section OracleSteps5.

Context {T' : choiceType}.

Lemma gen5_step (sp : 'list 'bool) {k : _ -> raw_code T'} {h : heap}
    {z : T'} :
  dfst (Pr_code (bind (LateGames.gen5_body PP N Dfin R F Tl Hgrind Htree
                         dPP dN dR dDu S_wn c_max h_sf n_max sp) k) h) z
  = if ~~ isSome (get_heap h Lst)
       && (size (leaf_paths (tshape sp)) <= n_max)%N
    then (\dlet_(pp <- Pr_fst dPP)
          \dlet_(_ <- Pr_fst dN)
          \dlet_(_ <- Pr_fst dR)
          \dlet_(xss <- Pr_fst (skeys (size (leaf_paths (tshape sp)))))
          \dlet_(sdm <- Pr_fst (fill5 (iota 0 n_max) emptym))
            (if sdgrind pp sp sdm
             then dfst (Pr_code (k (pp, fxroot pp sp xss))
                    (set_heap
                       (set_heap h Lst
                          (Some ((pp, fxroot pp sp xss), (sp, xss))))
                       Lsd sdm))
             else dnull)) z
    else 0.
Proof.
rewrite /LateGames.gen5_body. cbn [bind].
rewrite Pr_code_get.
case E1: (isSome (get_heap h Lst)).
{ by rewrite -[~~ true]/false assertD_false dPr_bind_fail. }
rewrite -[~~ false]/true assertD_true /=. cbn [bind].
case E2: ((size (leaf_paths (tshape sp)) <= n_max)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite bind_assoc dPr_dist. apply: eq_dlet_at => pp.
rewrite bind_assoc dPr_dist. apply: eq_dlet_at => x1.
rewrite bind_assoc dPr_dist. apply: eq_dlet_at => x2.
rewrite bind_assoc dPr_dist. apply: eq_dlet_at => xss.
rewrite bind_assoc dPr_dist. apply: eq_dlet_at => sdm.
case Eg: (sdgrind pp sp sdm); last first.
{ rewrite assertD_false. by rewrite dPr_bind_fail dnullE. }
rewrite assertD_true. cbn [bind].
by rewrite 2!Pr_code_put.
Qed.

Lemma sign5_step (mz : M × ('nat × 'nat)) {k : _ -> raw_code T'}
    {h : heap} {z : T'} :
  dfst (Pr_code (bind (LateGames.sign5_body PP N Dfin M R F Tl Hgrind Htree
                         dR dDu S_wn c_max h_sf q_s mz) k) h) z
  = if (scv h < q_s)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          if [&& flok st.2.1 mz.2 & mz.2 \notin domm (usv h)] then
            match getm (sdm h) (flidx st.2.1 mz.2) with
            | Some md =>
                (\dlet_(r <- Pr_fst dR)
                   dfst (Pr_code
                     (k (sfin h st (flidx st.2.1 mz.2) (scv h) (usv h)
                           (lgv h) (rom h) (tbl h) mz r md).1)
                     (sfin h st (flidx st.2.1 mz.2) (scv h) (usv h)
                        (lgv h) (rom h) (tbl h) mz r md).2)) z
            | None =>
                (\dlet_(r <- Pr_fst dR) \dlet_(md <- Pr_fst dDu)
                   dfst (Pr_code
                     (k (sfin h st (flidx st.2.1 mz.2) (scv h) (usv h)
                           (lgv h) (rom h) (tbl h) mz r md).1)
                     (sfin h st (flidx st.2.1 mz.2) (scv h) (usv h)
                        (lgv h) (rom h) (tbl h) mz r md).2)) z
            end
          else
            dfst (Pr_code (k None) (set_heap h fx_scnt_loc (scv h).+1)) z
      end
    else 0.
Proof.
rewrite /LateGames.sign5_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((scv h < q_s)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [bind].
rewrite 5!Pr_code_get.
case Eg: ([&& flok st.2.1 mz.2 & mz.2 \notin domm (usv h)]); last first.
{ cbn [bind]. by rewrite Pr_code_put. }
rewrite bind_assoc dPr_dist.
case E5: (getm (sdm h) (flidx st.2.1 mz.2)) => [md|].
- apply: eq_dlet_at => r. cbn [bind].
  rewrite 3!Pr_code_put.
  rewrite sign_finE.
  case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md) => [sg|] /=;
    cbn [bind]; by rewrite !Pr_code_put.
- apply: eq_dlet_at => r.
  rewrite bind_assoc. cbn [bind].
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 3!Pr_code_put.
  rewrite sign_finE.
  case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md) => [sg|] /=;
    cbn [bind]; by rewrite !Pr_code_put.
Qed.

(** The G5f FORGE step, generic in the case modifier and [b]. *)
Lemma forge5_step (keep : fcase (A:=N) -> bool) (b : bool) (m : M)
    (sg : FXSIG) {k : _ -> raw_code T'} {h : heap} {z : T'} :
  dfst (Pr_code (bind (LateGames.forge_keep_body PP N Dfin M R F Tl Hgrind
                         Htree dDu S_wn h_sf q_f keep b m sg) k) h) z
  = if (fcc h < q_f)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          match getm (rom h) (fgptx st m sg) with
          | Some md =>
              dfst (Pr_code
                      (k (if b
                          then Fvrd keep st st.2.2 st.2.1 (lgv h)
                                 (sdm h) (tbl h) m sg md
                          else false))
                      (forge_fin PP N Dfin M R h (fcc h) (rom h)
                         (fgptx st m sg) md)) z
          | None =>
              (\dlet_(md <- Pr_fst dDu)
                 dfst (Pr_code
                         (k (if b
                             then Fvrd keep st st.2.2 st.2.1 (lgv h)
                                    (sdm h) (tbl h) m sg md
                             else false))
                         (forge_fin PP N Dfin M R h (fcc h) (rom h)
                            (fgptx st m sg) md))) z
          end
      end
    else 0.
Proof.
rewrite /LateGames.forge_keep_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((fcc h < q_f)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [getSome bind].
rewrite 4!Pr_code_get.
rewrite -[(sg.1.2, (st.1, (sg.1.1, m)))]/(fgptx st m sg).
case E3: (getm (rom h) (fgptx st m sg)) => [md|].
- cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE.
- rewrite bind_assoc. cbn [bind].
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE.
Qed.

(** The G4c FORGE step, generic in [b]. *)
Lemma forge4c_stepb (b : bool) (m : M) (sg : FXSIG)
    {k : _ -> raw_code T'} {h : heap} {z : T'} :
  dfst (Pr_code (bind (resolve (G4C b) (DigestHop.fgo N M R) (m, sg)) k) h) z
  = if (fcc h < q_f)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          match getm (rom h) (fgptx st m sg) with
          | Some md =>
              dfst (Pr_code
                      (k (if b
                          then fgverdx st (lgv h) m sg md
                               && ~~ collev (sdm h) (tbl h)
                                    (sg.1.1, m) sg.1.2 md
                          else false))
                      (forge_fin PP N Dfin M R h (fcc h) (rom h)
                         (fgptx st m sg) md)) z
          | None =>
              (\dlet_(md <- Pr_fst dDu)
                 dfst (Pr_code
                         (k (if b
                             then fgverdx st (lgv h) m sg md
                                  && ~~ collev (sdm h) (tbl h)
                                       (sg.1.1, m) sg.1.2 md
                             else false))
                         (forge_fin PP N Dfin M R h (fcc h) (rom h)
                            (fgptx st m sg) md))) z
          end
      end
    else 0.
Proof.
rewrite (resolve_g4c_forge PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu
           S_wn c_max h_sf q_s q_h n_max q_f b m sg).
rewrite /DigestHop.forge4cf_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((fcc h < q_f)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [getSome bind].
rewrite 4!Pr_code_get.
rewrite -[(sg.1.2, (st.1, (sg.1.1, m)))]/(fgptx st m sg).
case E3: (getm (rom h) (fgptx st m sg)) => [md|].
- cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE /DigestHop.fgverd.
- rewrite bind_assoc. cbn [bind].
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE /DigestHop.fgverd.
Qed.

End OracleSteps5.

(** The G5f trivial-modifier verdict IS the G4c verdict ([andbT]). *)
Lemma fverd_trueE (st : FXST) (lg : seq M) (sd : chMap 'nat Dfin)
    (tb : chMap RTK R) (m : M) (sg : FXSIG) (md : Dfin) :
  Fvrd (fun _ => true) st st.2.2 st.2.1 lg sd tb m sg md
  = fgverdx st lg m sg md && ~~ collev sd tb (sg.1.1, m) sg.1.2 md.
Proof. by rewrite /LateGames.fverd /DigestHop.fgverd andbT. Qed.

(* ------------------------------------------------------------------ *)
(** ** The adversary section: the identical-until-bad induction *)

Section GrindAdversary.

(** Per-anchor ungrindable-digest counting bound (parameter DATA). *)
Context (n_ug : nat).
Context (Hug : forall (pp : PP) (zi : nat * nat),
  ((\sum_(y : 'I_d_n.+1)
     (~~ isSome (find_ctr PP Dfin Hgrind S_wn c_max zi.1 zi.2 pp y)
      : nat)) <= n_ug)%N).

Context (LA : Locations).
Context (sepL : fseparate LA (loc (G4M false))).

(** The adversary's locations avoid the game locations. *)
Local Notation advloc_neq :=
  (dadvloc_neq PP N M R d_n F Tl Hgrind Htree dPP dN dR
     S_wn c_max h_sf q_s q_h n_max q_f LA sepL).

(* Seal the composition/evaluation machinery and the game packages. *)
Opaque code_link Pr_code resolve G4m G4c LateGames.Gkeep LateGames.G5f.

(* ------------------------------------------------------------------ *)
(** ** Budget and invariant *)

Definition eps_g : Axioms.R := n_max%:R * (n_ug%:R / d_n.+1%:R).

Lemma eps_g_ge0 : 0 <= eps_g.
Proof. by rewrite /eps_g mulr_ge0 ?divr_ge0 ?ler0n. Qed.

(** The whole difference is charged at GEN. *)
Definition Gb (h : heap) : Axioms.R :=
  if get_heap h Lst then 0 else eps_g.

Lemma Gb_ge0 (h : heap) : 0 <= Gb h.
Proof. rewrite /Gb. case: (get_heap h Lst) => //. exact: eps_g_ge0. Qed.

(** The lockstep invariant.  Pre-GEN: the signing table is empty.
    Post-GEN: every signing-table key's leaf id is in the used-set, so
    the fresh-id guard forces a cache miss (the counter and grindability
    bookkeeping of the old proof are unnecessary in the lift). *)
Definition G_inv (h : heap) : Prop :=
  match get_heap h Lst with
  | None => tbl h = emptym
  | Some _ => forall kk : RTK, kk \in domm (tbl h) -> kk.1 \in domm (usv h)
  end.

(* Specialised resolve/step lemma shorthands. *)
Local Notation Rg4c_gen := (resolve_g4c_gen PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4c_sign := (resolve_g4c_sign PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4c_hash := (resolve_g4c_hash PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Sgen := (@gen4_step w l PP N Dfin R F Tl Htree dPP dN dR dDu h_sf n_max).
Local Notation Ssign := (@sign4_step w l PP N Dfin M R F Tl Hgrind Htree dR dDu S_wn c_max h_sf q_s).
Local Notation Shash := (@hash_step PP N Dfin M R dDu q_h).

(* ------------------------------------------------------------------ *)
(** ** The GEN fold: charge the ungrindable slots *)

Lemma fill_grind_le {T : choiceType} (pp : PP) (sp' : seq bool) (z : T) :
  forall (js : seq nat) (m0 : chMap 'nat Dfin)
         (K0 K1 : chMap 'nat Dfin -> {distr T / Axioms.R}),
  sdgrind pp sp' m0 ->
  (forall sd, sdgrind pp sp' sd -> K0 sd z = K1 sd z) ->
  `| (\dlet_(sd <- Pr_fst (fill4 js m0)) K0 sd) z
   - (\dlet_(sd <- Pr_fst (fill4 js m0))
        (if sdgrind pp sp' sd then K1 sd else dnull)) z |
  <= (size js)%:R * (n_ug%:R / d_n.+1%:R).
Proof.
elim=> [|j js IH] m0 K0 K1 hg0 hK.
- rewrite /= Pr_fst_ret 2!dlet_unit_ext /= hg0.
  rewrite hK //.
  by rewrite subrr normr0 mul0r.
- rewrite 2!fill_dlet_cons.
  set X := n_ug%:R / d_n.+1%:R.
  set c' := (size js)%:R * X.
  have hc' : 0 <= c'.
  { by rewrite /c' /X mulr_ge0 ?divr_ge0 ?ler0n. }
  apply: le_trans (uniform_split_le d_n
     (fun y : Dfin =>
        \dlet_(sd <- Pr_fst (fill4 js (setm m0 j y))) K0 sd)
     (fun y : Dfin =>
        \dlet_(sd <- Pr_fst (fill4 js (setm m0 j y)))
          (if sdgrind pp sp' sd then K1 sd else dnull))
     (fun y : Dfin => ~~ sgrind pp sp' j y) z c' n_ug hc' _ _) _.
  + move=> y; rewrite negbK => hy.
    apply: IH; [exact: sd_grindable_set hg0 hy | exact: hK].
  + exact: (Hug pp (posid (spath sp' j))).
  + rewrite [size (j :: js)]/= -[in X in _ <= X]natr1 mulrDl mul1r addrC.
    exact: lexx.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Per-oracle cases *)

(* GEN: the ONLY charging step. *)
Lemma GA_gen (b : bool) {T' : choiceType}
    (x : 'list 'bool) (k : (PP × N) -> raw_code T')
    (IH : forall (v : (PP × N)) (h : heap), G_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4C b)) h) z
        - dfst (Pr_code (code_link (k v) (G5F b)) h) z | <= Gb h)
    (h : heap) (hinv : G_inv h) (z : T') :
  `| dfst (Pr_code (bind (gen4_body PP N Dfin R F Tl Htree dPP dN dR dDu h_sf n_max x) (fun v => code_link (k v) (G4C b))) h) z
   - dfst (Pr_code (bind (LateGames.gen5_body PP N Dfin R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf n_max x) (fun v => code_link (k v) (G5F b))) h) z | <= Gb h.
Proof.
rewrite Sgen gen5_step.
rewrite fill_lg.
case Eg: (~~ isSome (get_heap h Lst)
          && (size (leaf_paths (tshape x)) <= n_max)%N); last first.
{ rewrite subrr normr0. exact: Gb_ge0. }
have hstN : get_heap h Lst = None.
{ move: Eg => /andP[h1 _]. by case: (get_heap h Lst) h1. }
have hGbh : Gb h = eps_g by rewrite /Gb hstN.
move: hinv; rewrite /G_inv hstN => htbe.
rewrite hGbh.
apply: dlet_diff_le; first exact: eps_g_ge0. move=> pp.
apply: dlet_diff_le; first exact: eps_g_ge0. move=> x1.
apply: dlet_diff_le; first exact: eps_g_ge0. move=> x2.
apply: dlet_diff_le; first exact: eps_g_ge0. move=> xss.
set v0 := (pp, fx_root_x PP N F Tl Htree h_sf pp x xss).
set vst := Some (v0, (x, xss)).
set h1 := set_heap h Lst vst.
have hKeq : forall sd, sdgrind pp x sd ->
    dfst (Pr_code (code_link (k v0) (G4C b)) (set_heap h1 Lsd sd)) z
    = dfst (Pr_code (code_link (k v0) (G5F b)) (set_heap h1 Lsd sd)) z.
{ move=> sd hgsd.
  have hstS : get_heap (set_heap h1 Lsd sd) Lst = vst.
  { rewrite (get_set_heap_neq _ _ _ Lst); last by [].
    by rewrite /h1 get_set_heap_eq. }
  have hinv' : G_inv (set_heap h1 Lsd sd).
  { rewrite /G_inv hstS => kk.
    rewrite (get_set_heap_neq _ _ _ Lrt); last by [].
    rewrite /h1 (get_set_heap_neq _ _ _ Lrt); last by [].
    by rewrite htbe domm0 in_fset0. }
  have := IH v0 (set_heap h1 Lsd sd) hinv' z.
  rewrite /Gb hstS /=.
  by rewrite normr_le0 subr_eq0 => /eqP. }
apply: le_trans (fill_grind_le pp x z (iota 0 n_max) emptym
  (fun sd => dfst (Pr_code (code_link (k v0) (G4C b)) (set_heap h1 Lsd sd)))
  (fun sd => dfst (Pr_code (code_link (k v0) (G5F b)) (set_heap h1 Lsd sd)))
  _ hKeq) _.
- by apply/allP => j _; rewrite emptymE.
- rewrite size_iota /eps_g. exact: lexx.
Qed.

(* SIGN: post-GEN lockstep (the cache branch is dead by the fresh id). *)

Lemma sfin5_st (h : heap) st qv sc us lg mp tb mz r md :
  get_heap (sfin h st qv sc us lg mp tb mz r md).2 Lst = get_heap h Lst.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  by do ? (rewrite (get_set_heap_neq _ _ _ Lst); last by []).
Qed.

Lemma sfin5_us (h : heap) st qv sc us lg mp tb mz r md :
  usv (sfin h st qv sc us lg mp tb mz r md).2 = setm us mz.2 Datatypes.tt.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  do ? (rewrite (get_set_heap_neq _ _ _ fx_used_loc); last by []);
  by rewrite get_set_heap_eq.
Qed.

Lemma sfin5_tb (h : heap) st qv sc us lg mp tb mz r md :
  tbl (sfin h st qv sc us lg mp tb mz r md).2 = setm tb (mz.2, mz.1) r.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  do ? (rewrite (get_set_heap_neq _ _ _ Lrt); last by []);
  by rewrite get_set_heap_eq.
Qed.

Lemma GA_sign (b : bool) {T' : choiceType}
    (mz : M × ('nat × 'nat)) (k : 'option FXSIG -> raw_code T')
    (IH : forall (v : 'option FXSIG) (h : heap), G_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4C b)) h) z
        - dfst (Pr_code (code_link (k v) (G5F b)) h) z | <= Gb h)
    (h : heap) (hinv : G_inv h) (z : T') :
  `| dfst (Pr_code (bind (sign4_body PP N Dfin M R F Tl Hgrind Htree dR dDu S_wn c_max h_sf q_s mz) (fun v => code_link (k v) (G4C b))) h) z
   - dfst (Pr_code (bind (LateGames.sign5_body PP N Dfin M R F Tl Hgrind Htree dR dDu S_wn c_max h_sf q_s mz) (fun v => code_link (k v) (G5F b))) h) z | <= Gb h.
Proof.
rewrite Ssign sign5_step.
case Esc: ((scv h < q_s)%N); last first.
{ rewrite subrr normr0. exact: Gb_ge0. }
case Est: (get_heap h Lst) => [st|]; last first.
{ rewrite subrr normr0. exact: Gb_ge0. }
move: (hinv); rewrite /G_inv Est => htb.
case Eg: ([&& flok st.2.1 mz.2 & mz.2 \notin domm (usv h)]); last first.
{ set h2 := set_heap h fx_scnt_loc (scv h).+1.
  have hst2 : get_heap h2 Lst = Some st.
  { by rewrite /h2 (get_set_heap_neq _ _ _ Lst) // Est. }
  have hinv2 : G_inv h2.
  { rewrite /G_inv hst2 => kk.
    rewrite /h2 (get_set_heap_neq _ _ _ Lrt); last by [].
    rewrite (get_set_heap_neq _ _ _ fx_used_loc); last by [].
    exact: (htb kk). }
  have hGb2 : Gb h2 = Gb h by rewrite /Gb hst2 Est.
  rewrite -hGb2. exact: (IH None h2 hinv2 z). }
move: Eg => /andP[hflok hnu].
have hcache : getm (tbl h) (mz.2, mz.1) = None.
{ case E: (getm (tbl h) (mz.2, mz.1)) => [r0|] //.
  have hk : (mz.2, mz.1) \in domm (tbl h) by rewrite mem_domm E.
  have := htb _ hk => /= hin. by move: hnu; rewrite hin. }
rewrite hcache.
case Esd: (getm (sdm h) (flidx st.2.1 mz.2)) => [md|].
- apply: dlet_diff_le; first exact: Gb_ge0. move=> r.
  set hs := (sfin h st (flidx st.2.1 mz.2) (scv h) (usv h)
               (lgv h) (rom h) (tbl h) mz r md).2.
  have hst' : get_heap hs Lst = Some st by rewrite /hs sfin5_st Est.
  have hinv' : G_inv hs.
  { rewrite /G_inv hst' => kk.
    rewrite /hs sfin5_tb sfin5_us domm_set in_fsetU1.
    case/orP => [/eqP -> | hin].
    - rewrite domm_set in_fsetU1. apply/orP; left. by [].
    - rewrite domm_set in_fsetU1. apply/orP; right. exact: (htb kk hin). }
  have hGb' : Gb hs = Gb h by rewrite /Gb hst' Est.
  rewrite -hGb'. exact: (IH _ hs hinv' z).
- apply: dlet_diff_le; first exact: Gb_ge0. move=> r.
  apply: dlet_diff_le; first exact: Gb_ge0. move=> md.
  set hs := (sfin h st (flidx st.2.1 mz.2) (scv h) (usv h)
               (lgv h) (rom h) (tbl h) mz r md).2.
  have hst' : get_heap hs Lst = Some st by rewrite /hs sfin5_st Est.
  have hinv' : G_inv hs.
  { rewrite /G_inv hst' => kk.
    rewrite /hs sfin5_tb sfin5_us domm_set in_fsetU1.
    case/orP => [/eqP -> | hin].
    - rewrite domm_set in_fsetU1. apply/orP; left. by [].
    - rewrite domm_set in_fsetU1. apply/orP; right. exact: (htb kk hin). }
  have hGb' : Gb hs = Gb h by rewrite /Gb hst' Est.
  rewrite -hGb'. exact: (IH _ hs hinv' z).
Qed.

(* HASH: identical bodies; the invariant ignores rom/hcnt. *)
Lemma GA_hash (b : bool) {T' : choiceType}
    (x : ROIN) (k : Dfin -> raw_code T')
    (IH : forall (v : Dfin) (h : heap), G_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4C b)) h) z
        - dfst (Pr_code (code_link (k v) (G5F b)) h) z | <= Gb h)
    (h : heap) (hinv : G_inv h) (z : T') :
  `| dfst (Pr_code (bind (DigestHop.hash_body PP N Dfin M R dDu q_h x) (fun v => code_link (k v) (G4C b))) h) z
   - dfst (Pr_code (bind (DigestHop.hash_body PP N Dfin M R dDu q_h x) (fun v => code_link (k v) (G5F b))) h) z | <= Gb h.
Proof.
rewrite Shash Shash.
case Eh: ((hcc h < q_h)%N); last first.
{ rewrite subrr normr0. exact: Gb_ge0. }
set hf := fun md => hash_fin PP N Dfin M R h (hcc h) (rom h) x md.
have hfst : forall md, get_heap (hf md) Lst = get_heap h Lst.
{ move=> md. rewrite /hf hash_finE.
  rewrite (get_set_heap_neq _ _ _ Lst); last by [].
  by rewrite (get_set_heap_neq _ _ _ Lst). }
have hftb : forall md, tbl (hf md) = tbl h.
{ move=> md. rewrite /hf hash_finE.
  rewrite (get_set_heap_neq _ _ _ Lrt); last by [].
  by rewrite (get_set_heap_neq _ _ _ Lrt). }
have hfus : forall md, usv (hf md) = usv h.
{ move=> md. rewrite /hf hash_finE.
  rewrite (get_set_heap_neq _ _ _ fx_used_loc); last by [].
  by rewrite (get_set_heap_neq _ _ _ fx_used_loc). }
have hfG : forall md, G_inv (hf md).
{ move=> md. rewrite /G_inv hfst hftb hfus.
  move: hinv. rewrite /G_inv.
  by case: (get_heap h Lst). }
have hfGb : forall md, Gb (hf md) = Gb h.
{ move=> md. by rewrite /Gb hfst. }
case Erx: (getm (rom h) x) => [md0|].
- rewrite -(hfGb md0). exact: (IH md0 (hf md0) (hfG md0) z).
- apply: dlet_diff_le; first exact: Gb_ge0. move=> md.
  rewrite -(hfGb md). exact: (IH md (hf md) (hfG md) z).
Qed.

(* FORGE: identical bookkeeping; the verdicts agree by [fverd_trueE]. *)
Lemma GA_forge (b : bool) {T' : choiceType}
    (x : (M × FXSIG)) (k : 'bool -> raw_code T')
    (IH : forall (v : 'bool) (h : heap), G_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4C b)) h) z
        - dfst (Pr_code (code_link (k v) (G5F b)) h) z | <= Gb h)
    (h : heap) (hinv : G_inv h) (z : T') :
  `| dfst (Pr_code (bind (resolve (G4C b) (DigestHop.fgo N M R) x) (fun v => code_link (k v) (G4C b))) h) z
   - dfst (Pr_code (bind (resolve (G5F b) (DigestHop.fgo N M R) x) (fun v => code_link (k v) (G5F b))) h) z | <= Gb h.
Proof.
case: x => m sg.
rewrite (forge4c_stepb b m sg (k := fun v => code_link (k v) (G4C b)) (h := h)).
rewrite (resolve_g5_forge b m sg).
rewrite (forge5_step (fun _ => true) b m sg
           (k := fun v => code_link (k v) (G5F b)) (h := h)).
case Ef: ((fcc h < q_f)%N); last first.
{ rewrite subrr normr0. exact: Gb_ge0. }
case Est: (get_heap h Lst) => [st|]; last first.
{ rewrite subrr normr0. exact: Gb_ge0. }
have hvE : forall md : Dfin,
    (if b then Fvrd (fun _ => true) st st.2.2 st.2.1 (lgv h)
            (sdm h) (tbl h) m sg md else false)
    = (if b then fgverdx st (lgv h) m sg md
            && ~~ collev (sdm h) (tbl h) (sg.1.1, m) sg.1.2 md else false).
{ move=> md. by rewrite fverd_trueE. }
set ff := fun md => forge_fin PP N Dfin M R h (fcc h) (rom h)
                      (fgptx st m sg) md.
have ffst : forall md, get_heap (ff md) Lst = get_heap h Lst.
{ move=> md. rewrite /ff forge_finE.
  rewrite (get_set_heap_neq _ _ _ Lst); last by [].
  by rewrite (get_set_heap_neq _ _ _ Lst). }
have fftb : forall md, tbl (ff md) = tbl h.
{ move=> md. rewrite /ff forge_finE.
  rewrite (get_set_heap_neq _ _ _ Lrt); last by [].
  by rewrite (get_set_heap_neq _ _ _ Lrt). }
have ffus : forall md, usv (ff md) = usv h.
{ move=> md. rewrite /ff forge_finE.
  rewrite (get_set_heap_neq _ _ _ fx_used_loc); last by [].
  by rewrite (get_set_heap_neq _ _ _ fx_used_loc). }
have ffG : forall md, G_inv (ff md).
{ move=> md. rewrite /G_inv ffst fftb ffus.
  move: hinv. rewrite /G_inv.
  by case: (get_heap h Lst). }
have ffGb : forall md, Gb (ff md) = Gb h.
{ move=> md. by rewrite /Gb ffst. }
case Erx: (getm (rom h) (fgptx st m sg)) => [md0|].
- rewrite hvE -(ffGb md0). exact: (IH _ (ff md0) (ffG md0) z).
- apply: dlet_diff_le; first exact: Gb_ge0. move=> md.
  rewrite hvE -(ffGb md). exact: (IH _ (ff md) (ffG md) z).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The identical-until-bad induction *)

Lemma GA_core (b : bool) {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IG c) :
  forall (h : heap), G_inv h -> forall z,
    `| dfst (Pr_code (code_link c (G4C b)) h) z
     - dfst (Pr_code (code_link c (G5F b)) h) z |
    <= Gb h.
Proof.
induction VA as [a | o x k Ho Hk IH | lo k Hl Hk IH
                | lo v k Hl Hk IH | op k Hk IH].
- move=> h hinv z. cbn [code_link].
  rewrite subrr normr0. exact: Gb_ge0.
- move=> h hinv z. cbn [code_link].
  fmap_invert Ho.
  + rewrite (Rg4c_gen b) (resolve_g5_gen b).
    exact: (GA_gen b x k IH h hinv z).
  + rewrite (Rg4c_sign b) (resolve_g5_sign b).
    exact: (GA_sign b x k IH h hinv z).
  + rewrite (Rg4c_hash b) (resolve_g5_hash b).
    exact: (GA_hash b x k IH h hinv z).
  + exact: (GA_forge b x k IH h hinv z).
- move=> h hinv z. cbn [code_link].
  case/and5P: (advloc_neq _ Hl) => n1 n2 n3 n4 /and5P[n5 n6 n7 n8 n9].
  rewrite 2!Pr_code_get. exact: (IH _ h hinv z).
- move=> h hinv z. cbn [code_link].
  case/and5P: (advloc_neq _ Hl) => n1 n2 n3 n4 /and5P[n5 n6 n7 n8 n9].
  rewrite 2!Pr_code_put.
  have hinv' : G_inv (set_heap h lo v).
  { move: hinv. rewrite /G_inv.
    rewrite (get_set_heap_neq _ _ _ _ (neqC n1)).
    rewrite (get_set_heap_neq _ _ _ _ (neqC n7)).
    by rewrite (get_set_heap_neq _ _ _ _ (neqC n2)). }
  have hGb : Gb (set_heap h lo v) = Gb h.
  { by rewrite /Gb (get_set_heap_neq _ _ _ _ (neqC n1)). }
  rewrite -hGb. exact: (IH (set_heap h lo v) hinv' z).
- move=> h hinv z. cbn [code_link].
  rewrite 2!dPr_sample.
  apply: dlet_diff_le; first exact: Gb_ge0.
  move=> a. exact: (IH a h hinv z).
Qed.

End GrindAdversary.

(* ------------------------------------------------------------------ *)
(** ** The grind-assert hop *)

Opaque code_link Pr_code resolve.

Theorem Grind_hop (n_ug : nat)
    (Hug : forall (pp : PP) (zi : nat * nat),
      ((\sum_(y : 'I_d_n.+1)
         (~~ isSome (find_ctr PP Dfin Hgrind S_wn c_max zi.1 zi.2 pp y)
          : nat)) <= n_ug)%N)
    (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) (I_G0fL PP N Dfin M R) A_export A) :
  (Adv (G4C b) (G5F b) A <= n_max%:R * (n_ug%:R / d_n.+1%:R) :> Axioms.R)%R.
Proof.
apply: (Adv_nom_ind _ _ _ (I_G0fL PP N Dfin M R)
          (fun x : Axioms.R => x <= n_max%:R * (n_ug%:R / d_n.+1%:R))) => //.
move=> A' LA' VA' _ sep1 sep2.
rewrite /AdvantageE.
have hRUN : fhas A_export RUN by fmap_solve.
have VC := valid_resolve _ _ _ _ RUN tt VA' hRUN.
have sepL : fseparate LA' (loc (G4M false)) by exact: sep1.
have inv0 : G_inv empty_heap.
{ rewrite /G_inv.
  have -> : get_heap empty_heap Lst = None by [].
  by []. }
have hGb0 : Gb n_ug empty_heap = n_max%:R * (n_ug%:R / d_n.+1%:R).
{ rewrite /Gb.
  by have -> : get_heap empty_heap Lst = None by []. }
rewrite 2!Pr_Pr_code 2!resolve_link -hGb0.
exact: (GA_core n_ug Hug LA' sepL b VC empty_heap inv0 true).
Qed.

End FXMSSGrindAssert.
