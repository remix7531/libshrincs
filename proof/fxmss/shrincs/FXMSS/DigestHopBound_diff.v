Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq Toolkit.ROPlus Toolkit.Reprogram.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.PRFHop FXMSS.ReproHop FXMSS.DigestHop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* Keep the kernel from normalising the (irrelevant) scheme internals;
   they only ever appear as opaque atoms in this development. *)
Opaque fx_root_x fx_sign_x fx_verify_md sample_keys leaf_paths shape_of
  sign_path pos_id.

Section FXMSSDigestBound.
Context (PP N M R : choice_type) (d_n : nat).
Context (F : PP -> adrs_sf -> N -> N) (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> (chFin d_n.+1) * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R).
Context (w l S_wn c_max h_sf q_s q_h n_max q_f : nat).
Local Notation Dfin := (chFin d_n.+1).
Local Notation dDu := (rp_dPfx d_n).

Local Notation G3C b := (ReproHop.G3c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4M b := (G4m PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4C b := (G4c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f b).

Local Notation Lsd := (fx_sd_loc Dfin).
Local Notation IG := (I_G0fL PP N Dfin M R).
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).

(** [rp_dPfx] is lossless (uniform on a nonempty finite type). *)
Lemma dDu_ll : LosslessCode dDu.
Proof. exact _. Qed.

(* ------------------------------------------------------------------ *)
(** ** The adversary section: the identical-until-bad induction *)

Section DigAdversary.

Context (LA : Locations).
Context (sepL : fseparate LA (loc (G4M false))).

(** The adversary's locations are disjoint from the 9 game locations. *)
Lemma dadvloc_neq (lo : Location) :
  fhas LA lo →
  [&& lo.1 != (fx_st_loc PP N).1, lo.1 != fx_used_loc.1, lo.1 != fx_scnt_loc.1,
      lo.1 != (fx_log_loc M).1, lo.1 != (fx_rom_loc PP N Dfin M R).1,
      lo.1 != fx_hcnt_loc.1, lo.1 != (fx_rt_loc M R).1,
      lo.1 != fx_fcnt_loc.1 & lo.1 != Lsd.1].
Proof.
move=> hl.
have hn := notin_has_separate _ _ _ hl sepL.
rewrite /G4m domm_mkfmap !inE /= !negb_or in hn.
by case/and5P: hn => -> -> -> -> /and4P [-> -> -> ->].
Qed.

(** [G4m] exposes the same locations for every [b]. *)
Lemma loc_g4m_eq (c : bool) : loc (G4M c) = loc (G4M false).
Proof. by rewrite /G4m. Qed.

(* Treat the (large) game packages as opaque atoms during the proofs;
   they are only ever touched through the resolve/step lemmas.  This
   slashes kernel conversion work in the final assembly. *)
Opaque G4m G4c.

(** Averaging a [dDu]-draw over a constant collapses (losslessness). *)
Lemma dlet_dDu_const {U : choiceType} (nu : {distr U / Axioms.R}) (u : U) :
  (\dlet_(_ <- Pr_fst dDu) nu) u = nu u.
Proof. by rewrite (Pr_fstC dDu_ll). Qed.

(** Peel one [dDu]-draw at the front of a [fill_code] average. *)
Lemma fill_dlet_cons {T : choiceType} (j : nat) (js : seq nat)
    (m0 : chMap 'nat Dfin) (G : chMap 'nat Dfin -> {distr T / Axioms.R})
    (z : T) :
  (\dlet_(sd <- Pr_fst (fill_code Dfin dDu (j :: js) m0)) G sd) z
  = (\dlet_(y <- (uniform d_n.+1).π2)
       \dlet_(sd <- Pr_fst (fill_code Dfin dDu js (setm m0 j y))) G sd) z.
Proof.
have hcons : fill_code Dfin dDu (j :: js) m0
  = (y ← dDu ;; fill_code Dfin dDu js (setm m0 j y)) by [].
rewrite hcons.
rewrite (Pr_fst_bind (c := dDu)) //.
rewrite dlet_dlet_ext.
have hdu : Pr_fst dDu = \dlet_(r <- (uniform d_n.+1).π2) dunit r.
{ by rewrite /rp_dPfx Pr_fst_sample; apply: eq_dlet => r; rewrite Pr_fst_ret. }
rewrite hdu dlet_dlet_ext.
apply: eq_dlet_at => y.
by rewrite dlet_unit_ext.
Qed.

(** Flip a location-name disequality. *)
Lemma neqC {T : eqType} {a b : T} : a != b -> b != a.
Proof. by rewrite eq_sym. Qed.

(** Counting: the number of ordinals lying in a finite value set is at
    most the size of that set. *)
Lemma sum_ord_in_fset (S : {fset Dfin}) :
  ((\sum_(r : 'I_d_n.+1) ((r \in S) : nat)) <= size S)%N.
Proof. exact: (sum_in_fset_le (fun r : 'I_d_n.+1 => r) S (fun a b e => e)). Qed.

(** ** [fill_split_le]: charge a fold of [uniform_split_le] over the
    [fill_code] slots.

    Sampling the [size js] fresh slots of [fill_code], any slot value
    landing in the "bad" value set [S] (at most [size S] of the
    [d_n.+1] values) costs [size S / d_n.+1]; outside that bad set the
    two continuations [G0]/[G1] are [c]-close.  Folded over the slots,
    the total cost is [size js * size S / d_n.+1 + c]. *)
Lemma fill_split_le {T : choiceType} (js : seq nat) (S : {fset Dfin})
    (c : Axioms.R) (z : T) :
  0 <= c ->
  forall (m0 : chMap 'nat Dfin)
         (G0 G1 : chMap 'nat Dfin -> {distr T / Axioms.R}),
  (forall v, v \in codomm m0 -> v \notin S) ->
  (forall sd, (forall v, v \in codomm sd -> v \notin S) ->
              (size (domm sd) <= size (domm m0) + size js)%N ->
              `| G0 sd z - G1 sd z | <= c) ->
  `| (\dlet_(sd <- Pr_fst (fill_code Dfin dDu js m0)) G0 sd) z
   - (\dlet_(sd <- Pr_fst (fill_code Dfin dDu js m0)) G1 sd) z |
  <= (size js)%:R * (size S)%:R / d_n.+1%:R + c.
Proof.
move=> hc.
elim: js => [|j js IH] m0 G0 G1 hm0 hgood.
- (* base: fill_code [] m0 = ret m0 *)
  rewrite /= Pr_fst_ret 2!dlet_unit_ext /=.
  rewrite mul0r mul0r GRing.add0r.
  apply: (hgood m0 hm0). by rewrite addn0.
- (* peel slot j *)
  rewrite 2!fill_dlet_cons.
  set c' := (size js)%:R * (size S)%:R / d_n.+1%:R + c.
  have c'_ge0 : 0 <= c'.
  { rewrite /c'. apply: addr_ge0 => //.
    by rewrite divr_ge0 ?ler0n // mulr_ge0 ?ler0n. }
  have HU := uniform_split_le d_n
       (fun y : Dfin => \dlet_(sd <- Pr_fst (fill_code Dfin dDu js (setm m0 j y))) G0 sd)
       (fun y : Dfin => \dlet_(sd <- Pr_fst (fill_code Dfin dDu js (setm m0 j y))) G1 sd)
       (fun r : Dfin => r \in S) z c' (size S) c'_ge0.
  apply: le_trans (HU _ _) _.
  + (* good slots: extend the base and recurse *)
    move=> r hr.
    have hm0' : forall v, v \in codomm (setm m0 j r) -> v \notin S.
    { move=> v /codommP [k hk].
      move: hk; rewrite setmE; case: eqP => [_ [<-] | _ hk].
      - by rewrite -[r \in S]/(r \in S : bool) (negbTE hr).
      - apply: hm0. apply/codommP. by exists k. }
    apply: (IH (setm m0 j r) G0 G1 hm0').
    move=> sd hsd hszsd. apply: hgood => //.
    apply: leq_trans hszsd _.
    rewrite domm_set sizesU1 -addnA [size (j :: js)]/= addnS.
    apply: leq_trans (leq_add (leq_b1 (j \notin domm m0)) (leqnn _)) _.
    by rewrite add1n.
  + exact: sum_ord_in_fset.
  + (* arithmetic: (size S)/|D| + c' = (size js).+1 * (size S)/|D| + c *)
    rewrite /c' /=.
    rewrite addrA. apply: lerD; last exact: lexx.
    rewrite -mulrDl. apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
    by rewrite -natr1 mulrDl mul1r addrC.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Heap shorthands *)

Local Notation Lst := (fx_st_loc PP N).
Local Notation Lrom := (fx_rom_loc PP N Dfin M R).
Local Notation Lrt := (fx_rt_loc M R).
Local Notation hcc h := (get_heap h fx_hcnt_loc).
Local Notation fcc h := (get_heap h fx_fcnt_loc).
Local Notation rom h := (get_heap h Lrom).
Local Notation tbl h := (get_heap h Lrt).
Local Notation sdm h := (get_heap h Lsd).

(** The bad event guard: a rom value [v] at a non-[tb]-cached point
    [(r,(pk,km))] avoids the presampled-slot values. *)
Definition dig_inv (h : heap) : Prop :=
  forall (x : RoIn PP N M R) (v : Dfin),
    getm (rom h) x = Some v ->
    getm (tbl h) x.2.2 != Some x.1 ->
    v \notin codomm (sdm h).

(** Pre-GEN, the slot map is still empty. *)
Definition dig_pre (h : heap) : Prop :=
  get_heap h Lst = None -> sdm h = emptym.

(** The presampled-slot codomain never exceeds [n_max] values (the
    per-leaf presample now runs over [iota 0 n_max]). *)
Definition dig_sz (h : heap) : Prop :=
  (size (codomm (sdm h)) <= n_max)%N.

(** The full carried invariant. *)
Definition D_inv (h : heap) : Prop :=
  [/\ dig_inv h, dig_pre h, dig_sz h, (hcc h <= q_h)%N & (fcc h <= q_f)%N].

(** The per-step charge budget [Bn h]. *)
Definition Bn (h : heap) : nat :=
  (q_h - hcc h) + (q_f - fcc h)
  + (if get_heap h Lst then 0 else size (domm (rom h)))%N.

Definition Db (h : heap) : Axioms.R := n_max%:R * (Bn h)%:R / d_n.+1%:R.

Lemma Db_ge0 (h : heap) : 0 <= Db h.
Proof.
by rewrite /Db divr_ge0 ?ler0n // mulr_ge0 ?ler0n.
Qed.

(* Specialised resolve/step lemmas (section context applied). *)
Local Notation Rg4m_gen := (resolve_g4m_gen PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4c_gen := (resolve_g4c_gen PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4m_sign := (resolve_g4m_sign PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4c_sign := (resolve_g4c_sign PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4m_hash := (resolve_g4m_hash PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4c_hash := (resolve_g4c_hash PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4m_forge := (resolve_g4m_forge PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).
Local Notation Rg4c_forge := (resolve_g4c_forge PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu w l S_wn c_max h_sf q_s q_h n_max q_f).

Local Notation Sgen := (@gen4_step PP N Dfin R F Tl Htree dPP dN dR dDu w l h_sf n_max).
Local Notation Ssign := (@sign4_step PP N Dfin M R F Tl Hgrind Htree dR dDu w l S_wn c_max h_sf q_s).
Local Notation Shash := (@hash_step PP N Dfin M R dDu q_h).
Local Notation Sfg4m := (@forge3_step PP N Dfin M R F Tl Hgrind Htree dDu w l S_wn h_sf q_f).
Local Notation Sfg4c := (@forge4c_step PP N Dfin M R F Tl Hgrind Htree dDu w l S_wn h_sf q_f).

Local Notation sfin h st qv sc us lg mp tb mz r md :=
  (sign_fin PP N Dfin M R F Tl Hgrind Htree w l S_wn c_max h_sf
     h st qv sc us lg mp tb mz r md).

(* ------------------------------------------------------------------ *)
(** ** [sign_fin] heap reads (the signing tail touches Lrt/Lrom/Llog/
       q_loc/scnt only). *)

Lemma sfin_sd (h : heap) st qv sc us lg mp tb mz r md :
  sdm (sfin h st qv sc us lg mp tb mz r md).2 = sdm h.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  by do ? (rewrite (get_set_heap_neq _ _ _ Lsd); last by []).
Qed.

Lemma sfin_st (h : heap) st qv sc us lg mp tb mz r md :
  get_heap (sfin h st qv sc us lg mp tb mz r md).2 Lst = get_heap h Lst.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  by do ? (rewrite (get_set_heap_neq _ _ _ Lst); last by []).
Qed.

Lemma sfin_hc (h : heap) st qv sc us lg mp tb mz r md :
  hcc (sfin h st qv sc us lg mp tb mz r md).2 = hcc h.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  by do ? (rewrite (get_set_heap_neq _ _ _ fx_hcnt_loc); last by []).
Qed.

Lemma sfin_fc (h : heap) st qv sc us lg mp tb mz r md :
  fcc (sfin h st qv sc us lg mp tb mz r md).2 = fcc h.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  by do ? (rewrite (get_set_heap_neq _ _ _ fx_fcnt_loc); last by []).
Qed.

Lemma sfin_rom (h : heap) st qv sc us lg mp tb mz r md :
  rom (sfin h st qv sc us lg mp tb mz r md).2
  = setm mp (r, (st.1, (mz.2, mz.1))) md.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  do ? (rewrite (get_set_heap_neq _ _ _ Lrom); last by []);
  by rewrite get_set_heap_eq.
Qed.

Lemma sfin_tb (h : heap) st qv sc us lg mp tb mz r md :
  tbl (sfin h st qv sc us lg mp tb mz r md).2 = setm tb (mz.2, mz.1) r.
Proof.
rewrite sign_finE /=.
case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
  do ? (rewrite (get_set_heap_neq _ _ _ Lrt); last by []);
  by rewrite get_set_heap_eq.
Qed.

(** [Db] is unchanged by a signing step (post-GEN: [Lst] is [Some]). *)
Lemma sfin_Db (h : heap) st qv sc us lg mp tb mz r md :
  get_heap h Lst = Some st ->
  Db (sfin h st qv sc us lg mp tb mz r md).2 = Db h.
Proof.
move=> hst. rewrite /Db /Bn sfin_hc sfin_fc sfin_st hst /=.
by case: (get_heap h Lst).
Qed.

(** A signing step preserves the invariant: the freshly written rom
    point is [tb]-cached, and the [tb] update either fills an empty key
    or rewrites it to the same value. *)
Lemma sfin_inv (h : heap) st qv mz r md :
  D_inv h ->
  get_heap h Lst = Some st ->
  (getm (tbl h) (mz.2, mz.1) = None
   \/ getm (tbl h) (mz.2, mz.1) = Some r) ->
  D_inv (sfin h st qv (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
            (get_heap h (fx_log_loc M)) (rom h) (tbl h) mz r md).2.
Proof.
move=> [di dp dsz dh df] hst Hr. split.
- move=> x0 vv. rewrite sfin_rom sfin_tb sfin_sd.
  rewrite setmE => hrom hguard.
  move: hrom; case: eqP => [hx0eq _ | hne hx0].
  + (* x0 = the written point (r,(st.1,(mz.2,mz.1))): tb-cached, guard false *)
    exfalso. move: hguard. rewrite hx0eq /= setmE eqxx.
    by rewrite eqxx.
  + (* x0 <> the written point: reduce to the old invariant *)
    apply: (di x0 vv hx0).
    move: hguard. rewrite setmE.
    case: (eqVneq x0.2.2 (mz.2, mz.1)) => [hkey | hkey] hg.
    * (* x0.2.2 = (mz.2,mz.1): [Hr] makes the old tb match *)
      apply/negP => habs; move: hg => /negP; apply.
      move: habs; rewrite hkey. case: Hr => H; rewrite H //.
    * exact: hg.
- move=> hst'. by move: hst'; rewrite sfin_st hst.
- by rewrite /dig_sz sfin_sd.
- by rewrite sfin_hc.
- by rewrite sfin_fc.
Qed.

(* Seal the composition/evaluation machinery BEFORE the per-oracle case
   lemmas: their proofs go only through proven equations ([Sgen]/[Ssign]/
   [Shash]/[Sfg4m]/[Sfg4c], [Pr_code_get]/[Pr_code_put], the [R*_*] resolve
   lemmas), never by unfolding [code_link]/[Pr_code]/[resolve].  Keeping
   them transparent makes the (large) per-oracle [Qed]s convert the giant
   [code_link _ (G4M/G4C _)] game terms — minutes per [Qed].  Sealing here
   keeps every kernel check fast. *)
Opaque code_link Pr_code resolve.

(* GEN oracle case (post-resolve) *)
Lemma DIG_gen (b : bool) {T' : choiceType}
    (x : 'list 'bool) (k : (PP × N) -> raw_code T')
    (IH : forall (v : (PP × N)) (h : heap), D_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4M b)) h) z
        - dfst (Pr_code (code_link (k v) (G4C b)) h) z | <= Db h)
    (h : heap) (hinv : D_inv h) (z : T') :
  `| dfst (Pr_code (bind (gen4_body PP N Dfin R F Tl Htree dPP dN dR dDu w l h_sf n_max x) (fun v => code_link (k v) (G4M b))) h) z
   - dfst (Pr_code (bind (gen4_body PP N Dfin R F Tl Htree dPP dN dR dDu w l h_sf n_max x) (fun v => code_link (k v) (G4C b))) h) z | <= Db h.
Proof.
rewrite Sgen Sgen.
case Eg: (~~ isSome (get_heap h Lst)
          && (size (leaf_paths (shape_of h_sf x)) <= n_max)%N); last first.
{ rewrite subrr normr0. exact: Db_ge0. }
have hstN : get_heap h Lst = None.
{ move: Eg => /andP[h1 _]. by case: (get_heap h Lst) h1. }
case: hinv => di dp dsz dh df.
apply: dlet_diff_le; first exact: Db_ge0. move=> pp.
apply: dlet_diff_le; first exact: Db_ge0. move=> xn.
apply: dlet_diff_le; first exact: Db_ge0. move=> xr.
apply: dlet_diff_le; first exact: Db_ge0. move=> xss.
set v0 := (pp, fx_root_x PP N F Tl Htree w l h_sf pp x xss).
set vst := Some (v0, (x, xss)).
set h1 := set_heap h Lst vst.
set Bp := ((q_h - hcc h) + (q_f - fcc h))%N.
apply: le_trans
  (fill_split_le (iota 0 n_max) (codomm (rom h)) (Db h1) z
     (Db_ge0 h1) emptym
     (fun sd => dfst (Pr_code (code_link (k v0) (G4M b)) (set_heap h1 Lsd sd)))
     (fun sd => dfst (Pr_code (code_link (k v0) (G4C b)) (set_heap h1 Lsd sd)))
     _ _) _.
* by move=> w0; rewrite codomm0 in_fset0.
* move=> sd hsd hszsd.
  have hsdm : sdm (set_heap h1 Lsd sd) = sd by rewrite get_set_heap_eq.
  have hrom1 : rom h1 = rom h by rewrite /h1 get_set_heap_neq.
  have htb1 : tbl h1 = tbl h by rewrite /h1 get_set_heap_neq.
  have hrom : rom (set_heap h1 Lsd sd) = rom h.
  { rewrite (get_set_heap_neq _ _ _ Lrom) // hrom1 //. }
  have hinv1 : D_inv (set_heap h1 Lsd sd).
  { split.
    - move=> x0 vv. rewrite hsdm hrom => hx0 _.
      have hvin : vv \in codomm (rom h) by apply/codommP; exists x0.
      apply/codommPn => k'. apply/eqP => habs.
      have hvsd : vv \in codomm sd by apply/codommP; exists k'.
      by move: (hsd vv hvsd); rewrite hvin.
    - move=> hst.
      move: hst. rewrite (get_set_heap_neq _ _ _ Lst) // /h1 get_set_heap_eq //.
    - rewrite /dig_sz hsdm.
      apply: leq_trans (size_codomm_le _) _.
      apply: leq_trans hszsd _. by rewrite domm0 size_iota.
    - by rewrite (get_set_heap_neq _ _ _ fx_hcnt_loc) // /h1 get_set_heap_neq.
    - by rewrite (get_set_heap_neq _ _ _ fx_fcnt_loc) // /h1 get_set_heap_neq. }
  have hDbeq : Db (set_heap h1 Lsd sd) = Db h1.
  { rewrite /Db /Bn hrom.
    rewrite (get_set_heap_neq _ _ _ fx_hcnt_loc) //.
    rewrite (get_set_heap_neq _ _ _ fx_fcnt_loc) //.
    rewrite (get_set_heap_neq _ _ _ Lst) //.
    by rewrite hrom1. }
  rewrite -hDbeq. apply: (IH v0 (set_heap h1 Lsd sd) _ z). exact: hinv1.
* have hBn1 : Bn h1 = Bp.
  { rewrite /Bn /Bp /h1.
    rewrite (get_set_heap_neq _ _ _ fx_hcnt_loc) //.
    rewrite (get_set_heap_neq _ _ _ fx_fcnt_loc) //.
    by rewrite get_set_heap_eq /vst /= addn0. }
  have hBnh : Bn h = Bp + size (domm (rom h)).
  { by rewrite /Bn /Bp hstN /=. }
  rewrite size_iota /Db hBn1 hBnh.
  rewrite -mulrDl.
  apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  rewrite -mulrDr. apply: ler_wpM2l; first by rewrite ler0n.
  rewrite -natrD ler_nat addnC leq_add2l.
  exact: size_codomm_le.
Qed.

(* SIGN oracle case (post-resolve).  M5 lift: the input is [mz : M×('nat×'nat)]
   and the old leaf-budget guard [q < #leaves] is REPLACED by the validation
   guard [leaf_okP … && (zi ∉ used)]; on a table miss the digest is read from
   the presampled slot [Lsd] at [lidx st.2.1 mz.2].  The walk is still charge
   -free for SIGN (the freshly written rom point is [tb]-cached, so [D_inv] and
   [Db] are preserved along every branch). *)
Lemma DIG_sign (b : bool) {T' : choiceType}
    (mz : M × ('nat × 'nat)) (k : 'option (FxSig N R) -> raw_code T')
    (IH : forall (v : 'option (FxSig N R)) (h : heap), D_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4M b)) h) z
        - dfst (Pr_code (code_link (k v) (G4C b)) h) z | <= Db h)
    (h : heap) (hinv : D_inv h) (z : T') :
  `| dfst (Pr_code (bind (sign4_body PP N Dfin M R F Tl Hgrind Htree dR dDu w l S_wn c_max h_sf q_s mz) (fun v => code_link (k v) (G4M b))) h) z
   - dfst (Pr_code (bind (sign4_body PP N Dfin M R F Tl Hgrind Htree dR dDu w l S_wn c_max h_sf q_s mz) (fun v => code_link (k v) (G4C b))) h) z | <= Db h.
Proof.
rewrite Ssign Ssign.
case Esc: ((get_heap h fx_scnt_loc < q_s)%N); last first.
{ rewrite subrr normr0. exact: Db_ge0. }
case Est: (get_heap h Lst) => [st|]; last first.
{ rewrite subrr normr0. exact: Db_ge0. }
have hinvE := hinv. case: hinv => di dp dsz dh df.
case Eg: ([&& flok st.2.1 mz.2
           & mz.2 \notin domm (get_heap h fx_used_loc)]); last first.
{ (* guard false (invalid or re-used id): continuation k None at scnt++;
     only [fx_scnt_loc] moves, so [D_inv]/[Db] are unchanged. *)
  set h2 := set_heap h fx_scnt_loc (get_heap h fx_scnt_loc).+1.
  have hinv2 : D_inv h2.
  { split.
    - move=> x0 vv. rewrite /h2 /dig_inv.
      rewrite (get_set_heap_neq _ _ _ Lrom) //.
      rewrite (get_set_heap_neq _ _ _ Lrt) //.
      rewrite (get_set_heap_neq _ _ _ Lsd) //. exact: di.
    - move=> hst. rewrite /h2 (get_set_heap_neq _ _ _ Lsd) //.
      apply: dp. by move: hst; rewrite /h2 (get_set_heap_neq _ _ _ Lst).
    - by rewrite /dig_sz /h2 (get_set_heap_neq _ _ _ Lsd).
    - by rewrite /h2 (get_set_heap_neq _ _ _ fx_hcnt_loc).
    - by rewrite /h2 (get_set_heap_neq _ _ _ fx_fcnt_loc). }
  have hDb2 : Db h2 = Db h.
  { rewrite /Db /Bn /h2.
    rewrite (get_set_heap_neq _ _ _ fx_hcnt_loc) //.
    rewrite (get_set_heap_neq _ _ _ fx_fcnt_loc) //.
    rewrite (get_set_heap_neq _ _ _ Lst) //.
    by rewrite (get_set_heap_neq _ _ _ Lrom). }
  rewrite -hDb2. exact: (IH None h2 hinv2 z). }
(* guard true: case on the signing table at key [(mz.2, mz.1)] *)
case Etb: (getm (tbl h) (mz.2, mz.1)) => [r|].
* (* tb hit: the rom point may be cached or fresh *)
  case Erom: (getm (rom h) (r, (st.1, (mz.2, mz.1)))) => [md|].
  -- (* rom hit: deterministic *)
     have hinvs := sfin_inv h st (flidx st.2.1 mz.2) mz r md
                    hinvE Est (or_intror Etb).
     have hDbs := sfin_Db h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                    (get_heap h fx_used_loc)
                    (get_heap h (fx_log_loc M)) (rom h) (tbl h) mz r md Est.
     rewrite -hDbs. exact: (IH _ _ hinvs z).
  -- (* rom miss: average over fresh md *)
     apply: dlet_diff_le; first exact: Db_ge0. move=> md.
     have hinvs := sfin_inv h st (flidx st.2.1 mz.2) mz r md
                    hinvE Est (or_intror Etb).
     have hDbs := sfin_Db h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                    (get_heap h fx_used_loc)
                    (get_heap h (fx_log_loc M)) (rom h) (tbl h) mz r md Est.
     rewrite -hDbs. exact: (IH _ _ hinvs z).
* (* tb miss: fresh r; the digest is read from the presampled slot
     [lidx st.2.1 mz.2] (slot hit) or a fresh [dD] draw (slot miss).  The
     written rom point is [tb]-cached either way, so [D_inv]/[Db] hold. *)
  case Esd: (getm (sdm h) (flidx st.2.1 mz.2)) => [md|].
  -- apply: dlet_diff_le; first exact: Db_ge0. move=> r.
     have hinvs := sfin_inv h st (flidx st.2.1 mz.2) mz r md
                    hinvE Est (or_introl Etb).
     have hDbs := sfin_Db h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                    (get_heap h fx_used_loc)
                    (get_heap h (fx_log_loc M)) (rom h) (tbl h) mz r md Est.
     rewrite -hDbs. exact: (IH _ _ hinvs z).
  -- apply: dlet_diff_le; first exact: Db_ge0. move=> r.
     apply: dlet_diff_le; first exact: Db_ge0. move=> md.
     have hinvs := sfin_inv h st (flidx st.2.1 mz.2) mz r md
                    hinvE Est (or_introl Etb).
     have hDbs := sfin_Db h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                    (get_heap h fx_used_loc)
                    (get_heap h (fx_log_loc M)) (rom h) (tbl h) mz r md Est.
     rewrite -hDbs. exact: (IH _ _ hinvs z).
Qed.

(* HASH oracle case (post-resolve) *)
Lemma DIG_hash (b : bool) {T' : choiceType}
    (x : RoIn PP N M R) (k : Dfin -> raw_code T')
    (IH : forall (v : Dfin) (h : heap), D_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4M b)) h) z
        - dfst (Pr_code (code_link (k v) (G4C b)) h) z | <= Db h)
    (h : heap) (hinv : D_inv h) (z : T') :
  `| dfst (Pr_code (bind (hash_body PP N Dfin M R dDu q_h x) (fun v => code_link (k v) (G4M b))) h) z
   - dfst (Pr_code (bind (hash_body PP N Dfin M R dDu q_h x) (fun v => code_link (k v) (G4C b))) h) z | <= Db h.
Proof.
rewrite Shash Shash.
case Eh: ((hcc h < q_h)%N); last first.
{ rewrite subrr normr0. exact: Db_ge0. }
case: hinv => di dp dsz dh df.
set hf := fun md => hash_fin PP N Dfin M R h (hcc h) (rom h) x md.
have hfrom : forall md, rom (hf md) = setm (rom h) x md.
{ move=> md. by rewrite /hf hash_finE (get_set_heap_neq _ _ _ Lrom) // get_set_heap_eq. }
have hfsd : forall md, sdm (hf md) = sdm h.
{ move=> md. by rewrite /hf hash_finE (get_set_heap_neq _ _ _ Lsd) // (get_set_heap_neq _ _ _ Lsd). }
have hftb : forall md, tbl (hf md) = tbl h.
{ move=> md. by rewrite /hf hash_finE (get_set_heap_neq _ _ _ Lrt) // (get_set_heap_neq _ _ _ Lrt). }
have hfst : forall md, get_heap (hf md) Lst = get_heap h Lst.
{ move=> md. by rewrite /hf hash_finE (get_set_heap_neq _ _ _ Lst) // (get_set_heap_neq _ _ _ Lst). }
have hfhc : forall md, hcc (hf md) = (hcc h).+1.
{ move=> md. by rewrite /hf hash_finE get_set_heap_eq. }
have hffc : forall md, fcc (hf md) = fcc h.
{ move=> md. by rewrite /hf hash_finE (get_set_heap_neq _ _ _ fx_fcnt_loc) // (get_set_heap_neq _ _ _ fx_fcnt_loc). }
have hdsz : forall md, dig_sz (hf md) by move=> md; rewrite /dig_sz hfsd.
have hdf : forall md, (fcc (hf md) <= q_f)%N by move=> md; rewrite hffc.
have hdh : forall md, (hcc (hf md) <= q_h)%N by move=> md; rewrite hfhc Eh.
have hBn0 : (0 < Bn h)%N.
{ rewrite /Bn -addnA addn_gt0. apply/orP; left. by rewrite subn_gt0 Eh. }
(* [Bn (hf md)] does not depend on the sampled value [md] (only on the
   domain of [rom]); and the dig_inv preservation needs only that [md]
   avoids [codomm sd]. *)
have hqh : (0 < q_h - hcc h)%N by rewrite subn_gt0.
have hBnf_post : forall md, get_heap h Lst -> Bn (hf md) = (Bn h).-1.
{ move=> md hst.
  have hBh : Bn h = ((q_h - hcc h) + (q_f - fcc h))%N
    by rewrite /Bn hst /= addn0.
  rewrite hBh /Bn (hfhc md) (hffc md) (hfst md) (hfrom md) hst /= addn0.
  rewrite subnS -subn1 addnBAC ?subn1 //. }
have hBnf_pre : forall md, get_heap h Lst = None ->
    getm (rom h) x = None -> Bn (hf md) = Bn h.
{ move=> md hst hx.
  have hBh : Bn h = ((q_h - hcc h) + (q_f - fcc h) + size (domm (rom h)))%N
    by rewrite /Bn hst /=.
  rewrite hBh /Bn (hfhc md) (hffc md) (hfst md) (hfrom md) hst /=.
  rewrite domm_set sizesU1 mem_domm hx /= add1n addnS subnS.
  by rewrite -[in RHS](prednK hqh) !addSn. }
case Erx: (getm (rom h) x) => [md0|].
* (* HASH-hit: deterministic, rom unchanged, Bn drops *)
  have hromeq : setm (rom h) x md0 = rom h.
  { apply/eq_fmap => y. rewrite setmE. by case: eqP => [-> | //]. }
  have hinvf : D_inv (hf md0).
  { split.
    - move=> x0 vv. rewrite hfrom hromeq hfsd hftb. exact: di.
    - move=> hst. rewrite hfsd. apply: dp. by rewrite -(hfst md0).
    - exact: hdsz.
    - exact: hdh.
    - exact: hdf. }
  apply: le_trans (IH md0 (hf md0) hinvf z) _.
  rewrite /Db. apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  apply: ler_wpM2l; first by rewrite ler0n.
  rewrite ler_nat /Bn (hfhc md0) (hffc md0) (hfst md0) (hfrom md0) hromeq.
  rewrite leq_add2r. apply: leq_add; last exact: leqnn.
  exact: leq_sub2l.
* (* HASH-miss: a fresh md.  D_inv is preserved when md avoids codomm sd;
     the charge is [size (codomm sd)/|D|]. *)
  have hkey : Pr_fst dDu = \dlet_(r <- (uniform d_n.+1).π2) dunit r.
  { by rewrite /rp_dPfx Pr_fst_sample; apply: eq_dlet => r; rewrite Pr_fst_ret. }
  rewrite hkey.
  rewrite [in X in `| _ - X|%R]dlet_dlet_ext [in X in `| X - _|%R]dlet_dlet_ext.
  under [in X in `| X - _|%R]eq_dlet => r do rewrite dlet_unit_ext.
  under [in X in `| _ - X|%R]eq_dlet => r do rewrite dlet_unit_ext.
  (* dig_inv preservation for any good [md] (md avoids codomm sd) *)
  have hgood : forall md, md \notin codomm (sdm h) -> D_inv (hf md).
  { move=> md hmd. split.
    - move=> x0 vv. rewrite hfrom hfsd hftb.
      rewrite setmE. case: eqP => [_ [<-] _ | _ hx0 hnc].
      + by rewrite -[md \in _]/(md \in _ : bool) (negbTE hmd).
      + exact: di hx0 hnc.
    - move=> hst. rewrite hfsd. apply: dp. by rewrite -(hfst md).
    - exact: hdsz.
    - exact: hdh.
    - exact: hdf. }
  case Est: (get_heap h Lst) => [st|].
  -- (* post-GEN: codomm sd has <= q_s values; charge q_s/|D| *)
     apply: le_trans
       (uniform_split_le d_n
          (fun md : Dfin => dfst (Pr_code (code_link (k md) (G4M b)) (hf md)))
          (fun md : Dfin => dfst (Pr_code (code_link (k md) (G4C b)) (hf md)))
          (fun md : Dfin => md \in codomm (sdm h)) z
          (n_max%:R * (Bn h).-1%:R / d_n.+1%:R) (size (codomm (sdm h))) _ _ _) _.
     ++ by rewrite divr_ge0 ?ler0n // mulr_ge0 ?ler0n.
     ++ move=> md hmd.
        have hDbf : Db (hf md) = n_max%:R * (Bn h).-1%:R / d_n.+1%:R.
        { by rewrite /Db (hBnf_post md) // Est. }
        rewrite -hDbf. apply: (IH md (hf md) _ z). apply: hgood. exact: hmd.
     ++ exact: sum_ord_in_fset.
     ++ rewrite /Db -mulrDl.
        apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
        rewrite -[in X in _ <= X](prednK hBn0).
        rewrite -[in X in _ <= X]natr1 mulrDr mulr1 addrC.
        rewrite lerD2l ler_nat. exact: dsz.
  -- (* pre-GEN: sd = emptym, so codomm sd is empty; charge nothing *)
     have hsd0 : sdm h = emptym by apply: dp.
     apply: le_trans
       (uniform_split_le d_n
          (fun md : Dfin => dfst (Pr_code (code_link (k md) (G4M b)) (hf md)))
          (fun md : Dfin => dfst (Pr_code (code_link (k md) (G4C b)) (hf md)))
          (fun md : Dfin => md \in codomm (sdm h)) z
          (Db h) (size (codomm (sdm h))) _ _ _) _.
     ++ exact: Db_ge0.
     ++ move=> md hmd.
        have hDbf : Db (hf md) = Db h.
        { by rewrite /Db (hBnf_pre md) // Est. }
        rewrite -hDbf. apply: (IH md (hf md) _ z). apply: hgood. exact: hmd.
     ++ exact: sum_ord_in_fset.
     ++ rewrite hsd0 codomm0 sizes0 /= mul0r.
        by rewrite GRing.add0r.
Qed.

(* FORGE oracle case (resolve form; the [match b] blocks reduction) *)
Lemma DIG_forge (b : bool) {T' : choiceType}
    (x : (M × FxSig N R)) (k : 'bool -> raw_code T')
    (IH : forall (v : 'bool) (h : heap), D_inv h -> forall z : T',
       `| dfst (Pr_code (code_link (k v) (G4M b)) h) z
        - dfst (Pr_code (code_link (k v) (G4C b)) h) z | <= Db h)
    (h : heap) (hinv : D_inv h) (z : T') :
  `| dfst (Pr_code (bind (resolve (G4M b) (fgo N M R) x) (fun v => code_link (k v) (G4M b))) h) z
   - dfst (Pr_code (bind (resolve (G4C b) (fgo N M R) x) (fun v => code_link (k v) (G4C b))) h) z | <= Db h.
Proof.
case: x => m sg.
case: b IH => [|] IH; last first.
{ (* b = false: both oracles still run the full forge bookkeeping and only
     the final [ret] is [false].  The G4m body reads [fc,Lst,Llog,Lrom]; the
     G4c body reads two extra locations ([Lrt],[Lsd]) that change neither the
     heap nor the verdict.  Both reach [code_link (k false) (forge_fin …)] at
     the SAME [ff md], so each side differs by at most [Db (ff md) <= Db h].
     We walk each body once (game-free, parametric in [K] and heap), then
     close by [IH] + [Db] monotonicity.  No reliance on [/=] collapsing the
     body. *)
  rewrite (Rg4m_forge false m sg) (Rg4c_forge false m sg).
  (* step lemma for the G4m [b=false] body (4 gets, verdict [false]) *)
  have fstepM : forall (K : 'bool -> raw_code T') (hh : heap),
      dfst (Pr_code
        (fc ← get fx_fcnt_loc ;;
         b0 ← (#assert (fc < q_f)%N ;;
               v0 ← get Lst ;;
               #assert v0 as vSome ;;
               _ ← get (fx_log_loc M) ;;
               mp ← get Lrom ;;
               md ← (match getm mp (sg.1.2, ((getSome v0 vSome).1, (sg.1.1, m))) with
                     | Some d => ret d
                     | None => d ← dDu ;; ret d
                     end) ;;
               #put Lrom := setm mp (sg.1.2, ((getSome v0 vSome).1, (sg.1.1, m))) md ;;
               #put fx_fcnt_loc := fc.+1 ;;
               ret false) ;;
         K b0) hh) z
      = if (fcc hh < q_f)%N then
          match get_heap hh Lst with
          | None => 0
          | Some st0 =>
            match getm (rom hh) (fgpt PP N M R st0 m sg) with
            | Some md =>
                dfst (Pr_code (K false)
                  (forge_fin PP N Dfin M R hh (fcc hh) (rom hh)
                     (fgpt PP N M R st0 m sg) md)) z
            | None =>
                (\dlet_(md <- Pr_fst dDu)
                   dfst (Pr_code (K false)
                     (forge_fin PP N Dfin M R hh (fcc hh) (rom hh)
                        (fgpt PP N M R st0 m sg) md))) z
            end
          end
        else 0.
  { move=> K hh. cbn [bind]. rewrite Pr_code_get.
    case E1: ((fcc hh < q_f)%N); last by rewrite assertD_false dPr_bind_fail.
    rewrite assertD_true. cbn [bind]. rewrite Pr_code_get.
    case E2: (get_heap hh Lst) => [st0|]; last first.
    { by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
    rewrite -[isSome (Some st0)]/true assertD_true. cbn [getSome bind].
    rewrite 2!Pr_code_get.
    rewrite -[(sg.1.2, (st0.1, (sg.1.1, m)))]/(fgpt PP N M R st0 m sg).
    case E3: (getm (rom hh) (fgpt PP N M R st0 m sg)) => [md|].
    - cbn [bind]. rewrite 2!Pr_code_put. by rewrite forge_finE.
    - rewrite bind_assoc. cbn [bind]. rewrite bind_assoc dPr_dist.
      apply: eq_dlet_at => md. cbn [bind]. rewrite 2!Pr_code_put.
      by rewrite forge_finE. }
  (* step lemma for the G4c [b=false] body (6 gets, verdict [false]) *)
  have fstepC : forall (K : 'bool -> raw_code T') (hh : heap),
      dfst (Pr_code
        (fc ← get fx_fcnt_loc ;;
         b0 ← (#assert (fc < q_f)%N ;;
               v0 ← get Lst ;;
               #assert v0 as vSome ;;
               _ ← get (fx_log_loc M) ;;
               mp ← get Lrom ;;
               _ ← get Lrt ;;
               _ ← get Lsd ;;
               md ← (match getm mp (sg.1.2, ((getSome v0 vSome).1, (sg.1.1, m))) with
                     | Some d => ret d
                     | None => d ← dDu ;; ret d
                     end) ;;
               #put Lrom := setm mp (sg.1.2, ((getSome v0 vSome).1, (sg.1.1, m))) md ;;
               #put fx_fcnt_loc := fc.+1 ;;
               ret false) ;;
         K b0) hh) z
      = if (fcc hh < q_f)%N then
          match get_heap hh Lst with
          | None => 0
          | Some st0 =>
            match getm (rom hh) (fgpt PP N M R st0 m sg) with
            | Some md =>
                dfst (Pr_code (K false)
                  (forge_fin PP N Dfin M R hh (fcc hh) (rom hh)
                     (fgpt PP N M R st0 m sg) md)) z
            | None =>
                (\dlet_(md <- Pr_fst dDu)
                   dfst (Pr_code (K false)
                     (forge_fin PP N Dfin M R hh (fcc hh) (rom hh)
                        (fgpt PP N M R st0 m sg) md))) z
            end
          end
        else 0.
  { move=> K hh. cbn [bind]. rewrite Pr_code_get.
    case E1: ((fcc hh < q_f)%N); last by rewrite assertD_false dPr_bind_fail.
    rewrite assertD_true. cbn [bind]. rewrite Pr_code_get.
    case E2: (get_heap hh Lst) => [st0|]; last first.
    { by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
    rewrite -[isSome (Some st0)]/true assertD_true. cbn [getSome bind].
    rewrite 4!Pr_code_get.
    rewrite -[(sg.1.2, (st0.1, (sg.1.1, m)))]/(fgpt PP N M R st0 m sg).
    case E3: (getm (rom hh) (fgpt PP N M R st0 m sg)) => [md|].
    - cbn [bind]. rewrite 2!Pr_code_put. by rewrite forge_finE.
    - rewrite bind_assoc. cbn [bind]. rewrite bind_assoc dPr_dist.
      apply: eq_dlet_at => md. cbn [bind]. rewrite 2!Pr_code_put.
      by rewrite forge_finE. }
  (* Apply the step lemmas with the continuation game supplied EXPLICITLY
     (no abstract [K] for [rewrite] to higher-order unify — that HO match
     over the large forge body is multi-minute; giving [K] makes it fast). *)
  rewrite (fstepM (fun v => code_link (k v) (G4M false)) h)
          (fstepC (fun v => code_link (k v) (G4C false)) h).
  case Ef: ((fcc h < q_f)%N); last first.
  { rewrite subrr normr0. exact: Db_ge0. }
  case Est: (get_heap h Lst) => [st|]; last first.
  { rewrite subrr normr0. exact: Db_ge0. }
  have hinvE := hinv. case: hinv => di dp dsz dh df.
  set ff := fun md => forge_fin PP N Dfin M R h (fcc h) (rom h)
                        (fgpt PP N M R st m sg) md.
  have ffrom : forall md, rom (ff md) = setm (rom h) (fgpt PP N M R st m sg) md.
  { move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lrom) // get_set_heap_eq. }
  have ffsd : forall md, sdm (ff md) = sdm h.
  { move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lsd) // (get_set_heap_neq _ _ _ Lsd). }
  have fftb : forall md, tbl (ff md) = tbl h.
  { move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lrt) // (get_set_heap_neq _ _ _ Lrt). }
  have ffst : forall md, get_heap (ff md) Lst = get_heap h Lst.
  { move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lst) // (get_set_heap_neq _ _ _ Lst). }
  have ffhc : forall md, hcc (ff md) = hcc h.
  { move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ fx_hcnt_loc) // (get_set_heap_neq _ _ _ fx_hcnt_loc). }
  have fffc : forall md, fcc (ff md) = (fcc h).+1.
  { move=> md. by rewrite /ff forge_finE get_set_heap_eq. }
  have ffinv : forall md,
      (getm (tbl h) (sg.1.1, m) != Some sg.1.2 -> md \notin codomm (sdm h)) ->
      D_inv (ff md).
  { move=> md Hmd. split.
    - move=> x0 vv. rewrite ffrom ffsd fftb setmE.
      case: eqP => [hx0 hsome hguard | hne hsome hguard].
      + case: hsome => hvv. rewrite -hvv. apply: Hmd.
        move: hguard. by rewrite hx0 /fgpt /=.
      + exact: (di x0 vv hsome hguard).
    - move=> hst. rewrite ffsd. apply: dp. by rewrite -(ffst md).
    - by rewrite /dig_sz ffsd.
    - by rewrite ffhc.
    - by rewrite fffc Ef. }
  have hBn0 : (0 < Bn h)%N.
  { rewrite /Bn addn_gt0. apply/orP; left.
    rewrite addn_gt0. apply/orP; right. by rewrite subn_gt0 Ef. }
  have hqf : (0 < q_f - fcc h)%N by rewrite subn_gt0.
  have hBnff : forall md, Bn (ff md) = (Bn h).-1.
  { move=> md. rewrite /Bn ffhc fffc ffst Est /= !addn0 subnS -!subn1.
    by rewrite addnBA. }
  have ffDb : forall md, getm (rom h) (fgpt PP N M R st m sg) = None ->
                Db (ff md) = n_max%:R * (Bn h).-1%:R / d_n.+1%:R.
  { move=> md hx. by rewrite /Db hBnff. }
  case Erx: (getm (rom h) (fgpt PP N M R st m sg)) => [md0|].
  * (* rom hit: [ff md0] rewrites [rom] to the same value, so [D_inv]
       holds and [k false]'s output differs by [<= Db (ff md0) <= Db h]. *)
    have hromeq : rom (ff md0) = rom h.
    { rewrite ffrom. apply/eq_fmap => x0. rewrite setmE.
      by case: eqP => [-> | //]. }
    have hinvf : D_inv (ff md0).
    { split.
      - move=> x0 vv. rewrite hromeq ffsd fftb. exact: di.
      - move=> hst. rewrite ffsd. apply: dp. by rewrite -(ffst md0).
      - by rewrite /dig_sz ffsd.
      - by rewrite ffhc.
      - by rewrite fffc Ef. }
    apply: le_trans (IH false (ff md0) hinvf z) _.
    rewrite /Db. apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
    apply: ler_wpM2l; first by rewrite ler0n.
    rewrite ler_nat hBnff. exact: leq_pred.
  * (* rom miss: charge fresh md via [uniform_split_le].  Verdict is
       [false] on BOTH sides (no [coll_ev] term), so the good-md branch is
       a direct [IH] bound; the [size (codomm sd)] bad-md term is charged. *)
    have hkey : Pr_fst dDu = \dlet_(r <- (uniform d_n.+1).π2) dunit r.
    { by rewrite /rp_dPfx Pr_fst_sample; apply: eq_dlet => r; rewrite Pr_fst_ret. }
    rewrite hkey.
    rewrite [in X in `| _ - X|%R]dlet_dlet_ext [in X in `| X - _|%R]dlet_dlet_ext.
    under [in X in `| X - _|%R]eq_dlet => r do rewrite dlet_unit_ext.
    under [in X in `| _ - X|%R]eq_dlet => r do rewrite dlet_unit_ext.
    apply: le_trans
      (uniform_split_le d_n
         (fun md : Dfin =>
            dfst (Pr_code (code_link (k false) (G4M false)) (ff md)))
         (fun md : Dfin =>
            dfst (Pr_code (code_link (k false) (G4C false)) (ff md)))
         (fun md : Dfin => md \in codomm (sdm h)) z
         (n_max%:R * (Bn h).-1%:R / d_n.+1%:R) (size (codomm (sdm h))) _ _ _) _.
    -- by rewrite divr_ge0 ?ler0n // mulr_ge0 ?ler0n.
    -- move=> md hmd.
       have hinvf : D_inv (ff md). { apply: ffinv => _. exact: hmd. }
       have hDbf : Db (ff md) = n_max%:R * (Bn h).-1%:R / d_n.+1%:R.
       { by rewrite ffDb. }
       rewrite -hDbf. exact: (IH false (ff md) hinvf z).
    -- exact: sum_ord_in_fset.
    -- rewrite -mulrDl.
       apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
       rewrite -[Bn h](prednK hBn0) /=.
       rewrite -natr1 mulrDr mulr1 addrC.
       apply: lerD; first exact: lexx.
       rewrite ler_nat. exact: dsz. }
rewrite (Rg4m_forge true) (Rg4c_forge true).
(* instantiate the step lemmas' continuations AND heap EXPLICITLY: an
   implicit [k]/[h] forces [rewrite] into a multi-minute higher-order match
   against the large forge body (the documented [forge3_step]/[forge4c_step]
   pathology). *)
rewrite (Sfg4m m sg (k := fun v => code_link (k v) (G4M true)) (h := h)).
rewrite (Sfg4c m sg (k := fun v => code_link (k v) (G4C true)) (h := h)).
case Ef: ((fcc h < q_f)%N); last first.
{ rewrite subrr normr0. exact: Db_ge0. }
case Est: (get_heap h Lst) => [st|]; last first.
{ rewrite subrr normr0. exact: Db_ge0. }
have hinvE := hinv. case: hinv => di dp dsz dh df.
set ff := fun md => forge_fin PP N Dfin M R h (fcc h) (rom h)
                      (fgpt PP N M R st m sg) md.
have ffrom : forall md, rom (ff md) = setm (rom h) (fgpt PP N M R st m sg) md.
{ move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lrom) // get_set_heap_eq. }
have ffsd : forall md, sdm (ff md) = sdm h.
{ move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lsd) // (get_set_heap_neq _ _ _ Lsd). }
have fftb : forall md, tbl (ff md) = tbl h.
{ move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lrt) // (get_set_heap_neq _ _ _ Lrt). }
have ffst : forall md, get_heap (ff md) Lst = get_heap h Lst.
{ move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ Lst) // (get_set_heap_neq _ _ _ Lst). }
have ffhc : forall md, hcc (ff md) = hcc h.
{ move=> md. by rewrite /ff forge_finE (get_set_heap_neq _ _ _ fx_hcnt_loc) // (get_set_heap_neq _ _ _ fx_hcnt_loc). }
have fffc : forall md, fcc (ff md) = (fcc h).+1.
{ move=> md. by rewrite /ff forge_finE get_set_heap_eq. }
have ffinv : forall md,
    (getm (tbl h) (sg.1.1, m) != Some sg.1.2 -> md \notin codomm (sdm h)) ->
    D_inv (ff md).
{ move=> md Hmd. split.
  - move=> x0 vv. rewrite ffrom ffsd fftb setmE.
    case: eqP => [hx0 hsome hguard | hne hsome hguard].
    + case: hsome => hvv. rewrite -hvv. apply: Hmd.
      move: hguard. by rewrite hx0 /fgpt /=.
    + exact: (di x0 vv hsome hguard).
  - move=> hst. rewrite ffsd. apply: dp. by rewrite -(ffst md).
  - by rewrite /dig_sz ffsd.
  - by rewrite ffhc.
  - by rewrite fffc Ef. }
have hqf : (0 < q_f - fcc h)%N by rewrite subn_gt0.
have hBn0 : (0 < Bn h)%N.
{ rewrite /Bn addn_gt0. apply/orP; left.
  rewrite addn_gt0. apply/orP; right. by rewrite subn_gt0 Ef. }
have hBnff : forall md, Bn (ff md) = (Bn h).-1.
{ move=> md. rewrite /Bn ffhc fffc ffst Est /= !addn0 subnS -!subn1.
  by rewrite addnBA. }
have ffDb : forall md, getm (rom h) (fgpt PP N M R st m sg) = None ->
              Db (ff md) = n_max%:R * (Bn h).-1%:R / d_n.+1%:R.
{ move=> md hx. by rewrite /Db hBnff. }
case Erx: (getm (rom h) (fgpt PP N M R st m sg)) => [md0|].
* (* rom hit: [coll_ev] is killed by [dig_inv]; verdicts agree *)
  have hcoll : ~~ coll_ev Dfin M R (sdm h) (tbl h) (sg.1.1, m) sg.1.2 md0.
  { rewrite /coll_ev negb_and negbK.
    case: (eqVneq (tbl h (sg.1.1, m)) (Some sg.1.2)) => [Etbc|Etbc].
    - apply/orP; right. by apply/eqP.
    - apply/orP; left.
      apply: (di (fgpt PP N M R st m sg) md0 Erx).
      rewrite /fgpt /=. exact: Etbc. }
  rewrite (negbTE hcoll) andbT.
  (* rom hit: [ff md0] rewrites [rom] to the SAME value [md0], so [rom]
     (hence [dig_inv]) is unchanged and [D_inv (ff md0)] follows directly. *)
  have hromeq : rom (ff md0) = rom h.
  { rewrite ffrom. apply/eq_fmap => x0. rewrite setmE.
    case: eqP => [-> | //]. by rewrite Erx. }
  have hinvf : D_inv (ff md0).
  { split.
    - move=> x0 vv. rewrite hromeq ffsd fftb. exact: di.
    - move=> hst. rewrite ffsd. apply: dp. by rewrite -(ffst md0).
    - by rewrite /dig_sz ffsd.
    - by rewrite ffhc.
    - by rewrite fffc Ef. }
  apply: le_trans (IH _ (ff md0) hinvf z) _.
  rewrite /Db. apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  apply: ler_wpM2l; first by rewrite ler0n.
  rewrite ler_nat hBnff. exact: leq_pred.
* (* rom miss: charge the fresh md via uniform_split_le *)
  have hkey : Pr_fst dDu = \dlet_(r <- (uniform d_n.+1).π2) dunit r.
  { by rewrite /rp_dPfx Pr_fst_sample; apply: eq_dlet => r; rewrite Pr_fst_ret. }
  rewrite hkey.
  rewrite [in X in `| _ - X|%R]dlet_dlet_ext [in X in `| X - _|%R]dlet_dlet_ext.
  under [in X in `| X - _|%R]eq_dlet => r do rewrite dlet_unit_ext.
  under [in X in `| _ - X|%R]eq_dlet => r do rewrite dlet_unit_ext.
  apply: le_trans
    (uniform_split_le d_n
       (fun md : Dfin =>
          dfst (Pr_code (code_link
             (k (fgverd PP N Dfin M R F Tl Hgrind Htree w l S_wn h_sf st
                   (get_heap h (fx_log_loc M)) m sg md)) (G4M true)) (ff md)))
       (fun md : Dfin =>
          dfst (Pr_code (code_link
             (k (fgverd PP N Dfin M R F Tl Hgrind Htree w l S_wn h_sf st
                   (get_heap h (fx_log_loc M)) m sg md
                 && ~~ coll_ev Dfin M R (sdm h) (tbl h) (sg.1.1, m) sg.1.2 md))
                (G4C true)) (ff md)))
       (fun md : Dfin => md \in codomm (sdm h)) z
       (n_max%:R * (Bn h).-1%:R / d_n.+1%:R) (size (codomm (sdm h))) _ _ _) _.
  -- by rewrite divr_ge0 ?ler0n // mulr_ge0 ?ler0n.
  -- (* good md: not in codomm sd, so coll_ev false, verdicts agree *)
     move=> md hmd.
     have hcoll : ~~ coll_ev Dfin M R (sdm h) (tbl h) (sg.1.1, m) sg.1.2 md.
     { by rewrite /coll_ev negb_and (negbTE hmd). }
     rewrite (negbTE hcoll) andbT.
     have hinvf : D_inv (ff md).
     { apply: ffinv => _. exact: hmd. }
     have hDbf : Db (ff md) = n_max%:R * (Bn h).-1%:R / d_n.+1%:R.
     { by rewrite ffDb. }
     rewrite -hDbf. exact: (IH _ (ff md) hinvf z).
  -- exact: sum_ord_in_fset.
  -- rewrite -mulrDl.
     apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
     rewrite -[Bn h](prednK hBn0) /=.
     rewrite -natr1 mulrDr mulr1 addrC.
     apply: lerD; first exact: lexx.
     rewrite ler_nat. exact: dsz.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The identical-until-bad induction *)

Lemma DIG_core (b : bool) {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IG c) :
  forall (h : heap), D_inv h -> forall z,
    `| dfst (Pr_code (code_link c (G4M b)) h) z
     - dfst (Pr_code (code_link c (G4C b)) h) z |
    <= Db h.
Proof.
induction VA as [a | o x k Ho Hk IH | lo k Hl Hk IH
                | lo v k Hl Hk IH | op k Hk IH].
- (* ret *)
  move=> h hinv z. cbn [code_link].
  rewrite subrr normr0. exact: Db_ge0.
- (* opr: dispatch to the per-oracle lemmas *)
  move=> h hinv z. cbn [code_link].
  fmap_invert Ho.
  + rewrite (Rg4m_gen b) (Rg4c_gen b). exact: (DIG_gen b x k IH h hinv z).
  + rewrite (Rg4m_sign b) (Rg4c_sign b). exact: (DIG_sign b x k IH h hinv z).
  + rewrite (Rg4m_hash b) (Rg4c_hash b). exact: (DIG_hash b x k IH h hinv z).
  + exact: (DIG_forge b x k IH h hinv z).
- (* getr (adversary location) *)
  move=> h hinv z. cbn [code_link].
  case/and5P: (dadvloc_neq _ Hl) => n1 n2 n3 n4 /and5P[n5 n6 n7 n8 n9].
  rewrite 2!Pr_code_get. exact: (IH _ h hinv z).
- (* putr (adversary location) *)
  move=> h hinv z. cbn [code_link].
  case/and5P: (dadvloc_neq _ Hl) => n1 n2 n3 n4 /and5P[n5 n6 n7 n8 n9].
  rewrite 2!Pr_code_put.
  have hinv' : D_inv (set_heap h lo v).
  { case: hinv => di dp dsz dh df. split.
    - move=> x0 v0. rewrite /dig_inv.
      rewrite (get_set_heap_neq _ _ _ _ (neqC n5)).
      rewrite (get_set_heap_neq _ _ _ _ (neqC n7)).
      rewrite (get_set_heap_neq _ _ _ _ (neqC n9)).
      exact: di.
    - move=> hst. rewrite (get_set_heap_neq _ _ _ _ (neqC n9)).
      apply: dp. by rewrite (get_set_heap_neq _ _ _ _ (neqC n1)) in hst.
    - rewrite /dig_sz (get_set_heap_neq _ _ _ _ (neqC n9)). exact: dsz.
    - by rewrite (get_set_heap_neq _ _ _ _ (neqC n6)).
    - by rewrite (get_set_heap_neq _ _ _ _ (neqC n8)). }
  have hDb : Db (set_heap h lo v) = Db h.
  { rewrite /Db /Bn.
    rewrite (get_set_heap_neq _ _ _ _ (neqC n6)).
    rewrite (get_set_heap_neq _ _ _ _ (neqC n8)).
    rewrite (get_set_heap_neq _ _ _ _ (neqC n1)).
    by rewrite (get_set_heap_neq _ _ _ _ (neqC n5)). }
  rewrite -hDb. exact: (IH (set_heap h lo v) hinv' z).
- (* sampler *)
  move=> h hinv z. cbn [code_link].
  rewrite 2!dPr_sample.
  apply: dlet_diff_le; first exact: Db_ge0.
  move=> a. exact: (IH a h hinv z).
Qed.

End DigAdversary.

(* ------------------------------------------------------------------ *)
(** ** The quantitative identical-until-bad bound *)

(* The assembly goes only through proven equations ([Pr_Pr_code],
   [resolve_link]) and the opaque [DIG_core]; keep the kernel from
   normalising the composition/evaluation machinery while checking it. *)
Opaque code_link Pr_code resolve.

Theorem DIG_diff (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) (I_G0fL PP N Dfin M R) A_export A) :
  (Adv (G4M b) (G4C b) A <= n_max%:R * ((q_h + q_f)%:R / d_n.+1%:R) :> Axioms.R)%R.
Proof.
apply: (Adv_nom_ind _ _ _ (I_G0fL PP N Dfin M R)
          (fun x : Axioms.R => x <= n_max%:R * ((q_h + q_f)%:R / d_n.+1%:R))) => //.
move=> A' LA' VA' _ sep1 sep2.
rewrite /AdvantageE.
have hRUN : fhas A_export RUN by fmap_solve.
have VC := valid_resolve _ _ _ _ RUN tt VA' hRUN.
have sepL : fseparate LA' (loc (G4M false)).
{ by move: sep1; rewrite (loc_g4m_eq b). }
have inv0 : D_inv empty_heap.
{ split.
  - move=> x v.
    have -> : get_heap empty_heap (fx_rom_loc PP N Dfin M R) = emptym by [].
    by rewrite emptymE.
  - move=> _. by [].
  - rewrite /dig_sz.
    have -> : get_heap empty_heap (fx_sd_loc Dfin) = emptym by [].
    by rewrite codomm0 sizes0.
  - by [].
  - by []. }
(* Identify the closed-form budget at the empty heap up front, so the
   numeric simplification is separated from the (heavy) conversion of the
   resolved package against [DIG_core]. *)
have hDb0 : Db empty_heap = n_max%:R * ((q_h + q_f)%:R / d_n.+1%:R).
{ rewrite /Db /Bn.
  have -> : get_heap empty_heap (fx_st_loc PP N) = None by [].
  have -> : get_heap empty_heap fx_hcnt_loc = 0%N by [].
  have -> : get_heap empty_heap fx_fcnt_loc = 0%N by [].
  have -> : get_heap empty_heap (fx_rom_loc PP N Dfin M R) = emptym by [].
  by rewrite domm0 sizes0 2!subn0 /= addn0 mulrA. }
rewrite 2!Pr_Pr_code 2!resolve_link -hDb0.
exact: (DIG_core LA' sepL b VC empty_heap inv0 true).
Qed.

End FXMSSDigestBound.
