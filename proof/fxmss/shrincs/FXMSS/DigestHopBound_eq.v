Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq Toolkit.ROPlus Toolkit.Reprogram.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.PRFHop FXMSS.ReproHop FXMSS.DigestHop
  FXMSS.DigestHopBound_g4indep.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FXMSSDigestBound.

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

Local Notation G3C b := (ReproHop.G3c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4M b := (G4m PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4C b := (G4c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).

Local Notation Lsd := (fx_sd_loc Dfin).
Local Notation IG := (I_G0fL PP N Dfin M R).

(** M5: the lifted leaf-id validation + slot selection (Games.v). *)
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).

(** M5: fully-[@]-applied [sign4_step] so we can rewrite it with its
    continuation [k] (and heap [h]) given EXPLICITLY.  When the induction
    hypothesis has already rewritten the G3c LHS into a
    [dfst (Pr_code (code_link (k _) (G4M b)) _)] term, a bare
    [rewrite sign4_step] scans leftmost-outermost and tries to unify that
    [code_link _ (G4M b)] subterm against [bind (sign4_body _) ?k] — a
    multi-minute conversion of the giant game term (the [Opaque] flag does
    NOT stop ssr's rewrite unifier).  Grounding [k]/[h] makes the pattern
    match only the intended [sign4_body] occurrence.  Same lever diff.v
    uses for [forge3_step] (DIGEST_OPT_NOTES.md UPDATE 2). *)
Local Notation Ssign :=
  (@sign4_step w l PP N Dfin M R F Tl Hgrind Htree dR dDu S_wn c_max h_sf q_s).
(** Fully-[@]-applied [sign4_body] (its section variables), so the
    [fill_peel_at] continuation is written in the exact shape that
    [resolve_g4m_sign] produces. *)
Local Notation sbody :=
  (@sign4_body w l PP N Dfin M R F Tl Hgrind Htree dR dDu S_wn c_max h_sf q_s).

(** [rp_dPfx] is lossless (uniform on a nonempty finite type). *)
Lemma dDu_ll : LosslessCode dDu.
Proof. exact _. Qed.

(** [fill_code] over [js] with base [setm m0 j y], averaged through a
    continuation that [unionm]s with a prefix [sd0] whose domain is
    disjoint from [j::js], equals the same with the [setm] absorbed
    into the prefix.  Proved by induction on [js]; the inner [setm]s
    commute ([setmC]) and the resulting maps are extensionally
    equal. *)
Lemma fill_union_setm (js : seq nat) (j : nat) (y : Dfin)
    {Tz : choiceType} (G0 : chMap 'nat Dfin -> {distr Tz / Axioms.R})
    (z : Tz) :
  forall (sd0 m0 : chMap 'nat Dfin),
    j \notin js ->
    j \notin domm sd0 ->
    (forall k, k \in js -> k \notin domm sd0) ->
    (\dlet_(rest <- Pr_fst (fill_code Dfin dDu js (setm m0 j y)))
        G0 (unionm sd0 rest)) z
    = (\dlet_(rest <- Pr_fst (fill_code Dfin dDu js m0))
          G0 (unionm (setm sd0 j y) rest)) z.
Proof.
elim: js => [|a js IH] sd0 m0 hj hjd hkd.
- rewrite /=. rewrite 2!Pr_fst_ret 2!dlet_unit_ext.
  congr (G0 _ z).
  have hsd0j : sd0 j = None.
  { by apply/dommPn. }
  apply/eq_fmap => k. rewrite 2!unionmE.
  rewrite (setmE m0) (setmE sd0).
  case: (eqVneq k j) => [-> | kj].
  + rewrite hsd0j /=.
    by case: (m0 j).
  + by case: (sd0 k).
- have hcons : forall (m : chMap 'nat Dfin),
    fill_code Dfin dDu (a :: js) m = (y ← dDu ;; fill_code Dfin dDu js (setm m a y)).
  { by []. }
  rewrite (hcons (setm m0 j y)) (hcons m0).
  rewrite Pr_fst_bind.
  rewrite Pr_fst_bind.
  rewrite (dlet_dlet_ext (t := Pr_fst dDu)).
  rewrite [in X in _ = X](dlet_dlet_ext (t := Pr_fst dDu)).
  apply: eq_dlet_at => v.
  have ha : a \notin domm sd0 by apply: hkd; rewrite inE eqxx.
  have hja : j != a by move: hj; rewrite inE negb_or => /andP[].
  have hjjs : j \notin js by move: hj; rewrite inE negb_or => /andP[].
  rewrite (@setmC _ _ m0 j y a v hja).
  apply: (IH sd0 (setm m0 a v) hjjs hjd).
  move=> k hk. apply: hkd. by rewrite inE hk orbT.
Qed.

(** [fill_code] inherits losslessness from [dDu]. *)
Lemma fill_code_ll (js : seq nat) (m0 : chMap 'nat Dfin) :
  LosslessCode (fill_code Dfin dDu js m0).
Proof.
elim: js m0 => [|j js IH] m0.
- exact: Lossless_ret.
- have -> : fill_code Dfin dDu (j :: js) m0
    = (r ← sample uniform d_n.+1 ;; fill_code Dfin dDu js (setm m0 j r))
    by [].
  by apply: Lossless_sample.
Qed.

(** ** dlet_dletC_at: pointwise Fubini for sub-distributions (ported
    from [.leaf-scratch/M5_lift_probe.v], via the baseline
    [__admitted__interchange_psum] — the same allowed assumption the
    whole Adv layer already rests on; no new axiom). *)
Lemma dlet_dletC_at {A B C : choiceType}
    (mu : {distr A / Axioms.R}) (nu : {distr B / Axioms.R})
    (Fc : A -> B -> {distr C / Axioms.R}) (z : C) :
  (\dlet_(a <- mu) \dlet_(b <- nu) Fc a b) z
  = (\dlet_(b <- nu) \dlet_(a <- mu) Fc a b) z.
Proof.
rewrite 2!dletE.
have -> : psum (fun a => mu a * (\dlet_(b <- nu) Fc a b) z)
        = psum (fun a => psum (fun b => mu a * (nu b * Fc a b z))).
{ apply: eq_psum => a. by rewrite dletE -psumZ ?ge0_mu. }
have -> : psum (fun b => nu b * (\dlet_(a <- mu) Fc a b) z)
        = psum (fun b => psum (fun a => mu a * (nu b * Fc a b z))).
{ apply: eq_psum => b. rewrite dletE -psumZ ?ge0_mu //.
  apply: eq_psum => a. by rewrite mulrCA. }
apply: __admitted__interchange_psum.
- move=> a. apply: summableZ. exact: (summable_mlet (fun b => Fc a b) nu z).
- apply: (eq_summable (S1 := fun a => mu a * (\dlet_(b <- nu) Fc a b) z)).
  + move=> a /=. by rewrite dletE -psumZ ?ge0_mu.
  + exact: (summable_mlet (fun a => \dlet_(b <- nu) Fc a b) mu z).
Qed.

(** ** fill_peel_at: peel an ARBITRARY slot [j] off the eager i.i.d.
    fill (ported from the probe; the head-only [fill_peel] is the
    special case [j = head]).  Reading any one unconsumed slot of a
    presampled table = lazily sampling it — the exchangeability that
    lets the lifted DIG_eq couple the lazy digest of SIGN(zi) with the
    per-leaf presampled [sd[flidx zi]] in ADAPTIVE order. *)
Lemma fill_peel_at {Tz : choiceType} (j : nat) :
  forall (js : seq nat) (sd0 : chMap 'nat Dfin)
         (G0 : chMap 'nat Dfin -> {distr Tz / Axioms.R}) (z : Tz),
  j \in js -> uniq js ->
  (forall k, k \in js -> k \notin domm sd0) ->
  (\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym)) G0 (unionm sd0 rest)) z
  = (\dlet_(y <- Pr_fst dDu)
       \dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem j js) emptym))
          G0 (unionm (setm sd0 j y) rest)) z.
Proof.
elim=> [|a js IH] sd0 G0 z hj huniq hkd; first by move: hj; rewrite in_nil.
move: huniq => /andP[hanotin huniq].
have hconsL : fill_code Dfin dDu (a :: js) emptym
  = (y ← dDu ;; fill_code Dfin dDu js (setm emptym a y)) by [].
rewrite hconsL Pr_fst_bind (dlet_dlet_ext (t := Pr_fst dDu)).
have had : a \notin domm sd0 by apply: hkd; rewrite inE eqxx.
case: (eqVneq a j) => [<- | haj].
- (* j = a : head peel, no swap needed *)
  apply: eq_dlet_at => y.
  have hrem : rem a (a :: js) = js by rewrite /= eqxx.
  rewrite hrem.
  apply: (fill_union_setm js a y G0 z sd0 emptym hanotin had).
  move=> k hk. apply: hkd. by rewrite inE hk orbT.
- (* j != a : prefix-absorb, IH, dlet swap, refold *)
  have hj' : j \in js.
  { move: hj; rewrite inE => /orP[/eqP e|//]. by move: haj; rewrite e eqxx. }
  have hrem : rem j (a :: js) = a :: rem j js by rewrite /= (negbTE haj).
  transitivity
    ((\dlet_(v <- Pr_fst dDu)
        \dlet_(y <- Pr_fst dDu)
          \dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem j js) emptym))
             G0 (unionm (setm (setm sd0 a v) j y) rest)) z).
  { apply: eq_dlet_at => v.
    rewrite (fill_union_setm js a v G0 z sd0 emptym hanotin had);
      last by move=> k hk; apply: hkd; rewrite inE hk orbT.
    apply: (IH (setm sd0 a v) G0 z hj' huniq).
    move=> k hk. rewrite domm_set in_fsetU1 negb_or.
    apply/andP; split.
    - by apply/eqP => e; move: hanotin; rewrite -e hk.
    - by apply: hkd; rewrite inE hk orbT. }
  transitivity
    ((\dlet_(y <- Pr_fst dDu)
        \dlet_(v <- Pr_fst dDu)
          \dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem j js) emptym))
             G0 (unionm (setm (setm sd0 a v) j y) rest)) z).
  { exact: (dlet_dletC_at (Pr_fst dDu) (Pr_fst dDu)
      (fun v y => \dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem j js) emptym))
                    G0 (unionm (setm (setm sd0 a v) j y) rest)) z). }
  apply: eq_dlet_at => y.
  rewrite hrem.
  have hconsR : fill_code Dfin dDu (a :: rem j js) emptym
    = (v ← dDu ;; fill_code Dfin dDu (rem j js) (setm emptym a v)) by [].
  rewrite hconsR Pr_fst_bind (dlet_dlet_ext (t := Pr_fst dDu)).
  apply: eq_dlet_at => v.
  have hjrem : forall k, k \in rem j js -> (k != j) && (k \in js).
  { move=> k hk. by move: hk; rewrite (mem_rem_uniq _ huniq) inE => /andP[-> ->]. }
  rewrite (@setmC _ _ sd0 a v j y haj).
  rewrite (fill_union_setm (rem j js) a v G0 z (setm sd0 j y) emptym) //.
  - by apply/negP => /hjrem /andP[_ hin]; move: hanotin; rewrite hin.
  - rewrite domm_set in_fsetU1 negb_or haj /=. exact: had.
  - move=> k hk. move: (hjrem k hk) => /andP[hkj hkjs].
    rewrite domm_set in_fsetU1 negb_or hkj /=.
    by apply: hkd; rewrite inE hkjs orbT.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The adversary section: the two inductions *)

Section DigAdversary.

Context (LA : Locations).
Context (sepL : fseparate LA (loc (G4M false))).

(** The adversary's locations are disjoint from the 9 game locations.
    M5: [fx_q_loc] counter deleted; the used-set [fx_used_loc] (410) is
    the new location, occupying the SAME [G4_locs] slot (position 2)
    that [fx_q_loc] held; [Lsd] stays last. *)
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

(** Averaging a [dDu]-draw over a constant collapses (losslessness). *)
Lemma dlet_dDu_const {U : choiceType} (nu : {distr U / Axioms.R}) (u : U) :
  (\dlet_(_ <- Pr_fst dDu) nu) u = nu u.
Proof. by rewrite (Pr_fstC dDu_ll). Qed.

(** [sign_fin]/[forge_fin]/[hash_fin] are heap-[Lsd]-independent and
    leave [Lsd] untouched; the lifted [sign_fin] additionally sets the
    used-set [fx_used_loc]. *)
Lemma sfin_h_lem (h : heap) st qv sc us lg mp tb mz r md (X : chMap 'nat Dfin) :
  (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
     (set_heap h Lsd X) st qv sc us lg mp tb mz r md).2
  = set_heap (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
      h st qv sc us lg mp tb mz r md).2 Lsd X.
Proof. rewrite sign_finE /=.
  case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
    rewrite !(set_heap_commut _ Lsd) //. Qed.

Lemma sfin_r_lem (h : heap) st qv sc us lg mp tb mz r md (X : chMap 'nat Dfin) :
  (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
     (set_heap h Lsd X) st qv sc us lg mp tb mz r md).1
  = (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
      h st qv sc us lg mp tb mz r md).1.
Proof. rewrite sign_finE /=.
  by case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|]. Qed.

Lemma sfin_st_lem (h : heap) st qv sc us lg mp tb mz r md :
  get_heap (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
    h st qv sc us lg mp tb mz r md).2 (fx_st_loc PP N)
  = get_heap h (fx_st_loc PP N).
Proof. rewrite sign_finE /=.
  case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
    by rewrite !get_set_heap_neq. Qed.

(** The lifted [sign_fin] sets [fx_used_loc] to [setm us mz.2 tt]. *)
Lemma sfin_used_lem (h : heap) st qv sc us lg mp tb mz r md :
  get_heap (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
    h st qv sc us lg mp tb mz r md).2 fx_used_loc
  = setm us mz.2 Datatypes.tt.
Proof. rewrite sign_finE /=.
  case: (fx_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|].
  - rewrite (get_set_heap_neq _ fx_scnt_loc _ fx_used_loc) //.
    rewrite (get_set_heap_neq _ (fx_log_loc M) _ fx_used_loc) //.
    rewrite (get_set_heap_neq _ (fx_rom_loc PP N Dfin M R) _ fx_used_loc) //.
    rewrite (get_set_heap_neq _ (fx_rt_loc M R) _ fx_used_loc) //.
    by rewrite get_set_heap_eq.
  - rewrite (get_set_heap_neq _ fx_scnt_loc _ fx_used_loc) //.
    rewrite (get_set_heap_neq _ (fx_rom_loc PP N Dfin M R) _ fx_used_loc) //.
    rewrite (get_set_heap_neq _ (fx_rt_loc M R) _ fx_used_loc) //.
    by rewrite get_set_heap_eq. Qed.

Lemma forgefin_sd_lem (h : heap) (sd0 : chMap 'nat Dfin)
    (fc0 : nat) (mp0 : chMap (RoIn PP N M R) Dfin)
    (pt0 : RoIn PP N M R) (md : Dfin) (rest : chMap 'nat Dfin) :
  forge_fin PP N Dfin M R (set_heap h Lsd (unionm sd0 rest)) fc0 mp0 pt0 md
  = set_heap (forge_fin PP N Dfin M R h fc0 mp0 pt0 md) Lsd (unionm sd0 rest).
Proof. rewrite forge_finE.
  rewrite (set_heap_commut _ Lsd _ (fx_rom_loc PP N Dfin M R)) //.
  by rewrite (set_heap_commut _ Lsd _ fx_fcnt_loc). Qed.

Lemma forgefin_st_lem (h : heap) (fc0 : nat)
    (mp0 : chMap (RoIn PP N M R) Dfin) (pt0 : RoIn PP N M R) (md : Dfin) :
  get_heap (forge_fin PP N Dfin M R h fc0 mp0 pt0 md) (fx_st_loc PP N)
  = get_heap h (fx_st_loc PP N).
Proof. by rewrite forge_finE !get_set_heap_neq. Qed.

Lemma forgefin_used_lem (h : heap) (fc0 : nat)
    (mp0 : chMap (RoIn PP N M R) Dfin) (pt0 : RoIn PP N M R) (md : Dfin) :
  get_heap (forge_fin PP N Dfin M R h fc0 mp0 pt0 md) fx_used_loc
  = get_heap h fx_used_loc.
Proof. by rewrite forge_finE !get_set_heap_neq. Qed.

Lemma hashfin_sd_lem (h : heap) (sd0 : chMap 'nat Dfin)
    (hc0 : nat) (mp0 : chMap (RoIn PP N M R) Dfin)
    (xv : RoIn PP N M R) (md : Dfin) (rest : chMap 'nat Dfin) :
  hash_fin PP N Dfin M R (set_heap h Lsd (unionm sd0 rest)) hc0 mp0 xv md
  = set_heap (hash_fin PP N Dfin M R h hc0 mp0 xv md) Lsd (unionm sd0 rest).
Proof. rewrite hash_finE.
  rewrite (set_heap_commut _ Lsd _ (fx_rom_loc PP N Dfin M R)) //.
  by rewrite (set_heap_commut _ Lsd _ fx_hcnt_loc). Qed.

Lemma hashfin_st_lem (h : heap) (hc0 : nat)
    (mp0 : chMap (RoIn PP N M R) Dfin) (xv : RoIn PP N M R) (md : Dfin) :
  get_heap (hash_fin PP N Dfin M R h hc0 mp0 xv md) (fx_st_loc PP N)
  = get_heap h (fx_st_loc PP N).
Proof. by rewrite hash_finE !get_set_heap_neq. Qed.

Lemma hashfin_used_lem (h : heap) (hc0 : nat)
    (mp0 : chMap (RoIn PP N M R) Dfin) (xv : RoIn PP N M R) (md : Dfin) :
  get_heap (hash_fin PP N Dfin M R h hc0 mp0 xv md) fx_used_loc
  = get_heap h fx_used_loc.
Proof. by rewrite hash_finE !get_set_heap_neq. Qed.

#[local] Opaque sign_fin forge_fin hash_fin.
#[local] Opaque ReproHop.G3c G4m.
(* M5: seal the game-plumbing constants BEFORE the per-oracle case lemmas.
   Without this, [rewrite sign4_step] keyed-matches its LHS
   [dfst (Pr_code (bind (sign4_body _) ?k) ?h)] against the giant
   [dfst (Pr_code (code_link (k _) (G4M b)) _)] subterms produced by the
   IH rewrite, forcing a multi-minute conversion of [code_link _ (G4M b)].
   Sealing [code_link Pr_code resolve] blocks that conversion (the explicit
   [cbn [code_link]] in each case still unfolds it where genuinely needed,
   since a [cbn] delta-list overrides Opaque).  Mirrors the fix recorded in
   DIGEST_OPT_NOTES.md UPDATE 2 for DigestHopBound_diff.v. *)
#[local] Opaque code_link Pr_code resolve.

(** Compact form of the digest-hop per-call goal and the lifted
    consumed-set/used-set relation.  M5: the counter-prefix invariant
    is REPLACED by an explicit remaining-list [js] + a used-set ↔
    consumed-slot bijection (clause (v)). *)
Local Notation cus h := (get_heap h fx_used_loc).

Local Notation DIGgoal c b h sd0 js z :=
  (dfst (Pr_code (code_link c (G3C b)) h) z
   = (\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
        dfst (Pr_code (code_link c (G4M b))
                (set_heap h Lsd (unionm sd0 rest)))) z).

Local Notation DIGrel c :=
  (forall (b : bool) (h : heap) (sd0 : chMap 'nat Dfin) (js : seq nat) (z : _),
    uniq js ->
    (forall s, s \in js -> s \notin domm sd0) ->
    (forall s, (s < n_max)%N -> s \notin domm sd0 -> s \in js) ->
    (forall st, get_heap h (fx_st_loc PP N) = Some st ->
       (size (leaf_paths (shape_of h_sf st.2.1)) <= n_max)%N
       /\ (forall s : nat, s \in domm sd0
             <-> (exists2 zi, zi \in domm (cus h) & flidx st.2.1 zi = s))
       /\ (forall zi, zi \in domm (cus h) -> flok st.2.1 zi)) ->
    (get_heap h (fx_st_loc PP N) = None -> sd0 = emptym /\ cus h = emptym) ->
    DIGgoal c b h sd0 js z).

Lemma DIG_gen_case {T' : choiceType} (x : 'list 'bool)
    (k : tgt (geno PP N) -> raw_code T')
    (Hk : forall v, valid_code LA IG (k v))
    (IH : forall v, DIGrel (k v)) :
  DIGrel (opr (geno PP N) x k).
Proof.
move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
rewrite resolve_g3_gen resolve_g4m_gen.
symmetry.
transitivity ((\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
    (if ~~ isSome (get_heap h (fx_st_loc PP N))
        && (size (leaf_paths (shape_of h_sf x)) <= n_max)%N then
       (\dlet_(pp <- Pr_fst dPP)
        \dlet_(_ <- Pr_fst dN)
        \dlet_(_ <- Pr_fst dR)
        \dlet_(xss <- Pr_fst (@sample_keys l N dN (size (leaf_paths (shape_of h_sf x)))))
        \dlet_(sdm <- Pr_fst (fill_code Dfin dDu (iota 0 n_max) emptym))
          dfst (Pr_code (code_link (k (pp, fx_root_x PP N F Tl Htree h_sf pp x xss))
                  (G4M b))
             (set_heap (set_heap (set_heap h Lsd (unionm sd0 rest))
                (fx_st_loc PP N)
                (Some ((pp, fx_root_x PP N F Tl Htree h_sf pp x xss), (x, xss))))
                Lsd sdm)))
     else dnull)) z).
{ apply: eq_dlet_at => rest. rewrite gen4_step.
  rewrite (get_set_heap_neq _ Lsd _ (fx_st_loc PP N)) //.
  by case: (~~ _ && _); rewrite ?dnullE. }
rewrite gen3_step.
case Eg: (~~ isSome (get_heap h (fx_st_loc PP N))
          && (size (leaf_paths (shape_of h_sf x)) <= n_max)%N); last first.
{ rewrite (Pr_fstC (fill_code_ll _ _)). by rewrite dnullE. }
have hstN : get_heap h (fx_st_loc PP N) = None.
{ move: Eg => /andP[h1 _]. by case: (get_heap h (fx_st_loc PP N)) h1. }
have hsize : (size (leaf_paths (shape_of h_sf x)) <= n_max)%N.
{ by move: Eg => /andP[_ ->]. }
case: (hpre hstN) => hsd00 hcus00. subst sd0.
(* the outer suffix-average [rest] is overwritten by the GEN slot
   draw [sdm]: simplify the heap so it no longer mentions [rest] *)
have genheap : forall (pp : PP) (xss : seq (seq N)) (rest sdm : chMap 'nat Dfin),
    set_heap (set_heap (set_heap h Lsd (unionm emptym rest))
      (fx_st_loc PP N)
      (Some ((pp, fx_root_x PP N F Tl Htree h_sf pp x xss), (x, xss))))
      Lsd sdm
    = set_heap (set_heap h (fx_st_loc PP N)
        (Some ((pp, fx_root_x PP N F Tl Htree h_sf pp x xss), (x, xss))))
        Lsd sdm.
{ move=> pp xss rest sdm.
  rewrite (set_heap_commut _ Lsd _ (fx_st_loc PP N)) //.
  by rewrite set_heap_contract. }
under eq_dlet => rest.
{ under eq_dlet => pp.
  { under eq_dlet => xn.
    { under eq_dlet => xr.
      { under eq_dlet => xss.
        { under eq_dlet => sdm. { rewrite genheap. over. } over. }
        over. }
      over. }
    over. }
  over. }
rewrite (Pr_fstC (fill_code_ll _ _)).
symmetry.
apply: eq_dlet_at => pp.
apply: eq_dlet_at => xn.
apply: eq_dlet_at => xr.
apply: eq_dlet_at => xss.
set h' := set_heap h (fx_st_loc PP N)
            (Some ((pp, fx_root_x PP N F Tl Htree h_sf pp x xss), (x, xss))).
have hcusN : get_heap h fx_used_loc = emptym by [].
have huniq' : uniq (iota 0 n_max) by exact: iota_uniq.
have hdisj' : forall s, s \in iota 0 n_max ->
    s \notin domm (emptym : chMap 'nat Dfin).
{ move=> s _. by rewrite domm0 in_fset0. }
have hcov' : forall s, (s < n_max)%N ->
    s \notin domm (emptym : chMap 'nat Dfin) -> s \in iota 0 n_max.
{ move=> s hs _. by rewrite mem_iota /= hs. }
have hst' : forall st, get_heap h' (fx_st_loc PP N) = Some st ->
     (size (leaf_paths (shape_of h_sf st.2.1)) <= n_max)%N
     /\ (forall s : nat, s \in domm (emptym : chMap 'nat Dfin) <->
           (exists2 zi, zi \in domm (cus h') & flidx st.2.1 zi = s))
     /\ (forall zi, zi \in domm (cus h') -> flok st.2.1 zi).
{ move=> st. rewrite /h' get_set_heap_eq => -[<-] /=. split; first exact: hsize.
  rewrite (get_set_heap_neq _ (fx_st_loc PP N) _ fx_used_loc) //.
  rewrite hcusN !domm0. split.
  - move=> s. split; first by rewrite in_fset0.
    by move=> [zi Hzi _]; move: Hzi; rewrite in_fset0.
  - move=> zi. by rewrite in_fset0. }
have hpre' : get_heap h' (fx_st_loc PP N) = None ->
    (emptym : chMap 'nat Dfin) = emptym /\ cus h' = emptym.
{ by rewrite /h' get_set_heap_eq. }
have := IH (pp, fx_root_x PP N F Tl Htree h_sf pp x xss) b h' emptym
         (iota 0 n_max) z huniq' hdisj' hcov' hst' hpre'.
move=> ->.
apply: eq_dlet_at => sdm.
by rewrite /h' union0m.
Qed.

Lemma DIG_sign_case {T' : choiceType} (mz : M × ('nat × 'nat))
    (k : tgt (sgo N M R) -> raw_code T')
    (Hk : forall v, valid_code LA IG (k v))
    (IH : forall v, DIGrel (k v)) :
  DIGrel (opr (sgo N M R) mz k).
Proof.
move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
rewrite resolve_g3_sign resolve_g4m_sign.
have sfin_h := sfin_h_lem h.
have sfin_r := sfin_r_lem h.
have sfin_st := sfin_st_lem h.
have sfin_used := sfin_used_lem h.
set Lg := get_heap h (fx_log_loc M).
set Mp := get_heap h (fx_rom_loc PP N Dfin M R).
set Tb := get_heap h (fx_rt_loc M R).
rewrite sign3_step.
case Es: ((get_heap h fx_scnt_loc < q_s)%N); last first.
{ (* counter exhausted: both fail *)
  symmetry.
  transitivity ((\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
                   (dnull : {distr T' / Axioms.R})) z).
  { apply: eq_dlet_at => rest. rewrite sign4_step.
    by rewrite get_set_heap_neq // Es dnullE. }
  by rewrite (Pr_fstC (fill_code_ll _ _)) dnullE. }
case Est: (get_heap h (fx_st_loc PP N)) => [st|]; last first.
{ (* Lst = None: getSome fails on both sides *)
  symmetry. apply: dlet_at0 => rest.
  by rewrite sign4_step get_set_heap_neq // Es get_set_heap_neq // Est. }
case Eg: ([&& flok st.2.1 mz.2 & mz.2 \notin domm (get_heap h fx_used_loc)]);
  last first.
{ (* guard FALSE (invalid or reused id): no slot read, bump counter,
     ret None; NO peel.  Recurse with [sd0], [js] UNCHANGED. *)
  set h2 := set_heap h fx_scnt_loc (get_heap h fx_scnt_loc).+1.
  have h2st : get_heap h2 (fx_st_loc PP N) = get_heap h (fx_st_loc PP N)
    by rewrite /h2 get_set_heap_neq.
  have h2us : get_heap h2 fx_used_loc = get_heap h fx_used_loc
    by rewrite /h2 get_set_heap_neq.
  have hst2 : forall st0, get_heap h2 (fx_st_loc PP N) = Some st0 ->
       (size (leaf_paths (shape_of h_sf st0.2.1)) <= n_max)%N
       /\ (forall s : nat, s \in domm sd0 <->
             (exists2 zi, zi \in domm (cus h2) & flidx st0.2.1 zi = s))
       /\ (forall zi, zi \in domm (cus h2) -> flok st0.2.1 zi).
  { move=> st0. rewrite h2st !h2us. exact: hst. }
  have hpre2 : get_heap h2 (fx_st_loc PP N) = None ->
               sd0 = emptym /\ cus h2 = emptym.
  { rewrite h2st h2us. exact: hpre. }
  rewrite (IH None b h2 sd0 js z huniq hdisj hcov hst2 hpre2).
  apply: eq_dlet_at => rest.
  rewrite (Ssign mz (k := fun v => code_link (k v) (G4M b))
                    (h := set_heap h Lsd (unionm sd0 rest))).
  rewrite (get_set_heap_neq h Lsd (unionm sd0 rest) fx_scnt_loc) // Es.
  rewrite (get_set_heap_neq h Lsd (unionm sd0 rest) (fx_st_loc PP N)) // Est.
  rewrite (get_set_heap_neq h Lsd (unionm sd0 rest) fx_used_loc) // Eg.
  by rewrite /h2 (set_heap_commut h Lsd (unionm sd0 rest)
       fx_scnt_loc (get_heap h fx_scnt_loc).+1). }
(* guard TRUE: the peel site *)
move: Eg => /andP[hok hfresh].
have [hsize [bij_old val_old]] := hst st Est.
have hlt : (flidx st.2.1 mz.2 < n_max)%N.
{ exact: (leq_trans (leafid_index_lt h_sf st.2.1 mz.2 hok) hsize). }
have hnotin : flidx st.2.1 mz.2 \notin domm sd0.
{ apply/negP => hin.
  move: (proj1 (bij_old (flidx st.2.1 mz.2)) hin) => [zi Hzi Hlz].
  have e := leafid_index_inj h_sf st.2.1 zi mz.2 (val_old zi Hzi) hok Hlz.
  by move: hfresh; rewrite -e Hzi. }
have hjin : flidx st.2.1 mz.2 \in js := hcov _ hlt hnotin.
(* [rec_post]: fold the [rem]-average back into G3c via [IH], with the
   consumed set [setm sd0 (flidx zi) y] and remaining list [rem (flidx zi) js]. *)
have rec_post : forall (r : R) (md y : Dfin),
    dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
           S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
           (get_heap h fx_used_loc) Lg Mp Tb mz r md).1) (G3C b))
      (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
         h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
         (get_heap h fx_used_loc) Lg Mp Tb mz r md).2) z
    = (\dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem (flidx st.2.1 mz.2) js) emptym))
         dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
                S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                (get_heap h fx_used_loc) Lg Mp Tb mz r md).1) (G4M b))
           (set_heap (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
              h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
              (get_heap h fx_used_loc) Lg Mp Tb mz r md).2 Lsd
              (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)))) z.
{ move=> r md y.
  set h3 := (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
    h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
    Lg Mp Tb mz r md).2.
  have Lh3 : get_heap h3 (fx_st_loc PP N) = Some st by rewrite /h3 sfin_st.
  have Uh3 : get_heap h3 fx_used_loc = setm (get_heap h fx_used_loc) mz.2 Datatypes.tt
    by rewrite /h3 sfin_used.
  apply: (IH _ b h3 (setm sd0 (flidx st.2.1 mz.2) y)
            (rem (flidx st.2.1 mz.2) js) z).
  - by apply: rem_uniq.
  - move=> s Hs. move: Hs; rewrite (mem_rem_uniq _ huniq) inE => /andP[hsj hsjs].
    rewrite domm_set in_fsetU1 negb_or hsj /=. exact: hdisj s hsjs.
  - move=> s hs. rewrite domm_set in_fsetU1 negb_or => /andP[hsj hsd].
    rewrite (mem_rem_uniq _ huniq) inE hsj /=. exact: hcov s hs hsd.
  - move=> st0. rewrite Lh3 => -[= <-]. split; first exact: hsize.
    rewrite Uh3. split.
    + move=> s. rewrite domm_set in_fsetU1 domm_set.
      split.
      * move=> /orP[/eqP -> | hs].
        -- by exists mz.2; rewrite ?in_fsetU1 ?eqxx.
        -- move: (proj1 (bij_old s) hs) => [zi Hzi Hlz].
           exists zi => //. by rewrite in_fsetU1 Hzi orbT.
      * move=> [zi]; rewrite in_fsetU1 => /orP[/eqP -> | Hzi] Hlz.
        -- by rewrite -Hlz eqxx.
        -- apply/orP; right. apply (proj2 (bij_old s)). by exists zi.
    + move=> zi. rewrite domm_set in_fsetU1 => /orP[/eqP -> | Hzi].
      * exact: hok.
      * exact: val_old zi Hzi.
  - rewrite Lh3. by []. }
have hslotget : forall (y : Dfin) (rest : chMap 'nat Dfin),
    getm (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest) (flidx st.2.1 mz.2)
    = Some y.
{ move=> y rest. by rewrite unionmE setmE eqxx. }
symmetry.
rewrite (fill_peel_at (flidx st.2.1 mz.2) js sd0
  (fun m => dfst (Pr_code (bind (sbody mz)
                   (fun v => code_link (k v) (G4M b)))
              (set_heap h Lsd m))) z hjin huniq hdisj).
case Etb: (getm Tb (mz.2, mz.1)) => [r|].
- (* Lrt HIT: [r] cached; peeled [y] discarded (via [dlet_dDu_const]). *)
  transitivity ((\dlet_(_ <- Pr_fst dDu)
    (match getm Mp (r, (st.1, (mz.2, mz.1))) with
     | Some md =>
         dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
                S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                (get_heap h fx_used_loc) Lg Mp Tb mz r md).1) (G3C b))
           (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
              h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
              (get_heap h fx_used_loc) Lg Mp Tb mz r md).2)
     | None =>
         (\dlet_(md <- Pr_fst dDu)
            dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
                   S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                   (get_heap h fx_used_loc) Lg Mp Tb mz r md).1) (G3C b))
              (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
                 h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                 (get_heap h fx_used_loc) Lg Mp Tb mz r md).2))
     end)) z).
  2: { rewrite dlet_dDu_const. by case: (getm Mp _). }
  apply: eq_dlet_at => y.
  case Erom: (getm Mp (r, (st.1, (mz.2, mz.1)))) => [md|].
  + rewrite (rec_post r md y).
    apply: eq_dlet_at => rest.
    rewrite (Ssign mz (k := fun v => code_link (k v) (G4M b))
       (h := set_heap h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest))).
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       fx_scnt_loc) // Es.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_st_loc PP N)) // Est.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       fx_used_loc) //.
    have -> : [&& flok st.2.1 mz.2 & mz.2 \notin domm (get_heap h fx_used_loc)]
      by rewrite hok /= (negbTE hfresh).
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_rt_loc M R)) // -/Tb Etb.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_rom_loc PP N Dfin M R)) // -/Mp Erom.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_log_loc M)) // -/Lg.
    by rewrite sfin_r sfin_h.
  + symmetry.
    transitivity ((\dlet_(md <- Pr_fst dDu)
        \dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem (flidx st.2.1 mz.2) js) emptym))
          dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
                 S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
                 (get_heap h fx_used_loc) Lg Mp Tb mz r md).1) (G4M b))
            (set_heap (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
               h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
               (get_heap h fx_used_loc) Lg Mp Tb mz r md).2 Lsd
               (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)))) z).
    { apply: eq_dlet_at => md. exact: (rec_post r md y). }
    rewrite dlet_commut.
    apply: eq_dlet_at => rest.
    rewrite (Ssign mz (k := fun v => code_link (k v) (G4M b))
       (h := set_heap h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest))).
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       fx_scnt_loc) // Es.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_st_loc PP N)) // Est.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       fx_used_loc) //.
    have -> : [&& flok st.2.1 mz.2 & mz.2 \notin domm (get_heap h fx_used_loc)]
      by rewrite hok /= (negbTE hfresh).
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_rt_loc M R)) // -/Tb Etb.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_rom_loc PP N Dfin M R)) // -/Mp Erom.
    apply: eq_dlet_at => md.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_log_loc M)) // -/Lg.
    by rewrite sfin_r sfin_h.
- (* Lrt MISS: the eager/lazy coupling.  G3 samples [r<-dR] and [md<-dDu]
     fresh; G4m reads slot [flidx zi] = the peeled [y]. *)
  symmetry.
  transitivity ((\dlet_(y <- Pr_fst dDu)
      \dlet_(rest <- Pr_fst (fill_code Dfin dDu (rem (flidx st.2.1 mz.2) js) emptym))
      \dlet_(r <- Pr_fst dR)
        dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
               S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
               (get_heap h fx_used_loc) Lg Mp Tb mz r y).1) (G4M b))
          (set_heap (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
             h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
             (get_heap h fx_used_loc) Lg Mp Tb mz r y).2 Lsd
             (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)))) z).
  2: { apply: eq_dlet_at => y. apply: eq_dlet_at => rest.
    rewrite (Ssign mz (k := fun v => code_link (k v) (G4M b))
       (h := set_heap h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest))).
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       fx_scnt_loc) // Es.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_st_loc PP N)) // Est.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       fx_used_loc) //.
    have -> : [&& flok st.2.1 mz.2 & mz.2 \notin domm (get_heap h fx_used_loc)]
      by rewrite hok /= (negbTE hfresh).
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_rt_loc M R)) // -/Tb Etb.
    rewrite (get_set_heap_eq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest))
       hslotget.
    apply: eq_dlet_at => r.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_log_loc M)) // -/Lg.
    rewrite (get_set_heap_neq h Lsd (unionm (setm sd0 (flidx st.2.1 mz.2) y) rest)
       (fx_rom_loc PP N Dfin M R)) // -/Mp.
    by rewrite sfin_r sfin_h. }
  transitivity ((\dlet_(y <- Pr_fst dDu)
      \dlet_(r <- Pr_fst dR)
        dfst (Pr_code (code_link (k (sign_fin PP N Dfin M R F Tl Hgrind Htree
               S_wn c_max h_sf h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
               (get_heap h fx_used_loc) Lg Mp Tb mz r y).1) (G3C b))
          (sign_fin PP N Dfin M R F Tl Hgrind Htree S_wn c_max h_sf
             h st (flidx st.2.1 mz.2) (get_heap h fx_scnt_loc)
             (get_heap h fx_used_loc) Lg Mp Tb mz r y).2)) z).
  2: { apply: eq_dlet_at => y.
    rewrite dlet_commut.
    apply: eq_dlet_at => r.
    exact: (rec_post r y y). }
  rewrite dlet_commut.
  apply: eq_dlet_at => r. by apply: eq_dlet_at => md.
Qed.

Lemma DIG_hash_case {T' : choiceType} (x : RoIn PP N M R)
    (k : tgt (hho PP N Dfin M R) -> raw_code T')
    (Hk : forall v, valid_code LA IG (k v))
    (IH : forall v, DIGrel (k v)) :
  DIGrel (opr (hho PP N Dfin M R) x k).
Proof.
move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
rewrite resolve_g3_hash resolve_g4m_hash.
have hashfin_sd := hashfin_sd_lem h sd0.
rewrite hash_step. symmetry.
transitivity ((\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
    (if (get_heap h fx_hcnt_loc < q_h)%N then
       match getm (get_heap h (fx_rom_loc PP N Dfin M R)) x with
       | Some md =>
           dfst (Pr_code (code_link (k md) (G4M b))
                   (set_heap (hash_fin PP N Dfin M R h (get_heap h fx_hcnt_loc)
                      (get_heap h (fx_rom_loc PP N Dfin M R)) x md)
                      Lsd (unionm sd0 rest)))
       | None =>
           (\dlet_(md <- Pr_fst dDu)
              dfst (Pr_code (code_link (k md) (G4M b))
                      (set_heap (hash_fin PP N Dfin M R h (get_heap h fx_hcnt_loc)
                         (get_heap h (fx_rom_loc PP N Dfin M R)) x md)
                         Lsd (unionm sd0 rest))))
       end
     else dnull)) z).
{ apply: eq_dlet_at => rest. rewrite hash_step.
  rewrite get_set_heap_neq // get_set_heap_neq //.
  case: ((get_heap h fx_hcnt_loc < q_h)%N); last by rewrite dnullE.
  case: (getm _ x) => [md|].
  - by rewrite hashfin_sd.
  - apply: eq_dlet_at => md. by rewrite hashfin_sd. }
case Eh: ((get_heap h fx_hcnt_loc < q_h)%N); last first.
{ rewrite (Pr_fstC (fill_code_ll _ _)). by rewrite dnullE. }
have hst' : forall (md : Dfin) st,
    get_heap (hash_fin PP N Dfin M R h (get_heap h fx_hcnt_loc)
      (get_heap h (fx_rom_loc PP N Dfin M R)) x md) (fx_st_loc PP N) = Some st ->
    (size (leaf_paths (shape_of h_sf st.2.1)) <= n_max)%N
    /\ (forall s : nat, s \in domm sd0 <->
          (exists2 zi, zi \in domm (cus (hash_fin PP N Dfin M R h
            (get_heap h fx_hcnt_loc) (get_heap h (fx_rom_loc PP N Dfin M R)) x md))
            & flidx st.2.1 zi = s))
    /\ (forall zi, zi \in domm (cus (hash_fin PP N Dfin M R h
          (get_heap h fx_hcnt_loc) (get_heap h (fx_rom_loc PP N Dfin M R)) x md))
          -> flok st.2.1 zi).
{ move=> md st. rewrite hashfin_st_lem !hashfin_used_lem. exact: hst. }
have hpre' : forall (md : Dfin),
    get_heap (hash_fin PP N Dfin M R h (get_heap h fx_hcnt_loc)
      (get_heap h (fx_rom_loc PP N Dfin M R)) x md) (fx_st_loc PP N) = None ->
    sd0 = emptym /\ cus (hash_fin PP N Dfin M R h (get_heap h fx_hcnt_loc)
      (get_heap h (fx_rom_loc PP N Dfin M R)) x md) = emptym.
{ move=> md. rewrite hashfin_st_lem hashfin_used_lem. exact: hpre. }
case Em: (getm (get_heap h (fx_rom_loc PP N Dfin M R)) x) => [md|].
* by rewrite (IH md b _ sd0 js z huniq hdisj hcov (hst' md) (hpre' md)).
* rewrite dlet_commut. symmetry.
  apply: eq_dlet_at => md.
  by rewrite (IH md b _ sd0 js z huniq hdisj hcov (hst' md) (hpre' md)).
Qed.

Lemma DIG_forge_case {T' : choiceType} (x : M * FxSig N R)
    (k : tgt (fgo N M R) -> raw_code T')
    (Hk : forall v, valid_code LA IG (k v))
    (IH : forall v, DIGrel (k v)) :
  DIGrel (opr (fgo N M R) x k).
Proof.
move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
move: x => [m sg].
rewrite resolve_g3_forge resolve_g4m_forge.
(* FORGE is unchanged by the digest hop: both games run [forge3f_body b].
   It never touches [Lsd] or [fx_used_loc]; the invariant is preserved. *)
set fbody := (X in dfst (Pr_code (bind X _) h) z).
have fstep : forall (K : 'bool -> raw_code T') (hh : heap),
  dfst (Pr_code (bind fbody K) hh) z
  = if (get_heap hh fx_fcnt_loc < q_f)%N then
      match get_heap hh (fx_st_loc PP N) with
      | None => 0
      | Some st =>
        match getm (get_heap hh (fx_rom_loc PP N Dfin M R))
                (sg.1.2, (st.1, (sg.1.1, m))) with
        | Some md =>
            dfst (Pr_code (K (if b then
                    fx_verify_md PP N Dfin F Tl Hgrind Htree S_wn h_sf
                      st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
                    && (m \notin get_heap hh (fx_log_loc M)) else false))
              (forge_fin PP N Dfin M R hh (get_heap hh fx_fcnt_loc)
                 (get_heap hh (fx_rom_loc PP N Dfin M R))
                 (sg.1.2, (st.1, (sg.1.1, m))) md)) z
        | None =>
            (\dlet_(md <- Pr_fst dDu)
               dfst (Pr_code (K (if b then
                       fx_verify_md PP N Dfin F Tl Hgrind Htree S_wn h_sf
                         st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
                       && (m \notin get_heap hh (fx_log_loc M)) else false))
                 (forge_fin PP N Dfin M R hh (get_heap hh fx_fcnt_loc)
                    (get_heap hh (fx_rom_loc PP N Dfin M R))
                    (sg.1.2, (st.1, (sg.1.1, m))) md))) z
        end
      end
    else 0.
{ move=> K hh. rewrite /fbody /forge3f_body. cbn [bind].
  rewrite Pr_code_get.
  case E1: ((get_heap hh fx_fcnt_loc < q_f)%N); last first.
  { by rewrite assertD_false dPr_bind_fail. }
  rewrite assertD_true. cbn [bind].
  rewrite Pr_code_get.
  case E2: (get_heap hh (fx_st_loc PP N)) => [st|]; last first.
  { by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
  rewrite -[isSome (Some st)]/true assertD_true. cbn [getSome bind].
  rewrite 2!Pr_code_get.
  case E3: (getm (get_heap hh (fx_rom_loc PP N Dfin M R))
              (sg.1.2, (st.1, (sg.1.1, m)))) => [md|].
  - cbn [bind]. by rewrite 2!Pr_code_put forge_finE.
  - rewrite bind_assoc. cbn [bind]. rewrite bind_assoc dPr_dist.
    apply: eq_dlet_at => md. cbn [bind]. by rewrite 2!Pr_code_put forge_finE. }
have forgefin_sd := forgefin_sd_lem h sd0.
rewrite fstep. symmetry.
transitivity ((\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
    (if (get_heap h fx_fcnt_loc < q_f)%N then
       match get_heap h (fx_st_loc PP N) with
       | None => (dnull : {distr T' / Axioms.R})
       | Some st =>
         match getm (get_heap h (fx_rom_loc PP N Dfin M R))
                 (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some md =>
             dfst (Pr_code (code_link (k (if b then
                     fx_verify_md PP N Dfin F Tl Hgrind Htree S_wn h_sf
                       st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
                     && (m \notin get_heap h (fx_log_loc M)) else false)) (G4M b))
               (set_heap (forge_fin PP N Dfin M R h (get_heap h fx_fcnt_loc)
                  (get_heap h (fx_rom_loc PP N Dfin M R))
                  (sg.1.2, (st.1, (sg.1.1, m))) md)
                  Lsd (unionm sd0 rest)))
         | None =>
             (\dlet_(md <- Pr_fst dDu)
                dfst (Pr_code (code_link (k (if b then
                        fx_verify_md PP N Dfin F Tl Hgrind Htree S_wn h_sf
                          st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
                        && (m \notin get_heap h (fx_log_loc M)) else false)) (G4M b))
                  (set_heap (forge_fin PP N Dfin M R h (get_heap h fx_fcnt_loc)
                     (get_heap h (fx_rom_loc PP N Dfin M R))
                     (sg.1.2, (st.1, (sg.1.1, m))) md)
                     Lsd (unionm sd0 rest))))
         end
       end
     else dnull)) z).
{ apply: eq_dlet_at => rest. rewrite fstep.
  rewrite !(get_set_heap_neq _ Lsd _ fx_fcnt_loc) //.
  rewrite !(get_set_heap_neq _ Lsd _ (fx_st_loc PP N)) //.
  rewrite !(get_set_heap_neq _ Lsd _ (fx_rom_loc PP N Dfin M R)) //.
  rewrite !(get_set_heap_neq _ Lsd _ (fx_log_loc M)) //.
  case: ((get_heap h fx_fcnt_loc < q_f)%N); last by rewrite dnullE.
  case: (get_heap h (fx_st_loc PP N)) => [st|]; last by rewrite dnullE.
  case: (getm _ (sg.1.2, (st.1, (sg.1.1, m)))) => [md|].
  - by rewrite forgefin_sd.
  - apply: eq_dlet_at => md. by rewrite forgefin_sd. }
case Ef: ((get_heap h fx_fcnt_loc < q_f)%N); last first.
{ rewrite (Pr_fstC (fill_code_ll _ _)). by rewrite dnullE. }
case Est: (get_heap h (fx_st_loc PP N)) => [st|]; last first.
{ rewrite (Pr_fstC (fill_code_ll _ _)). by rewrite dnullE. }
have hst' : forall (md : Dfin) st0,
    get_heap (forge_fin PP N Dfin M R h (get_heap h fx_fcnt_loc)
      (get_heap h (fx_rom_loc PP N Dfin M R)) (sg.1.2, (st.1, (sg.1.1, m))) md)
      (fx_st_loc PP N) = Some st0 ->
    (size (leaf_paths (shape_of h_sf st0.2.1)) <= n_max)%N
    /\ (forall s : nat, s \in domm sd0 <->
          (exists2 zi, zi \in domm (cus (forge_fin PP N Dfin M R h
            (get_heap h fx_fcnt_loc) (get_heap h (fx_rom_loc PP N Dfin M R))
            (sg.1.2, (st.1, (sg.1.1, m))) md)) & flidx st0.2.1 zi = s))
    /\ (forall zi, zi \in domm (cus (forge_fin PP N Dfin M R h
          (get_heap h fx_fcnt_loc) (get_heap h (fx_rom_loc PP N Dfin M R))
          (sg.1.2, (st.1, (sg.1.1, m))) md)) -> flok st0.2.1 zi).
{ move=> md st0. rewrite forgefin_st_lem !forgefin_used_lem. exact: hst. }
have hpre' : forall (md : Dfin),
    get_heap (forge_fin PP N Dfin M R h (get_heap h fx_fcnt_loc)
      (get_heap h (fx_rom_loc PP N Dfin M R)) (sg.1.2, (st.1, (sg.1.1, m))) md)
      (fx_st_loc PP N) = None ->
    sd0 = emptym /\ cus (forge_fin PP N Dfin M R h (get_heap h fx_fcnt_loc)
      (get_heap h (fx_rom_loc PP N Dfin M R)) (sg.1.2, (st.1, (sg.1.1, m))) md)
      = emptym.
{ move=> md. rewrite forgefin_st_lem forgefin_used_lem. exact: hpre. }
case Em: (getm (get_heap h (fx_rom_loc PP N Dfin M R))
            (sg.1.2, (st.1, (sg.1.1, m)))) => [md|].
* by rewrite (IH _ b _ sd0 js z huniq hdisj hcov (hst' md) (hpre' md)).
* rewrite dlet_commut. symmetry.
  apply: eq_dlet_at => md.
  by rewrite (IH _ b _ sd0 js z huniq hdisj hcov (hst' md) (hpre' md)).
Qed.

(** The digest-hop core, assembled from the per-oracle case lemmas
    (each its own [Qed], keeping every proof term small). *)
Lemma DIG_eq_core_b {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IG c) : DIGrel c.
Proof.
induction VA as [a | o x k Ho Hk IH | lo k Hl Hk IH
                | lo v k Hl Hk IH | op k Hk IH].
- (* ret *)
  move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
  rewrite dPr_ret. symmetry.
  transitivity ((\dlet_(_ <- Pr_fst (fill_code Dfin dDu js emptym)) (dunit a)) z).
  { by apply: eq_dlet_at => rest; rewrite dPr_ret. }
  by rewrite (Pr_fstC (fill_code_ll _ _)).
- (* opr *)
  fmap_invert Ho.
  + exact: (DIG_gen_case x k Hk IH).
  + exact: (DIG_sign_case x k Hk IH).
  + exact: (DIG_hash_case x k Hk IH).
  + exact: (DIG_forge_case x k Hk IH).
- (* getr *)
  move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
  case/and5P: (dadvloc_neq _ Hl) => n1 n2 n3 n4 /and5P [n5 n6 n7 n8 n9].
  rewrite Pr_code_get.
  rewrite (IH (get_heap h lo) b h sd0 js z huniq hdisj hcov hst hpre).
  apply: eq_dlet_at => rest.
  by rewrite Pr_code_get get_set_heap_neq // eq_sym.
- (* putr *)
  move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
  case/and5P: (dadvloc_neq _ Hl) => n1 n2 n3 n4 /and5P [n5 n6 n7 n8 n9].
  rewrite Pr_code_put.
  have nst : (fx_st_loc PP N).1 != lo.1 by rewrite eq_sym.
  have nus : fx_used_loc.1 != lo.1 by rewrite eq_sym.
  have hst' : forall st, get_heap (set_heap h lo v) (fx_st_loc PP N) = Some st ->
       (size (leaf_paths (shape_of h_sf st.2.1)) <= n_max)%N
       /\ (forall s : nat, s \in domm sd0
             <-> (exists2 zi, zi \in domm (cus (set_heap h lo v)) & flidx st.2.1 zi = s))
       /\ (forall zi, zi \in domm (cus (set_heap h lo v)) -> flok st.2.1 zi).
  { rewrite (get_set_heap_neq _ lo _ (fx_st_loc PP N) nst).
    rewrite !(get_set_heap_neq _ lo _ fx_used_loc nus). exact: hst. }
  have hpre' : get_heap (set_heap h lo v) (fx_st_loc PP N) = None ->
               sd0 = emptym /\ cus (set_heap h lo v) = emptym.
  { rewrite (get_set_heap_neq _ lo _ (fx_st_loc PP N) nst)
            (get_set_heap_neq _ lo _ fx_used_loc nus). exact: hpre. }
  rewrite (IH b (set_heap h lo v) sd0 js z huniq hdisj hcov hst' hpre').
  apply: eq_dlet_at => rest.
  rewrite Pr_code_put.
  have nsd : Lsd.1 != lo.1 by rewrite eq_sym.
  by rewrite (set_heap_commut h Lsd (unionm sd0 rest) lo v nsd).
- (* sampler *)
  move=> b h sd0 js z huniq hdisj hcov hst hpre. cbn [code_link].
  rewrite dPr_sample.
  transitivity ((\dlet_(a <- op.π2)
      \dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
        dfst (Pr_code (code_link (k a) (G4M b))
                (set_heap h Lsd (unionm sd0 rest)))) z).
  { apply: eq_dlet_at => a. exact: (IH a b h sd0 js z huniq hdisj hcov hst hpre). }
  rewrite dlet_commut.
  apply: eq_dlet_at => rest.
  by rewrite dPr_sample.
Qed.

(** Core equality (G3c = suffix-averaged G4m), [b = false] specialization
    of [DIG_eq_core_b].  M5: the suffix average is now over the explicit
    remaining-list [js] with the consumed-set/used-set invariant. *)
Lemma DIG_eq_core {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IG c) :
  forall (h : heap) (sd0 : chMap 'nat Dfin) (js : seq nat) (z : T'),
    uniq js ->
    (forall k, k \in js -> k \notin domm sd0) ->
    (forall s, (s < n_max)%N -> s \notin domm sd0 -> s \in js) ->
    (forall st, get_heap h (fx_st_loc PP N) = Some st ->
       (size (leaf_paths (shape_of h_sf st.2.1)) <= n_max)%N
       /\ (forall s : nat, s \in domm sd0
             <-> (exists2 zi, zi \in domm (cus h) & flidx st.2.1 zi = s))
       /\ (forall zi, zi \in domm (cus h) -> flok st.2.1 zi)) ->
    (get_heap h (fx_st_loc PP N) = None -> sd0 = emptym /\ cus h = emptym) ->
    dfst (Pr_code (code_link c (G3C false)) h) z
    = (\dlet_(rest <- Pr_fst (fill_code Dfin dDu js emptym))
         dfst (Pr_code (code_link c (G4M false))
                 (set_heap h Lsd (unionm sd0 rest)))) z.
Proof. move=> h sd0 js z; exact: (DIG_eq_core_b VA false h sd0 js z). Qed.

End DigAdversary.

(** The wrapper: [G3c] and [G4m] are perfectly indistinguishable. *)
Lemma DIG_eq (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G3C b) (G4M b) A = 0.
Proof.
  apply: (Adv_nom_ind _ _ _ IG (eq^~ 0)) => //.
  move=> A' LA' VA' _ sep1 sep2.
  rewrite /AdvantageE.
  have hRUN : fhas A_export RUN by fmap_solve.
  have VC := valid_resolve _ _ _ _ RUN tt VA' hRUN.
  have sepL : fseparate LA' (loc (G4M false)).
  { by move: sep1; rewrite /G4m. }
  rewrite 2!Pr_Pr_code 2!resolve_link.
  have huniq0 : uniq (iota 0 n_max) by exact: iota_uniq.
  have hdisj0 : forall k, k \in iota 0 n_max ->
      k \notin domm (emptym : chMap 'nat Dfin).
  { move=> k _. by rewrite domm0 in_fset0. }
  have hcov0 : forall s, (s < n_max)%N ->
      s \notin domm (emptym : chMap 'nat Dfin) -> s \in iota 0 n_max.
  { move=> s hs _. by rewrite mem_iota /= hs. }
  have hst0 : forall st, get_heap empty_heap (fx_st_loc PP N) = Some st ->
       (size (leaf_paths (shape_of h_sf st.2.1)) <= n_max)%N
       /\ (forall s : nat, s \in domm (emptym : chMap 'nat Dfin)
             <-> (exists2 zi, zi \in domm (get_heap empty_heap fx_used_loc) & flidx st.2.1 zi = s))
       /\ (forall zi, zi \in domm (get_heap empty_heap fx_used_loc) -> flok st.2.1 zi).
  { by []. }
  have hpre0 : get_heap empty_heap (fx_st_loc PP N) = None ->
               (emptym : chMap 'nat Dfin) = emptym /\ get_heap empty_heap fx_used_loc = emptym.
  { by []. }
  rewrite (DIG_eq_core_b LA' sepL VC b empty_heap emptym (iota 0 n_max) true
             huniq0 hdisj0 hcov0 hst0 hpre0).
  (* collapse the average: G4m ignores the prefilled Lsd (pre-GEN no
     oracle reads it, GEN re-draws it). *)
  have collapse :
    (\dlet_(rest <- Pr_fst (fill_code Dfin dDu (iota 0 n_max) emptym))
       dfst (Pr_code (code_link (resolve A' RUN tt) (G4M b))
               (set_heap empty_heap (fx_sd_loc Dfin) (unionm emptym rest))))
    = dfst (Pr_code (code_link (resolve A' RUN tt) (G4M b)) empty_heap).
  { rewrite -[RHS](Pr_fstC (fill_code_ll (iota 0 n_max) emptym) (mu := dfst (Pr_code
      (code_link (resolve A' RUN tt) (G4M b)) empty_heap))).
    apply: eq_dlet => rest. rewrite union0m.
    apply: distr_ext => u.
    apply: (DigestHopBound_g4indep.g4_lsd_indep PP N M R d_n F Tl Hgrind Htree
              dPP dN dR S_wn c_max h_sf q_s q_h n_max q_f LA' sepL VC b _ _ u).
    - move=> lo hlo. by rewrite (get_set_heap_neq _ (fx_sd_loc Dfin) _ lo hlo).
    - by rewrite get_set_heap_neq. }
  rewrite collapse subrr normr0 //.
Qed.

End FXMSSDigestBound.
