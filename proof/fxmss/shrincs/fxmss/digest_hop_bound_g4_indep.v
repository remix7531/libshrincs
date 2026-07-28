(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.digest_hop_bound_g4_indep

    Establishes that the fourth digest-hop game is independent of the stored
    signing digest, providing the relational invariant used by the equal and
    unequal digest branches. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From Sec.lib Require Import prelude math.bin_tree math.merkle sig.scheme games.thf toolkit.sample_seq toolkit.ro_plus toolkit.reprogram.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.prf_hop fxmss.repro_hop fxmss.digest_hop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FXMSSDigestBound.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).
Context (PP N M R : choice_type) (d_n : nat).
Context (F : PP -> adrs_sf -> N -> N) (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> (chFin d_n.+1) * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R).
Context (S_wn c_max h_sf q_s q_h n_max q_f : nat).
Local Notation Dfin := (chFin d_n.+1).
Local Notation dDu := (rp_dPfx d_n).

Local Notation G3C b := (repro_hop.G3c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4M b := (G4m PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4C b := (G4c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).

Local Notation Lsd := (shrincs_fxmss_sd_loc Dfin).
Local Notation IG := (I_G0fL PP N Dfin M R).

(** [rp_dPfx] is lossless (uniform on a nonempty finite type). *)
Lemma dDu_ll : LosslessCode dDu.
Proof. exact _. Qed.

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

Section DigAdversary.

Context (LA : Locations).
Context (sepL : fseparate LA (loc (G4M false))).

Local Notation csc h := (get_heap h shrincs_fxmss_scnt_loc).

(** M5: [shrincs_fxmss_q_loc] counter deleted; the used-set [shrincs_fxmss_used_loc] (410)
    is the new game location, occupying the SAME [G4_locs] slot (position
    2) that [shrincs_fxmss_q_loc] held.  [domm (G4_locs)] follows the fmap-literal
    order, so the conjunction order is unchanged apart from that one swap
    ([Lsd] = [shrincs_fxmss_sd_loc] stays LAST = [n9]). *)
Lemma dadvloc_neq (lo : Location) :
  fhas LA lo →
  [&& lo.1 != (shrincs_fxmss_st_loc PP N).1, lo.1 != shrincs_fxmss_used_loc.1, lo.1 != shrincs_fxmss_scnt_loc.1,
      lo.1 != (shrincs_fxmss_log_loc M).1, lo.1 != (shrincs_fxmss_rom_loc PP N Dfin M R).1,
      lo.1 != shrincs_fxmss_hcnt_loc.1, lo.1 != (shrincs_fxmss_rt_loc M R).1,
      lo.1 != shrincs_fxmss_fcnt_loc.1 & lo.1 != Lsd.1].
Proof.
move=> hl.
have hn := notin_has_separate _ _ _ hl sepL.
rewrite /G4m domm_mkfmap !inE /= !negb_or in hn.
by case/and5P: hn => -> -> -> -> /and4P [-> -> -> ->].
Qed.

(** The DIG_eq invariant on the shared heap [h]:
    - [sd0] (the consumed-slot prefix in [Lsd]) covers only slots
      [< sc] (the per-call counter);
    - [sc <= q_s];
    - before GEN ([Lst = None]) no slot has been consumed. *)


Lemma dlet_dDu_const {U : choiceType} (nu : {distr U / Axioms.R}) (u : U) :
  (\dlet_(_ <- Pr_fst dDu) nu) u = nu u.
Proof. by rewrite (Pr_fstC dDu_ll). Qed.

Lemma forgefin_st_lem (h : heap) (fc0 : nat)
    (mp0 : chMap (shrincs_fxmss_random_oracle_input PP N M R) Dfin) (pt0 : shrincs_fxmss_random_oracle_input PP N M R) (md : Dfin) :
  get_heap (forge_fin PP N Dfin M R h fc0 mp0 pt0 md) (shrincs_fxmss_st_loc PP N)
  = get_heap h (shrincs_fxmss_st_loc PP N).
Proof. by rewrite forge_finE !get_set_heap_neq. Qed.

Lemma hashfin_st_lem (h : heap) (hc0 : nat)
    (mp0 : chMap (shrincs_fxmss_random_oracle_input PP N M R) Dfin) (xv : shrincs_fxmss_random_oracle_input PP N M R) (md : Dfin) :
  get_heap (hash_fin PP N Dfin M R h hc0 mp0 xv md) (shrincs_fxmss_st_loc PP N)
  = get_heap h (shrincs_fxmss_st_loc PP N).
Proof. by rewrite hash_finE !get_set_heap_neq. Qed.


Lemma hashfin_agree (h1 h2 : heap) hc mp x md :
  (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
  forall lo, lo.1 != Lsd.1 ->
    get_heap (hash_fin PP N Dfin M R h1 hc mp x md) lo
    = get_heap (hash_fin PP N Dfin M R h2 hc mp x md) lo.
Proof.
move=> hag lo hlo. rewrite hash_finE.
case: (eqVneq lo.1 shrincs_fxmss_hcnt_loc.1) => [e|n1].
- by rewrite /get_heap /set_heap !setmE e eqxx.
- rewrite 2!(get_set_heap_neq _ shrincs_fxmss_hcnt_loc _ lo n1).
  case: (eqVneq lo.1 (shrincs_fxmss_rom_loc PP N Dfin M R).1) => [e2|n2].
  + by rewrite /get_heap /set_heap !setmE e2 eqxx.
  + rewrite 2!(get_set_heap_neq _ (shrincs_fxmss_rom_loc PP N Dfin M R) _ lo n2).
    exact: hag.
Qed.

Lemma forgefin_agree (h1 h2 : heap) fc mp pt md :
  (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
  forall lo, lo.1 != Lsd.1 ->
    get_heap (forge_fin PP N Dfin M R h1 fc mp pt md) lo
    = get_heap (forge_fin PP N Dfin M R h2 fc mp pt md) lo.
Proof.
move=> hag lo hlo. rewrite forge_finE.
case: (eqVneq lo.1 shrincs_fxmss_fcnt_loc.1) => [e|n1].
- by rewrite /get_heap /set_heap !setmE e eqxx.
- rewrite 2!(get_set_heap_neq _ shrincs_fxmss_fcnt_loc _ lo n1).
  case: (eqVneq lo.1 (shrincs_fxmss_rom_loc PP N Dfin M R).1) => [e2|n2].
  + by rewrite /get_heap /set_heap !setmE e2 eqxx.
  + rewrite 2!(get_set_heap_neq _ (shrincs_fxmss_rom_loc PP N Dfin M R) _ lo n2).
    exact: hag.
Qed.

(** M5: the [signfin_agree] / [signfin_st_agree] / [signfin_lsd_agree] /
    [signfin_out] helpers (for a [sign4_step]-based SIGN case) are DEAD
    — the SIGN case is discharged by the inline lockstep [sign_walk_eq]
    below (via [agree_set] / [lsd_set]).  They are dropped here because
    the lifted [sign_fin] signature changed (extra [us : chMap (…) 'unit]
    used-set argument, [mz : M × ('nat × 'nat)] input). *)

Lemma hashfin_lsd_agree (h1 h2 : heap) hc mp x md :
  get_heap h1 Lsd = get_heap h2 Lsd ->
  get_heap (hash_fin PP N Dfin M R h1 hc mp x md) Lsd
  = get_heap (hash_fin PP N Dfin M R h2 hc mp x md) Lsd.
Proof. move=> he. by rewrite hash_finE !get_set_heap_neq. Qed.

Lemma forgefin_lsd_agree (h1 h2 : heap) fc mp pt md :
  get_heap h1 Lsd = get_heap h2 Lsd ->
  get_heap (forge_fin PP N Dfin M R h1 fc mp pt md) Lsd
  = get_heap (forge_fin PP N Dfin M R h2 fc mp pt md) Lsd.
Proof. move=> he. by rewrite forge_finE !get_set_heap_neq. Qed.


(** Two G4m runs whose heaps agree off [Lsd], and additionally agree on
    [Lsd] once [Lst] is set, give the same output distribution.  Lsd is
    read only by SIGN (which needs [Lst = Some]); GEN re-draws it. *)
#[local] Opaque sign_fin forge_fin hash_fin.
#[local] Opaque repro_hop.G3c G4m.

(** ** One-layer heap helpers for the SIGN direct walk.

    [g4_lsd_indep_sign] (below) walks [sign4_body] on h1/h2 in lockstep
    rather than materialising [sign4_step]'s RHS twice.  Its leaves apply
    [IH] to the explicit [set_heap]-chain heaps; these two lemmas peel one
    [set_heap] layer of the off-[Lsd] agreement and the [Lsd]-conditional
    so each chain leaf is discharged by [do ! apply: agree_set …] /
    [do ! apply: lsd_set …]. *)
Lemma agree_set (h1 h2 : heap) (L : Location) (v : L)
    (hL : L.1 != Lsd.1)
    (hag : forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) :
  forall lo, lo.1 != Lsd.1 ->
    get_heap (set_heap h1 L v) lo = get_heap (set_heap h2 L v) lo.
Proof.
move=> lo hlo.
case: (eqVneq lo.1 L.1) => [e|n].
- by rewrite /get_heap /set_heap !setmE e eqxx.
- rewrite !(get_set_heap_neq _ L _ lo n). exact: hag.
Qed.

Lemma lsd_set (h1 h2 : heap) (L : Location) (v : L)
    (hL : L.1 != Lsd.1) (hLst : L.1 != (shrincs_fxmss_st_loc PP N).1)
    (hlsd : get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) :
  get_heap (set_heap h1 L v) (shrincs_fxmss_st_loc PP N) ->
  get_heap (set_heap h1 L v) Lsd = get_heap (set_heap h2 L v) Lsd.
Proof.
(* Provide the [<>] side-conditions EXPLICITLY (as [eq_sym]-flipped hyps).
   The terse [rewrite (get_set_heap_neq ...) ?eq_sym //] form instead leaves
   the [<>] obligation to a [?eq_sym //] that -- over the abstract dependent
   [v : L] -- sends the elaborator into a multi-GB blowup (this lemma is
   applied at every SIGN-walk leaf, so that pathology dominated the whole
   file; see the digest-hop kernel-cost analysis). *)
have hLst' : (shrincs_fxmss_st_loc PP N).1 != L.1 by rewrite eq_sym.
have hL' : Lsd.1 != L.1 by rewrite eq_sym.
rewrite (get_set_heap_neq _ L _ (shrincs_fxmss_st_loc PP N) hLst') => hstSome.
rewrite (get_set_heap_neq _ L _ Lsd hL') (get_set_heap_neq _ L _ Lsd hL').
exact: (hlsd hstSome).
Qed.


(** ** Per-oracle splits of the [g4_lsd_indep] induction.

    The monolithic [g4_lsd_indep] proof OOM-kills (~48 GB) because the
    kernel [Qed] holds the leaf-heavy terms of ALL FOUR oracle cases
    simultaneously.  We extract each oracle case into its OWN top-level
    [Qed]-sealed lemma, taking the induction hypothesis [IH] (the property
    for the continuation [k]) as an EXPLICIT hypothesis.  Each [Qed] frees
    its memory before the next, so the whole file fits.  The main proof
    then just runs the induction and discharges each oracle by
    [apply: g4_lsd_indep_<oracle>] (passing [IH]). *)

(** GEN: both runs reset [Lsd] to the same fresh fill and recurse with
    heaps agreeing everywhere. *)
Lemma g4_lsd_indep_gen {T' : choiceType}
    (x : 'list 'bool) (k : (PP × N) -> raw_code T')
    (IH : forall (v : PP × N) (b : bool) (h1 h2 : heap) (z : T'),
        (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
        (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
        dfst (Pr_code (code_link (k v) (G4M b)) h1) z
        = dfst (Pr_code (code_link (k v) (G4M b)) h2) z) :
  forall (b : bool) (h1 h2 : heap) (z : T'),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (code_link (opr (mkopsig FXGEN ('list 'bool) (PP × N)) x k) (G4M b)) h1) z
    = dfst (Pr_code (code_link (opr (mkopsig FXGEN ('list 'bool) (PP × N)) x k) (G4M b)) h2) z.
Proof.
move=> b h1 h2 z hoff hlsd. cbn [code_link].
rewrite resolve_g4m_gen [X in X = _]gen4_step [X in _ = X]gen4_step.
have hst : get_heap h1 (shrincs_fxmss_st_loc PP N) = get_heap h2 (shrincs_fxmss_st_loc PP N).
{ by apply: hoff. }
rewrite -hst.
case: (~~ _ && _) => //.
apply: eq_dlet_at => pp. apply: eq_dlet_at => xn.
apply: eq_dlet_at => xr. apply: eq_dlet_at => xss.
apply: eq_dlet_at => sdm.
apply: (IH _ b _ _ z).
* move=> lo' hlo'.
  rewrite !(get_set_heap_neq _ Lsd _ lo' hlo').
  case: (eqVneq lo'.1 (shrincs_fxmss_st_loc PP N).1) => [e1|ne1].
  - by rewrite /get_heap /set_heap !setmE e1 eqxx.
  - rewrite !(get_set_heap_neq _ (shrincs_fxmss_st_loc PP N) _ lo' ne1).
    exact: hoff.
* move=> _. by rewrite 2!get_set_heap_eq.
Qed.

(** SIGN's lockstep walk, with the continuation kept fully ABSTRACT.

    THE memory AND time lever for SIGN on this box.  [sign_walk_eq] takes
    the post-resolve continuation [kk] as an OPAQUE PARAMETER and assumes
    the [IH]-shaped agreement [Hk].  Its statement and proof therefore
    mention NO game term — the huge [code_link _ (G4M b)] enters only once,
    when [g4_lsd_indep_sign] instantiates [kk] and [apply:]s this lemma.

    - Every [case:] ([< q_s], [Lst], [< #leaves], [Lrt], [Lrom], [Lsd],
      [fxsignx]) builds its motive over the small abstract [kk], so the
      walk's proof term stays small.
    - Crucially the kernel [Qed] never has to CONVERT [code_link _ (G4M b)]
      (it is not in the term), so the check is fast — the inline
      [set KC]-then-[apply IH] variant instead zeta-exposes the game at
      every leaf and the kernel spends >15 min converting it.

    Both heaps are walked in lockstep: each [get] is stepped by
    [Pr_code_get] and its read VALUE unified across h1/h2 by [Hoff]/[Hlsd]
    BEFORE any [case:], so only ONE case tree is built (we never call
    [sign4_step], whose two-sided RHS materialisation was the original
    ~44 GB wall).  The leaf [≠]-side conditions go through [agree_set] /
    [lsd_set] (the latter MUST supply its [≠] hyps explicitly — see its
    proof). *)
#[local] Opaque sign_fin.
Lemma sign_walk_eq {T' : choiceType}
    (mz : M × ('nat × 'nat)) (kk : 'option (shrincs_fxmss_game_signature N R) -> raw_code T') (z : T')
    (Hk : forall (v : 'option (shrincs_fxmss_game_signature N R)) (h1 h2 : heap),
        (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
        (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
        dfst (Pr_code (kk v) h1) z = dfst (Pr_code (kk v) h2) z) :
  forall (h1 h2 : heap),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (bind (sign4_body PP N Dfin M R F Tl Hgrind Htree
                           dR dDu S_wn c_max h_sf q_s mz) kk) h1) z
    = dfst (Pr_code (bind (sign4_body PP N Dfin M R F Tl Hgrind Htree
                           dR dDu S_wn c_max h_sf q_s mz) kk) h2) z.
Proof.
move=> h1 h2 hoff hlsd.
rewrite /sign4_body. cbn [bind].
(* sc ← get shrincs_fxmss_scnt_loc ;; #assert (sc < q_s) *)
rewrite 2!Pr_code_get -(hoff shrincs_fxmss_scnt_loc) //.
case: ((get_heap h1 shrincs_fxmss_scnt_loc < q_s)%N); last by rewrite 2!dPr_bind_fail.
rewrite !assertD_true. cbn [bind].
(* st ← getSome Lst *)
rewrite 2!Pr_code_get -(hoff (shrincs_fxmss_st_loc PP N)) //.
case Est: (get_heap h1 (shrincs_fxmss_st_loc PP N)) => [st|]; last by rewrite 2!dPr_bind_fail.
rewrite !assertD_true. cbn [getSome bind].
(* The used set, log, random-oracle map, and randomness table agree by
   [hoff]. *)
rewrite 8!Pr_code_get.
rewrite -(hoff shrincs_fxmss_used_loc) // -(hoff (shrincs_fxmss_log_loc M)) //
        -(hoff (shrincs_fxmss_rom_loc PP N Dfin M R)) // -(hoff (shrincs_fxmss_rt_loc M R)) //.
(* [Lsd] read (used only on the table-miss branch below) agrees via [hlsd]
   and [Est]. *)
have hsd : get_heap h1 Lsd = get_heap h2 Lsd by apply: hlsd; rewrite Est.
(* The validation guard is [leaf_okP ... && (zi notin used)]. On false,
   bump [shrincs_fxmss_scnt_loc] and return [None];
   guard-true: table hit / miss (miss reads the presampled [Lsd] slot
   [lidx st.2.1 mz.2]).  Each spine leaf inlines the [fxsignx] [case]-split
   directly; agreement via [do ! apply: agree_set / lsd_set]. *)
case: ([&& leaf_okP h_sf st.2.1 mz.2
         & mz.2 \notin domm (get_heap h1 shrincs_fxmss_used_loc)]); last first.
{ (* guard false: both bump [shrincs_fxmss_scnt_loc], return [None]. *)
  cbn [bind]. rewrite 2!Pr_code_put.
  apply: (Hk None).
  { apply: agree_set; first by []; exact: hoff. }
  apply: lsd_set; [by []|by []|]; exact: hlsd. }
case: (getm (get_heap h1 (shrincs_fxmss_rt_loc M R)) (mz.2, mz.1)) => [r|].
- (* table hit: #put shrincs_fxmss_used_loc ; #put Lrt ; md ← Lrom ; #put Lrom ; fxsignx *)
  cbn [bind]. rewrite 4!Pr_code_put.
  case: (getm (get_heap h1 (shrincs_fxmss_rom_loc PP N Dfin M R))
            (r, (st.1, (mz.2, mz.1)))) => [md|].
  + cbn [bind]. rewrite 2!Pr_code_put.
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
      cbn [bind].
    { rewrite 4!Pr_code_put. apply: (Hk (Some sg)).
      { do ! (apply: agree_set; first by []); exact: hoff. }
      do ! (apply: lsd_set; [by []|by []|]); exact: hlsd. }
    rewrite 2!Pr_code_put. apply: (Hk None).
    { do ! (apply: agree_set; first by []); exact: hoff. }
    do ! (apply: lsd_set; [by []|by []|]); exact: hlsd.
  + rewrite bind_assoc. cbn [bind]. rewrite 2!dPr_dist.
    apply: eq_dlet_at => md.
    cbn [bind]. rewrite 2!Pr_code_put.
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
      cbn [bind].
    { rewrite 4!Pr_code_put. apply: (Hk (Some sg)).
      { do ! (apply: agree_set; first by []); exact: hoff. }
      do ! (apply: lsd_set; [by []|by []|]); exact: hlsd. }
    rewrite 2!Pr_code_put. apply: (Hk None).
    { do ! (apply: agree_set; first by []); exact: hoff. }
    do ! (apply: lsd_set; [by []|by []|]); exact: hlsd.
- (* table miss: r ← dR ; sd ← get Lsd ; md ← sd[lidx …] ; #put×3 ; fxsignx *)
  rewrite bind_assoc. cbn [bind]. rewrite 2!dPr_dist.
  apply: eq_dlet_at => r.
  cbn [bind]. rewrite 2!Pr_code_get -hsd.
  case: (getm (get_heap h1 Lsd) (lidx h_sf st.2.1 mz.2)) => [md|].
  + cbn [bind]. rewrite 6!Pr_code_put.
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
      cbn [bind].
    { rewrite 4!Pr_code_put. apply: (Hk (Some sg)).
      { do ! (apply: agree_set; first by []); exact: hoff. }
      do ! (apply: lsd_set; [by []|by []|]); exact: hlsd. }
    rewrite 2!Pr_code_put. apply: (Hk None).
    { do ! (apply: agree_set; first by []); exact: hoff. }
    do ! (apply: lsd_set; [by []|by []|]); exact: hlsd.
  + rewrite bind_assoc. cbn [bind]. rewrite 2!dPr_dist.
    apply: eq_dlet_at => md.
    cbn [bind]. rewrite 6!Pr_code_put.
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => [sg|];
      cbn [bind].
    { rewrite 4!Pr_code_put. apply: (Hk (Some sg)).
      { do ! (apply: agree_set; first by []); exact: hoff. }
      do ! (apply: lsd_set; [by []|by []|]); exact: hlsd. }
    rewrite 2!Pr_code_put. apply: (Hk None).
    { do ! (apply: agree_set; first by []); exact: hoff. }
    do ! (apply: lsd_set; [by []|by []|]); exact: hlsd.
Qed.

(** SIGN: thin wrapper.  Resolve [opr]/[code_link] to expose the
    [bind (sign4_body … x) (fun b0 => code_link (k b0) (G4M b))] shape, then
    [apply: sign_walk_eq] with [kk] the game-bearing continuation.  This is
    the ONLY place the game enters SIGN's proof term — once as the [kk] arg
    and once inside [IH]'s type — so the kernel [Qed] here is also small. *)
Lemma g4_lsd_indep_sign {T' : choiceType}
    (mz : M × ('nat × 'nat)) (k : 'option (shrincs_fxmss_game_signature N R) -> raw_code T')
    (IH : forall (v : 'option (shrincs_fxmss_game_signature N R)) (b : bool) (h1 h2 : heap) (z : T'),
        (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
        (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
        dfst (Pr_code (code_link (k v) (G4M b)) h1) z
        = dfst (Pr_code (code_link (k v) (G4M b)) h2) z) :
  forall (b : bool) (h1 h2 : heap) (z : T'),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (code_link (opr (mkopsig FXSIGN (M × ('nat × 'nat)) ('option (shrincs_fxmss_game_signature N R))) mz k) (G4M b)) h1) z
    = dfst (Pr_code (code_link (opr (mkopsig FXSIGN (M × ('nat × 'nat)) ('option (shrincs_fxmss_game_signature N R))) mz k) (G4M b)) h2) z.
Proof.
move=> b h1 h2 z hoff hlsd. cbn [code_link].
rewrite resolve_g4m_sign.
apply: (sign_walk_eq mz (fun b0 => code_link (k b0) (G4M b)) z) => //.
move=> v h1' h2'. exact: (IH v b h1' h2' z).
Qed.

(** HASH: does not read [Lsd]; sign-free, recurse with same invariant. *)
Lemma g4_lsd_indep_hash {T' : choiceType}
    (x : shrincs_fxmss_random_oracle_input PP N M R) (k : Dfin -> raw_code T')
    (IH : forall (v : Dfin) (b : bool) (h1 h2 : heap) (z : T'),
        (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
        (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
        dfst (Pr_code (code_link (k v) (G4M b)) h1) z
        = dfst (Pr_code (code_link (k v) (G4M b)) h2) z) :
  forall (b : bool) (h1 h2 : heap) (z : T'),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (code_link (opr (mkopsig FXHASH (shrincs_fxmss_random_oracle_input PP N M R) Dfin) x k) (G4M b)) h1) z
    = dfst (Pr_code (code_link (opr (mkopsig FXHASH (shrincs_fxmss_random_oracle_input PP N M R) Dfin) x k) (G4M b)) h2) z.
Proof.
move=> b h1 h2 z hoff hlsd. cbn [code_link].
rewrite resolve_g4m_hash [X in X = _]hash_step [X in _ = X]hash_step.
have hhcE : get_heap h1 shrincs_fxmss_hcnt_loc = get_heap h2 shrincs_fxmss_hcnt_loc by apply: hoff.
have hromE : get_heap h1 (shrincs_fxmss_rom_loc PP N Dfin M R)
           = get_heap h2 (shrincs_fxmss_rom_loc PP N Dfin M R) by apply: hoff.
rewrite -hhcE -hromE.
set hc := get_heap h1 shrincs_fxmss_hcnt_loc.
set Mp := get_heap h1 (shrincs_fxmss_rom_loc PP N Dfin M R).
pose recd := fun (md : Dfin) (hh : heap) =>
  dfst (Pr_code (code_link (k md) (G4M b))
    (hash_fin PP N Dfin M R hh hc Mp x md)).
have recE : forall md, recd md h1 z = recd md h2 z.
{ move=> md. rewrite /recd.
  apply: (IH _ b _ _ z).
  - move=> lo hlo. exact: (hashfin_agree h1 h2 hc Mp x md hoff lo hlo).
  - rewrite hashfin_st_lem => hstSome.
    apply: hashfin_lsd_agree. exact: (hlsd hstSome). }
case: ((hc < q_h)%N) => //.
case: (getm Mp x) => [md|].
* rewrite -/(recd md h1) -/(recd md h2). exact: (recE md).
* apply: eq_dlet_at => md. exact: (recE md).
Qed.

(** FORGE: lockstep walk, continuation kept ABSTRACT and game-free, for
    BOTH [b].  Replaces the original [[X in X=_]forge3_step [X in _=X]
    forge3_step] (b=true, double RHS materialisation) and [rewrite /=
    2!dPr_ret] (b=false, whose [/=] [simpl]s the full post-refactor
    bookkeeping body and runs minutes).  Walks each [get] with [Pr_code_get]
    unifying h1/h2 first, then the two [md] leaves apply [IH] via
    [agree_set]/[lsd_set].  No game term, no [/=], no [forge3_step]. *)
Lemma forge_walk_eq {T' : choiceType}
    (b : bool) (m : M) (sg : shrincs_fxmss_game_signature N R)
    (kk : 'bool -> raw_code T') (z : T')
    (Hk : forall (v : 'bool) (h1 h2 : heap),
        (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
        (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
        dfst (Pr_code (kk v) h1) z = dfst (Pr_code (kk v) h2) z) :
  forall (h1 h2 : heap),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (bind (forge3f_body PP N Dfin M R F Tl Hgrind Htree
                           dDu S_wn h_sf q_f b m sg) kk) h1) z
    = dfst (Pr_code (bind (forge3f_body PP N Dfin M R F Tl Hgrind Htree
                           dDu S_wn h_sf q_f b m sg) kk) h2) z.
Proof.
move=> h1 h2 hoff hlsd.
rewrite /forge3f_body. cbn [bind].
rewrite 2!Pr_code_get -(hoff shrincs_fxmss_fcnt_loc) //.
case: ((get_heap h1 shrincs_fxmss_fcnt_loc < q_f)%N); last by rewrite 2!dPr_bind_fail.
rewrite !assertD_true. cbn [bind].
rewrite 2!Pr_code_get -(hoff (shrincs_fxmss_st_loc PP N)) //.
case Est: (get_heap h1 (shrincs_fxmss_st_loc PP N)) => [st|]; last by rewrite 2!dPr_bind_fail.
rewrite !assertD_true. cbn [getSome bind].
rewrite 4!Pr_code_get -(hoff (shrincs_fxmss_log_loc M)) //
        -(hoff (shrincs_fxmss_rom_loc PP N Dfin M R)) //.
case: (get_heap h1 (shrincs_fxmss_rom_loc PP N Dfin M R) _) => [md|].
- cbn [bind]. rewrite 2!Pr_code_put.
  apply: (Hk _).
  { do ! (apply: agree_set; first by []); exact: hoff. }
  do ! (apply: lsd_set; [by []|by []|]); exact: hlsd.
- rewrite bind_assoc. cbn [bind]. rewrite 2!dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 2!Pr_code_put.
  apply: (Hk _).
  { do ! (apply: agree_set; first by []); exact: hoff. }
  do ! (apply: lsd_set; [by []|by []|]); exact: hlsd.
Qed.

(** FORGE: thin wrapper.  Resolve to [bind (forge3f_body ...) kk] then
    [apply: forge_walk_eq] with the game-bearing [kk].  As with SIGN, the
    game enters only via [kk]/[IH], so [forge_walk_eq]'s [rewrite 2!dPr_dist]
    over the [dDu] sample sees an OPAQUE [kk] (never the lifted game), so
    its [ValidCode]/associativity match stays on [c := dDu]. *)
Lemma g4_lsd_indep_forge {T' : choiceType}
    (x : (M × shrincs_fxmss_game_signature N R)) (k : 'bool -> raw_code T')
    (IH : forall (v : 'bool) (b : bool) (h1 h2 : heap) (z : T'),
        (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
        (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
        dfst (Pr_code (code_link (k v) (G4M b)) h1) z
        = dfst (Pr_code (code_link (k v) (G4M b)) h2) z) :
  forall (b : bool) (h1 h2 : heap) (z : T'),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (code_link (opr (mkopsig FXFORGE (M × shrincs_fxmss_game_signature N R) 'bool) x k) (G4M b)) h1) z
    = dfst (Pr_code (code_link (opr (mkopsig FXFORGE (M × shrincs_fxmss_game_signature N R) 'bool) x k) (G4M b)) h2) z.
Proof.
move: x => [m sg].
move=> b h1 h2 z hoff hlsd. cbn [code_link].
rewrite resolve_g4m_forge.
apply: (forge_walk_eq b m sg (fun b0 => code_link (k b0) (G4M b)) z) => //.
move=> v h1' h2'. exact: (IH v b h1' h2' z).
Qed.


Lemma g4_lsd_indep {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IG c) :
  forall (b : bool) (h1 h2 : heap) (z : T'),
    (forall lo, lo.1 != Lsd.1 -> get_heap h1 lo = get_heap h2 lo) ->
    (get_heap h1 (shrincs_fxmss_st_loc PP N) -> get_heap h1 Lsd = get_heap h2 Lsd) ->
    dfst (Pr_code (code_link c (G4M b)) h1) z
    = dfst (Pr_code (code_link c (G4M b)) h2) z.
Proof.
induction VA as [a | o x k Ho Hk IH | lo k Hl Hk IH
                | lo v k Hl Hk IH | op k Hk IH].
- (* ret *)
  move=> b h1 h2 z hoff hlsd. cbn [code_link]. by rewrite 2!dPr_ret.
- (* opr — each oracle case is an opaque per-oracle lemma so the kernel
     [Qed]s and frees each leaf-heavy term separately (see the kernel-cost analysis). *)
  fmap_invert Ho.
  + exact: (g4_lsd_indep_gen x k IH).
  + exact: (g4_lsd_indep_sign x k IH).
  + exact: (g4_lsd_indep_hash x k IH).
  + exact: (g4_lsd_indep_forge x k IH).
- (* getr *)
  move=> b h1 h2 z hoff hlsd. cbn [code_link].
  case/and5P: (dadvloc_neq _ Hl) => n1 n2 n3 n4 /and5P [n5 n6 n7 n8 n9].
  rewrite 2!Pr_code_get (hoff lo n9).
  exact: (IH (get_heap h2 lo) b h1 h2 z hoff hlsd).
- (* putr *)
  move=> b h1 h2 z hoff hlsd. cbn [code_link].
  case/and5P: (dadvloc_neq _ Hl) => n1 n2 n3 n4 /and5P [n5 n6 n7 n8 n9].
  rewrite 2!Pr_code_put.
  (* Provide the [≠] side-conditions EXPLICITLY (from [dadvloc_neq]'s
     [n1]/[n9], [eq_sym]-flipped).  The terse [rewrite … ?eq_sym //] form
     instead leaves them to [?eq_sym //] which — over the abstract [lo :
     Location] — blows the kernel [Qed] of this induction past 44 GB (the
     SAME pathology as the original [lsd_set]; see the digest-hop kernel-cost analysis). *)
  have nst : (shrincs_fxmss_st_loc PP N).1 != lo.1 by rewrite eq_sym.
  have nsd : Lsd.1 != lo.1 by rewrite eq_sym.
  apply: (IH b _ _ z).
  * move=> lo' hlo'.
    case: (eqVneq lo'.1 lo.1) => [e|ne].
    - by rewrite /get_heap /set_heap !setmE e eqxx.
    - rewrite (get_set_heap_neq _ lo _ lo' ne) (get_set_heap_neq _ lo _ lo' ne).
      exact: hoff.
  * rewrite (get_set_heap_neq _ lo _ (shrincs_fxmss_st_loc PP N) nst) => hstSome.
    rewrite (get_set_heap_neq _ lo _ Lsd nsd) (get_set_heap_neq _ lo _ Lsd nsd).
    exact: (hlsd hstSome).
- (* sampler *)
  move=> b h1 h2 z hoff hlsd. cbn [code_link].
  rewrite 2!dPr_sample. apply: eq_dlet_at => a.
  exact: (IH a b _ _ z hoff hlsd).
Qed.

End DigAdversary.
End FXMSSDigestBound.
