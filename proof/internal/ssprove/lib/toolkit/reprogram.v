(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.reprogram

    The CLASSICAL adaptive-reprogramming bound for the game pair of
    Shrincs.internal.ssprove.lib.toolkit.ro_plus.

    The carrier-independent theorems take a proved injective uniform
    enumeration of the prefix sampler. The ordinal theorems specialize
    these comparisons to ['fin n.+1]; reprogram_bytes applies them to
    independent byte tuples.

    ** Statements

    - [repro_bound]  : AdvOf (RO_repro …) A
                         <= qp%:R * ((qh + qp.-1)%:R / n.+1%:R)
    - [repro_bound_1] (the headline, [qp := 1]) :
                       AdvOf (RO_repro … 1) A <= qh%:R / n.+1%:R
      — no multi-query slack for one reprogramming query.

    For [qp > 1] the bound carries the documented slack [qp.-1]: the
    union bound here also counts collisions of the fresh prefix with
    points written by EARLIER reprogramming queries (harmless
    information-theoretically, but discounting them would need a
    "still-fresh set" generalisation of the coupling).

    ** Proof shape (no relational logic — everything at the
       [Pr_code]/[distr] semantics level)

    The two games differ only in the REPRO oracle: after the common
    fresh sample [r <- uniform], the [true] side overwrites the map
    at [(r, x)] with a fresh [y <- dR], the [false] side does
    nothing.  Two inductions over the adversary's [ValidCode]:

    - [gf_presample] ("lazy = eager at one fresh point"): presampling
      an UNQUERIED point of the lazy oracle and storing it is
      invisible: for [p ∉ dom M],
        Pr[c ∘ GF, h] = E_{y <- dR} Pr[c ∘ GF, h[map[p] := y]].
      This is the eager/lazy core that a step-by-step relational
      coupling cannot express (the stored value on one side couples
      with a sample that happens LATER on the other side).

    - [gt_gf_diff] (the master bound): with equal heaps on both
      sides,
        |Pr[c ∘ GT, h] - Pr[c ∘ GF, h]|
          <= (qp - rcnt(h))%:R * ((qh + qp.-1)%:R / n.+1%:R).
      At a REPRO call, for each prefix [r]: if [(r, x)] is already in
      the map ("bad", at most |dom M| <= qh + qp.-1 of the n.+1
      prefixes, by the invariant [rp_inv]), bound the difference by
      1; otherwise [gf_presample] rewrites the false side into the
      true side's shape (both continue with the SAME heap containing
      the fresh point), and the induction hypothesis applies — this
      is where "the reprogrammed point is fresh in both worlds"
      becomes a formal step.

    The probability machinery: [Pr_code]/[Pr_fst] stepping lemmas
    (SSProve nominal/Pr.v), [dletE]/[psum] (mathcomp
    experimental_reals), [dlet_uniform] (SSProve HybridArgument), and
    [Adv_nom_ind] to get from [Adv] (sep_link) to [AdvantageE]/[Pr]
    with a separated adversary. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import probability ro_plus.

From mathcomp Require Import reals distr realsum.

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** ** The instantiated game pair *)

Section ReprogramBound.
Context (n : nat) (Pfx X R : choice_type) (dPfx : dist Pfx).
Context (enc : 'I_n.+1 -> Pfx) (henc : injective enc).
Context (huniform : Pr_fst dPfx = dmargin enc (uniform n.+1).π2).
Context (dR : dist R) (dR_ll : LosslessCode dR).
Context (qh qp : nat).
Abbreviation IRO := (I_RO Pfx X R).
Abbreviation Gm b := (RO_repro Pfx X R dPfx dR qh qp b).
Abbreviation mloc := (ro_map_loc Pfx X R).
Abbreviation qloc := ro_qcnt_loc.
Abbreviation rloc := ro_rcnt_loc.
Abbreviation muR := (Pr_fst dR).

(* Distinctness of the game locations, by computation. *)
Lemma neq_qm : qloc.1 != mloc.1.  Proof. by []. Qed.
Lemma neq_rm : rloc.1 != mloc.1.  Proof. by []. Qed.
Lemma neq_rq : rloc.1 != qloc.1.  Proof. by []. Qed.

(** The one-point presample update: store [y] at the (fresh) point
    [p] of the oracle map. *)
Definition updm (h : heap) (p : chProd Pfx X) (y : R) : heap :=
  set_heap h mloc (setm (get_heap h mloc) p y).

(* The resolved oracle bodies, computed once. *)
Lemma resolve_query (b : bool) (q : chProd Pfx X) :
  resolve (Gm b) (mkopsig QUERY (chProd Pfx X) R) q =
  (qc ← get qloc ;;
   #assert (qc < qh)%N ;;
   #put qloc := qc.+1 ;;
   m ← get mloc ;;
   match getm m q with
   | Some y => ret y
   | None => y ← dR ;; #put mloc := setm m q y ;; ret y
   end).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

Lemma resolve_repro_false (x : X) :
  resolve (Gm false) (mkopsig REPRO X Pfx) x =
  (rc ← get rloc ;;
   #assert (rc < qp)%N ;;
   #put rloc := rc.+1 ;;
   r ← dPfx ;;
   ret r).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

Lemma resolve_repro_true (x : X) :
  resolve (Gm true) (mkopsig REPRO X Pfx) x =
  (rc ← get rloc ;;
   #assert (rc < qp)%N ;;
   #put rloc := rc.+1 ;;
   r ← dPfx ;;
   m ← get mloc ;;
   y ← dR ;;
   #put mloc := setm m (r, x) y ;;
   ret r).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

(* ------------------------------------------------------------------ *)
(** ** Invariant, loss term, and the union-bound step *)

(** Reachability invariant: the oracle map never has more entries
    than the number of successful QUERY calls plus the number of
    successful REPRO calls, and the query counter respects its cap. *)
Definition rp_inv (h : heap) : bool :=
  ((size (domm (get_heap h mloc)) <= get_heap h qloc + get_heap h rloc)
   && (get_heap h qloc <= qh))%N.

(** Per-reprogramming-query loss.  [qp.-1] is the documented slack
    for collisions of the fresh prefix with previously reprogrammed
    points (zero for [qp = 1], where this is the paper's
    [qh / |Pfx|]). *)
Definition rp_B : Axioms.R := (qh + qp.-1)%:R / n.+1%:R.

Lemma rp_B_ge0 : 0 <= rp_B.
Proof. by rewrite /rp_B divr_ge0 ?ler0n. Qed.

Lemma rp_bound_ge0 (m : nat) : 0 <= (qp - m)%:R * rp_B.
Proof. by rewrite mulr_ge0 ?ler0n ?rp_B_ge0. Qed.

(* ------------------------------------------------------------------ *)
(** ** The adversary side *)

Section Adversary.

Context (LA : Locations).
Context (sepL : fseparate LA [fmap mloc; qloc; rloc]).

Lemma advloc_neq (l : Location) :
  fhas LA l →
  [&& l.1 != mloc.1, l.1 != qloc.1 & l.1 != rloc.1].
Proof.
move=> hl.
have hn := notin_has_separate _ _ _ hl sepL.
rewrite domm_mkfmap !inE /= !negb_or in hn.
by case/and3P: hn => -> -> ->.
Qed.

(* [updm] commutes with writes to any other location. *)
Lemma updm_set_heap (l : Location) (v : l) h p y :
  l.1 != mloc.1 →
  updm (set_heap h l v) p y = set_heap (updm h p y) l v.
Proof.
move=> hneq.
rewrite /updm.
rewrite get_set_heap_neq; first by rewrite eq_sym.
by rewrite set_heap_commut.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The eager/lazy core: presampling one fresh point is invisible

    For any point [p] outside the domain of the oracle map,
    lazily-sampling-later (left) equals presampling-and-storing-now
    (right), in the [b = false] game.  This is an induction over the
    adversary's code at the semantics level; the crucial case is a
    QUERY at [p] itself, where the left side's lazy sample couples
    with the right side's presample. *)

Lemma gf_presample {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IRO c) :
  ∀ (h : heap) (p : chProd Pfx X),
    p \notin domm (get_heap h mloc) →
    ∀ z,
      dfst (Pr_code (code_link c (Gm false)) h) z
      = (\dlet_(y <- muR)
           dfst (Pr_code (code_link c (Gm false)) (updm h p y))) z.
Proof.
induction VA as [a | o x k Ho Hk IH | l k Hl Hk IH
                | l v k Hl Hk IH | op k Hk IH].
- (* ret *)
  move=> h p hp z. cbn [code_link].
  rewrite dPr_ret. symmetry.
  transitivity ((\dlet_(_ <- muR) dunit a) z).
  { apply: eq_dlet_at => y. by rewrite dPr_ret. }
  by rewrite (Pr_fstC dR_ll).
- (* opr: QUERY / REPRO *)
  fmap_invert Ho.
  + (* QUERY, argument x *)
    move=> h p hp z. cbn [code_link].
    rewrite resolve_query. cbn [bind].
    rewrite Pr_code_get.
    case E: ((get_heap h qloc < qh)%N); last first.
    { (* query budget exhausted: both sides fail *)
      rewrite assertD_false dPr_bind_fail. symmetry.
      apply: dlet_at0 => y.
      rewrite Pr_code_get /updm get_set_heap_neq //.
      by rewrite E assertD_false dPr_bind_fail. }
    rewrite assertD_true. cbn [bind].
    rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
    set qc := get_heap h qloc.
    set M := get_heap h mloc.
    set h1 := set_heap h qloc qc.+1.
    case Eq: (getm M x) => [y0 |].
    * (* answered from the map: x <> p, recurse *)
      have xnp : x != p.
      { apply: contraNneq hp => <-. by rewrite mem_domm Eq. }
      have hp1 : p \notin domm (get_heap h1 mloc).
      { by rewrite get_set_heap_neq. }
      cbn [bind].
      rewrite (IH y0 h1 p hp1 z).
      apply: eq_dlet_at => y.
      rewrite Pr_code_get /(updm h p y) get_set_heap_neq // E.
      rewrite assertD_true. cbn [bind].
      rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
      rewrite get_set_heap_eq setmE (negbTE xnp) Eq. cbn [bind].
      rewrite /updm get_set_heap_neq // -/M.
      by rewrite set_heap_commut.
    * (* not yet sampled *)
      rewrite bind_assoc. cbn [bind].
      rewrite dPr_dist.
      case: (eqVneq x p) => [xeqp | xnp].
      { (* x = p: the lazy sample IS the presample; no recursion *)
        rewrite -xeqp.
        apply: eq_dlet_at => y.
        rewrite Pr_code_put.
        rewrite Pr_code_get /(updm h x y) get_set_heap_neq // E.
        rewrite assertD_true. cbn [bind].
        rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
        rewrite get_set_heap_eq -/M setmE eqxx. cbn [bind].
        by rewrite set_heap_commut.
      }
      (* x <> p: recurse under the lazy sample, then swap *)
      have hpx : ∀ y', p \notin domm (setm M x y').
      { move=> y'. rewrite domm_set in_fset1U negb_or eq_sym xnp /=.
        exact: hp. }
      transitivity
        ((\dlet_(y' <- muR) \dlet_(y <- muR)
            dfst (Pr_code (code_link (k y') (Gm false))
                    (updm (set_heap h1 mloc (setm M x y')) p y))) z).
      { apply: eq_dlet_at => y'.
        rewrite Pr_code_put.
        apply: (IH y' _ p _ z).
        by rewrite get_set_heap_eq. }
      rewrite dlet_commut.
      apply: eq_dlet_at => y.
      rewrite Pr_code_get /(updm h p y) get_set_heap_neq // E.
      rewrite assertD_true. cbn [bind].
      rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
      rewrite get_set_heap_eq -/M setmE (negbTE xnp) Eq.
      rewrite bind_assoc. cbn [bind].
      rewrite dPr_dist.
      apply: eq_dlet_at => y'.
      rewrite Pr_code_put.
      rewrite /updm get_set_heap_eq set_heap_contract.
      rewrite (setmC _ _ _ xnp).
      rewrite [in X in _ = X]set_heap_commut //.
      rewrite [in X in _ = X]set_heap_contract.
      by rewrite /h1 set_heap_commut.
  + (* REPRO, argument x; b = false: nothing is written *)
    move=> h p hp z. cbn [code_link].
    rewrite resolve_repro_false. cbn [bind].
    rewrite Pr_code_get.
    case Er: ((get_heap h rloc < qp)%N); last first.
    { rewrite assertD_false dPr_bind_fail. symmetry.
      apply: dlet_at0 => y.
      rewrite Pr_code_get /updm get_set_heap_neq //.
      by rewrite Er assertD_false dPr_bind_fail. }
    rewrite assertD_true. cbn [bind].
    rewrite Pr_code_put.
    set rc := get_heap h rloc.
    set h1 := set_heap h rloc rc.+1.
    rewrite ?bind_ret dPr_dist.
    have hp1 : p \notin domm (get_heap h1 mloc).
    { by rewrite get_set_heap_neq. }
    transitivity
      ((\dlet_(r <- Pr_fst dPfx) \dlet_(y <- muR)
          dfst (Pr_code (code_link (k r) (Gm false)) (updm h1 p y))) z).
    { apply: eq_dlet_at => r. exact: (IH r h1 p hp1 z). }
    rewrite dlet_commut.
    apply: eq_dlet_at => y.
    rewrite Pr_code_get /(updm h p y) get_set_heap_neq // Er.
    rewrite assertD_true. cbn [bind].
    rewrite Pr_code_put.
    rewrite ?bind_ret dPr_dist.
    apply: eq_dlet_at => r.
    rewrite /updm get_set_heap_neq //.
    by rewrite set_heap_commut.
- (* getr (adversary location) *)
  move=> h p hp z. cbn [code_link].
  case/and3P: (advloc_neq _ Hl) => nm nq nr.
  rewrite Pr_code_get (IH _ h p hp z).
  apply: eq_dlet_at => y.
  rewrite Pr_code_get /updm get_set_heap_neq //.
- (* putr (adversary location) *)
  move=> h p hp z. cbn [code_link].
  case/and3P: (advloc_neq _ Hl) => nm nq nr.
  have hp' : p \notin domm (get_heap (set_heap h l v) mloc).
  { by rewrite get_set_heap_neq // eq_sym. }
  rewrite Pr_code_put (IH (set_heap h l v) p hp' z).
  apply: eq_dlet_at => y.
  by rewrite Pr_code_put updm_set_heap.
- (* sampler *)
  move=> h p hp z. cbn [code_link].
  rewrite dPr_sample.
  transitivity
    ((\dlet_(a <- op.π2) \dlet_(y <- muR)
        dfst (Pr_code (code_link (k a) (Gm false)) (updm h p y))) z).
  { apply: eq_dlet_at => a. exact: (IH a h p hp z). }
  rewrite dlet_commut.
  apply: eq_dlet_at => y.
  by rewrite dPr_sample.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The master bound: real vs ideal game from equal heaps

    [(qp - rcnt)%:R * rp_B] is the budget left for the remaining
    reprogramming queries.  The two linked codes differ only in the
    REPRO oracle; everything else steps in lockstep on the same
    heap. *)

Lemma gt_gf_diff {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IRO c) :
  ∀ h, rp_inv h → ∀ z,
    `| dfst (Pr_code (code_link c (Gm true)) h) z
     - dfst (Pr_code (code_link c (Gm false)) h) z |
    <= (qp - get_heap h rloc)%:R * rp_B.
Proof.
induction VA as [a | o x k Ho Hk IH | l k Hl Hk IH
                | l v k Hl Hk IH | op k Hk IH].
- (* ret *)
  move=> h hinv z. cbn [code_link].
  rewrite subrr normr0. exact: rp_bound_ge0.
- (* opr *)
  fmap_invert Ho.
  + (* QUERY: the two oracles run the same code *)
    move=> h hinv z. cbn [code_link].
    rewrite !resolve_query. cbn [bind].
    rewrite !Pr_code_get.
    case E: ((get_heap h qloc < qh)%N); last first.
    { rewrite !assertD_false !dPr_bind_fail subrr normr0.
      exact: rp_bound_ge0. }
    rewrite !assertD_true. cbn [bind].
    rewrite !Pr_code_put !Pr_code_get !get_set_heap_neq //.
    case/andP: hinv => i1 i2.
    set qc := get_heap h qloc.
    set M := get_heap h mloc.
    have rE : get_heap (set_heap h qloc qc.+1) rloc = get_heap h rloc.
    { by rewrite get_set_heap_neq. }
    case Eq: (getm M x) => [y0 |].
    * (* answered from the map *)
      cbn [bind].
      have hinv1 : rp_inv (set_heap h qloc qc.+1).
      { rewrite /rp_inv get_set_heap_eq rE get_set_heap_neq // -/M.
        apply/andP; split; last exact: E.
        apply: leq_trans i1 _. by rewrite addSn leqnSn. }
      rewrite -rE. exact: (IH y0 _ hinv1 z).
    * (* fresh query point: the two lazy samples couple *)
      rewrite !bind_assoc. cbn [bind].
      rewrite !dPr_dist.
      apply: dlet_diff_le; first exact: rp_bound_ge0.
      move=> y'.
      rewrite !Pr_code_put.
      have hinv2 : rp_inv
          (set_heap (set_heap h qloc qc.+1) mloc (setm M x y')).
      { rewrite /rp_inv get_set_heap_eq.
        rewrite !(get_set_heap_neq _ mloc) // get_set_heap_eq.
        rewrite (get_set_heap_neq _ qloc) //.
        apply/andP; split; last exact: E.
        rewrite domm_set sizesU1.
        apply: leq_trans (leq_add (leq_b1 _) i1) _.
        by rewrite add1n addSn leqnn. }
      have rE2 :
        get_heap (set_heap (set_heap h qloc qc.+1) mloc (setm M x y')) rloc
        = get_heap h rloc.
      { by rewrite !get_set_heap_neq. }
      rewrite -rE2. exact: (IH y' _ hinv2 z).
  + (* REPRO: the only difference between the games *)
    move=> h hinv z. cbn [code_link].
    rewrite resolve_repro_true resolve_repro_false. cbn [bind].
    rewrite !Pr_code_get.
    case Er: ((get_heap h rloc < qp)%N); last first.
    { rewrite !assertD_false !dPr_bind_fail subrr normr0.
      exact: rp_bound_ge0. }
    rewrite !assertD_true. cbn [bind].
    rewrite !Pr_code_put !bind_assoc; cbn [bind].
    rewrite ?bind_ret !dPr_dist.
    case/andP: hinv => i1 i2.
    set rc := get_heap h rloc.
    set M := get_heap h mloc.
    set c' := (qp - rc.+1)%:R * rp_B.
    have c'_ge0 : 0 <= c' by exact: rp_bound_ge0.
    have hcnt := sum_in_fset_le (λ r : 'I_n.+1, (enc r, x)) (domm M)
                   (ltac:(by move=> a b [heq]; exact: henc heq)).
    have HU := uniform_split_encoded n Pfx dPfx enc huniform
      _ _ (fun r => (r, x) \in domm M) _ _ _ c'_ge0 _ hcnt.
    apply: le_trans (HU _ _ _ _ _) _.
    * (* good prefixes: presample on the false side, recurse *)
      move=> r hgood.
      rewrite Pr_code_get get_set_heap_neq // -/M.
      rewrite bind_assoc. cbn [bind].
      rewrite dPr_dist.
      have hfresh :
        (r, x) \notin domm (get_heap (set_heap h rloc rc.+1) mloc).
      { by rewrite get_set_heap_neq. }
      rewrite (gf_presample (Hk r) _ _ hfresh z).
      apply: dlet_diff_le; first exact: c'_ge0.
      move=> y.
      rewrite Pr_code_put /updm get_set_heap_neq // -/M.
      have hinvH : rp_inv
          (set_heap (set_heap h rloc rc.+1) mloc (setm M (r, x) y)).
      { rewrite /rp_inv get_set_heap_eq.
        rewrite !(get_set_heap_neq _ mloc) //.
        rewrite (get_set_heap_neq _ rloc) // get_set_heap_eq.
        apply/andP; split; last exact: i2.
        rewrite domm_set sizesU1.
        apply: leq_trans (leq_add (leq_b1 _) i1) _.
        by rewrite add1n addnS leqnn. }
      have rEH :
        get_heap (set_heap (set_heap h rloc rc.+1) mloc (setm M (r, x) y))
          rloc = rc.+1.
      { by rewrite get_set_heap_neq // get_set_heap_eq. }
      have := IH r _ hinvH z.
      by rewrite rEH.
    * (* arithmetic: bad-set mass + remaining budget <= budget *)
      have rcle : (rc <= qp.-1)%N.
      { have qp0 : (0 < qp)%N := leq_ltn_trans (leq0n rc) Er.
        by rewrite -ltnS prednK. }
      have -> : (qp - rc)%:R * rp_B = rp_B + c'.
      { by rewrite /c' -(subnSK Er) mulrS mulrDl mul1r. }
      apply: lerD; last exact: lexx.
      rewrite /rp_B. apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
      rewrite ler_nat. apply: leq_trans i1 _. exact: leq_add i2 rcle.
- (* getr *)
  move=> h hinv z. cbn [code_link].
  rewrite !Pr_code_get. exact: (IH _ h hinv z).
- (* putr *)
  move=> h hinv z. cbn [code_link].
  case/and3P: (advloc_neq _ Hl) => nm nq nr.
  rewrite !Pr_code_put.
  have hinv' : rp_inv (set_heap h l v).
  { move: hinv. rewrite /rp_inv.
    by rewrite !get_set_heap_neq // eq_sym. }
  have rE : get_heap (set_heap h l v) rloc = get_heap h rloc.
  { by rewrite get_set_heap_neq // eq_sym. }
  rewrite -rE. exact: (IH _ hinv' z).
- (* sampler *)
  move=> h hinv z. cbn [code_link].
  rewrite !dPr_sample.
  apply: dlet_diff_le; first exact: rp_bound_ge0.
  move=> a. exact: (IH a h hinv z).
Qed.

End Adversary.

(* ------------------------------------------------------------------ *)
(** ** The reprogramming bound *)

Lemma repro_bound_uniform (A : nom_package)
    (VA : ValidPackage (loc A) IRO A_export A) :
  AdvOf (RO_repro Pfx X R dPfx dR qh qp) A <= qp%:R * rp_B.
Proof.
apply: (Adv_nom_ind _ _ _ IRO (λ x : Axioms.R, x <= qp%:R * rp_B)) => //.
move=> A' LA' VA' _ sep1 sep2.
rewrite /AdvantageE.
have hRUN : fhas A_export RUN by fmap_solve.
have VC := valid_resolve _ _ _ _ RUN tt VA' hRUN.
have inv0 : rp_inv empty_heap.
{ rewrite /rp_inv.
  have -> : get_heap empty_heap mloc = emptym by [].
  have -> : get_heap empty_heap qloc = 0%N by [].
  have -> : get_heap empty_heap rloc = 0%N by [].
  by rewrite domm0. }
rewrite 2!Pr_Pr_code 2!resolve_link.
apply: le_trans (gt_gf_diff LA' sep1 VC empty_heap inv0 true) _.
have -> : get_heap empty_heap rloc = 0%N by [].
by rewrite subn0.
Qed.

End ReprogramBound.

(** A finite carrier presented by an injective uniform enumeration. *)
Lemma repro_bound_finite (N : nat) (hN : (0 < N)%N)
  (Pfx X R : choice_type) (dPfx : dist Pfx) (enc : 'I_N -> Pfx)
  (henc : injective enc)
  (huniform : Pr_fst dPfx = dmargin enc (uniform N).π2)
  (dR : dist R) (dR_ll : LosslessCode dR) (qh qp : nat)
  (A : nom_package) (VA : ValidPackage (loc A) (I_RO Pfx X R) A_export A) :
  AdvOf (RO_repro Pfx X R dPfx dR qh qp) A
  <= qp%:R * ((qh + qp.-1)%:R / N%:R).
Proof.
case: N hN enc henc huniform => [|n] hN enc henc huniform //.
exact: (repro_bound_uniform n Pfx X R dPfx enc henc huniform
  dR dR_ll qh qp A VA).
Qed.

(** The ordinal specialization retains the original interface. *)
Lemma repro_bound (n : nat) (X R : choice_type)
  (dR : dist R) (dR_ll : LosslessCode dR) (qh qp : nat)
  (A : nom_package)
  (VA : ValidPackage (loc A) (I_RO (chFin n.+1) X R) A_export A) :
  AdvOf (RO_repro (chFin n.+1) X R (rp_d_pfx n) dR qh qp) A
  <= qp%:R * rp_B n qh qp.
Proof.
exact: (repro_bound_uniform n (chFin n.+1) X R (rp_d_pfx n)
  id (fun x y h => h) (rp_d_pfx_uniform n) dR dR_ll qh qp A VA).
Qed.

(** The paper's classical bound for ONE reprogramming query
    (reprogramming.tex, lemma:ROM reprogramming with [R := 1]):
    the distinguishing advantage is at most [qh / |Pfx|]. *)
Lemma repro_bound_1 (n : nat) (X R : choice_type)
    (dR : dist R) (dR_ll : LosslessCode dR) (qh : nat)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_RO (chFin n.+1) X R) A_export A) :
  (AdvOf (RO_repro (chFin n.+1) X R (rp_d_pfx n) dR qh 1) A
   <= qh%:R / n.+1%:R :> Axioms.R)%R.
Proof.
have := repro_bound n X R dR dR_ll qh 1 A VA.
by rewrite /rp_B addn0 mulr1n mul1r.
Qed.

(* Micro-test (proof/STYLE.md): the bound applies to the toy
   adversary of ROPlus.v at concrete parameters. *)
Module ReprogramTest.

Import ROPlusTest.

Lemma dB_ll : LosslessCode dB.
Proof. exact _. Qed.

Lemma test_bound :
  (AdvOf (RO_repro (chFin 3) 'nat 'bool (rp_d_pfx 2) dB 5 1) test_adv
   <= 5%:R / 3%:R :> Axioms.R)%R.
Proof. by apply: repro_bound_1. Qed.

End ReprogramTest.
