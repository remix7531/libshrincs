(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.lib.toolkit.reprogram

    The CLASSICAL adaptive-reprogramming bound for the game pair of
    Sec.lib.toolkit.ro_plus.

    Counterpart: resources/SHRINCS-security-specification/
    reprogramming.tex, lemma:ROM reprogramming — for a classical
    adversary making at most [qh] random-oracle queries and [qp]
    reprogramming queries,
      Adv^Repro(A) <= qp * qh / |Pfx|.
    This file proves it for the uniform prefix sampler over
    ['fin n.+1] (so |Pfx| = n.+1), the scope documented in the header
    of ROPlus.v.  This backs the SHRINCS hop F.2 -> F.3.

    ** Statements

    - [Repro_bound]  : AdvOf (RO_repro …) A
                         <= qp%:R * ((qh + qp.-1)%:R / n.+1%:R)
    - [Repro_bound_1] (the headline, [qp := 1]) :
                       AdvOf (RO_repro … 1) A <= qh%:R / n.+1%:R
      — exactly the paper's bound for one reprogramming query.

    For [qp > 1] the bound carries the documented slack [qp.-1]: the
    union bound here also counts collisions of the fresh prefix with
    points written by EARLIER reprogramming queries (harmless
    information-theoretically, but discounting them would need a
    "still-fresh set" generalisation of the coupling; the paper's
    informal proof skips this case silently).

    ** Proof shape (no relational logic — everything at the
       [Pr_code]/[distr] semantics level)

    The two games differ only in the REPRO oracle: after the common
    fresh sample [r <- uniform], the [true] side overwrites the map
    at [(r, x)] with a fresh [y <- dR], the [false] side does
    nothing.  Two inductions over the adversary's [ValidCode]:

    - [GF_presample] ("lazy = eager at one fresh point"): presampling
      an UNQUERIED point of the lazy oracle and storing it is
      invisible: for [p ∉ dom M],
        Pr[c ∘ GF, h] = E_{y <- dR} Pr[c ∘ GF, h[map[p] := y]].
      This is the eager/lazy core that a step-by-step relational
      coupling cannot express (the stored value on one side couples
      with a sample that happens LATER on the other side).

    - [GT_GF_diff] (the master bound): with equal heaps on both
      sides,
        |Pr[c ∘ GT, h] - Pr[c ∘ GF, h]|
          <= (qp - rcnt(h))%:R * ((qh + qp.-1)%:R / n.+1%:R).
      At a REPRO call, for each prefix [r]: if [(r, x)] is already in
      the map ("bad", at most |dom M| <= qh + qp.-1 of the n.+1
      prefixes, by the invariant [rp_inv]), bound the difference by
      1; otherwise [GF_presample] rewrites the false side into the
      true side's shape (both continue with the SAME heap containing
      the fresh point), and the induction hypothesis applies — this
      is where "the reprogrammed point is fresh in both worlds"
      becomes a formal step.

    The probability machinery: [Pr_code]/[Pr_fst] stepping lemmas
    (SSProve nominal/Pr.v), [dletE]/[psum] (mathcomp
    experimental_reals), [dlet_uniform] (SSProve HybridArgument), and
    [Adv_nom_ind] to get from [Adv] (sep_link) to [AdvantageE]/[Pr]
    with a separated adversary. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From Sec.lib Require Import prelude toolkit.ro_plus.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** ** Scalar-level distribution helpers

    The whole proof works with real-valued goals
    [dfst (Pr_code c h) z]; these lemmas do the [psum] plumbing once
    and for all. *)

Section DistrHelpers.

Context {A B : choiceType}.

(* Congruence for [\dlet] applied at a point, from pointwise-at-a-point
   equality of the bodies. *)
Lemma eq_dlet_at (mu : {distr A / Axioms.R}) (F G : A → {distr B / Axioms.R}) (z : B) :
  (∀ a, F a z = G a z) →
  (\dlet_(a <- mu) F a) z = (\dlet_(a <- mu) G a) z.
Proof. move=> H. rewrite 2!dletE. apply: eq_psum => a. by rewrite H. Qed.

(* |E_mu F - E_mu G| <= sup |F - G|, the "difference of two averages"
   step (mass of mu at most 1). *)
Lemma dlet_diff_le (mu : {distr A / Axioms.R}) (F G : A → {distr B / Axioms.R})
    (z : B) (eps : Axioms.R) :
  0 <= eps →
  (∀ a, `| F a z - G a z | <= eps) →
  `| (\dlet_(a <- mu) F a) z - (\dlet_(a <- mu) G a) z | <= eps.
Proof.
  move=> ge0e H.
  rewrite 2!dletE.
  have sumF : ∀ (F' : A → {distr B / Axioms.R}),
      summable (λ a, mu a * F' a z).
  { move=> F'. exact: (summable_mlet F' mu z). }
  have sumC : summable (λ a : A, mu a * eps).
  { apply: summableZr. exact: summable_mu. }
  have key : ∀ F' G' : A → {distr B / Axioms.R},
      (∀ a, F' a z - G' a z <= eps) →
      psum (λ a, mu a * F' a z) <= psum (λ a, mu a * G' a z) + eps.
  { move=> F' G' H'.
    apply: le_trans
      (_ : psum ((λ a, mu a * G' a z) \+ (λ a, mu a * eps)) <= _).
    - apply: le_psum; last first.
      + apply: summableD; [exact: sumF | exact: sumC].
      + move=> a; apply/andP; split.
        * by rewrite mulr_ge0 // ge0_mu.
        * rewrite /= -mulrDr ler_wpM2l ?ge0_mu //.
          by rewrite -lerBlDl.
    - have -> : psum ((λ a, mu a * G' a z) \+ (λ a, mu a * eps))
              = psum (λ a, mu a * G' a z) + psum (λ a : A, mu a * eps).
      { apply: psumD => //.
        - by move=> a; rewrite mulr_ge0 // ge0_mu.
        - by move=> a; rewrite mulr_ge0 // ge0_mu. }
      rewrite lerD2l psumZr // -[X in _ <= X]mul1r.
      apply: ler_wpM2r => //. exact: le1_mu. }
  have Hl : ∀ a, F a z - G a z <= eps.
  { move=> a; have := H a; by rewrite ler_norml => /andP []. }
  have Hr : ∀ a, G a z - F a z <= eps.
  { move=> a; have := H a; by rewrite distrC ler_norml => /andP []. }
  rewrite ler_norml; apply/andP; split.
  - rewrite lerNl opprB lerBlDr addrC. exact: (key _ _ Hr).
  - rewrite lerBlDr addrC. exact: (key _ _ Hl).
Qed.

(* Two (sub)probabilities are within distance 1. *)
Lemma norm_dist_le1 (mu nu : {distr B / Axioms.R}) (z : B) :
  `| mu z - nu z | <= 1.
Proof.
  rewrite ler_norml; apply/andP; split.
  - by rewrite lerNl opprB lerBlDr (le_trans (le1_mu1 nu z)) // lerDl ge0_mu.
  - by rewrite lerBlDr (le_trans (le1_mu1 mu z)) // lerDl ge0_mu.
Qed.

End DistrHelpers.

(* The union-bound counting step: the number of points of a finite
   type that an injection maps into a finite set is at most the size
   of that set. *)
Lemma sum_in_fset_le {T : finType} {K : ordType} (f : T → K) (s : {fset K}) :
  injective f →
  ((\sum_(r : T) ((f r \in s) : nat)) <= size s)%N.
Proof.
  move=> injf.
  have -> : (\sum_(r : T) ((f r \in s) : nat))%N
            = count (λ r, f r \in s) (index_enum T).
  { rewrite -sum1_count [in RHS]big_mkcond /=.
    by apply: eq_bigr => r _; case: (f r \in s). }
  rewrite -size_filter -(size_map f).
  apply: uniq_leq_size.
  - rewrite map_inj_uniq //. apply: filter_uniq. exact: index_enum_uniq.
  - move=> kk /mapP [r]. rewrite mem_filter => /andP [hin _] ->. exact: hin.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping lemmas for [dfst (Pr_code c h) z]

    [Pr_code_get]/[Pr_code_put] (full distribution equalities) are
    used directly; the lemmas here cover the steps where [dfst] has
    to commute into a [\dlet], plus the trivial endpoints.  All
    stated on the raw [dfst (Pr_code …) z] form so that they are
    usable as rewrite rules in the bound proofs. *)

Section DPrLemmas.

Context {T : choiceType}.

Lemma dPr_ge0 (c : raw_code T) h z : 0 <= dfst (Pr_code c h) z.
Proof. exact: ge0_mu. Qed.

Lemma dPr_le1 (c : raw_code T) h z : dfst (Pr_code c h) z <= 1.
Proof. exact: le1_mu1. Qed.

Lemma dPr_ret (a : T) h z : dfst (Pr_code (ret a) h) z = dunit a z.
Proof.
  rewrite Pr_code_ret.
  by rewrite (dmargin_dunit (a, h) fst).
Qed.

Lemma dPr_sample (op : Op) (k : Arit op → raw_code T) h z :
  dfst (Pr_code (sampler op k) h) z
  = (\dlet_(a <- op.π2) dfst (Pr_code (k a) h)) z.
Proof.
  rewrite (@Pr_code_sample T op k h).
  by rewrite dfst_dlet_commut.
Qed.

Lemma dPr_bind_fail (B : choice_type) (k : B → raw_code T) h z :
  dfst (Pr_code (bind (@fail B) k) h) z = 0.
Proof.
  rewrite /fail /= (@Pr_code_sample T _ _ h).
  rewrite dfst_dlet_commut.
  by rewrite dlet_null_ext dnullE.
Qed.

(* Sequencing a closed sampler (a [dist]) in front. *)
Lemma dPr_dist {T' : choiceType} (c : raw_code T')
    (k : T' → raw_code T) h z :
  ValidCode emptym [interface] c →
  dfst (Pr_code (bind c k) h) z
  = (\dlet_(a <- Pr_fst c) dfst (Pr_code (k a) h)) z.
Proof.
  move=> V.
  rewrite (Pr_code_fst V).
  by rewrite dfst_dlet_commut.
Qed.

(* A [\dlet] of pointwise-null bodies is null. *)
Lemma dlet_at0 {A : choiceType} (mu : {distr A / Axioms.R})
    (F : A → {distr T / Axioms.R}) (z : T) :
  (∀ a, F a z = 0) →
  (\dlet_(a <- mu) F a) z = 0.
Proof.
  move=> H. rewrite dletE. apply: psum_eq0 => a. by rewrite H mulr0.
Qed.

End DPrLemmas.

(* [assertD] computation rules, usable as rewrites after a [case] on
   the asserted boolean. *)
Lemma assertD_true {A : choice_type} (k : (true = true) → raw_code A) :
  assertD true k = k erefl.
Proof. by []. Qed.

Lemma assertD_false {A : choice_type} (k : (false = true) → raw_code A) :
  assertD false k = fail.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** The instantiated game pair *)

Section ReprogramBound.

Context (n : nat) (X R : choice_type).
Context (dR : dist R) (dR_ll : LosslessCode dR).
Context (qh qp : nat).

(** Uniform prefix sampler over ['fin n.+1] (|Pfx| = n.+1). *)
Definition rp_dPfx : dist (chFin n.+1) :=
  {code r ← sample uniform n.+1 ;; ret r}.

Notation Pfx := (chFin n.+1).
Notation IRO := (I_RO Pfx X R).
Notation Gm b := (RO_repro Pfx X R rp_dPfx dR qh qp b).
Notation mloc := (ro_map_loc Pfx X R).
Notation qloc := ro_qcnt_loc.
Notation rloc := ro_rcnt_loc.
Notation muR := (Pr_fst dR).

(* Distinctness of the game locations, by computation. *)
Lemma neq_qm : qloc.1 != mloc.1.  Proof. by []. Qed.
Lemma neq_rm : rloc.1 != mloc.1.  Proof. by []. Qed.
Lemma neq_rq : rloc.1 != qloc.1.  Proof. by []. Qed.

(** The one-point presample update: store [y] at the (fresh) point
    [p] of the oracle map. *)
Definition updm (h : heap) (p : chProd Pfx X) (y : R) : heap :=
  set_heap h mloc (setm (get_heap h mloc) p y).

(* The resolved oracle bodies, computed once. *)
Lemma resolve_QUERY (b : bool) (q : chProd Pfx X) :
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

Lemma resolve_REPRO_false (x : X) :
  resolve (Gm false) (mkopsig REPRO X Pfx) x =
  (rc ← get rloc ;;
   #assert (rc < qp)%N ;;
   #put rloc := rc.+1 ;;
   r ← rp_dPfx ;;
   ret r).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

Lemma resolve_REPRO_true (x : X) :
  resolve (Gm true) (mkopsig REPRO X Pfx) x =
  (rc ← get rloc ;;
   #assert (rc < qp)%N ;;
   #put rloc := rc.+1 ;;
   r ← rp_dPfx ;;
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

(** The union-bound step, isolated: a uniform prefix lands in a
    "bad" set of at most [m] values with probability [m / n.+1];
    outside the bad set the integrands are [c]-close. *)
Lemma uniform_split_le {B : choiceType}
    (Ft Ff : 'I_n.+1 → {distr B / Axioms.R})
    (bad : pred 'I_n.+1) (z : B) (c : Axioms.R) (m : nat) :
  0 <= c →
  (∀ r, ~~ bad r → `| Ft r z - Ff r z | <= c) →
  ((\sum_(r : 'I_n.+1) (bad r : nat)) <= m)%N →
  `| (\dlet_(r <- (uniform n.+1).π2) Ft r) z
   - (\dlet_(r <- (uniform n.+1).π2) Ff r) z |
  <= m%:R / n.+1%:R + c.
Proof.
  move=> ge0c hgood hcount.
  have nE : ((n.+1)%:~R : Axioms.R) = n.+1%:R by rewrite -pmulrn.
  have hinv : 0 <= ((n.+1)%:~R : Axioms.R)^-1 by rewrite invr_ge0 ler0z.
  rewrite 2!dlet_uniform -mulrBl normrM (ger0_norm hinv).
  rewrite nE ler_pdivrMr ?ltr0n //.
  rewrite mulrDl divfK ?pnatr_eq0 //.
  rewrite -sumrB.
  apply: le_trans (ler_norm_sum _ _ _) _.
  apply: le_trans (_ : \sum_(r : 'I_n.+1) ((bad r : nat)%:R + c) <= _).
  - apply: ler_sum => r _.
    case hb: (bad r).
    + apply: le_trans (norm_dist_le1 _ _ _) _.
      by rewrite mulr1n lerDl.
    + rewrite mulr0n add0r. apply: hgood. by rewrite hb.
  - rewrite big_split /=.
    apply: lerD.
    + rewrite -natr_sum ler_nat. exact: hcount.
    + apply: le_trans
        (UniformDistrLemmas.cardinality_bound _ (index_enum_uniq _) _ ge0c) _.
      by rewrite card_ord nE mulrC.
Qed.

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
  rewrite get_set_heap_neq; last by rewrite eq_sym.
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

Lemma GF_presample {T' : choiceType} {c : raw_code T'}
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
      rewrite resolve_QUERY. cbn [bind].
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
        { move=> y'. rewrite domm_set in_fsetU1 negb_or eq_sym xnp /=.
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
      rewrite resolve_REPRO_false. cbn [bind].
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
      rewrite /rp_dPfx. cbn [prog bind].
      rewrite dPr_sample.
      have hp1 : p \notin domm (get_heap h1 mloc).
      { by rewrite get_set_heap_neq. }
      transitivity
        ((\dlet_(r <- (uniform n.+1).π2) \dlet_(y <- muR)
            dfst (Pr_code (code_link (k r) (Gm false)) (updm h1 p y))) z).
      { apply: eq_dlet_at => r. exact: (IH r h1 p hp1 z). }
      rewrite dlet_commut.
      apply: eq_dlet_at => y.
      rewrite Pr_code_get /(updm h p y) get_set_heap_neq // Er.
      rewrite assertD_true. cbn [bind].
      rewrite Pr_code_put.
      rewrite /rp_dPfx. cbn [prog bind].
      rewrite dPr_sample.
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

Lemma GT_GF_diff {T' : choiceType} {c : raw_code T'}
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
      rewrite !resolve_QUERY. cbn [bind].
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
      rewrite resolve_REPRO_true resolve_REPRO_false. cbn [bind].
      rewrite !Pr_code_get.
      case Er: ((get_heap h rloc < qp)%N); last first.
      { rewrite !assertD_false !dPr_bind_fail subrr normr0.
        exact: rp_bound_ge0. }
      rewrite !assertD_true. cbn [bind].
      rewrite !Pr_code_put.
      rewrite /rp_dPfx. cbn [prog bind].
      rewrite !dPr_sample.
      case/andP: hinv => i1 i2.
      set rc := get_heap h rloc.
      set M := get_heap h mloc.
      set c' := (qp - rc.+1)%:R * rp_B.
      have c'_ge0 : 0 <= c' by exact: rp_bound_ge0.
      have hcnt := sum_in_fset_le (λ r : 'I_n.+1, (r, x)) (domm M)
                     (ltac:(by move=> a b [])).
      have HU := uniform_split_le _ _ _ _ _ _ c'_ge0 _ hcnt.
      apply: le_trans (HU _ _ _ _ _) _.
      * (* good prefixes: presample on the false side, recurse *)
        move=> r hgood.
        rewrite Pr_code_get get_set_heap_neq // -/M.
        rewrite bind_assoc. cbn [bind].
        rewrite dPr_dist.
        have hfresh :
          (r, x) \notin domm (get_heap (set_heap h rloc rc.+1) mloc).
        { by rewrite get_set_heap_neq. }
        rewrite (GF_presample (Hk r) _ _ hfresh z).
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

Theorem Repro_bound (A : nom_package)
    (VA : ValidPackage (loc A) IRO A_export A) :
  AdvOf (RO_repro Pfx X R rp_dPfx dR qh qp) A <= qp%:R * rp_B.
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
  apply: le_trans (GT_GF_diff LA' sep1 VC empty_heap inv0 true) _.
  have -> : get_heap empty_heap rloc = 0%N by [].
  by rewrite subn0.
Qed.

End ReprogramBound.

(** The paper's classical bound for ONE reprogramming query
    (reprogramming.tex, lemma:ROM reprogramming with [R := 1]):
    the distinguishing advantage is at most [qh / |Pfx|]. *)
Theorem Repro_bound_1 (n : nat) (X R : choice_type)
    (dR : dist R) (dR_ll : LosslessCode dR) (qh : nat)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_RO (chFin n.+1) X R) A_export A) :
  (AdvOf (RO_repro (chFin n.+1) X R (rp_dPfx n) dR qh 1) A
   <= qh%:R / n.+1%:R :> Axioms.R)%R.
Proof.
  have := Repro_bound n X R dR dR_ll qh 1 A VA.
  by rewrite /rp_B addn0 mulr1n mul1r.
Qed.

(* Micro-test (docs/STYLE.md rule 12): the bound applies to the toy
   adversary of ROPlus.v at concrete parameters. *)
Module ReprogramTest.

Import ROPlusTest.

Lemma dB_ll : LosslessCode dB.
Proof. exact _. Qed.

Lemma test_bound :
  (AdvOf (RO_repro (chFin 3) 'nat 'bool (rp_dPfx 2) dB 5 1) test_adv
   <= 5%:R / 3%:R :> Axioms.R)%R.
Proof. by apply: Repro_bound_1. Qed.

End ReprogramTest.
