(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.probability

    Pointwise distribution congruence and bounds, finite-set counting,
    and stepping rules for observable program probabilities. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp Require Import reals distr realsum.

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
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
    PosSum.psum (λ a, mu a * F' a z) <= PosSum.psum (λ a, mu a * G' a z) + eps.
{ move=> F' G' H'.
  apply: le_trans
    (_ : PosSum.psum ((λ a, mu a * G' a z) \+ (λ a, mu a * eps)) <= _).
  - apply: le_psum; last first.
    + apply: summableD; [exact: sumF | exact: sumC].
    + move=> a; apply/andP; split.
      * by rewrite mulr_ge0 // ge0_mu.
      * rewrite /= -mulrDr ler_wpM2l ?ge0_mu //.
        by rewrite -lerBlDl.
  - have -> : PosSum.psum ((λ a, mu a * G' a z) \+ (λ a, mu a * eps))
            = PosSum.psum (λ a, mu a * G' a z) + PosSum.psum (λ a : A, mu a * eps).
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
(** ** Uniform sampling and a bounded bad set *)

(** Uniform ordinal sampler used by the bound specializations. *)
Definition rp_d_pfx (n : nat) : dist (chFin n.+1) :=
  {code r ← sample uniform n.+1 ;; ret r}.

Lemma rp_d_pfx_uniform n :
  Pr_fst (rp_d_pfx n) = dmargin id (uniform n.+1).π2.
Proof.
rewrite /rp_d_pfx Pr_fst_sample.
apply: eq_dlet => r.
exact: Pr_fst_ret.
Qed.

Section UniformSplit.
Context (n : nat).
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

End UniformSplit.

Lemma uniform_split_encoded (n : nat) (Pfx : choice_type)
  (dPfx : dist Pfx) (enc : 'I_n.+1 -> Pfx)
  (huniform : Pr_fst dPfx = dmargin enc (uniform n.+1).π2)
  {B : choiceType} (Ft Ff : Pfx -> {distr B / Axioms.R})
  (bad : pred Pfx) (z : B) (c : Axioms.R) (m : nat) :
  0 <= c ->
  (forall r, ~~ bad r -> `|Ft r z - Ff r z| <= c) ->
  ((\sum_(r : 'I_n.+1) (bad (enc r) : nat)) <= m)%N ->
  `| (\dlet_(r <- Pr_fst dPfx) Ft r) z
    - (\dlet_(r <- Pr_fst dPfx) Ff r) z | <= m%:R / n.+1%:R + c.
Proof.
move=> hc hgood hcount.
rewrite huniform !dlet_dmargin.
apply: (uniform_split_le n _ _ (fun r => bad (enc r)) _ _ _ hc _ hcount).
by move=> r; apply: hgood.
Qed.
