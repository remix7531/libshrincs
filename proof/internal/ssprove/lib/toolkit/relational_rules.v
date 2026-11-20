(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.relational_rules

    Generic one-sided / semantic relational program-logic rules used by
    the WOTS+C block inductions.

    These step ONE side of a relational judgment while transforming an
    EXPLICIT precondition, and preserve the [bind _ k] spine
    SYNTACTICALLY (so applying them never forces the unifier to unfold
    [bind] into its raw fixpoint) -- properties the [rem_]/[set_]
    machinery of SSProve's stock rules does not provide under an
    induction over an unbounded query sequence. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp.experimental_reals Require Import distr.
From SSProve.Crypt Require Import SubDistr Couplings.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic one-sided / semantic judgment rules *)

Section SemanticRules.

(** Extract a pure consequence of the precondition. *)
Lemma r_fact {A B : choiceType} (P : Prop) (pre : precond)
    (c0 : raw_code A) (c1 : raw_code B) (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) -> P) ->
  (P -> ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> hP h.
apply rpre_hypothesis_rule => s0 s1 hpre.
eapply rpre_weaken_rule; first exact: (h (hP _ _ hpre)).
by move=> s0' s1' [e1 e2]; move: e1 e2 => /= -> ->.
Qed.

(** rhs get of a location whose value the precondition determines. *)
Lemma r_get_rhs_known {A B : choiceType} (ℓ : Location) (v : ℓ) (pre : precond)
    (c0 : raw_code A) (k1 : ℓ -> raw_code B) (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) -> get_heap s1 ℓ = v) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ k1 v ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ x ← get ℓ ;; k1 x ⦃ post ⦄.
Proof.
move=> hv h.
eapply r_get_remember_rhs => x.
eapply (r_fact (v = x)).
- move=> s0 s1 [hpre hrem].
  by rewrite -(hv _ _ hpre) -hrem.
- move=> e; subst x.
  eapply rpre_weaken_rule; first exact: h.
  by move=> ? ? [].
Qed.

(** rhs get under a bind (the [bind _ k] spine is preserved
    SYNTACTICALLY by all these rules, so that applying them never
    forces the unifier to unfold [bind] into its raw fixpoint). *)
Lemma r_get_bind_rhs {A B C : choiceType} (ℓ : Location) (v : ℓ)
    (pre : precond) (c0 : raw_code A)
    (f : ℓ -> raw_code B) (k1 : B -> raw_code C) (post : postcond A C) :
  (forall s0 s1, pre (s0, s1) -> get_heap s1 ℓ = v) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ bind (f v) k1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ bind (getr ℓ f) k1 ⦃ post ⦄.
Proof.
move=> hv h.
exact: (r_get_rhs_known ℓ v pre c0 (λ x, bind (f x) k1) post hv h).
Qed.

(** rhs assert under a bind, with the bool proved from the
    precondition. *)
Lemma r_bind_assertD_rhs {A C : choiceType} {B : choice_type} (b : bool)
    (pre : precond) (c0 : raw_code A)
    (f : b = true -> raw_code B) (k1 : B -> raw_code C)
    (post : postcond A C) :
  (forall s0 s1, pre (s0, s1) -> b = true) ->
  (forall e : b = true,
     ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ bind (f e) k1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ bind (assertD b f) k1 ⦃ post ⦄.
Proof.
move: f; case: b => f hb h; first exact: h.
by apply rpre_hypothesis_rule => s0 s1 /hb.
Qed.

(** rhs put with an explicit precondition transformer. *)
Lemma r_put_rhs_weak {A B : choiceType} (ℓ : Location) (v : ℓ)
    (pre pre' : precond) (c0 : raw_code A) (c1 : raw_code B)
    (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) -> pre' (s0, set_heap s1 ℓ v)) ->
  ⊢ ⦃ λ '(s0, s1), pre' (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ #put ℓ := v ;; c1 ⦃ post ⦄.
Proof.
move=> hp h.
apply r_put_rhs.
eapply rpre_weaken_rule; first exact: h.
by move=> s0 s1 [s1' [hpre ->]]; exact: hp.
Qed.

(** Two successive rhs puts, one transformer. *)
Lemma r_put2_rhs_weak {A B : choiceType} (ℓ1 : Location) (v1 : ℓ1)
    (ℓ2 : Location) (v2 : ℓ2)
    (pre pre' : precond) (c0 : raw_code A) (c1 : raw_code B)
    (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) ->
     pre' (s0, set_heap (set_heap s1 ℓ1 v1) ℓ2 v2)) ->
  ⊢ ⦃ λ '(s0, s1), pre' (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ #put ℓ1 := v1 ;; #put ℓ2 := v2 ;; c1 ⦃ post ⦄.
Proof.
move=> hp h.
apply r_put_rhs; apply r_put_rhs.
eapply rpre_weaken_rule; first exact: h.
by move=> s0 s1 [s1' [[s1'' [hpre ->]] ->]]; exact: hp.
Qed.

(** rhs put under a bind, with an explicit precondition
    transformer. *)
Lemma r_put_bind_rhs {A B C : choiceType} (ℓ : Location) (v : ℓ)
    (pre pre' : precond) (c0 : raw_code A)
    (c : raw_code B) (k1 : B -> raw_code C) (post : postcond A C) :
  (forall s0 s1, pre (s0, s1) -> pre' (s0, set_heap s1 ℓ v)) ->
  ⊢ ⦃ λ '(s0, s1), pre' (s0, s1) ⦄ c0 ≈ bind c k1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ c0 ≈ bind (putr ℓ v c) k1 ⦃ post ⦄.
Proof.
move=> hp h.
exact: (r_put_rhs_weak ℓ v pre pre' c0 (bind c k1) post hp h).
Qed.

(** Two successive rhs puts under a bind. *)
Lemma r_put2_bind_rhs {A B C : choiceType} (ℓ1 : Location) (v1 : ℓ1)
    (ℓ2 : Location) (v2 : ℓ2) (pre pre' : precond) (c0 : raw_code A)
    (c : raw_code B) (k1 : B -> raw_code C) (post : postcond A C) :
  (forall s0 s1, pre (s0, s1) ->
     pre' (s0, set_heap (set_heap s1 ℓ1 v1) ℓ2 v2)) ->
  ⊢ ⦃ λ '(s0, s1), pre' (s0, s1) ⦄ c0 ≈ bind c k1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄
     c0 ≈ bind (putr ℓ1 v1 (putr ℓ2 v2 c)) k1 ⦃ post ⦄.
Proof.
move=> hp h.
exact: (r_put2_rhs_weak ℓ1 v1 ℓ2 v2 pre pre' c0 (bind c k1) post hp h).
Qed.


(** Scheme-scheme commutation: two stateless, import-free pieces of
    code commute.  SSProve ships scheme-command swaps
    ([r_swap_cmd_scheme]); the scheme-scheme version follows by
    induction on the first scheme. *)
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

(** Eager-vs-lazy sampling alignment: the lhs samples [c0] first and
    then runs a block whose head samples [c1]; the equivalent form
    samples [c1] first.  Used ONCE to align an eager [pp ← dPP]
    with SM-TCR's lazy parameter sampling inside the first TQUERY. *)
Lemma r_swap_eager_lazy {A B C D : choiceType}
    (c0 : raw_code A) (c1 : raw_code B)
    (g : A -> B -> raw_code C) (K : A -> C -> raw_code D)
    (c1' : raw_code D) (pre : precond) (post : postcond D D) :
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
- (* bind c0 (λ x, bind c1 (λ y, ...)) ≈ bind c0 (λ x, bind (bind c1 (g x)) (K x)) *)
  eapply (rsame_head (f₀ := λ x, y ← c1 ;; bind (g x y) (K x))
                     (f₁ := λ x, bind (bind c1 (g x)) (K x))) => x.
  rewrite bind_assoc.
  exact: rreflexivity_rule.
- exact: (r_swap_scheme_scheme c1 c0 (λ y x, bind (g x y) (K x)) h1 h0).
Qed.

(** Both sides of a bind whose head is the same stateless,
    import-free code (a [dist] sampler, [sample_seq], ...) can be
    related by relating the continuations pointwise, under ANY
    precondition.  Specialization of [rsame_head_alt] to
    [L := emptym]; stated over [choiceType] (not [choice_type]) so
    that it unifies with goals whose carrier products have been
    reduced by [simpl]. *)
Lemma r_scheme_bind {A B : choiceType}
  (c : raw_code A) (f₀ f₁ : A -> raw_code B) pre (post : postcond B B) :
  ValidCode emptym [interface] c ->
  (forall a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄ x ← c ;; f₀ x ≈ x ← c ;; f₁ x ⦃ post ⦄.
Proof.
move=> hc hf.
eapply rsame_head_alt; first exact hc.
- by move=> [n T] hn.
- by move=> [n T] v hn.
- exact: hf.
Qed.

(** A failing program is related to any bind whose head fails (the
    composite has null semantics).  Used when one side aborts directly
    and the other aborts at the head of a linked computation.
    Same semantic proof as SSProve's [r_fail]. *)
Lemma r_fail_bind_rhs {A B C : choice_type} (k : B -> raw_code C)
    (pre : precond) (post : postcond A C) :
  ⊢ ⦃ pre ⦄ @fail A ≈ bind (@fail B) k ⦃ post ⦄.
Proof.
eapply from_sem_jdg. intros [s₀ s₁]. hnf. intro P. hnf.
intros [hpre hpost]. simpl.
exists dnull. split.
- unfold coupling. split.
  + unfold lmg. apply distr_ext.
    intro. unfold dfst. rewrite dlet_null.
    unfold SDistr_bind. rewrite dlet_null.
    reflexivity.
  + unfold rmg. apply distr_ext.
    intro. unfold dsnd. rewrite dlet_null.
    unfold SDistr_bind. rewrite dlet_null.
    reflexivity.
- intros [? ?] [? ?]. rewrite dnullE.
  rewrite Order.POrderTheory.ltxx. discriminate.
Qed.

(** A failing program is related to any stateless, import-free scheme
    [c] FOLLOWED by a fail: the trailing fail nulls the whole
    composite, so swapping it to the front ([r_swap_scheme_scheme])
    collapses the goal to [r_fail_bind_rhs] ([bind fail k] has null
    semantics).  The scheme generalization of SSProve's single-command
    [r_cmd_fail]; used for the sign-refusal COMMIT branch of the
    KOTS<->WOTS+C link (Shrincs.internal.ssprove.wots.kots_link), where the game side aborts
    outright and the keyed side samples its key/chain starts before
    the refused sign fails. *)
Lemma r_fail_scheme_rhs {A B C : choice_type} (c : raw_code B)
    (pre : precond) (post : postcond A C) :
  ValidCode emptym [interface] c ->
  ⊢ ⦃ pre ⦄ @fail A ≈ bind c (λ _, @fail C) ⦃ post ⦄.
Proof.
move=> hc.
eapply r_transR.
- (* move the trailing fail to the front:
     [x ← fail ;; y ← c ;; ret x ≈ y ← c ;; x ← fail ;; ret x]
     and the rhs collapses to [bind c (λ _, fail)] by [bind fail ret]. *)
  exact: (r_swap_scheme_scheme (@fail C) c (λ x _, ret x) (valid_fail C _ _) hc).
- (* [fail ≈ bind fail k] has null semantics. *)
  exact: r_fail_bind_rhs.
Qed.

(** rhs-only get whose value the precondition pins, WITHOUT a bind spine
    (companion to [r_get_rhs_known]; the SM-UD query loop reads pinned
    rhs oracle state directly under a continuation [k]). *)
Lemma r_get_rhs_pin {A B : choiceType} (ℓ : Location) (v : ℓ)
    (pre : precond) (c₀ : raw_code A) (k : ℓ -> raw_code B)
    (post : postcond A B) :
  (forall s₀ s₁, pre (s₀, s₁) -> get_heap s₁ ℓ = v) ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ k v ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ x ← get ℓ ;; k x ⦃ post ⦄.
Proof.
(* Same statement as [r_get_rhs_known] (up to binder names); re-export it. *)
exact: r_get_rhs_known.
Qed.

(** rhs-only put with an explicit precondition transformer, WITHOUT a
    bind spine (companion to [r_put_rhs_weak]). *)
Lemma r_put_rhs_pre {A B : choiceType} (ℓ : Location) (v : ℓ)
    (pre pre' : precond) (c₀ : raw_code A) (c₁ : raw_code B)
    (post : postcond A B) :
  (forall s₀ s₁, pre (s₀, s₁) -> pre' (s₀, set_heap s₁ ℓ v)) ->
  ⊢ ⦃ λ '(s₀, s₁), pre' (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ #put ℓ := v ;; c₁ ⦃ post ⦄.
Proof.
(* Same statement as [r_put_rhs_weak] (up to binder names); re-export it. *)
exact: r_put_rhs_weak.
Qed.

(** [heap_ignore] is preserved by a one-sided write to an ignored
    location (rhs / lhs forms). *)
Lemma heap_ignore_set_r (L : Locations) (ℓ : Location) (v : ℓ)
    (s₀ s₁ : heap) :
  ℓ.1 \in domm L ->
  heap_ignore L (s₀, s₁) -> heap_ignore L (s₀, set_heap s₁ ℓ v).
Proof.
move=> hin h; rewrite /heap_ignore => ℓ' hl'.
rewrite get_set_heap_neq; last exact: h.
by apply/eqP => e; rewrite e hin in hl'.
Qed.

Lemma heap_ignore_set_l (L : Locations) (ℓ : Location) (v : ℓ)
    (s₀ s₁ : heap) :
  ℓ.1 \in domm L ->
  heap_ignore L (s₀, s₁) -> heap_ignore L (set_heap s₀ ℓ v, s₁).
Proof.
move=> hin h; rewrite /heap_ignore => ℓ' hl'.
rewrite get_set_heap_neq; last exact: h.
by apply/eqP => e; rewrite e hin in hl'.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Exact denotational transport *)

Lemma r_pr_code_rhs_state {A B : choiceType} (pre pre' : precond)
    (post : postcond A B) (c0 : raw_code A) (c1 c1' : raw_code B)
    (f : heap -> heap) :
  (forall h0 h1, pre (h0,h1) -> Pr_code c1 h1 = Pr_code c1' (f h1)) ->
  (forall h0 h1, pre (h0,h1) -> pre' (h0,f h1)) ->
  ⊢ ⦃ pre' ⦄ c0 ≈ c1' ⦃ post ⦄ ->
  ⊢ ⦃ pre ⦄ c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> he hf h.
eapply from_sem_jdg.
intros [s0 s1].
hnf.
intro P.
hnf.
intros [hp hpost].
pose proof (to_sem_jdg _ _ _ _ h (s0,f s1)) as hh.
hnf in hh.
specialize (hh P).
hnf in hh.
cbn in hh |- *.
have [d [hd hs]] := hh (conj (hf _ _ hp) hpost).
exists d; split; last exact hs.
have he' := he s0 s1 hp.
cbn in he'.
rewrite /SubDistr.SDistr_obligation_2 !SDistr_rightneutral in he'.
cbn in he'.
by rewrite he'.
Qed.

Lemma r_pr_code_rhs {A B : choiceType} (pre : precond)
    (post : postcond A B) (c0 : raw_code A) (c1 c1' : raw_code B) :
  (forall h0 h1, pre (h0,h1) -> Pr_code c1 h1 = Pr_code c1' h1) ->
  ⊢ ⦃ pre ⦄ c0 ≈ c1' ⦃ post ⦄ ->
  ⊢ ⦃ pre ⦄ c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> he h.
exact: (r_pr_code_rhs_state pre pre post c0 c1 c1' id he (fun _ _ h => h) h).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Deterministic return facts *)

Lemma r_ret_lhs_fact {A B : choiceType} (x : A) (c : raw_code B)
  (pre : precond) (post : postcond A B) :
⊢ ⦃ pre ⦄ ret x ≈ c ⦃ post ⦄ ->
⊢ ⦃ pre ⦄ ret x ≈ c
  ⦃ fun '(y,s0) '(z,s1) => y = x /\ post (y,s0) (z,s1) ⦄.
Proof.
move=> hc.
apply from_sem_jdg.
move=> [s0 s1].
rewrite /RulesStateProb.θ /= /SpecificationMonads.MonoCont_order /=.
move=> pi [hp hpost].
have hh := to_sem_jdg _ _ _ _ hc (s0,s1).
rewrite /RulesStateProb.θ /= /SpecificationMonads.MonoCont_order /= in hh.
case: (hh (fun '(a,b) => post a b) (conj hp (fun _ _ h => h))) => d [hd hpos].
exists d; split; first exact: hd.
move=> [y t0] [z t1] hpositive.
apply: hpost.
split; last exact: hpos hpositive.
have he : (x,s0) = (y,t0).
{
  case: (eqVneq (x,s0) (y,t0)) => [he|hne]; first exact: he.
  have hn : (x,s0) <> (y,t0) by apply/eqP.
  have hz := @lmg_SDistr_unit _ _ (x,s0) d (proj1 hd) (y,t0) (z,t1) hn.
  by rewrite hz Order.POrderTheory.ltxx in hpositive.
}
by case: he.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reflexivity with separate read and write obligations *)

Fixpoint code_stable (pre : precond) {A : choiceType} (c : raw_code A) : Prop :=
  match c with
  | ret _ => True
  | opr _ _ _ => False
  | getr l k => get_pre_cond l pre /\ forall x, code_stable pre (k x)
  | putr l v k => put_pre_cond l v pre /\ code_stable pre k
  | sampler _ k => forall x, code_stable pre (k x)
  end.

Lemma code_stable_bind (pre : precond) {A B : choiceType}
    (c : raw_code A) (k : A -> raw_code B) :
  code_stable pre c -> (forall x, code_stable pre (k x)) ->
  code_stable pre (bind c k).
Proof.
elim: c => [x|o x f ih|l f ih|l v c ih|o f ih] /= => hc hk //.
- (* Reads preserve the precondition and continue. *)
  case: hc => hg hc; split=> // x; exact: ih x (hc x) hk.
- (* Writes preserve the precondition and continue. *)
  case: hc => hp hc; split=> //; exact: ih hc hk.
- (* Every sample continuation is stable. *)
  move=> x; exact: ih x (hc x) hk.
Qed.

Lemma code_stable_valid {A : choiceType} (L : Locations) (pre : precond)
    (c : raw_code A) :
  ValidCode L [interface] c ->
  (forall l, fhas L l -> get_pre_cond l pre) ->
  (forall l v, fhas L l -> put_pre_cond l v pre) ->
  code_stable pre c.
Proof.
move=> hc hg hp.
elim: hc => /=.
- by [].
- by move=> [o [S T]] x k.
- move=> l k hl _ ih; split; [exact: hg l hl | exact ih].
- move=> l v k hl _ ih; split; [exact: hp l v hl | exact ih].
- by move=> o k _ ih.
Qed.

Lemma r_code_stable {A : choiceType} (pre : precond) (c : raw_code A) :
  code_stable pre c ->
  ⊢ ⦃ λ '(s0,s1), pre (s0,s1) ⦄ c ≈ c
  ⦃ λ '(x,s0) '(y,s1), x = y /\ pre (s0,s1) ⦄.
Proof.
elim: c => [x|o x k ih|l k ih|l v c ih|o k ih] /=.
- move=> _; apply: r_ret; by [].
- by [].
- (* Couple a read under its read-specific obligation. *)
  move=> [hg hk].
  eapply (rsame_head_cmd_alt (cmd_get l)).
  + exact: cmd_get_preserve_pre hg.
  + by move=> x; apply: ih; exact: hk.
- (* Couple a write under its write-specific obligation. *)
  move=> [hp hc].
  eapply (@rsame_head_cmd_alt _ _ (fun _ => _) (fun _ => _) (cmd_put l v)).
  + exact: cmd_put_preserve_pre hp.
  + by move=> []; apply: ih.
- (* Couple the sample and preserve every continuation. *)
  move=> hk.
  eapply (rsame_head_cmd_alt (cmd_sample o)).
  + apply: cmd_sample_preserve_pre.
  + by move=> x; apply: ih; exact: hk.
Qed.

End SemanticRules.
