(** * HBS.Examples.FixedSumOTS.TCRHop

    The SM-TCR reduction package of the FixedSumOTS security proof
    (PROOF_PLAN.md, step "G1 -> SM-TCR + SM-PRE split", TCR half) and
    its perfect equivalences on BOTH sides of the SM-TCR pair:

      [R_tcr_real  : perfect (I_KOTS FS) (G1v ... true)
                             (R_tcr ∘ SMTCR_game Tots Cots p_tcr true)]
      [R_tcr_ideal : perfect (I_KOTS FS) Gmid
                             (R_tcr ∘ SMTCR_game Tots Cots p_tcr false)]

    where [Gmid] is G1v-real with KFORGE answering false exactly on
    the classifier's TCR case — the intermediate game of the
    forgery-split triangle (its hop to G1v-ideal is the PRE half,
    PROOF_PLAN.md).  Hence
    [Adv (G1v true) Gmid <= AdvOf (SMTCR_game ...) (A ∘ R_tcr)] by the
    standard reduction steps at the consumer.

    ** Design (deviations from the obvious transliteration)

    - Query ORDER: instead of the two-block layout (all sigma queries,
      then all target-walk queries) suggested in PROOF_PLAN.md, the
      reduction commits the targets PER CHAIN, in chain order: for
      chain [i] with digit [d_i] and sampled root [u_i] it first makes
      the sigma query [TQUERY ((i, d_i - 1), u_i)] (none if [d_i = 0]),
      then walks the chain upward with one TQUERY per position
      [k = d_i .. w-2].  This interleaved order makes the relational
      proof ONE induction over the digit list (each chain is handled
      completely before the next), aligned with [sample_sig_roots] on
      the G1v side.  The CHECK index of target [(i,k)] is [q_index m i k]
      (all queries of earlier chains, plus the sigma query of chain [i]
      if any, plus the offset [k - d_i]); the bookkeeping lemma is
      [qnth_commit_queries].  The freshness of every TQUERY tweak is
      maintained LOCALLY by the induction invariants ([all (tlt i k)]
      within a chain, [all (.1 < st)] across chains) instead of a
      global uniqueness lemma, so [tcr_targets_tweaks_uniq] is not
      consumed here.
    - Budget: [p_tcr := l + l * w].  Chain [i] makes
      [(0 < d_i) + (w.-1 - d_i) <= 1 + w] queries ([nq]/[nqs]), so the
      total is at most [l * (1 + w) = p_tcr] ([nqs_le]).
    - [pp] flows through GETPP at the END of COMMIT (after all
      TQUERYs): COMMIT must output the public key, which contains
      [pp].  This also flips SM-TCR's phase, so KFORGE needs no GETPPS
      call at all: it reads the stored key.
    - KFORGE classifier: the pure function [tcr_decision] recomputes
      the forgery classification (the computable counterpart of
      [Analysis.forgery_classify]): the attacked chain is the FIRST
      [i] with [mstar_i < m_i] ([ohead] of a filter; existence from
      [forged_digit_lt]), signature values are accessed with the
      default-free [qnth s i := ohead (drop i s)] (the hash domain [N]
      has no canonical inhabitant).  Its spec [tcr_decisionP] is
      derived from [forgery_cases] + the nth-form verification lemmas
      of Analysis.v, instantiated at the computed chain (Analysis's
      [forgery_classify] only provides an existential witness).
      Branches that cannot fire on a verifying forgery return
      [ret true] = the G1v answer, so no deadness arguments are needed.
    - SIDE CONDITIONS [0 < l] and [1 < w] on [R_tcr_real] (the
      documented side-condition route of the task): they guarantee
      that chain 0 always makes a TQUERY directly after sampling its
      root, which is where SM-TCR's lazily sampled [pp] is aligned
      with G1v's eagerly sampled [pp] (one scheme-scheme swap).  The
      excluded cases are degenerate: [l = 0] or [w <= 1] admit at most
      one valid message, so no forgery exists and the KOTS advantage
      is trivially 0; they are handled separately by the consumer if
      ever needed.

    ** Proof architecture of [R_tcr_real]

    Invariant: [heap_ignore] over all nine private locations, joined
    with ONE [rel_app] relation [RT] over them: the G1v pk/log mirror
    R's pk/log, and R's pk determines the whole SM-TCR state (None:
    everything initial; Some pk: there exist [m, us] with the log,
    stored signature, key, committed fmap, tweak list and revealed
    flag all computed from [(pk.1, m, us)]).

    Inside COMMIT the invariant machinery is dropped (rpre_weaken) in
    favour of the EXPLICIT precondition family [blk_pre Φ ppo Q]
    (heaps satisfy Φ; SM-TCR's pp/rev/tws/tgts hold [ppo], [false],
    [unzip1 Q], [qmap_from 0 Q]); the committed-so-far list [Q] is the
    single induction variable.  The linked TQUERY body is stepped by
    small one-sided semantic rules ([r_get_rhs_known],
    [r_bind_assertD_rhs], [r_put_rhs_weak]) packaged as
    [r_tquery_known] (pp already sampled) and [r_tquery_first] (pp
    None; syncs SM-TCR's lazy [dPP] against G1v's eager one); on top
    sit the walk induction [r_walk_spec] and the per-chain induction
    [r_chains_spec].  The lazy/eager alignment swaps G1v's [pp ← dPP]
    past the root sample [u_0 ← dN] with [r_swap_scheme_scheme]
    (scheme-scheme commutation, derived from [r_swap_cmd_scheme] by
    induction; SSProve only ships scheme-command swaps). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Games.SMTCR Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic seq access: total nth via [ohead (drop i s)]

    The hash domain [N] is an abstract [choice_type] with no canonical
    inhabitant, so [nth] (which needs a default) is unusable inside
    code.  [qnth] is the option-valued variant; the lemmas connect it
    back to [nth] once a witness is at hand. *)

Section QNth.

Context {X : Type}.

Definition qnth (s : seq X) (i : nat) : option X := ohead (drop i s).

Lemma qnth_size (s : seq X) i x : qnth s i = Some x -> i < size s.
Proof.
rewrite /qnth; case: (ltnP i (size s)) => // hle.
by rewrite drop_oversize.
Qed.

Lemma qnth_nth (x0 : X) s i x : qnth s i = Some x -> nth x0 s i = x.
Proof.
by elim: s i => [|a s IH] [|i] //=; [case=> -> | exact: IH].
Qed.

Lemma qnth_some (s : seq X) i : i < size s -> exists x, qnth s i = Some x.
Proof.
move=> hi; rewrite /qnth; case E: (drop i s) => [|a r]; last by exists a.
have := size_drop i s; rewrite E /= => /esym/eqP.
by rewrite subn_eq0 leqNgt hi.
Qed.

Lemma qnth_cat_r (s t : seq X) j : qnth (s ++ t) (size s + j)%N = qnth t j.
Proof. by rewrite /qnth drop_cat ltnNge leq_addr /= addKn. Qed.

Lemma qnth_cat_l (s t : seq X) j : j < size s -> qnth (s ++ t) j = qnth s j.
Proof.
move=> hj; rewrite /qnth drop_cat hj.
case E: (drop j s) => [|a r] //=.
have := size_drop j s; rewrite E /= => /esym/eqP.
by rewrite subn_eq0 leqNgt hj.
Qed.

End QNth.

(* ------------------------------------------------------------------ *)
(** ** Insertion-ordered fmaps from lists

    SM-TCR's target map grows by [setm tgts (size tws) (t, m)], i.e.
    the j-th committed target lands at key j.  [qmap_from j Q] is the
    fmap holding list [Q] at keys [j, j+1, ...]; [qmap_from_rcons] is
    exactly the oracle's update step, [qmap_from_get] the CHECK-time
    lookup. *)

Section QMap.

Context {X : Type}.

Fixpoint qmap_from (j : nat) (Q : seq X) : {fmap nat -> X} :=
  if Q is e :: Q' then setm (qmap_from j.+1 Q') j e else emptym.

Lemma qmap_from_rcons j Q e :
  qmap_from j (rcons Q e) = setm (qmap_from j Q) (j + size Q)%N e.
Proof.
elim: Q j => [|a Q IH] j /=; first by rewrite addn0.
rewrite IH setmC; last by apply/negbT/gtn_eqF; rewrite addSn ltnS leq_addr.
by rewrite addSn addnS.
Qed.

Lemma qmap_from_get j Q i : getm (qmap_from j Q) (j + i)%N = qnth Q i.
Proof.
elim: Q j i => [|e Q IH] j i /=; first by rewrite emptymE /qnth; case: i.
rewrite setmE; case: i => [|i] /=.
- by rewrite addn0 eqxx.
- case: eqP => [heq|_].
  + have : j < (j + i.+1)%N by rewrite addnS ltnS leq_addr.
    by rewrite heq ltnn.
  + by rewrite -addSnnS IH.
Qed.

End QMap.

(* ------------------------------------------------------------------ *)
(** ** Generic one-sided / semantic judgment rules

    The block inductions below manipulate EXPLICIT preconditions, so
    they need rules that step ONE side of the judgment and transform
    the precondition semantically (the rem_/set_-machinery of SSProve
    keeps the precondition opaque, which does not survive an induction
    over an unbounded query sequence). *)

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

(** Symmetric lhs version (not needed below, kept for symmetry). *)
Lemma r_get_lhs_known {A B : choiceType} (ℓ : Location) (v : ℓ) (pre : precond)
    (k0 : ℓ -> raw_code A) (c1 : raw_code B) (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) -> get_heap s0 ℓ = v) ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ k0 v ≈ c1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ x ← get ℓ ;; k0 x ≈ c1 ⦃ post ⦄.
Proof.
move=> hv h.
eapply r_get_remember_lhs => x.
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

(** lhs put with an explicit precondition transformer. *)
Lemma r_put_lhs_weak {A B : choiceType} (ℓ : Location) (v : ℓ)
    (pre pre' : precond) (c0 : raw_code A) (c1 : raw_code B)
    (post : postcond A B) :
  (forall s0 s1, pre (s0, s1) -> pre' (set_heap s0 ℓ v, s1)) ->
  ⊢ ⦃ λ '(s0, s1), pre' (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ #put ℓ := v ;; c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> hp h.
apply r_put_lhs.
eapply rpre_weaken_rule; first exact: h.
by move=> s0 s1 [s0' [hpre ->]]; exact: hp.
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
    samples [c1] first.  Used ONCE to align G1v's eager [pp ← dPP]
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

End SemanticRules.

(* ------------------------------------------------------------------ *)
(** ** Tweak-order bookkeeping for freshness

    [tlt i k t]: tweak [t] was committed strictly before position
    [(i, k)] in the reduction's per-chain order. *)

Definition tlt (i k : nat) (t : nat * nat) : bool :=
  (t.1 < i) || ((t.1 == i) && (t.2 < k)).

Lemma tlt_notin i k (ts : seq (nat * nat)) :
  all (tlt i k) ts -> (i, k) \notin ts.
Proof.
move=> /allP h; apply/negP => hin.
by have := h _ hin; rewrite /tlt /= ltnn eqxx ltnn.
Qed.

Lemma all_tlt_widen i k (ts : seq (nat * nat)) :
  all (tlt i k) ts -> all (tlt i k.+1) ts.
Proof.
apply: sub_all => t; rewrite /tlt => /orP[-> //|/andP[e hk]].
by rewrite e ltnS (ltnW hk) orbT.
Qed.

Lemma all_lt_tlt i k (ts : seq (nat * nat)) :
  all (λ t : nat * nat, t.1 < i) ts -> all (tlt i k) ts.
Proof. by apply: sub_all => t; rewrite /tlt => ->. Qed.

Lemma all_tlt_lt i k (ts : seq (nat * nat)) :
  all (tlt i k) ts -> all (λ t : nat * nat, t.1 < i.+1) ts.
Proof.
apply: sub_all => t; rewrite /tlt => /orP[h|/andP[/eqP -> _]] //.
exact: ltnW.
Qed.

Lemma lt_notin st d' (ts : seq (nat * nat)) :
  all (λ t : nat * nat, t.1 < st) ts -> (st, d') \notin ts.
Proof.
move=> /allP h; apply/negP => hin.
by have := h _ hin; rewrite /= ltnn.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The reduction and its analysis *)

Section TCRHop.

(** Same section context as FixedSumOTS.Games / Analysis. *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (l w tsum : nat).

Local Notation FS := (FixedSumOTS PP N F dPP dN l w tsum).
Local Notation TT := (Tots PP N F dPP dN).
Local Notation CC := (Cots PP N F dPP dN).
Local Notation cf := (chainf PP N F).

(** SM-TCR budget: [l] sigma queries plus at most [l * w] walk
    queries (crude but provable; see [nqs_le]). *)
Definition p_tcr : nat := l + l * w.

Local Notation pp_loc' := (tcr_pp_loc TT).
Local Notation tgts_loc' := (tcr_tgts_loc TT).
Local Notation tws_loc' := (tcr_tws_loc TT).
Local Notation rev_loc' := tcr_rev_loc.

Local Notation g0v_pk' := (g0v_pk_loc PP N F dPP dN l w tsum).
Local Notation g0v_log' := (g0v_log_loc PP N F dPP dN l w tsum).

(* ------------------------------------------------------------------ *)
(** *** Pure layer: committed queries, signatures, ends, indices *)

(** The committed (tweak, input) pairs live in the carrier of SM-TCR's
    target entry type. *)
Local Notation qentry := ((nat * nat) * N)%type.

(** Signature digit of chain [i] with digit [d] from root [u]
    (the pure shape of [sample_sig_roots]'s entries). *)
Definition sig_of_root (pp : PP) (i d : nat) (u : N) : N :=
  if d is d'.+1 then F pp (i, d') u else u.

(** Queries of the upward walk of chain [i]: positions [k .. k+n-1],
    inputs the successive chain values from [x] at [k]. *)
Definition walkq (pp : PP) (i k n : nat) (x : N) : seq qentry :=
  [seq ((i, (j + k)%N), chain (cf pp i) x k j) | j <- iota 0 n].

Lemma size_walkq pp i k n x : size (walkq pp i k n x) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma walkq_cons pp i k n x :
  walkq pp i k n.+1 x
  = ((i, k), x) :: walkq pp i k.+1 n (F pp (i, k) x).
Proof.
rewrite /walkq /=; congr (_ :: _).
rewrite -[1]/(1 + 0)%N iotaDl -map_comp.
apply: eq_map => j /=.
by rewrite add1n addSnnS.
Qed.

Lemma walkq_tweak1 pp i k n x :
  all (λ t : nat * nat, (t.1 == i)%B) (unzip1 (walkq pp i k n x)).
Proof.
rewrite /walkq /unzip1 -map_comp all_map.
by apply/allP => j _ /=.
Qed.

(** Every walk tweak has position [< k + n]. *)
Lemma walkq_tweak2 pp i k n x b :
  (k + n <= b)%N ->
  all (λ t : nat * nat, (t.2 < b)%N) (unzip1 (walkq pp i k n x)).
Proof.
move=> hb; rewrite /walkq /unzip1 -map_comp all_map.
apply/allP => j; rewrite mem_iota add0n => /andP[_ hj] /=.
by rewrite addnC; apply: leq_trans hb; rewrite ltn_add2l.
Qed.

(** All queries of one chain: the sigma query (for positive digits)
    followed by the walk from the signature position. *)
Definition chain_queries (pp : PP) (i d : nat) (u : N) : seq qentry :=
  (if d is d'.+1 then [:: ((i, d'), u)] else [::])
  ++ walkq pp i d (w.-1 - d) (sig_of_root pp i d u).

(** Number of queries of one chain / of a digit list. *)
Definition nq (d : nat) : nat := (0 < d) + (w.-1 - d).
Definition nqs (ds : seq nat) : nat := sumn [seq nq d | d <- ds].

Lemma size_chain_queries pp i d u : size (chain_queries pp i d u) = nq d.
Proof. by rewrite size_cat size_walkq /nq; case: d. Qed.

Lemma chain_queries_tweaks pp i d u :
  all (λ t : nat * nat, (t.1 == i)%B) (unzip1 (chain_queries pp i d u)).
Proof.
rewrite /chain_queries unzip1_cat all_cat walkq_tweak1 andbT.
by case: d => //= d; rewrite eqxx.
Qed.

(** Full committed list, chains [st, st+1, ...] with digits [ds] and
    roots [us]. *)
Definition commit_queries (pp : PP) (st : nat) (ds : seq nat) (us : seq N) :
    seq qentry :=
  flatten [seq chain_queries pp q.1 q.2.1 q.2.2
          | q <- zip (iota st (size ds)) (zip ds us)].

Lemma commit_queries_cons pp st d ds u us :
  commit_queries pp st (d :: ds) (u :: us)
  = chain_queries pp st d u ++ commit_queries pp st.+1 ds us.
Proof. by []. Qed.

(** Budget cap: [nqs] of any [l]-digit message fits in [p_tcr]. *)
Lemma nqs_le (ds : seq nat) : size ds = l -> nqs ds <= p_tcr.
Proof.
move=> hsz.
have hall : all (λ x, x <= w.+1) [seq nq d | d <- ds].
  apply/allP => x /mapP[d _ ->]; rewrite /nq.
  apply: (@leq_trans (1 + w.-1)%N).
  - by apply: leq_add; [case: (0 < d) | exact: leq_subr].
  - by rewrite add1n ltnS leq_pred.
have := sumn_all_leq _ _ hall.
by rewrite size_map hsz /p_tcr mulnSr addnC.
Qed.

(** Signature digits and public ends, generalized over the start
    chain so the inductions go through ([sigs_of pp 0 m us] is the
    value [sample_sig_roots] returns, [ends_of pp 0 m _] is
    [ends_from_sig]). *)
Definition sigs_of (pp : PP) (st : nat) (ds : seq nat) (us : seq N) : seq N :=
  [seq sig_of_root pp q.1 q.2.1 q.2.2 | q <- zip (iota st (size ds)) (zip ds us)].

Lemma size_sigs_of pp st ds us :
  size us = size ds -> size (sigs_of pp st ds us) = size ds.
Proof. by move=> h; rewrite size_map !size_zip size_iota h !minnn. Qed.

Lemma qnth_sigs_of pp st ds us i ui :
  size us = size ds -> i < size ds -> qnth us i = Some ui ->
  qnth (sigs_of pp st ds us) i
  = Some (sig_of_root pp (st + i)%N (nth 0 ds i) ui).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu.
- by case: hu => <-; rewrite addn0.
- by rewrite -addSnnS; apply: IH.
Qed.

Definition ends_of (pp : PP) (st : nat) (ds : seq nat) (sgs : seq N) : seq N :=
  [seq chain (cf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota st (size ds)) (zip ds sgs)].

Lemma ends_of_from_sig pp (m : seq nat) (sgs : seq N) :
  size m = l ->
  ends_of pp 0 m sgs = ends_from_sig PP N F l w pp m sgs.
Proof. by move=> hm; rewrite /ends_of /ends_from_sig hm. Qed.

(** CHECK index of the walk target [(i, k)] in the committed order. *)
Definition q_index (ds : seq nat) (i k : nat) : nat :=
  nqs (take i ds) + ((0 < nth 0 ds i) + (k - nth 0 ds i)).

(** Position of [(i,k)] inside one chain's queries. *)
Lemma qnth_chain_queries pp i d u k :
  d <= k < w.-1 ->
  qnth (chain_queries pp i d u) ((0 < d) + (k - d))
  = Some ((i, k), chain (cf pp i) (sig_of_root pp i d u) d (k - d)).
Proof.
move=> /andP[hdk hkw].
have hdw : d < w.-1 := leq_ltn_trans hdk hkw.
have hlt : k - d < w.-1 - d := ltn_sub2r hdw hkw.
have hw : qnth (walkq pp i d (w.-1 - d) (sig_of_root pp i d u)) (k - d)
          = Some ((i, k), chain (cf pp i) (sig_of_root pp i d u) d (k - d)).
  rewrite /qnth /walkq -map_drop (drop_nth 0) ?size_iota //=.
  by rewrite nth_iota // add0n subnK.
by case: d hdk hdw hlt hw => [|d'] hdk hdw hlt hw; rewrite /chain_queries //=.
Qed.

(** THE bookkeeping lemma: at index [q_index ds i k] the reduction
    committed exactly tweak [(st+i, k)] with input the honest chain
    value at [k] (recomputed from the signature digit). *)
Lemma qnth_commit_queries pp st ds us i k ui :
  size us = size ds -> i < size ds -> qnth us i = Some ui ->
  nth 0 ds i <= k < w.-1 ->
  qnth (commit_queries pp st ds us) (q_index ds i k)
  = Some (((st + i)%N, k),
          chain (cf pp (st + i)%N) (sig_of_root pp (st + i)%N (nth 0 ds i) ui)
                (nth 0 ds i) (k - nth 0 ds i)%N).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu hk.
- case: hu => <-; rewrite addn0 /q_index /= add0n.
  rewrite qnth_cat_l ?size_chain_queries; last first.
    rewrite /nq ltn_add2l; apply: ltn_sub2r; last by case/andP: hk.
    by apply: leq_ltn_trans (proj1 (andP hk)) (proj2 (andP hk)).
  exact: qnth_chain_queries.
- rewrite /q_index /= -addnA.
  rewrite -(size_chain_queries pp st d u) qnth_cat_r.
  by rewrite -addSnnS; apply: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The forgery classifier (computable counterpart of
    [Analysis.forgery_classify]) *)

(** Decide what the reduction submits for a forgery [(mstar, sgstar)]
    against signed message [m], stored signature [sgs] (and public
    parameter [pp]): [Some (j, u)] means "call CHECK (j, u)" (the TCR
    case), [None] means "the PRE case (or a branch that cannot occur
    on a verifying forgery)" — the reduction then returns [true],
    matching G1v's answer. *)
Definition tcr_decision (pp : PP) (m mstar : seq nat) (sgs sgstar : seq N) :
    option (nat * N) :=
  match ohead [seq i <- iota 0 l | nth 0 mstar i < nth 0 m i] with
  | Some i =>
      match qnth sgs i, qnth sgstar i with
      | Some si, Some si' =>
          match chain_extract (cf pp i) si' (nth 0 mstar i) si (nth 0 m i) w.-1 with
          | ChainColl k u _ => Some (q_index m i k, u)
          | ChainMeet => None
          end
      | _, _ => None
      end
  | None => None
  end.

(** Specification: on a verifying fresh forgery against the G1v key,
    a [Some (j, u)] decision points at a committed pair [(t, v)] with
    [u != v] and [F pp t u = F pp t v] — exactly SM-TCR's CHECK win
    condition at index [j]. *)
Lemma tcr_decisionP (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg l w tsum m -> size us = l ->
  verify_sig PP N F l w tsum pp
    (ends_of pp 0 m (sigs_of pp 0 m us)) mstar sgstar ->
  mstar \notin [:: m] ->
  match tcr_decision pp m mstar (sigs_of pp 0 m us) sgstar with
  | Some (j, u) =>
      exists t v,
        [/\ qnth (commit_queries pp 0 m us) j = Some (t, v),
            u != v & F pp t u = F pp t v]
  | None => True
  end.
Proof.
move=> hvm hus hver hnin.
have hm : size m = l by case/and3P: hvm => /eqP.
have hussz : size us = size m by rewrite hus hm.
have hsgs : size (sigs_of pp 0 m us) = l by rewrite size_sigs_of // hm.
rewrite (ends_of_from_sig pp m _ hm) in hver.
rewrite /tcr_decision.
case E1: (ohead _) => [i|]; last by [].
have hifacts : i \in [seq i0 <- iota 0 l | nth 0 mstar i0 < nth 0 m i0].
  by case: (filter _ _) E1 => //= a s [<-]; rewrite in_cons eqxx.
move: hifacts; rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
case E2: (qnth (sigs_of pp 0 m us) i) => [si|]; last by [].
case E3: (qnth sgstar i) => [si'|]; last by [].
have hdw : nth 0 m i < w := valid_msg_digit _ _ _ _ _ hvm hil.
have hends := size_ends_from_sig PP N F l w pp m _ hm hsgs.
have h1 := verify_sig_nth PP N F l w tsum pp _ mstar sgstar si' i hver hends hil.
rewrite (ends_from_sig_nth PP N F l w pp m _ si' i hm hsgs hil) in h1.
rewrite (qnth_nth si' _ _ _ E3) (qnth_nth si' _ _ _ E2) in h1.
have := forgery_cases PP N F w pp i (nth 0 m i) si (nth 0 mstar i) si' hlt hdw h1.
case E4: (chain_extract _ _ _ _ _ _) => [k u v|]; last by [].
move=> [hk hv hne hcol].
have hilm : i < size m by rewrite hm.
have [ui hui] : exists ui, qnth us i = Some ui.
  by apply: qnth_some; rewrite hus.
have hsig : sig_of_root pp i (nth 0 m i) ui = si.
  have h2 := qnth_sigs_of pp 0 m us i ui hussz hilm hui.
  rewrite add0n E2 in h2.
  by case: h2 => ->.
exists (i, k), v; split.
- have h2 := qnth_commit_queries pp 0 m us i k ui hussz hilm hui hk.
  by rewrite add0n hsig -hv in h2.
- exact: hne.
- exact: hcol.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

(** TQUERY/GETPP/CHECK opsigs as committed to I_SMTCR. *)
Definition tqo : opsig := (TQUERY, (th_T TT × th_M TT, th_N TT)).
Definition gpo : opsig := (GETPP, ('unit, th_PP TT)).
Definition cko : opsig := (CHECK, ('nat × th_M TT, 'bool)).

(** Walk chain [i] upward from value [x] at position [k] for [n]
    steps, one TQUERY per step; returns the value at [k + n]. *)
Fixpoint r_walk (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr tqo ((i, k), x) (λ y, r_walk i k.+1 n' y)
  else ret x.

#[local] Instance r_walk_valid (L : Locations) i k n x :
  ValidCode L (I_SMTCR TT CC) (r_walk i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> y; exact: IH.
Qed.

(** All chains from index [st] with digits [ds]: per chain, sample
    the root, make the sigma query (positive digits), walk upward;
    returns (signature digits, public ends). *)
Fixpoint r_chains (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← dN ;;
      s ← (if d is d'.+1 then opr tqo ((st, d'), u) (λ y, ret y) else ret u) ;;
      e ← r_walk st d (w.-1 - d) s ;;
      '(ss, es) ← r_chains st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance r_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMTCR TT CC) (r_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by fmap_solve.
    move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: r_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(** R's own locations (ids 230+ per the task). *)
Definition rt_pk_loc := mkloc 230 (None : option (Pk FS)).
Definition rt_log_loc := mkloc 231 ([::] : seq (Msg FS)).
Definition rt_sig_loc := mkloc 232 ([::] : seq N).

(** THE reduction: plays [I_KOTS FS] using the SM-TCR oracles. *)
Definition R_tcr : package (I_SMTCR TT CC) (I_KOTS FS) :=
  [package [fmap rt_pk_loc ; rt_log_loc ; rt_sig_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get rt_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      '(sgs, ends) ← r_chains 0 m ;;
      pp ← opr gpo Datatypes.tt (λ p, ret p) ;;
      #put rt_pk_loc := Some (pp, ends) ;;
      #put rt_log_loc := [:: m] ;;
      #put rt_sig_loc := sgs ;;
      ret ((pp, ends), Some sgs)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(mst, sgst) {
      pk ← getSome rt_pk_loc ;;
      log ← get rt_log_loc ;;
      sgs ← get rt_sig_loc ;;
      if verify_sig PP N F l w tsum pk.1 pk.2 mst sgst && (mst \notin log)
      then
        match tcr_decision pk.1 (head [::] log) mst sgs sgst with
        | Some ju => opr cko ju (λ ans, ret ans)
        | None => ret true
        end
      else ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies

    [resolve] of the real SM-TCR game at the three opsigs the
    reduction uses, computed once and for all (the [simplify_linking]
    rewrites [resolve_set]/[coerce_kleisliE] normalize the package
    lookup). *)

Local Notation SMB b := (SMTCR_game TT CC p_tcr b).
Local Notation SMR := (SMB true).

(* The TQUERY/GETPP bodies do not depend on the real/ideal flag, so
   the whole COMMIT machinery below is parametric in [b]. *)

Section CommitMachinery.

Context (b : bool).

Lemma resolve_tq (t : nat * nat) (x : N) :
  resolve (SMB b) tqo (t, x) =
  (revealed ← get rev_loc' ;;
   #assert ~~ revealed ;;
   tws ← get tws_loc' ;;
   #assert (size tws < p_tcr)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get tgts_loc' ;;
   #put tgts_loc' := setm tgts (size tws) (t, x) ;;
   #put tws_loc' := rcons tws t ;;
   ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   ret (F pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_gp (u : unit) :
  resolve (SMB b) gpo u =
  (ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   #put rev_loc' := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

End CommitMachinery.

Lemma resolve_ck (j : nat) (x : N) :
  resolve SMR cko (j, x) =
  (revealed ← get rev_loc' ;;
   #assert revealed ;;
   tgts ← get tgts_loc' ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get pp_loc' ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put pp_loc' := Some pp ;; ret pp
            end ;;
       ret ((x != m0) && (F pp t0 x == F pp t0 m0))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side CHECK answers false unconditionally. *)
Lemma resolve_ck_false (j : nat) (x : N) :
  resolve (SMB false) cko (j, x) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

Section CommitMachineryB.

Context (b : bool).

(* ------------------------------------------------------------------ *)
(** *** The block precondition family

    Used INSIDE COMMIT, where the eq_rel_perf_ind invariant is
    temporarily dropped: the heaps satisfy a frame [Φ] (instantiated
    with [heap_ignore] over all private locations), and SM-TCR's four
    locations hold exactly the state after committing the list [Q]
    (in order), with [po] the lazily sampled parameter. *)

Definition blk_pre (Φ : precond) (po : option PP) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ Φ (s0, s1),
      get_heap s1 pp_loc' = po,
      get_heap s1 rev_loc' = false,
      get_heap s1 tws_loc' = unzip1 Q &
      get_heap s1 tgts_loc' = qmap_from 0 Q].

Arguments blk_pre : simpl never.

(** Frames are insensitive to writes at SM-TCR's locations. *)
Definition phi_stable (Φ : precond) : Prop :=
  forall s0 s1 (ℓ : Location) (v : ℓ),
    ℓ.1 \in [:: 44; 45; 46; 47] -> Φ (s0, s1) -> Φ (s0, set_heap s1 ℓ v).

(** The TQUERY state update (put tgts; put tws). *)
Lemma blk_pre_qupd (Φ : precond) (po : option PP) Q (t : nat * nat) (x : N)
    s0 s1 :
  phi_stable Φ ->
  blk_pre Φ po Q (s0, s1) ->
  blk_pre Φ po (rcons Q (t, x))
    (s0, set_heap (set_heap s1 tgts_loc'
            (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, x)))
          tws_loc' (rcons (unzip1 Q) t)).
Proof.
move=> hΦ [h0 hpp hrev htws htgts]; split.
- by apply hΦ; [done | apply hΦ; [done | exact: h0]].
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq /unzip1 map_rcons.
- rewrite get_set_heap_neq // get_set_heap_eq.
  by rewrite qmap_from_rcons add0n size_map.
Qed.

(** The lazy parameter sampling (put pp). *)
Lemma blk_pre_set_pp (Φ : precond) (pp : PP) Q s0 s1 :
  phi_stable Φ ->
  blk_pre Φ None Q (s0, s1) ->
  blk_pre Φ (Some pp) Q (s0, set_heap s1 pp_loc' (Some pp)).
Proof.
move=> hΦ [h0 hpp hrev htws htgts]; split.
- by apply: hΦ.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked TQUERY *)

(** Parameter already sampled: the oracle call is rhs-only. *)
Lemma r_tquery_known {B : choiceType} (Φ : precond) (pp : PP)
    (t : nat * nat) (x : N) (Q : seq qentry)
    (c0 : raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  phi_stable Φ ->
  size Q < p_tcr ->
  t \notin unzip1 Q ->
  ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp) (rcons Q (t, x)) (s0, s1) ⦄
     c0 ≈ k1 (F pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp) Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) tqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> hΦ hbud hfresh h.
rewrite resolve_tq.
eapply (r_get_bind_rhs rev_loc' false).
  by move=> s0 s1 [_ _ hrev _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs tws_loc' (unzip1 Q)).
  by move=> s0 s1 [_ _ _ htws _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite hfresh.
move=> _.
eapply (r_get_bind_rhs tgts_loc' (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ htgts].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: blk_pre_qupd hΦ hpre.
eapply (r_get_bind_rhs pp_loc' (Some pp)).
  by move=> s0 s1 [_ hpp _ _ _].
exact: h.
Qed.

(** First query: SM-TCR's parameter is still unsampled; its lazy
    [dPP] is synchronized with the lhs's (eager) one. *)
Lemma r_tquery_first {B : choiceType} (Φ : precond)
    (t : nat * nat) (x : N) (Q : seq qentry)
    (k0 : PP -> raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  phi_stable Φ ->
  size Q < p_tcr ->
  t \notin unzip1 Q ->
  (forall pp,
     ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp) (rcons Q (t, x)) (s0, s1) ⦄
        k0 pp ≈ k1 (F pp t x) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), blk_pre Φ None Q (s0, s1) ⦄
     bind dPP k0 ≈ bind (resolve (SMB b) tqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> hΦ hbud hfresh h.
rewrite resolve_tq.
eapply (r_get_bind_rhs rev_loc' false).
  by move=> s0 s1 [_ _ hrev _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs tws_loc' (unzip1 Q)).
  by move=> s0 s1 [_ _ _ htws _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite hfresh.
move=> _.
eapply (r_get_bind_rhs tgts_loc' (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ htgts].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: blk_pre_qupd hΦ hpre.
eapply (r_get_bind_rhs pp_loc' None).
  by move=> s0 s1 [_ hpp _ _ _].
cbv beta iota.
rewrite !bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> pp.
cbv beta.
eapply r_put_bind_rhs.
  by move=> s0 s1 hpre; exact: blk_pre_set_pp hΦ hpre.
exact: (h pp).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The walk and per-chain inductions *)

(* Keep the package and the resolved oracle bodies folded under
   [simpl]: the spec lemmas below match them up to conversion. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.

(** Walking chain [i] from position [k] for [n] TQUERYs: rhs-only;
    extends the committed list by [walkq pp i k n x] and returns the
    chain value at [k + n]. *)
Lemma r_walk_spec {B : choiceType} (Φ : precond) (pp : PP)
    (post : postcond B B) :
  forall n i k (x : N) (Q : seq qentry) (c0 : raw_code B)
         (k1 : N -> raw_code B),
  phi_stable Φ ->
  (size Q + n <= p_tcr)%N ->
  all (tlt i k) (unzip1 Q) ->
  ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp) (Q ++ walkq pp i k n x) (s0, s1) ⦄
     c0 ≈ k1 (chain (cf pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp) Q (s0, s1) ⦄
     c0 ≈ bind (code_link (r_walk i k n x) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x Q c0 k1 hΦ hbud hfresh h.
- by move: h; rewrite cats0.
- rewrite /= bind_assoc.
  eapply r_tquery_known => //.
  + by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + exact: tlt_notin hfresh.
  + apply: IH => //.
    * by rewrite size_rcons addSnnS.
    * rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
      -- by rewrite /tlt /= ltnn eqxx ltnSn.
      -- exact: all_tlt_widen hfresh.
    * by move: h; rewrite walkq_cons cat_rcons.
Qed.

(** The per-chain induction: lhs [sample_sig_roots], rhs the linked
    [r_chains]; the committed list grows by [commit_queries] and the
    results are [sigs_of]/[ends_of] of the sampled roots. *)
Lemma r_chains_spec {B : choiceType} (Φ : precond) (pp : PP)
    (post : postcond B B) :
  forall ds st (Q : seq qentry) (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  phi_stable Φ ->
  (size Q + nqs ds <= p_tcr)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp)
            (Q ++ commit_queries pp st ds us) (s0, s1) ⦄
        K0 (sigs_of pp st ds us)
      ≈ K1 (sigs_of pp st ds us, ends_of pp st ds (sigs_of pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), blk_pre Φ (Some pp) Q (s0, s1) ⦄
     bind (sample_sig_roots PP N F dN pp st ds) K0
   ≈ bind (code_link (r_chains st ds) (SMB b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st Q K0 K1 hΦ hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- rewrite /= code_link_bind.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d hbud h => [|d'] hbud h.
  + (* d = 0 : no sigma query, walk from the root itself *)
    rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    eapply (r_walk_spec Φ pp post (w.-1 - 0) st 0 u Q) => //.
    * apply: leq_trans hbud.
      by rewrite leq_add2l /nqs /= /nq /= leq_addr.
    * exact: all_lt_tlt.
    * rewrite (code_link_bind (r_chains st.+1 ds)) bind_assoc.
      eapply IH => //.
      -- by rewrite size_cat size_walkq -addnA.
      -- rewrite unzip1_cat all_cat; apply/andP; split.
         ++ by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ apply: sub_all (walkq_tweak1 pp st 0 _ u) => t /= /eqP ->.
            exact: ltnSn.
      -- move=> us hus.
         move: (h (u :: us)); rewrite /= hus => /(_ erefl).
         by rewrite commit_queries_cons /chain_queries /= catA.
  + (* d = d'.+1 : sigma query first *)
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply r_tquery_known => //.
    * apply: leq_trans hbud.
      by rewrite addnS ltnS leq_addr.
    * exact: lt_notin.
    * rewrite /= (code_link_bind (r_walk st d'.+1 (w.-1 - d'.+1)
                    (F pp (st, d') u))) bind_assoc.
      eapply (r_walk_spec Φ pp post (w.-1 - d'.+1) st d'.+1
                (F pp (st, d') u) (rcons Q ((st, d'), u))) => //.
      -- rewrite size_rcons addSnnS; apply: leq_trans hbud.
         by rewrite leq_add2l /nqs /= /nq /= add1n addSn ltnS leq_addr.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /tlt /= ltnn eqxx ltnSn.
         ++ exact: all_lt_tlt.
      -- rewrite /= (code_link_bind (r_chains st.+1 ds)) bind_assoc.
         eapply IH => //.
         ++ rewrite size_cat size_rcons size_walkq.
            apply: leq_trans hbud.
            by rewrite addSnnS -addnA leq_add2l /nqs /= /nq /= add1n.
         ++ rewrite unzip1_cat all_cat /unzip1 map_rcons all_rcons.
            apply/andP; split; last first.
            ** apply: sub_all (walkq_tweak1 pp st d'.+1 _ _) => t /= /eqP ->.
               exact: ltnSn.
            ** apply/andP; split; first by rewrite /= ltnSn.
               by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ move=> us hus.
            move: (h (u :: us)); rewrite /= hus => /(_ erefl).
            by rewrite commit_queries_cons /chain_queries cat_rcons catA.
Qed.

End CommitMachineryB.

(* [Arguments] directives do not survive section closing. *)
Arguments blk_pre : simpl never.

(* ------------------------------------------------------------------ *)
(** *** The invariant of [R_tcr_real]

    [heap_ignore] over all nine private locations, joined with ONE
    [rel_app] relation [RT]: G1v's pk/log mirror R's pk/log, and R's
    pk determines the entire SM-TCR state.  Before a successful
    COMMIT everything is at its initial value; afterwards there are
    [m, us] explaining the log, the stored signature, the key and the
    committed targets. *)

Definition IGN : Locations :=
  [fmap g0v_pk' ; g0v_log' ; rt_pk_loc ; rt_log_loc ; rt_sig_loc ;
        pp_loc' ; tgts_loc' ; tws_loc' ; rev_loc' ].

Definition RT (pko : option (Pk FS)) (lg : seq (Msg FS))
    (pko' : option (Pk FS)) (lg' : seq (Msg FS)) (sgs : seq N)
    (po : option PP) (tg : {fmap nat -> (th_T TT × th_M TT)})
    (tw : seq (nat * nat)) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg &
      match pko with
      | None =>
          [/\ lg = [::], sgs = [::], po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists m us,
            [/\ lg = [:: m], valid_msg l w tsum m, size us = l,
                sgs = sigs_of pk.1 0 m us
              & [/\ pk.2 = ends_of pk.1 0 m (sigs_of pk.1 0 m us),
                    po = Some pk.1,
                    tg = qmap_from 0 (commit_queries pk.1 0 m us),
                    tw = unzip1 (commit_queries pk.1 0 m us)
                  & rv = true]]
      end].

Definition tcr_inv : precond :=
  heap_ignore IGN
  ⋊ rel_app [:: (lhs, g0v_pk') ; (lhs, g0v_log') ;
                (rhs, rt_pk_loc) ; (rhs, rt_log_loc) ; (rhs, rt_sig_loc) ;
                (rhs, pp_loc') ; (rhs, tgts_loc') ; (rhs, tws_loc') ;
                (rhs, rev_loc') ] RT.

Arguments tcr_inv : simpl never.

Lemma tcr_invE s0 s1 :
  tcr_inv (s0, s1) ->
  heap_ignore IGN (s0, s1) /\
  RT (get_heap s0 g0v_pk') (get_heap s0 g0v_log')
     (get_heap s1 rt_pk_loc) (get_heap s1 rt_log_loc)
     (get_heap s1 rt_sig_loc) (get_heap s1 pp_loc')
     (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma tcr_invI s0 s1 :
  heap_ignore IGN (s0, s1) ->
  RT (get_heap s0 g0v_pk') (get_heap s0 g0v_log')
     (get_heap s1 rt_pk_loc) (get_heap s1 rt_log_loc)
     (get_heap s1 rt_sig_loc) (get_heap s1 pp_loc')
     (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc') ->
  tcr_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** [heap_ignore IGN] is a frame for the block lemmas. *)
Lemma phi_stable_ign : phi_stable (heap_ignore IGN).
Proof.
move=> s0 s1 ℓ v hin h ℓ' hni.
rewrite get_set_heap_neq; first exact: h.
apply/eqP => e; move: hni; rewrite e.
by move: hin; rewrite !inE => /or4P[] /eqP ->; rewrite mem_domm.
Qed.

(** State family after GETPP flipped the phase (end of COMMIT),
    parameterized by the ignore-set of the ambient invariant. *)
Definition fin_pre (L : Locations) (pp : PP) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore L (s0, s1),
      get_heap s1 pp_loc' = Some pp,
      get_heap s1 rev_loc' = true,
      get_heap s1 tws_loc' = unzip1 Q &
      get_heap s1 tgts_loc' = qmap_from 0 Q].

Arguments fin_pre : simpl never.

Lemma heap_ignore_set_r (L : Locations) (ℓ : Location) (v : ℓ) s0 s1 :
  ℓ.1 \in domm L -> heap_ignore L (s0, s1) ->
  heap_ignore L (s0, set_heap s1 ℓ v).
Proof.
move=> hin h ℓ' hni; rewrite get_set_heap_neq; first exact: h.
by apply/eqP => e; move: hni; rewrite e hin.
Qed.

Lemma heap_ignore_set_l (L : Locations) (ℓ : Location) (v : ℓ) s0 s1 :
  ℓ.1 \in domm L -> heap_ignore L (s0, s1) ->
  heap_ignore L (set_heap s0 ℓ v, s1).
Proof.
move=> hin h ℓ' hni; rewrite get_set_heap_neq; first exact: h.
by apply/eqP => e; move: hni; rewrite e hin.
Qed.

Lemma blk_to_fin (L : Locations) pp Q s0 s1 :
  47 \in domm L ->
  blk_pre (heap_ignore L) (Some pp) Q (s0, s1) ->
  fin_pre L pp Q (s0, set_heap s1 rev_loc' true).
Proof.
move=> h47 [h0 hpp hrev htws htgts]; split.
- exact: heap_ignore_set_r h0.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The common ending of COMMIT: GETPP, the five puts, the returns,
    and the re-establishment of the invariant. *)
Lemma r_commit_final (pp : PP) (m : seq nat) (us : seq N) :
  valid_msg l w tsum m -> size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        blk_pre (heap_ignore IGN) (Some pp) (commit_queries pp 0 m us)
          (s0, s1) ⦄
     (#put g0v_pk' := Some (pp,
        ends_from_sig PP N F l w pp m (sigs_of pp 0 m us)) ;;
      #put g0v_log' := [:: m] ;;
      ret ((pp, ends_from_sig PP N F l w pp m (sigs_of pp 0 m us)),
           Some (sigs_of pp 0 m us)))
   ≈ bind (resolve SMR gpo Datatypes.tt)
       (λ p,
        #put rt_pk_loc := Some (p, ends_of pp 0 m (sigs_of pp 0 m us)) ;;
        #put rt_log_loc := [:: m] ;;
        #put rt_sig_loc := sigs_of pp 0 m us ;;
        ret ((p, ends_of pp 0 m (sigs_of pp 0 m us)),
             Some (sigs_of pp 0 m us)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ tcr_inv (s0, s1) ⦄.
Proof.
move=> hvm hus.
have hm : size m = l by case/and3P: hvm => /eqP.
rewrite resolve_gp.
eapply (r_get_bind_rhs pp_loc' (Some pp)).
  by move=> s0 s1 [_ hpp _ _ _].
cbv beta iota.
eapply (r_put_bind_rhs rev_loc' true _
          (fin_pre IGN pp (commit_queries pp 0 m us))).
  by move=> s0 s1; apply: blk_to_fin; rewrite mem_domm.
eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hfin ->].
case: hfin => hign hpp hrev htws htgts.
split; first by rewrite (ends_of_from_sig pp m _ hm).
apply: tcr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split; first by rewrite (ends_of_from_sig pp m _ hm).
  + by [].
  + exists m, us; split=> //.
    by split=> //=; rewrite (ends_of_from_sig pp m _ hm).
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_tcr_real (hl : 0 < l) (hw : 1 < w) :
  perfect (I_KOTS FS) (G1v PP N F dPP dN l w tsum true)
          (R_tcr ∘ SMTCR_game TT CC p_tcr true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ tcr_inv).
{ rewrite /tcr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/tcr_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hvm _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), blk_pre (heap_ignore IGN) None [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/tcr_invE: hinv => hign hRT.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRT => _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  have hm : size m = l by case/and3P: hvm => /eqP.
  rewrite (code_link_bind (r_chains 0 m)).
  case: m hvm hm => [|d0 m'] hvm hm.
    by move: hl; rewrite -hm ltnn.
  (* align G1v's eager pp with the first TQUERY's lazy sampling *)
  simpl.
  eapply (r_swap_eager_lazy (dPP : raw_code PP) (dN : raw_code N)).
  { eapply valid_scheme, prog_valid. }
  { eapply valid_scheme, prog_valid. }
  (* expose the rhs root sampling and sync it *)
  rewrite (code_link_bind (dN : raw_code N)).
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta.
  case: d0 hvm hm => [|d''] hvm hm.
  + (* d_0 = 0 : the first TQUERY is the first walk step (1 < w) *)
    have hw1 : (w.-1 - 0)%N = (w.-2).+1.
      by rewrite subn0 prednK // -subn1 subn_gt0.
    rewrite code_link_bind bind_assoc /=.
    rewrite hw1 /=.
    rewrite bind_assoc.
    eapply (r_tquery_first true) => //.
    { exact: phi_stable_ign. }
    { by rewrite /p_tcr addn_gt0 hl. }
    move=> pp.
    rewrite bind_assoc.
    rewrite (code_link_bind (r_walk 0 1 w.-2 (F pp (0, 0) u))) bind_assoc.
    eapply (r_walk_spec true (heap_ignore IGN) pp _ w.-2 0 1
              (F pp (0, 0) u) (rcons [::] ((0, 0), u))) => //.
    { exact: phi_stable_ign. }
    { apply: leq_trans (nqs_le _ hm).
      by rewrite size_rcons add1n -hw1 /nqs /= /nq /= add0n leq_addr. }
    rewrite /= (code_link_bind (r_chains 1 m')) bind_assoc.
    eapply (r_chains_spec true (heap_ignore IGN) pp _ m' 1) => //.
    { exact: phi_stable_ign. }
    { apply: leq_trans (nqs_le _ hm).
      rewrite /= size_walkq /nqs /= /nq /= hw1.
      exact: leqnn. }
    { rewrite /=.
      by apply: sub_all (walkq_tweak1 pp 0 1 _ _) => t /= /eqP ->. }
    move=> us' hus'.
    have eQ : (((0, 0), u) :: walkq pp 0 1 w.-2 (F pp (0, 0) u))
                ++ commit_queries pp 1 m' us'
              = commit_queries pp 0 (0 :: m') (u :: us').
      by rewrite commit_queries_cons /chain_queries /= hw1 walkq_cons.
    rewrite eQ.
    have e0eq : chain (cf pp 0) (F pp (0, 0) u) 1 w.-2
                = chain (cf pp 0) u 0 (w.-1 - 0)%N.
      by rewrite hw1.
    rewrite e0eq.
    eapply (r_commit_final pp (0 :: m') (u :: us')) => //.
    by rewrite /= hus'; move: hm => /= ->.
  + (* d_0 = d''.+1 : the first TQUERY is the sigma query *)
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_tquery_first true) => //.
    { exact: phi_stable_ign. }
    { by rewrite /p_tcr addn_gt0 hl. }
    move=> pp.
    rewrite /= bind_assoc.
    rewrite (code_link_bind (r_walk 0 d''.+1 (w.-1 - d''.+1)
               (F pp (0, d'') u))) bind_assoc.
    eapply (r_walk_spec true (heap_ignore IGN) pp _ (w.-1 - d''.+1) 0 d''.+1
              (F pp (0, d'') u) (rcons [::] ((0, d''), u))) => //.
    { exact: phi_stable_ign. }
    { apply: leq_trans (nqs_le _ hm).
      by rewrite size_rcons add1n /nqs /= /nq /= add1n leq_addr. }
    { by rewrite /tlt /= ltnSn. }
    rewrite /= (code_link_bind (r_chains 1 m')) bind_assoc.
    eapply (r_chains_spec true (heap_ignore IGN) pp _ m' 1) => //.
    { exact: phi_stable_ign. }
    { apply: leq_trans (nqs_le _ hm).
      rewrite /= size_walkq /nqs /= /nq /=.
      exact: leqnn. }
    { rewrite /=.
      by apply: sub_all (walkq_tweak1 pp 0 d''.+1 _ _) => t /= /eqP ->. }
    move=> us' hus'.
    eapply (r_commit_final pp (d''.+1 :: m') (u :: us')) => //.
    by rewrite /= hus'; move: hm => /= ->.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/tcr_invE: hinv => _ [e1 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/tcr_invE: hinv => _ [_ e2 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_rhs => sgs.
  eapply (r_fact (exists m, [/\ lg = [:: m], valid_msg l w tsum m
                              & pk.2 = ends_of pk.1 0 m sgs])).
    { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
      case/tcr_invE: hinv => _ [_ _ hmatch].
      rewrite /rem_inv /= in h1 h2 h3 h4 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [uss [hA hB hC hD [hE _ _ _ _]]].
      exists mm; split=> //.
      - by rewrite -h3.
      - by rewrite h5 in hD; rewrite hE hD. }
  move=> [m [hlg hvm hpk2]].
  rewrite hlg.
  case E0: (verify_sig PP N F l w tsum pk.1 pk.2 mst sgst
              && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[hinv _] _] _] _] _].
  + (* valid fresh forgery *)
    case/andP: E0 => hver hfresh.
    case E1: (tcr_decision pk.1 m mst sgs sgst) => [[j uu]|]; last first.
    * (* PRE case (or impossible branches): answer true on both sides *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[hinv _] _] _] _] _].
    * (* TCR case: CHECK answers true *)
      simpl.
      rewrite resolve_ck.
      eapply (r_get_bind_rhs rev_loc' true).
        { move=> s0 s1 [[[[[hinv h1] _] _] _] _].
          case/tcr_invE: hinv => _ [_ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => mm [uss [_ _ _ _ [_ _ _ _ hrv]]]. }
      cbv beta.
      eapply r_get_remember_rhs => tg.
      eapply (r_fact (exists us,
                [/\ size us = l, sgs = sigs_of pk.1 0 m us
                  & tg = qmap_from 0 (commit_queries pk.1 0 m us)])).
        { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
          case/tcr_invE: hinv => _ [_ _ hmatch].
          rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6.
          rewrite h1 in hmatch.
          case: hmatch => mm [uss [hA hB hC hD [_ _ hG _ _]]].
          have emm : mm = m.
            have : [:: mm] = lg by rewrite -hA h3.
            by rewrite hlg => -[].
          exists uss; rewrite -emm; split=> //.
          - by rewrite -h5.
          - by rewrite -h6. }
      move=> [us [husz hsgs htg]].
      have hwin := tcr_decisionP pk.1 m mst us sgst hvm husz.
      rewrite -hsgs in hwin.
      move: hwin; rewrite -hpk2 => /(_ hver hfresh).
      rewrite E1 => -[t0 [v0 [hget hne hcol]]].
      have hgetm : getm tg j = Some (t0, v0).
        rewrite htg.
        by have := qmap_from_get 0 (commit_queries pk.1 0 m us) j;
           rewrite add0n => ->.
      rewrite hgetm.
      eapply (r_get_rhs_known pp_loc' (Some pk.1)).
        { move=> s0 s1 [[[[[[hinv h1] _] _] _] _] _].
          case/tcr_invE: hinv => _ [_ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => mm [uss [_ _ _ _ [_ hpo _ _ _]]]. }
      simpl.
      rewrite hne hcol eqxx.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** *** The ideal side: Gmid and [R_tcr_ideal]

    [Gmid] is G1v-real with KFORGE answering [false] exactly on the
    classifier's TCR case ([tcr_decision = Some _]); to run the
    classifier it additionally stores the issued signature
    ([gm_sig_loc]).  It is perfectly equivalent to the reduction
    linked against the IDEAL SM-TCR game (CHECK answers false), which
    is the intermediate game of the forgery-split triangle in
    PROOF_PLAN.md. *)

Definition gm_sig_loc := mkloc 233 ([::] : seq N).

Definition Gmid : game (I_KOTS FS) :=
  [package [fmap g0v_pk' ; g0v_log' ; gm_sig_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0v_pk' ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      pp ← dPP ;;
      sg ← sample_sig_roots PP N F dN pp 0 m ;;
      #put g0v_pk' := Some (pp, ends_from_sig PP N F l w pp m sg) ;;
      #put g0v_log' := [:: m] ;;
      #put gm_sig_loc := sg ;;
      ret ((pp, ends_from_sig PP N F l w pp m sg), Some sg)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(mst, sgst) {
      pk ← getSome g0v_pk' ;;
      log ← get g0v_log' ;;
      sgs ← get gm_sig_loc ;;
      if verify_sig PP N F l w tsum pk.1 pk.2 mst sgst && (mst \notin log)
      then
        match tcr_decision pk.1 (head [::] log) mst sgs sgst with
        | Some _ => ret false
        | None => ret true
        end
      else ret false
    }
  ].

Definition IGN2 : Locations :=
  [fmap g0v_pk' ; g0v_log' ; gm_sig_loc ; rt_pk_loc ; rt_log_loc ;
        rt_sig_loc ; pp_loc' ; tgts_loc' ; tws_loc' ; rev_loc' ].

(** Invariant relation: as [RT], plus Gmid's stored signature mirrors
    R's. *)
Definition RT2 (pko : option (Pk FS)) (lg : seq (Msg FS)) (sgl : seq N)
    (pko' : option (Pk FS)) (lg' : seq (Msg FS)) (sgs : seq N)
    (po : option PP) (tg : {fmap nat -> (th_T TT × th_M TT)})
    (tw : seq (nat * nat)) (rv : bool) : Prop :=
  RT pko lg pko' lg' sgs po tg tw rv /\ sgl = sgs.

Definition tcr_inv2 : precond :=
  heap_ignore IGN2
  ⋊ rel_app [:: (lhs, g0v_pk') ; (lhs, g0v_log') ; (lhs, gm_sig_loc) ;
                (rhs, rt_pk_loc) ; (rhs, rt_log_loc) ; (rhs, rt_sig_loc) ;
                (rhs, pp_loc') ; (rhs, tgts_loc') ; (rhs, tws_loc') ;
                (rhs, rev_loc') ] RT2.

Arguments tcr_inv2 : simpl never.

Lemma tcr_inv2E s0 s1 :
  tcr_inv2 (s0, s1) ->
  heap_ignore IGN2 (s0, s1) /\
  RT2 (get_heap s0 g0v_pk') (get_heap s0 g0v_log') (get_heap s0 gm_sig_loc)
     (get_heap s1 rt_pk_loc) (get_heap s1 rt_log_loc)
     (get_heap s1 rt_sig_loc) (get_heap s1 pp_loc')
     (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma tcr_inv2I s0 s1 :
  heap_ignore IGN2 (s0, s1) ->
  RT2 (get_heap s0 g0v_pk') (get_heap s0 g0v_log') (get_heap s0 gm_sig_loc)
     (get_heap s1 rt_pk_loc) (get_heap s1 rt_log_loc)
     (get_heap s1 rt_sig_loc) (get_heap s1 pp_loc')
     (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc') ->
  tcr_inv2 (s0, s1).
Proof. by move=> h1 h2; split. Qed.

Lemma phi_stable_ign2 : phi_stable (heap_ignore IGN2).
Proof.
move=> s0 s1 ℓ v hin h ℓ' hni.
rewrite get_set_heap_neq; first exact: h.
apply/eqP => e; move: hni; rewrite e.
by move: hin; rewrite !inE => /or4P[] /eqP ->; rewrite mem_domm.
Qed.

(** Ending of Gmid's COMMIT against the ideal game. *)
Lemma r_commit_final2 (pp : PP) (m : seq nat) (us : seq N) :
  valid_msg l w tsum m -> size us = l ->
  ⊢ ⦃ λ '(s0, s1),
        blk_pre (heap_ignore IGN2) (Some pp) (commit_queries pp 0 m us)
          (s0, s1) ⦄
     (#put g0v_pk' := Some (pp,
        ends_from_sig PP N F l w pp m (sigs_of pp 0 m us)) ;;
      #put g0v_log' := [:: m] ;;
      #put gm_sig_loc := sigs_of pp 0 m us ;;
      ret ((pp, ends_from_sig PP N F l w pp m (sigs_of pp 0 m us)),
           Some (sigs_of pp 0 m us)))
   ≈ bind (resolve (SMB false) gpo Datatypes.tt)
       (λ p,
        #put rt_pk_loc := Some (p, ends_of pp 0 m (sigs_of pp 0 m us)) ;;
        #put rt_log_loc := [:: m] ;;
        #put rt_sig_loc := sigs_of pp 0 m us ;;
        ret ((p, ends_of pp 0 m (sigs_of pp 0 m us)),
             Some (sigs_of pp 0 m us)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ tcr_inv2 (s0, s1) ⦄.
Proof.
move=> hvm hus.
have hm : size m = l by case/and3P: hvm => /eqP.
rewrite resolve_gp.
eapply (r_get_bind_rhs pp_loc' (Some pp)).
  by move=> s0 s1 [_ hpp _ _ _].
cbv beta iota.
eapply (r_put_bind_rhs rev_loc' true _
          (fin_pre IGN2 pp (commit_queries pp 0 m us))).
  by move=> s0 s1; apply: blk_to_fin; rewrite mem_domm.
eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hfin ->].
case: hfin => hign hpp hrev htws htgts.
split; first by rewrite (ends_of_from_sig pp m _ hm).
apply: tcr_inv2I.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split; last by [].
  split; first by rewrite (ends_of_from_sig pp m _ hm).
  + by [].
  + exists m, us; split=> //.
    by split=> //=; rewrite (ends_of_from_sig pp m _ hm).
Qed.

(** THE ideal-side equivalence: Gmid against the reduction linked
    with the ideal SM-TCR game. *)
Lemma R_tcr_ideal (hl : 0 < l) (hw : 1 < w) :
  perfect (I_KOTS FS) Gmid (R_tcr ∘ SMTCR_game TT CC p_tcr false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ tcr_inv2).
{ rewrite /tcr_inv2; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/tcr_inv2E: hinv => _ [[e1 _ _] _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hvm _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), blk_pre (heap_ignore IGN2) None [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/tcr_inv2E: hinv => hign hRT.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRT => [[_ _ hmatch] _]; move: hmatch; rewrite hrem0.
    move=> [_ _ hpo htg [htw hrv]].
    by split. }
  have hm : size m = l by case/and3P: hvm => /eqP.
  rewrite (code_link_bind (r_chains 0 m)).
  case: m hvm hm => [|d0 m'] hvm hm.
    by move: hl; rewrite -hm ltnn.
  simpl.
  eapply (r_swap_eager_lazy (dPP : raw_code PP) (dN : raw_code N)).
  { eapply valid_scheme, prog_valid. }
  { eapply valid_scheme, prog_valid. }
  rewrite (code_link_bind (dN : raw_code N)).
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta.
  case: d0 hvm hm => [|d''] hvm hm.
  + (* d_0 = 0 *)
    have hw1 : (w.-1 - 0)%N = (w.-2).+1.
      by rewrite subn0 prednK // -subn1 subn_gt0.
    rewrite code_link_bind bind_assoc /=.
    rewrite hw1 /=.
    rewrite bind_assoc.
    eapply (r_tquery_first false) => //.
    { exact: phi_stable_ign2. }
    { by rewrite /p_tcr addn_gt0 hl. }
    move=> pp.
    rewrite bind_assoc.
    rewrite (code_link_bind (r_walk 0 1 w.-2 (F pp (0, 0) u))) bind_assoc.
    eapply (r_walk_spec false (heap_ignore IGN2) pp _ w.-2 0 1
              (F pp (0, 0) u) (rcons [::] ((0, 0), u))) => //.
    { exact: phi_stable_ign2. }
    { apply: leq_trans (nqs_le _ hm).
      by rewrite size_rcons add1n -hw1 /nqs /= /nq /= add0n leq_addr. }
    rewrite /= (code_link_bind (r_chains 1 m')) bind_assoc.
    eapply (r_chains_spec false (heap_ignore IGN2) pp _ m' 1) => //.
    { exact: phi_stable_ign2. }
    { apply: leq_trans (nqs_le _ hm).
      rewrite /= size_walkq /nqs /= /nq /= hw1.
      exact: leqnn. }
    { rewrite /=.
      by apply: sub_all (walkq_tweak1 pp 0 1 _ _) => t /= /eqP ->. }
    move=> us' hus'.
    have eQ : (((0, 0), u) :: walkq pp 0 1 w.-2 (F pp (0, 0) u))
                ++ commit_queries pp 1 m' us'
              = commit_queries pp 0 (0 :: m') (u :: us').
      by rewrite commit_queries_cons /chain_queries /= hw1 walkq_cons.
    rewrite eQ.
    have e0eq : chain (cf pp 0) (F pp (0, 0) u) 1 w.-2
                = chain (cf pp 0) u 0 (w.-1 - 0)%N.
      by rewrite hw1.
    rewrite e0eq.
    eapply (r_commit_final2 pp (0 :: m') (u :: us')) => //.
    by rewrite /= hus'; move: hm => /= ->.
  + (* d_0 = d''.+1 *)
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_tquery_first false) => //.
    { exact: phi_stable_ign2. }
    { by rewrite /p_tcr addn_gt0 hl. }
    move=> pp.
    rewrite /= bind_assoc.
    rewrite (code_link_bind (r_walk 0 d''.+1 (w.-1 - d''.+1)
               (F pp (0, d'') u))) bind_assoc.
    eapply (r_walk_spec false (heap_ignore IGN2) pp _ (w.-1 - d''.+1) 0
              d''.+1 (F pp (0, d'') u) (rcons [::] ((0, d''), u))) => //.
    { exact: phi_stable_ign2. }
    { apply: leq_trans (nqs_le _ hm).
      by rewrite size_rcons add1n /nqs /= /nq /= add1n leq_addr. }
    { by rewrite /tlt /= ltnSn. }
    rewrite /= (code_link_bind (r_chains 1 m')) bind_assoc.
    eapply (r_chains_spec false (heap_ignore IGN2) pp _ m' 1) => //.
    { exact: phi_stable_ign2. }
    { apply: leq_trans (nqs_le _ hm).
      rewrite /= size_walkq /nqs /= /nq /=.
      exact: leqnn. }
    { rewrite /=.
      by apply: sub_all (walkq_tweak1 pp 0 d''.+1 _ _) => t /= /eqP ->. }
    move=> us' hus'.
    eapply (r_commit_final2 pp (d''.+1 :: m') (u :: us')) => //.
    by rewrite /= hus'; move: hm => /= ->.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  eapply (r_fact (pko' = pko)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/tcr_inv2E: hinv => _ [[e1 _ _] _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/tcr_inv2E: hinv => _ [[_ e2 _] _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => sgl.
  eapply r_get_remember_rhs => sgs.
  eapply (r_fact (sgs = sgl)).
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/tcr_inv2E: hinv => _ [_ e2].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgs.
  eapply (r_fact (exists m, [/\ lg = [:: m], valid_msg l w tsum m
                              & pk.2 = ends_of pk.1 0 m sgl])).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/tcr_inv2E: hinv => _ [[_ _ hmatch] hsg].
      rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6.
      rewrite h1 in hmatch.
      case: hmatch => mm [uss [hA hB hC hD [hE _ _ _ _]]].
      exists mm; split=> //.
      - by rewrite -h3.
      - by rewrite -hsg h5 in hD; rewrite hE hD. }
  move=> [m [hlg hvm hpk2]].
  rewrite hlg.
  case E0: (verify_sig PP N F l w tsum pk.1 pk.2 mst sgst
              && (mst \notin [:: m])); last first.
  + apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[[hinv _] _] _] _] _] _].
  + case E1: (tcr_decision pk.1 m mst sgl sgst) => [[j uu]|]; last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * simpl.
      rewrite resolve_ck_false.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

End TCRHop.
