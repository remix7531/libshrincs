(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * HBS.wots.ud_hop

    The SM-UD hybrid telescope of the fixed-sum WOTS security proof,
    relating [G0v]
    (chains rooted at position 0) to [G1v] (chains re-rooted at the
    signing positions) through the hybrid games [Hud s].

    ** The hybrid

    Per chain [i] with digit [d := nth 0 m i], hybrid [Hud s] samples
    ONE hidden uniform root [x_i] and reveals the signature digit
      [σ_i := chain x_i p (d - p)]   with [p := minn s d.-1];
    the public end is chained onward from [σ_i] ([ends_from_sig]).
    - [Hud 0]: [p = 0], [σ_i = chain x_i 0 d] — exactly G0v's
      distribution ([G0v_Hud0]; the unrevealed positions above [d]
      coincide by [chain_split], positions below 0 don't exist).
    - [Hud w.-2]: [p = d.-1] for every valid digit ([d < w]), i.e.
      [σ_i = x_i] for [d = 0] and [σ_i = F pp (i, d-1) x_i] otherwise
      — exactly G1v's [sample_sig_roots] distribution ([G1v_Hudw]).
    Both endpoint identifications hold for EVERY [w] (no [1 < w] side
    condition): for [w < 2] all valid digits are 0 and all hybrids
    collapse to "σ_i = x_i".

    ** The reduction

    [R_ud b s : package (I_SMUD T C l) (I_KOTS FS)] implements COMMIT
    by querying, for every chain with [d >= s + 2], the SM-UD oracle
    at tweak [(i, s)] — real answer [F pp (i,s) (hidden x)] = the
    chain value at position [s+1] of a hidden root at [s] (= [Hud s]);
    ideal answer = a hidden fresh value at position [s+1] (= [Hud
    s.+1]).  Chains with [d <= s + 1] sample their root directly (the
    two neighbouring hybrids agree on them: [minn s d.-1 = d.-1 =
    minn s.+1 d.-1]).  Since UQUERY hides [pp] and is disabled after
    UGETPP, the reduction first forces [pp]'s lazy initialisation
    with one UCOLLQ call (the trivial collection), then queries all
    chains, then reveals [pp] via UGETPP and finishes purely.  This
    UCOLLQ trick pins the sampling of [pp] to the SAME program point
    (before all per-chain samplings) in BOTH the real and the ideal
    composition, so no sampler-commutation rules are ever needed.

    ** Telescope

    [UD_telescope]: for every KFORGE-bit [b],
      [Adv (G0v b) (G1v b) A
         <= \sum_(0 <= s < w.-2) AdvOf (SMUD_game T C l) (A ∘ R_ud b s)]
    via [Adv_hybrid_dep] (SSProve's nominal hybrid argument) over
      [Game s b' := R_ud b s ∘ SMUD_game T C l b'].
    Note the cap [p := l]: COMMIT makes at most one UQUERY per chain.

    Locations: 250/251 for [Hud], 252/253 for [R_ud] (the proof architecture:
    ids 250+; all relational proofs here cross distinct ids). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import reals.
From HBS Require Import prelude math.chain math.encoding sig.scheme sig.kots
  games.thf games.smud toolkit.sample_seq.
From HBS Require Import wots.scheme wots.games
  wots.analysis.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic relational mini-rules

    The SM-UD reduction's query loop reads and writes ONLY rhs-side
    oracle state, whose values are pinned by a Prop-style
    precondition carried through the loop induction (the
    [set_rhs]/[rem_rhs] combinator preconditions of the ssprove
    tactic layer do not recurse).  Building blocks: a rhs-only get
    with pinned value, a rhs-only put with explicit precondition
    transformation, and preservation of [heap_ignore] under
    one-sided writes to ignored locations. *)

Lemma r_get_rhs_pin {A B : choiceType} (ℓ : Location) (v : ℓ)
    (pre : precond) (c₀ : raw_code A) (k : ℓ -> raw_code B)
    (post : postcond A B) :
  (forall s₀ s₁, pre (s₀, s₁) -> get_heap s₁ ℓ = v) ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ k v ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ x ← get ℓ ;; k x ⦃ post ⦄.
Proof.
move=> hv h.
eapply r_get_remember_rhs => x.
eapply rpre_hypothesis_rule => s₀ s₁ [hpre hrem].
move: hrem; rewrite /rem_inv /= => hx.
subst x; rewrite (hv _ _ hpre).
eapply rpre_weaken_rule; [exact: h|] => ? ? /= [-> ->] //.
Qed.

Lemma r_put_rhs_pre {A B : choiceType} (ℓ : Location) (v : ℓ)
    (pre pre' : precond) (c₀ : raw_code A) (c₁ : raw_code B)
    (post : postcond A B) :
  (forall s₀ s₁, pre (s₀, s₁) -> pre' (s₀, set_heap s₁ ℓ v)) ->
  ⊢ ⦃ λ '(s₀, s₁), pre' (s₀, s₁) ⦄ c₀ ≈ c₁ ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄ c₀ ≈ #put ℓ := v ;; c₁ ⦃ post ⦄.
Proof.
move=> hset h.
apply r_put_rhs.
eapply rpre_weaken_rule; [exact: h|] => s₀ s₁ [s₁' [hpre ->]].
exact: hset.
Qed.

Lemma heap_ignore_set_rhs (L : Locations) (ℓ : Location) (v : ℓ)
    (s₀ s₁ : heap) :
  ℓ.1 \in domm L ->
  heap_ignore L (s₀, s₁) -> heap_ignore L (s₀, set_heap s₁ ℓ v).
Proof.
move=> hin h; rewrite /heap_ignore => ℓ' hl'.
rewrite get_set_heap_neq; first exact: h.
by apply/eqP => e; rewrite e hin in hl'.
Qed.

Lemma heap_ignore_set_lhs (L : Locations) (ℓ : Location) (v : ℓ)
    (s₀ s₁ : heap) :
  ℓ.1 \in domm L ->
  heap_ignore L (s₀, s₁) -> heap_ignore L (set_heap s₀ ℓ v, s₁).
Proof.
move=> hin h; rewrite /heap_ignore => ℓ' hl'.
rewrite get_set_heap_neq; first exact: h.
by apply/eqP => e; rewrite e hin in hl'.
Qed.

Section wots_ud_hop.

(** Same section context as wots.games / Analysis Part 2. *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (l w tsum : nat).

Local Notation FS := (fixed_sum_scheme PP N F dPP dN l w tsum).
Local Notation cf := (chainf PP N F).
Local Notation T := (Tots PP N F dPP dN).
Local Notation C := (Cots PP N F dPP dN).

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the per-chain sampling maps

    All hybrid/reduction games sample ONE uniform value per chain and
    post-process it purely.  The post-processings, as maps over
    (digit list, sampled list) — recursion on the digit list with the
    chain index [i] threaded through, truncating like [zip]:

    - [roots_map s]: the hybrid [Hud s]'s signature digits: root at
      position [minn s d.-1], chained up to the digit.
    - [uq_real_map s]: what the real SM-UD oracle hands the reduction
      for the queried chains ([F pp (i,s) x]), the raw root for the
      others.
    - [rud_sig s]: how the reduction turns the oracle answers into
      signature digits (queried chains: continue from position
      [s + 1]; others: from the root position [minn s d.-1]).
    - [sig_map]: Games.v's [sample_sig_roots] post-processing (G1v's
      shape: one [F]-step below the digit). *)

Fixpoint roots_map (pp : PP) (s i : nat) (m : seq nat) (xs : seq N)
    {struct m} : seq N :=
  match m, xs with
  | d :: m', x :: xs' =>
      chain (cf pp i) x (minn s d.-1) (d - minn s d.-1)
        :: roots_map pp s i.+1 m' xs'
  | _, _ => [::]
  end.

Fixpoint uq_real_map (pp : PP) (s i : nat) (m : seq nat) (xs : seq N)
    {struct m} : seq N :=
  match m, xs with
  | d :: m', x :: xs' =>
      (if s.+2 <= d then F pp (i, s) x else x)
        :: uq_real_map pp s i.+1 m' xs'
  | _, _ => [::]
  end.

Fixpoint rud_sig (pp : PP) (s i : nat) (m : seq nat) (ys : seq N)
    {struct m} : seq N :=
  match m, ys with
  | d :: m', y :: ys' =>
      (if s.+2 <= d
       then chain (cf pp i) y s.+1 (d - s.+1)
       else chain (cf pp i) y (minn s d.-1) (d - minn s d.-1))
        :: rud_sig pp s i.+1 m' ys'
  | _, _ => [::]
  end.

Fixpoint sig_map (pp : PP) (i : nat) (m : seq nat) (xs : seq N)
    {struct m} : seq N :=
  match m, xs with
  | d :: m', x :: xs' =>
      (if d is d'.+1 then F pp (i, d') x else x)
        :: sig_map pp i.+1 m' xs'
  | _, _ => [::]
  end.

(* ------------------------------------------------------------------ *)
(** *** Pure identities between the maps *)

(** Digit arithmetic for the queried chains ([d >= s + 2]). *)
Let big_digit_pred s d : s.+2 <= d -> s.+1 <= d.-1.
Proof.
move=> hd.
have h0d : 0 < d := leq_trans (ltn0Sn s.+1) hd.
by rewrite -ltnS (ltn_predK h0d).
Qed.

(** The reduction's post-processing of the REAL oracle answers is the
    [Hud s] sampling map: queried chains walk [F pp (i,s) x] from
    [s+1], which is the root [x] at [s] walked one step further. *)
Lemma rud_sig_real (pp : PP) (s i : nat) (m : seq nat) (xs : seq N) :
  rud_sig pp s i m (uq_real_map pp s i m xs) = roots_map pp s i m xs.
Proof.
elim: m i xs => [|d m IH] i [|x xs] //=.
case: (boolP (s.+2 <= d)) => hd; rewrite IH //.
congr cons.
have hs1 : s.+1 <= d.-1 := big_digit_pred _ _ hd.
have hsd : s < d := ltnW hd.
have -> : minn s d.-1 = s by apply/minn_idPl; exact: ltnW hs1.
have -> : d - s = (d - s.+1).+1 by rewrite subnS prednK // subn_gt0.
by rewrite chainS.
Qed.

(** The reduction's post-processing of the IDEAL oracle answers (the
    raw fresh values) is the [Hud s.+1] sampling map. *)
Lemma rud_sig_ideal (pp : PP) (s i : nat) (m : seq nat) (ys : seq N) :
  rud_sig pp s i m ys = roots_map pp s.+1 i m ys.
Proof.
elim: m i ys => [|d m IH] i [|y ys] //=.
rewrite IH; congr cons.
case: (boolP (s.+2 <= d)) => hd.
- have hs1 : s.+1 <= d.-1 := big_digit_pred _ _ hd.
  by rewrite (minn_idPl hs1).
- rewrite -ltnNge ltnS in hd.
  have hds : d.-1 <= s by rewrite -subn1 leq_subLR add1n.
  by rewrite (minn_idPr hds) (minn_idPr (leq_trans hds (leqnSn s))).
Qed.

(** Endpoint [s = 0]: roots at position 0, signature digit = the
    G0v honest chain walk. *)
Lemma roots_map0E (pp : PP) (i : nat) (ds : seq nat) (xs : seq N) :
  roots_map pp 0 i ds xs
  = [seq chain (cf pp q.1.1) q.1.2 0 q.2
    | q <- zip (zip (iota i (size ds)) xs) ds].
Proof.
by elim: ds i xs => [|d ds IH] i [|x xs] //=; rewrite min0n subn0 IH.
Qed.

Lemma roots_map_sign (pp : PP) (m : seq nat) (xs : seq N) :
  size m = l ->
  roots_map pp 0 0 m xs = sign_digits PP N F l pp xs m.
Proof. by move=> hm; rewrite roots_map0E /sign_digits hm. Qed.

(** Endpoint [s = 0], public ends: completing the [Hud 0] digit
    [chain x 0 d] with [w.-1 - d] more steps is the G0v chain end
    [chain x 0 w.-1] ([chain_split]). *)
Lemma ends_roots_map0 (pp : PP) (i : nat) (ds : seq nat) (xs : seq N) :
  wf_digits w ds ->
  [seq chain (cf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota i (size ds)) (zip ds (roots_map pp 0 i ds xs))]
  = [seq chain (cf pp ix.1) ix.2 0 w.-1 | ix <- zip (iota i (size ds)) xs].
Proof.
elim: ds i xs => [|d ds IH] i [|x xs] //= /andP[hd hds].
rewrite min0n subn0 IH //; congr cons.
have hdw : d <= w.-1 by rewrite -ltnS (ltn_predK hd).
have h := chain_split (cf pp i) x (leq0n d) hdw.
by rewrite !subn0 in h; rewrite -h.
Qed.

Lemma ends_from_roots_map0 (pp : PP) (m : seq nat) (xs : seq N) :
  size m = l -> wf_digits w m ->
  ends_from_sig PP N F l w pp m (roots_map pp 0 0 m xs)
  = chain_ends PP N F l w pp xs.
Proof.
move=> hm hwd.
by rewrite /ends_from_sig /chain_ends -hm ends_roots_map0.
Qed.

(** Endpoint [s = w.-2]: for valid digits ([d < w]) the root position
    [minn w.-2 d.-1] is [d.-1], so the [Hud w.-2] digit is G1v's
    [sample_sig_roots] shape ([x] itself for [d = 0], one [F]-step
    for [d > 0]). *)
Lemma sig_map_roots (pp : PP) (i : nat) (ds : seq nat) (xs : seq N) :
  wf_digits w ds ->
  sig_map pp i ds xs = roots_map pp w.-2 i ds xs.
Proof.
elim: ds i xs => [|d ds IH] i [|x xs] //= /andP[hd hds].
rewrite IH //; congr cons.
case: d hd => [|d'] hd.
- by rewrite minn0 subn0.
- have hle1 : d' < w.-1 by rewrite -ltnS (ltn_predK hd).
  have hle2 : d' <= w.-2 by rewrite -ltnS (ltn_predK hle1).
  by rewrite (minn_idPr hle2) subSnn chain1.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Relational sampler couplings

    [sample_seq dN n] is the reference sampler of all games here; the
    two lemmas below couple it (identically) with itself resp. with
    G1v's [sample_sig_roots], handing the continuation the size of
    the sampled list resp. the pure post-processing.  Both are stated
    in continuation-passing form under an ARBITRARY precondition, as
    [r_scheme_bind] (Games.v). *)

Lemma r_sample_seq_size {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k₀ k₁ : chList N -> raw_code B) :
  (forall xs : seq N, size xs = n -> ⊢ ⦃ pre ⦄ k₀ xs ≈ k₁ xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xs ← sample_seq dN n ;; k₀ xs ≈ xs ← sample_seq dN n ;; k₁ xs
  ⦃ post ⦄.
Proof.
elim: n k₀ k₁ => [|n IH] k₀ k₁ hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact _|] => x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

Lemma r_sample_sig_roots {B : choiceType} (pp : PP) (i : nat)
    (m : seq nat) (pre : precond) (post : postcond B B)
    (k₀ k₁ : chList N -> raw_code B) :
  (forall xs : seq N, size xs = size m ->
    ⊢ ⦃ pre ⦄ k₀ (sig_map pp i m xs) ≈ k₁ xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    sg ← sample_sig_roots PP N F dN pp i m ;; k₀ sg
    ≈ xs ← sample_seq dN (size m) ;; k₁ xs
  ⦃ post ⦄.
Proof.
elim: m i k₀ k₁ => [|d m IH] i k₀ k₁ hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact _|] => x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The hybrid games Hud s *)

Definition hud_pk_loc := mkloc 250 (None : option (Pk FS)).
Definition hud_log_loc := mkloc 251 ([::] : seq (Msg FS)).

Definition Hud (s : nat) (b : bool) : game (I_KOTS FS) :=
  [package [fmap hud_pk_loc ; hud_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get hud_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      pp ← dPP ;;
      xs ← sample_seq dN l ;;
      #put hud_pk_loc :=
        Some (pp, ends_from_sig PP N F l w pp m (roots_map pp s 0 m xs)) ;;
      #put hud_log_loc := [:: m] ;;
      ret ((pp, ends_from_sig PP N F l w pp m (roots_map pp s 0 m xs)),
           Some (roots_map pp s 0 m xs))
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, sg) {
      if b then
        pk ← getSome hud_pk_loc ;;
        log ← get hud_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m sg && (m \notin log))
      else
        ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Endpoint identifications *)

(** Invariant for both endpoint hops: heaps agree outside the four
    private locations; the G0v/G1v locations on the left mirror the
    Hud locations on the right (G0flat_perfect's recipe). *)
Notation inv01 := (
  heap_ignore ([fmap g0v_pk_loc PP N F dPP dN l w tsum ;
                g0v_log_loc PP N F dPP dN l w tsum ;
                hud_pk_loc ; hud_log_loc ])
  ⋊ couple_cross (g0v_pk_loc PP N F dPP dN l w tsum) hud_pk_loc eq
  ⋊ couple_cross (g0v_log_loc PP N F dPP dN l w tsum) hud_log_loc eq
).

Lemma G0v_Hud0 (b : bool) :
  perfect (I_KOTS FS) (G0v PP N F dPP dN l w tsum b) (Hud 0 b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv01).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  ssprove_sync => hv.
  have hm : size m = l by case/and3P: hv => /eqP.
  have hwd : wf_digits w m by case/and3P: hv.
  eapply r_scheme_bind; [exact _|] => pp.
  eapply r_sample_seq_size => xs hxs.
  rewrite ends_from_roots_map0 // roots_map_sign //.
  apply r_put_vs_put.
  apply r_put_vs_put.
  ssprove_restore_mem.
  { ssprove_invariant. }
  by apply r_ret.
- destruct arg as [m sg].
  destruct b; last by apply r_ret.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  eapply r_get_remember_lhs => log.
  eapply r_get_remember_rhs => log'.
  ssprove_rem_rel 0%N => e'. subst log'.
  ssprove_forget_all.
  by apply r_ret.
Qed.

Lemma G1v_Hudw (b : bool) :
  perfect (I_KOTS FS) (G1v PP N F dPP dN l w tsum b) (Hud w.-2 b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv01).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  ssprove_sync => hv.
  have hm : size m = l by case/and3P: hv => /eqP.
  have hwd : wf_digits w m by case/and3P: hv.
  eapply r_scheme_bind; [exact _|] => pp.
  have -> : sample_seq dN l = sample_seq dN (size m) by rewrite hm.
  eapply r_sample_sig_roots => xs hxs.
  rewrite sig_map_roots //.
  apply r_put_vs_put.
  apply r_put_vs_put.
  ssprove_restore_mem.
  { ssprove_invariant. }
  by apply r_ret.
- destruct arg as [m sg].
  destruct b; last by apply r_ret.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  eapply r_get_remember_lhs => log.
  eapply r_get_remember_rhs => log'.
  ssprove_rem_rel 0%N => e'. subst log'.
  ssprove_forget_all.
  by apply r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The SM-UD reduction R_ud *)

Definition rud_pk_loc := mkloc 252 (None : option (Pk FS)).
Definition rud_log_loc := mkloc 253 ([::] : seq (Msg FS)).

(** The query loop: one UQUERY at tweak [(i, s)] per chain with
    [d >= s + 2] (the chains on which the neighbouring hybrids
    differ), a direct root sample for the others. *)
Fixpoint rud_loop (s i : nat) (m : seq nat) : raw_code (chList N) :=
  match m with
  | [::] => ret [::]
  | d :: m' =>
      y ← (if s.+2 <= d
           then call [ UQUERY ] : { ('nat × 'nat) ~> N } (i, s)
           else u ← dN ;; ret u) ;;
      ys ← rud_loop s i.+1 m' ;;
      ret (y :: ys)
  end.

#[export] Instance rud_loop_valid (L : Locations) (s i : nat) (m : seq nat) :
  ValidCode L (I_SMUD T C) (rud_loop s i m).
Proof.
elim: m i => [|d m IH] i /=.
- apply valid_ret.
- eapply valid_bind.
  + case: (s.+2 <= d).
    * eapply valid_opr; first by fmap_solve.
      move=> v; apply valid_ret.
    * eapply valid_bind; [eapply valid_scheme, prog_valid|].
      move=> u; apply valid_ret.
  + move=> y; eapply valid_bind; [exact: IH|].
    move=> ys; apply valid_ret.
Qed.

(** The reduction.  The UCOLLQ call before the loop forces the
    SM-UD game's lazy [pp] initialisation at a FIXED program point
    in both the real and the ideal composition (see header). *)
Definition R_ud (b : bool) (s : nat) : package (I_SMUD T C) (I_KOTS FS) :=
  [package [fmap rud_pk_loc ; rud_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get rud_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      _ ← (call [ UCOLLQ ] : { ('unit × 'unit) ~> 'unit } (tt, tt)) ;;
      ys ← rud_loop s 0 m ;;
      pp ← (call [ UGETPP ] : { 'unit ~> PP } tt) ;;
      #put rud_pk_loc :=
        Some (pp, ends_from_sig PP N F l w pp m (rud_sig pp s 0 m ys)) ;;
      #put rud_log_loc := [:: m] ;;
      ret ((pp, ends_from_sig PP N F l w pp m (rud_sig pp s 0 m ys)),
           Some (rud_sig pp s 0 m ys))
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, sg) {
      if b then
        pk ← getSome rud_pk_loc ;;
        log ← get rud_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m sg && (m \notin log))
      else
        ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** The query-loop couplings

    Loop-invariant precondition: heaps agree outside the private
    locations, [pp] is initialised (by the UCOLLQ call) and UGETPP
    has not yet been called.  [Prop]-style (see the mini-rules
    above); the tweak list is pinned separately since it grows. *)

Notation LL := ([fmap hud_pk_loc ; hud_log_loc ; rud_pk_loc ; rud_log_loc ;
                 ud_pp_loc T ; ud_tws_loc T ; ud_rev_loc ]).

Definition rud_pre (pp : PP) : precond :=
  λ '(s₀, s₁),
    [/\ heap_ignore LL (s₀, s₁),
        get_heap s₁ (ud_pp_loc T) = Some pp
      & get_heap s₁ ud_rev_loc = false].

Arguments rud_pre : simpl never.

(** Loop precondition with the current tweak list pinned. *)
Definition rud_pre_t (pp : PP) (tws : seq (nat * nat)) : precond :=
  λ '(s₀, s₁),
    rud_pre pp (s₀, s₁) /\ get_heap s₁ (ud_tws_loc T) = tws.

Arguments rud_pre_t : simpl never.

Lemma rud_pre_set_tws (pp : PP) (v : ud_tws_loc T) (s₀ s₁ : heap) :
  rud_pre pp (s₀, s₁) ->
  rud_pre pp (s₀, set_heap s₁ (ud_tws_loc T) v).
Proof.
case=> h1 h2 h3; split.
- by apply: heap_ignore_set_rhs h1; apply: fhas_in; fmap_solve.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

Lemma r_rud_loop_real (pp : PP) (s i : nat) (m : seq nat)
    (tws : seq (nat * nat)) :
  (size tws + count [pred d | s.+2 <= d] m <= l)%N ->
  (forall j : nat, i <= j -> ((j, s) \notin tws)) ->
  ⊢ ⦃ λ '(s₀, s₁), rud_pre_t pp tws (s₀, s₁) ⦄
      sample_seq dN (size m)
    ≈ code_link (rud_loop s i m) (SMUD_game T C l true)
  ⦃ λ '(xs, s₀) '(ys, s₁),
      (rud_pre pp (s₀, s₁) /\ size xs = size m)
      /\ ys = uq_real_map pp s i m xs ⦄.
Proof.
elim: m i tws => [|d m IH] i tws hcnt hfresh /=.
- by apply r_ret => s₀ s₁ [hpre htws]; split; [split|].
- rewrite code_link_bind.
  case: (boolP (s.+2 <= d)) => hd.
  + (* queried chain: inlined real UQUERY *)
    ssprove_code_simpl; simpl.
    (* get ud_rev; assert passes *)
    eapply (r_get_rhs_pin ud_rev_loc false);
      first by move=> s₀ s₁ [[_ _ h] _].
    simpl.
    (* get ud_tws; both asserts pass *)
    eapply (r_get_rhs_pin (ud_tws_loc T) tws);
      first by move=> s₀ s₁ [_ h].
    have hlt : size tws < l.
    { apply: leq_trans hcnt; rewrite /= hd add1n addnS ltnS.
      exact: leq_addr. }
    have hni : (i, s) \notin tws := hfresh i (leqnn i).
    rewrite hlt hni; simpl.
    (* put ud_tws := rcons tws (i, s) *)
    eapply (r_put_rhs_pre (ud_tws_loc T) (rcons tws (i, s)) _
      (rud_pre_t pp (rcons tws (i, s)))).
    { move=> s₀ s₁ [hpre _]; split.
      - exact: rud_pre_set_tws.
      - exact: get_set_heap_eq. }
    (* get ud_pp: initialised by the UCOLLQ call *)
    eapply (r_get_rhs_pin (ud_pp_loc T) (Some pp));
      first by move=> s₀ s₁ [[_ h _] _].
    rewrite !bind_assoc; simpl.
    (* the hidden sample, coupled with the hybrid's root *)
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by move: hcnt; rewrite /= hd add1n addnS size_rcons addSn. }
      move=> j hij; rewrite mem_rcons in_cons negb_or; apply/andP; split.
      { by rewrite xpair_eqE eqxx andbT gtn_eqF. }
      exact: hfresh (ltnW hij).
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
  + (* direct sample *)
    ssprove_code_simpl; simpl.
    rewrite (code_link_scheme _ _ _ _ (prog_valid dN)) bind_ret.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by move: hcnt; rewrite /= (negbTE hd) add0n. }
      move=> j hij; exact: hfresh (ltnW hij).
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
Qed.

Lemma r_rud_loop_ideal (pp : PP) (s i : nat) (m : seq nat)
    (tws : seq (nat * nat)) :
  (size tws + count [pred d | s.+2 <= d] m <= l)%N ->
  (forall j : nat, i <= j -> ((j, s) \notin tws)) ->
  ⊢ ⦃ λ '(s₀, s₁), rud_pre_t pp tws (s₀, s₁) ⦄
      sample_seq dN (size m)
    ≈ code_link (rud_loop s i m) (SMUD_game T C l false)
  ⦃ λ '(xs, s₀) '(ys, s₁),
      (rud_pre pp (s₀, s₁) /\ size xs = size m)
      /\ ys = xs ⦄.
Proof.
elim: m i tws => [|d m IH] i tws hcnt hfresh /=.
- by apply r_ret => s₀ s₁ [hpre htws]; split; [split|].
- rewrite code_link_bind.
  case: (boolP (s.+2 <= d)) => hd.
  + (* queried chain: inlined ideal UQUERY *)
    ssprove_code_simpl; simpl.
    eapply (r_get_rhs_pin ud_rev_loc false);
      first by move=> s₀ s₁ [[_ _ h] _].
    simpl.
    eapply (r_get_rhs_pin (ud_tws_loc T) tws);
      first by move=> s₀ s₁ [_ h].
    have hlt : size tws < l.
    { apply: leq_trans hcnt; rewrite /= hd add1n addnS ltnS.
      exact: leq_addr. }
    have hni : (i, s) \notin tws := hfresh i (leqnn i).
    rewrite hlt hni; simpl.
    eapply (r_put_rhs_pre (ud_tws_loc T) (rcons tws (i, s)) _
      (rud_pre_t pp (rcons tws (i, s)))).
    { move=> s₀ s₁ [hpre _]; split.
      - exact: rud_pre_set_tws.
      - exact: get_set_heap_eq. }
    rewrite !bind_assoc; simpl.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by move: hcnt; rewrite /= hd add1n addnS size_rcons addSn. }
      move=> j hij; rewrite mem_rcons in_cons negb_or; apply/andP; split.
      { by rewrite xpair_eqE eqxx andbT gtn_eqF. }
      exact: hfresh (ltnW hij).
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
  + (* direct sample *)
    ssprove_code_simpl; simpl.
    rewrite (code_link_scheme _ _ _ _ (prog_valid dN)) bind_assoc; simpl.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by move: hcnt; rewrite /= (negbTE hd) add0n. }
      move=> j hij; exact: hfresh (ltnW hij).
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The adjacent-hybrid equivalences *)

(** Invariant: heaps agree outside the private locations; the Hud
    locations on the left mirror the R_ud locations on the right; and
    as long as no commitment happened ([rud_pk_loc] still [None]) the
    SM-UD oracle state is untouched (its lazy [pp] is unset, UGETPP
    has not been called, no tweak was queried) — which is what lets
    COMMIT inline the oracle code deterministically. *)
Notation invR := (
  heap_ignore LL
  ⋊ couple_cross hud_pk_loc rud_pk_loc eq
  ⋊ couple_cross hud_log_loc rud_log_loc eq
  ⋊ couple_rhs rud_pk_loc (ud_pp_loc T)
      (λ pk ppo, pk = None -> ppo = None)
  ⋊ couple_rhs rud_pk_loc ud_rev_loc
      (λ pk r, pk = None -> r = false)
  ⋊ couple_rhs rud_pk_loc (ud_tws_loc T)
      (λ pk tws, pk = None -> tws = [::])
).

Lemma Rud_real_perfect (b : bool) (s : nat) :
  perfect (I_KOTS FS) (Hud s b) (R_ud b s ∘ SMUD_game T C l true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ invR).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 4%N => e. subst pko'.
  rewrite code_link_assertD.
  ssprove_sync => hpko.
  rewrite code_link_assertD.
  ssprove_sync => hv.
  ssprove_code_simpl; simpl; simplify_linking.
  have hm : size m = l by case/and3P: hv => /eqP.
  case: pko hpko => [a|] //= _.
  (* UCOLLQ: pp is still unset, gets sampled here *)
  eapply (r_get_rhs_pin (ud_pp_loc T) None).
  { move=> s₀ s₁ [[hbase hrl] hrr].
    case: hbase => [[[[[hig hcc1] hcc2] hcr1] hcr2] hcr3].
    move: hcr1; rewrite !rel_app_cons /= => hcr1.
    move: hrr; rewrite /rem_inv /= => hrr.
    exact: hcr1 hrr. }
  rewrite !bind_assoc; simpl.
  eapply r_scheme_bind; [exact _|] => pp.
  apply r_put_rhs.
  rewrite code_link_bind.
  have -> : sample_seq dN l = sample_seq dN (size m) by rewrite hm.
  (* enter the query loop under the loop precondition *)
  eapply (rpre_weaken_rule (λ '(s₀, s₁), rud_pre_t pp [::] (s₀, s₁)));
    last first.
  { move=> s₀ s₁ [s₁' [hh e]]; subst s₁.
    case: hh => [[hbase hrl] hrr].
    case: hbase => [[[[[hig hcc1] hcc2] hcr1] hcr2] hcr3].
    move: hcr2 hcr3; rewrite !rel_app_cons /= => hcr2 hcr3.
    move: hrr; rewrite /rem_inv /= => hrr.
    split; first split.
    - by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
    - exact: get_set_heap_eq.
    - rewrite get_set_heap_neq //; exact: hcr2 hrr.
    - rewrite get_set_heap_neq //; exact: hcr3 hrr. }
  eapply r_bind.
  { apply: r_rud_loop_real.
    - rewrite /= add0n; apply: leq_trans (count_size _ _) _.
      by rewrite hm.
    - by []. }
  move=> xs ys.
  eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
  eapply (rpre_weaken_rule (λ '(h₀, h₁), rud_pre pp (h₀, h₁)));
    last by move=> ? ? /= [-> ->].
  subst ys.
  simpl; simplify_linking.
  (* UGETPP: reveal the (already set) pp *)
  eapply (r_get_rhs_pin (ud_pp_loc T) (Some pp));
    first by move=> ? ? [].
  simpl.
  eapply (r_put_rhs_pre ud_rev_loc true _
    (λ '(h₀, h₁), heap_ignore LL (h₀, h₁))).
  { move=> h₀ h₁ [hig _ _].
    by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve. }
  rewrite rud_sig_real.
  apply r_put_vs_put.
  apply r_put_vs_put.
  apply r_ret => h₀ h₁ [a [[b' [[c [[d [hig ->]] ->]] ->]] ->]].
  split; first by [].
  split; first split; first split; first split; first split.
  - apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by rewrite get_set_heap_neq // get_set_heap_eq.
  - by rewrite !rel_app_cons /= !get_set_heap_eq.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by [].
- destruct arg as [m sg].
  destruct b.
  + ssprove_code_simpl; simpl.
    eapply r_get_remember_lhs => pko.
    eapply r_get_remember_rhs => pko'.
    ssprove_rem_rel 4%N => e. subst pko'.
    rewrite code_link_assertD.
    ssprove_sync => hpko.
    simpl.
    eapply r_get_remember_lhs => log.
    eapply r_get_remember_rhs => log'.
    ssprove_rem_rel 3%N => e'. subst log'.
    ssprove_forget_all.
    by apply r_ret.
  + ssprove_code_simpl; simpl.
    by apply r_ret.
Qed.

Lemma Rud_ideal_perfect (b : bool) (s : nat) :
  perfect (I_KOTS FS) (Hud s.+1 b) (R_ud b s ∘ SMUD_game T C l false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ invR).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 4%N => e. subst pko'.
  rewrite code_link_assertD.
  ssprove_sync => hpko.
  rewrite code_link_assertD.
  ssprove_sync => hv.
  ssprove_code_simpl; simpl; simplify_linking.
  have hm : size m = l by case/and3P: hv => /eqP.
  case: pko hpko => [a|] //= _.
  (* UCOLLQ: pp is still unset, gets sampled here *)
  eapply (r_get_rhs_pin (ud_pp_loc T) None).
  { move=> s₀ s₁ [[hbase hrl] hrr].
    case: hbase => [[[[[hig hcc1] hcc2] hcr1] hcr2] hcr3].
    move: hcr1; rewrite !rel_app_cons /= => hcr1.
    move: hrr; rewrite /rem_inv /= => hrr.
    exact: hcr1 hrr. }
  rewrite !bind_assoc; simpl.
  eapply r_scheme_bind; [exact _|] => pp.
  apply r_put_rhs.
  rewrite code_link_bind.
  have -> : sample_seq dN l = sample_seq dN (size m) by rewrite hm.
  (* enter the query loop under the loop precondition *)
  eapply (rpre_weaken_rule (λ '(s₀, s₁), rud_pre_t pp [::] (s₀, s₁)));
    last first.
  { move=> s₀ s₁ [s₁' [hh e]]; subst s₁.
    case: hh => [[hbase hrl] hrr].
    case: hbase => [[[[[hig hcc1] hcc2] hcr1] hcr2] hcr3].
    move: hcr2 hcr3; rewrite !rel_app_cons /= => hcr2 hcr3.
    move: hrr; rewrite /rem_inv /= => hrr.
    split; first split.
    - by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
    - exact: get_set_heap_eq.
    - rewrite get_set_heap_neq //; exact: hcr2 hrr.
    - rewrite get_set_heap_neq //; exact: hcr3 hrr. }
  eapply r_bind.
  { apply: r_rud_loop_ideal.
    - rewrite /= add0n; apply: leq_trans (count_size _ _) _.
      by rewrite hm.
    - by []. }
  move=> xs ys.
  eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
  eapply (rpre_weaken_rule (λ '(h₀, h₁), rud_pre pp (h₀, h₁)));
    last by move=> ? ? /= [-> ->].
  subst ys.
  simpl; simplify_linking.
  (* UGETPP: reveal the (already set) pp *)
  eapply (r_get_rhs_pin (ud_pp_loc T) (Some pp));
    first by move=> ? ? [].
  simpl.
  eapply (r_put_rhs_pre ud_rev_loc true _
    (λ '(h₀, h₁), heap_ignore LL (h₀, h₁))).
  { move=> h₀ h₁ [hig _ _].
    by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve. }
  rewrite rud_sig_ideal.
  apply r_put_vs_put.
  apply r_put_vs_put.
  apply r_ret => h₀ h₁ [a [[b' [[c [[d [hig ->]] ->]] ->]] ->]].
  split; first by [].
  split; first split; first split; first split; first split.
  - apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by rewrite get_set_heap_neq // get_set_heap_eq.
  - by rewrite !rel_app_cons /= !get_set_heap_eq.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by [].
- destruct arg as [m sg].
  destruct b.
  + ssprove_code_simpl; simpl.
    eapply r_get_remember_lhs => pko.
    eapply r_get_remember_rhs => pko'.
    ssprove_rem_rel 4%N => e. subst pko'.
    rewrite code_link_assertD.
    ssprove_sync => hpko.
    simpl.
    eapply r_get_remember_lhs => log.
    eapply r_get_remember_rhs => log'.
    ssprove_rem_rel 3%N => e'. subst log'.
    ssprove_forget_all.
    by apply r_ret.
  + ssprove_code_simpl; simpl.
    by apply r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The telescope *)

(** THE deliverable: for either KFORGE-bit [b], the distance between
    the position-0-rooted game [G0v b] and the re-rooted game [G1v b]
    is bounded by [w - 2] SM-UD distinguishing advantages, one per
    hybrid step, each through the reduction [R_ud b s].  Instantiates
    SSProve's [Adv_hybrid_dep] with
      [Game s b' := R_ud b s ∘ SMUD_game T C l b'],
    whose endpoints are identified with [G0v b]/[G1v b] through
    [Hud 0]/[Hud w.-2] and whose adjacent hybrids meet in
    [Hud s.+1]. *)
Lemma UD_telescope (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS FS) A_export A) :
  (Adv (G0v PP N F dPP dN l w tsum b) (G1v PP N F dPP dN l w tsum b) A
     <= \sum_(0 <= s < w.-2)
          AdvOf (SMUD_game T C l) (A ∘ R_ud b s))%R.
Proof.
have hperf0 : perfect (I_KOTS FS)
    (G0v PP N F dPP dN l w tsum b)
    ((R_ud b 0 ∘ SMUD_game T C l true)%sep).
{ exact: perfect_trans (G0v_Hud0 b) (Rud_real_perfect b 0). }
have hperfw : perfect (I_KOTS FS)
    (G1v PP N F dPP dN l w tsum b)
    ((R_ud b w.-2 ∘ SMUD_game T C l true)%sep).
{ exact: perfect_trans (G1v_Hudw b) (Rud_real_perfect b w.-2). }
have hadj : forall s : nat, s < w.-2 ->
    perfect (I_KOTS FS)
      ((R_ud b s ∘ SMUD_game T C l false)%sep)
      ((R_ud b s.+1 ∘ SMUD_game T C l true)%sep).
{ move=> s _.
  exact: perfect_trans (perfect_sym (Rud_ideal_perfect b s))
           (Rud_real_perfect b s.+1). }
have h := Adv_hybrid_dep (n := w.-2)
  (Multi := fun b' => if b' then as_nom (G0v PP N F dPP dN l w tsum b)
                      else as_nom (G1v PP N F dPP dN l w tsum b))
  (Game := fun s b' => (R_ud b s ∘ SMUD_game T C l b')%sep)
  (A := A) hperf0 hperfw hadj.
have -> : (\sum_(0 <= s < w.-2) AdvOf (SMUD_game T C l) (A ∘ R_ud b s)
  = \sum_(0 <= s < w.-2)
      AdvOf (λ b' : bool, (R_ud b s ∘ SMUD_game T C l b')%sep) A)%R.
{ by apply: eq_big_nat => s _; rewrite Adv_reduction. }
exact: h.
Qed.

End wots_ud_hop.
