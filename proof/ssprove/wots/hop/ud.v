(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.ud

    The SM-UD hybrid telescope of the WOTS+C one-time security proof,
    step "UD hybrids (G_forge_sampledkey -> G_forge_uniformchains)": relating [G_forge_sampledkey] (chains rooted at
    position 0) to [G_forge_uniformchains] (chains re-rooted at the digits of the
    grinded digest) through the hybrid games [Hw s].

    Built on the generic SM-UD chain layer [Sec.lib.chain.ud], whose pure
    layer ([roots_map]/[rud_sig]/[uq_real_map]/[sig_map] and their
    identities), sampler couplings ([r_sample_seq_size],
    [r_sample_sig_roots]) and relational mini-rules ([r_get_rhs_pin],
    [r_put_rhs_pre], [heap_ignore_set_l/rhs]) apply at the
    address-wrapped chain hash [Fw] (the Sec.games bridge):
    [Fw pp (i, k) x = F pp (chain_adrs i k) x], so all of them line up
    with shrincs_wots_scheme's [chainf]/[complete_ends] by conversion.

    ** Specifics of this instantiation

    - The digit vector is the GRINDING DIGEST: COMMIT first asserts
      grinding success and computes [d := digest_of pp m c] at the
      found counter [c]; only then are the [chain_count] chains sampled, with
      the hybrid's per-chain digit [nth 0 d i].  The digits are < w
      by [wf_digits] (from the COMMIT assert via
      [find_counter_isSome_good]), so both endpoint identifications hold
      for EVERY [w].
    - Tweaks are ENCODED CHAIN ADDRESSES: the SM-UD oracle is queried
      at [encode_adrs (chain_adrs i s)] instead of [(i, s)];
      distinctness is [encode_adrs_inj] + [chain_adrs_inj].
    - [pp] is hidden until UGETPP, but the reduction needs the digest
      BEFORE its first UQUERY (the digits select the queried chains).
      The collection [coll_chain] exposes H_grind for exactly this purpose:
      the reduction performs the grinding THROUGH the collection
      oracle — one unguarded UCOLLQ call pins [pp]'s lazy sampling at
      a fixed program point (the UCOLLQ pin), then [grind_all] queries
      H_grind at every counter below [c_max] and the bounded search
      ([grind_pick]) happens on the answers, purely; [grind_pick_map]
      identifies the result with the scheme's [find_counter].
    - The pk is COMPRESSED: ends are completed from the signature
      values ([complete_ends]) and T_sf-compressed at [pk_adrs].
      The reduction computes the compression AFTER UGETPP with [pp]
      in hand (pure post-processing, no extra oracle traffic), in the
      same shape as G_forge_uniformchains's code.

    Locations: 310/311/312 for [Hw], 313/314/315 for [R_ud] (all
    relational proofs here cross distinct ids).

    ** Telescope

    [UDw_telescope]: for every KFORGE-bit [b],
      [Adv (G_forge_sampledkey b) (G_forge_uniformchains b) A
         <= \sum_(0 <= s < w.-2) AdvOf (SMUD_game thf_chain coll_chain chain_count) (A ∘ R_ud b s)]
    via [Adv_hybrid_dep] over
      [Game s b' := R_ud b s ∘ SMUD_game thf_chain coll_chain chain_count b'].
    Note the cap [p := chain_count]: COMMIT makes at most one UQUERY per chain
    (UCOLLQ calls are not budgeted). *)

From mathcomp Require Import reals.
From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf games.smud toolkit.sample_seq toolkit.relational_rules.
From Model Require Import math.chain math.encoding.
From Sec.lib Require Import chain.core chain.ud.
From Sec Require Import addressing.
From Sec.wots Require Import addressing.
From Sec.wots Require Import scheme games analysis hop.intermediates.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section WOTSCUDHop.

(** The WOTS+C parameter record [P] (Sec.wots.params); the same
    section context as Sec.wots.games. *)
Context (P : wc_params).

(** Relational proof shorthand (twelve call sites below): remember the paired
    [get] on both sides, use the [couple_cross] relation at index [n] to
    identify the two remembered values, and [subst] the right-hand copy —
    leaving the shared value bound as [x] on the left. *)
Local Ltac ud_remember_rel x n :=
  eapply r_get_remember_lhs => x;
  let xr := fresh "xrhs" in eapply r_get_remember_rhs => xr;
  let xe := fresh "xeq" in ssprove_rem_rel n => xe;
  subst xr.

(* ------------------------------------------------------------------ *)
(** ** Pure bridges into the chain layer

    All by conversion at [FW] (smart constructors and pair
    projections iota-reduce); stated once so the endpoint proofs can
    rewrite instead of relying on implicit conversion.  [wcendsE]
    (shrincs_wots_scheme [complete_ends] = [ends_from_sig] at [FW]) is consumed from
    Sec.wots.analysis. *)

Lemma wsignE pp (xs : seq (wcp_N P)) (ds : seq nat) :
  Sec.lib.chain.core.sign_digits (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp xs ds
  = (sign_chains P) pp xs ds.
Proof. by []. Qed.

Lemma wpk_ofE pp (xs : seq (wcp_N P)) :
  (wcp_T_sf P) pp (pk_adrs P) (Sec.lib.chain.core.chain_ends (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp xs)
  = (shrincs_wots_pubkey P) pp xs.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the in-oracle grinding search

    The reduction queries H_grind through UCOLLQ at every counter
    below [c_max] ([grind_all] below) and runs the bounded search on
    the answer list: [grind_pick] returns the first (counter, digest
    value) whose decoded digits satisfy the digit-sum predicate —
    [find_counter]'s search, re-rooted at the oracle answers
    ([grind_pick_map]).  These are exactly [Sec.hop.intermediates]'s
    shared [cp_pick]/[cp_pick_map] (same picker the Compress and chain
    hops use); re-abbreviated here under this section's context. *)


(* ------------------------------------------------------------------ *)
(** ** The hybrid games Hw s *)

Definition ud_hybrid_pk_loc := mkloc 310 (None : option (Pk (shrincs_wots_scheme P))).
Definition ud_hybrid_log_loc := mkloc 311 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition ud_hybrid_sig_loc := mkloc 312 (None : option (Sig (shrincs_wots_scheme P))).

(** Per chain [i] with digit [d_i := nth 0 d i] of the grinded
    digest, [Hw s] samples ONE hidden uniform root at position
    [minn s d_i.-1] and reveals the signature value chained up to
    [d_i] ([roots_map] (Sec.lib.chain.ud) at [FW]); the pk is the
    T_sf compression of the completed ends, the stored signature
    carries the grinding counter (as in G_forge_sampledkey/G_forge_uniformchains). *)
Definition HGw (s : nat) (b : bool) : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap ud_hybrid_pk_loc ; ud_hybrid_log_loc ; ud_hybrid_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get ud_hybrid_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← (wcp_dPP P) ;;
      #assert (isSome ((find_counter P) pp m)) ;;
      let c := odflt 0 ((find_counter P) pp m) in
      let d := (digest_of P) pp m c in
      xs ← sample_seq (wcp_dN P) (wcp_chain_count P) ;;
      #put ud_hybrid_pk_loc :=
        Some (pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp d (roots_map (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d xs))) ;;
      #put ud_hybrid_log_loc := [:: m] ;;
      #put ud_hybrid_sig_loc := Some (roots_map (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d xs, c) ;;
      ret ((pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp d (roots_map (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d xs))),
           Some (roots_map (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d xs, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, sg) {
      pk ← getSome ud_hybrid_pk_loc ;;
      log ← get ud_hybrid_log_loc ;;
      if b then
        ret ((shrincs_wots_verify P) pk.1 pk.2 m sg && (m \notin log))
      else
        ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Endpoint identifications *)

(** Invariant for both endpoint hops: heaps agree outside the six
    private locations; the G_forge_sampledkey/G_forge_uniformchains locations on the left mirror the
    Hw locations on the right. *)
Local Abbreviation inv01 := (
  heap_ignore ([fmap (forge_pk_loc P) ; (forge_log_loc P) ; (forge_sig_loc P) ; ud_hybrid_pk_loc ; ud_hybrid_log_loc ; ud_hybrid_sig_loc ])
  ⋊ couple_cross (forge_pk_loc P) ud_hybrid_pk_loc eq
  ⋊ couple_cross (forge_log_loc P) ud_hybrid_log_loc eq
  ⋊ couple_cross (forge_sig_loc P) ud_hybrid_sig_loc eq
).

Lemma G_forge_sampledkey_Hw0 (b : bool) :
  perfect (I_KOTS (shrincs_wots_scheme P))
    (G_forge_sampledkey P b)
    (HGw 0 b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv01).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  ud_remember_rel pko 2%N.
  ssprove_sync => hpko.
  eapply r_scheme_bind; [exact _|] => pp.
  ssprove_sync => hctr.
  have hgood := find_counter_isSome_good P
                  pp m hctr.
  have hwd : wf_digits (wcp_w P) ((digest_of P) pp m (odflt 0 ((find_counter P) pp m))).
  { by case/andP: hgood. }
  have hm : size ((digest_of P) pp m (odflt 0 ((find_counter P) pp m))) = (wcp_chain_count P)
    := size_digest_of P pp m _.
  eapply r_sample_seq_size => xs hxs.
  rewrite !(wcendsE P) !ends_from_roots_map0 // !wpk_ofE
          !(roots_map_sign (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P)) // !wsignE.
  do 3 apply r_put_vs_put.
  ssprove_restore_mem.
  { ssprove_invariant. }
  by apply r_ret.
- destruct arg as [m sg].
  ud_remember_rel pko 2%N.
  ssprove_sync => hpko.
  ud_remember_rel log 1%N.
  ssprove_forget_all.
  case: b => /=; by apply r_ret.
Qed.

Lemma G_forge_uniformchains_Hww (b : bool) :
  perfect (I_KOTS (shrincs_wots_scheme P))
    (G_forge_uniformchains P b)
    (HGw (wcp_w P).-2 b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv01).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  ud_remember_rel pko 2%N.
  ssprove_sync => hpko.
  eapply r_scheme_bind; [exact _|] => pp.
  ssprove_sync => hctr.
  have hgood := find_counter_isSome_good P
                  pp m hctr.
  have hwd : wf_digits (wcp_w P) ((digest_of P) pp m (odflt 0 ((find_counter P) pp m))).
  { by case/andP: hgood. }
  have -> : sample_seq (wcp_dN P) (wcp_chain_count P)
            = sample_seq (wcp_dN P) (size ((digest_of P) pp m (odflt 0 ((find_counter P) pp m)))).
  { by rewrite size_digest_of. }
  eapply r_sample_sig_roots => xs hxs.
  rewrite !(sig_map_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P)) //.
  do 3 apply r_put_vs_put.
  ssprove_restore_mem.
  { ssprove_invariant. }
  by apply r_ret.
- destruct arg as [m sg].
  ud_remember_rel pko 2%N.
  ssprove_sync => hpko.
  ud_remember_rel log 1%N.
  ssprove_forget_all.
  case: b => /=; by apply r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The SM-UD reduction R_ud *)

Definition r_ud_pk_loc := mkloc 313 (None : option (Pk (shrincs_wots_scheme P))).
Definition r_ud_log_loc := mkloc 314 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition r_ud_sig_loc := mkloc 315 (None : option (Sig (shrincs_wots_scheme P))).

(** The grinding loop: one UCOLLQ call per counter below [c_max],
    each evaluating H_grind at the grinding address of this instance
    under the hidden [pp]; returns the answer list. *)
Fixpoint grind_all (m : (wcp_M P)) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      r ← (call [ UCOLLQ ] :
             { ((wc_adrs_ch P) × (('list (wcp_N P)) ∐ ((wcp_M P) × 'nat))) ~> ((wcp_N P) ∐ 'nat) }
             ((encode_tweak P) (grind_adrs P), inr (m, c))) ;;
      hs ← grind_all m cs' ;;
      ret ((if r is inr h then h else 0) :: hs)
  end.

#[export] Instance grind_all_valid (L : Locations) (m : (wcp_M P)) (cs : seq nat) :
  ValidCode L (I_SMUD (thf_chain P) (coll_chain P)) (grind_all m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** The query loop: one UQUERY at the encoded chain address
    [(i, s)] per chain with digit [>= s + 2] (the chains on which the
    neighbouring hybrids differ), a direct root sample for the
    others — [rud_loop] at encoded tweaks. *)
Fixpoint r_ud_loop (s i : nat) (ds : seq nat) : raw_code (chList (wcp_N P)) :=
  match ds with
  | [::] => ret [::]
  | d :: ds' =>
      y ← (if s.+2 <= d
           then call [ UQUERY ] : { (wc_adrs_ch P) ~> (wcp_N P) } (chain_tweak P i s)
           else u ← (wcp_dN P) ;; ret u) ;;
      ys ← r_ud_loop s i.+1 ds' ;;
      ret (y :: ys)
  end.

#[export] Instance r_ud_loop_valid (L : Locations) (s i : nat) (ds : seq nat) :
  ValidCode L (I_SMUD (thf_chain P) (coll_chain P)) (r_ud_loop s i ds).
Proof.
elim: ds i => [|d ds IH] i /=.
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

(** The reduction.  COMMIT: one unguarded UCOLLQ call pins [pp]'s
    lazy sampling at a fixed program point in both compositions (the
    UCOLLQ pin), the grinding runs through the collection oracle
    ([grind_all] + the pure [grind_pick]), the per-chain
    queries follow at the digest's digits, then UGETPP reveals [pp]
    and COMMIT finishes purely (compressed pk from the completed
    ends, exactly G_forge_uniformchains's code shape). *)
(* Performance: build the package term with [notypeclasses refine] so the
   [ValidPackage] hole is NOT resolved during elaboration (when the call's
   import interface is still a metavariable, which sends [fmap_solve] into a
   ~330s fsubmap search); discharge it afterwards on the now-concrete goal
   with [ssprove_valid], then close the [grind_all]/[r_ud_loop] subgoals via
   their registered [ValidCode] instances.  Cuts this definition ~330s -> <1s. *)
Definition R_ud (b : bool) (s : nat) : package (I_SMUD (thf_chain P) (coll_chain P)) (I_KOTS (shrincs_wots_scheme P)).
Proof.
  notypeclasses refine [package [fmap r_ud_pk_loc ; r_ud_log_loc ; r_ud_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get r_ud_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← (call [ UCOLLQ ] :
             { ((wc_adrs_ch P) × (('list (wcp_N P)) ∐ ((wcp_M P) × 'nat))) ~> ((wcp_N P) ∐ 'nat) }
             ((encode_tweak P) (grind_adrs P), inl [::])) ;;
      hs ← grind_all m (iota 0 (wcp_c_max P)) ;;
      #assert (isSome ((intermediates.cp_pick P) hs)) ;;
      let c := (odflt (0, 0) ((intermediates.cp_pick P) hs)).1 in
      let d := rev (digits_w (wcp_w P) (wcp_chain_count P) (odflt (0, 0) ((intermediates.cp_pick P) hs)).2) in
      ys ← r_ud_loop s 0 d ;;
      pp ← (call [ UGETPP ] : { 'unit ~> (wcp_PP P) } tt) ;;
      #put r_ud_pk_loc :=
        Some (pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp d (rud_sig (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d ys))) ;;
      #put r_ud_log_loc := [:: m] ;;
      #put r_ud_sig_loc := Some (rud_sig (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d ys, c) ;;
      ret ((pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp d (rud_sig (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d ys))),
           Some (rud_sig (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 d ys, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, sg) {
      pk ← getSome r_ud_pk_loc ;;
      log ← get r_ud_log_loc ;;
      if b then
        ret ((shrincs_wots_verify P) pk.1 pk.2 m sg && (m \notin log))
      else
        ret false
    }
  ].
  ssprove_valid.
  all: typeclasses eauto.
Defined.

(* ------------------------------------------------------------------ *)
(** ** The oracle-loop couplings

    Loop-invariant preconditions: heaps agree outside the private
    locations, [pp] is initialised (by the UCOLLQ pin) and UGETPP has
    not been called; the tweak list is pinned separately since the
    query loop grows it. *)

Local Abbreviation LL := ([fmap ud_hybrid_pk_loc ; ud_hybrid_log_loc ; ud_hybrid_sig_loc ;
                 r_ud_pk_loc ; r_ud_log_loc ; r_ud_sig_loc ;
                 ud_pp_loc (thf_chain P) ; ud_tws_loc (thf_chain P) ; ud_rev_loc ]).

Definition r_ud_pre (pp : (wcp_PP P)) : precond :=
  λ '(s₀, s₁),
    [/\ heap_ignore LL (s₀, s₁),
        get_heap s₁ (ud_pp_loc (thf_chain P)) = Some pp
      & get_heap s₁ ud_rev_loc = false].

Arguments r_ud_pre : simpl never.

Definition r_ud_pre_t (pp : (wcp_PP P)) (tws : seq (wc_adrs_ch P)) : precond :=
  λ '(s₀, s₁),
    r_ud_pre pp (s₀, s₁) /\ get_heap s₁ (ud_tws_loc (thf_chain P)) = tws.

Arguments r_ud_pre_t : simpl never.

Lemma r_ud_pre_set_tws (pp : (wcp_PP P)) (v : ud_tws_loc (thf_chain P)) (s₀ s₁ : heap) :
  r_ud_pre pp (s₀, s₁) ->
  r_ud_pre pp (s₀, set_heap s₁ (ud_tws_loc (thf_chain P)) v).
Proof.
case=> h1 h2 h3; split.
- by apply: heap_ignore_set_r h1; apply: fhas_in; fmap_solve.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The grinding loop is rhs-only and deterministic once [pp] is
    pinned: every UCOLLQ call reads the initialised [ud_pp_loc] and
    returns an H_grind evaluation; the precondition is preserved and
    the continuation receives the honest answer list. *)
Lemma r_grind_all (b : bool) {B Bc : choiceType} (pp : (wcp_PP P)) (m : (wcp_M P))
    (cs : seq nat) (pre : precond) (post : postcond B Bc)
    (c₀ : raw_code B) (k : chList 'nat -> raw_code Bc) :
  (forall s₀ s₁, pre (s₀, s₁) -> get_heap s₁ (ud_pp_loc (thf_chain P)) = Some pp) ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      c₀ ≈ k [seq (wcp_H_grind P) pp (grind_adrs P) (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
      c₀ ≈ bind (code_link (grind_all m cs) (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) b)) k ⦃ post ⦄.
Proof.
elim: cs k => [|c cs IH] k hpin hk /=.
- exact: hk.
- ssprove_code_simpl; simpl; simplify_linking.
  eapply (r_get_rhs_pin (ud_pp_loc (thf_chain P)) (Some pp)); first exact: hpin.
  simpl.
  rewrite code_link_bind bind_assoc; simpl.
  (* The UCOLLQ answer at the grind tweak IS H_grind at the grind
     address: the decoded grind tweak reproduces [gadrs] ([encode_adrsK]);
     fold the simplified record back to [gadrs]. *)
  rewrite [X in (wcp_H_grind P) pp X](_ : _ = (grind_adrs P)); last exact: ((encode_tweakK P) (grind_adrs P)).
  apply: IH; [exact: hpin | exact: hk].
Qed.

(** The query-loop couplings ([r_rud_loop_real/ideal] at encoded
    tweaks; the [_l] wrappers below specialise to chain 0, an empty
    tweak list and a length-[chain_count] digit list, which is how the
    adjacent-hybrid proofs consume them). *)
Lemma r_rw_loop_real (pp : (wcp_PP P)) (s i : nat) (ds : seq nat)
    (tws : seq (wc_adrs_ch P)) :
  (s < (wcp_w P).-1)%N ->
  (i + size ds <= (wcp_chain_count P))%N ->
  (size tws + count [pred d | s.+2 <= d] ds <= (wcp_chain_count P))%N ->
  (forall j : nat, i <= j -> (j < (wcp_chain_count P))%N -> (chain_tweak P j s \notin tws)) ->
  ⊢ ⦃ λ '(s₀, s₁), r_ud_pre_t pp tws (s₀, s₁) ⦄
      sample_seq (wcp_dN P) (size ds)
    ≈ code_link (r_ud_loop s i ds) (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true)
  ⦃ λ '(xs, s₀) '(ys, s₁),
      (r_ud_pre pp (s₀, s₁) /\ size xs = size ds)
      /\ ys = uq_real_map (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s i ds xs ⦄.
Proof.
move=> hs.
elim: ds i tws => [|d ds IH] i tws hicc hcnt hfresh /=.
- by apply r_ret => s₀ s₁ [hpre htws]; split; [split|].
- have hicc0 : (i < (wcp_chain_count P))%N.
  { by apply: leq_trans hicc; rewrite /= addnS ltnS leq_addr. }
  rewrite code_link_bind.
  case: (boolP (s.+2 <= d)) => hd.
  + (* queried chain: inlined real UQUERY *)
    ssprove_code_simpl; simpl.
    eapply (r_get_rhs_pin ud_rev_loc false);
      first by move=> s₀ s₁ [[_ _ h] _].
    simpl.
    eapply (r_get_rhs_pin (ud_tws_loc (thf_chain P)) tws);
      first by move=> s₀ s₁ [_ h].
    have hlt : size tws < (wcp_chain_count P).
    { apply: leq_trans hcnt; rewrite /= hd add1n addnS ltnS.
      exact: leq_addr. }
    have hni : (chain_tweak P i s \notin tws) := hfresh i (leqnn i) hicc0.
    rewrite hlt hni; simpl.
    eapply (r_put_rhs_pre (ud_tws_loc (thf_chain P))
      (rcons tws (chain_tweak P i s)) _
      (r_ud_pre_t pp (rcons tws (chain_tweak P i s)))).
    { move=> s₀ s₁ [hpre _]; split.
      - exact: r_ud_pre_set_tws.
      - exact: get_set_heap_eq. }
    eapply (r_get_rhs_pin (ud_pp_loc (thf_chain P)) (Some pp));
      first by move=> s₀ s₁ [[_ h _] _].
    rewrite !bind_assoc; simpl.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by rewrite addSnnS. }
      { by move: hcnt; rewrite /= hd add1n addnS size_rcons addSn. }
      move=> j hij hjcc; rewrite mem_rcons in_cons negb_or; apply/andP; split.
      { apply/eqP => e.
        have ej : j = i := proj1 (chain_tweak_inj P j s i s hjcc hicc0 hs hs e).
        by rewrite ej ltnn in hij. }
      exact: hfresh (ltnW hij) hjcc.
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      (* The real UQUERY answer at the chain tweak IS the wrapped chain
         hash.  With the EXACT tweak space [decode_tweak (ctw i s)] is
         [otf (fto (cadrs i s))], no longer definitionally [cadrs i s], so
         the chain-hash head needs an explicit [decode_adrs_chain_tweak]
         fold (the [otf]/[fto] cancel). *)
      congr (_ :: _); last exact: hys.
      have hsw : (s < (wcp_w P))%N by apply: (ltn_trans hs); rewrite ltn_predL; apply: (ltnW (wcp_Hw P)).
      by rewrite core_decodeE (decode_chain_tweak P) (FcE (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp i s x hsw).
  + (* direct sample *)
    ssprove_code_simpl; simpl.
    rewrite (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P))) bind_ret.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by rewrite addSnnS. }
      { by move: hcnt; rewrite /= (negbTE hd) add0n. }
      move=> j hij hjcc; exact: hfresh (ltnW hij) hjcc.
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
Qed.

Lemma r_rw_loop_ideal (pp : (wcp_PP P)) (s i : nat) (ds : seq nat)
    (tws : seq (wc_adrs_ch P)) :
  (s < (wcp_w P).-1)%N ->
  (i + size ds <= (wcp_chain_count P))%N ->
  (size tws + count [pred d | s.+2 <= d] ds <= (wcp_chain_count P))%N ->
  (forall j : nat, i <= j -> (j < (wcp_chain_count P))%N -> (chain_tweak P j s \notin tws)) ->
  ⊢ ⦃ λ '(s₀, s₁), r_ud_pre_t pp tws (s₀, s₁) ⦄
      sample_seq (wcp_dN P) (size ds)
    ≈ code_link (r_ud_loop s i ds) (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) false)
  ⦃ λ '(xs, s₀) '(ys, s₁),
      (r_ud_pre pp (s₀, s₁) /\ size xs = size ds)
      /\ ys = xs ⦄.
Proof.
move=> hs.
elim: ds i tws => [|d ds IH] i tws hicc hcnt hfresh /=.
- by apply r_ret => s₀ s₁ [hpre htws]; split; [split|].
- have hicc0 : (i < (wcp_chain_count P))%N.
  { by apply: leq_trans hicc; rewrite /= addnS ltnS leq_addr. }
  rewrite code_link_bind.
  case: (boolP (s.+2 <= d)) => hd.
  + (* queried chain: inlined ideal UQUERY *)
    ssprove_code_simpl; simpl.
    eapply (r_get_rhs_pin ud_rev_loc false);
      first by move=> s₀ s₁ [[_ _ h] _].
    simpl.
    eapply (r_get_rhs_pin (ud_tws_loc (thf_chain P)) tws);
      first by move=> s₀ s₁ [_ h].
    have hlt : size tws < (wcp_chain_count P).
    { apply: leq_trans hcnt; rewrite /= hd add1n addnS ltnS.
      exact: leq_addr. }
    have hni : (chain_tweak P i s \notin tws) := hfresh i (leqnn i) hicc0.
    rewrite hlt hni; simpl.
    eapply (r_put_rhs_pre (ud_tws_loc (thf_chain P))
      (rcons tws (chain_tweak P i s)) _
      (r_ud_pre_t pp (rcons tws (chain_tweak P i s)))).
    { move=> s₀ s₁ [hpre _]; split.
      - exact: r_ud_pre_set_tws.
      - exact: get_set_heap_eq. }
    rewrite !bind_assoc; simpl.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by rewrite addSnnS. }
      { by move: hcnt; rewrite /= hd add1n addnS size_rcons addSn. }
      move=> j hij hjcc; rewrite mem_rcons in_cons negb_or; apply/andP; split.
      { apply/eqP => e.
        have ej : j = i := proj1 (chain_tweak_inj P j s i s hjcc hicc0 hs hs e).
        by rewrite ej ltnn in hij. }
      exact: hfresh (ltnW hij) hjcc.
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
  + (* direct sample *)
    ssprove_code_simpl; simpl.
    rewrite (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P))) bind_assoc; simpl.
    eapply r_scheme_bind; [exact _|] => x.
    eapply r_bind.
    * apply: IH.
      { by rewrite addSnnS. }
      { by move: hcnt; rewrite /= (negbTE hd) add0n. }
      move=> j hij hjcc; exact: hfresh (ltnW hij) hjcc.
    * move=> xs ys.
      eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
      apply r_ret => s₀' s₁' /= [-> ->].
      split; first by split; [exact: hpre| rewrite /= hsz].
      by rewrite hys.
Qed.

(** The COMMIT-shaped specialisations: chain 0, no tweaks queried
    yet, [chain_count] digits (the digest's length) — the lhs sampler is the
    games' [sample_seq dN chain_count]. *)
Lemma r_rw_loop_real_l (pp : (wcp_PP P)) (s : nat) (ds : seq nat) :
  (s < (wcp_w P).-1)%N ->
  size ds = (wcp_chain_count P) ->
  ⊢ ⦃ λ '(s₀, s₁), r_ud_pre_t pp [::] (s₀, s₁) ⦄
      sample_seq (wcp_dN P) (wcp_chain_count P)
    ≈ code_link (r_ud_loop s 0 ds) (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true)
  ⦃ λ '(xs, s₀) '(ys, s₁),
      (r_ud_pre pp (s₀, s₁) /\ size xs = (wcp_chain_count P))
      /\ ys = uq_real_map (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp s 0 ds xs ⦄.
Proof.
move=> hs hds.
have hcnt : (size ([::] : seq (wc_adrs_ch P))
             + count [pred d | s.+2 <= d] ds <= (wcp_chain_count P))%N.
{ by rewrite /= add0n -hds; exact: count_size. }
have hicc : (0 + size ds <= (wcp_chain_count P))%N by rewrite add0n hds.
have hfr : forall j : nat, 0 <= j -> (j < (wcp_chain_count P))%N ->
    (chain_tweak P j s \notin ([::] : seq (wc_adrs_ch P))).
{ by []. }
have h := r_rw_loop_real pp s 0 ds [::] hs hicc hcnt hfr.
by rewrite hds in h.
Qed.

Lemma r_rw_loop_ideal_l (pp : (wcp_PP P)) (s : nat) (ds : seq nat) :
  (s < (wcp_w P).-1)%N ->
  size ds = (wcp_chain_count P) ->
  ⊢ ⦃ λ '(s₀, s₁), r_ud_pre_t pp [::] (s₀, s₁) ⦄
      sample_seq (wcp_dN P) (wcp_chain_count P)
    ≈ code_link (r_ud_loop s 0 ds) (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) false)
  ⦃ λ '(xs, s₀) '(ys, s₁),
      (r_ud_pre pp (s₀, s₁) /\ size xs = (wcp_chain_count P))
      /\ ys = xs ⦄.
Proof.
move=> hs hds.
have hcnt : (size ([::] : seq (wc_adrs_ch P))
             + count [pred d | s.+2 <= d] ds <= (wcp_chain_count P))%N.
{ by rewrite /= add0n -hds; exact: count_size. }
have hicc : (0 + size ds <= (wcp_chain_count P))%N by rewrite add0n hds.
have hfr : forall j : nat, 0 <= j -> (j < (wcp_chain_count P))%N ->
    (chain_tweak P j s \notin ([::] : seq (wc_adrs_ch P))).
{ by []. }
have h := r_rw_loop_ideal pp s 0 ds [::] hs hicc hcnt hfr.
by rewrite hds in h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The adjacent-hybrid equivalences *)

(** Invariant: heaps agree outside the private locations; the Hw
    locations on the left mirror the R_ud locations on the right; and
    as long as no commitment happened ([r_ud_pk_loc] still [None]) the
    SM-UD oracle state is untouched. *)
Local Abbreviation invR := (
  heap_ignore LL
  ⋊ couple_cross ud_hybrid_pk_loc r_ud_pk_loc eq
  ⋊ couple_cross ud_hybrid_log_loc r_ud_log_loc eq
  ⋊ couple_cross ud_hybrid_sig_loc r_ud_sig_loc eq
  ⋊ couple_rhs r_ud_pk_loc (ud_pp_loc (thf_chain P))
      (λ pk ppo, pk = None -> ppo = None)
  ⋊ couple_rhs r_ud_pk_loc ud_rev_loc
      (λ pk r, pk = None -> r = false)
  ⋊ couple_rhs r_ud_pk_loc (ud_tws_loc (thf_chain P))
      (λ pk tws, pk = None -> tws = [::])
).

Lemma Rw_real_perfect (b : bool) (s : nat) (hsw : (s < (wcp_w P).-1)%nat) :
  perfect (I_KOTS (shrincs_wots_scheme P)) (HGw s b) (R_ud b s ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ invR).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  ud_remember_rel pko 5%N.
  rewrite code_link_assertD.
  ssprove_sync => hpko.
  ssprove_code_simpl; simpl; simplify_linking.
  case: pko hpko => [a|] //= _.
  (* UCOLLQ pin: pp is still unset, gets sampled here *)
  eapply (r_get_rhs_pin (ud_pp_loc (thf_chain P)) None).
  { move=> s₀ s₁ [[hbase hrl] hrr].
    case: hbase => [[[[[[hig hcc1] hcc2] hcc3] hcr1] hcr2] hcr3].
    move: hcr1; rewrite !rel_app_cons /= => hcr1.
    move: hrr; rewrite /rem_inv /= => hrr.
    exact: hcr1 hrr. }
  rewrite !bind_assoc; simpl.
  eapply r_scheme_bind; [exact _|] => pp.
  apply r_put_rhs.
  (* enter the grinding loop under the loop precondition *)
  eapply (rpre_weaken_rule (λ '(s₀, s₁), r_ud_pre_t pp [::] (s₀, s₁)));
    last first.
  { move=> s₀ s₁ [s₁' [hh e]]; subst s₁.
    case: hh => [[hbase hrl] hrr].
    case: hbase => [[[[[[hig hcc1] hcc2] hcc3] hcr1] hcr2] hcr3].
    move: hcr2 hcr3; rewrite !rel_app_cons /= => hcr2 hcr3.
    move: hrr; rewrite /rem_inv /= => hrr.
    split; first split.
    - by apply: heap_ignore_set_r hig; apply: fhas_in; fmap_solve.
    - exact: get_set_heap_eq.
    - rewrite get_set_heap_neq //; exact: hcr2 hrr.
    - rewrite get_set_heap_neq //; exact: hcr3 hrr. }
  rewrite code_link_bind.
  (* NB: the bit must be EXPLICIT: in this goal the composed SMUD game
     is the unfolded fmap-of-mkdefs literal with the bit already
     iota-reduced inside the oracle bodies, so a bare
     [eapply r_grind_all] cannot recover the [SMUD_game T C chain_count ?b]
     instance by unification; with [true] pinned, conversion identifies
     [SMUD_game T C chain_count true] with the literal.  [pp] must be explicit
     too: it does not occur in the conclusion, and the leftover evar
     in the pin premise ([Some ?pp]) defeats [done]'s assumption. *)
  eapply (r_grind_all true pp).
  { by move=> s₀ s₁ [[_ h _] _]. }
  cbv beta.
  rewrite code_link_assertD !(intermediates.cp_pick_map P).
  (* refine, not eapply: in this goal shape clenv unification fails
     but elaboration succeeds *)
  refine (r_assertD _ _ _ _ _ _ _ _).
  { by move=> ? _; case: ((find_counter P) pp m). }
  move=> e₀ _.
  move: e₀; case E: ((find_counter P) pp m) => [c|] /= e₀; last by [].
  rewrite code_link_bind.
  eapply r_bind.
  { apply: r_rw_loop_real_l => //.
    by rewrite size_rev size_digits_w. }
  move=> xs ys.
  eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
  eapply (rpre_weaken_rule (λ '(h₀, h₁), r_ud_pre pp (h₀, h₁)));
    last by move=> ? ? /= [-> ->].
  subst ys.
  simpl; simplify_linking.
  (* UGETPP: reveal the (already set) pp *)
  eapply (r_get_rhs_pin (ud_pp_loc (thf_chain P)) (Some pp));
    first by move=> ? ? [].
  simpl.
  eapply (r_put_rhs_pre ud_rev_loc true _
    (λ '(h₀, h₁), heap_ignore LL (h₀, h₁))).
  { move=> h₀ h₁ [hig _ _].
    by apply: heap_ignore_set_r hig; apply: fhas_in; fmap_solve. }
  rewrite rud_sig_real.
  do 3 apply r_put_vs_put.
  apply r_ret => h₀ h₁
    [a1 [[a2 [[a3 [[a4 [[a5 [[a6 [hig ->]] ->]] ->]] ->]] ->]] ->]].
  split; first by [].
  split; first split; first split; first split; first split; first split.
  - apply: heap_ignore_set_l; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_r; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_l; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_r; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_l; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_r; first by apply: fhas_in; fmap_solve.
    exact: hig.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by rewrite get_set_heap_neq // get_set_heap_neq // get_set_heap_eq.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by rewrite get_set_heap_neq // get_set_heap_eq.
  - by rewrite !rel_app_cons /= !get_set_heap_eq.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by [].
- destruct arg as [m sg].
  ssprove_code_simpl; simpl.
  ud_remember_rel pko 5%N.
  rewrite code_link_assertD.
  ssprove_sync => hpko.
  simpl.
  ud_remember_rel log 4%N.
  ssprove_forget_all.
  case: b => /=; by apply r_ret.
Qed.

Lemma Rw_ideal_perfect (b : bool) (s : nat) (hsw : (s < (wcp_w P).-1)%nat) :
  perfect (I_KOTS (shrincs_wots_scheme P)) (HGw s.+1 b) (R_ud b s ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ invR).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  ud_remember_rel pko 5%N.
  rewrite code_link_assertD.
  ssprove_sync => hpko.
  ssprove_code_simpl; simpl; simplify_linking.
  case: pko hpko => [a|] //= _.
  (* UCOLLQ pin: pp is still unset, gets sampled here *)
  eapply (r_get_rhs_pin (ud_pp_loc (thf_chain P)) None).
  { move=> s₀ s₁ [[hbase hrl] hrr].
    case: hbase => [[[[[[hig hcc1] hcc2] hcc3] hcr1] hcr2] hcr3].
    move: hcr1; rewrite !rel_app_cons /= => hcr1.
    move: hrr; rewrite /rem_inv /= => hrr.
    exact: hcr1 hrr. }
  rewrite !bind_assoc; simpl.
  eapply r_scheme_bind; [exact _|] => pp.
  apply r_put_rhs.
  (* enter the grinding loop under the loop precondition *)
  eapply (rpre_weaken_rule (λ '(s₀, s₁), r_ud_pre_t pp [::] (s₀, s₁)));
    last first.
  { move=> s₀ s₁ [s₁' [hh e]]; subst s₁.
    case: hh => [[hbase hrl] hrr].
    case: hbase => [[[[[[hig hcc1] hcc2] hcc3] hcr1] hcr2] hcr3].
    move: hcr2 hcr3; rewrite !rel_app_cons /= => hcr2 hcr3.
    move: hrr; rewrite /rem_inv /= => hrr.
    split; first split.
    - by apply: heap_ignore_set_r hig; apply: fhas_in; fmap_solve.
    - exact: get_set_heap_eq.
    - rewrite get_set_heap_neq //; exact: hcr2 hrr.
    - rewrite get_set_heap_neq //; exact: hcr3 hrr. }
  rewrite code_link_bind.
  (* explicit bit and pp, as on the real side *)
  eapply (r_grind_all false pp).
  { by move=> s₀ s₁ [[_ h _] _]. }
  cbv beta.
  rewrite code_link_assertD !(intermediates.cp_pick_map P).
  (* refine, not eapply: in this goal shape clenv unification fails
     but elaboration succeeds *)
  refine (r_assertD _ _ _ _ _ _ _ _).
  { by move=> ? _; case: ((find_counter P) pp m). }
  move=> e₀ _.
  move: e₀; case E: ((find_counter P) pp m) => [c|] /= e₀; last by [].
  rewrite code_link_bind.
  eapply r_bind.
  { apply: r_rw_loop_ideal_l => //.
    by rewrite size_rev size_digits_w. }
  move=> xs ys.
  eapply rpre_hypothesis_rule => s₀ s₁ [[hpre hsz] hys].
  eapply (rpre_weaken_rule (λ '(h₀, h₁), r_ud_pre pp (h₀, h₁)));
    last by move=> ? ? /= [-> ->].
  subst ys.
  simpl; simplify_linking.
  (* UGETPP: reveal the (already set) pp *)
  eapply (r_get_rhs_pin (ud_pp_loc (thf_chain P)) (Some pp));
    first by move=> ? ? [].
  simpl.
  eapply (r_put_rhs_pre ud_rev_loc true _
    (λ '(h₀, h₁), heap_ignore LL (h₀, h₁))).
  { move=> h₀ h₁ [hig _ _].
    by apply: heap_ignore_set_r hig; apply: fhas_in; fmap_solve. }
  rewrite rud_sig_ideal.
  do 3 apply r_put_vs_put.
  apply r_ret => h₀ h₁
    [a1 [[a2 [[a3 [[a4 [[a5 [[a6 [hig ->]] ->]] ->]] ->]] ->]] ->]].
  split; first by [].
  split; first split; first split; first split; first split; first split.
  - apply: heap_ignore_set_l; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_r; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_l; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_r; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_l; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_r; first by apply: fhas_in; fmap_solve.
    exact: hig.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by rewrite get_set_heap_neq // get_set_heap_neq // get_set_heap_eq.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_eq.
    by rewrite get_set_heap_neq // get_set_heap_eq.
  - by rewrite !rel_app_cons /= !get_set_heap_eq.
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by [].
  - rewrite !rel_app_cons /= get_set_heap_neq // get_set_heap_neq //
            get_set_heap_eq.
    by [].
- destruct arg as [m sg].
  ssprove_code_simpl; simpl.
  ud_remember_rel pko 5%N.
  rewrite code_link_assertD.
  ssprove_sync => hpko.
  simpl.
  ud_remember_rel log 4%N.
  ssprove_forget_all.
  case: b => /=; by apply r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The telescope *)

(** THE deliverable: for either KFORGE-bit [b], the distance between
    the position-0-rooted game [G_forge_sampledkey b] and the digest-re-rooted game
    [G_forge_uniformchains b] is bounded by [w - 2] SM-UD distinguishing advantages,
    one per hybrid step, each through the reduction [R_ud b s]. *)
Lemma UDw_telescope (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A) :
  (Adv (G_forge_sampledkey P b)
       (G_forge_uniformchains P b) A
     <= \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud b s))%R.
Proof.
(* The position [s] queried by the hybrid at index [s] is in range
   [s < w.-1]: the telescope runs [s] over [0 .. w.-2), and [w.-2 < w.-1]
   (both from [Hw : 1 < w]).  These bounds feed [Rw_*_perfect]'s
   [s < w.-1] side condition (needed by the exact chain tweak). *)
have hw1 : (0 < (wcp_w P).-1)%nat by case: (wcp_w P) (wcp_Hw P) => [|[|w']].
have hw2 : ((wcp_w P).-2 < (wcp_w P).-1)%nat by case: (wcp_w P) (wcp_Hw P) => [|[|w']].
have hperf0 : perfect (I_KOTS (shrincs_wots_scheme P))
    (G_forge_sampledkey P b)
    ((R_ud b 0 ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true)%sep).
{ exact: perfect_trans (G_forge_sampledkey_Hw0 b) (Rw_real_perfect b 0 hw1). }
have hperfw : perfect (I_KOTS (shrincs_wots_scheme P))
    (G_forge_uniformchains P b)
    ((R_ud b (wcp_w P).-2 ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true)%sep).
{ exact: perfect_trans (G_forge_uniformchains_Hww b) (Rw_real_perfect b (wcp_w P).-2 hw2). }
have hadj : forall s : nat, s < (wcp_w P).-2 ->
    perfect (I_KOTS (shrincs_wots_scheme P))
      ((R_ud b s ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) false)%sep)
      ((R_ud b s.+1 ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true)%sep).
{ move=> s hs2.
  exact: perfect_trans (perfect_sym (Rw_ideal_perfect b s (ltn_trans hs2 hw2)))
           (Rw_real_perfect b s.+1 (leq_ltn_trans hs2 hw2)). }
have h := Adv_hybrid_dep (n := (wcp_w P).-2)
  (Multi := fun b' => if b'
            then as_nom (G_forge_sampledkey P b)
            else as_nom (G_forge_uniformchains P b))
  (Game := fun s b' => (R_ud b s ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) b')%sep)
  (A := A) hperf0 hperfw hadj.
have -> : (\sum_(0 <= s < (wcp_w P).-2) AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud b s)
  = \sum_(0 <= s < (wcp_w P).-2)
      AdvOf (λ b' : bool, (R_ud b s ∘ SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P) b')%sep) A)%R.
{ by apply: eq_big_nat => s _; rewrite Adv_reduction. }
exact: h.
Qed.

End WOTSCUDHop.
