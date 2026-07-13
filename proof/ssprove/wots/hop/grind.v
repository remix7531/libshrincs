(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.grind

    The S-TCR(Prop) grinding hop of the WOTS+C one-time security
    proof: the FIRST split of the forgery analysis at
    [G_forge_uniformchains], nulling the grinding-collision case
    (case 1 / GRIND of [analysis.shrincs_wots_forgery_classify]).
    Delivered:

      [R_grind_real  : perfect (I_KOTS (shrincs_wots_scheme P))
                            (G_forge_uniformchains P true)
                            (R_grind ∘ STCRP_game (thf_grind P) (coll_grind P) ... true)]
      [R_grind_ideal : perfect (I_KOTS (shrincs_wots_scheme P))
                            (intermediates.G_post_grind P)
                            (R_grind ∘ STCRP_game ... false)]

    where [intermediates.G_post_grind P] is [G_forge_uniformchains]-real
    with KFORGE answering false exactly on the GRIND case — i.e. when the
    forgery's recomputed digest equals the signed digest AS DIGIT VECTORS
    ([digest_of P pp mstar cstar == digest_of P pp m c]); the next hop
    (Sec.wots.hop.compress) continues from [G_post_grind].
    Hence [Adv (G_forge_uniformchains P true) (G_post_grind P) <=
    AdvOf (STCRP_game ... 1) (A ∘ R_grind)] by the standard reduction
    steps at the consumer.

    ** Design

    - ONE SQUERY, in-oracle grinding: COMMIT makes the single query
      [SQUERY (encode_tweak P (grind_adrs P), m)].  The STCRP oracle
      itself runs the bounded counter search and ABORTS ([#assert false])
      exactly when the search fails — by [games.grind_search_find_ctr] the
      oracle's search IS the scheme's [find_counter], so the abort event
      coincides with [G_forge_uniformchains]'s grinding assert
      [#assert (isSome (find_counter P pp m))], and the returned counter is
      the signed one.  Budget p = 1.
    - SQUERY hides pp, so COMMIT calls SGETPP directly AFTER the
      single query (no more queries are needed; this flips the STCRP
      phase, so KFORGE makes no SGETPP call).  The digest is decoded
      from the SQUERY answer ([digits_w w chain_count res.1] = the signed digit
      vector, [digest_resE]); the per-chain re-rooted sampling
      ([sample_sig_roots] at [Fw P]) and the pk compression are then
      pure/local, exactly [G_forge_uniformchains]'s COMMIT tail.
    - KFORGE: getSome pk, read log, getSome the stored (sigs, ctr);
      [v := verify && freshness]; if [~~ v] ret false; otherwise the
      GRIND discriminant [digest_of P pp mstar cstar == digest_of P pp m c]
      (the classifier's first split): on equality call
      [SCHECK (0, (mstar, cstar))] and return its answer, else ret
      true ([G_forge_uniformchains]'s answer; the remaining cases are
      absorbed by the later hops).
      Real side: freshness gives [mstar != m] ([notin_log_neq]) and
      [wdigest_inj] (the [grind_range P] side condition) lifts the digit
      equality to the H_grind-output collision, so SCHECK answers true
      = [G_forge_uniformchains]-real's answer.  Ideal side: SCHECK answers
      false = [G_post_grind].
      The signed message is recovered from the log by a match (M has
      no canonical inhabitant, so no [head] default; the nil branch
      is dead — the invariant gives [log = [:: m]] under a committed
      key).
    - [grind_range P] ([forall pp a x, H_grind pp a x < w ^ chain_count]) is a
      DATA-level side condition of [R_grind_real] ONLY (the ideal side
      never inspects hash values), passed as an explicit lemma
      argument (proof/STYLE.md's Honesty constraints section, "no smuggled
      assumptions"; discharged at instantiation,
      where H_grind outputs n-bit strings parsed as exactly chain_count base-w
      digits).
    - The dummy sampler [wcp_dM P : dist M] is data only (it feeds
      [thf_grind]'s dummy [th_dM] record field; no game ever samples it).

    ** Invariant

    [heap_ignore] over all ten private locations joined with ONE
    [rel_app] relation [RG]: [G_forge_uniformchains]'s (= [G_post_grind]'s)
    pk/log/sig locations mirror R's, and R's pk determines the entire STCRP
    state — None: everything initial; Some pk: there are [m, c, sg] with
    log = [:: m], stored signature (sg, c), parameter pinned to
    pk.1, ONE committed target [(encode_tweak P (grind_adrs P), (m, c))] at
    index 0, and the phase revealed.

    Locations 330-332. *)

From mathcomp.experimental_reals Require Import distr.
From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf games.stcrp toolkit.sample_seq toolkit.relational_rules.
From Model Require Import math.chain math.encoding.
From Sec.lib Require Import chain.core
  toolkit.hop_tactics.
From Sec Require Import addressing.
From Sec.wots Require Import params scheme games analysis hop.intermediates.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section GrindHop.

Context (P : wc_params).

(** The STCRP instance and its private STCRP locations, kept as
    file-local abbreviations (library-game pins at this instance). *)
Local Notation STB b :=
  (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P) (grind_enc P) (grind_prp P) (wcp_c_max P) 1 b).
Local Notation pp_loc' := (stcr_pp_loc (thf_grind P)).
Local Notation tgts_loc' := (stcr_tgts_loc (thf_grind P) (wcp_M P)).
Local Notation tws_loc' := (stcr_tws_loc (thf_grind P)).
Local Notation rev_loc' := stcr_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** The reduction package *)

(** SQUERY/SGETPP/SCHECK opsigs as committed to [I_STCRP (thf_grind P) (coll_grind P) (wcp_M P)]. *)
Definition gsqo : opsig := (SQUERY, (th_T (thf_grind P) × wcp_M P, th_N (thf_grind P) × 'nat)).
Definition ggpo : opsig := (SGETPP, ('unit, th_PP (thf_grind P))).
Definition gcko : opsig := (SCHECK, ('nat × (wcp_M P × 'nat), 'bool)).

(** R's own locations (330+, see header). *)
Definition r_grind_pk_loc := mkloc 330 (None : option (Pk (shrincs_wots_scheme P))).
Definition r_grind_log_loc := mkloc 331 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition r_grind_sig_loc := mkloc 332 (None : option (Sig (shrincs_wots_scheme P))).

(** THE reduction: plays [I_KOTS (shrincs_wots_scheme P)] using the STCRP oracles. *)
Definition R_grind : package (I_STCRP (thf_grind P) (coll_grind P) (wcp_M P)) (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap r_grind_pk_loc ; r_grind_log_loc ; r_grind_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get r_grind_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      res ← opr gsqo (encode_tweak P (grind_adrs P), m) (λ r, ret r) ;;
      pp ← opr ggpo Datatypes.tt (λ p, ret p) ;;
      sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0 (rev (digits_w (wcp_w P) (wcp_chain_count P) res.1)) ;;
      #put r_grind_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (rev (digits_w (wcp_w P) (wcp_chain_count P) res.1)) sg)) ;;
      #put r_grind_log_loc := [:: m] ;;
      #put r_grind_sig_loc := Some (sg, res.2) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (rev (digits_w (wcp_w P) (wcp_chain_count P) res.1)) sg)),
           Some (sg, res.2))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome r_grind_pk_loc ;;
      log ← get r_grind_log_loc ;;
      sgo ← getSome r_grind_sig_loc ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m sgo.2
            then opr gcko (0, (mst, sgst.2)) (λ ans, ret ans)
            else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** G_post_grind: G_forge_uniformchains-real with the GRIND case nulled

    Defined in [Sec.wots.hop.intermediates] (shared so the hops
    type-check in parallel); used under this section's [P] as
    [intermediates.G_post_grind P]. *)

(* ------------------------------------------------------------------ *)
(** ** Linked oracle bodies (resolve equations, computed once) *)

(* The SQUERY/SGETPP bodies do not depend on the real/ideal flag, so
   the whole COMMIT machinery below is parametric in [b]. *)

Lemma resolve_gsq (b : bool) (t : th_T (thf_grind P)) (m : wcp_M P) :
  resolve (STB b) gsqo (t, m) =
  (revealed ← get rev_loc' ;;
   #assert ~~ revealed ;;
   tws ← get tws_loc' ;;
   #assert (size tws < 1)%N ;;
   #assert (t \notin tws) ;;
   ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   match [seq i <- iota 0 (wcp_c_max P) | grind_prp P (th_eval (thf_grind P) pp t (grind_enc P m i))] with
   | i :: _ =>
       tgts ← get tgts_loc' ;;
       #put tgts_loc' := setm tgts (size tws) (t, (m, i)) ;;
       #put tws_loc' := rcons tws t ;;
       ret (th_eval (thf_grind P) pp t (grind_enc P m i), i)
   | [::] =>
       #assert false ;;
       ret (th_eval (thf_grind P) pp t (grind_enc P m 0), 0)
   end).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ggp (b : bool) (u : unit) :
  resolve (STB b) ggpo u =
  (ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   #put rev_loc' := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_gck (j : nat) (mc : wcp_M P) (ctr : nat) :
  resolve (STB true) gcko (j, (mc, ctr)) =
  (revealed ← get rev_loc' ;;
   #assert revealed ;;
   tgts ← get tgts_loc' ;;
   match getm tgts j with
   | Some (t0, (m0, i0)) =>
       ppo ← get pp_loc' ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← wcp_dPP P ;; #put pp_loc' := Some pp ;; ret pp
            end ;;
       ret ((mc != m0) &&
            (th_eval (thf_grind P) pp t0 (grind_enc P m0 i0) == th_eval (thf_grind P) pp t0 (grind_enc P mc ctr)))
   | None => ret false
   end).
Proof.
by simplify_linking.
Qed.

(** Ideal-side SCHECK answers false unconditionally. *)
Lemma resolve_gck_false (j : nat) (mc : wcp_M P) (ctr : nat) :
  resolve (STB false) gcko (j, (mc, ctr)) = ret false.
Proof.
by simplify_linking.
Qed.

(* Keep the package and the resolved oracle bodies folded under
   [simpl] from here on (the resolve equations above are proved). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments STCRP_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_counter : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments grind_enc : simpl never.
#[local] Arguments Sec.wots.params.decode_tweak : simpl never.

(** The SQUERY answer decodes to the signed digit vector (the [thf_grind]
    tweak evaluates the scheme's H_grind at the canonical address, by
    [decode_tweakK]-computation). *)
Lemma digest_resE (pp : wcp_PP P) (m : wcp_M P) (c : nat) :
  rev (digits_w (wcp_w P) (wcp_chain_count P) (th_eval (thf_grind P) pp (encode_tweak P (grind_adrs P)) (grind_enc P m c))) = digest_of P pp m c.
Proof. by rewrite /grind_enc th_evalE_Tgr /digest_of. Qed.

(* ------------------------------------------------------------------ *)
(** ** The invariant (header)

    THE HOP-INVARIANT TEMPLATE (shared by Grind/Compress/ChainTCR/
    ChainPRE — read this once, then only the per-hop delta below).
    Each hop's relation has the SAME skeleton:

      [/\ pko' = pko, lg' = lg, sgo' = sgo &
          match pko with
          | None   => everything initial  (* IDENTICAL in all four:
              lg = [::], sgo = None, po = None, tg = emptym,
              tw = [::], rv = false *)
          | Some pk => exists (the committed witness) , [/\ ... ] end]

    i.e. the game's pk/log/sig MIRROR the reduction's, and once a key
    is committed (Some pk) the reduction's oracle state is pinned to a
    single committed message.  Wrapped as
    [heap_ignore IGN_ ⋊ rel_app [...] R_], with two-line projection /
    injection views [*_invE]/[*_invI] (mechanically identical in every
    hop) and a block precondition [*blk] with three update lemmas
    ([_set_pp] lazy sample, [_qupd] commit a target, [_set_rev] phase
    flip).  PER-HOP DELTA (the Some-branch witness): Grind stores the
    grinding target [(encode_tweak P (grind_adrs P),(m,c))]; Compress adds
    [pk.2 = T_sf ...] and the ends target; the two chain hops store the
    re-tagged per-chain query list ([qmap_from] of [wq]-tagged
    [commit_queries]/[pre_queries]). *)

Definition IGNG : Locations :=
  [fmap forge_pk_loc P ; forge_log_loc P ; forge_sig_loc P ; r_grind_pk_loc ; r_grind_log_loc ; r_grind_sig_loc ;
        pp_loc' ; tgts_loc' ; tws_loc' ; rev_loc' ].

Definition RG (pko : option (Pk (shrincs_wots_scheme P))) (lg : seq (Msg (shrincs_wots_scheme P)))
    (sgo : option (Sig (shrincs_wots_scheme P)))
    (pko' : option (Pk (shrincs_wots_scheme P))) (lg' : seq (Msg (shrincs_wots_scheme P))) (sgo' : option (Sig (shrincs_wots_scheme P)))
    (po : option (wcp_PP P)) (tg : {fmap nat -> (th_T (thf_grind P) × (wcp_M P × 'nat))})
    (tw : seq (th_T (thf_grind P))) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
            [/\ lg = [:: m], sgo = Some (sg, c), po = Some pk.1,
                tg = setm emptym 0 (encode_tweak P (grind_adrs P), (m, c))
              & tw = [:: encode_tweak P (grind_adrs P)] /\ rv = true]
      end].

Definition grind_inv : precond :=
  heap_ignore IGNG
  ⋊ rel_app [:: (lhs, forge_pk_loc P) ; (lhs, forge_log_loc P) ; (lhs, forge_sig_loc P) ;
                (rhs, r_grind_pk_loc) ; (rhs, r_grind_log_loc) ; (rhs, r_grind_sig_loc) ;
                (rhs, pp_loc') ; (rhs, tgts_loc') ; (rhs, tws_loc') ;
                (rhs, rev_loc') ] RG.

Arguments grind_inv : simpl never.

Lemma grind_invE s0 s1 :
  grind_inv (s0, s1) ->
  heap_ignore IGNG (s0, s1) /\
  RG (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_grind_pk_loc) (get_heap s1 r_grind_log_loc) (get_heap s1 r_grind_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma grind_invI s0 s1 :
  heap_ignore IGNG (s0, s1) ->
  RG (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_grind_pk_loc) (get_heap s1 r_grind_log_loc) (get_heap s1 r_grind_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc') ->
  grind_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside COMMIT, machinery dropped)

    The heaps satisfy [heap_ignore IGNG] and the four STCRP locations
    hold exactly the given values (the committed-targets history is
    [::] or the single grinding target). *)

Definition gblk (po : option (wcp_PP P)) (rv : bool)
    (tw : seq (th_T (thf_grind P))) (tg : {fmap nat -> (th_T (thf_grind P) × (wcp_M P × 'nat))}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNG (s0, s1),
      get_heap s1 pp_loc' = po,
      get_heap s1 rev_loc' = rv,
      get_heap s1 tws_loc' = tw &
      get_heap s1 tgts_loc' = tg].

Arguments gblk : simpl never.

(** The lazy parameter sampling (put pp). *)
Lemma gblk_set_pp (pp : wcp_PP P) rv tw tg s0 s1 :
  gblk None rv tw tg (s0, s1) ->
  gblk (Some pp) rv tw tg (s0, set_heap s1 pp_loc' (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The SQUERY state update (put tgts; put tws). *)
Lemma gblk_qupd (pp : wcp_PP P) (m : wcp_M P) (c : nat) s0 s1 :
  gblk (Some pp) false [::] emptym (s0, s1) ->
  gblk (Some pp) false [:: encode_tweak P (grind_adrs P)] (setm emptym 0 (encode_tweak P (grind_adrs P), (m, c)))
    (s0, set_heap (set_heap s1 tgts_loc' (setm emptym 0 (encode_tweak P (grind_adrs P), (m, c))))
           tws_loc' [:: encode_tweak P (grind_adrs P)]).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

(** The phase flip (SGETPP's put rev). *)
Lemma gblk_set_rev (po : option (wcp_PP P)) tw tg s0 s1 :
  gblk po false tw tg (s0, s1) ->
  gblk po true tw tg (s0, set_heap s1 rev_loc' true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The common COMMIT tail

    Both sides sample the re-rooted chains at the signed digest and
    store key/log/signature; the invariant is re-established from the
    final block state.  Parametric in nothing oracle-side: by this
    point all STCRP interaction is over. *)

Lemma r_commit_tail (pp : wcp_PP P) (m : wcp_M P) (c : nat) :
  ⊢ ⦃ λ '(s0, s1),
        gblk (Some pp) true [:: encode_tweak P (grind_adrs P)] (setm emptym 0 (encode_tweak P (grind_adrs P), (m, c)))
          (s0, s1) ⦄
     (sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put forge_pk_loc P := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc P := [:: m] ;;
      #put forge_sig_loc P := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c)))
   ≈ (sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put r_grind_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put r_grind_log_loc := [:: m] ;;
      #put r_grind_sig_loc := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ grind_inv (s0, s1) ⦄.
Proof.
eapply r_scheme_bind; first exact: sample_sig_roots_valid.
move=> sg.
eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
do 6 (case: hpre => ? [hpre ->]).
case: hpre => hign hpp hrev htws htgts.
split; first by [].
apply: grind_invI.
- do 3 (apply: heap_ignore_set_l; first by rewrite mem_domm).
  do 3 (apply: heap_ignore_set_r; first by rewrite mem_domm).
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists m, c, sg; split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence *)

Lemma R_grind_real (Hrange : grind_range P) :
  perfect (I_KOTS (shrincs_wots_scheme P)) (G_forge_uniformchains P true)
          (R_grind ∘ STCRP_game (thf_grind P) (coll_grind P) (wcp_M P) (grind_enc P) (grind_prp P) (wcp_c_max P) 1 true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ grind_inv).
{ rewrite /grind_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), gblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/grind_invE: hinv => hign hRG.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRG => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the single SQUERY: the oracle performs the grinding *)
  rewrite (resolve_gsq true (encode_tweak P (grind_adrs P)) m).
  eapply (r_get_bind_rhs rev_loc' false).
    { by move=> s0 s1 [_ _ h _ _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs tws_loc' [::]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (gblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  (* the in-oracle search is find_counter: split on its outcome *)
  have hfc := grind_search_find_ctr P pp m.
  case E: [seq i <- iota 0 (wcp_c_max P) | grind_prp P (th_eval (thf_grind P) pp (encode_tweak P (grind_adrs P)) (grind_enc P m i))]
    => [|c crest]; rewrite E /= in hfc.
  + (* grinding failure: both sides abort *)
    rewrite -hfc /=.
    exact: r_fail_bind_rhs.
  + (* grinding success at the signed counter c *)
    rewrite -hfc /=.
    eapply (r_get_rhs_known tgts_loc' emptym).
      { by move=> s0 s1 [_ _ _ _ h]. }
    eapply r_put2_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_qupd pp m c _ _ hpre). }
    rewrite (resolve_ggp true Datatypes.tt).
    eapply (r_get_bind_rhs pp_loc' (Some pp)).
      { by move=> s0 s1 [_ h _ _ _]. }
    cbv beta iota.
    simpl.
    eapply r_put_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_set_rev _ _ _ _ _ hpre). }
    rewrite (code_link_bind (sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0
              (rev (digits_w (wcp_w P) (wcp_chain_count P) (th_eval (thf_grind P) pp (encode_tweak P (grind_adrs P)) (grind_enc P m c)))))).
    rewrite (code_link_scheme _ _ _ _
              (sample_sig_roots_valid (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) emptym _ pp 0 _)).
    rewrite !digest_resE.
    exact: r_commit_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/grind_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_rhs => sgov.
  eapply (r_fact (exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
            lg = [:: m] /\ sgov = Some (sg, c))).
    { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
      case/grind_invE: hinv => _ [_ _ e3 hmatch].
      rewrite /rem_inv /= in h1 h2 h3 h4 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ _ _]]].
      exists mm, cc, sgg; split.
      - by rewrite -h3.
      - by rewrite -h5 e3. }
  move=> [m [c [sg [hlg hsgov]]]].
  rewrite hlg hsgov /=.
  case E0: (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[hinv _] _] _] _] _].
  + case/andP: (E0) => _ hfresh.
    case E1: ((digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m c)%B); last first.
    * (* non-GRIND cases: both sides answer true *)
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[hinv _] _] _] _] _].
    * (* GRIND: SCHECK answers true = G_forge_uniformchains-real's verdict *)
      simpl.
      rewrite (resolve_gck 0 mst sgst.2).
      eapply (r_get_bind_rhs rev_loc' true).
        { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
          case/grind_invE: hinv => _ [_ _ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => mm [cc [sgg [_ _ _ _ [_ hrv]]]]. }
      cbv beta.
      eapply r_bind_assertD_rhs; first by [].
      move=> _.
      eapply r_get_remember_rhs => tg.
      eapply (r_fact (tg = setm emptym 0 (encode_tweak P (grind_adrs P), (m, c)))).
        { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
          case/grind_invE: hinv => _ [_ _ e3 hmatch].
          rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6.
          rewrite h1 in hmatch.
          case: hmatch => mm [cc [sgg [hA hB _ hC _]]].
          have emm : mm = m.
            { have : [:: mm] = [:: m] by rewrite -hA h3.
              by case. }
          have ecc : cc = c.
            { have : Some (sgg, cc) = Some (sg, c).
              { by rewrite -hB -e3 h5. }
              by case. }
          by rewrite -h6 hC emm ecc. }
      move=> htg.
      rewrite htg setmE /=.
      eapply (r_get_rhs_known pp_loc' (Some pk.1)).
        { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
          case/grind_invE: hinv => _ [_ _ _ hmatch].
          rewrite /rem_inv /= in h1.
          rewrite h1 in hmatch.
          by case: hmatch => mm [cc [sgg [_ _ hpo _ _]]]. }
      simpl.
      have hne : mst != m := notin_log_neq P m mst hfresh.
      have hcol := wdigest_inj P pk.1 mst sgst.2 m c Hrange (eqP E1).
      rewrite /grind_enc !th_evalE_Tgr hne hcol eqxx /=.
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence *)

Lemma R_grind_ideal :
  perfect (I_KOTS (shrincs_wots_scheme P)) (intermediates.G_post_grind P)
          (R_grind ∘ STCRP_game (thf_grind P) (coll_grind P) (wcp_M P) (grind_enc P) (grind_prp P) (wcp_c_max P) 1 false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ grind_inv).
{ rewrite /grind_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (the SQUERY/SGETPP bodies
     and the COMMIT tail are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), gblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/grind_invE: hinv => hign hRG.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRG => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_gsq false (encode_tweak P (grind_adrs P)) m).
  eapply (r_get_bind_rhs rev_loc' false).
    { by move=> s0 s1 [_ _ h _ _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs tws_loc' [::]).
    { by move=> s0 s1 [_ _ _ h _]. }
  cbv beta.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (gblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  have hfc := grind_search_find_ctr P pp m.
  case E: [seq i <- iota 0 (wcp_c_max P) | grind_prp P (th_eval (thf_grind P) pp (encode_tweak P (grind_adrs P)) (grind_enc P m i))]
    => [|c crest]; rewrite E /= in hfc.
  + rewrite -hfc /=.
    exact: r_fail_bind_rhs.
  + rewrite -hfc /=.
    eapply (r_get_rhs_known tgts_loc' emptym).
      { by move=> s0 s1 [_ _ _ _ h]. }
    eapply r_put2_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_qupd pp m c _ _ hpre). }
    rewrite (resolve_ggp false Datatypes.tt).
    eapply (r_get_bind_rhs pp_loc' (Some pp)).
      { by move=> s0 s1 [_ h _ _ _]. }
    cbv beta iota.
    simpl.
    eapply r_put_rhs_weak.
      { move=> s0 s1 hpre; exact: (gblk_set_rev _ _ _ _ _ hpre). }
    rewrite (code_link_bind (sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0
              (rev (digits_w (wcp_w P) (wcp_chain_count P) (th_eval (thf_grind P) pp (encode_tweak P (grind_adrs P)) (grind_enc P m c)))))).
    rewrite (code_link_scheme _ _ _ _
              (sample_sig_roots_valid (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) emptym _ pp 0 _)).
    rewrite !digest_resE.
    exact: r_commit_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/grind_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/grind_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  sync_eq sgol sgov.
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/grind_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/grind_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ _ _]]].
      exists mm, cc, sgg; split.
      - by rewrite -h3.
      - by rewrite -h5. }
  move=> [m [c [sg [hlg hsgol]]]].
  rewrite hlg hsgol /=.
  case E0: (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + apply r_ret => s0 s1 hpre; split=> //.
    by case: hpre => [[[[[[hinv _] _] _] _] _] _].
  + case E1: ((digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m c)%B); last first.
    * apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
    * (* GRIND: ideal SCHECK answers false = G_post_grind's null *)
      simpl.
      rewrite (resolve_gck_false 0 mst sgst.2).
      apply r_ret => s0 s1 hpre; split=> //.
      by case: hpre => [[[[[[hinv _] _] _] _] _] _].
Qed.

End GrindHop.
