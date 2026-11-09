(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.hop.chain_tcr

    The SM-TCR(F) chain hop, [G_post_compress -> G_post_chain]: the reduction [R_chain_tcr]
    routes G_post_compress's KFORGE chain-collision case to an SM-TCR(F) CHECK and
    is perfect on both sides of the SM-TCR pair ([R_chain_tcr_real],
    [R_chain_tcr_ideal]).  The shared chain substrate (context, tweak
    notations, the forgery bridge lemmas) lives in
    [Shrincs.internal.ssprove.hop.chain_common], and the shared intermediate games
    (including the endpoint [G_post_chain]) in [Shrincs.internal.ssprove.hop.intermediates]; this
    file is the SM-TCR half built over that substrate. *)

From mathcomp.experimental_reals Require Import distr.
From Shrincs.internal.ssprove.lib Require Import prelude sig.scheme sig.kots
  games.thf games.smtcr games.smpre toolkit.sample_seq toolkit.relational_rules
  toolkit.hop_tactics.
From Shrincs.internal.common Require Import math.chain math.encoding.
From Shrincs.internal.ssprove.lib Require Import chain.core.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import scheme games analysis
  hop.intermediates.
From Shrincs.internal.ssprove.wots Require Import hop.chain_common.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Section ChainTCR.

(** Same section context as Shrincs.internal.ssprove.games minus the dummy message
    sampler [dM] (only [thf_grind] needs it). *)
Context (P : wc_params).

(** Library-game pins at this file's SM-TCR instance ([thf_chain P] /
    [coll_chain P]) and its oracle locations. *)
Local Abbreviation SMT b :=
  (SMTCR_game (thf_chain P) (coll_chain P) (tcr_budget (wcp_chain_count P) (wcp_w P)) b).
Local Abbreviation tpp_loc := (tcr_pp_loc (thf_chain P)).
Local Abbreviation ttgts_loc := (tcr_tgts_loc (thf_chain P)).
Local Abbreviation ttws_loc := (tcr_tws_loc (thf_chain P)).
Local Abbreviation trev_loc := tcr_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the re-tagging into encoded tweaks

    The chain bookkeeping lists ([commit_queries], [pre_queries]) live
    over abstract (chain, position) tweaks; the SM-TCR game on
    [thf_chain] stores ENCODED addresses ([chain_common.wq] re-tags one
    committed entry; positions are untouched). *)

Local Abbreviation qentry := ((nat * nat) * wcp_N P)%type.

(* ================================================================== *)
(** ** The SM-TCR(F) hop (G_post_compress -> G_post_chain) *)

(* ------------------------------------------------------------------ *)
(** *** The oracle-routed loops *)

(** COLLQ/TQUERY/GETPP/CHECK opsigs as committed to [I_SMTCR TF CF]. *)
Definition ct_cqo : opsig := (COLLQ, (tc_T (coll_chain P) × tc_M (coll_chain P), tc_N (coll_chain P))).
Definition ct_tqo : opsig := (TQUERY, (th_T (thf_chain P) × th_M (thf_chain P), th_N (thf_chain P))).
Definition ct_gpo : opsig := (GETPP, ('unit, th_PP (thf_chain P))).
Definition ct_cko : opsig := (CHECK, ('nat × th_M (thf_chain P), 'bool)).

(** The grinding loop: one COLLQ (H_grind member, [inr]) per counter;
    returns the answer list ([cp_grind] of Shrincs.internal.ssprove.hop.compress at
    [coll_chain]). *)
Fixpoint ct_grind (m : (wcp_M P)) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr ct_cqo ((encode_tweak P (grind_adrs P)), inr (m, c))
        (λ r,
           hs ← ct_grind m cs' ;;
           ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance ct_grind_valid (L : Locations) (m : (wcp_M P)) (cs : seq nat) :
  ValidCode L (I_SMTCR (thf_chain P) (coll_chain P)) (ct_grind m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n]
    steps, one TQUERY per step at the encoded chain address; returns
    the value at [k + n] (the oracle-routed walk at encoded
    tweaks). *)
Fixpoint ct_walk (i k n : nat) (x : (wcp_N P)) : raw_code (wcp_N P) :=
  if n is n'.+1
  then opr ct_tqo (chain_tweak P i k, x) (λ y, ct_walk i k.+1 n' y)
  else ret x.

#[local] Instance ct_walk_valid (L : Locations) i k n (x : (wcp_N P)) :
  ValidCode L (I_SMTCR (thf_chain P) (coll_chain P)) (ct_walk i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> y; exact: IH.
Qed.

(** All chains from index [st] with digits [ds]: per chain, sample
    the root LOCALLY, sigma TQUERY (positive digits), walk upward;
    returns (signature values, completed ends) — the targets are
    committed PER CHAIN in [commit_queries]' interleaved order. *)
Fixpoint ct_chains (st : nat) (ds : seq nat) :
    raw_code (chList (wcp_N P) × chList (wcp_N P)) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← (wcp_dN P) ;;
      s ← (if d is d'.+1 then opr ct_tqo (chain_tweak P st d', u) (λ y, ret y) else ret u) ;;
      e ← ct_walk st d ((wcp_w P).-1 - d) s ;;
      '(ss, es) ← ct_chains st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance ct_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMTCR (thf_chain P) (coll_chain P)) (ct_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by fmap_solve.
    move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: ct_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

(** R's own locations (350+, see header). *)
Definition r_chain_tcr_pk_loc := mkloc 350 (None : option (Pk (shrincs_wots_scheme P))).
Definition r_chain_tcr_log_loc := mkloc 351 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition r_chain_tcr_sig_loc := mkloc 352 (None : option (Sig (shrincs_wots_scheme P))).

(** THE reduction: plays [I_KOTS WC] using the SM-TCR oracles. *)
Definition R_chain_tcr : package (I_SMTCR (thf_chain P) (coll_chain P)) (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap r_chain_tcr_pk_loc ; r_chain_tcr_log_loc ; r_chain_tcr_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get r_chain_tcr_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr ct_cqo ((encode_tweak P (grind_adrs P)), inr (m, 0)) (λ r, ret r) ;;
      hs ← ct_grind m (iota 0 (wcp_c_max P)) ;;
      #assert (isSome ((intermediates.cp_pick P) hs)) ;;
      let c := (odflt (0, 0) ((intermediates.cp_pick P) hs)).1 in
      let d := rev (digits_w (wcp_w P) (wcp_chain_count P) (odflt (0, 0) ((intermediates.cp_pick P) hs)).2) in
      '(sgs, ends) ← ct_chains 0 d ;;
      pp ← opr ct_gpo Datatypes.tt (λ p, ret p) ;;
      #put r_chain_tcr_pk_loc := Some (pp, (wcp_T_sf P) pp (pk_adrs P) ends) ;;
      #put r_chain_tcr_log_loc := [:: m] ;;
      #put r_chain_tcr_sig_loc := Some (sgs, c) ;;
      ret ((pp, (wcp_T_sf P) pp (pk_adrs P) ends), Some (sgs, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome r_chain_tcr_pk_loc ;;
      log ← get r_chain_tcr_log_loc ;;
      sgo ← getSome r_chain_tcr_sig_loc ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if (shrincs_wots_verify P) pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if (digest_of P) pk.1 mst sgst.2 == (digest_of P) pk.1 m sgo.2
            then ret false
            else
              if (complete_ends P) pk.1 ((digest_of P) pk.1 mst sgst.2) sgst.1
                 != (complete_ends P) pk.1 ((digest_of P) pk.1 m sgo.2) sgo.1
              then ret false
              else
                match (wtcr_dec P) pk.1 ((digest_of P) pk.1 m sgo.2)
                        ((digest_of P) pk.1 mst sgst.2) sgo.1 sgst.1 with
                | Some ju => opr ct_cko ju (λ ans, ret ans)
                | None => ret true
                end
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies (resolve equations, computed once) *)

Lemma resolve_ct_cq (b : bool) (t : tc_T (coll_chain P)) (x : tc_M (coll_chain P)) :
  resolve (SMT b) ct_cqo (t, x) =
  (ppo ← get tpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← (wcp_dPP P) ;; #put tpp_loc := Some pp ;; ret pp
        end ;;
   ret (tc_eval (coll_chain P) pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ct_tq (b : bool) (t : th_T (thf_chain P)) (x : th_M (thf_chain P)) :
  resolve (SMT b) ct_tqo (t, x) =
  (revealed ← get trev_loc ;;
   #assert ~~ revealed ;;
   tws ← get ttws_loc ;;
   #assert (size tws < tcr_budget (wcp_chain_count P) (wcp_w P))%N ;;
   #assert (t \notin tws) ;;
   tgts ← get ttgts_loc ;;
   #put ttgts_loc := setm tgts (size tws) (t, x) ;;
   #put ttws_loc := rcons tws t ;;
   ppo ← get tpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← (wcp_dPP P) ;; #put tpp_loc := Some pp ;; ret pp
        end ;;
   ret (th_eval (thf_chain P) pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ct_gp (b : bool) (u : unit) :
  resolve (SMT b) ct_gpo u =
  (ppo ← get tpp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← (wcp_dPP P) ;; #put tpp_loc := Some pp ;; ret pp
        end ;;
   #put trev_loc := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_ct_ck (j : nat) (x : th_M (thf_chain P)) :
  resolve (SMT true) ct_cko (j, x) =
  (revealed ← get trev_loc ;;
   #assert revealed ;;
   tgts ← get ttgts_loc ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get tpp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← (wcp_dPP P) ;; #put tpp_loc := Some pp ;; ret pp
            end ;;
       ret ((x != m0) && (th_eval (thf_chain P) pp t0 x == th_eval (thf_chain P) pp t0 m0))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side CHECK enforces the reveal phase and then answers false. *)
Lemma resolve_ct_ck_false (j : nat) (x : th_M (thf_chain P)) :
  resolve (SMT false) ct_cko (j, x) =
  (revealed ← get trev_loc ;;
   #assert revealed ;;
   ret false).
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the package, the resolved oracle bodies, the pure layer and
   the KFORGE discriminants folded under [simpl] from here on. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments SMPRE_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_counter : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments Shrincs.internal.ssprove.wots.params.decode_tweak : simpl never.
#[local] Arguments intermediates.cp_pick : simpl never.
#[local] Arguments tcr_decision : simpl never.
#[local] Arguments pre_decision : simpl never.

(** Conversion bridge ([Shrincs.internal.ssprove.hop.chain_common.ct_collq_H_E]): the COLLQ
    answer at the grinding address, post-processed by the loop's
    [inr]-projection, IS the scheme's H_grind output. *)

(* ------------------------------------------------------------------ *)
(** *** The invariant (header)

    Follows the hop-invariant template (see [Shrincs.internal.ssprove.hop.grind]); the
    Some-branch delta here stores the per-chain committed query list
    [qmap_from 0 [seq wq q | q <- commit_queries ...]]. *)

Definition IGNT : Locations :=
  [fmap (forge_pk_loc P) ; (forge_log_loc P) ; (forge_sig_loc P) ; r_chain_tcr_pk_loc ; r_chain_tcr_log_loc ;
        r_chain_tcr_sig_loc ; tpp_loc ; ttgts_loc ; ttws_loc ; trev_loc ].

Definition RT (pko : option (Pk (shrincs_wots_scheme P))) (lg : seq (Msg (shrincs_wots_scheme P)))
    (sgo : option (Sig (shrincs_wots_scheme P)))
    (pko' : option (Pk (shrincs_wots_scheme P))) (lg' : seq (Msg (shrincs_wots_scheme P))) (sgo' : option (Sig (shrincs_wots_scheme P)))
    (po : option (wcp_PP P)) (tg : {fmap nat -> (th_T (thf_chain P) × th_M (thf_chain P))})
    (tw : seq (th_T (thf_chain P))) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : (wcp_M P)) (c : nat) (us : seq (wcp_N P)),
            [/\ lg = [:: m],
                sgo = Some ((wsigs P) pk.1 0 ((digest_of P) pk.1 m c) us, c),
                po = Some pk.1,
                size us = (wcp_chain_count P) /\ (good_counter P) pk.1 m c
              & [/\ tg = qmap_from 0
                          [seq (chain_common.wq P) q | q <- (wcommitq P) pk.1 0 ((digest_of P) pk.1 m c) us],
                    tw = [seq (shrincs_wots_tweak P) t | t <- unzip1 ((wcommitq P) pk.1 0 ((digest_of P) pk.1 m c) us)]
                  & rv = true]]
      end].

Definition ct_inv : precond :=
  heap_ignore IGNT
  ⋊ rel_app [:: (lhs, (forge_pk_loc P)) ; (lhs, (forge_log_loc P)) ; (lhs, (forge_sig_loc P)) ;
                (rhs, r_chain_tcr_pk_loc) ; (rhs, r_chain_tcr_log_loc) ; (rhs, r_chain_tcr_sig_loc) ;
                (rhs, tpp_loc) ; (rhs, ttgts_loc) ; (rhs, ttws_loc) ;
                (rhs, trev_loc) ] RT.

Arguments ct_inv : simpl never.

Lemma ct_invE s0 s1 :
  ct_inv (s0, s1) ->
  heap_ignore IGNT (s0, s1) /\
  RT (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_chain_tcr_pk_loc) (get_heap s1 r_chain_tcr_log_loc)
     (get_heap s1 r_chain_tcr_sig_loc)
     (get_heap s1 tpp_loc) (get_heap s1 ttgts_loc) (get_heap s1 ttws_loc)
     (get_heap s1 trev_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma ct_invI s0 s1 :
  heap_ignore IGNT (s0, s1) ->
  RT (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_chain_tcr_pk_loc) (get_heap s1 r_chain_tcr_log_loc)
     (get_heap s1 r_chain_tcr_sig_loc)
     (get_heap s1 tpp_loc) (get_heap s1 ttgts_loc) (get_heap s1 ttws_loc)
     (get_heap s1 trev_loc) ->
  ct_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** *** File-local proof tactics for the two equivalence lemmas

    Both [R_chain_tcr_real] and [R_chain_tcr_ideal] repeatedly discharge
    two proof shapes.  [ct_sync_side] closes a [sync_eq] value-agreement
    side goal: peel the two just-remembered values, walk the
    variable-length remember chain back to [ct_inv], then finish from the
    RT equalities.  [ct_ret_inv] closes an [r_ret] leaf that re-establishes
    the invariant: [ct_inv] sits at the far left of the remember chain, so
    peel it out and close by assumption. *)

Local Ltac ct_sync_side :=
  intros s0 s1 hinv;
  destruct hinv as [hinv hrem1];
  destruct hinv as [hinv hrem0];
  repeat lazymatch type of hinv with
         | ct_inv _ => fail
         | _ => destruct hinv as [hinv _]
         end;
  apply ct_invE in hinv;
  destruct hinv as [_ [hpk hlg hsg _]];
  unfold rem_inv in hrem0, hrem1;
  simpl in hrem0, hrem1;
  rewrite <- hrem0, <- hrem1;
  assumption.

Local Ltac ct_ret_inv :=
  apply r_ret;
  intros s0 s1 hpre;
  split; [ reflexivity | repeat first [ assumption | destruct hpre as [hpre _] ] ].

(* ------------------------------------------------------------------ *)
(** *** The block precondition (inside COMMIT, machinery dropped)

    [Q] is the committed-so-far list over ABSTRACT (chain, position)
    tweaks; the SM-TCR heap holds its re-tagged image (the block
    precondition + the [wq] re-tagging). *)

Definition tblk (po : option (wcp_PP P)) (rv : bool) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNT (s0, s1),
      get_heap s1 tpp_loc = po,
      get_heap s1 trev_loc = rv,
      get_heap s1 ttws_loc = [seq (shrincs_wots_tweak P) t | t <- unzip1 Q] &
      get_heap s1 ttgts_loc = qmap_from 0 [seq (chain_common.wq P) q | q <- Q]].

Arguments tblk : simpl never.

(** The lazy parameter sampling (put pp, at the COLLQ pin). *)
Lemma tblk_set_pp (pp : (wcp_PP P)) rv Q s0 s1 :
  tblk None rv Q (s0, s1) ->
  tblk (Some pp) rv Q (s0, set_heap s1 tpp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The TQUERY state update (put tgts; put tws). *)
Lemma tblk_qupd (pp : (wcp_PP P)) (Q : seq qentry) (t : nat * nat) (x : (wcp_N P)) s0 s1 :
  tblk (Some pp) false Q (s0, s1) ->
  tblk (Some pp) false (rcons Q (t, x))
    (s0, set_heap (set_heap s1 ttgts_loc
            (setm (qmap_from 0 [seq (chain_common.wq P) q | q <- Q])
                  (size [seq (shrincs_wots_tweak P) t' | t' <- unzip1 Q]) ((shrincs_wots_tweak P) t, x)))
          ttws_loc (rcons [seq (shrincs_wots_tweak P) t' | t' <- unzip1 Q] ((shrincs_wots_tweak P) t))).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq /unzip1 !map_rcons.
- rewrite get_set_heap_neq // get_set_heap_eq.
  by rewrite map_rcons qmap_from_rcons add0n /unzip1 !size_map.
Qed.

(** The phase flip (GETPP's put rev). *)
Lemma tblk_set_rev (po : option (wcp_PP P)) Q s0 s1 :
  tblk po false Q (s0, s1) ->
  tblk po true Q (s0, set_heap s1 trev_loc true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked COLLQ (pp pinned: state untouched) *)

Lemma r_ctcollq_known (b : bool) {B : choiceType} (pp : (wcp_PP P))
    (t : tc_T (coll_chain P)) (x : tc_M (coll_chain P)) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : tc_N (coll_chain P) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 (tc_eval (coll_chain P) pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMT b) ct_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_ct_cq b t x).
eapply (r_get_bind_rhs tpp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: h.
Qed.

(** Grinding loop: the continuation receives the honest H_grind answer
    list. *)
Lemma r_ctgrind_spec (b : bool) {B : choiceType} (pp : (wcp_PP P)) (m : (wcp_M P))
    (cs : seq nat) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B)
    (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 [seq (wcp_H_grind P) pp (grind_adrs P) (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (code_link (ct_grind m cs) (SMT b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_ctcollq_known b).
  cbv beta.
  rewrite (chain_common.ct_collq_H_E P).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked TQUERY (pp pinned by the COLLQ pin) *)

Lemma r_ctquery_known (b : bool) {B : choiceType} (pp : (wcp_PP P))
    (i k : nat) (x : (wcp_N P)) (Q : seq qentry)
    (c0 : raw_code B) (k1 : (wcp_N P) -> raw_code B) (post : postcond B B) :
  (i < (wcp_chain_count P))%N -> (k < (wcp_w P).-1)%N ->
  all (λ t : nat * nat, (t.1 < (wcp_chain_count P))%N && (t.2 < (wcp_w P).-1)%N) (unzip1 Q) ->
  size Q < tcr_budget (wcp_chain_count P) (wcp_w P) ->
  (i, k) \notin unzip1 Q ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false (rcons Q ((i, k), x)) (s0, s1) ⦄
     c0 ≈ k1 (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (i, k) x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMT b) ct_tqo (chain_tweak P i k, x)) k1 ⦃ post ⦄.
Proof.
move=> hi hk hQr hbud hfresh h.
rewrite (resolve_ct_tq b (chain_tweak P i k) x).
eapply (r_get_bind_rhs trev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs ttws_loc [seq (shrincs_wots_tweak P) t | t <- unzip1 Q]).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map /unzip1 size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  move=> s0 s1 _; apply: ((chain_common.wtw_notin P) (i, k) (unzip1 Q) hi hk _ hfresh).
  by move=> t' /(allP hQr) /andP[h1 h2]; split.
move=> _.
eapply (r_get_bind_rhs ttgts_loc (qmap_from 0 [seq (chain_common.wq P) q | q <- Q])).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (tblk_qupd pp Q (i, k) x s0 s1 hpre).
eapply (r_get_bind_rhs tpp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
simpl.
have hkw : (k < (wcp_w P))%N.
  by apply: (ltn_trans hk); rewrite ltn_predL; apply: (ltnW (wcp_Hw P)).
rewrite ((chain_common.Fc_wtw P) pp (i, k) x hkw).
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The walk and per-chain inductions (re-tagged) *)

Lemma r_ctwalk_spec (b : bool) {B : choiceType} (pp : (wcp_PP P))
    (post : postcond B B) :
  forall n i k (x : (wcp_N P)) (Q : seq qentry) (c0 : raw_code B)
         (k1 : (wcp_N P) -> raw_code B),
  (i < (wcp_chain_count P))%N ->
  (k + n <= (wcp_w P).-1)%N ->
  all (λ t : nat * nat, (t.1 < (wcp_chain_count P))%N && (t.2 < (wcp_w P).-1)%N) (unzip1 Q) ->
  (size Q + n <= tcr_budget (wcp_chain_count P) (wcp_w P))%N ->
  all (tweak_lt i k) (unzip1 Q) ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false
         (Q ++ walkq (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp i k n x) (s0, s1) ⦄
     c0 ≈ k1 (chainc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp i x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (code_link (ct_walk i k n x) (SMT b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x Q c0 k1 hi hkn hQr hbud hfresh h.
- by move: h; rewrite cats0.
- rewrite /= bind_assoc.
  have hk : (k < (wcp_w P).-1)%N by apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
  eapply r_ctquery_known => //.
  + by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + exact: tlt_notin hfresh.
  + apply: IH => //.
    * by rewrite addSnnS.
    * rewrite /unzip1 map_rcons all_rcons hQr /=.
      by rewrite hi hk.
    * by rewrite size_rcons addSnnS.
    * rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
      -- by rewrite /tweak_lt /= ltnn eqxx ltnSn.
      -- exact: all_tlt_widen hfresh.
    * by move: h; rewrite (walkq_cons (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P)) cat_rcons.
Qed.

(** The per-chain induction: lhs [sample_sig_roots] at [FW] (the lhs
    games' sampling), rhs the linked [ct_chains]; the committed list
    grows by [commit_queries] and the results are [sigs_of]/[ends_of]
    of the sampled roots. *)
Lemma r_ctchains_spec (b : bool) {B : choiceType} (pp : (wcp_PP P))
    (post : postcond B B) :
  forall ds st (Q : seq qentry) (K0 : chList (wcp_N P) -> raw_code B)
         (K1 : chList (wcp_N P) * chList (wcp_N P) -> raw_code B),
  (st + size ds <= (wcp_chain_count P))%N ->
  all (λ d : nat, (d < (wcp_w P))%N) ds ->
  all (λ t : nat * nat, (t.1 < (wcp_chain_count P))%N && (t.2 < (wcp_w P).-1)%N) (unzip1 Q) ->
  (size Q + total_query_count (wcp_w P) ds <= tcr_budget (wcp_chain_count P) (wcp_w P))%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false
            (Q ++ (wcommitq P) pp st ds us) (s0, s1) ⦄
        K0 ((wsigs P) pp st ds us)
      ≈ K1 ((wsigs P) pp st ds us, (wends P) pp st ds ((wsigs P) pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), tblk (Some pp) false Q (s0, s1) ⦄
     bind (sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp st ds) K0
   ≈ bind (code_link (ct_chains st ds) (SMT b)) K1 ⦃ post ⦄.
Proof.
have hw0 : (0 < (wcp_w P))%N := ltnW (wcp_Hw P).
elim=> [|d ds IH] st Q K0 K1 hst hds hQr hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- move: hst => /=; rewrite addnS => hst2.
  have hstcc : (st < (wcp_chain_count P))%N := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : (st.+1 + size ds <= (wcp_chain_count P))%N := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /= code_link_bind.
  rewrite (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P))).
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* d = 0 : no sigma query, walk from the root itself.  The range
       side conditions ([st < chain_count], positions [< w.-1]) are
       [have]d into context so the [eapply .. => //] discharges them by
       assumption; only the budget / freshness / continuation goals
       remain as bullets. *)
    have hkn0 : (0 + ((wcp_w P).-1 - 0) <= (wcp_w P).-1)%N by rewrite add0n subn0.
    rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    eapply (r_ctwalk_spec b pp post ((wcp_w P).-1 - 0) st 0 u Q) => //.
    * apply: leq_trans hbud.
      by rewrite leq_add2l /total_query_count /= /chain_query_count /= leq_addr.
    * exact: all_lt_tlt.
    * rewrite (code_link_bind (ct_chains st.+1 ds)) bind_assoc.
      eapply IH => //.
      -- rewrite unzip1_cat all_cat; apply/andP; split; first exact: hQr.
         apply/allP => t ht; apply/andP; split.
         ++ by move: (allP (walkq_tweak1 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st 0 ((wcp_w P).-1 - 0) u) t ht) => /eqP ->.
         ++ exact: (allP (walkq_tweak2 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st 0 ((wcp_w P).-1 - 0) u (wcp_w P).-1 hkn0) t ht).
      -- by rewrite size_cat size_walkq -addnA.
      -- rewrite unzip1_cat all_cat; apply/andP; split.
         ++ by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ apply: sub_all (walkq_tweak1 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st 0 _ u) => t /= /eqP ->.
            exact: ltnSn.
      -- move=> us hus.
         move: (h (u :: us)); rewrite /= hus => /(_ erefl).
         by rewrite /wcommitq (commit_queries_cons (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P)) /chain_queries /= catA.
  + (* d = d'.+1 : sigma query first ([d' < w.-1] from [d = d'.+1 < w]). *)
    have hdw1 : (d'.+1 <= (wcp_w P).-1)%N by rewrite -ltnS prednK.
    have hkn1 : (d'.+1 + ((wcp_w P).-1 - d'.+1) <= (wcp_w P).-1)%N by rewrite subnKC.
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply r_ctquery_known => //.
    * apply: leq_trans hbud.
      by rewrite addnS ltnS leq_addr.
    * exact: lt_notin.
    * rewrite /= (code_link_bind (ct_walk st d'.+1 ((wcp_w P).-1 - d'.+1)
                    (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u))) bind_assoc.
      eapply (r_ctwalk_spec b pp post ((wcp_w P).-1 - d'.+1) st d'.+1
                (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u) (rcons Q ((st, d'), u))) => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstcc hdw1.
      -- rewrite size_rcons addSnnS; apply: leq_trans hbud.
         by rewrite leq_add2l /total_query_count /= /chain_query_count /= add1n addSn ltnS leq_addr.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /tweak_lt /= ltnn eqxx ltnSn.
         ++ exact: all_lt_tlt.
      -- rewrite /= (code_link_bind (ct_chains st.+1 ds)) bind_assoc.
         eapply IH => //.
         ++ rewrite unzip1_cat all_cat; apply/andP; split.
            ** rewrite /unzip1 map_rcons all_rcons hQr /=.
               by rewrite hstcc hdw1.
            ** apply/allP => t ht; apply/andP; split.
               --- by move: (allP (walkq_tweak1 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st d'.+1
                             ((wcp_w P).-1 - d'.+1) (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u)) t ht) => /eqP ->.
               --- exact: (allP (walkq_tweak2 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st d'.+1
                             ((wcp_w P).-1 - d'.+1) (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u) (wcp_w P).-1 hkn1) t ht).
         ++ rewrite size_cat size_rcons size_walkq.
            apply: leq_trans hbud.
            by rewrite addSnnS -addnA leq_add2l /total_query_count /= /chain_query_count /= add1n.
         ++ rewrite unzip1_cat all_cat /unzip1 map_rcons all_rcons.
            apply/andP; split; last first.
            ** apply: sub_all (walkq_tweak1 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st d'.+1 _ _)
                 => t /= /eqP ->.
               exact: ltnSn.
            ** apply/andP; split; first by rewrite /= ltnSn.
               by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ move=> us hus.
            move: (h (u :: us)); rewrite /= hus => /(_ erefl).
            by rewrite /wcommitq (commit_queries_cons (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P)) /chain_queries
                       cat_rcons catA.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The common COMMIT tail

    By this point all sampling and oracle interaction is over: both
    sides store key/log/signature (the same values) and return; the
    invariant is re-established from the final block state. *)

Lemma r_ct_tail (pp : (wcp_PP P)) (m : (wcp_M P)) (c : nat) (us : seq (wcp_N P)) :
  (good_counter P) pp m c -> size us = (wcp_chain_count P) ->
  ⊢ ⦃ λ '(s0, s1),
        tblk (Some pp) true ((wcommitq P) pp 0 ((digest_of P) pp m c) us) (s0, s1) ⦄
     (#put (forge_pk_loc P) := Some (pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp ((digest_of P) pp m c)
        ((wsigs P) pp 0 ((digest_of P) pp m c) us))) ;;
      #put (forge_log_loc P) := [:: m] ;;
      #put (forge_sig_loc P) := Some ((wsigs P) pp 0 ((digest_of P) pp m c) us, c) ;;
      ret ((pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp ((digest_of P) pp m c)
             ((wsigs P) pp 0 ((digest_of P) pp m c) us))),
           Some ((wsigs P) pp 0 ((digest_of P) pp m c) us, c)))
   ≈ (#put r_chain_tcr_pk_loc := Some (pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp ((digest_of P) pp m c)
        ((wsigs P) pp 0 ((digest_of P) pp m c) us))) ;;
      #put r_chain_tcr_log_loc := [:: m] ;;
      #put r_chain_tcr_sig_loc := Some ((wsigs P) pp 0 ((digest_of P) pp m c) us, c) ;;
      ret ((pp, (wcp_T_sf P) pp (pk_adrs P) ((complete_ends P) pp ((digest_of P) pp m c)
             ((wsigs P) pp 0 ((digest_of P) pp m c) us))),
           Some ((wsigs P) pp 0 ((digest_of P) pp m c) us, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ ct_inv (s0, s1) ⦄.
Proof.
move=> hgood hus.
do 3 eapply r_put_lhs.
do 3 eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hblk ->].
case: hblk => hign hpp hrev htws htgts.
split; first by [].
apply: ct_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- simplify_heap_reads.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists m, c, us; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_chain_tcr_real :
  perfect (I_KOTS (shrincs_wots_scheme P)) (intermediates.G_post_compress P) (R_chain_tcr ∘ SMTCR_game (thf_chain P) (coll_chain P) (tcr_budget (wcp_chain_count P) (wcp_w P)) true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ct_inv).
{ rewrite /ct_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_eq pko pko'.
    { ct_sync_side. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), tblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/ct_invE: hinv => hign hRT.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRT => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the COLLQ pin: SM-TCR's lazy pp is sampled here, against the
     lhs game's eager one *)
  rewrite (resolve_ct_cq true (encode_tweak P (grind_adrs P)) (inr (m, 0))).
  eapply (r_get_bind_rhs tpp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (tblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  (* the grinding loop through COLLQ *)
  rewrite (code_link_bind (ct_grind m (iota 0 (wcp_c_max P)))).
  eapply (r_ctgrind_spec true pp m).
  cbv beta.
  rewrite code_link_assertD
          (cp_pick_map P).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: ((find_counter P) pp m). }
  move=> e1 _.
  move: e1; case E: ((find_counter P) pp m) => [c|] /= e1; last by [].
  rewrite !(intermediates.digestE P).
  (* the chains: lhs re-rooted sampling, rhs TQUERY-committed walks *)
  rewrite (code_link_bind (ct_chains 0 ((digest_of P) pp m c))).
  have hszd : size ((digest_of P) pp m c) = (wcp_chain_count P)
    := size_digest_of P pp m c.
  eapply (r_ctchains_spec true pp _ ((digest_of P) pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_counter_good P pp m c E; exact: hwf. }
    { by rewrite /= (nqs_le (wcp_chain_count P) (wcp_w P) _ hszd). }
  move=> us hus.
  cbv beta iota.
  rewrite (intermediates.wendsE P pp _ _
            (size_digest_of P pp m c)).
  simpl.
  (* GETPP: reveal pp, flip the phase; then the pure pk compression *)
  rewrite (resolve_ct_gp true Datatypes.tt).
  eapply (r_get_bind_rhs tpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (tblk_set_rev _ _ _ _ hpre). }
  apply: r_ct_tail => //.
  - exact: (find_counter_good P pp m c E).
  - by rewrite hus (size_digest_of P).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  sync_eq pko pko'.
    { ct_sync_side. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { ct_sync_side. }
  move=> e; subst lg'.
  sync_eq sgol sgov.
    { ct_sync_side. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : (wcp_M P)) (c : nat) (sg : seq (wcp_N P)),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/ct_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [uss [hA hB _ _ _]]].
      exists mm, cc, ((wsigs P) pk.1 0 ((digest_of P) pk.1 mm cc) uss); split.
      - by rewrite -h3.
      - by rewrite -h5. }
  move=> [m [c [sg [hlg hsgol]]]].
  rewrite hlg hsgol /=.
  case E0: ((shrincs_wots_verify P) pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    ct_ret_inv.
  + case/andP: (E0) => hver hfresh.
    case E1: (((digest_of P) pk.1 mst sgst.2 == (digest_of P) pk.1 m c)%B).
    * (* GRIND: both games null it *)
      ct_ret_inv.
    * case E2: (((complete_ends P) pk.1 ((digest_of P) pk.1 mst sgst.2) sgst.1
                 != (complete_ends P) pk.1 ((digest_of P) pk.1 m c) sg)%B).
      -- (* COMPRESS: both games null it *)
         ct_ret_inv.
      -- (* CHAIN: run the shared classifier *)
         case E3: ((wtcr_dec P) pk.1 ((digest_of P) pk.1 m c)
                     ((digest_of P) pk.1 mst sgst.2) sg sgst.1) => [[j u]|];
           last first.
         ++ (* ChainMeet: both sides answer true *)
            ct_ret_inv.
         ++ (* ChainColl: CHECK answers true = G_post_compress's verdict *)
            simpl.
            rewrite (resolve_ct_ck j u).
            eapply (r_get_bind_rhs trev_loc true).
              { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch => mm [cc [uss [_ _ _ _ [_ _ hrv]]]]. }
            cbv beta.
            eapply r_bind_assertD_rhs; first by [].
            move=> _.
            eapply r_get_remember_rhs => tg.
            eapply (r_fact (exists us,
                      [/\ size us = (wcp_chain_count P), (good_counter P) pk.1 m c,
                          sg = (wsigs P) pk.1 0 ((digest_of P) pk.1 m c) us
                        & tg = qmap_from 0
                            [seq (chain_common.wq P) q
                            | q <- (wcommitq P) pk.1 0 ((digest_of P) pk.1 m c) us]])).
              { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
                rewrite h1 in hmatch.
                case: hmatch
                  => mm [cc [uss [hA hB _ [husz hgood] [htg _ _]]]].
                have emm : mm = m.
                  { have : [:: mm] = [:: m] by rewrite -hA h3.
                    by case. }
                rewrite emm in hB hgood htg.
                have hsgcc : Some ((wsigs P) pk.1 0 ((digest_of P) pk.1 m cc) uss, cc)
                             = Some (sg, c).
                  { by rewrite -hB h5. }
                have ecc : cc = c by case: hsgcc.
                rewrite ecc in hsgcc hgood htg.
                have esg : sg = (wsigs P) pk.1 0 ((digest_of P) pk.1 m c) uss.
                  { by case: hsgcc. }
                by exists uss; split=> //; rewrite -h7. }
            move=> [us [husz hgood hsg htg]].
            have hned := negbT E1.
            have hends : (complete_ends P) pk.1 ((digest_of P) pk.1 mst sgst.2) sgst.1
                         = (complete_ends P) pk.1 ((digest_of P) pk.1 m c)
                             ((wsigs P) pk.1 0 ((digest_of P) pk.1 m c) us).
              { by move/negbFE/eqP: E2 => ->; rewrite hsg. }
            move: (hver); rewrite /shrincs_wots_verify => /and3P[hvd' hys _].
            have hwin := (chain_common.wtcr_decisionP P) pk.1 m mst c sgst.2 us sgst.1
                           hgood husz hvd' hys hends hned.
            rewrite -hsg E3 in hwin.
            case: hwin => t [v [hqn hne hcol]].
            have hgetm : getm tg j = Some ((shrincs_wots_tweak P) t, v).
              { rewrite htg.
                have := qmap_from_get 0
                  [seq (chain_common.wq P) q | q <- (wcommitq P) pk.1 0 ((digest_of P) pk.1 m c) us] j.
                rewrite add0n => ->.
                by rewrite qnth_map hqn. }
            rewrite hgetm.
            eapply (r_get_rhs_known tpp_loc (Some pk.1)).
              { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch => mm [cc [uss [_ _ hpo _ _]]]. }
            simpl.
            rewrite ((chain_common.wcheck_bridge P) pk.1 m c us j t v u hgood husz hqn)
                    ((chain_common.wcheck_bridge P) pk.1 m c us j t v v hgood husz hqn).
            rewrite hne hcol eqxx /=.
            ct_ret_inv.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence *)

Lemma R_chain_tcr_ideal :
  perfect (I_KOTS (shrincs_wots_scheme P)) (intermediates.G_post_chain P) (R_chain_tcr ∘ SMTCR_game (thf_chain P) (coll_chain P) (tcr_budget (wcp_chain_count P) (wcp_w P)) false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ ct_inv).
{ rewrite /ct_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (all oracle bodies and loop
     specs are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_eq pko pko'.
    { ct_sync_side. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), tblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/ct_invE: hinv => hign hRT.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRT => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_ct_cq false (encode_tweak P (grind_adrs P)) (inr (m, 0))).
  eapply (r_get_bind_rhs tpp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (tblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  rewrite (code_link_bind (ct_grind m (iota 0 (wcp_c_max P)))).
  eapply (r_ctgrind_spec false pp m).
  cbv beta.
  rewrite code_link_assertD
          (cp_pick_map P).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: ((find_counter P) pp m). }
  move=> e1 _.
  move: e1; case E: ((find_counter P) pp m) => [c|] /= e1; last by [].
  rewrite !(intermediates.digestE P).
  rewrite (code_link_bind (ct_chains 0 ((digest_of P) pp m c))).
  have hszd : size ((digest_of P) pp m c) = (wcp_chain_count P)
    := size_digest_of P pp m c.
  eapply (r_ctchains_spec false pp _ ((digest_of P) pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_counter_good P pp m c E; exact: hwf. }
    { by rewrite /= (nqs_le (wcp_chain_count P) (wcp_w P) _ hszd). }
  move=> us hus.
  cbv beta iota.
  rewrite (intermediates.wendsE P pp _ _
            (size_digest_of P pp m c)).
  simpl.
  rewrite (resolve_ct_gp false Datatypes.tt).
  eapply (r_get_bind_rhs tpp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (tblk_set_rev _ _ _ _ hpre). }
  apply: r_ct_tail => //.
  - exact: (find_counter_good P pp m c E).
  - by rewrite hus (size_digest_of P).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  sync_eq pko pko'.
    { ct_sync_side. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { ct_sync_side. }
  move=> e; subst lg'.
  sync_eq sgol sgov.
    { ct_sync_side. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : (wcp_M P)) (c : nat) (sg : seq (wcp_N P)),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/ct_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [uss [hA hB _ _ _]]].
      exists mm, cc, ((wsigs P) pk.1 0 ((digest_of P) pk.1 mm cc) uss); split.
      - by rewrite -h3.
      - by rewrite -h5. }
  move=> [m [c [sg [hlg hsgol]]]].
  rewrite hlg hsgol /=.
  case E0: ((shrincs_wots_verify P) pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + ct_ret_inv.
  + case E1: (((digest_of P) pk.1 mst sgst.2 == (digest_of P) pk.1 m c)%B).
    * ct_ret_inv.
    * case E2: (((complete_ends P) pk.1 ((digest_of P) pk.1 mst sgst.2) sgst.1
                 != (complete_ends P) pk.1 ((digest_of P) pk.1 m c) sg)%B).
      -- ct_ret_inv.
      -- case E3: ((wtcr_dec P) pk.1 ((digest_of P) pk.1 m c)
                     ((digest_of P) pk.1 mst sgst.2) sg sgst.1) => [[j u]|];
           last first.
         ++ (* ChainMeet: both sides answer true *)
            ct_ret_inv.
         ++ (* ChainColl: ideal CHECK answers false = G_post_chain's null *)
            simpl.
            rewrite (resolve_ct_ck_false j u).
            eapply (r_get_bind_rhs trev_loc true).
              { move=> s0 s1 [[[[[[hinv h1] _] _] _] _] _].
                case/ct_invE: hinv => _ [_ _ _ hmatch].
                rewrite /rem_inv /= in h1.
                rewrite h1 in hmatch.
                by case: hmatch => mm [cc [uss [_ _ _ _ [_ _ hrv]]]]. }
            cbv beta.
            eapply r_bind_assertD_rhs; first by [].
            move=> _.
            ct_ret_inv.
Qed.


End ChainTCR.
