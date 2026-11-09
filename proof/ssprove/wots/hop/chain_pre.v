(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.chain_pre

    The SM-PRE(F) chain hop, [G_post_chain -> G_forge_uniformchains-ideal]: the reduction
    [R_chain_pre] routes G_post_chain's residual chain-meet case to an SM-PRE(F)
    PCHECK and is perfect on both sides of the SM-PRE pair
    ([R_chain_pre_real], [R_chain_pre_ideal]).  The shared chain substrate lives
    in [Sec.hop.chain_common]; this file is the SM-PRE half built
    over that substrate (with the shared [simpl never] directives
    re-declared locally, ahead of the proofs). *)

From mathcomp.experimental_reals Require Import distr.
From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf games.smtcr games.smpre toolkit.sample_seq toolkit.relational_rules
  toolkit.hop_tactics.
From Model Require Import math.chain math.encoding.
From Sec.lib Require Import chain.core.
From Sec Require Import addressing.
From Sec.wots Require Import addressing.
From Sec.wots Require Import scheme games analysis
  hop.intermediates.
From Sec.wots Require Import hop.chain_common.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Section ChainPRE.

(** The WOTS+C parameter record (see Sec.wots.params), as in
    Sec.wots.games. *)
Context (P : wc_params).

(** The SM-PRE game pair at this instance (a library-game pin) and the
    SM-PRE reduction's own location pins (library locations at the
    file-local [thf_chain P] instance). *)
Local Abbreviation SMP b := (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P) b).
Local Abbreviation ppp_loc := (pre_pp_loc (thf_chain P)).
Local Abbreviation ptgts_loc := (pre_tgts_loc (thf_chain P)).
Local Abbreviation ptws_loc := (pre_tws_loc (thf_chain P)).
Local Abbreviation prev_loc := pre_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the re-tagging into encoded tweaks

    The chain bookkeeping lists ([commit_queries], [pre_queries]) live
    over abstract (chain, position) tweaks; the SM-TCR/SM-PRE games on
    [thf_chain] store ENCODED addresses.  [chain_common.wq] re-tags one
    committed entry; positions are untouched, so all indices
    ([q_index], [pre_index]) are consumed unchanged. *)

Local Abbreviation qentry := ((nat * nat) * wcp_N P)%type.

(* Shared proof-shaping directives (declared once, ahead of the
   proofs). *)
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
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments intermediates.cp_pick : simpl never.
#[local] Arguments tcr_decision : simpl never.
#[local] Arguments pre_decision : simpl never.

(* ================================================================== *)
(** ** The SM-PRE(F) hop (G_post_chain -> G_forge_uniformchains-ideal) *)

(* ------------------------------------------------------------------ *)
(** *** The oracle-routed loops *)

(** PQUERY/PGETPP/PCHECK/PCOLLQ opsigs as committed to
    [I_SMPRE (thf_chain P) (coll_chain P)]. *)
Definition pr_pqo : opsig := (PQUERY, (th_T (thf_chain P), th_N (thf_chain P))).
Definition pr_gpo : opsig := (PGETPP, ('unit, th_PP (thf_chain P))).
Definition pr_cko : opsig := (PCHECK, ('nat × th_M (thf_chain P), 'bool)).
Definition pr_cqo : opsig := (PCOLLQ, (tc_T (coll_chain P) × tc_M (coll_chain P), tc_N (coll_chain P))).

(** The grinding loop through PCOLLQ ([ct_grind]'s twin). *)
Fixpoint pr_grind (m : wcp_M P) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr pr_cqo (encode_tweak P (grind_adrs P), inr (m, c))
        (λ r,
           hs ← pr_grind m cs' ;;
           ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance pr_grind_valid (L : Locations) (m : wcp_M P) (cs : seq nat) :
  ValidCode L (I_SMPRE (thf_chain P) (coll_chain P)) (pr_grind m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** All chains from index [st] with digits [ds]: positive digits make
    the sigma PQUERY at the encoded chain address (the oracle hides
    the root and answers the signature value), zero digits sample the
    value locally; returns the signature values (the oracle-routed
    per-chain loop at encoded tweaks). *)
Fixpoint pr_chains (st : nat) (ds : seq nat) : raw_code (chList (wcp_N P)) :=
  match ds with
  | [::] => ret [::]
  | d :: ds' =>
      s ← (if d is d'.+1
           then opr pr_pqo (chain_tweak P st d') (λ y, ret y)
           else (wcp_dN P : raw_code (wcp_N P))) ;;
      ss ← pr_chains st.+1 ds' ;;
      ret (s :: ss)
  end.

#[local] Instance pr_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMPRE (thf_chain P) (coll_chain P)) (pr_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind.
  + case: d => [|d'].
    * eapply valid_scheme, prog_valid.
    * eapply valid_opr; first by fmap_solve.
      move=> y; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: IH.
    move=> ss; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The reduction package *)

(** R's own locations (360+, see header). *)
Definition r_chain_pre_pk_loc := mkloc 360 (None : option (Pk (shrincs_wots_scheme P))).
Definition r_chain_pre_log_loc := mkloc 361 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition r_chain_pre_sig_loc := mkloc 362 (None : option (Sig (shrincs_wots_scheme P))).

(** THE reduction: plays [I_KOTS (shrincs_wots_scheme P)] using the SM-PRE
    oracles.  See the header for the PCOLLQ pin in COMMIT. *)
Definition R_chain_pre : package (I_SMPRE (thf_chain P) (coll_chain P)) (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap r_chain_pre_pk_loc ; r_chain_pre_log_loc ; r_chain_pre_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get r_chain_pre_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr pr_cqo (encode_tweak P (grind_adrs P), inr (m, 0)) (λ r, ret r) ;;
      hs ← pr_grind m (iota 0 (wcp_c_max P)) ;;
      #assert (isSome (intermediates.cp_pick P hs)) ;;
      let c := (odflt (0, 0) (intermediates.cp_pick P hs)).1 in
      let d := rev (digits_w (wcp_w P) (wcp_chain_count P) (odflt (0, 0) (intermediates.cp_pick P hs)).2) in
      sgs ← pr_chains 0 d ;;
      pp ← opr pr_gpo Datatypes.tt (λ p, ret p) ;;
      #put r_chain_pre_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp d sgs)) ;;
      #put r_chain_pre_log_loc := [:: m] ;;
      #put r_chain_pre_sig_loc := Some (sgs, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp d sgs)), Some (sgs, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome r_chain_pre_pk_loc ;;
      log ← get r_chain_pre_log_loc ;;
      sgo ← get r_chain_pre_sig_loc ;;
      match log, sgo with
      | m :: _, Some sgc =>
          if shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m sgc.2
            then ret false
            else
              if complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                 != complete_ends P pk.1 (digest_of P pk.1 m sgc.2) sgc.1
              then ret false
              else
                match wtcr_dec P pk.1 (digest_of P pk.1 m sgc.2)
                        (digest_of P pk.1 mst sgst.2) sgc.1 sgst.1 with
                | Some _ => ret false
                | None =>
                    match wpre_dec P pk.1 (digest_of P pk.1 m sgc.2)
                            (digest_of P pk.1 mst sgst.2) sgc.1 sgst.1 with
                    | Some jx => opr pr_cko jx (λ ans, ret ans)
                    | None => ret true
                    end
                end
          else ret false
      | _, _ => ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** *** Linked oracle bodies (resolve equations, computed once) *)

Lemma resolve_pr_cq (b : bool) (t : tc_T (coll_chain P)) (x : tc_M (coll_chain P)) :
  resolve (SMP b) pr_cqo (t, x) =
  (ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   ret (tc_eval (coll_chain P) pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pr_pq (b : bool) (t : th_T (thf_chain P)) :
  resolve (SMP b) pr_pqo t =
  (revealed ← get prev_loc ;;
   #assert ~~ revealed ;;
   tws ← get ptws_loc ;;
   #assert (size tws < wcp_chain_count P)%N ;;
   #assert (t \notin tws) ;;
   x ← wcp_dN P ;;
   tgts ← get ptgts_loc ;;
   #put ptgts_loc := setm tgts (size tws) (t, x) ;;
   #put ptws_loc := rcons tws t ;;
   ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   ret (th_eval (thf_chain P) pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pr_gp (b : bool) (u : unit) :
  resolve (SMP b) pr_gpo u =
  (ppo ← get ppp_loc ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put ppp_loc := Some pp ;; ret pp
        end ;;
   #put prev_loc := true ;;
   ret pp).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_pr_ck (j : nat) (x : th_M (thf_chain P)) :
  resolve (SMP true) pr_cko (j, x) =
  (revealed ← get prev_loc ;;
   #assert revealed ;;
   tgts ← get ptgts_loc ;;
   match getm tgts j with
   | Some (t0, x0) =>
       ppo ← get ppp_loc ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← wcp_dPP P ;; #put ppp_loc := Some pp ;; ret pp
            end ;;
       ret (th_eval (thf_chain P) pp t0 x == th_eval (thf_chain P) pp t0 x0)%B
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side PCHECK enforces the reveal phase and then answers false. *)
Lemma resolve_pr_ck_false (j : nat) (x : th_M (thf_chain P)) :
  resolve (SMP false) pr_cko (j, x) =
  (revealed ← get prev_loc ;;
   #assert revealed ;;
   ret false).
Proof.
simplify_linking.
reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The invariant (header)

    Follows the hop-invariant template (see [Sec.hop.grind]); the
    Some-branch delta here stores the per-chain pre-query list
    [qmap_from 0 [seq wq q | q <- pre_queries ...]]. *)

Definition IGNP : Locations :=
  [fmap forge_pk_loc P ; forge_log_loc P ; forge_sig_loc P ; r_chain_pre_pk_loc ; r_chain_pre_log_loc ;
        r_chain_pre_sig_loc ; ppp_loc ; ptgts_loc ; ptws_loc ; prev_loc ].

Definition RP (pko : option (Pk (shrincs_wots_scheme P))) (lg : seq (Msg (shrincs_wots_scheme P)))
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
          exists (m : wcp_M P) (c : nat) (us : seq (wcp_N P)),
            [/\ lg = [:: m],
                sgo = Some (wsigs P pk.1 0 (digest_of P pk.1 m c) us, c),
                po = Some pk.1,
                size us = wcp_chain_count P /\ good_counter P pk.1 m c
              & [/\ tg = qmap_from 0
                          [seq chain_common.wq P q | q <- wpreq P 0 (digest_of P pk.1 m c) us],
                    tw = [seq shrincs_wots_tweak P t | t <- unzip1 (wpreq P 0 (digest_of P pk.1 m c) us)]
                  & rv = true]]
      end].

Definition pr_inv : precond :=
  heap_ignore IGNP
  ⋊ rel_app [:: (lhs, forge_pk_loc P) ; (lhs, forge_log_loc P) ; (lhs, forge_sig_loc P) ;
                (rhs, r_chain_pre_pk_loc) ; (rhs, r_chain_pre_log_loc) ; (rhs, r_chain_pre_sig_loc) ;
                (rhs, ppp_loc) ; (rhs, ptgts_loc) ; (rhs, ptws_loc) ;
                (rhs, prev_loc) ] RP.

Arguments pr_inv : simpl never.

Lemma pr_invE s0 s1 :
  pr_inv (s0, s1) ->
  heap_ignore IGNP (s0, s1) /\
  RP (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_chain_pre_pk_loc) (get_heap s1 r_chain_pre_log_loc)
     (get_heap s1 r_chain_pre_sig_loc)
     (get_heap s1 ppp_loc) (get_heap s1 ptgts_loc) (get_heap s1 ptws_loc)
     (get_heap s1 prev_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma pr_invI s0 s1 :
  heap_ignore IGNP (s0, s1) ->
  RP (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_chain_pre_pk_loc) (get_heap s1 r_chain_pre_log_loc)
     (get_heap s1 r_chain_pre_sig_loc)
     (get_heap s1 ppp_loc) (get_heap s1 ptgts_loc) (get_heap s1 ptws_loc)
     (get_heap s1 prev_loc) ->
  pr_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** *** The block precondition (inside COMMIT, machinery dropped) *)

Definition pblk (po : option (wcp_PP P)) (rv : bool) (Q : seq qentry) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNP (s0, s1),
      get_heap s1 ppp_loc = po,
      get_heap s1 prev_loc = rv,
      get_heap s1 ptws_loc = [seq shrincs_wots_tweak P t | t <- unzip1 Q] &
      get_heap s1 ptgts_loc = qmap_from 0 [seq chain_common.wq P q | q <- Q]].

Arguments pblk : simpl never.

(** The lazy parameter sampling (put pp, at the PCOLLQ pin). *)
Lemma pblk_set_pp (pp : wcp_PP P) rv Q s0 s1 :
  pblk None rv Q (s0, s1) ->
  pblk (Some pp) rv Q (s0, set_heap s1 ppp_loc (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The PQUERY state update (put tgts; put tws). *)
Lemma pblk_qupd (pp : wcp_PP P) (Q : seq qentry) (t : nat * nat) (x : wcp_N P) s0 s1 :
  pblk (Some pp) false Q (s0, s1) ->
  pblk (Some pp) false (rcons Q (t, x))
    (s0, set_heap (set_heap s1 ptgts_loc
            (setm (qmap_from 0 [seq chain_common.wq P q | q <- Q])
                  (size [seq shrincs_wots_tweak P t' | t' <- unzip1 Q]) (shrincs_wots_tweak P t, x)))
          ptws_loc (rcons [seq shrincs_wots_tweak P t' | t' <- unzip1 Q] (shrincs_wots_tweak P t))).
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

(** The phase flip (PGETPP's put rev). *)
Lemma pblk_set_rev (po : option (wcp_PP P)) Q s0 s1 :
  pblk po false Q (s0, s1) ->
  pblk po true Q (s0, set_heap s1 prev_loc true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked PCOLLQ (pp pinned: state untouched) *)

Lemma r_prcollq_known (b : bool) {B : choiceType} (pp : wcp_PP P)
    (t : tc_T (coll_chain P)) (x : tc_M (coll_chain P)) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : tc_N (coll_chain P) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 (tc_eval (coll_chain P) pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMP b) pr_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_pr_cq b t x).
eapply (r_get_bind_rhs ppp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
cbv beta iota.
exact: h.
Qed.

(** Grinding loop through PCOLLQ. *)
Lemma r_prgrind_spec (b : bool) {B : choiceType} (pp : wcp_PP P) (m : wcp_M P)
    (cs : seq nat) rv (Q : seq qentry)
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B)
    (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ k1 [seq wcp_H_grind P pp (grind_adrs P) (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) rv Q (s0, s1) ⦄
     c0 ≈ bind (code_link (pr_grind m cs) (SMP b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_prcollq_known b).
  cbv beta.
  rewrite (chain_common.ct_collq_H_E P).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Stepping one linked PQUERY

    Unlike TQUERY (whose input is supplied by the reduction), PQUERY
    samples the hidden input INSIDE the oracle; the rule couples the
    lhs's [dN] (the game's root sample) with the oracle's hidden one
    (the SM-PRE query step at encoded tweaks). *)

Lemma r_prquery (b : bool) {B : choiceType} (pp : wcp_PP P)
    (i k : nat) (Q : seq qentry)
    (k0 k1 : wcp_N P -> raw_code B) (post : postcond B B) :
  (i < wcp_chain_count P)%N -> (k < (wcp_w P).-1)%N ->
  all (λ t : nat * nat, (t.1 < wcp_chain_count P)%N && (t.2 < (wcp_w P).-1)%N) (unzip1 Q) ->
  size Q < wcp_chain_count P ->
  (i, k) \notin unzip1 Q ->
  (forall x : wcp_N P,
     ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false (rcons Q ((i, k), x)) (s0, s1) ⦄
        k0 x ≈ k1 (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (i, k) x) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false Q (s0, s1) ⦄
     bind (wcp_dN P) k0 ≈ bind (resolve (SMP b) pr_pqo (chain_tweak P i k)) k1 ⦃ post ⦄.
Proof.
move=> hi hk hQr hbud hfresh h.
rewrite (resolve_pr_pq b (chain_tweak P i k)).
eapply (r_get_bind_rhs prev_loc false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs ptws_loc [seq shrincs_wots_tweak P t | t <- unzip1 Q]).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map /unzip1 size_map hbud.
move=> _.
eapply r_bind_assertD_rhs.
  move=> s0 s1 _; apply: (chain_common.wtw_notin P (i, k) (unzip1 Q) hi hk _ hfresh).
  by move=> t' /(allP hQr) /andP[h1 h2]; split.
move=> _.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> x; cbv beta.
eapply (r_get_bind_rhs ptgts_loc (qmap_from 0 [seq chain_common.wq P q | q <- Q])).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (pblk_qupd pp Q (i, k) x s0 s1 hpre).
eapply (r_get_bind_rhs ppp_loc (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
simpl.
have hkw : (k < wcp_w P)%N.
  by apply: (ltn_trans hk); rewrite ltn_predL; apply: (ltnW (wcp_Hw P)).
rewrite (chain_common.Fc_wtw P pp (i, k) x hkw).
exact: (h x).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain induction

    lhs [sample_sig_roots] at [Fw], rhs the linked [pr_chains]; the
    committed list grows by [pre_queries] and both results are
    [sigs_of] of the hidden inputs. *)

Lemma r_prchains_spec (b : bool) {B : choiceType} (pp : wcp_PP P)
    (post : postcond B B) :
  forall ds st (Q : seq qentry) (K0 K1 : chList (wcp_N P) -> raw_code B),
  (st + size ds <= wcp_chain_count P)%N ->
  all (λ d : nat, (d < wcp_w P)%N) ds ->
  all (λ t : nat * nat, (t.1 < wcp_chain_count P)%N && (t.2 < (wcp_w P).-1)%N) (unzip1 Q) ->
  (size Q + preimage_query_count ds <= wcp_chain_count P)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false
            (Q ++ wpreq P st ds us) (s0, s1) ⦄
        K0 (wsigs P pp st ds us) ≈ K1 (wsigs P pp st ds us) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), pblk (Some pp) false Q (s0, s1) ⦄
     bind (sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp st ds) K0
   ≈ bind (code_link (pr_chains st ds) (SMP b)) K1 ⦃ post ⦄.
Proof.
have hw0 : (0 < wcp_w P)%N := ltnW (wcp_Hw P).
elim=> [|d ds IH] st Q K0 K1 hst hds hQr hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- move: hst => /=; rewrite addnS => hst2.
  have hstcc : (st < wcp_chain_count P)%N := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : (st.+1 + size ds <= wcp_chain_count P)%N := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /= code_link_bind.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* d = 0 : both sides sample the value locally; [Q] is unchanged so
       the [eapply IH => //] discharges the range invariant [hQr] by
       assumption. *)
    rewrite (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P))).
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> u; cbv beta.
    rewrite !bind_assoc.
    rewrite (code_link_bind (pr_chains st.+1 ds)) !bind_assoc.
    eapply IH => //.
    * by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
    * move=> us hus.
      move: (h (u :: us)); rewrite /= hus => /(_ erefl).
      by [].
  + (* d = d'.+1 : the sigma PQUERY at position [d' < w.-1]. *)
    have hdw1 : (d'.+1 <= (wcp_w P).-1)%N by rewrite -ltnS prednK.
    rewrite bind_assoc.
    simpl.
    rewrite !bind_assoc.
    eapply r_prquery => //.
    * by apply: leq_trans hbud; rewrite /preimage_query_count /= addnS ltnS leq_addr.
    * exact: lt_notin hfresh.
    * move=> x; cbv beta.
      rewrite !bind_assoc.
      simpl.
      rewrite (code_link_bind (pr_chains st.+1 ds)) !bind_assoc.
      eapply IH => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstcc hdw1.
      -- by move: hbud; rewrite size_rcons /preimage_query_count /= addnS addSn.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /= ltnSn.
         ++ by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
      -- move=> us hus.
         move: (h (x :: us)); rewrite /= hus => /(_ erefl).
         by rewrite /wpreq (pre_queries_cons (wcp_N P)) /= cat_rcons.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The common COMMIT tail *)

Lemma r_pr_tail (pp : wcp_PP P) (m : wcp_M P) (c : nat) (us : seq (wcp_N P)) :
  good_counter P pp m c -> size us = wcp_chain_count P ->
  ⊢ ⦃ λ '(s0, s1),
        pblk (Some pp) true (wpreq P 0 (digest_of P pp m c) us) (s0, s1) ⦄
     (#put forge_pk_loc P := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c)
        (wsigs P pp 0 (digest_of P pp m c) us))) ;;
      #put forge_log_loc P := [:: m] ;;
      #put forge_sig_loc P := Some (wsigs P pp 0 (digest_of P pp m c) us, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c)
             (wsigs P pp 0 (digest_of P pp m c) us))),
           Some (wsigs P pp 0 (digest_of P pp m c) us, c)))
   ≈ (#put r_chain_pre_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c)
        (wsigs P pp 0 (digest_of P pp m c) us))) ;;
      #put r_chain_pre_log_loc := [:: m] ;;
      #put r_chain_pre_sig_loc := Some (wsigs P pp 0 (digest_of P pp m c) us, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c)
             (wsigs P pp 0 (digest_of P pp m c) us))),
           Some (wsigs P pp 0 (digest_of P pp m c) us, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ pr_inv (s0, s1) ⦄.
Proof.
move=> hgood hus.
eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.
eapply r_put_rhs; eapply r_put_rhs; eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hblk ->].
case: hblk => hign hpp hrev htws htgts.
split; first by [].
apply: pr_invI.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.
  exact: hign.
- get_heap_simpl.
  rewrite hpp hrev htws htgts.
  split=> //.
  by exists m, c, us; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Closing a null KFORGE leaf

    In every non-forging KFORGE branch both the game and the reduction
    return the same boolean and leave [pr_inv] untouched.  The invariant
    sits at the deep-left of the precond, under however many remembered
    relations the branch has accumulated (1 to 7 across the two proofs);
    [pr_take_inv] peels those off agnostically rather than each leaf
    hand-counting the nesting depth. *)

Local Ltac pr_take_inv h := first [ exact: h | case: h => h _; pr_take_inv h ].

(* ------------------------------------------------------------------ *)
(** *** THE real-side equivalence *)

Lemma R_chain_pre_real :
  perfect (I_KOTS (shrincs_wots_scheme P)) (intermediates.G_post_chain P) (R_chain_pre ∘ SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P) true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pr_inv).
{ rewrite /pr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), pblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/pr_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the PCOLLQ pin *)
  rewrite (resolve_pr_cq true (encode_tweak P (grind_adrs P)) (inr (m, 0))).
  eapply (r_get_bind_rhs ppp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (pblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  (* the grinding loop through PCOLLQ *)
  rewrite (code_link_bind (pr_grind m (iota 0 (wcp_c_max P)))).
  eapply (r_prgrind_spec true pp m).
  cbv beta.
  rewrite code_link_assertD
          (cp_pick_map P).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (find_counter P pp m). }
  move=> e1 _.
  move: e1; case E: (find_counter P pp m) => [c|] /= e1; last by [].
  rewrite !(intermediates.digestE P).
  (* the chains: lhs re-rooted sampling, rhs hidden PQUERY samples *)
  rewrite (code_link_bind (pr_chains 0 (digest_of P pp m c))).
  have hszd : size (digest_of P pp m c) = wcp_chain_count P
    := size_digest_of P pp m c.
  eapply (r_prchains_spec true pp _ (digest_of P pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_counter_good P pp m c E; exact: hwf. }
    { by rewrite /= (npq_le (wcp_chain_count P) _ hszd). }
  move=> us hus.
  cbv beta.
  simpl.
  (* PGETPP, then the PURE completion/compression *)
  rewrite (resolve_pr_gp true Datatypes.tt).
  eapply (r_get_bind_rhs ppp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (pblk_set_rev _ _ _ _ hpre). }
  apply: r_pr_tail => //.
  - exact: (find_counter_good P pp m c E).
  - by rewrite hus (size_digest_of P).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  (* committed: mirror G_post_chain *)
    sync_eq lg lg'.
      { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
        case/pr_invE: hinv => _ [_ e2 _ _].
        rewrite /rem_inv /= in hrem0 hrem1.
        by rewrite -hrem0 -hrem1. }
    move=> e; subst lg'.
    sync_eq sgol sgov.
      { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
        case/pr_invE: hinv => _ [_ _ e3 _].
        rewrite /rem_inv /= in hrem0 hrem1.
        by rewrite -hrem0 -hrem1. }
    move=> e; subst sgov.
    eapply (r_fact (exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
              lg = [:: m] /\ sgol = Some (sg, c))).
      { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
        case/pr_invE: hinv => _ [_ _ _ hmatch].
        rewrite /rem_inv /= in h1 h3 h5.
        rewrite h1 in hmatch.
        case: hmatch => mm [cc [uss [hA hB _ _ _]]].
        exists mm, cc, (wsigs P pk.1 0 (digest_of P pk.1 mm cc) uss); split.
        - by rewrite -h3.
        - by rewrite -h5. }
    move=> [m [c [sg [hlg hsgol]]]].
    rewrite hlg hsgol /=.
    case E0: (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin [:: m]));
      last first.
    * (* invalid forgery: both sides answer false *)
      apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
    * case/andP: (E0) => hver hfresh.
      case E1: ((digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m c)%B).
      -- (* GRIND: both null *)
         apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
      -- case E2: ((complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                    != complete_ends P pk.1 (digest_of P pk.1 m c) sg)%B).
         ++ (* COMPRESS: both null *)
            apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
         ++ case E3: (wtcr_dec P pk.1 (digest_of P pk.1 m c)
                        (digest_of P pk.1 mst sgst.2) sg sgst.1) => [ju|].
            ** (* ChainColl: both null *)
               apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
            ** case E4: (wpre_dec P pk.1 (digest_of P pk.1 m c)
                           (digest_of P pk.1 mst sgst.2) sg sgst.1)
                 => [[j x]|]; last first.
               --- (* degenerate: both answer true *)
                   apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
               --- (* ChainMeet: PCHECK answers true = G_post_chain's true *)
                   simpl.
                   rewrite (resolve_pr_ck j x).
                   eapply (r_get_bind_rhs prev_loc true).
                     { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1.
                       rewrite h1 in hmatch.
                       by case: hmatch
                         => mm [cc [uss [_ _ _ _ [_ _ hrv]]]]. }
                   cbv beta.
                   eapply r_bind_assertD_rhs; first by [].
                   move=> _.
                   eapply r_get_remember_rhs => tg.
                   eapply (r_fact (exists us,
                             [/\ size us = wcp_chain_count P, good_counter P pk.1 m c,
                                 sg = wsigs P pk.1 0 (digest_of P pk.1 m c) us
                               & tg = qmap_from 0
                                   [seq chain_common.wq P q
                                   | q <- wpreq P 0 (digest_of P pk.1 m c) us]])).
                     { move=> s0 s1
                         [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
                       rewrite h1 in hmatch.
                       case: hmatch
                         => mm [cc [uss [hA hB _ [husz hgood] [htg _ _]]]].
                       have emm : mm = m.
                         { have : [:: mm] = [:: m] by rewrite -hA h3.
                           by case. }
                       rewrite emm in hB hgood htg.
                       have hsgcc :
                           Some (wsigs P pk.1 0 (digest_of P pk.1 m cc) uss, cc)
                           = Some (sg, c).
                         { by rewrite -hB h5. }
                       have ecc : cc = c by case: hsgcc.
                       rewrite ecc in hsgcc hgood htg.
                       have esg : sg = wsigs P pk.1 0 (digest_of P pk.1 m c) uss.
                         { by case: hsgcc. }
                       by exists uss; split=> //; rewrite -h7. }
                   move=> [us [husz hgood hsg htg]].
                   have hned := negbT E1.
                   have hends : complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                                = complete_ends P pk.1 (digest_of P pk.1 m c)
                                    (wsigs P pk.1 0 (digest_of P pk.1 m c) us).
                     { by move/negbFE/eqP: E2 => ->; rewrite hsg. }
                   move: (hver); rewrite /shrincs_wots_verify => /and3P[hvd' hys _].
                   have hwin := chain_common.wpre_decisionP P pk.1 m mst c sgst.2 us sgst.1
                                  hgood husz hvd' hys hends hned.
                   rewrite -hsg E4 in hwin.
                   case: hwin => t [u [hqn hfeq]].
                   have hgetm : getm tg j = Some (shrincs_wots_tweak P t, u).
                     { rewrite htg.
                       have := qmap_from_get 0
                         [seq chain_common.wq P q | q <- wpreq P 0 (digest_of P pk.1 m c) us] j.
                       rewrite add0n => ->.
                       by rewrite qnth_map hqn. }
                   rewrite hgetm.
                   eapply (r_get_rhs_known ppp_loc (Some pk.1)).
                     { move=> s0 s1
                         [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1.
                       rewrite h1 in hmatch.
                       by case: hmatch => mm [cc [uss [_ _ hpo _ _]]]. }
                   simpl.
                   rewrite !(chain_common.wpre_check_bridge P pk.1 m c us j t u _ hgood husz hqn).
                   rewrite hfeq eqxx.
                   apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE ideal-side equivalence *)

Lemma R_chain_pre_ideal :
  perfect (I_KOTS (shrincs_wots_scheme P)) (G_forge_uniformchains P false) (R_chain_pre ∘ SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P) false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ pr_inv).
{ rewrite /pr_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (G_forge_uniformchains's COMMIT is verbatim
     G_post_chain's; all oracle bodies and loop specs are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst pko'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), pblk None false [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/pr_invE: hinv => hign hRP.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRP => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_pr_cq false (encode_tweak P (grind_adrs P)) (inr (m, 0))).
  eapply (r_get_bind_rhs ppp_loc None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (pblk_set_pp pp _ _ _ _ hpre). }
  simpl.
  rewrite (code_link_bind (pr_grind m (iota 0 (wcp_c_max P)))).
  eapply (r_prgrind_spec false pp m).
  cbv beta.
  rewrite code_link_assertD
          (cp_pick_map P).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (find_counter P pp m). }
  move=> e1 _.
  move: e1; case E: (find_counter P pp m) => [c|] /= e1; last by [].
  rewrite !(intermediates.digestE P).
  rewrite (code_link_bind (pr_chains 0 (digest_of P pp m c))).
  have hszd : size (digest_of P pp m c) = wcp_chain_count P
    := size_digest_of P pp m c.
  eapply (r_prchains_spec false pp _ (digest_of P pp m c) 0 [::]) => //.
    { by rewrite add0n hszd. }
    { by have /andP[hwf _] := find_counter_good P pp m c E; exact: hwf. }
    { by rewrite /= (npq_le (wcp_chain_count P) _ hszd). }
  move=> us hus.
  cbv beta.
  simpl.
  rewrite (resolve_pr_gp false Datatypes.tt).
  eapply (r_get_bind_rhs ppp_loc (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (pblk_set_rev _ _ _ _ hpre). }
  apply: r_pr_tail => //.
  - exact: (find_counter_good P pp m c E).
  - by rewrite hus (size_digest_of P).
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  sync_eq pko pko'.
    { move=> s0 s1 [[hinv hrem0] hrem1].
      case/pr_invE: hinv => _ [e1 _ _ _].
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
      case/pr_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  eapply r_get_remember_rhs => sgov.
    eapply (r_fact (exists (m : wcp_M P) (c : nat) (us : seq (wcp_N P)),
              [/\ lg = [:: m],
                  sgov = Some (wsigs P pk.1 0 (digest_of P pk.1 m c) us, c),
                  size us = wcp_chain_count P & good_counter P pk.1 m c])).
      { move=> s0 s1 [[[[[hinv h1] h2] h3] h4] h5].
        case/pr_invE: hinv => _ [epk elog esig hmatch].
        rewrite /rem_inv /= in h1 h2 h3 h4 h5.
        rewrite h1 in hmatch.
        case: hmatch => mm [cc [uss [hA hB _ [husz hgood] _]]].
        exists mm, cc, uss; split=> //.
        - by rewrite -h3.
        - by rewrite -h5 esig hB. }
    move=> [m [c [us [hlg hsgov husz hgood]]]].
    rewrite hlg hsgov /=.
    case E0: (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin [:: m]));
      last first.
    * apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
    * case/andP: (E0) => hver hfresh.
      case E1: ((digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m c)%B).
      -- apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
      -- case E2: ((complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                    != complete_ends P pk.1 (digest_of P pk.1 m c)
                         (wsigs P pk.1 0 (digest_of P pk.1 m c) us))%B).
         ++ apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
         ++ case E3: (wtcr_dec P pk.1 (digest_of P pk.1 m c)
                        (digest_of P pk.1 mst sgst.2)
                        (wsigs P pk.1 0 (digest_of P pk.1 m c) us) sgst.1)
              => [ju|].
            ** apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
            ** case E4: (wpre_dec P pk.1 (digest_of P pk.1 m c)
                           (digest_of P pk.1 mst sgst.2)
                           (wsigs P pk.1 0 (digest_of P pk.1 m c) us) sgst.1)
                 => [[j x]|]; last first.
               --- (* dead branch: the classifier is total on the
                      CHAIN branch (wclassify_some) *)
                   eapply (r_fact False); last by [].
                   move=> s0 s1 _.
                   have hned := negbT E1.
                   have hends : complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                                = complete_ends P pk.1 (digest_of P pk.1 m c)
                                    (wsigs P pk.1 0 (digest_of P pk.1 m c) us).
                     { by move/negbFE/eqP: E2. }
                   move: (hver); rewrite /shrincs_wots_verify => /and3P[hvd' hys _].
                   have := chain_common.wclassify_some P pk.1 m mst c sgst.2 us sgst.1
                             hgood husz hvd' hys hends hned E3.
                   by rewrite E4 eqxx.
               --- (* ChainMeet: ideal PCHECK answers false, as does
                      G_forge_uniformchains-ideal *)
                   simpl.
                   rewrite (resolve_pr_ck_false j x).
                   eapply (r_get_bind_rhs prev_loc true).
                     { move=> s0 s1 [[[[[hinv h1] _] _] _] _].
                       case/pr_invE: hinv => _ [_ _ _ hmatch].
                       rewrite /rem_inv /= in h1.
                       rewrite h1 in hmatch.
                       by case: hmatch
                         => mm [cc [uss [_ _ _ _ [_ _ hrv]]]]. }
                   cbv beta.
                   eapply r_bind_assertD_rhs; first by [].
                   move=> _.
                   apply r_ret => s0 s1 hpre; split=> //; pr_take_inv hpre.
Qed.


End ChainPRE.
