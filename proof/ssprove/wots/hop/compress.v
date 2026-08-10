(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.compress

    The SM-TCR(T_sf) compression hop of the WOTS+C one-time
    security proof: the SECOND split of the forgery analysis, nulling
    the pk-compression-collision case (case 2 / COMPRESS of
    [analysis.shrincs_wots_forgery_classify]) between [G_post_grind]
    (Sec.hop.grind) and [G_post_compress].  Delivered:

      [R_compress_real  : perfect (I_KOTS WC) G_post_grind
                            (R_compress ∘ SMTCR_game thf_pkcompress coll_pkcompress 1 true)]
      [R_compress_ideal : perfect (I_KOTS WC) G_post_compress
                            (R_compress ∘ SMTCR_game thf_pkcompress coll_pkcompress 1 false)]

    where [G_post_compress] is [G_post_grind] with KFORGE ALSO answering false on the
    COMPRESS case — a verifying fresh forgery whose recomputed digest
    DIFFERS from the signed one (digit vectors) but whose completed
    chain ends differ from the honest stored ends (verification
    already forces the T_sf compressions of the two end lists to
    coincide, so within the verified branch the single boolean
    discriminant [forged completed ends != honest completed ends]
    captures exactly the classifier's second disjunct); the next hop
    (Sec.hop.chain_tcr, chain collisions) continues from [G_post_compress].
    Hence
    [Adv G_post_grind G_post_compress <= AdvOf (SMTCR_game thf_pkcompress coll_pkcompress 1) (A ∘ R_compress)] by
    the standard reduction steps at the consumer.

    ** Design

    - ONE TQUERY (budget p = 1): the committed SM-TCR(T_sf) target
      is [(encode_tweak pk_adrs, honest completed ends)].  Everything
      the reduction must compute BEFORE that query — the grinded
      digest and the per-chain re-rooted signature/completion chains
      — needs H_grind and F under the still-hidden [pp]; [coll_pkcompress]
      (games.v) exposes exactly those two through the COLLQ oracle
      (sum-tagged inputs/outputs).
    - COMMIT: one-shot guard; ONE unguarded COLLQ at the grinding
      address pins [pp]'s lazy sampling at a fixed program point (the
      COLLQ-pin trick — couples SM-TCR's lazy [dPP] against G_post_grind's
      eager one, no swap needed; works for every [c_max], including
      0); the grinding queries H_grind at every counter below [c_max]
      ([cp_grind], one COLLQ each) and the bounded search runs purely
      on the answer list ([cp_pick]; [cp_pick_map] identifies it with
      the scheme's [find_counter], so the [#assert] aborts exactly with
      G_post_grind's grinding assert); per chain, the root is sampled LOCALLY
      ([dN] — hidden values never touch an oracle) and the signature
      value/completed end are computed through COLLQ F-calls
      ([cp_chains]/[cp_walk], the oracle-routed walk pattern); then
      the ONE
      [TQUERY (encode_tweak pk_adrs, ends)] — whose answer IS
      [T_sf pp pk_adrs ends] — and GETPP; store pk/log/(sigs, ctr).
    - KFORGE: getSome pk, log, getSome (sigs, ctr);
      [v := verify && freshness]; if [~~ v] ret false; if the digests
      agree as digit vectors (GRIND case) ret false (BOTH G_post_grind and
      G_post_compress null it — the grinding hop absorbed that case); else if the
      forged completed ends differ from the honest ones (COMPRESS
      discriminant), call [CHECK (0, forged completed ends)] and
      return its answer; else ret true (the CHAIN cases — both games
      answer true there, the later hops absorb them).
      Real side: the discriminant gives [forged ends != honest ends],
      and the verification equation [T_sf pp pk_adrs (forged ends) =
      pk.2 = T_sf pp pk_adrs (honest ends)] (the invariant records
      pk.2's shape) is SM-TCR's collision — CHECK answers true =
      G_post_grind's verdict.  Ideal side: CHECK answers false = G_post_compress.
    - NO side conditions: no [Hrange] (the COMPRESS discriminants are
      computed directly, no digit-vector injectivity needed), no
      [0 < chain_count] / [1 < w] / [0 < c_max] (the COLLQ pin makes the
      lazy/eager pp coupling unconditional), no [dM] (thf_grind is not
      involved; thf_pkcompress's dummy input sampler is [ret [::]]).

    ** Invariant

    [heap_ignore] over all ten private locations joined with ONE
    [rel_app] relation [RC]: G_post_grind's (= G_post_compress's) pk/log/sig locations
    (300-302, shared with G_forge_sampledkey/G_forge_uniformchains) mirror R's (340-342), and R's pk
    determines the entire SM-TCR state — None: everything initial;
    Some pk: there are [m, c, sg] with log = [:: m], stored signature
    [(sg, c)], [pk.2 = T_sf pk.1 pk_adrs (honest ends)], parameter
    pinned to [pk.1], ONE committed target
    [(encode_tweak pk_adrs, honest ends)] at index 0, phase revealed.

    Locations 340-342. *)

From mathcomp.experimental_reals Require Import distr.
From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf games.smtcr toolkit.sample_seq toolkit.relational_rules
  toolkit.hop_tactics.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Sec.lib Require Import chain.core.
From Sec Require Import addressing.
From Sec.wots Require Import addressing.
From Sec.wots Require Import scheme games analysis
  hop.intermediates.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section CompressHop.

(** The WOTS+C parameter record (see Sec.wots.params). *)
Context (P : wc_params).

Local Notation SMB b := (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1 b).

Local Notation pp_loc' := (tcr_pp_loc (thf_pkcompress P)).
Local Notation tgts_loc' := (tcr_tgts_loc (thf_pkcompress P)).
Local Notation tws_loc' := (tcr_tws_loc (thf_pkcompress P)).
Local Notation rev_loc' := tcr_rev_loc.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the COLLQ-routed grinding search

    The reduction queries H_grind through COLLQ at every counter below
    [c_max] ([cp_grind] below) and runs the bounded search on the
    answer list: [cp_pick] returns the first (counter, digest value)
    whose decoded digits satisfy the digit-sum predicate —
    [find_counter]'s search, re-rooted at the oracle answers ([cp_pick_map]).
    [cp_pick]/[cp_pick_map] live in [Sec.hop.intermediates] (shared
    with the chain hops). *)

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed loops *)

(** COLLQ/TQUERY/GETPP/CHECK opsigs as committed to [I_SMTCR TP CP]. *)
Definition cp_cqo : opsig :=
  (COLLQ, (tc_T (coll_pkcompress P) × tc_M (coll_pkcompress P), tc_N (coll_pkcompress P))).
Definition cp_tqo : opsig :=
  (TQUERY, (th_T (thf_pkcompress P) × th_M (thf_pkcompress P), th_N (thf_pkcompress P))).
Definition cp_gpo : opsig := (GETPP, ('unit, th_PP (thf_pkcompress P))).
Definition cp_cko : opsig := (CHECK, ('nat × th_M (thf_pkcompress P), 'bool)).

(** The grinding loop: one COLLQ (H_grind member, [inr]) per counter;
    returns the answer list. *)
Fixpoint cp_grind (m : wcp_M P) (cs : seq nat) : raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr cp_cqo (encode_tweak P (grind_adrs P), inr (m, c))
        (λ r,
           hs ← cp_grind m cs' ;;
           ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance cp_grind_valid (L : Locations) (m : wcp_M P) (cs : seq nat) :
  ValidCode L (I_SMTCR (thf_pkcompress P) (coll_pkcompress P)) (cp_grind m cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Walk chain [i] upward from value [x] at position [k] for [n]
    steps, one COLLQ (F member, [inl]) per step; returns the value at
    [k + n]. *)
Fixpoint cp_walk (i k n : nat) (x : wcp_N P) : raw_code (wcp_N P) :=
  if n is n'.+1
  then opr cp_cqo (chain_tweak P i k, inl x)
         (λ r, cp_walk i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance cp_walk_valid (L : Locations) i k n (x : wcp_N P) :
  ValidCode L (I_SMTCR (thf_pkcompress P) (coll_pkcompress P)) (cp_walk i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; exact: IH.
Qed.

(** All chains from index [st] with digits [ds]: per chain, sample
    the root LOCALLY, one COLLQ F-step to the signature position
    (positive digits), walk upward; returns (signature values,
    completed ends). *)
Fixpoint cp_chains (st : nat) (ds : seq nat) :
    raw_code (chList (wcp_N P) × chList (wcp_N P)) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
      u ← wcp_dN P ;;
      s ← (if d is d'.+1
           then opr cp_cqo (chain_tweak P st d', inl u)
                  (λ r, ret (if r is inl y then y else u))
           else ret u) ;;
      e ← cp_walk st d ((wcp_w P).-1 - d) s ;;
      '(ss, es) ← cp_chains st.+1 ds' ;;
      ret (s :: ss, e :: es)
  end.

#[local] Instance cp_chains_valid (L : Locations) st ds :
  ValidCode L (I_SMTCR (thf_pkcompress P) (coll_pkcompress P)) (cp_chains st ds).
Proof.
elim: ds st => [|d ds IH] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first by fmap_solve.
    move=> r; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: cp_walk_valid.
    move=> e; eapply valid_bind; first exact: IH.
    move=> [ss es]; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The reduction package *)

(** R's own locations (340+, see header). *)
Definition r_compress_pk_loc := mkloc 340 (None : option (Pk (shrincs_wots_scheme P))).
Definition r_compress_log_loc := mkloc 341 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition r_compress_sig_loc := mkloc 342 (None : option (Sig (shrincs_wots_scheme P))).

(** THE reduction: plays [I_KOTS WC] using the SM-TCR oracles. *)
Definition R_compress :
    package (I_SMTCR (thf_pkcompress P) (coll_pkcompress P)) (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap r_compress_pk_loc ; r_compress_log_loc ; r_compress_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P)
                   ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get r_compress_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      _ ← opr cp_cqo (encode_tweak P (grind_adrs P), inr (m, 0)) (λ r, ret r) ;;
      hs ← cp_grind m (iota 0 (wcp_c_max P)) ;;
      #assert (isSome (intermediates.cp_pick P hs)) ;;
      let c := (odflt (0, 0) (intermediates.cp_pick P hs)).1 in
      let d := rev (digits_w (wcp_w P) (wcp_chain_count P) (odflt (0, 0) (intermediates.cp_pick P hs)).2) in
      '(sgs, ends) ← cp_chains 0 d ;;
      root ← opr cp_tqo (encode_tweak P (pk_adrs P), ends) (λ r, ret r) ;;
      pp ← opr cp_gpo Datatypes.tt (λ p, ret p) ;;
      #put r_compress_pk_loc := Some (pp, root) ;;
      #put r_compress_log_loc := [:: m] ;;
      #put r_compress_sig_loc := Some (sgs, c) ;;
      ret ((pp, root), Some (sgs, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome r_compress_pk_loc ;;
      log ← get r_compress_log_loc ;;
      sgo ← getSome r_compress_sig_loc ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m sgo.2
            then ret false
            else
              if complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                 != complete_ends P pk.1 (digest_of P pk.1 m sgo.2) sgo.1
              then opr cp_cko
                     (0, complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1)
                     (λ ans, ret ans)
              else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** G_post_compress: G_post_grind with ALSO the COMPRESS case nulled

    Defined in [Sec.hop.intermediates] (shared so the hops type-check
    in parallel). *)

(* ------------------------------------------------------------------ *)
(** ** Linked oracle bodies (resolve equations, computed once)

    The COLLQ/TQUERY/GETPP bodies do not depend on the real/ideal
    flag, so the whole COMMIT machinery below is parametric in [b]. *)

Lemma resolve_cq (b : bool) (t : tc_T (coll_pkcompress P)) (x : tc_M (coll_pkcompress P)) :
  resolve (SMB b) cp_cqo (t, x) =
  (ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   ret (tc_eval (coll_pkcompress P) pp t x)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_tq (b : bool) (t : th_T (thf_pkcompress P)) (xs : th_M (thf_pkcompress P)) :
  resolve (SMB b) cp_tqo (t, xs) =
  (revealed ← get rev_loc' ;;
   #assert ~~ revealed ;;
   tws ← get tws_loc' ;;
   #assert (size tws < 1)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get tgts_loc' ;;
   #put tgts_loc' := setm tgts (size tws) (t, xs) ;;
   #put tws_loc' := rcons tws t ;;
   ppo ← get pp_loc' ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← wcp_dPP P ;; #put pp_loc' := Some pp ;; ret pp
        end ;;
   ret (th_eval (thf_pkcompress P) pp t xs)).
Proof.
by case: b; simplify_linking.
Qed.

Lemma resolve_gp (b : bool) (u : unit) :
  resolve (SMB b) cp_gpo u =
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

Lemma resolve_ck (j : nat) (xs : th_M (thf_pkcompress P)) :
  resolve (SMB true) cp_cko (j, xs) =
  (revealed ← get rev_loc' ;;
   #assert revealed ;;
   tgts ← get tgts_loc' ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get pp_loc' ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← wcp_dPP P ;; #put pp_loc' := Some pp ;; ret pp
            end ;;
       ret ((xs != m0) && (th_eval (thf_pkcompress P) pp t0 xs == th_eval (thf_pkcompress P) pp t0 m0))
   | None => ret false
   end).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side CHECK answers false unconditionally. *)
Lemma resolve_ck_false (j : nat) (xs : th_M (thf_pkcompress P)) :
  resolve (SMB false) cp_cko (j, xs) = ret false.
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the package, the resolved oracle bodies and the pure layer
   folded under [simpl] from here on (the resolve equations above are
   proved). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_counter : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments digits_w : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments Sec.wots.params.decode_tweak : simpl never.
#[local] Arguments intermediates.cp_pick : simpl never.

(* ------------------------------------------------------------------ *)
(** ** Conversion bridges (canonical tweaks compute; [decode_tweak]
    at closed type tags, the [digest_resE] flavor) *)

(** The COLLQ answer at the grinding address, post-processed by the
    loop's [inr]-projection, IS the scheme's H_grind output. *)
Lemma collq_H_E (pp : wcp_PP P) (m : wcp_M P) (c : nat) :
  (if tc_eval (coll_pkcompress P) pp (encode_tweak P (grind_adrs P)) (inr (m, c)) is inr h then h else 0)
  = wcp_H_grind P pp (grind_adrs P) (m, c).
Proof.
rewrite /tc_eval /coll_pkcompress /coll_pkcompress_core /=.
congr (wcp_H_grind P).
rewrite core_decodeE.
exact: (encode_tweakK P (grind_adrs P)).
Qed.

(** The COLLQ answer at a chain address, post-processed by the walk's
    [inl]-projection, IS the scheme's F-step. *)
Lemma collq_F_E (pp : wcp_PP P) (i k : nat) (x : wcp_N P) :
  (if tc_eval (coll_pkcompress P) pp (chain_tweak P i k) (inl x) is inl y then y else x)
  = wcp_F P pp (chain_adrs P i k) x.
Proof.
rewrite /tc_eval /coll_pkcompress /coll_pkcompress_core /=.
by rewrite core_decodeE decode_chain_tweak.
Qed.

(** The COLLQ answer IS the abstract chain step [Fw] (which is what the
    honest chains compute). *)
Lemma collq_Fc_E (pp : wcp_PP P) (i k : nat) (x : wcp_N P) :
  (k < wcp_w P)%N ->
  (if tc_eval (coll_pkcompress P) pp (chain_tweak P i k) (inl x) is inl y then y else x)
  = (Fw P) pp (i, k) x.
Proof.
move=> hk.
by rewrite collq_F_E.
Qed.

(** [digestE]/[wendsE] (oracle-answer = [digest_of]; length-chain_count walk's
    completed ends = verifier's [complete_ends]) live in
    [Sec.hop.intermediates]. *)

(* ------------------------------------------------------------------ *)
(** ** The invariant (header)

    Follows the hop-invariant template (see [Sec.hop.grind]); the
    Some-branch delta here adds [pk.2 = T_sf pk.1 pk_adrs (...)] and the
    single ends target. *)

Definition IGNC : Locations :=
  [fmap forge_pk_loc P ; forge_log_loc P ; forge_sig_loc P ;
        r_compress_pk_loc ; r_compress_log_loc ;
        r_compress_sig_loc ; pp_loc' ; tgts_loc' ; tws_loc' ; rev_loc' ].

Definition RC (pko : option (Pk (shrincs_wots_scheme P))) (lg : seq (Msg (shrincs_wots_scheme P)))
    (sgo : option (Sig (shrincs_wots_scheme P)))
    (pko' : option (Pk (shrincs_wots_scheme P))) (lg' : seq (Msg (shrincs_wots_scheme P)))
    (sgo' : option (Sig (shrincs_wots_scheme P)))
    (po : option (wcp_PP P)) (tg : {fmap nat -> (th_T (thf_pkcompress P) × th_M (thf_pkcompress P))})
    (tw : seq (th_T (thf_pkcompress P))) (rv : bool) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None =>
          [/\ lg = [::], sgo = None, po = None, tg = emptym
            & tw = [::] /\ rv = false]
      | Some pk =>
          exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
            [/\ lg = [:: m], sgo = Some (sg, c), po = Some pk.1,
                pk.2 = wcp_T_sf P pk.1 (pk_adrs P) (complete_ends P pk.1 (digest_of P pk.1 m c) sg)
                /\ tg = setm emptym 0 (encode_tweak P (pk_adrs P),
                                       complete_ends P pk.1 (digest_of P pk.1 m c) sg)
              & tw = [:: encode_tweak P (pk_adrs P)] /\ rv = true]
      end].

Definition cp_inv : precond :=
  heap_ignore IGNC
  ⋊ rel_app [:: (lhs, forge_pk_loc P) ; (lhs, forge_log_loc P) ; (lhs, forge_sig_loc P) ;
                (rhs, r_compress_pk_loc) ; (rhs, r_compress_log_loc) ; (rhs, r_compress_sig_loc) ;
                (rhs, pp_loc') ; (rhs, tgts_loc') ; (rhs, tws_loc') ;
                (rhs, rev_loc') ] RC.

Arguments cp_inv : simpl never.

Lemma cp_invE s0 s1 :
  cp_inv (s0, s1) ->
  heap_ignore IGNC (s0, s1) /\
  RC (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_compress_pk_loc) (get_heap s1 r_compress_log_loc)
     (get_heap s1 r_compress_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma cp_invI s0 s1 :
  heap_ignore IGNC (s0, s1) ->
  RC (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_compress_pk_loc) (get_heap s1 r_compress_log_loc)
     (get_heap s1 r_compress_sig_loc)
     (get_heap s1 pp_loc') (get_heap s1 tgts_loc') (get_heap s1 tws_loc')
     (get_heap s1 rev_loc') ->
  cp_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside COMMIT, machinery dropped) *)

Definition cblk (po : option (wcp_PP P)) (rv : bool)
    (tw : seq (th_T (thf_pkcompress P)))
    (tg : {fmap nat -> (th_T (thf_pkcompress P) × th_M (thf_pkcompress P))}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGNC (s0, s1),
      get_heap s1 pp_loc' = po,
      get_heap s1 rev_loc' = rv,
      get_heap s1 tws_loc' = tw &
      get_heap s1 tgts_loc' = tg].

Arguments cblk : simpl never.

(** The lazy parameter sampling (put pp, at the COLLQ pin). *)
Lemma cblk_set_pp (pp : wcp_PP P) rv tw tg s0 s1 :
  cblk None rv tw tg (s0, s1) ->
  cblk (Some pp) rv tw tg (s0, set_heap s1 pp_loc' (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** The TQUERY state update (put tgts; put tws). *)
Lemma cblk_qupd (pp : wcp_PP P) (xs : th_M (thf_pkcompress P)) s0 s1 :
  cblk (Some pp) false [::] emptym (s0, s1) ->
  cblk (Some pp) false [:: encode_tweak P (pk_adrs P)]
    (setm emptym 0 (encode_tweak P (pk_adrs P), xs))
    (s0, set_heap (set_heap s1 tgts_loc' (setm emptym 0 (encode_tweak P (pk_adrs P), xs)))
           tws_loc' [:: encode_tweak P (pk_adrs P)]).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

(** The phase flip (GETPP's put rev). *)
Lemma cblk_set_rev (po : option (wcp_PP P)) tw tg s0 s1 :
  cblk po false tw tg (s0, s1) ->
  cblk po true tw tg (s0, set_heap s1 rev_loc' true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked COLLQ (pp pinned: state untouched) *)

Lemma r_cpcollq_known (b : bool) {B : choiceType} (pp : wcp_PP P)
    (t : tc_T (coll_pkcompress P)) (x : tc_M (coll_pkcompress P)) rv tw tg
    (c0 : raw_code B) (k1 : tc_N (coll_pkcompress P) -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (tc_eval (coll_pkcompress P) pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (resolve (SMB b) cp_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_cq b t x).
eapply (r_get_bind_rhs pp_loc' (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The loop specs (rhs-only; pp pinned, state constant) *)

(** Grinding loop: the continuation receives the honest H_grind answer
    list. *)
Lemma r_cpgrind_spec (b : bool) {B : choiceType} (pp : wcp_PP P) (m : wcp_M P)
    (cs : seq nat) rv tw tg
    (c0 : raw_code B) (k1 : chList 'nat -> raw_code B)
    (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 [seq wcp_H_grind P pp (grind_adrs P) (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (cp_grind m cs) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim: cs k1 => [|c cs IH] k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_cpcollq_known b).
  cbv beta.
  rewrite collq_H_E.
  rewrite code_link_bind bind_assoc.
  apply: IH.
  exact: h.
Qed.

(** Walk loop: the continuation receives the chain value [n] steps
    up. *)
Lemma r_cpwalk_spec (b : bool) {B : choiceType} (pp : wcp_PP P)
    (post : postcond B B) :
  forall n i k (x : wcp_N P) rv tw tg
         (c0 : raw_code B) (k1 : wcp_N P -> raw_code B),
  (k + n <= (wcp_w P).-1)%N ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (cp_walk i k n x) (SMB b)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i k x rv tw tg c0 k1 hkn h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_cpcollq_known b).
  cbv beta.
  have hk : (k < (wcp_w P).-1)%N by apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
  have hkw : (k < wcp_w P)%N by apply: (ltn_trans hk); rewrite ltn_predL; apply: (ltnW (wcp_Hw P)).
  rewrite (collq_Fc_E pp i k x hkw).
  apply: IH; first by rewrite addSnnS.
  exact: h.
Qed.

(** The per-chain spec: lhs [sample_sig_roots] at [FW] (G_post_grind's
    sampling), rhs the linked [cp_chains]; the roots are coupled
    pointwise, the results are [sigs_of]/[ends_of] of the sampled
    roots. *)
Lemma r_cpchains_spec (b : bool) {B : choiceType} (pp : wcp_PP P)
    (post : postcond B B) :
  forall ds st rv tw tg (K0 : chList (wcp_N P) -> raw_code B)
         (K1 : chList (wcp_N P) * chList (wcp_N P) -> raw_code B),
  all (λ d : nat, (d < wcp_w P)%N) ds ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
        K0 (wsigs P pp st ds us)
      ≈ K1 (wsigs P pp st ds us, wends P pp st ds (wsigs P pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), cblk (Some pp) rv tw tg (s0, s1) ⦄
     bind (sample_sig_roots (wcp_PP P) (wcp_N P) (Fw P) (wcp_dN P) pp st ds) K0
   ≈ bind (code_link (cp_chains st ds) (SMB b)) K1 ⦃ post ⦄.
Proof.
elim=> [|d ds IH] st rv tw tg K0 K1 hds h.
- exact: (h [::] erefl).
- move: hds => /= /andP[hd hds'].
  rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P)))
          !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d hd h => [|d'] hd h.
  + (* d = 0: no sigma step, walk from the root itself *)
    rewrite code_link_bind bind_assoc /=.
    rewrite code_link_bind bind_assoc.
    eapply (r_cpwalk_spec b pp post ((wcp_w P).-1 - 0) st 0 u); first by rewrite add0n subn0.
    rewrite (code_link_bind (cp_chains st.+1 ds)) bind_assoc.
    eapply IH; first exact: hds'.
    move=> us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
  + (* d = d'.+1: one COLLQ F-step to the signature position *)
    have hd'w : (d' < wcp_w P)%N := ltn_trans (ltnSn d') hd.
    have hd1 : (d'.+1 <= (wcp_w P).-1)%N by rewrite -ltnS (ltn_predK (wcp_Hw P)).
    rewrite code_link_bind bind_assoc /=.
    rewrite bind_assoc.
    eapply (r_cpcollq_known b).
    cbv beta.
    rewrite (collq_Fc_E pp st d' u hd'w) /=.
    rewrite (code_link_bind (cp_walk st d'.+1 ((wcp_w P).-1 - d'.+1)
              ((Fw P) pp (st, d') u))) bind_assoc.
    eapply (r_cpwalk_spec b pp post ((wcp_w P).-1 - d'.+1) st d'.+1
              ((Fw P) pp (st, d') u)); first by rewrite (subnKC hd1).
    rewrite /= (code_link_bind (cp_chains st.+1 ds)) bind_assoc.
    eapply IH; first exact: hds'.
    move=> us hus.
    move: (h (u :: us)); rewrite /= hus => /(_ erefl).
    exact: id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The common COMMIT tail

    By this point all sampling and all oracle interaction is over:
    both sides store key/log/signature (the same values) and return;
    the invariant is re-established from the final block state. *)

Lemma r_cp_tail (pp : wcp_PP P) (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)) :
  ⊢ ⦃ λ '(s0, s1),
        cblk (Some pp) true [:: encode_tweak P (pk_adrs P)]
          (setm emptym 0 (encode_tweak P (pk_adrs P), complete_ends P pp (digest_of P pp m c) sg))
          (s0, s1) ⦄
     (#put forge_pk_loc P := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc P := [:: m] ;;
      #put forge_sig_loc P := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c)))
   ≈ (#put r_compress_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put r_compress_log_loc := [:: m] ;;
      #put r_compress_sig_loc := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ cp_inv (s0, s1) ⦄.
Proof.
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
apply: cp_invI.
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
  by exists m, c, sg; split=> //; split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Proof-local tactics for the recurring relational leaves

    [cp_sync_pko] synchronises the [pk] location across the two games
    and substitutes it away -- the opening move of every COMMIT/KFORGE
    branch, both flags (4 sites).  [cp_ret_leaf] closes a
    both-sides-agree early return, re-establishing [cp_inv] straight
    from the six-times-remembered precondition -- every KFORGE case
    both games answer alike (7 sites; the deeper COMPRESS leaf keeps
    its own explicit destructuring). *)

Local Ltac cp_sync_pko :=
  let hi := fresh "hinv" in
  let h0 := fresh "hrem0" in
  let h1 := fresh "hrem1" in
  let pkr := fresh "pko'" in
  sync_eq pko pkr;
    [ move=> s0 s1 [[hi h0] h1];
      case/cp_invE: hi => _ [e1 _ _ _];
      rewrite /rem_inv /= in h0 h1;
      by rewrite -h0 -h1
    | move=> e; subst pkr ].

Local Ltac cp_ret_leaf :=
  let hp := fresh "hpre" in
  apply r_ret => s0 s1 hp; split=> //;
  by case: hp => [[[[[[hinv _] _] _] _] _] _].

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence *)

Lemma R_compress_real :
  perfect (I_KOTS (shrincs_wots_scheme P)) (intermediates.G_post_grind P)
    (R_compress ∘ SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1 true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ cp_inv).
{ rewrite /cp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  cp_sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), cblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/cp_invE: hinv => hign hRC.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRC => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  (* the COLLQ pin: SM-TCR's lazy pp is sampled here, against G_post_grind's
     eager one *)
  rewrite (resolve_cq true (encode_tweak P (grind_adrs P)) (inr (m, 0))).
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  (* the grinding loop through COLLQ *)
  rewrite (code_link_bind (cp_grind m (iota 0 (wcp_c_max P)))).
  eapply (r_cpgrind_spec true pp m).
  cbv beta.
  rewrite code_link_assertD (intermediates.cp_pick_map P).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (find_counter P pp m). }
  move=> e1 _.
  move: e1; case E: (find_counter P pp m) => [c|] /= e1; last by [].
  rewrite !(intermediates.digestE P).
  (* the chains through COLLQ, roots sampled locally on both sides *)
  rewrite (code_link_bind (cp_chains 0 (digest_of P pp m c))).
  eapply (r_cpchains_spec true pp).
    { by have /andP[hwf _] := find_counter_good P pp m c E; exact: hwf. }
  move=> us hus.
  cbv beta iota.
  rewrite (intermediates.wendsE P pp (digest_of P pp m c) _ (size_digest_of P pp m c)).
  simpl.
  (* the ONE TQUERY: commit the honest ends *)
  rewrite (resolve_tq true (encode_tweak P (pk_adrs P))
            (complete_ends P pp (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us))).
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
  eapply (r_get_bind_rhs tgts_loc' emptym).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_qupd pp _ _ _ hpre). }
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  rewrite !(th_evalE_Tpk P).
  (* GETPP: reveal pp, flip the phase *)
  rewrite (resolve_gp true Datatypes.tt).
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (cblk_set_rev _ _ _ _ _ hpre). }
  exact: r_cp_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  cp_sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/cp_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  sync_eq sgol sgov.
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/cp_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
            [/\ lg = [:: m], sgol = Some (sg, c)
              & pk.2 = wcp_T_sf P pk.1 (pk_adrs P) (complete_ends P pk.1 (digest_of P pk.1 m c) sg)])).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/cp_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ [hD _] _]]].
      exists mm, cc, sgg; split.
      - by rewrite -h3.
      - by rewrite -h5.
      - by rewrite hD. }
  move=> [m [c [sg [hlg hsgol hpk2]]]].
  rewrite hlg hsgol /=.
  case E0: (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + (* invalid forgery: both sides answer false *)
    cp_ret_leaf.
  + case/andP: (E0) => hver hfresh.
    case E1: ((digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m c)%B).
    * (* GRIND: both games null it (the grinding hop absorbed this case) *)
      cp_ret_leaf.
    * case E2: ((complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                 != complete_ends P pk.1 (digest_of P pk.1 m c) sg)%B); last first.
      -- (* equal ends (CHAIN cases): both sides answer true *)
         cp_ret_leaf.
      -- (* COMPRESS: CHECK answers true = G_post_grind's verdict *)
         simpl.
         rewrite (resolve_ck 0
                   (complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1)).
         eapply (r_get_bind_rhs rev_loc' true).
           { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
             case/cp_invE: hinv => _ [_ _ _ hmatch].
             rewrite /rem_inv /= in h1.
             rewrite h1 in hmatch.
             by case: hmatch => mm [cc [sgg [_ _ _ _ [_ hrv]]]]. }
         cbv beta.
         eapply r_bind_assertD_rhs; first by [].
         move=> _.
         eapply r_get_remember_rhs => tg.
         eapply (r_fact
           (tg = setm emptym 0
                   (encode_tweak P (pk_adrs P), complete_ends P pk.1 (digest_of P pk.1 m c) sg))).
           { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
             case/cp_invE: hinv => _ [_ _ e3 hmatch].
             rewrite /rem_inv /= in h1 h2 h3 h4 h5 h6 h7.
             rewrite h1 in hmatch.
             case: hmatch => mm [cc [sgg [hA hB _ [_ hC] _]]].
             have emm : mm = m.
               { have : [:: mm] = [:: m] by rewrite -hA h3.
                 by case. }
             have hsgcc : Some (sgg, cc) = Some (sg, c).
               { by rewrite -hB h5. }
             have esgg : sgg = sg by case: hsgcc.
             have ecc : cc = c by case: hsgcc.
             by rewrite -h7 hC emm ecc esgg. }
         move=> htg.
         rewrite htg setmE /=.
         eapply (r_get_rhs_known pp_loc' (Some pk.1)).
           { move=> s0 s1 [[[[[[[hinv h1] h2] h3] h4] h5] h6] h7].
             case/cp_invE: hinv => _ [_ _ _ hmatch].
             rewrite /rem_inv /= in h1.
             rewrite h1 in hmatch.
             by case: hmatch => mm [cc [sgg [_ _ hpo _ _]]]. }
         simpl.
         rewrite !(th_evalE_Tpk P).
         move: hver; rewrite /shrincs_wots_verify => /and3P[_ _ /eqP hTl].
         rewrite E2 hTl hpk2 eqxx /=.
         apply r_ret => s0 s1 hpre; split=> //.
         by case: hpre => [[[[[[[hinv _] _] _] _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence *)

Lemma R_compress_ideal :
  perfect (I_KOTS (shrincs_wots_scheme P)) (intermediates.G_post_compress P)
    (R_compress ∘ SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1 false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ cp_inv).
{ rewrite /cp_inv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: verbatim the real-side proof (the COLLQ/TQUERY/GETPP
     bodies and the loop specs are b-independent) *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  cp_sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), cblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/cp_invE: hinv => hign hRC.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRC => _ _ _; rewrite hrem0 => -[_ _ hpo htg [htw hrv]].
    by split. }
  simpl.
  rewrite (resolve_cq false (encode_tweak P (grind_adrs P)) (inr (m, 0))).
  eapply (r_get_bind_rhs pp_loc' None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  rewrite (code_link_bind (cp_grind m (iota 0 (wcp_c_max P)))).
  eapply (r_cpgrind_spec false pp m).
  cbv beta.
  rewrite code_link_assertD (intermediates.cp_pick_map P).
  refine (r_assertD _ _ _ _ _ _ _ _).
    { by move=> ? _; case: (find_counter P pp m). }
  move=> e1 _.
  move: e1; case E: (find_counter P pp m) => [c|] /= e1; last by [].
  rewrite !(intermediates.digestE P).
  rewrite (code_link_bind (cp_chains 0 (digest_of P pp m c))).
  eapply (r_cpchains_spec false pp).
    { by have /andP[hwf _] := find_counter_good P pp m c E; exact: hwf. }
  move=> us hus.
  cbv beta iota.
  rewrite (intermediates.wendsE P pp (digest_of P pp m c) _ (size_digest_of P pp m c)).
  simpl.
  rewrite (resolve_tq false (encode_tweak P (pk_adrs P))
            (complete_ends P pp (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us))).
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
  eapply (r_get_bind_rhs tgts_loc' emptym).
    { by move=> s0 s1 [_ _ _ _ h]. }
  cbv beta.
  eapply r_put2_bind_rhs.
    { move=> s0 s1 hpre; exact: (cblk_qupd pp _ _ _ hpre). }
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  rewrite !(th_evalE_Tpk P).
  rewrite (resolve_gp false Datatypes.tt).
  eapply (r_get_bind_rhs pp_loc' (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  simpl.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (cblk_set_rev _ _ _ _ _ hpre). }
  exact: r_cp_tail.
- (* KFORGE *)
  destruct arg as [mst sgst].
  simpl.
  cp_sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/cp_invE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  sync_eq sgol sgov.
    { move=> s0 s1 [[[[[[hinv _] _] _] _] hrem0] hrem1].
      case/cp_invE: hinv => _ [_ _ e3 _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst sgov.
  eapply (r_fact (exists (m : wcp_M P) (c : nat) (sg : seq (wcp_N P)),
            lg = [:: m] /\ sgol = Some (sg, c))).
    { move=> s0 s1 [[[[[[hinv h1] h2] h3] h4] h5] h6].
      case/cp_invE: hinv => _ [_ _ _ hmatch].
      rewrite /rem_inv /= in h1 h3 h5.
      rewrite h1 in hmatch.
      case: hmatch => mm [cc [sgg [hA hB _ _ _]]].
      exists mm, cc, sgg; split.
      - by rewrite -h3.
      - by rewrite -h5. }
  move=> [m [c [sg [hlg hsgol]]]].
  rewrite hlg hsgol /=.
  case E0: (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin [:: m])); last first.
  + cp_ret_leaf.
  + case E1: ((digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m c)%B).
    * cp_ret_leaf.
    * case E2: ((complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                 != complete_ends P pk.1 (digest_of P pk.1 m c) sg)%B); last first.
      -- cp_ret_leaf.
      -- (* COMPRESS: ideal CHECK answers false = G_post_compress's null *)
         simpl.
         rewrite (resolve_ck_false 0
                   (complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1)).
         cp_ret_leaf.
Qed.

End CompressHop.
