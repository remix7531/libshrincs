(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.lib.games.prf_link

    The distinct-query PRF game as a REDUCTION to the adaptive one.

    Two PRF game pairs live in this library:

    - [Sec.lib.games.prf_adaptive] -- the CANONICAL notion.  One EVAL
      oracle capped at [q] queries; inputs are arbitrary and may
      repeat, and the ideal branch is a lazily sampled random function
      (a table).
    - [Sec.lib.games.prf] -- the DISTINCT-QUERY variant.  FQUERY
      additionally refuses a repeated input, which lets the ideal
      branch answer with a fresh sample and keep no table at all.

    The distinct-query game is the weaker experiment, so assuming it
    hard is the weaker assumption; this file PROVES that, i.e. that no
    trust is lost by keeping only the adaptive notion:

      [prf_distinct_reduce :
         AdvOf (prf.PRF_game K q) A
           = AdvOf (prf_adaptive.PRF_game K q) (A ∘ R_prf_distinct)]

    so any adaptive bound transfers verbatim to the distinct-query
    advantage, at the same query cap [q] and with no additive loss.

    ** The reduction

    [R_prf_distinct] re-implements FQUERY's bookkeeping in its OWN
    query log and forwards the surviving queries to EVAL:

      FQUERY m = { read the log; assert the cap and the freshness of
                   [m]; append [m]; return EVAL m }.

    ** The coupling invariant

    The two games count queries differently -- the distinct-query game
    keeps the query LIST, the adaptive game a COUNTER and a TABLE -- so
    the invariant ([RQ]) relates them:

      - the reduction's log mirrors the distinct game's log ([ms' = ms]);
      - the two hidden keys agree ([ko' = ko]);
      - the adaptive counter is the log's length ([cnt = size ms]);
      - the adaptive table is supported inside the log
        ([x \notin ms -> getm t x = None]).

    The last clause is what makes the IDEAL sides agree: the freshness
    assert gives [m \notin ms], hence [getm t m = None], hence the
    adaptive oracle takes its fresh-sample branch -- exactly what the
    distinct-query oracle does unconditionally.

    ** Scope

    This file is additive: it does not touch either game, so
    [Sec.axioms]'s [sha256_prf_secure] (stated over the distinct-query
    game) and every bound derived from it keep their statements.
    Retiring [Sec.lib.games.prf] in favour of the adaptive game plus
    this corollary is a separate, trust-surface-visible step. *)

From Sec.lib Require Import prelude games.thf toolkit.relational_rules.
From Sec.lib.games Require prf prf_adaptive.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section PRFLink.

(** The keyed hash under attack and the shared query cap. *)
Context (K : khf) (q : nat).

(** The distinct-query game (Sec.lib.games.prf) ... *)
Local Notation FQUERY := Sec.lib.games.prf.FQUERY.
Local Notation I_dq := (Sec.lib.games.prf.I_PRF K).
Local Notation DQ b := (Sec.lib.games.prf.PRF_game K q b).
Local Notation dq_k_loc := (Sec.lib.games.prf.prf_k_loc K).
Local Notation dq_qs_loc := (Sec.lib.games.prf.prf_qs_loc K).

(** ... and the adaptive one (Sec.lib.games.prf_adaptive). *)
Local Notation EVAL := Sec.lib.games.prf_adaptive.EVAL.
Local Notation I_ad := (Sec.lib.games.prf_adaptive.I_PRF K).
Local Notation AD b := (Sec.lib.games.prf_adaptive.PRF_game K q b).
Local Notation ad_key_loc := (Sec.lib.games.prf_adaptive.prf_key_loc K).
Local Notation ad_tab_loc := (Sec.lib.games.prf_adaptive.prf_tab_loc K).
Local Notation ad_cnt_loc := Sec.lib.games.prf_adaptive.prf_cnt_loc.

(* ------------------------------------------------------------------ *)
(** ** The reduction *)

(** R's own query log (location 90; the distinct-query game holds
    84/85, the adaptive game 31-33). *)
Definition r_prf_distinct_qs_loc := mkloc 90 ([::] : seq (kh_M K)).

(** THE reduction: FQUERY's cap and freshness bookkeeping, replayed on
    R's own log, in front of one EVAL call. *)
Definition R_prf_distinct : package I_ad I_dq :=
  [package [fmap r_prf_distinct_qs_loc ] ;
    [ FQUERY ] : { kh_M K ~> kh_N K } (m) {
      ms ← get r_prf_distinct_qs_loc ;;
      #assert (size ms < q)%N ;;
      #assert (m \notin ms) ;;
      #put r_prf_distinct_qs_loc := rcons ms m ;;
      call [ EVAL ] : { kh_M K ~> kh_N K } m
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Linked oracle bodies (resolve equations, computed once) *)

(** EVAL's opsig as committed to [I_ad]. *)
Definition evo : opsig := (EVAL, (kh_M K, kh_N K)).

Lemma resolve_ad_true (x : kh_M K) :
  resolve (AD true) evo x =
  (cnt ← get ad_cnt_loc ;;
   #assert (cnt < q)%N ;;
   #put ad_cnt_loc := cnt.+1 ;;
   ko ← get ad_key_loc ;;
   match ko with
   | Some k => ret (kh_eval K k x)
   | None =>
       k ← kh_dK K ;;
       #put ad_key_loc := Some k ;;
       ret (kh_eval K k x)
   end).
Proof. simplify_linking. reflexivity. Qed.

Lemma resolve_ad_false (x : kh_M K) :
  resolve (AD false) evo x =
  (cnt ← get ad_cnt_loc ;;
   #assert (cnt < q)%N ;;
   #put ad_cnt_loc := cnt.+1 ;;
   t ← get ad_tab_loc ;;
   match getm t x with
   | Some y => ret y
   | None =>
       y ← kh_dN K ;;
       #put ad_tab_loc := setm t x y ;;
       ret y
   end).
Proof. simplify_linking. reflexivity. Qed.

(* Keep the packages and the resolved oracle bodies folded under
   [simpl] from here on. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments Sec.lib.games.prf.PRF_game : simpl never.
#[local] Arguments Sec.lib.games.prf_adaptive.PRF_game : simpl never.
#[local] Arguments kh_eval : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The invariant (header) *)

Definition LIG : Locations :=
  [fmap dq_k_loc ; dq_qs_loc ; r_prf_distinct_qs_loc ;
        ad_key_loc ; ad_tab_loc ; ad_cnt_loc ].

Definition RQ (ko : option (kh_K K)) (ms ms' : seq (kh_M K))
    (ko' : option (kh_K K)) (t : {fmap kh_M K -> kh_N K}) (cnt : nat) : Prop :=
  [/\ ms' = ms, ko' = ko, cnt = size ms
    & forall x, x \notin ms -> getm t x = None].

Definition linv : precond :=
  heap_ignore LIG
  ⋊ rel_app [:: (lhs, dq_k_loc) ; (lhs, dq_qs_loc) ;
                (rhs, r_prf_distinct_qs_loc) ; (rhs, ad_key_loc) ;
                (rhs, ad_tab_loc) ; (rhs, ad_cnt_loc) ] RQ.

Arguments linv : simpl never.

Lemma linvE s0 s1 :
  linv (s0, s1) ->
  heap_ignore LIG (s0, s1) /\
  RQ (get_heap s0 dq_k_loc) (get_heap s0 dq_qs_loc)
     (get_heap s1 r_prf_distinct_qs_loc) (get_heap s1 ad_key_loc)
     (get_heap s1 ad_tab_loc) (get_heap s1 ad_cnt_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma linvI s0 s1 :
  heap_ignore LIG (s0, s1) ->
  RQ (get_heap s0 dq_k_loc) (get_heap s0 dq_qs_loc)
     (get_heap s1 r_prf_distinct_qs_loc) (get_heap s1 ad_key_loc)
     (get_heap s1 ad_tab_loc) (get_heap s1 ad_cnt_loc) ->
  linv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside the oracle, machinery dropped) *)

Definition blk (ko : option (kh_K K)) (ms ms' : seq (kh_M K))
    (ko' : option (kh_K K)) (t : {fmap kh_M K -> kh_N K}) (cnt : nat) : precond :=
  λ '(s0, s1),
  heap_ignore LIG (s0, s1) /\
  [/\ get_heap s0 dq_k_loc = ko, get_heap s0 dq_qs_loc = ms,
      get_heap s1 r_prf_distinct_qs_loc = ms', get_heap s1 ad_key_loc = ko'
    & [/\ get_heap s1 ad_tab_loc = t & get_heap s1 ad_cnt_loc = cnt]].

Arguments blk : simpl never.

Lemma blk_linv ko ms ms' ko' t cnt s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) -> RQ ko ms ms' ko' t cnt -> linv (s0, s1).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]] hRQ.
by apply: linvI => //; rewrite h1 h2 h3 h4 h5 h6.
Qed.

(** Resolve every [get_heap (set_heap ..)] of the six block locations
    against the write just performed. *)
Local Ltac blk_heap :=
  repeat lazymatch goal with
  | |- context [get_heap (set_heap _ ?l _) ?l] => rewrite get_set_heap_eq
  | |- context [get_heap (set_heap _ _ _) _] => rewrite get_set_heap_neq; [| done]
  end.

(** The six one-sided writes of the oracle. *)

Lemma blk_put_dq_qs ko ms ms' ko' t cnt (v : seq (kh_M K)) s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) ->
  blk ko v ms' ko' t cnt (set_heap s0 dq_qs_loc v, s1).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]]; split.
- by apply: heap_ignore_set_l hig; rewrite mem_domm.
- by blk_heap; split.
Qed.

Lemma blk_put_r_qs ko ms ms' ko' t cnt (v : seq (kh_M K)) s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) ->
  blk ko ms v ko' t cnt (s0, set_heap s1 r_prf_distinct_qs_loc v).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]]; split.
- by apply: heap_ignore_set_r hig; rewrite mem_domm.
- by blk_heap; split.
Qed.

Lemma blk_put_dq_k ko ms ms' ko' t cnt (v : option (kh_K K)) s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) ->
  blk v ms ms' ko' t cnt (set_heap s0 dq_k_loc v, s1).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]]; split.
- by apply: heap_ignore_set_l hig; rewrite mem_domm.
- by blk_heap; split.
Qed.

Lemma blk_put_ad_key ko ms ms' ko' t cnt (v : option (kh_K K)) s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) ->
  blk ko ms ms' v t cnt (s0, set_heap s1 ad_key_loc v).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]]; split.
- by apply: heap_ignore_set_r hig; rewrite mem_domm.
- by blk_heap; split.
Qed.

Lemma blk_put_ad_tab ko ms ms' ko' t cnt (v : {fmap kh_M K -> kh_N K}) s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) ->
  blk ko ms ms' ko' v cnt (s0, set_heap s1 ad_tab_loc v).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]]; split.
- by apply: heap_ignore_set_r hig; rewrite mem_domm.
- by blk_heap; split.
Qed.

Lemma blk_put_ad_cnt ko ms ms' ko' t cnt (v : nat) s0 s1 :
  blk ko ms ms' ko' t cnt (s0, s1) ->
  blk ko ms ms' ko' t v (s0, set_heap s1 ad_cnt_loc v).
Proof.
move=> [hig [h1 h2 h3 h4 [h5 h6]]]; split.
- by apply: heap_ignore_set_r hig; rewrite mem_domm.
- by blk_heap; split.
Qed.

(** The table stays supported inside the log when the log grows ... *)
Lemma fresh_rcons (t : {fmap kh_M K -> kh_N K}) (ms : seq (kh_M K)) (m : kh_M K) :
  (forall x, x \notin ms -> getm t x = None) ->
  forall x, x \notin rcons ms m -> getm t x = None.
Proof. by move=> h x; rewrite mem_rcons in_cons negb_or => /andP[_ /h]. Qed.

(** ... and when the answer to the just-logged query is memoized. *)
Lemma fresh_setm (t : {fmap kh_M K -> kh_N K}) (ms : seq (kh_M K))
    (m : kh_M K) (y : kh_N K) :
  (forall x, x \notin ms -> getm t x = None) ->
  forall x, x \notin rcons ms m -> getm (setm t m y) x = None.
Proof.
move=> h x; rewrite mem_rcons in_cons negb_or => /andP[hne hx].
by rewrite setmE (negbTE hne); apply: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Entering the oracle

    Drop the [rel_app] machinery: name the six locations' contents and
    keep the two PURE facts the invariant carries about them (the
    counter is the log's length, the table is supported inside the
    log).  Shared by both perfect lemmas below. *)

Lemma r_blk_intro {A B : choiceType} (c0 : raw_code A) (c1 : raw_code B)
    (post : postcond A B) :
  (forall (ko : option (kh_K K)) (ms : seq (kh_M K))
          (t : {fmap kh_M K -> kh_N K}) (cnt : nat),
     cnt = size ms ->
     (forall x, x \notin ms -> getm t x = None) ->
     ⊢ ⦃ λ '(s0, s1), blk ko ms ms ko t cnt (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), linv (s0, s1) ⦄ c0 ≈ c1 ⦃ post ⦄.
Proof.
move=> h.
apply rpre_hypothesis_rule => s0 s1 hpre.
case/linvE: hpre => hig [e1 e2 e3 e4].
eapply rpre_weaken_rule;
  first exact: (h (get_heap s0 dq_k_loc) (get_heap s0 dq_qs_loc)
                  (get_heap s1 ad_tab_loc) (get_heap s1 ad_cnt_loc) e3 e4).
move=> s0' s1' /= [-> ->]; split; first exact: hig.
by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE two perfect equivalences *)

Lemma R_prf_distinct_real :
  perfect I_dq (DQ true) (R_prf_distinct ∘ AD true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ linv).
{ rewrite /linv; ssprove_invariant => //. }
simplify_eq_rel m.
ssprove_code_simpl. simpl.
apply: r_blk_intro => ko ms t cnt hcnt hfresh.
(* the shared query-log bookkeeping: read, cap, freshness, append *)
eapply (r_get_lhs_known dq_qs_loc ms); first by move=> ? ? [_ [_ ? _ _ _]].
eapply (r_get_rhs_known r_prf_distinct_qs_loc ms);
  first by move=> ? ? [_ [_ _ ? _ _]].
eapply r_assertD_same => e1.
eapply r_assertD_same => e2.
eapply (r_put_lhs_pre dq_qs_loc (rcons ms m) _ (blk ko (rcons ms m) ms ko t cnt));
  first by move=> ? ? h; exact: blk_put_dq_qs h.
eapply (r_put_rhs_pre r_prf_distinct_qs_loc (rcons ms m) _
          (blk ko (rcons ms m) (rcons ms m) ko t cnt));
  first by move=> ? ? h; exact: blk_put_r_qs h.
(* the adaptive counter: its cap assert is the cap assert already spent *)
eapply (r_get_rhs_known ad_cnt_loc cnt); first by move=> ? ? [_ [_ _ _ _ [_ ?]]].
eapply r_bind_assertD_rhs; first by move=> *; rewrite hcnt.
move=> _.
eapply (r_put_bind_rhs ad_cnt_loc cnt.+1 _
          (blk ko (rcons ms m) (rcons ms m) ko t cnt.+1));
  first by move=> ? ? h; exact: blk_put_ad_cnt h.
(* the lazily sampled key, mirrored on both sides *)
eapply (r_get_lhs_known dq_k_loc ko); first by move=> ? ? [_ [? _ _ _ _]].
eapply (r_get_bind_rhs ad_key_loc ko); first by move=> ? ? [_ [_ _ _ ? _]].
case: ko => [k|].
- (* key already sampled: both sides evaluate it *)
  simpl.
  apply r_ret => s0 s1 hpre; split; first by [].
  apply: blk_linv hpre _; split=> //.
  + by rewrite size_rcons hcnt.
  + exact: fresh_rcons.
- (* first query: the two key samples couple *)
  rewrite bind_assoc.
  eapply (r_scheme_bind (kh_dK K)); first exact: prog_valid.
  move=> k; cbv beta; simpl.
  eapply (r_put_lhs_pre dq_k_loc (Some k) _
            (blk (Some k) (rcons ms m) (rcons ms m) None t cnt.+1));
    first by move=> ? ? h; exact: blk_put_dq_k h.
  eapply (r_put_rhs_pre ad_key_loc (Some k) _
            (blk (Some k) (rcons ms m) (rcons ms m) (Some k) t cnt.+1));
    first by move=> ? ? h; exact: blk_put_ad_key h.
  apply r_ret => s0 s1 hpre; split; first by [].
  apply: blk_linv hpre _; split=> //.
  + by rewrite size_rcons hcnt.
  + exact: fresh_rcons.
Qed.

Lemma R_prf_distinct_ideal :
  perfect I_dq (DQ false) (R_prf_distinct ∘ AD false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ linv).
{ rewrite /linv; ssprove_invariant => //. }
simplify_eq_rel m.
ssprove_code_simpl. simpl.
apply: r_blk_intro => ko ms t cnt hcnt hfresh.
(* the shared query-log bookkeeping (verbatim as on the real side) *)
eapply (r_get_lhs_known dq_qs_loc ms); first by move=> ? ? [_ [_ ? _ _ _]].
eapply (r_get_rhs_known r_prf_distinct_qs_loc ms);
  first by move=> ? ? [_ [_ _ ? _ _]].
eapply r_assertD_same => e1.
eapply r_assertD_same => e2.
eapply (r_put_lhs_pre dq_qs_loc (rcons ms m) _ (blk ko (rcons ms m) ms ko t cnt));
  first by move=> ? ? h; exact: blk_put_dq_qs h.
eapply (r_put_rhs_pre r_prf_distinct_qs_loc (rcons ms m) _
          (blk ko (rcons ms m) (rcons ms m) ko t cnt));
  first by move=> ? ? h; exact: blk_put_r_qs h.
eapply (r_get_rhs_known ad_cnt_loc cnt); first by move=> ? ? [_ [_ _ _ _ [_ ?]]].
eapply r_bind_assertD_rhs; first by move=> *; rewrite hcnt.
move=> _.
eapply (r_put_bind_rhs ad_cnt_loc cnt.+1 _
          (blk ko (rcons ms m) (rcons ms m) ko t cnt.+1));
  first by move=> ? ? h; exact: blk_put_ad_cnt h.
(* THE step: the freshness assert makes the lazy table MISS, so the
   adaptive oracle samples -- exactly what the distinct-query one does *)
eapply (r_get_bind_rhs ad_tab_loc t); first by move=> ? ? [_ [_ _ _ _ [? _]]].
rewrite (hfresh m e2).
cbv iota.
rewrite bind_assoc.
eapply (r_scheme_bind (kh_dN K)); first exact: prog_valid.
move=> y; cbv beta; simpl.
eapply (r_put_rhs_pre ad_tab_loc (setm t m y) _
          (blk ko (rcons ms m) (rcons ms m) ko (setm t m y) cnt.+1));
  first by move=> ? ? h; exact: blk_put_ad_tab h.
apply r_ret => s0 s1 hpre; split; first by [].
apply: blk_linv hpre _; split=> //.
- by rewrite size_rcons hcnt.
- exact: fresh_setm.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The corollary *)

Lemma prf_distinct_reduce (A : nom_package)
    (VA : ValidPackage (loc A) I_dq A_export A) :
  AdvOf (Sec.lib.games.prf.PRF_game K q) A
    = AdvOf (Sec.lib.games.prf_adaptive.PRF_game K q) (A ∘ R_prf_distinct).
Proof.
rewrite (Adv_perfect_l R_prf_distinct_real).
rewrite (Adv_perfect_r R_prf_distinct_ideal).
by rewrite Adv_reduction.
Qed.

End PRFLink.
