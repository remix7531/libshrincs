(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.prf_memo_real_coupling

    Fresh real memo queries return evaluations of the initialized PRF key.
    The batch coupling preserves that key and tracks the exact history and
    all-call counter. No cache-value premise is needed for fresh inputs. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.prf_memo
  games.prf_memo_state games.prf_memo_coupling games.prf_memo_real
  toolkit.relational_rules toolkit.sample_seq.
From Shrincs Require Import games.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Real.
Context (K : khf) (L : Locations).

Definition prf_memo_key_rel (qs : seq (kh_M K)) (cnt : nat) (k : kh_K K) : precond :=
  prf_memo_rel K L qs cnt ⋊ rel_app [:: (rhs, prf.prf_k_loc K)]
    (fun ko => ko = Some k).

Lemma prf_memo_key_rel_insert tab qs cnt m k s0 s1 :
  (prf_memo_tab_loc K).1 \in domm L ->
  (prf.prf_qs_loc K).1 \in domm L -> prf_memo_cnt_loc.1 \in domm L ->
  heap_ignore L (s0,s1) -> prf_memo_log K tab qs cnt ->
  get_heap s1 (prf.prf_k_loc K) = Some k ->
  prf_memo_key_rel (rcons qs m) cnt.+1 k
    (s0, set_heap
      (set_heap (set_heap s1 prf_memo_cnt_loc cnt.+1)
        (prf.prf_qs_loc K) (rcons qs m))
      (prf_memo_tab_loc K) (setm tab m (kh_eval K k m))).
Proof.
move=> ht hq hc hi hl hk.
split.
- exact: prf_memo_rel_insert ht hq hc hi hl.
- (* Preserve the initialized key. *)
  rewrite /rel_app /get_side /=.
  rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc K) _ (prf.prf_k_loc K)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc K) _ (prf.prf_k_loc K)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_k_loc K)
    ltac:(reflexivity)) at 1.
  exact: hk.
Qed.

Lemma r_prf_memo_real_fresh q qs cnt m k :
  (prf_memo_tab_loc K).1 \in domm L ->
  (prf.prf_qs_loc K).1 \in domm L -> prf_memo_cnt_loc.1 \in domm L ->
  m \notin qs -> cnt < q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_key_rel qs cnt k (s0,s1) ⦄
    ret (kh_eval K k m)
    ≈ code_link (resolve (R_prf_memo K q) (MQUERY,(kh_M K,kh_N K)) m)
        (prf.PRF_game K q true)
    ⦃ fun '(y0,s0) '(y1,s1) =>
      y0 = y1 /\ prf_memo_key_rel (rcons qs m) cnt.+1 k (s0,s1) ⦄.
Proof.
move=> ht hq hc hf hb.
apply rpre_hypothesis_rule => s0 s1 [[hi hr] hk].
rewrite /rel_app /get_side /= in hr hk.
case: hr => hqs hcnt hl.
set tab := get_heap s1 (prf_memo_tab_loc K).
have hm : getm tab m = None.
{
  case he: (getm tab m) => [y|]; last reflexivity.
  have hd := proj2 hl m.
  change ((m \in qs) = isSome (getm tab m)) in hd.
  by rewrite he (negbTE hf) in hd.
}
eapply r_pr_code_rhs with (c1' := #put prf_memo_cnt_loc := cnt.+1 ;;
  #put (prf.prf_qs_loc K) := rcons qs m ;;
  #put (prf_memo_tab_loc K) := setm tab m (kh_eval K k m) ;;
  ret (kh_eval K k m)).
{
  move=> t0 t1 [h0 h1].
  change (t1 = s1) in h1.
  subst t1.
  rewrite !Pr_code_put Pr_code_ret.
  exact: prf_memo_link_real_miss hcnt erefl hqs hk hl hb hm.
}
eapply rpre_weaken_rule with (pre := fun '(t0,t1) => t0 = s0 /\ t1 = s1);
  last by [].
eapply (@r_put_rhs (kh_N K) (kh_N K) prf_memo_cnt_loc cnt.+1 _ _
  (fun '(t0,t1) => t0=s0 /\ t1=s1)).
do 2 apply r_put_rhs.
apply r_ret.
move=> t0 t1 h.
do 3 (let t := fresh "t" in case: h => t [h ->]).
case: h => h0 h1.
subst t0 t3.
split; first reflexivity.
exact: prf_memo_key_rel_insert ht hq hc hi hl hk.
Qed.

Lemma r_prf_memo_real_queries q qs cnt ms k :
  (prf_memo_tab_loc K).1 \in domm L ->
  (prf.prf_qs_loc K).1 \in domm L -> prf_memo_cnt_loc.1 \in domm L ->
  uniq (qs ++ ms) -> cnt + size ms <= q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_key_rel qs cnt k (s0,s1) ⦄
    ret [seq kh_eval K k m | m <- ms]
    ≈ code_link (code_link (prf_memo_queries K ms) (R_prf_memo K q))
        (prf.PRF_game K q true)
    ⦃ fun '(ys0,s0) '(ys1,s1) =>
      ys0 = ys1 /\ prf_memo_key_rel (qs ++ ms) (cnt + size ms) k (s0,s1) ⦄.
Proof.
move=> ht hq hc.
elim: ms qs cnt => [|m ms ih] qs cnt hu hb.
- (* Empty query list. *)
  rewrite /= cats0 addn0.
  simplify_linking.
  apply r_ret.
  by move=> s0 s1 hr; split.
- (* Evaluate the head and recurse. *)
  rewrite /= in hb.
  rewrite /prf_memo_queries -/prf_memo_queries.
  cbn [map].
  rewrite !code_link_bind !bind_ret.
  change (ret (kh_eval K k m :: [seq kh_eval K k x | x <- ms])) with
    (y ← ret (kh_eval K k m) ;;
     ys ← ret [seq kh_eval K k x | x <- ms] ;; ret (y :: ys)).
  eapply r_bind with (mid := fun '(y0,s0) '(y1,s1) => y0 = y1 /\
    prf_memo_key_rel (rcons qs m) cnt.+1 k (s0,s1)).
  + (* Couple the head evaluation. *)
    apply: r_prf_memo_real_fresh ht hq hc _ _.
    * (* The head is fresh. *)
      move: hu.
      rewrite cat_uniq /=.
      by move/and3P=> [_ /norP [hf _] _].
    * (* The head fits the remaining budget. *)
      apply: leq_trans _ hb.
      by rewrite addnS ltnS leq_addr.
  + (* Couple the tail with the same key. *)
    move=> y0 y1.
    eapply (@r_fact ('list (kh_N K)) ('list (kh_N K)) (y0 = y1)
      (fun '(s0,s1) => y0 = y1 /\
        prf_memo_key_rel (rcons qs m) cnt.+1 k (s0,s1)));
      first by move=> s0 s1 [he hr].
    move=> ->.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
      prf_memo_key_rel (rcons qs m) cnt.+1 k (s0,s1));
      last by move=> s0 s1 [_ hr].
    rewrite !code_link_bind.
    have hu' : uniq (rcons qs m ++ ms) by rewrite cat_rcons.
    have hb' : cnt.+1 + size ms <= q by rewrite addSn -addnS.
    eapply r_bind with (mid := fun '(ys0,s0) '(ys1,s1) => ys0 = ys1 /\
      prf_memo_key_rel (rcons qs m ++ ms) (cnt.+1 + size ms) k (s0,s1)).
    * exact: ih hu' hb'.
    * (* Reassemble the output and query history. *)
      move=> ys0 ys1.
      apply r_ret.
      move=> s0 s1 [he hr]; split; first by rewrite he.
      by rewrite cat_rcons addSn -addnS in hr.
Qed.
End Real.
