(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.prf_memo_coupling

    Fresh distinct-input memo queries couple to independent ideal samples.
    The relation records the query history and all-call counter. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.prf_memo
  games.prf_memo_state toolkit.relational_rules toolkit.sample_seq.
From Shrincs Require Import games.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Memo.
Context (K : khf) (L : Locations).

Definition prf_memo_rel (qs : seq (kh_M K)) (cnt : nat) : precond :=
  heap_ignore L ⋊ rel_app
    [:: (rhs, prf_memo_tab_loc K); (rhs, prf.prf_qs_loc K);
        (rhs, prf_memo_cnt_loc)]
    (fun tab qs' cnt' => [/\ qs' = qs, cnt' = cnt & prf_memo_log K tab qs cnt]).

Lemma prf_memo_rel_insert tab qs cnt m y s0 s1 :
  (prf_memo_tab_loc K).1 \in domm L ->
  (prf.prf_qs_loc K).1 \in domm L -> prf_memo_cnt_loc.1 \in domm L ->
  heap_ignore L (s0,s1) -> prf_memo_log K tab qs cnt ->
  prf_memo_rel (rcons qs m) cnt.+1
    (s0, set_heap
      (set_heap (set_heap s1 prf_memo_cnt_loc cnt.+1)
        (prf.prf_qs_loc K) (rcons qs m))
      (prf_memo_tab_loc K) (setm tab m y)).
Proof.
move=> ht hq hc hi hl.
split.
- (* Preserve the untouched heap. *)
  apply: heap_ignore_set_r ht _.
  apply: heap_ignore_set_r hq _.
  exact: heap_ignore_set_r hc hi.
- (* Update the memo table and query log. *)
  rewrite !rel_app_cons /= rel_app_nil.
  rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc K) _ (prf.prf_qs_loc K)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_eq _ (prf.prf_qs_loc K) _) at 1.
  rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc K) _ prf_memo_cnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc K) _ prf_memo_cnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_eq _ prf_memo_cnt_loc _) at 1.
  rewrite -> (get_set_heap_eq _ (prf_memo_tab_loc K) _) at 1.
  split; try reflexivity.
  exact: prf_memo_log_set hl.
Qed.

Lemma r_prf_memo_ideal_fresh q qs cnt m :
  (prf_memo_tab_loc K).1 \in domm L ->
  (prf.prf_qs_loc K).1 \in domm L -> prf_memo_cnt_loc.1 \in domm L ->
  m \notin qs -> cnt < q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_rel qs cnt (s0,s1) ⦄
    kh_dN K
    ≈ code_link (resolve (R_prf_memo K q) (MQUERY,(kh_M K,kh_N K)) m)
        (prf.PRF_game K q false)
    ⦃ fun '(y0,s0) '(y1,s1) =>
      y0 = y1 /\ prf_memo_rel (rcons qs m) cnt.+1 (s0,s1) ⦄.
Proof.
move=> htl hql hcl hf hb.
apply rpre_hypothesis_rule => s0 s1 [hi hr].
rewrite /rel_app /get_side /= in hr.
case: hr => hq hc hl.
set tab := get_heap s1 (prf_memo_tab_loc K).
have hm : getm tab m = None.
{
  case he: (getm tab m) => [y|]; last reflexivity.
  have hd := proj2 hl m.
  change ((m \in qs) = isSome (getm tab m)) in hd.
  by rewrite he (negbTE hf) in hd.
}
eapply r_pr_code_rhs with (c1' := #put prf_memo_cnt_loc := cnt.+1 ;; #put
  (prf.prf_qs_loc K) := rcons qs m ;; y ← prf_memo_response K false m ;; #put
  (prf_memo_tab_loc K) := setm tab m y ;; ret y).
{
  move=> t0 t1 [h0 h1].
  change (t1 = s1) in h1.
  subst t1.
  exact: (prf_memo_link_miss K q false m s1 tab qs cnt hc erefl hq hl hb hm).
}
rewrite /prf_memo_response.
ssprove_code_simpl.
eapply rpre_weaken_rule with (pre := fun '(t0,t1) => t0 = s0 /\ t1 = s1); last by [].
eapply (@r_put_rhs (kh_N K) (kh_N K) prf_memo_cnt_loc cnt.+1 _ _ (fun '(t0,t1) =>
  t0=s0 /\ t1=s1)).
apply r_put_rhs.
rewrite <- (@bind_ret (kh_N K) (kh_dN K)) at 1.
eapply r_scheme_bind; first exact: prog_valid.
move=> y; cbv beta.
apply r_put_rhs.
apply r_ret.
move=> t0 t1 h.
do 3 (let t := fresh "t" in case: h => t [h ->]).
case: h => h0 h1.
subst t0 t3.
split; first reflexivity.
exact: prf_memo_rel_insert htl hql hcl hi hl.
Qed.

Fixpoint prf_memo_queries (ms : seq (kh_M K)) : raw_code ('list (kh_N K)) :=
  match ms with
  | [::] => ret [::]
  | m :: rest =>
      y ← (call [ MQUERY ] : { kh_M K ~> kh_N K } m) ;;
      ys ← prf_memo_queries rest ;;
      ret (y :: ys)
  end.

Lemma r_prf_memo_ideal_queries q qs cnt ms :
  (prf_memo_tab_loc K).1 \in domm L ->
  (prf.prf_qs_loc K).1 \in domm L -> prf_memo_cnt_loc.1 \in domm L ->
  uniq (qs ++ ms) -> cnt + size ms <= q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_rel qs cnt (s0,s1) ⦄
    sample_seq (kh_dN K) (size ms)
    ≈ code_link (code_link (prf_memo_queries ms) (R_prf_memo K q))
        (prf.PRF_game K q false)
    ⦃ fun '(ys0,s0) '(ys1,s1) =>
      ys0 = ys1 /\ prf_memo_rel (qs ++ ms) (cnt + size ms) (s0,s1) ⦄.
Proof.
move=> htl hql hcl.
elim: ms qs cnt => [|m ms ih] qs cnt hu hb.
- (* Empty query list. *)
  rewrite /= cats0 addn0.
  simplify_linking.
  apply r_ret.
  by move=> s0 s1 hr; split.
- (* Fresh head query followed by the tail. *)
  rewrite /= in hb.
  rewrite /prf_memo_queries -/prf_memo_queries.
  rewrite /sample_seq -/sample_seq.
  cbn [size sample_seq].
  (rewrite !code_link_bind).
  rewrite !bind_ret.
  eapply r_bind with (mid := fun '(y0,s0) '(y1,s1) => y0 = y1 /\ prf_memo_rel (rcons
    qs m) cnt.+1 (s0,s1)).
  + (* Couple the head query. *)
    apply: r_prf_memo_ideal_fresh htl hql hcl _ _.
    * (* The head is fresh. *)
      move: hu.
      rewrite cat_uniq /=.
      by move/and3P=> [_ /norP [hf _] _].
    * (* The head fits the remaining budget. *)
      apply: leq_trans _ hb.
      by rewrite addnS ltnS leq_addr.
  + (* Couple the remaining queries. *)
    move=> y0 y1.
    eapply (@r_fact ('list (kh_N K)) ('list (kh_N K)) (y0 = y1) (fun '(s0,s1) => y0 =
      y1 /\ prf_memo_rel (rcons qs m) cnt.+1 (s0,s1))); first by move=> s0 s1 [he hr].
    move=> ->.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_memo_rel (rcons qs m)
      cnt.+1 (s0,s1)); last by move=> s0 s1 [_ hr].
    rewrite !code_link_bind.
    have hu' : uniq (rcons qs m ++ ms) by rewrite cat_rcons.
    have hb' : cnt.+1 + size ms <= q by rewrite addSn -addnS.
    eapply r_bind with (mid := fun '(ys0,s0) '(ys1,s1) => ys0 = ys1 /\ prf_memo_rel
      (rcons qs m ++ ms) (cnt.+1 + size ms) (s0,s1)).
    * (* Apply the induction hypothesis to the tail. *)
      exact: (ih (rcons qs m) cnt.+1 hu' hb').
    * (* Reassemble the output and query history. *)
      move=> ys0 ys1.
      apply r_ret.
      move=> s0 s1 [he hr]; split; first by rewrite he.
      by rewrite cat_rcons addSn -addnS in hr.
Qed.

Lemma prf_memo_queries_valid ls ms :
  ValidCode ls (I_PRF_memo K) (prf_memo_queries ms).
Proof.
elim: ms => [|m ms ih]; first exact: valid_ret.
cbn [prf_memo_queries].
eapply valid_opr; first by fmap_solve.
move=> y.
eapply valid_bind; first exact: ih.
move=> ys.
exact: valid_ret.
Qed.
#[export] Existing Instance prf_memo_queries_valid.
End Memo.
