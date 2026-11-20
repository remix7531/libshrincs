(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.prf_memo_real

    Real memo responses agree with the stored PRF key. Cache hits and
    misses expose their exact heap updates without expanding callers. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.prf_memo
  games.prf_memo_state.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Real.
Context (K : khf).

Definition prf_memo_eval (tab : {fmap kh_M K -> kh_N K}) (k : kh_K K) : Prop :=
  forall m y, getm tab m = Some y -> y = kh_eval K k m.

Lemma prf_memo_eval_empty k : prf_memo_eval emptym k.
Proof. move=> m y. by rewrite emptymE. Qed.

Lemma prf_memo_eval_set tab k m :
  prf_memo_eval tab k ->
  prf_memo_eval (setm tab m (kh_eval K k m)) k.
Proof.
move=> he x y. rewrite setmE.
case: eqP => [->|hne]; first by case=> <-.
exact: he.
Qed.

Lemma prf_memo_link_real_miss q m h tab qs cnt k :
  get_heap h prf_memo_cnt_loc = cnt ->
  get_heap h (prf_memo_tab_loc K) = tab ->
  get_heap h (prf.prf_qs_loc K) = qs ->
  get_heap h (prf.prf_k_loc K) = Some k ->
  prf_memo_log K tab qs cnt -> cnt < q -> getm tab m = None ->
  Pr_code (code_link
    (resolve (R_prf_memo K q) (MQUERY, (kh_M K, kh_N K)) m)
    (prf.PRF_game K q true)) h =
  dunit (kh_eval K k m,
    set_heap
      (set_heap (set_heap h prf_memo_cnt_loc cnt.+1)
        (prf.prf_qs_loc K) (rcons qs m))
      (prf_memo_tab_loc K) (setm tab m (kh_eval K k m))).
Proof.
move=> hc ht hq hk hl hb hm.
rewrite (prf_memo_link_miss K q true m h tab qs cnt hc ht hq hl hb hm).
rewrite /prf_memo_response !Pr_code_put /= Pr_code_get.
rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc K) _ (prf.prf_k_loc K)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_k_loc K)
  ltac:(reflexivity)) at 1.
by rewrite hk /= Pr_code_put Pr_code_ret.
Qed.

Lemma prf_memo_link_real_hit q m h cnt k y :
  get_heap h prf_memo_cnt_loc = cnt -> cnt < q ->
  prf_memo_eval (get_heap h (prf_memo_tab_loc K)) k ->
  getm (get_heap h (prf_memo_tab_loc K)) m = Some y ->
  Pr_code (code_link
    (resolve (R_prf_memo K q) (MQUERY, (kh_M K, kh_N K)) m)
    (prf.PRF_game K q true)) h =
  dunit (kh_eval K k m, set_heap h prf_memo_cnt_loc cnt.+1).
Proof.
move=> hc hb he hh.
rewrite (prf_memo_link_hit K q true m y h cnt hc hb hh).
by rewrite (he m y hh).
Qed.
End Real.
