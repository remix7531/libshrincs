(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.prf_memo_state

    The memo adapter's cache domain is exactly the backend query log.
    Its counter bounds the number of backend queries, including after hits.
    Thus a cache miss satisfies both checks of the distinct-input game. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.prf_memo.
From Shrincs Require Import games.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section State.
Context (K : khf).

Definition prf_memo_log (tab : {fmap kh_M K -> kh_N K})
    (qs : seq (kh_M K)) (cnt : nat) : Prop :=
  size qs <= cnt /\ forall m, (m \in qs) = isSome (getm tab m).

Lemma prf_memo_log_empty : prf_memo_log emptym [::] 0.
Proof. split; first by []. by move=> m; rewrite emptymE. Qed.

Lemma prf_memo_log_hit tab qs cnt :
  prf_memo_log tab qs cnt -> prf_memo_log tab qs cnt.+1.
Proof.
move=> [hsize hdom].
split; last exact: hdom.
exact: leq_trans hsize (leqnSn cnt).
Qed.

Lemma prf_memo_log_miss tab qs cnt q m :
  prf_memo_log tab qs cnt -> cnt < q -> getm tab m = None ->
  size qs < q /\ m \notin qs.
Proof.
move=> [hsize hdom] hbudget hmiss.
split; first exact: leq_ltn_trans hsize hbudget.
by rewrite hdom hmiss.
Qed.

Lemma prf_memo_log_set tab qs cnt m y :
  prf_memo_log tab qs cnt ->
  prf_memo_log (setm tab m y) (rcons qs m) cnt.+1.
Proof.
move=> [hsize hdom].
split.
- by rewrite size_rcons ltnS.
- move=> x.
  rewrite mem_rcons setmE in_cons.
  by case: eqP => [->|hne] //=; rewrite hdom.
Qed.

Definition prf_memo_response (b : bool) (m : kh_M K) : raw_code (kh_N K) :=
  if b then
    ko ← get (prf.prf_k_loc K) ;;
    k ← match ko with
         | Some k => ret k
         | None =>
             k ← kh_dK K ;;
             #put (prf.prf_k_loc K) := Some k ;;
             ret k
         end ;;
    ret (kh_eval K k m)
  else y ← kh_dN K ;; ret y.

Lemma prf_memo_link_miss q b m h tab qs cnt :
  get_heap h (prf_memo_cnt_loc) = cnt ->
  get_heap h (prf_memo_tab_loc K) = tab ->
  get_heap h (prf.prf_qs_loc K) = qs ->
  prf_memo_log tab qs cnt -> cnt < q -> getm tab m = None ->
  Pr_code (code_link
    (resolve (R_prf_memo K q) (MQUERY, (kh_M K, kh_N K)) m)
    (prf.PRF_game K q b)) h =
  Pr_code
    (#put prf_memo_cnt_loc := cnt.+1 ;;
     #put (prf.prf_qs_loc K) := rcons qs m ;;
     y ← prf_memo_response b m ;;
     #put (prf_memo_tab_loc K) := setm tab m y ;;
     ret y) h.

Proof.
move=> hcnt htab hqs hlog hbudget hmiss.
have [hsize hfresh] := prf_memo_log_miss tab qs cnt q m hlog hbudget hmiss.
simplify_linking.
rewrite Pr_code_get hcnt hbudget /=.
rewrite Pr_code_put Pr_code_get get_set_heap_neq // htab hmiss.
simplify_linking.
rewrite Pr_code_get !get_set_heap_neq // hqs hsize hfresh /=.
rewrite [RHS]Pr_code_put.
reflexivity.
Qed.

Lemma prf_memo_link_hit q b m y h cnt :
  get_heap h prf_memo_cnt_loc = cnt -> cnt < q ->
  getm (get_heap h (prf_memo_tab_loc K)) m = Some y ->
  Pr_code (code_link
    (resolve (R_prf_memo K q) (MQUERY, (kh_M K, kh_N K)) m)
    (prf.PRF_game K q b)) h =
    dunit
      (y, set_heap h prf_memo_cnt_loc cnt.+1).
Proof.
move=> hcnt hbudget hhit.
simplify_linking.
rewrite Pr_code_get hcnt hbudget /=.
rewrite Pr_code_put Pr_code_get get_set_heap_neq // hhit.
exact: Pr_code_ret.
Qed.

Section Encoded.
Context (X : choice_type) (encode : X -> kh_M K).

Definition prf_memo_encoded (logical : {fmap X -> kh_N K})
    (tab : {fmap kh_M K -> kh_N K}) : Prop :=
  forall x, getm tab (encode x) = getm logical x.

Lemma prf_memo_encoded_empty : prf_memo_encoded emptym emptym.
Proof. by move=> x; rewrite !emptymE. Qed.

Lemma prf_memo_encoded_pin logical tab pin y :
  (forall x, encode x <> pin) ->
  prf_memo_encoded logical tab ->
  prf_memo_encoded logical (setm tab pin y).
Proof.
move=> hfresh htab x.
rewrite setmE.
case: eqP => he; last exact: htab.
exact: False_ind _ (hfresh x he).
Qed.

Lemma prf_memo_encoded_set logical tab x y :
  injective encode -> prf_memo_encoded logical tab ->
  prf_memo_encoded (setm logical x y) (setm tab (encode x) y).
Proof.
move=> hinj htab x'.
rewrite !setmE (inj_eq hinj).
by case: ifP => // _; exact: htab.
Qed.

End Encoded.

End State.
