(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.prf_memo

    A memoizing reduction to the public distinct-input PRF game. The local
    budget counts every call, including cache hits; only misses call FQUERY.
    Linking this adapter preserves advantage exactly, with no extra term. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import games.
From mathcomp Require Import reals.
From mathcomp.experimental_reals Require Import distr.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Memo.
Context (K : khf) (q : nat).

Definition MQUERY : nat := 1020.
Definition prf_memo_tab_loc :=
  mkloc 1020 (emptym : {fmap kh_M K -> kh_N K}).
Definition prf_memo_cnt_loc := mkloc 1021 (0 : nat).
Definition I_PRF_memo := [interface [ MQUERY ] : { kh_M K ~> kh_N K } ].

Definition R_prf_memo : package (prf.I_PRF K) I_PRF_memo :=
  [package [fmap prf_memo_tab_loc ; prf_memo_cnt_loc ] ;
    [ MQUERY ] : { kh_M K ~> kh_N K } (m) {
      cnt ← get prf_memo_cnt_loc ;;
      #assert (cnt < q)%N ;;
      #put prf_memo_cnt_loc := cnt.+1 ;;
      tab ← get prf_memo_tab_loc ;;
      match getm tab m with
      | Some y => ret y
      | None =>
          y ← (call [ prf.FQUERY ] : { kh_M K ~> kh_N K } m) ;;
          #put prf_memo_tab_loc := setm tab m y ;;
          ret y
      end
    }
  ].

Lemma resolve_prf_memo (m : kh_M K) :
  resolve R_prf_memo (MQUERY, (kh_M K, kh_N K)) m =
  (cnt ← get prf_memo_cnt_loc ;;
   #assert (cnt < q)%N ;;
   #put prf_memo_cnt_loc := cnt.+1 ;;
   tab ← get prf_memo_tab_loc ;;
   match getm tab m with
   | Some y => ret y
   | None =>
       y ← (call [ prf.FQUERY ] : { kh_M K ~> kh_N K } m) ;;
       #put prf_memo_tab_loc := setm tab m y ;;
       ret y
   end).
Proof. simplify_linking. reflexivity. Qed.

(** Hits increment the counter and neither call nor modify the backend. *)
Lemma prf_memo_hit (m : kh_M K) (y : kh_N K) (h : heap) (cnt : nat) :
  get_heap h prf_memo_cnt_loc = cnt ->
  (cnt < q)%N ->
  getm (get_heap h prf_memo_tab_loc) m = Some y ->
  Pr_code (resolve R_prf_memo (MQUERY, (kh_M K, kh_N K)) m) h =
    dunit (y, set_heap h prf_memo_cnt_loc cnt.+1).
Proof.
move=> hcnt hbudget hhit.
rewrite resolve_prf_memo Pr_code_get hcnt hbudget /=.
rewrite Pr_code_put Pr_code_get get_set_heap_neq // hhit.
exact: Pr_code_ret.
Qed.

(** Budget exhaustion refuses even a cached input, independently of a bit. *)
Lemma prf_memo_budget_abort (m : kh_M K) (h : heap) :
  (q <= get_heap h prf_memo_cnt_loc)%N ->
  Pr_code (resolve R_prf_memo (MQUERY, (kh_M K, kh_N K)) m) h = dnull.
Proof.
move=> hbudget.
rewrite resolve_prf_memo Pr_code_get ltnNge hbudget /=.
by rewrite Pr_code_sample dlet_null_ext.
Qed.

End Memo.
