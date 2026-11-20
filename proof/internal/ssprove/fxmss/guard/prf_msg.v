(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.prf_msg

    The concrete message PRF inherits the public game's repeated-query guard.
    Both budget and input freshness are checked before the real/ideal bit. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common guard.prf.
From Shrincs Require Import games schemes.

Import PackageNotation prf.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma shrincs_prf_msg_query_repeated_abort q
    (m : kh_M shrincs_khf_prf_msg) (answer : bool) :
  AdvOf (shrincs_prf_msg_game q)
    (guard_calls (FQUERY,
      (kh_M shrincs_khf_prf_msg, kh_N shrincs_khf_prf_msg)) m q.+1 answer) = 0%R.
Proof. exact: prf_fquery_repeated_abort. Qed.

Lemma shrincs_prf_msg_query_budget_abort q b
    (m : kh_M shrincs_khf_prf_msg) (h : heap) :
  (q <= size (get_heap h (prf_qs_loc shrincs_khf_prf_msg)))%N ->
  Pr_code (resolve (shrincs_prf_msg_game q b)
    (FQUERY, (kh_M shrincs_khf_prf_msg, kh_N shrincs_khf_prf_msg)) m) h =
    Pr_code fail h.
Proof. exact: prf_query_budget_abort. Qed.
