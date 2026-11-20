(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.chain.tcr_extra

    All-max refusal digits cannot produce a chain-collision witness.
    Actual target calls satisfy the paper's digit-count times base bound,
    while reductions may retain the inherited larger tcr_budget. *)

From Shrincs.internal.ssprove.lib Require Import prelude chain.core.
#[local] Open Scope nat_scope.

Lemma tcr_allmax_none (PP N : choice_type) (l w : nat)
    (F : PP -> nat -> nat -> N -> N) (pp : PP)
    (mstar : seq nat) (sgs sgstar : seq N) :
  tcr_decision PP N l w F pp (nseq l w.-1) mstar sgs sgstar = None.
Proof.
rewrite /tcr_decision.
case he: (ohead _) => [i|]; last by [].
have hil : i < l.
{ have : i \in [seq i0 <- iota 0 l |
      nth 0 mstar i0 < nth 0 (nseq l w.-1) i0].
  { by case: (filter _ _) he => //= a s [<-]; rewrite in_cons eqxx. }
  by rewrite mem_filter mem_iota /= add0n => /andP[_ ->]. }
case: (qnth sgs i) => [si|]; last by [].
case: (qnth sgstar i) => [si'|]; last by [].
by rewrite nth_nseq hil /chain_extractc subnn /=.
Qed.

Lemma chain_query_count_le_base w d : 0 < w ->
  chain_query_count w d <= w.
Proof.
move=> hw.
rewrite /chain_query_count.
apply: (@leq_trans (1 + w.-1)).
- apply: leq_add; last exact: leq_subr.
  by case: (0 < d).
- by rewrite add1n (prednK hw).
Qed.

Lemma total_query_count_le_base w ds : 0 < w ->
  total_query_count w ds <= size ds * w.
Proof.
move=> hw.
rewrite /total_query_count.
have ha : all (fun n => n <= w) [seq chain_query_count w d | d <- ds].
{ apply/allP => n /mapP[d hd ->]. exact: chain_query_count_le_base hw. }
by have := sumn_all_leq _ _ ha; rewrite size_map.
Qed.

Lemma size_commit_queries (PP N : choice_type) w
    (F : PP -> nat -> nat -> N -> N) (pp : PP) st ds us :
  size us = size ds ->
  size (commit_queries PP N w F pp st ds us) = total_query_count w ds.
Proof.
elim: ds us st => [|d ds ih] [|u us] st //= [hlen].
rewrite commit_queries_cons size_cat size_chain_queries ih //.
Qed.

Lemma commit_queries_chain_range (PP N : choice_type) w
    (F : PP -> nat -> nat -> N -> N) (pp : PP) st ds us :
  all (fun t : nat * nat => (st <= t.1) && (t.1 < st + size ds))
    (unzip1 (commit_queries PP N w F pp st ds us)).
Proof.
elim: ds us st => [|d ds ih] [|u us] st //=.
rewrite commit_queries_cons unzip1_cat all_cat.
apply/andP; split.
- apply: sub_all (chain_queries_tweaks PP N w F pp st d u).
  by move=> t /= /eqP ->; rewrite leqnn addnS ltnS leq_addr.
- apply: sub_all (ih us st.+1).
  move=> t /= /andP[hl hr]; apply/andP; split.
  + exact: leq_trans (leqnSn _) hl.
  + by rewrite addnS -addSn.
Qed.
