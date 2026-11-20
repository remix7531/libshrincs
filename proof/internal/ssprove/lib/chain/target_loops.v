(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.chain.target_loops

    Oracle-routed chain walks and re-rooted signature sampling. The
    relational induction takes a local target-query contract, separating
    the generic chain bookkeeping from concrete address encodings and
    the caller's already committed target prefix. *)

From Shrincs.internal.ssprove.lib Require Import prelude chain.core
  toolkit.relational_rules.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Oracle-routed walks and their contracts *)

Section Loops.
Context (PP N : choice_type) (l w p : nat).
Context (F : PP -> nat -> nat -> N -> N) (dN : dist N).
Context (query : nat -> nat -> N -> raw_code N).

Fixpoint target_walk (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1 then
    y ← query i k x ;; target_walk i k.+1 n' y
  else ret x.

Fixpoint target_chains (st : nat) (ds : seq nat) :
    raw_code (chList N × chList N) :=
  match ds with
  | [::] => ret ([::], [::])
  | d :: ds' =>
    u ← dN ;;
    s ← (if d is d'.+1 then query st d' u else ret u) ;;
    e ← target_walk st d (w.-1 - d) s ;;
    '(ss, es) ← target_chains st.+1 ds' ;;
    ret (s :: ss, e :: es)
  end.

Lemma target_walk_valid L I :
  (forall i k x, ValidCode L I (query i k x)) ->
  forall n i k x, ValidCode L I (target_walk i k n x).
Proof.
move=> hquery.
elim=> [|n ih] i k x /=; first exact: valid_ret.
eapply valid_bind; first exact: hquery.
move=> y; exact: ih.
Qed.

Lemma target_chains_valid L I :
  (forall i k x, ValidCode L I (query i k x)) ->
  forall ds st, ValidCode L I (target_chains st ds).
Proof.
move=> hquery.
elim=> [|d ds ih] st /=; first exact: valid_ret.
eapply valid_bind; first by eapply valid_scheme, prog_valid.
move=> u; eapply valid_bind.
- (* Produce the signature element for the head digit. *)
  case: d => [|d']; first exact: valid_ret.
  exact: hquery.
- (* Walk the remaining chain and recurse on the digit list. *)
  move=> s; eapply valid_bind; first by apply: target_walk_valid.
  move=> e; eapply valid_bind; first exact: ih.
  move=> [ss es]; exact: valid_ret.
Qed.

Local Abbreviation qentry := ((nat * nat) * N)%type.

Definition target_query_spec (pp : PP) (state : seq qentry -> precond)
    {B : choiceType} (post : postcond B B) :=
  forall i k x Q (c0 : raw_code B) (k1 : N -> raw_code B),
  i < l -> k < w.-1 ->
  all (fun t : nat * nat => (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  size Q < p -> (i, k) \notin unzip1 Q ->
  ⊢ ⦃ fun '(s0, s1) => state (rcons Q ((i, k), x)) (s0, s1) ⦄
    c0 ≈ k1 (Fc PP N w F pp (i, k) x) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(s0, s1) => state Q (s0, s1) ⦄
    c0 ≈ bind (query i k x) k1 ⦃ post ⦄.

Lemma target_walk_spec {B : choiceType} (pp : PP) (state : seq qentry -> precond)
    (post : postcond B B) :
  target_query_spec pp state post ->
  forall n i k (x : N) (Q : seq qentry) (c0 : raw_code B)
         (k1 : N -> raw_code B),
  (i < l)%N ->
  (k + n <= w.-1)%N ->
  all (λ t : nat * nat, (t.1 < l)%N && (t.2 < w.-1)%N) (unzip1 Q) ->
  (size Q + n <= p)%N ->
  all (tweak_lt i k) (unzip1 Q) ->
  ⊢ ⦃ λ '(s0, s1), state
         (Q ++ walkq PP N w F pp i k n x) (s0, s1) ⦄
     c0 ≈ k1 (chainc PP N w F pp i x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), state Q (s0, s1) ⦄
     c0 ≈ bind (target_walk i k n x) k1 ⦃ post ⦄.
Proof.
move=> hquery.
elim=> [|n IH] i k x Q c0 k1 hi hkn hQr hbud hfresh h.
- by move: h; rewrite cats0.
- (* Extend the query prefix by one chain step. *)
  rewrite /= bind_assoc.
  have hk : (k < w.-1)%N by apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
  eapply hquery => //.
  + by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + exact: tlt_notin hfresh.
  + apply: IH => //.
    * by rewrite addSnnS.
    * rewrite /unzip1 map_rcons all_rcons hQr /=.
      by rewrite hi hk.
    * by rewrite size_rcons addSnnS.
    * rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
      -- by rewrite /tweak_lt /= ltnn eqxx ltnSn.
      -- exact: all_tlt_widen hfresh.
    * by move: h; rewrite (walkq_cons PP N w F) cat_rcons.
Qed.

Lemma target_chains_spec {B : choiceType} (pp : PP) (state : seq qentry -> precond)
    (post : postcond B B) :
  0 < w -> target_query_spec pp state post ->
  forall ds st (Q : seq qentry) (K0 : chList N -> raw_code B)
         (K1 : chList N * chList N -> raw_code B),
  (st + size ds <= l)%N ->
  all (λ d : nat, (d < w)%N) ds ->
  all (λ t : nat * nat, (t.1 < l)%N && (t.2 < w.-1)%N) (unzip1 Q) ->
  (size Q + total_query_count w ds <= p)%N ->
  all (λ t : nat * nat, t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ λ '(s0, s1), state
            (Q ++ (commit_queries PP N w F) pp st ds us) (s0, s1) ⦄
        K0 ((sigs_of PP N w F) pp st ds us)
      ≈ K1 ((sigs_of PP N w F) pp st ds us, (ends_of PP N w F) pp st ds ((sigs_of PP N w F) pp st ds us))
     ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), state Q (s0, s1) ⦄
     bind (sample_sig_roots PP N w F dN pp st ds) K0
   ≈ bind (target_chains st ds) K1 ⦃ post ⦄.
Proof.
move=> hw0 hquery.
elim=> [|d ds IH] st Q K0 K1 hst hds hQr hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- (* Nonempty chain list: sample the root and handle its digit. *)
  move: hst => /=; rewrite addnS => hst2.
  have hstcc : (st < l)%N := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : (st.+1 + size ds <= l)%N := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /=.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> u; cbv beta; rewrite !bind_assoc.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* d = 0 : no sigma query, walk from the root itself.  The range
       side conditions ([st < chain_count], positions [< w.-1]) are
       [have]d into context so the [eapply .. => //] discharges them by
       assumption; only the budget / freshness / continuation goals
       remain as bullets. *)
    have hkn0 : (0 + (w.-1 - 0) <= w.-1)%N by rewrite add0n subn0.
    rewrite /= ?bind_assoc.
    eapply (target_walk_spec pp state post hquery (w.-1 - 0) st 0 u Q) => //.
    * apply: leq_trans hbud.
      by rewrite leq_add2l /total_query_count /= /chain_query_count /= leq_addr.
    * exact: all_lt_tlt.
    * rewrite bind_assoc.
      eapply IH => //.
      -- rewrite unzip1_cat all_cat; apply/andP; split; first exact: hQr.
         apply/allP => t ht; apply/andP; split.
         ++ by move: (allP (walkq_tweak1 PP N w F pp st 0 (w.-1 - 0) u) t ht) => /eqP ->.
         ++ exact: (allP (walkq_tweak2 PP N w F pp st 0 (w.-1 - 0) u w.-1 hkn0) t ht).
      -- by rewrite size_cat size_walkq -addnA.
      -- rewrite unzip1_cat all_cat; apply/andP; split.
         ++ by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ apply: sub_all (walkq_tweak1 PP N w F pp st 0 _ u) => t /= /eqP ->.
            exact: ltnSn.
      -- move=> us hus.
         move: (h (u :: us)); rewrite /= hus => /(_ erefl).
         by rewrite  (commit_queries_cons PP N w F) /chain_queries /= catA.
  + (* d = d'.+1 : sigma query first ([d' < w.-1] from [d = d'.+1 < w]). *)
    have hdw1 : (d'.+1 <= w.-1)%N by rewrite -ltnS prednK.
    have hkn1 : (d'.+1 + (w.-1 - d'.+1) <= w.-1)%N by rewrite subnKC.
    rewrite /= ?bind_assoc.
    eapply hquery => //.
    * apply: leq_trans hbud.
      by rewrite addnS ltnS leq_addr.
    * exact: lt_notin.
    * rewrite /= bind_assoc.
      eapply (target_walk_spec pp state post hquery (w.-1 - d'.+1) st d'.+1
                (Fc PP N w F pp (st, d') u) (rcons Q ((st, d'), u))) => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstcc hdw1.
      -- rewrite size_rcons addSnnS; apply: leq_trans hbud.
         by rewrite leq_add2l /total_query_count /= /chain_query_count /= add1n addSn ltnS leq_addr.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /tweak_lt /= ltnn eqxx ltnSn.
         ++ exact: all_lt_tlt.
      -- (* Extend the query prefix by one chain step. *)
  rewrite /= bind_assoc.
         eapply IH => //.
         ++ rewrite unzip1_cat all_cat; apply/andP; split.
            ** rewrite /unzip1 map_rcons all_rcons hQr /=.
               by rewrite hstcc hdw1.
            ** apply/allP => t ht; apply/andP; split.
               --- by move: (allP (walkq_tweak1 PP N w F pp st d'.+1
                             (w.-1 - d'.+1) (Fc PP N w F pp (st, d') u)) t ht) => /eqP ->.
               --- exact: (allP (walkq_tweak2 PP N w F pp st d'.+1
                             (w.-1 - d'.+1) (Fc PP N w F pp (st, d') u) w.-1 hkn1) t ht).
         ++ rewrite size_cat size_rcons size_walkq.
            apply: leq_trans hbud.
            by rewrite addSnnS -addnA leq_add2l /total_query_count /= /chain_query_count /= add1n.
         ++ rewrite unzip1_cat all_cat /unzip1 map_rcons all_rcons.
            apply/andP; split; last first.
            ** apply: sub_all (walkq_tweak1 PP N w F pp st d'.+1 _ _)
                 => t /= /eqP ->.
               exact: ltnSn.
            ** apply/andP; split; first by rewrite /= ltnSn.
               by apply: sub_all hfresh => t /= /ltnW; rewrite ltnS.
         ++ move=> us hus.
            move: (h (u :: us)); rewrite /= hus => /(_ erefl).
            by rewrite  (commit_queries_cons PP N w F) /chain_queries
                       cat_rcons catA.
Qed.

End Loops.

(* ------------------------------------------------------------------ *)
(** ** Linking the target loops *)

Lemma target_walk_link (N : choice_type)
    (query : nat -> nat -> N -> raw_code N) (pkg : raw_package) n i k x :
  code_link (target_walk N query i k n x) pkg =
  target_walk N (fun i k x => code_link (query i k x) pkg) i k n x.
Proof.
elim: n i k x => [|n ih] i k x //=.
rewrite code_link_bind; apply: f_equal.
by apply: functional_extensionality => y; apply: ih.
Qed.

Lemma target_chains_link (N : choice_type) w (dN : dist N)
    (query : nat -> nat -> N -> raw_code N) (pkg : raw_package) ds st :
  code_link (target_chains N w dN query st ds) pkg =
  target_chains N w dN (fun i k x => code_link (query i k x) pkg) st ds.
Proof.
elim: ds st => [|d ds ih] st //=.
rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
apply: f_equal; apply: functional_extensionality => u.
rewrite code_link_bind.
have hsig : code_link (if d is d'.+1 then query st d' u else ret u) pkg =
  if d is d'.+1 then code_link (query st d' u) pkg else ret u by case: d.
rewrite hsig; apply: f_equal; apply: functional_extensionality => s.
rewrite code_link_bind target_walk_link.
apply: f_equal; apply: functional_extensionality => e.
rewrite code_link_bind ih.
apply: f_equal; apply: functional_extensionality => [[ss es]].
by [].
Qed.
