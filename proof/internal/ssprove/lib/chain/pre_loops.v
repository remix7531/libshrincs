(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.chain.pre_loops

    Batch preimage sampling with an abstract hidden-input oracle.
    Positive digits consume one target; zero digits sample locally.
    Completion is deliberately absent until the caller reveals the seed. *)

From Shrincs.internal.ssprove.lib Require Import prelude chain.core
  toolkit.relational_rules.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Loops.
Context (PP N : choice_type) (l w p : nat).
Context (F : PP -> nat -> nat -> N -> N) (dN : dist N).
Context (query : nat -> nat -> raw_code N).

Fixpoint pre_chains (st : nat) (ds : seq nat) : raw_code (chList N) :=
  match ds with
  | [::] => ret [::]
  | d :: ds' =>
    s ← (if d is d'.+1 then query st d' else dN) ;;
    ss ← pre_chains st.+1 ds' ;;
    ret (s :: ss)
  end.

Lemma pre_chains_valid L I :
  (forall i k, ValidCode L I (query i k)) ->
  forall ds st, ValidCode L I (pre_chains st ds).
Proof.
move=> hquery.
elim=> [|d ds ih] st /=; first exact: valid_ret.
eapply valid_bind.
- (* Query a positive digit; sample a zero digit locally. *)
  case: d => [|d']; first by eapply valid_scheme, prog_valid.
  exact: hquery.
- (* Recurse and prepend the sampled signature element. *)
  move=> s; eapply valid_bind; first exact: ih.
  move=> ss; exact: valid_ret.
Qed.

Local Abbreviation qentry := ((nat * nat) * N)%type.

Definition pre_query_spec (pp : PP) (state : seq qentry -> precond)
    {B : choiceType} (post : postcond B B) :=
  forall i k Q (k0 k1 : N -> raw_code B),
  i < l -> k < w.-1 ->
  all (fun t : nat * nat => (t.1 < l) && (t.2 < w.-1)) (unzip1 Q) ->
  size Q < p -> (i, k) \notin unzip1 Q ->
  (forall x,
    ⊢ ⦃ fun '(s0, s1) => state (rcons Q ((i, k), x)) (s0, s1) ⦄
      k0 x ≈ k1 (Fc PP N w F pp (i, k) x) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(s0, s1) => state Q (s0, s1) ⦄
    bind dN k0 ≈ bind (query i k) k1 ⦃ post ⦄.

Lemma pre_chains_spec {B : choiceType} (pp : PP) (state : seq qentry -> precond)
    (post : postcond B B) :
  0 < w -> pre_query_spec pp state post ->
  forall ds st (Q : seq qentry) (K0 K1 : chList N -> raw_code B),
  (st + size ds <= l)%N ->
  all (fun d => (d < w)%N) ds ->
  all (fun t : nat * nat => (t.1 < l)%N && (t.2 < w.-1)%N) (unzip1 Q) ->
  (size Q + preimage_query_count ds <= p)%N ->
  all (fun t : nat * nat => t.1 < st) (unzip1 Q) ->
  (forall us, size us = size ds ->
     ⊢ ⦃ fun '(s0, s1) => state
            (Q ++ pre_queries N st ds us) (s0, s1) ⦄
        K0 (sigs_of PP N w F pp st ds us)
      ≈ K1 (sigs_of PP N w F pp st ds us) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(s0, s1) => state Q (s0, s1) ⦄
     bind (sample_sig_roots PP N w F dN pp st ds) K0
   ≈ bind (pre_chains st ds) K1 ⦃ post ⦄.
Proof.
move=> hw0 hquery.
elim=> [|d ds IH] st Q K0 K1 hst hds hQr hbud hfresh h.
- by move: (h [::] erefl); rewrite cats0.
- (* Nonempty chain list: handle the head digit. *)
  move: hst => /=; rewrite addnS => hst2.
  have hstcc : (st < l)%N := leq_ltn_trans (leq_addr _ _) hst2.
  have hstds : (st.+1 + size ds <= l)%N := hst2.
  move: hds => /= /andP[hd0 hds'].
  rewrite /=.
  case: d hd0 hbud h => [|d'] hd0 hbud h.
  + (* Zero digit: sample locally without consuming a target. *)
    rewrite !bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> u; cbv beta; rewrite !bind_assoc.
    eapply IH => //.
    * by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
    * move=> us hus.
      move: (h (u :: us)); rewrite /= hus => /(_ erefl).
      by [].
  + (* Positive digit: consume one target before recursing. *)
    have hdw1 : (d'.+1 <= w.-1)%N by rewrite -ltnS prednK.
    rewrite !bind_assoc.
    eapply hquery => //.
    * by apply: leq_trans hbud; rewrite /preimage_query_count /= addnS ltnS leq_addr.
    * exact: lt_notin hfresh.
    * move=> x; cbv beta; rewrite !bind_assoc.
      eapply IH => //.
      -- rewrite /unzip1 map_rcons all_rcons hQr /=.
         by rewrite hstcc hdw1.
      -- by move: hbud; rewrite size_rcons /preimage_query_count /= addnS addSn.
      -- rewrite /unzip1 map_rcons all_rcons; apply/andP; split.
         ++ by rewrite /= ltnSn.
         ++ by apply: sub_all hfresh => t ht; exact: leq_trans ht (leqnSn st).
      -- move=> us hus.
         move: (h (x :: us)); rewrite /= hus => /(_ erefl).
         by rewrite (pre_queries_cons N) /= cat_rcons.
Qed.

End Loops.

Lemma pre_chains_link (N : choice_type) (dN : dist N)
    (query : nat -> nat -> raw_code N) (pkg : raw_package) ds st :
  code_link (pre_chains N dN query st ds) pkg =
  pre_chains N dN (fun i k => code_link (query i k) pkg) st ds.
Proof.
elim: ds st => [|d ds ih] st //=.
rewrite code_link_bind.
have hsig : code_link (if d is d'.+1 then query st d' else dN) pkg =
  if d is d'.+1 then code_link (query st d') pkg else dN.
{ case: d => [|d'] //.
  exact: (code_link_scheme _ _ _ _ (prog_valid dN)). }
rewrite hsig; apply: f_equal; apply: functional_extensionality => s.
rewrite code_link_bind ih.
by apply: f_equal; apply: functional_extensionality => ss.
Qed.
