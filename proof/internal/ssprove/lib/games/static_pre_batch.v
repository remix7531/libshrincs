(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.static_pre_batch

    List scheduling for static SM-PRE. Positive-digit challenges retain
    their compact target indices; local samples do not consume a target.
    CHECK shares the target table established before the single reveal. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.relational_rules games.static_batch.
From Shrincs Require Import games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Static preimage challenges *)

Section StaticPreBatch.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition I_batch_pre :=
  [interface
    [ batch_gen ] : { 'unit ~> batch_output T };
    [ batch_check ] : { 'nat × th_M T ~> 'bool }
  ].

Definition batch_pre_query (t : th_T T) : raw_code (th_N T) :=
  call [ PQUERY ] : { th_T T ~> th_N T } t.

Definition batch_pre_local (pp : th_PP T) (t : th_T T) :=
  #assert target_class t ;;
  revealed ← get pre_rev_loc ;;
  #assert ~~ revealed ;;
  tws ← get (pre_tws_loc T) ;;
  #assert (size tws < p)%N ;;
  #assert (t \notin tws) ;;
  x ← th_dM T ;;
  tgts ← get (pre_tgts_loc T) ;;
  #put (pre_tgts_loc T) := setm tgts (size tws) (t, x) ;;
  #put (pre_tws_loc T) := rcons tws t ;;
  ret (th_eval T pp t x).

Definition batch_pre_check (b : bool) (q : nat * th_M T) :=
  revealed ← get pre_rev_loc ;;
  #assert revealed ;;
  if b then
    tgts ← get (pre_tgts_loc T) ;;
    match getm tgts q.1 with
    | Some (t, x) =>
        ppo ← get (pre_pp_loc T) ;;
        pp ← match ppo with
             | Some pp => ret pp
             | None => pp ← th_dPP T ;;
                       #put (pre_pp_loc T) := Some pp ;; ret pp
             end ;;
        ret (th_eval T pp t q.2 == th_eval T pp t x)
    | None => ret false
    end
  else ret false.

Definition batch_pre_locs :=
  [fmap batch_done_loc; pre_pp_loc T; pre_tgts_loc T;
        pre_tws_loc T; pre_rev_loc].

#[local] Instance batch_pre_local_valid pp t :
  ValidCode batch_pre_locs emptym (batch_pre_local pp t).
Proof. rewrite /batch_pre_local; ssprove_valid. Qed.

#[local] Instance batch_pre_check_valid b q :
  ValidCode batch_pre_locs emptym (batch_pre_check b q).
Proof. rewrite /batch_pre_check; ssprove_valid. Qed.

Definition R_batch_pre (pin : th_T T * th_M T)
    (ts : seq (option (th_T T))) : package (I_SMPRE T) I_batch_pre.
Proof.
notypeclasses refine [package [fmap batch_done_loc];
  [ batch_gen ] : { 'unit ~> batch_output T } (_) {
    done ← get batch_done_loc ;;
    #assert ~~ done ;;
    _ ← call [ EVAL ] : { th_T T × th_M T ~> th_N T } pin ;;
    ys ← batch_loop T batch_pre_query ts ;;
    pp ← call [ PGETPP ] : { 'unit ~> th_PP T } tt ;;
    #put batch_done_loc := true ;;
    ret (pp, ys)
  };
  [ batch_check ] : { 'nat × th_M T ~> 'bool } (q) {
    call [ PCHECK ] : { 'nat × th_M T ~> 'bool } q
  }
].
ssprove_valid.
apply batch_loop_valid => t.
rewrite /batch_pre_query; ssprove_valid.
Defined.

Definition G_batch_pre (pin : th_T T * th_M T)
    (ts : seq (option (th_T T))) (b : bool) : game I_batch_pre.
Proof.
notypeclasses refine [package batch_pre_locs;
  [ batch_gen ] : { 'unit ~> batch_output T } (_) {
    done ← get batch_done_loc ;;
    #assert ~~ done ;;
    #assert ~~ target_class pin.1 ;;
    ppo ← get (pre_pp_loc T) ;;
    pp ← match ppo with
         | Some pp => ret pp
         | None => pp ← th_dPP T ;;
                   #put (pre_pp_loc T) := Some pp ;; ret pp
         end ;;
    ys ← batch_loop T (batch_pre_local pp) ts ;;
    #put pre_rev_loc := true ;;
    #put batch_done_loc := true ;;
    ret (pp, ys)
  };
  [ batch_check ] : { 'nat × th_M T ~> 'bool } (q) {
    batch_pre_check b q
  }
].
ssprove_valid.
all: typeclasses eauto.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Simulation of the challenge loop *)

Definition batch_pre_pre (pp : th_PP T) : precond :=
  fun '(h0, h1) => h0 = h1 /\ get_heap h1 (pre_pp_loc T) = Some pp.

Lemma batch_pre_query_link b t :
  code_link (batch_pre_query t) (SMPRE_game T target_class p b) =
  (#assert target_class t ;;
   revealed ← get pre_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get (pre_tws_loc T) ;;
   #assert (size tws < p)%N ;;
   #assert (t \notin tws) ;;
   x ← th_dM T ;;
   tgts ← get (pre_tgts_loc T) ;;
   #put (pre_tgts_loc T) := setm tgts (size tws) (t, x) ;;
   #put (pre_tws_loc T) := rcons tws t ;;
   ppo ← get (pre_pp_loc T) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← th_dPP T ;;
                  #put (pre_pp_loc T) := Some pp ;; ret pp
        end ;;
   ret (th_eval T pp t x)).
Proof. by case: b; simplify_linking; rewrite ?bind_ret. Qed.

Lemma r_batch_pre_query b pp t :
  ⊢ ⦃ fun '(h0, h1) => batch_pre_pre pp (h0, h1) ⦄
      batch_pre_local pp t
    ≈ code_link (batch_pre_query t) (SMPRE_game T target_class p b)
  ⦃ fun '(x, h0) '(y, h1) => x = y /\ batch_pre_pre pp (h0, h1) ⦄.
Proof.
rewrite batch_pre_query_link /batch_pre_local.
ssprove_sync => ht.
refine (r_get_remember_lhs pre_rev_loc _ _ (batch_pre_pre pp) _ _).
move=> rev.
eapply r_get_remember_rhs => rev'.
eapply (r_fact (rev' = rev)).
- by move=> h0 h1 [[[-> hpp] hr0] hr1]; rewrite -hr1 -hr0.
- move=> heq; subst rev'.
  ssprove_sync => hrev.
  eapply r_get_remember_lhs => tws.
  eapply r_get_remember_rhs => tws'.
  eapply (r_fact (tws' = tws)).
  + by move=> h0 h1 [[[[[-> hpp] hr0] hr1] ht0] ht1];
      rewrite -ht1 -ht0.
  + move=> heq; subst tws'.
    ssprove_sync => hbudget.
    ssprove_sync => hfresh.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> x.
    eapply r_get_remember_lhs => tgts.
    eapply r_get_remember_rhs => tgts'.
    eapply (r_fact (tgts' = tgts)).
    * by move=> h0 h1 [[[[[[[-> hpp] hr0] hr1] ht0] ht1] hg0] hg1];
        rewrite -hg1 -hg0.
    * (* Equal target tables remain related after the challenge updates. *)
      move=> heq; subst tgts'.
      do 2 apply r_put_vs_put.
      eapply (rpre_weaken_rule
        (fun '(h0, h1) => batch_pre_pre pp (h0, h1))); last first.
      { move=> h0 h1
          [h1' [[h0' [[h1'' [[h0'' [hpre heq0]] heq1]] heq2]] heq3]].
        subst h0 h1 h0' h1'.
        case: hpre => [[[[[[[heq hpp] hr0] hr1] ht0] ht1] hg0] hg1].
        split; first by rewrite heq.
        by rewrite !get_set_heap_neq. }
      eapply (r_get_rhs_known (pre_pp_loc T) (Some pp));
        first by move=> h0 h1 [_ hpp].
      simpl.
      by apply r_ret.
Qed.

Lemma r_batch_pre_loop b pp ts :
  ⊢ ⦃ fun '(h0, h1) => batch_pre_pre pp (h0, h1) ⦄
      batch_loop T (batch_pre_local pp) ts
    ≈ code_link (batch_loop T batch_pre_query ts)
        (SMPRE_game T target_class p b)
  ⦃ fun '(xs, h0) '(ys, h1) => xs = ys /\ batch_pre_pre pp (h0, h1) ⦄.
Proof.
elim: ts => [|t ts ih] /=.
- by apply r_ret.
- rewrite code_link_bind.
  eapply r_bind.
  + case: t => [t|]; first exact: r_batch_pre_query.
    rewrite (code_link_scheme _ _ _ _ (prog_valid (th_dN T))).
    eapply (r_reflexivity_alt (batch_pre_pre pp) (th_dN T)
      (prog_valid (th_dN T))).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + (* Equal head samples leave the tail simulations related. *)
    move=> x y.
    eapply rpre_hypothesis_rule => h0 h1 [heq hpre].
    subst y.
    eapply (rpre_weaken_rule
      (fun '(h0, h1) => batch_pre_pre pp (h0, h1)));
      last by move=> ? ? /= [-> ->].
    rewrite code_link_bind.
    eapply r_bind; first exact: ih.
    move=> xs ys.
    by apply r_ret => h0' h1' [-> hpre'].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Perfect simulation and advantage *)

Lemma R_batch_pre_perfect pin ts b :
  perfect I_batch_pre (G_batch_pre pin ts b)
    (R_batch_pre pin ts ∘ SMPRE_game T target_class p b).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (fun '(h0, h1) => h0 = h1)).
{ ssprove_invariant. }
simplify_eq_rel arg.
- simpl.
  eapply (rsame_head_cmd (cmd_get batch_done_loc)) => done.
  rewrite code_link_assertD.
  ssprove_sync => hdone.
  case: pin => t m /=.
  rewrite /resolve.
  ssprove_code_simpl.
  simpl.
  rewrite coerce_kleisliE.
  simpl.
  ssprove_code_simpl.
  simpl.
  rewrite /assertD.
  case: (boolP (~~ target_class t)) => hclass /=.
  - refine (r_get_remember_lhs (pre_pp_loc T) _ _
      (fun '(h0, h1) => h0 = h1) _ _).
    move=> ppo.
    eapply r_get_remember_rhs => ppo'.
    eapply (r_fact (ppo' = ppo)).
    + by move=> h0 h1 [[-> hp0] hp1]; rewrite -hp1 -hp0.
    + (* Both simulations use the same existing or freshly sampled seed. *)
      move=> heq; subst ppo'.
      case: ppo => [pp|].
      * (* The seed was already pinned. *)
        eapply (rpre_weaken_rule
          (fun '(h0, h1) => batch_pre_pre pp (h0, h1))); last first.
        { by move=> h0 h1 [[heq hp0] hp1]; split. }
        simpl.
        eapply r_bind; first exact: r_batch_pre_loop.
        move=> xs ys.
        eapply (r_get_rhs_known (pre_pp_loc T) (Some pp)
          (fun '(h0, h1) => xs = ys /\ batch_pre_pre pp (h0, h1)));
          first by move=> h0 h1 [_ [_ hpp]].
        simpl.
        eapply rpre_hypothesis_rule => h0 h1 [-> [-> hpp]].
        eapply rpre_weaken_rule.
        { eapply rpost_weaken_rule; first apply rreflexivity_rule.
          by move=> [x h0'] [y h1'] [= -> ->]. }
        by move=> h0' h1' /= [-> ->].
      * (* The outside-class pin samples the seed once. *)
        rewrite bind_assoc; simpl.
        eapply r_scheme_bind; first exact: prog_valid.
        move=> pp.
        apply r_put_vs_put.
        eapply (rpre_weaken_rule
          (fun '(h0, h1) => batch_pre_pre pp (h0, h1))); last first.
        { move=> h0 h1 [h1' [[h0' [[[heq hp0] hp1] ->]] ->]].
          split; first by rewrite heq.
          exact: get_set_heap_eq. }
        eapply r_bind; first exact: r_batch_pre_loop.
        move=> xs ys.
        eapply (r_get_rhs_known (pre_pp_loc T) (Some pp)
          (fun '(h0, h1) => xs = ys /\ batch_pre_pre pp (h0, h1)));
          first by move=> h0 h1 [_ [_ hpp]].
        simpl.
        eapply rpre_hypothesis_rule => h0 h1 [-> [-> hpp]].
        eapply rpre_weaken_rule.
        { eapply rpost_weaken_rule; first apply rreflexivity_rule.
          by move=> [x h0'] [y h1'] [= -> ->]. }
        by move=> h0' h1' /= [-> ->].
  - exact: r_fail_bind_rhs.
- case: arg => j m.
  rewrite /batch_pre_check bind_ret.
  eapply rpost_weaken_rule; first apply rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
Qed.

Lemma R_batch_pre_real pin ts :
  perfect I_batch_pre (G_batch_pre pin ts true)
    (R_batch_pre pin ts ∘ SMPRE_game T target_class p true).
Proof. exact: R_batch_pre_perfect. Qed.

Lemma R_batch_pre_ideal pin ts :
  perfect I_batch_pre (G_batch_pre pin ts false)
    (R_batch_pre pin ts ∘ SMPRE_game T target_class p false).
Proof. exact: R_batch_pre_perfect. Qed.

Lemma batch_pre_advantage pin ts (A : adversary I_batch_pre) :
  Adv (G_batch_pre pin ts true) (G_batch_pre pin ts false) A =
  AdvOf (SMPRE_game T target_class p) (A ∘ R_batch_pre pin ts).
Proof.
rewrite (Adv_perfect_l (R_batch_pre_real pin ts)).
rewrite (Adv_perfect_r (R_batch_pre_ideal pin ts)).
exact: Adv_reduction.
Qed.

End StaticPreBatch.
