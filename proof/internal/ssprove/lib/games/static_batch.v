(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.static_batch

    Finite lists of static-class challenges, followed by one reveal.
    A missing challenge samples a local node. The direct games sample
    hidden inputs locally; the reductions obtain their images from the
    public games in Shrincs.games. All protocol guards are retained.
    Operation and heap identifiers 1100..1199 belong to this batch layer. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.relational_rules.
From Shrincs Require Import games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Static indistinguishability challenges *)

Section StaticBatch.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition batch_gen : nat := 1100.
Definition batch_check : nat := 1101.
Definition batch_done_loc := mkloc 1100 false.
Definition batch_output := th_PP T × 'list (th_N T).
Definition I_batch_ud :=
  [interface [ batch_gen ] : { 'unit ~> batch_output } ].

Fixpoint batch_loop (query : th_T T -> raw_code (th_N T))
    (ts : seq (option (th_T T))) : raw_code (chList (th_N T)) :=
  match ts with
  | [::] => ret [::]
  | t :: ts' =>
      y ← match t with
           | Some t => query t
           | None => th_dN T
           end ;;
      ys ← batch_loop query ts' ;;
      ret (y :: ys)
  end.

#[export] Instance batch_loop_valid L I query ts
    (hquery : forall t, ValidCode L I (query t)) :
  ValidCode L I (batch_loop query ts).
Proof.
elim: ts => [|t ts ih] /=.
- apply valid_ret.
- eapply valid_bind.
  + case: t => [t|]; first exact: hquery.
    eapply valid_scheme, prog_valid.
  + move=> y; eapply valid_bind; first exact: ih.
    move=> ys; apply valid_ret.
Qed.

Definition batch_ud_query (t : th_T T) : raw_code (th_N T) :=
  call [ UQUERY ] : { th_T T ~> th_N T } t.

Definition batch_ud_local (b : bool) (pp : th_PP T) (t : th_T T) :=
  #assert target_class t ;;
  revealed ← get ud_rev_loc ;;
  #assert ~~ revealed ;;
  tws ← get (ud_tws_loc T) ;;
  #assert (size tws < p)%N ;;
  #assert (t \notin tws) ;;
  #put (ud_tws_loc T) := rcons tws t ;;
  if b then x ← th_dM T ;; ret (th_eval T pp t x)
  else th_dN T.

Definition batch_ud_locs :=
  [fmap batch_done_loc; ud_pp_loc T; ud_tws_loc T; ud_rev_loc].

#[local] Instance batch_ud_local_valid b pp t :
  ValidCode batch_ud_locs emptym (batch_ud_local b pp t).
Proof. rewrite /batch_ud_local; ssprove_valid. Qed.

Definition R_batch_ud (pin : th_T T * th_M T)
    (ts : seq (option (th_T T))) : package (I_SMUD T) I_batch_ud.
Proof.
notypeclasses refine [package [fmap batch_done_loc];
  [ batch_gen ] : { 'unit ~> batch_output } (_) {
    done ← get batch_done_loc ;;
    #assert ~~ done ;;
    _ ← call [ EVAL ] : { th_T T × th_M T ~> th_N T } pin ;;
    ys ← batch_loop batch_ud_query ts ;;
    pp ← call [ UGETPP ] : { 'unit ~> th_PP T } tt ;;
    #put batch_done_loc := true ;;
    ret (pp, ys)
  }
].
ssprove_valid.
apply batch_loop_valid => t.
rewrite /batch_ud_query; ssprove_valid.
Defined.

Definition G_batch_ud (pin : th_T T * th_M T)
    (ts : seq (option (th_T T))) (b : bool) : game I_batch_ud.
Proof.
notypeclasses refine [package batch_ud_locs;
  [ batch_gen ] : { 'unit ~> batch_output } (_) {
    done ← get batch_done_loc ;;
    #assert ~~ done ;;
    #assert ~~ target_class pin.1 ;;
    ppo ← get (ud_pp_loc T) ;;
    pp ← match ppo with
         | Some pp => ret pp
         | None => pp ← th_dPP T ;;
                   #put (ud_pp_loc T) := Some pp ;; ret pp
         end ;;
    ys ← batch_loop (batch_ud_local b pp) ts ;;
    #put ud_rev_loc := true ;;
    #put batch_done_loc := true ;;
    ret (pp, ys)
  }
].
ssprove_valid.
apply batch_loop_valid => t.
exact: batch_ud_local_valid.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Simulation of the challenge loop *)

Definition batch_ud_pre (pp : th_PP T) : precond :=
  fun '(h0, h1) => h0 = h1 /\ get_heap h1 (ud_pp_loc T) = Some pp.

Lemma batch_ud_query_link b t :
  code_link (batch_ud_query t) (SMUD_game T target_class p b) =
  (#assert target_class t ;;
   revealed ← get ud_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get (ud_tws_loc T) ;;
   #assert (size tws < p)%N ;;
   #assert (t \notin tws) ;;
   #put (ud_tws_loc T) := rcons tws t ;;
   if b then
     ppo ← get (ud_pp_loc T) ;;
     pp ← match ppo with
          | Some pp => ret pp
          | None => pp ← th_dPP T ;;
                    #put (ud_pp_loc T) := Some pp ;; ret pp
          end ;;
     x ← th_dM T ;; ret (th_eval T pp t x)
   else th_dN T).
Proof. by case: b; simplify_linking; rewrite ?bind_ret. Qed.

Lemma r_batch_ud_query b pp t :
  ⊢ ⦃ batch_ud_pre pp ⦄
      batch_ud_local b pp t
    ≈ code_link (batch_ud_query t) (SMUD_game T target_class p b)
  ⦃ fun '(x, h0) '(y, h1) => x = y /\ batch_ud_pre pp (h0, h1) ⦄.
Proof.
rewrite batch_ud_query_link /batch_ud_local.
ssprove_sync => ht.
refine (r_get_remember_lhs ud_rev_loc _ _ (batch_ud_pre pp) _ _).
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
    apply r_put_vs_put.
    eapply (rpre_weaken_rule
      (fun '(h0, h1) => batch_ud_pre pp (h0, h1))); last first.
    { move=> h0 h1 [h1' [[h0' [hpre heq0]] heq1]].
      subst h0 h1.
      case: hpre => [[[[[heq hpp] hr0] hr1] ht0] ht1].
      split; first by rewrite heq.
      by rewrite get_set_heap_neq. }
    case: b.
    * (* The real branch hashes a sampled message under the shared seed. *)
      eapply (r_get_rhs_known (ud_pp_loc T) (Some pp));
        first by move=> h0 h1 [_ hpp].
      simpl.
      eapply r_scheme_bind; first exact: prog_valid.
      move=> x; by apply r_ret.
    * eapply (r_reflexivity_alt (batch_ud_pre pp) (th_dN T)
        (prog_valid (th_dN T))).
      -- by move=> l /fhas_empty.
      -- by move=> l v /fhas_empty.
Qed.

Lemma r_batch_ud_loop b pp ts :
  ⊢ ⦃ fun '(h0, h1) => batch_ud_pre pp (h0, h1) ⦄
      batch_loop (batch_ud_local b pp) ts
    ≈ code_link (batch_loop batch_ud_query ts)
        (SMUD_game T target_class p b)
  ⦃ fun '(xs, h0) '(ys, h1) => xs = ys /\ batch_ud_pre pp (h0, h1) ⦄.
Proof.
elim: ts => [|t ts ih] /=.
- by apply r_ret.
- rewrite code_link_bind.
  eapply r_bind.
  + case: t => [t|]; first exact: r_batch_ud_query.
    rewrite (code_link_scheme _ _ _ _ (prog_valid (th_dN T))).
    eapply (r_reflexivity_alt (batch_ud_pre pp) (th_dN T)
      (prog_valid (th_dN T))).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + (* Equal head samples leave the tail simulations related. *)
    move=> x y.
    eapply rpre_hypothesis_rule => h0 h1 [heq hpre].
    subst y.
    eapply (rpre_weaken_rule
      (fun '(h0, h1) => batch_ud_pre pp (h0, h1)));
      last by move=> ? ? /= [-> ->].
    rewrite code_link_bind.
    eapply r_bind; first exact: ih.
    move=> xs ys.
    by apply r_ret => h0' h1' [-> hpre'].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Perfect simulation and advantage *)

Lemma R_batch_ud_perfect pin ts b :
  perfect I_batch_ud (G_batch_ud pin ts b)
    (R_batch_ud pin ts ∘ SMUD_game T target_class p b).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (fun '(h0, h1) => h0 = h1)).
{ ssprove_invariant. }
simplify_eq_rel arg.
simpl.
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
- refine (r_get_remember_lhs (ud_pp_loc T) _ _
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
        (fun '(h0, h1) => batch_ud_pre pp (h0, h1))); last first.
      { by move=> h0 h1 [[heq hp0] hp1]; split. }
      simpl.
      eapply r_bind; first exact: r_batch_ud_loop.
      move=> xs ys.
      eapply (r_get_rhs_known (ud_pp_loc T) (Some pp)
        (fun '(h0, h1) => xs = ys /\ batch_ud_pre pp (h0, h1)));
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
        (fun '(h0, h1) => batch_ud_pre pp (h0, h1))); last first.
      { move=> h0 h1 [h1' [[h0' [[[heq hp0] hp1] ->]] ->]].
        split; first by rewrite heq.
        exact: get_set_heap_eq. }
      eapply r_bind; first exact: r_batch_ud_loop.
      move=> xs ys.
      eapply (r_get_rhs_known (ud_pp_loc T) (Some pp)
        (fun '(h0, h1) => xs = ys /\ batch_ud_pre pp (h0, h1)));
        first by move=> h0 h1 [_ [_ hpp]].
      simpl.
      eapply rpre_hypothesis_rule => h0 h1 [-> [-> hpp]].
      eapply rpre_weaken_rule.
      { eapply rpost_weaken_rule; first apply rreflexivity_rule.
        by move=> [x h0'] [y h1'] [= -> ->]. }
      by move=> h0' h1' /= [-> ->].
- exact: r_fail_bind_rhs.
Qed.

Lemma R_batch_ud_real pin ts :
  perfect I_batch_ud (G_batch_ud pin ts true)
    (R_batch_ud pin ts ∘ SMUD_game T target_class p true).
Proof. exact: R_batch_ud_perfect. Qed.

Lemma R_batch_ud_ideal pin ts :
  perfect I_batch_ud (G_batch_ud pin ts false)
    (R_batch_ud pin ts ∘ SMUD_game T target_class p false).
Proof. exact: R_batch_ud_perfect. Qed.

Lemma batch_ud_advantage pin ts (A : adversary I_batch_ud) :
  Adv (G_batch_ud pin ts true) (G_batch_ud pin ts false) A =
  AdvOf (SMUD_game T target_class p) (A ∘ R_batch_ud pin ts).
Proof.
rewrite (Adv_perfect_l (R_batch_ud_real pin ts)).
rewrite (Adv_perfect_r (R_batch_ud_ideal pin ts)).
exact: Adv_reduction.
Qed.

End StaticBatch.

(* ------------------------------------------------------------------ *)
(** ** Composition with a common context *)

(** A proved scheduler simulation remains perfect under a caller that
    caches and post-processes its results. *)
Lemma batch_context_perfect {I O : Interface} (C : package I O)
    (G0 G1 : nom_package) :
  perfect I G0 G1 -> perfect O (C ∘ G0) (C ∘ G1).
Proof.
move=> hsim A hA.
rewrite Adv_reduction.
exact: (hsim _ (valid_adv_link hA)).
Qed.
