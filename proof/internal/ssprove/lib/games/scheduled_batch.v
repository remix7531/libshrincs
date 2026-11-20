(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.scheduled_batch

    A batch may be selected after outside-class EVAL calls, with the same
    public seed used throughout. GEN fixes the complete challenge list,
    makes all queries, then reveals exactly once. This extends the fixed
    list interface without changing the static class or challenge budget. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.relational_rules games.static_batch games.static_pre_batch.
From Shrincs Require Import games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition scheduled_gen : nat := 1520.
Definition scheduled_check : nat := 1521.
Definition scheduled_done_loc := mkloc 1520 false.

(* ------------------------------------------------------------------ *)
(** ** Scheduled indistinguishability challenges *)

Section ScheduledUD.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition I_scheduled_ud :=
  [interface
    [ scheduled_gen ] : { 'list ('option (th_T T)) ~> batch_output T };
    [ EVAL ] : { th_T T × th_M T ~> th_N T }
  ].

Definition scheduled_ud_locs :=
  [fmap scheduled_done_loc; ud_pp_loc T; ud_tws_loc T; ud_rev_loc].

Definition R_scheduled_ud (pin : th_T T * th_M T)
    : package (I_SMUD T) I_scheduled_ud.
Proof.
notypeclasses refine [package [fmap scheduled_done_loc];
  [ scheduled_gen ] : { 'list ('option (th_T T)) ~> batch_output T } (ts) {
    done ← get scheduled_done_loc ;;
    #assert ~~ done ;;
    _ ← call [ EVAL ] : { th_T T × th_M T ~> th_N T } pin ;;
    ys ← batch_loop T (batch_ud_query T) ts ;;
    pp ← call [ UGETPP ] : { 'unit ~> th_PP T } tt ;;
    #put scheduled_done_loc := true ;;
    ret (pp, ys)
  };
  [ EVAL ] : { th_T T × th_M T ~> th_N T } (q) {
    call [ EVAL ] : { th_T T × th_M T ~> th_N T } q
  }
].
ssprove_valid.
apply batch_loop_valid => t.
rewrite /batch_ud_query; ssprove_valid.
Defined.

Definition G_scheduled_ud (pin : th_T T * th_M T)
    (b : bool) : game I_scheduled_ud.
Proof.
notypeclasses refine [package scheduled_ud_locs;
  [ scheduled_gen ] : { 'list ('option (th_T T)) ~> batch_output T } (ts) {
    done ← get scheduled_done_loc ;;
    #assert ~~ done ;;
    #assert ~~ target_class pin.1 ;;
    ppo ← get (ud_pp_loc T) ;;
    pp ← match ppo with
         | Some pp => ret pp
         | None => pp ← th_dPP T ;;
                   #put (ud_pp_loc T) := Some pp ;; ret pp
         end ;;
    ys ← batch_loop T (batch_ud_local T target_class p b pp) ts ;;
    #put ud_rev_loc := true ;;
    #put scheduled_done_loc := true ;;
    ret (pp, ys)
  };
  [ EVAL ] : { th_T T × th_M T ~> th_N T } (q) {
    #assert ~~ target_class q.1 ;;
    ppo ← get (ud_pp_loc T) ;;
    pp ← match ppo with
         | Some pp => ret pp
         | None => pp ← th_dPP T ;;
                   #put (ud_pp_loc T) := Some pp ;; ret pp
         end ;;
    ret (th_eval T pp q.1 q.2)
  }
].
ssprove_valid.
apply batch_loop_valid => t.
rewrite /batch_ud_local; ssprove_valid.
Defined.

Lemma R_scheduled_ud_perfect pin b :
  perfect I_scheduled_ud (G_scheduled_ud pin b)
    (R_scheduled_ud pin ∘ SMUD_game T target_class p b).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (fun '(h0, h1) => h0 = h1)).
{ ssprove_invariant. }
simplify_eq_rel arg.
- simpl.
  eapply (rsame_head_cmd (cmd_get scheduled_done_loc)) => done.
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
          (fun '(h0, h1) => batch_ud_pre T pp (h0, h1))); last first.
        { by move=> h0 h1 [[heq hp0] hp1]; split. }
        simpl.
        eapply r_bind; first exact: r_batch_ud_loop.
        move=> xs ys.
        eapply (r_get_rhs_known (ud_pp_loc T) (Some pp)
          (fun '(h0, h1) => xs = ys /\ batch_ud_pre T pp (h0, h1)));
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
          (fun '(h0, h1) => batch_ud_pre T pp (h0, h1))); last first.
        { move=> h0 h1 [h1' [[h0' [[[heq hp0] hp1] ->]] ->]].
          split; first by rewrite heq.
          exact: get_set_heap_eq. }
        eapply r_bind; first exact: r_batch_ud_loop.
        move=> xs ys.
        eapply (r_get_rhs_known (ud_pp_loc T) (Some pp)
          (fun '(h0, h1) => xs = ys /\ batch_ud_pre T pp (h0, h1)));
          first by move=> h0 h1 [_ [_ hpp]].
        simpl.
        eapply rpre_hypothesis_rule => h0 h1 [-> [-> hpp]].
        eapply rpre_weaken_rule.
        { eapply rpost_weaken_rule; first apply rreflexivity_rule.
          by move=> [x h0'] [y h1'] [= -> ->]. }
        by move=> h0' h1' /= [-> ->].
  - exact: r_fail_bind_rhs.
- case: arg => t m.
  rewrite bind_ret.
  eapply rpost_weaken_rule; first apply rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
Qed.

Lemma scheduled_ud_advantage pin (A : adversary I_scheduled_ud) :
  Adv (G_scheduled_ud pin true) (G_scheduled_ud pin false) A =
  AdvOf (SMUD_game T target_class p) (A ∘ R_scheduled_ud pin).
Proof.
rewrite (Adv_perfect_l (R_scheduled_ud_perfect pin true)).
rewrite (Adv_perfect_r (R_scheduled_ud_perfect pin false)).
exact: Adv_reduction.
Qed.

End ScheduledUD.

(* ------------------------------------------------------------------ *)
(** ** Scheduled preimage challenges *)

Section ScheduledPRE.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition I_scheduled_pre :=
  [interface
    [ scheduled_gen ] : { 'list ('option (th_T T)) ~> batch_output T };
    [ scheduled_check ] : { 'nat × th_M T ~> 'bool };
    [ EVAL ] : { th_T T × th_M T ~> th_N T }
  ].

Definition scheduled_pre_locs :=
  [fmap scheduled_done_loc; pre_pp_loc T; pre_tgts_loc T;
    pre_tws_loc T; pre_rev_loc].

Definition R_scheduled_pre (pin : th_T T * th_M T)
    : package (I_SMPRE T) I_scheduled_pre.
Proof.
notypeclasses refine [package [fmap scheduled_done_loc];
  [ scheduled_gen ] : { 'list ('option (th_T T)) ~> batch_output T } (ts) {
    done ← get scheduled_done_loc ;;
    #assert ~~ done ;;
    _ ← call [ EVAL ] : { th_T T × th_M T ~> th_N T } pin ;;
    ys ← batch_loop T (batch_pre_query T) ts ;;
    pp ← call [ PGETPP ] : { 'unit ~> th_PP T } tt ;;
    #put scheduled_done_loc := true ;;
    ret (pp, ys)
  };
  [ scheduled_check ] : { 'nat × th_M T ~> 'bool } (q) {
    call [ PCHECK ] : { 'nat × th_M T ~> 'bool } q
  };
  [ EVAL ] : { th_T T × th_M T ~> th_N T } (q) {
    call [ EVAL ] : { th_T T × th_M T ~> th_N T } q
  }
].
ssprove_valid.
apply batch_loop_valid => t.
rewrite /batch_pre_query; ssprove_valid.
Defined.

Definition G_scheduled_pre (pin : th_T T * th_M T)
    (b : bool) : game I_scheduled_pre.
Proof.
notypeclasses refine [package scheduled_pre_locs;
  [ scheduled_gen ] : { 'list ('option (th_T T)) ~> batch_output T } (ts) {
    done ← get scheduled_done_loc ;;
    #assert ~~ done ;;
    #assert ~~ target_class pin.1 ;;
    ppo ← get (pre_pp_loc T) ;;
    pp ← match ppo with
         | Some pp => ret pp
         | None => pp ← th_dPP T ;;
                   #put (pre_pp_loc T) := Some pp ;; ret pp
         end ;;
    ys ← batch_loop T (batch_pre_local T target_class p pp) ts ;;
    #put pre_rev_loc := true ;;
    #put scheduled_done_loc := true ;;
    ret (pp, ys)
  };
  [ scheduled_check ] : { 'nat × th_M T ~> 'bool } (q) {
    batch_pre_check T b q
  };
  [ EVAL ] : { th_T T × th_M T ~> th_N T } (q) {
    #assert ~~ target_class q.1 ;;
    ppo ← get (pre_pp_loc T) ;;
    pp ← match ppo with
         | Some pp => ret pp
         | None => pp ← th_dPP T ;;
                   #put (pre_pp_loc T) := Some pp ;; ret pp
         end ;;
    ret (th_eval T pp q.1 q.2)
  }
].
ssprove_valid;
  try (apply batch_loop_valid => t);
  rewrite /batch_pre_local /batch_pre_check; ssprove_valid.
Defined.

Lemma R_scheduled_pre_perfect pin b :
  perfect I_scheduled_pre (G_scheduled_pre pin b)
    (R_scheduled_pre pin ∘ SMPRE_game T target_class p b).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (fun '(h0, h1) => h0 = h1)).
{ ssprove_invariant. }
simplify_eq_rel arg.
- simpl.
  eapply (rsame_head_cmd (cmd_get scheduled_done_loc)) => done.
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
          (fun '(h0, h1) => batch_pre_pre T pp (h0, h1))); last first.
        { by move=> h0 h1 [[heq hp0] hp1]; split. }
        simpl.
        eapply r_bind; first exact: r_batch_pre_loop.
        move=> xs ys.
        eapply (r_get_rhs_known (pre_pp_loc T) (Some pp)
          (fun '(h0, h1) => xs = ys /\ batch_pre_pre T pp (h0, h1)));
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
          (fun '(h0, h1) => batch_pre_pre T pp (h0, h1))); last first.
        { move=> h0 h1 [h1' [[h0' [[[heq hp0] hp1] ->]] ->]].
          split; first by rewrite heq.
          exact: get_set_heap_eq. }
        eapply r_bind; first exact: r_batch_pre_loop.
        move=> xs ys.
        eapply (r_get_rhs_known (pre_pp_loc T) (Some pp)
          (fun '(h0, h1) => xs = ys /\ batch_pre_pre T pp (h0, h1)));
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
- case: arg => t m.
  rewrite bind_ret.
  eapply rpost_weaken_rule; first apply rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
Qed.

Lemma scheduled_pre_advantage pin (A : adversary I_scheduled_pre) :
  Adv (G_scheduled_pre pin true) (G_scheduled_pre pin false) A =
  AdvOf (SMPRE_game T target_class p) (A ∘ R_scheduled_pre pin).
Proof.
rewrite (Adv_perfect_l (R_scheduled_pre_perfect pin true)).
rewrite (Adv_perfect_r (R_scheduled_pre_perfect pin false)).
exact: Adv_reduction.
Qed.

End ScheduledPRE.
