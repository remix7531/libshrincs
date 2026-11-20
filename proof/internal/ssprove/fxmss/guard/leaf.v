(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.leaf

    Abort guards for the batched leaf experiments. Missing setup and
    out-of-range openings abort before the distinguishing bit; GEN, SIGN
    and EVAL do not inspect it. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import schemes.
From Shrincs.internal.ssprove.fxmss Require Import leaf.opening.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma leaf_opening_check_no_setup P q answer :
  AdvOf (G_leaf_opening P)
    (guard_calls (leaf_opening_check, (leaf_opening_opening, 'bool)) q 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
by rewrite /leaf_opening_check_body !Pr_code_get /=.
Qed.

Lemma leaf_opening_gen_repeated P sp n answer :
  AdvOf (G_leaf_opening P)
    (guard_calls (leaf_opening_gen, (params.shrincs_fxmss_structure,
      leaf_opening_public)) sp n answer) =
      0%R.
Proof.
apply: guard_adv_oracle_eq.
by rewrite /G_leaf_opening /resolve /= !coerce_kleisliE.
Qed.

Lemma leaf_opening_sign_repeated P q n answer :
  AdvOf (G_leaf_opening P)
    (guard_calls (leaf_opening_sign, ('nat × bytes 32, 'option leaf_opening_signature))
      q n answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
by rewrite /G_leaf_opening /resolve /= !coerce_kleisliE.
Qed.

Lemma leaf_opening_eval_repeated P q n answer :
  AdvOf (G_leaf_opening P)
    (guard_calls (leaf_opening_eval, (leaf_opening_eval_input, bytes 16)) q n answer) =
      0%R.
Proof.
apply: guard_adv_oracle_eq.
by rewrite /G_leaf_opening /resolve /= !coerce_kleisliE.
Qed.

Lemma leaf_opening_check_budget_abort P bit q st h :
  get_heap h leaf_opening_st_loc = Some st ->
  size (games.shrincs_fxmss_schedule st.2) <= q.1 ->
  Pr_code (resolve (G_leaf_opening P bit)
    (leaf_opening_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h.
Proof.
move=> hst hq.
rewrite resolve_leaf_opening_check /leaf_opening_check_body.
rewrite Pr_code_get hst /=.
rewrite ltnNge hq /=.
by rewrite Pr_code_sample Pr_code_fail dlet_null_ext.
Qed.

From Shrincs.internal.ssprove.fxmss Require Import leaf.known_message_game.


Lemma known_message_check_no_setup P q answer :
  AdvOf (G_known_message P)
    (guard_calls (known_message_check, (leaf_opening_opening, 'bool)) q 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
cbn [guard_repeat code_link].
rewrite !resolve_known_message_check /known_message_check_body.
by rewrite !Pr_code_get /=.
Qed.

Lemma known_message_check_budget_abort P bit q st h :
  get_heap h leaf_opening_st_loc = Some st ->
  size (games.shrincs_fxmss_schedule st.2) <= q.1 ->
  Pr_code (resolve (G_known_message P bit)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h.
Proof.
move=> hst hq.
rewrite resolve_known_message_check /known_message_check_body.
rewrite Pr_code_get hst.
cbv beta iota zeta delta [bind assertD getSome isSome].
rewrite ltnNge hq /=.
by rewrite Pr_code_sample Pr_code_fail dlet_null_ext.
Qed.

Lemma known_message_sign_consumes_failed j st h :
  get_heap h leaf_opening_st_loc = Some st ->
  j < size (games.shrincs_fxmss_schedule st.2) ->
  j \notin get_heap h leaf_opening_slog_loc ->
  nth None (get_heap h known_message_cache_loc) j = None ->
  Pr_code (known_message_sign_body j) h =
  Pr_code (ret None)
    (set_heap h leaf_opening_slog_loc (j :: get_heap h leaf_opening_slog_loc)).
Proof.
move=> hst hj hnot hcache.
rewrite /known_message_sign_body Pr_code_get hst /= hj /= Pr_code_get hnot /=.
rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
by rewrite hcache.
Qed.
