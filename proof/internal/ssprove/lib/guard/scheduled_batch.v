(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.scheduled_batch

    All scheduling phases share the primitive's static-class restrictions.
    Repeated generation and premature checking abort on both bits. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common
  games.scheduled_batch games.static_batch games.static_pre_batch.
From Shrincs Require Import games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T).

Lemma scheduled_ud_gen_invalid_pin ts answer :
  target_class pin.1 ->
  AdvOf (G_scheduled_ud T target_class p pin)
    (guard_calls (scheduled_gen,
      ('list ('option (th_T T)), batch_output T)) ts 1 answer) = 0%R.
Proof.
move=> hclass.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /= hclass /=.
Qed.

Lemma scheduled_ud_gen_phase_abort ts b h :
  get_heap h scheduled_done_loc = true ->
  Pr_code (resolve (G_scheduled_ud T target_class p pin b)
    (scheduled_gen, ('list ('option (th_T T)), batch_output T)) ts) h =
    Pr_code fail h.
Proof.
move=> hdone.
simplify_linking.
by rewrite Pr_code_get hdone /=.
Qed.

Lemma scheduled_ud_eval_repeated q n answer :
  AdvOf (G_scheduled_ud T target_class p pin)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) q n answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
by rewrite /G_scheduled_ud /resolve /= !coerce_kleisliE.
Qed.

Lemma scheduled_pre_gen_invalid_pin ts answer :
  target_class pin.1 ->
  AdvOf (G_scheduled_pre T target_class p pin)
    (guard_calls (scheduled_gen,
      ('list ('option (th_T T)), batch_output T)) ts 1 answer) = 0%R.
Proof.
move=> hclass.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /= hclass /=.
Qed.

Lemma scheduled_pre_gen_phase_abort ts b h :
  get_heap h scheduled_done_loc = true ->
  Pr_code (resolve (G_scheduled_pre T target_class p pin b)
    (scheduled_gen, ('list ('option (th_T T)), batch_output T)) ts) h =
    Pr_code fail h.
Proof.
move=> hdone.
simplify_linking.
by rewrite Pr_code_get hdone /=.
Qed.

Lemma scheduled_pre_check_no_setup q answer :
  AdvOf (G_scheduled_pre T target_class p pin)
    (guard_calls (scheduled_check, ('nat × th_M T, 'bool)) q 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: q => j m.
by rewrite /batch_pre_check !Pr_code_get /=.
Qed.

Lemma scheduled_pre_eval_repeated q n answer :
  AdvOf (G_scheduled_pre T target_class p pin)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) q n answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
by rewrite /G_scheduled_pre /resolve /= !coerce_kleisliE.
Qed.

End Guards.
