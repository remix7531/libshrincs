(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.static_batch

    The static batch experiments reject a pin in their target class and
    a second generation attempt in either branch. PRE checking also
    refuses an uninitialized batch. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common
  games.static_batch games.static_pre_batch.
From Shrincs Require Import games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T) (ts : seq (option (th_T T))).

Lemma batch_ud_gen_invalid_pin (answer : bool) :
  target_class pin.1 ->
  AdvOf (G_batch_ud T target_class p pin ts)
    (guard_calls (batch_gen, ('unit, batch_output T)) tt 1 answer) = 0%R.
Proof.
move=> hclass.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /= hclass /=.
Qed.

Lemma batch_ud_gen_phase_abort (b : bool) (h : heap) :
  get_heap h batch_done_loc = true ->
  Pr_code (resolve (G_batch_ud T target_class p pin ts b)
    (batch_gen, ('unit, batch_output T)) tt) h = Pr_code fail h.
Proof.
move=> hdone.
simplify_linking.
by rewrite Pr_code_get hdone /=.
Qed.

Lemma batch_pre_gen_invalid_pin (answer : bool) :
  target_class pin.1 ->
  AdvOf (G_batch_pre T target_class p pin ts)
    (guard_calls (batch_gen, ('unit, batch_output T)) tt 1 answer) = 0%R.
Proof.
move=> hclass.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /= hclass /=.
Qed.

Lemma batch_pre_gen_phase_abort (b : bool) (h : heap) :
  get_heap h batch_done_loc = true ->
  Pr_code (resolve (G_batch_pre T target_class p pin ts b)
    (batch_gen, ('unit, batch_output T)) tt) h = Pr_code fail h.
Proof.
move=> hdone.
simplify_linking.
by rewrite Pr_code_get hdone /=.
Qed.

Lemma batch_pre_check_no_setup (x : 'nat × th_M T) (answer : bool) :
  AdvOf (G_batch_pre T target_class p pin ts)
    (guard_calls (batch_check, ('nat × th_M T, 'bool)) x 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
case: x => [j m].
by rewrite /batch_pre_check !Pr_code_get /=.
Qed.

End Guards.
