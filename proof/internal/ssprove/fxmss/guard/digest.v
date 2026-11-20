(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.digest

    Protocol-abort guards for the internal games. Fixed-call adversaries
    ignore replies; heap guards separately exercise initialized exhausted
    counters and all calls after the terminal operation. The collision filter
    is independent of the security bit. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games digest.filtered digest.games.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).
Context (filter : bool).

Lemma digest_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_forge_no_setup (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof.
case: candidate => cm sg.
apply: guard_adv_eq.
simplify_linking.
by rewrite /shrincs_fxmss_forge_body !Pr_code_get /=.
Qed.

Lemma digest_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof.
move=> hd.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=.
- reflexivity.
- by rewrite Pr_code_get hd.
Qed.

Lemma digest_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof.
move=> hst.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE.
by rewrite Pr_code_get hst.
Qed.

Lemma digest_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof.
move=> hd.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=.
- by rewrite Pr_code_get hd.
- reflexivity.
Qed.

Lemma digest_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof.
move=> hst hd hq.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE.
by rewrite Pr_code_get hst Pr_code_get hd Pr_code_get ltnNge hq.
Qed.

(** HASH-only executions agree on both bits, including before GEN. *)
Lemma digest_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool) :
  AdvOf (G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma digest_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof.
move=> hd.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE Pr_code_get.
by rewrite hd.
Qed.

Lemma digest_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof.
move=> hst hd hq.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE.
by rewrite Pr_code_get hd Pr_code_get ltnNge hq.
Qed.

Lemma digest_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof.
move=> hst.
case: candidate => cm sg.
rewrite /G_digest /resolve /= coerce_kleisliE /shrincs_fxmss_forge_body.
by rewrite Pr_code_get hst /= Pr_code_sample dlet_null_ext Pr_code_fail.
Qed.

Lemma digest_forge_after_forge (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof.
move=> hd.
case: candidate => cm sg.
rewrite /G_digest /resolve /= coerce_kleisliE /shrincs_fxmss_forge_body Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=.
- by rewrite Pr_code_get hd /= Pr_code_sample dlet_null_ext Pr_code_fail.
- by rewrite Pr_code_sample dlet_null_ext Pr_code_fail.
Qed.

Lemma digest_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof.
move=> hst.
rewrite /G_digest /resolve /= coerce_kleisliE /digest_gen_body /digest_sign_body
  /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve /=
  coerce_kleisliE.
by rewrite Pr_code_get hst.
Qed.

End Guards.

Lemma g_digest_preassigned_forge_no_key (P : shrincs_fxmss_params) (Q :
  shrincs_fxmss_resources) (bit :
  bool)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_digest_preassigned P Q bit) shrincs_fxmss_forge_op candidate) h =
    Pr_code fail h.
Proof. exact: digest_forge_no_key. Qed.

Lemma g_digest_filtered_forge_no_key (P : shrincs_fxmss_params) (Q :
  shrincs_fxmss_resources) (bit :
  bool)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_digest_filtered P Q bit) shrincs_fxmss_forge_op candidate) h =
    Pr_code fail h.
Proof. exact: digest_forge_no_key. Qed.


Lemma g_digest_preassigned_sign_no_setup (P : shrincs_fxmss_params) (Q :
  shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_digest_preassigned P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: digest_sign_no_setup. Qed.

Lemma g_digest_filtered_sign_no_setup (P : shrincs_fxmss_params) (Q :
  shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: digest_sign_no_setup. Qed.
