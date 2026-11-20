(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.tree

    The tree-collision filter inherits all protocol guards from the
    full-signature preassigned experiment. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games tree.forgery tree.classify guard.forgery.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Lemma gtree_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: forge_full_signature_gen_no_setup. Qed.

Lemma gtree_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: forge_full_signature_gen_over_budget. Qed.

Lemma gtree_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: forge_full_signature_sign_no_setup. Qed.

Lemma gtree_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: forge_full_signature_sign_over_budget. Qed.

Lemma gtree_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: forge_full_signature_hash_no_setup. Qed.

Lemma gtree_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: forge_full_signature_hash_over_budget. Qed.

Lemma gtree_forge_no_setup (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: forge_full_signature_forge_no_setup. Qed.

Lemma gtree_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: forge_full_signature_gen_after_forge. Qed.

Lemma gtree_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: forge_full_signature_sign_no_key. Qed.

Lemma gtree_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: forge_full_signature_sign_after_forge. Qed.

Lemma gtree_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: forge_full_signature_sign_budget_abort. Qed.

(** HASH-only executions agree on both bits, including before GEN. *)
Lemma gtree_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool) :
  AdvOf (G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: forge_full_signature_hash_only. Qed.

Lemma gtree_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: forge_full_signature_hash_after_forge. Qed.

Lemma gtree_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: forge_full_signature_hash_budget_abort. Qed.

Lemma gtree_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: forge_full_signature_forge_no_key. Qed.

Lemma gtree_forge_after_forge (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: forge_full_signature_forge_after_forge. Qed.

Lemma gtree_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_tree_free P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: forge_full_signature_gen_twice_abort. Qed.

End Guards.
