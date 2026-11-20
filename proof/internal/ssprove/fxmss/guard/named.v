(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.named

    Each named internal hybrid inherits the shared protocol guards. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games digest.filtered guard.hybrids.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Lemma g_forge_keyed_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_keyed_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_keyed_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_keyed_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_keyed_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_keyed_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_keyed_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_keyed_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_keyed_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_keyed_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_keyed_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_keyed_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool) :
  AdvOf (G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_keyed_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_keyed_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_keyed_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_keyed_forge_after_forge (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_keyed_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_keyed P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

Lemma g_forge_sampledkey_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_sampledkey_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_sampledkey_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_sampledkey_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_sampledkey_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_sampledkey_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool)
  :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_sampledkey_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_sampledkey_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_sampledkey_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_sampledkey_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_sampledkey_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h
  : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_sampledkey_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer :
  bool) :
  AdvOf (G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_sampledkey_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h
  : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_sampledkey_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input)
  (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_sampledkey_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_sampledkey_forge_after_forge (bit : bool) (candidate :
  shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_sampledkey_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

Lemma g_forge_randomized_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_randomized_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_randomized_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_randomized_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_randomized_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_randomized_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool)
  :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_randomized_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_randomized_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_randomized_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_randomized_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_randomized_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h
  : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_randomized_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer :
  bool) :
  AdvOf (G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_randomized_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h
  : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_randomized_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input)
  (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_randomized_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_randomized_forge_after_forge (bit : bool) (candidate :
  shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_randomized_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_randomized P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

Section Keep.
Context (keep : shrincs_fxmss_keep).

Lemma g_forge_filtered_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_filtered_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_filtered_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_filtered_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_filtered_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_filtered_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_filtered_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_filtered_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_filtered_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
  :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_filtered_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_filtered_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_filtered_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer :
  bool) :
  AdvOf (G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_filtered_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_filtered_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input) (h
  : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_filtered_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_filtered_forge_after_forge (bit : bool) (candidate : shrincs_fxmss_message
  ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_filtered_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

End Keep.

Lemma g_forge_digest_filtered_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_digest_filtered_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool)
  :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_digest_filtered_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool)
  :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_digest_filtered_sign_over_budget (cm : shrincs_fxmss_message) (answer :
  bool) :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_digest_filtered_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer :
  bool) :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_digest_filtered_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer :
  bool) :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_digest_filtered_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_digest_filtered_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h
  : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_digest_filtered_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_digest_filtered_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message)
  (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_digest_filtered_sign_budget_abort (bit : bool) (cm :
  shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_digest_filtered_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer
  : bool) :
  AdvOf (G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_digest_filtered_hash_after_forge (bit : bool) (x :
  shrincs_fxmss_hmsg_input) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_digest_filtered_hash_budget_abort (bit : bool) (x :
  shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_digest_filtered_forge_no_key (bit : bool) (candidate :
  shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_digest_filtered_forge_after_forge (bit : bool) (candidate :
  shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_digest_filtered_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h
  : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

Lemma g_forge_known_anchor_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_known_anchor_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_known_anchor_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_known_anchor_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool)
  :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_known_anchor_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool)
  :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_known_anchor_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer :
  bool) :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_known_anchor_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_known_anchor_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_known_anchor_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_known_anchor_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h
  : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_known_anchor_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message)
  (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_known_anchor_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer :
  bool) :
  AdvOf (G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_known_anchor_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input)
  (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_known_anchor_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input)
  (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_known_anchor_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message
  ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_known_anchor_forge_after_forge (bit : bool) (candidate :
  shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_known_anchor_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

Lemma g_forge_matching_leaf_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_matching_leaf_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_matching_leaf_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_matching_leaf_sign_over_budget (cm : shrincs_fxmss_message) (answer :
  bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_matching_leaf_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool)
  :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_matching_leaf_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer :
  bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_matching_leaf_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_matching_leaf_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_matching_leaf_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_matching_leaf_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message)
  (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_matching_leaf_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message)
  (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_matching_leaf_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer :
  bool) :
  AdvOf (G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_matching_leaf_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input)
  (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_matching_leaf_hash_budget_abort (bit : bool) (x :
  shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_matching_leaf_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message
  ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_matching_leaf_forge_after_forge (bit : bool) (candidate :
  shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_matching_leaf_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

Lemma g_forge_reject_gen_no_setup (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) =
      0%R.
Proof. exact: g_forge_gen_no_setup. Qed.

Lemma g_forge_reject_gen_over_budget (sp : shrincs_fxmss_setup) (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) =
      0%R.
Proof. exact: g_forge_gen_over_budget. Qed.

Lemma g_forge_reject_sign_no_setup (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm 1 answer) = 0%R.
Proof. exact: g_forge_sign_no_setup. Qed.

Lemma g_forge_reject_sign_over_budget (cm : shrincs_fxmss_message) (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_sign_over_budget. Qed.

Lemma g_forge_reject_hash_no_setup (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x 1 answer) = 0%R.
Proof. exact: g_forge_hash_no_setup. Qed.

Lemma g_forge_reject_hash_over_budget (x : shrincs_fxmss_hmsg_input) (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R.
Proof. exact: g_forge_hash_over_budget. Qed.

Lemma g_forge_reject_forge_no_setup (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes)
  (answer : bool) :
  AdvOf (G_forge_reject P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R.
Proof. exact: g_forge_forge_no_setup. Qed.

Lemma g_forge_reject_gen_after_forge (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
  :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_after_forge. Qed.

Lemma g_forge_reject_sign_no_key (bit : bool) (cm : shrincs_fxmss_message) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_no_key. Qed.

Lemma g_forge_reject_sign_after_forge (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_after_forge. Qed.

Lemma g_forge_reject_sign_budget_abort (bit : bool) (cm : shrincs_fxmss_message) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h
      = Pr_code fail h.
Proof. exact: g_forge_sign_budget_abort. Qed.

Lemma g_forge_reject_hash_only (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool)
  :
  AdvOf (G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32)))
      x n answer) = 0%R.
Proof. exact: g_forge_hash_only. Qed.

Lemma g_forge_reject_hash_after_forge (bit : bool) (x : shrincs_fxmss_hmsg_input) (h :
  heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_after_forge. Qed.

Lemma g_forge_reject_hash_budget_abort (bit : bool) (x : shrincs_fxmss_hmsg_input) (h :
  heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h =
      Pr_code fail h.
Proof. exact: g_forge_hash_budget_abort. Qed.

Lemma g_forge_reject_forge_no_key (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_no_key. Qed.

Lemma g_forge_reject_forge_after_forge (bit : bool) (candidate : shrincs_fxmss_message ×
  shrincs_fxmss_bytes) (h : heap) :
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
      candidate) h = Pr_code fail h.
Proof. exact: g_forge_forge_after_forge. Qed.

Lemma g_forge_reject_gen_twice_abort (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state) :
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (G_forge_reject P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h.
Proof. exact: g_forge_gen_twice_abort. Qed.

End Guards.
