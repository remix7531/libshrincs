(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.experiment

    Protocol guards for the concrete stateful ROM experiment. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude guard.common guard.stateful_rom.
From Shrincs Require Import games schemes.

Import PackageNotation Shrincs.games.stateful_rom.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (q_s q_h : nat).

Lemma fxmss_eucma_gen_no_setup (sp : sf_Setup fxmss_sf_scheme) (answer : bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (GEN, (sf_Setup fxmss_sf_scheme, sf_Pk fxmss_sf_scheme)) sp 1 answer) = 0%R.
Proof. exact: sf_gen_no_setup. Qed.

Lemma fxmss_eucma_gen_over_budget (sp : sf_Setup fxmss_sf_scheme) (answer : bool)
  :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (GEN, (sf_Setup fxmss_sf_scheme, sf_Pk fxmss_sf_scheme)) sp 2 answer) = 0%R.
Proof. exact: sf_gen_over_budget. Qed.

Lemma fxmss_eucma_sign_no_setup (cm : sf_Msg fxmss_sf_scheme) (answer : bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (SIGN, (sf_Msg fxmss_sf_scheme, 'option (sf_Sig fxmss_sf_scheme))) cm 1 answer) = 0%R.
Proof. exact: sf_sign_no_setup. Qed.

Lemma fxmss_eucma_sign_repeated_no_setup (cm : sf_Msg fxmss_sf_scheme) (answer :
  bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (SIGN, (sf_Msg fxmss_sf_scheme, 'option (sf_Sig fxmss_sf_scheme))) cm (q_s).+1 answer) = 0%R.
Proof. exact: sf_sign_repeated_no_setup. Qed.

Lemma fxmss_eucma_hash_no_setup (x : sf_Hin fxmss_sf_scheme) (answer : bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (HASH, (sf_Hin fxmss_sf_scheme, 'option (sf_Hout fxmss_sf_scheme))) x 1 answer) = 0%R.
Proof. exact: sf_hash_no_setup. Qed.

Lemma fxmss_eucma_hash_over_budget (x : sf_Hin fxmss_sf_scheme) (answer : bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (HASH, (sf_Hin fxmss_sf_scheme, 'option (sf_Hout fxmss_sf_scheme))) x (q_h).+1 answer) = 0%R.
Proof. exact: sf_hash_over_budget. Qed.

Lemma fxmss_eucma_forge_no_setup (candidate : (sf_Msg fxmss_sf_scheme × sf_Sig
  fxmss_sf_scheme)) (answer : bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (FORGE, ((sf_Msg fxmss_sf_scheme × sf_Sig fxmss_sf_scheme), 'bool)) candidate 1 answer) = 0%R.
Proof. exact: sf_forge_no_setup. Qed.

Lemma fxmss_eucma_terminal_no_key bit candidate (T : choiceType) (k : bool ->
  raw_code T) h :
  get_heap h (sf_st_loc fxmss_sf_scheme) = None ->
  Pr_code (bind (forge_body fxmss_sf_scheme bit candidate) k) h = distr.dnull.
Proof. exact: sf_terminal_no_key. Qed.

Lemma fxmss_eucma_forge_repeated_no_setup (candidate : (sf_Msg fxmss_sf_scheme ×
  sf_Sig fxmss_sf_scheme)) (answer : bool) :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (FORGE, ((sf_Msg fxmss_sf_scheme × sf_Sig fxmss_sf_scheme), 'bool)) candidate 2 answer) = 0%R.
Proof. exact: sf_forge_repeated_no_setup. Qed.

Lemma fxmss_eucma_sign_budget_abort cm h st :
  get_heap h (sf_st_loc fxmss_sf_scheme) = Some st ->
  get_heap h sf_done_loc = false ->
  (q_s <= get_heap h sf_scnt_loc)%N ->
  Pr_code (sign_body fxmss_sf_scheme q_s cm) h = Pr_code fail h.
Proof. exact: sf_sign_budget_abort. Qed.

Lemma fxmss_eucma_hash_budget_abort x h st :
  get_heap h (sf_st_loc fxmss_sf_scheme) = Some st ->
  get_heap h sf_done_loc = false ->
  (q_h <= get_heap h sf_hcnt_loc)%N ->
  Pr_code (hash_body fxmss_sf_scheme q_h x) h = Pr_code fail h.
Proof. exact: sf_hash_budget_abort. Qed.

Lemma fxmss_eucma_forge_budget_abort bit candidate h st :
  get_heap h (sf_st_loc fxmss_sf_scheme) = Some st ->
  get_heap h sf_done_loc = true ->
  Pr_code (forge_body fxmss_sf_scheme bit candidate) h = Pr_code fail h.
Proof. exact: sf_forge_budget_abort. Qed.

Lemma fxmss_eucma_gen_invalid sp :
  ~~ sf_setup_valid fxmss_sf_scheme sp -> gen_body fxmss_sf_scheme sp = fail.
Proof. exact: sf_gen_invalid. Qed.

Lemma fxmss_eucma_gen_twice_abort sp h st :
  get_heap h (sf_st_loc fxmss_sf_scheme) = Some st ->
  Pr_code (gen_body fxmss_sf_scheme sp) h = Pr_code fail h.
Proof. exact: sf_gen_twice_abort. Qed.

Lemma fxmss_eucma_sign_no_key cm h :
  get_heap h (sf_st_loc fxmss_sf_scheme) = None ->
  Pr_code (sign_body fxmss_sf_scheme q_s cm) h = Pr_code fail h.
Proof. exact: sf_sign_no_key. Qed.

Lemma fxmss_eucma_hash_only (x : sf_Hin fxmss_sf_scheme) (n : nat) (answer : bool)
  :
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (HASH, (sf_Hin fxmss_sf_scheme, 'option (sf_Hout fxmss_sf_scheme))) x n answer) = 0%R.
Proof. exact: sf_hash_only. Qed.

Lemma fxmss_eucma_gen_after_forge sp h :
  get_heap h sf_done_loc = true ->
  Pr_code (gen_body fxmss_sf_scheme sp) h = Pr_code fail h.
Proof. exact: sf_gen_after_forge. Qed.

Lemma fxmss_eucma_sign_after_forge cm h :
  get_heap h sf_done_loc = true ->
  Pr_code (sign_body fxmss_sf_scheme q_s cm) h = Pr_code fail h.
Proof. exact: sf_sign_after_forge. Qed.

Lemma fxmss_eucma_hash_after_forge x h :
  get_heap h sf_done_loc = true ->
  Pr_code (hash_body fxmss_sf_scheme q_h x) h = Pr_code fail h.
Proof. exact: sf_hash_after_forge. Qed.

Lemma fxmss_eucma_forge_after_forge b candidate h :
  get_heap h sf_done_loc = true ->
  Pr_code (forge_body fxmss_sf_scheme b candidate) h = Pr_code fail h.
Proof. exact: sf_forge_after_forge. Qed.

End Guards.
