(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.stateful_rom

    Protocol-abort guards for the public stateful ROM experiment. The
    regression adversaries ignore replies; repeated calls include executions
    stopped by the first missing-setup abort. HASH is permitted before setup.
    Separate heap lemmas test exhausted SIGN/HASH counters and a repeated
    terminal call after initialization. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.lib.games Require Import stateful_rom.

Import PackageNotation Shrincs.games.stateful_rom.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (S : stateful_rom_scheme) (q_s q_h : nat).

Lemma sf_gen_no_setup (sp : sf_Setup S) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (GEN, (sf_Setup S, sf_Pk S)) sp 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_gen_over_budget (sp : sf_Setup S) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (GEN, (sf_Setup S, sf_Pk S)) sp 2 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_sign_no_setup (cm : sf_Msg S) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (SIGN, (sf_Msg S, 'option (sf_Sig S))) cm 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_sign_repeated_no_setup (cm : sf_Msg S) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (SIGN, (sf_Msg S, 'option (sf_Sig S))) cm (q_s).+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_hash_no_setup (x : sf_Hin S) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (HASH, (sf_Hin S, 'option (sf_Hout S))) x 1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_hash_over_budget (x : sf_Hin S) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (HASH, (sf_Hin S, 'option (sf_Hout S))) x (q_h).+1 answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_forge_no_setup (candidate : (sf_Msg S × sf_Sig S)) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (FORGE, ((sf_Msg S × sf_Sig S), 'bool)) candidate 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
rewrite /guard_repeat /= !sf_resolve_forge.
rewrite /forge_body /check_body.
by rewrite !Pr_code_get /=.
Qed.

Lemma sf_terminal_no_key bit candidate (T : choiceType) (k : bool -> raw_code T) h :
  get_heap h (sf_st_loc S) = None ->
  Pr_code (bind (forge_body S bit candidate) k) h = distr.dnull.
Proof.
move=> hn.
by rewrite /forge_body /check_body Pr_code_get hn /assertD /= Pr_code_sample dlet_null_ext.
Qed.

Lemma sf_forge_repeated_no_setup (candidate : (sf_Msg S × sf_Sig S)) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (FORGE, ((sf_Msg S × sf_Sig S), 'bool)) candidate 2 answer) = 0%R.
Proof.
apply: guard_adv_eq.
change (Pr_code (bind (resolve (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h true)
    (FORGE,((sf_Msg S × sf_Sig S),'bool)) candidate)
  (fun _ => code_link (guard_repeat (FORGE,((sf_Msg S × sf_Sig S),'bool)) candidate 1 answer)
    (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h true))) empty_heap =
Pr_code (bind (resolve (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h false)
    (FORGE,((sf_Msg S × sf_Sig S),'bool)) candidate)
  (fun _ => code_link (guard_repeat (FORGE,((sf_Msg S × sf_Sig S),'bool)) candidate 1 answer)
    (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h false))) empty_heap).
rewrite !sf_resolve_forge.
by rewrite !sf_terminal_no_key.
Qed.

Lemma sf_sign_budget_abort cm h st :
  get_heap h (sf_st_loc S) = Some st ->
  get_heap h sf_done_loc = false ->
  (q_s <= get_heap h sf_scnt_loc)%N ->
  Pr_code (sign_body S q_s cm) h = Pr_code fail h.
Proof.
move=> hst hd hq.
by rewrite /sign_body Pr_code_get hst Pr_code_get hd
Pr_code_get ltnNge hq.
Qed.

Lemma sf_hash_budget_abort x h st :
  get_heap h (sf_st_loc S) = Some st ->
  get_heap h sf_done_loc = false ->
  (q_h <= get_heap h sf_hcnt_loc)%N ->
  Pr_code (hash_body S q_h x) h = Pr_code fail h.
Proof.
move=> hst hd hq.
by rewrite /hash_body Pr_code_get hd
Pr_code_get ltnNge hq.
Qed.

Lemma sf_forge_budget_abort bit candidate h st :
  get_heap h (sf_st_loc S) = Some st ->
  get_heap h sf_done_loc = true ->
  Pr_code (forge_body S bit candidate) h = Pr_code fail h.
Proof.
move=> hst hd.
by rewrite /forge_body /check_body Pr_code_get hst Pr_code_get hd /= Pr_code_sample dlet_null_ext
  Pr_code_fail.
Qed.

Lemma sf_gen_invalid sp :
  ~~ sf_setup_valid S sp -> gen_body S sp = fail.
Proof. by move=> hi; rewrite /gen_body (negbTE hi). Qed.

Lemma sf_gen_twice_abort sp h st :
  get_heap h (sf_st_loc S) = Some st ->
  Pr_code (gen_body S sp) h = Pr_code fail h.
Proof.
move=> hst.
rewrite /gen_body.
case: (sf_setup_valid S sp) => //=.
by rewrite Pr_code_get hst.
Qed.

Lemma sf_sign_no_key cm h :
  get_heap h (sf_st_loc S) = None ->
  Pr_code (sign_body S q_s cm) h = Pr_code fail h.
Proof. by move=> hst; rewrite /sign_body Pr_code_get hst. Qed.

(** HASH may run before GEN; any fixed number of HASH-only calls is bit-independent. *)
Lemma sf_hash_only (x : sf_Hin S) (n : nat) (answer : bool) :
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (HASH, (sf_Hin S, 'option (sf_Hout S))) x n answer) = 0%R.
Proof.
apply: guard_adv_oracle_eq.
simplify_linking.
reflexivity.
Qed.

Lemma sf_gen_after_forge sp h :
  get_heap h sf_done_loc = true ->
  Pr_code (gen_body S sp) h = Pr_code fail h.
Proof.
move=> hd.
rewrite /gen_body.
case: (sf_setup_valid S sp) => //=.
rewrite Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|] //=.
by rewrite Pr_code_get hd.
Qed.

Lemma sf_sign_after_forge cm h :
  get_heap h sf_done_loc = true ->
  Pr_code (sign_body S q_s cm) h = Pr_code fail h.
Proof.
move=> hd.
rewrite /sign_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|] //=.
by rewrite Pr_code_get hd.
Qed.

Lemma sf_hash_after_forge x h :
  get_heap h sf_done_loc = true ->
  Pr_code (hash_body S q_h x) h = Pr_code fail h.
Proof.
move=> hd.
by rewrite /hash_body Pr_code_get hd.
Qed.

Lemma sf_forge_after_forge b candidate h :
  get_heap h sf_done_loc = true ->
  Pr_code (forge_body S b candidate) h = Pr_code fail h.
Proof.
move=> hd.
rewrite /forge_body /check_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|] /=.
- by rewrite Pr_code_get hd /= Pr_code_sample dlet_null_ext Pr_code_fail.
- by rewrite Pr_code_sample dlet_null_ext Pr_code_fail.
Qed.

End Guards.
