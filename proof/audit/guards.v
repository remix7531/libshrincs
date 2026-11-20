(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Protocol-abort statement pins

    Reviewed full types and fixed-call adversaries for gate 7.
    The gate checks these statements; it never generates them. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common guard.stcrp_option
  guard.tcrx guard.smtcr games.stateful_rom guard.stateful_rom guard.kots guard.prf
  toolkit.ro_plus toolkit.reprogram_sep guard.reprogram_sep guard.ro_plus
  toolkit.sample_seq guard.sample_seq guard.smpre guard.smud games.static_batch
  games.static_pre_batch guard.static_batch guard.stcrp.
From Shrincs.internal.ssprove.fxmss Require Import guard.public params shape games
  digest.filtered guard.hybrids guard.named guard.experiment.
From mathcomp Require Import reals.
From mathcomp.experimental_reals Require Import distr.
From Shrincs.internal.ssprove.wots Require Import guard.public params scheme games
  hop.intermediates hop.prf hop.ud guard.hybrids.

From Shrincs Require Import games schemes.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint pinned_guard_repeat (o : opsig) (x : src o) (n : nat)
    (answer : bool) : raw_code 'bool :=
  match n with
  | 0 => ret answer
  | n'.+1 => _ ← op o ⋅ x ;; pinned_guard_repeat o x n' answer
  end.
Check (@Logic.eq_refl _ _ : @guard_repeat = @pinned_guard_repeat).
Example pinned_guard_run (o : opsig) (x : src o) (n : nat) (answer : bool) :
  resolve (guard_calls o x n answer) RUN tt = pinned_guard_repeat o x n answer.
Proof. simplify_linking. reflexivity. Qed.

Example pinned_guard_then (o0 : opsig) (x0 : src o0) (o1 : opsig)
    (x1 : src o1) (hneq : o0.1 != o1.1) (answer : bool) :
  resolve (guard_then o0 x0 o1 x1 hneq answer) RUN tt =
    (_ ← op o0 ⋅ x0 ;; _ ← op o1 ⋅ x1 ;; ret answer).
Proof. simplify_linking. reflexivity. Qed.

Module Concrete_hash_pins.
Import PackageNotation stcrp_option tcrx smtcr.

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_query_no_setup :
  forall (p : nat) (x : th_T (shrincs_thf) × (bytes 32)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_grind_game p)
    (guard_calls (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_query_over_budget :
  forall (p : nat) (x : th_T (shrincs_thf) × (bytes 32)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_grind_game p)
    (guard_calls (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_check_no_setup :
  forall (p : nat) (x : 'nat × ((bytes 32) × 'nat)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_grind_game p)
    (guard_calls (SCHECK, ('nat × ((bytes 32) × 'nat), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_reveal_no_setup :
  forall (p : nat) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_grind_game p)
    (guard_calls (SGETPP, ('unit, th_PP (shrincs_thf))) tt 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_eval_no_setup :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_grind_game p)
    (guard_calls (EVAL, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_query_phase_abort :
  forall (p : nat) (b : bool) (t : th_T (shrincs_thf)) (m : (bytes 32)) (h : heap),
  get_heap h stcr_option_rev_loc = true ->
  Pr_code (resolve (Shrincs.schemes.fxmss_grind_game p b)
    (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_query_budget_abort :
  forall (p : nat) (b : bool) (t : th_T (shrincs_thf)) (m : (bytes 32)) (h : heap),
  get_heap h stcr_option_rev_loc = false ->
  (p <= size (get_heap h (stcr_option_tws_loc (shrincs_thf))))%N ->
  Pr_code (resolve (Shrincs.schemes.fxmss_grind_game p b)
    (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_grind_query_after_reveal_phase_abort :
  forall (p : nat) (t : th_T (shrincs_thf)) (m : (bytes 32))
    (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_grind_game p)
    (guard_then (SGETPP, ('unit, th_PP (shrincs_thf))) tt
      (SQUERY, (th_T (shrincs_thf) × (bytes 32), 'option (th_N (shrincs_thf) × 'nat))) (t, m) erefl answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_query_no_setup :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tcrx_game p)
    (guard_calls (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_query_over_budget :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tcrx_game p)
    (guard_calls (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_check_no_setup :
  forall (p : nat) (x : 'nat × (th_T (shrincs_thf) × th_M (shrincs_thf))) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tcrx_game p)
    (guard_calls (XCHECK, ('nat × (th_T (shrincs_thf) × th_M (shrincs_thf)), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_reveal_no_setup :
  forall (p : nat) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tcrx_game p)
    (guard_calls (XGETPP, ('unit, th_PP (shrincs_thf))) tt 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_eval_no_setup :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tcrx_game p)
    (guard_calls (EVAL, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_query_phase_abort :
  forall (p : nat) (b : bool) (t : th_T (shrincs_thf)) (m : th_M (shrincs_thf)) (h : heap),
  get_heap h tcrx_rev_loc = true ->
  Pr_code (resolve (Shrincs.schemes.fxmss_tcrx_game p b)
    (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_query_budget_abort :
  forall (p : nat) (b : bool) (t : th_T (shrincs_thf)) (m : th_M (shrincs_thf)) (h : heap),
  get_heap h tcrx_rev_loc = false ->
  (p <= size (get_heap h (tcrx_tws_loc (shrincs_thf))))%N ->
  Pr_code (resolve (Shrincs.schemes.fxmss_tcrx_game p b)
    (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tcrx_query_after_reveal_phase_abort :
  forall (p : nat) (t : th_T (shrincs_thf)) (m : th_M (shrincs_thf))
    (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tcrx_game p)
    (guard_then (XGETPP, ('unit, th_PP (shrincs_thf))) tt
      (XQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m) erefl answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_query_no_setup :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tree_game p)
    (guard_calls (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_query_over_budget :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tree_game p)
    (guard_calls (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_reveal_no_setup :
  forall (p : nat) (x : 'unit) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tree_game p)
    (guard_calls (GETPP, ('unit, th_PP (shrincs_thf))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_eval_no_setup :
  forall (p : nat) (x : th_T (shrincs_thf) × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tree_game p)
    (guard_calls (EVAL, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_check_no_setup :
  forall (p : nat) (x : 'nat × th_M (shrincs_thf)) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tree_game p)
    (guard_calls (CHECK, ('nat × th_M (shrincs_thf), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_query_phase_abort :
  forall (p : nat) (b : bool) (t : th_T (shrincs_thf)) (m : th_M (shrincs_thf)) (h : heap),
  get_heap h tcr_rev_loc = true ->
  Pr_code (resolve (Shrincs.schemes.fxmss_tree_game p b)
    (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_query_budget_abort :
  forall (p : nat) (b : bool) (t : th_T (shrincs_thf)) (m : th_M (shrincs_thf)) (h : heap),
  get_heap h tcr_rev_loc = false ->
  (p <= size (get_heap h (tcr_tws_loc (shrincs_thf))))%N ->
  Pr_code (resolve (Shrincs.schemes.fxmss_tree_game p b)
    (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.public.fxmss_tree_query_after_reveal_phase_abort :
  forall (p : nat) (t : th_T (shrincs_thf)) (m : th_M (shrincs_thf))
    (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_tree_game p)
    (guard_then (GETPP, ('unit, th_PP (shrincs_thf))) tt
      (TQUERY, (th_T (shrincs_thf) × th_M (shrincs_thf), th_N (shrincs_thf))) (t, m) erefl answer) = 0%R).

End Concrete_hash_pins.

Module Kots_pins.
Import PackageNotation kots.

Check (Shrincs.internal.ssprove.lib.guard.kots.kots_vc_commit_no_setup :
  forall (S : sig_scheme) (sp : SParam S) (m : Msg S) (answer : bool),
  AdvOf (Shrincs.games.kots.KOTS_vc_game S)
    (guard_calls (COMMIT, (SParam S × Msg S, Pk S × 'option (Sig S))) (sp, m) 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.kots.kots_vc_commit_over_budget :
  forall (S : sig_scheme) (sp : SParam S) (m : Msg S) (answer : bool),
  AdvOf (Shrincs.games.kots.KOTS_vc_game S)
    (guard_calls (COMMIT, (SParam S × Msg S, Pk S × 'option (Sig S))) (sp, m) 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.kots.kots_vc_kforge_no_setup :
  forall (S : sig_scheme) (m : Msg S) (sig : Sig S)
    (answer : bool),
  AdvOf (Shrincs.games.kots.KOTS_vc_game S)
    (guard_calls (KFORGE, (Msg S × Sig S, 'bool))
      (m, sig) 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.kots.kots_vc_commit_phase_abort :
  forall (S : sig_scheme) (b : bool) (sp : SParam S)
    (m : Msg S) (pk : Pk S) (h : heap),
  get_heap h (kots_pk_loc S) = Some pk ->
  Pr_code (resolve (Shrincs.games.kots.KOTS_vc_game S b)
    (COMMIT, (SParam S × Msg S, Pk S × 'option (Sig S))) (sp, m)) h =
    Pr_code fail h).

End Kots_pins.

Module Prf_pins.
Import PackageNotation prf.

Check (Shrincs.internal.ssprove.lib.guard.prf.prf_fquery_no_setup :
  forall (K : khf) (hdk : LosslessCode (kh_dK K))
    (hdn : LosslessCode (kh_dN K)) (q : nat) (m : kh_M K) (answer : bool),
  AdvOf (Shrincs.games.prf.PRF_game K q)
    (guard_calls (FQUERY, (kh_M K, kh_N K)) m 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.prf.prf_fquery_repeated_abort :
  forall (K : khf) (q : nat) (m : kh_M K) (answer : bool),
  AdvOf (Shrincs.games.prf.PRF_game K q)
    (guard_calls (FQUERY, (kh_M K, kh_N K)) m q.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.prf.prf_query_budget_abort :
  forall (K : khf) (q : nat) (b : bool)
    (m : kh_M K) (h : heap),
  (q <= size (get_heap h (prf_qs_loc K)))%N ->
  Pr_code (resolve (Shrincs.games.prf.PRF_game K q b)
    (FQUERY, (kh_M K, kh_N K)) m) h = Pr_code fail h).

End Prf_pins.

Module Sampler_pins.
Import PackageNotation.

Check (Shrincs.internal.ssprove.lib.guard.sample_seq.sample_seq_test_no_setup :
  forall (d : dist 'nat) (answer : bool),
  AdvOf (fun _ : bool => Shrincs.internal.ssprove.lib.toolkit.sample_seq.SampleSeqTest.test_pkg d)
    (guard_calls (SampleSeqTest.TEST, ('unit, 'list ('nat))) tt 1 answer) = 0%R).

End Sampler_pins.

Module Smpre_pins.
Import PackageNotation smpre.

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_query_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : th_T T) (answer : bool),
  AdvOf (Shrincs.games.smpre.SMPRE_game T target_class p)
    (guard_calls (PQUERY, (th_T T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_query_over_budget :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : th_T T) (answer : bool),
  AdvOf (Shrincs.games.smpre.SMPRE_game T target_class p)
    (guard_calls (PQUERY, (th_T T, th_N T)) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_reveal_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : 'unit) (answer : bool),
  AdvOf (Shrincs.games.smpre.SMPRE_game T target_class p)
    (guard_calls (PGETPP, ('unit, th_PP T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_eval_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.smpre.SMPRE_game T target_class p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : 'nat × th_M T) (answer : bool),
  AdvOf (Shrincs.games.smpre.SMPRE_game T target_class p)
    (guard_calls (PCHECK, ('nat × th_M T, 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_query_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (b : bool) (t : th_T T) (h : heap),
  get_heap h pre_rev_loc = true ->
  Pr_code (resolve (Shrincs.games.smpre.SMPRE_game T target_class p b)
    (PQUERY, (th_T T, th_N T)) t) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_query_budget_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (b : bool) (t : th_T T) (h : heap),
  get_heap h pre_rev_loc = false ->
  (p <= size (get_heap h (pre_tws_loc T)))%N ->
  Pr_code (resolve (Shrincs.games.smpre.SMPRE_game T target_class p b)
    (PQUERY, (th_T T, th_N T)) t) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.smpre.smpre_query_after_reveal_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (t : th_T T)
    (answer : bool),
  AdvOf (Shrincs.games.smpre.SMPRE_game T target_class p)
    (guard_then (PGETPP, ('unit, th_PP T)) tt
      (PQUERY, (th_T T, th_N T)) t erefl answer) = 0%R).

End Smpre_pins.

Module Smtcr_pins.
Import PackageNotation smtcr.

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_query_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.smtcr.SMTCR_game T target_class p)
    (guard_calls (TQUERY, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_query_over_budget :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.smtcr.SMTCR_game T target_class p)
    (guard_calls (TQUERY, (th_T T × th_M T, th_N T)) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_reveal_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : 'unit) (answer : bool),
  AdvOf (Shrincs.games.smtcr.SMTCR_game T target_class p)
    (guard_calls (GETPP, ('unit, th_PP T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_eval_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.smtcr.SMTCR_game T target_class p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (x : 'nat × th_M T) (answer : bool),
  AdvOf (Shrincs.games.smtcr.SMTCR_game T target_class p)
    (guard_calls (CHECK, ('nat × th_M T, 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_query_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (b : bool) (t : th_T T) (m : th_M T) (h : heap),
  get_heap h tcr_rev_loc = true ->
  Pr_code (resolve (Shrincs.games.smtcr.SMTCR_game T target_class p b)
    (TQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_query_budget_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (b : bool) (t : th_T T) (m : th_M T) (h : heap),
  get_heap h tcr_rev_loc = false ->
  (p <= size (get_heap h (tcr_tws_loc T)))%N ->
  Pr_code (resolve (Shrincs.games.smtcr.SMTCR_game T target_class p b)
    (TQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.smtcr.smtcr_query_after_reveal_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (t : th_T T) (m : th_M T)
    (answer : bool),
  AdvOf (Shrincs.games.smtcr.SMTCR_game T target_class p)
    (guard_then (GETPP, ('unit, th_PP T)) tt
      (TQUERY, (th_T T × th_M T, th_N T)) (t, m) erefl answer) = 0%R).

End Smtcr_pins.

Module Smud_pins.
Import PackageNotation smud.

Check (Shrincs.internal.ssprove.lib.guard.smud.smud_uquery_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
    (hdpp : LosslessCode (th_dPP T)) (hdm : LosslessCode (th_dM T))
    (hdn : LosslessCode (th_dN T)) (p : nat) (t : th_T T) (answer : bool),
  AdvOf (Shrincs.games.smud.SMUD_game T target_class p)
    (guard_calls (UQUERY, (th_T T, th_N T)) t 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smud.smud_uquery_repeated_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (t : th_T T) (answer : bool),
  AdvOf (Shrincs.games.smud.SMUD_game T target_class p)
    (guard_calls (UQUERY, (th_T T, th_N T)) t p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.smud.smud_query_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (b : bool) (p : nat) (t : th_T T) (h : heap),
  get_heap h ud_rev_loc = true ->
  Pr_code (resolve (Shrincs.games.smud.SMUD_game T target_class p b)
    (UQUERY, (th_T T, th_N T)) t) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.smud.smud_query_budget_abort :
  forall (T : thf) (target_class : th_T T -> bool) (b : bool) (p : nat) (t : th_T T) (h : heap),
  get_heap h ud_rev_loc = false ->
  (p <= size (get_heap h (ud_tws_loc T)))%N ->
  Pr_code (resolve (Shrincs.games.smud.SMUD_game T target_class p b)
    (UQUERY, (th_T T, th_N T)) t) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.smud.smud_query_after_reveal_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat) (t : th_T T)
    (answer : bool),
  AdvOf (Shrincs.games.smud.SMUD_game T target_class p)
    (guard_then (UGETPP, ('unit, th_PP T)) tt
      (UQUERY, (th_T T, th_N T)) t erefl answer) = 0%R).

End Smud_pins.

Module Static_batch_pins.
Import PackageNotation.

Check (Shrincs.internal.ssprove.lib.guard.static_batch.batch_ud_gen_invalid_pin :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (answer : bool),
  target_class pin.1 ->
  AdvOf (Shrincs.internal.ssprove.lib.games.static_batch.G_batch_ud T target_class p pin ts)
    (guard_calls (batch_gen, ('unit, batch_output T)) tt 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.static_batch.batch_ud_gen_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (b : bool) (h : heap),
  get_heap h batch_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.lib.games.static_batch.G_batch_ud T target_class p pin ts b)
    (batch_gen, ('unit, batch_output T)) tt) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.static_batch.batch_pre_gen_invalid_pin :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (answer : bool),
  target_class pin.1 ->
  AdvOf (Shrincs.internal.ssprove.lib.games.static_pre_batch.G_batch_pre T target_class p pin ts)
    (guard_calls (batch_gen, ('unit, batch_output T)) tt 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.static_batch.batch_pre_gen_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (b : bool) (h : heap),
  get_heap h batch_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.lib.games.static_pre_batch.G_batch_pre T target_class p pin ts b)
    (batch_gen, ('unit, batch_output T)) tt) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.static_batch.batch_pre_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
  (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (x : 'nat × th_M T) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.lib.games.static_pre_batch.G_batch_pre T target_class p pin ts)
    (guard_calls (batch_check, ('nat × th_M T, 'bool)) x 1 answer) = 0%R).

End Static_batch_pins.

Module Grinding_pins.
Import PackageNotation stcrp.

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_query_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (x : th_T T × Mb) (answer : bool),
  AdvOf (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p)
    (guard_calls (SQUERY, (th_T T × Mb, th_N T × 'nat)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_query_over_budget :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (x : th_T T × Mb) (answer : bool),
  AdvOf (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p)
    (guard_calls (SQUERY, (th_T T × Mb, th_N T × 'nat)) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_reveal_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (x : 'unit) (answer : bool),
  AdvOf (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p)
    (guard_calls (SGETPP, ('unit, th_PP T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (x : 'nat × (Mb × 'nat)) (answer : bool),
  AdvOf (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p)
    (guard_calls (SCHECK, ('nat × (Mb × 'nat), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_query_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (b : bool) (t : th_T T) (m : Mb) (h : heap),
  get_heap h stcr_rev_loc = true ->
  Pr_code (resolve (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p b)
    (SQUERY, (th_T T × Mb, th_N T × 'nat)) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_query_budget_abort :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (b : bool) (t : th_T T) (m : Mb) (h : heap),
  get_heap h stcr_rev_loc = false ->
  (p <= size (get_heap h (stcr_tws_loc T)))%N ->
  Pr_code (resolve (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p b)
    (SQUERY, (th_T T × Mb, th_N T × 'nat)) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.stcrp.stcrp_query_after_reveal_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (Mb : choice_type)
  (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap : nat) (p : nat) (t : th_T T) (m : Mb)
    (answer : bool),
  AdvOf (Shrincs.games.stcrp.STCRP_game T target_class Mb enc prp cap p)
    (guard_then (SGETPP, ('unit, th_PP T)) tt
      (SQUERY, (th_T T × Mb, th_N T × 'nat)) (t, m) erefl answer) = 0%R).

End Grinding_pins.

Module Optional_grinding_pins.
Import PackageNotation stcrp_option.

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_query_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (x : th_T T × Mb) (answer : bool),
  AdvOf (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_query_over_budget :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (x : th_T T × Mb) (answer : bool),
  AdvOf (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (x : 'nat × (Mb × 'nat)) (answer : bool),
  AdvOf (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SCHECK, ('nat × (Mb × 'nat), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_reveal_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (answer : bool),
  AdvOf (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (SGETPP, ('unit, th_PP T)) tt 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_eval_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_query_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (b : bool) (t : th_T T) (m : Mb) (h : heap),
  get_heap h stcr_option_rev_loc = true ->
  Pr_code (resolve (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p b)
    (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_query_budget_abort :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (b : bool) (t : th_T T) (m : Mb) (h : heap),
  get_heap h stcr_option_rev_loc = false ->
  (p <= size (get_heap h (stcr_option_tws_loc T)))%N ->
  Pr_code (resolve (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p b)
    (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.stcrp_option.stcrp_option_query_after_reveal_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool)
  (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
  (prp : th_N T -> bool) (cap p : nat) (t : th_T T) (m : Mb)
    (answer : bool),
  AdvOf (Shrincs.games.stcrp_option.STCRP_option_game T target_class Mb enc prp cap p)
    (guard_then (SGETPP, ('unit, th_PP T)) tt
      (SQUERY, (th_T T × Mb, 'option (th_N T × 'nat))) (t, m) erefl answer) = 0%R).

End Optional_grinding_pins.

Module Paired_tweak_pins.
Import PackageNotation tcrx.

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_query_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.tcrx.TCRX_game T target_class partner p)
    (guard_calls (XQUERY, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_query_over_budget :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.tcrx.TCRX_game T target_class partner p)
    (guard_calls (XQUERY, (th_T T × th_M T, th_N T)) x p.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (x : 'nat × (th_T T × th_M T)) (answer : bool),
  AdvOf (Shrincs.games.tcrx.TCRX_game T target_class partner p)
    (guard_calls (XCHECK, ('nat × (th_T T × th_M T), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_reveal_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (answer : bool),
  AdvOf (Shrincs.games.tcrx.TCRX_game T target_class partner p)
    (guard_calls (XGETPP, ('unit, th_PP T)) tt 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_eval_no_setup :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (x : th_T T × th_M T) (answer : bool),
  AdvOf (Shrincs.games.tcrx.TCRX_game T target_class partner p)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_query_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (b : bool) (t : th_T T) (m : th_M T) (h : heap),
  get_heap h tcrx_rev_loc = true ->
  Pr_code (resolve (Shrincs.games.tcrx.TCRX_game T target_class partner p b)
    (XQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_query_budget_abort :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (b : bool) (t : th_T T) (m : th_M T) (h : heap),
  get_heap h tcrx_rev_loc = false ->
  (p <= size (get_heap h (tcrx_tws_loc T)))%N ->
  Pr_code (resolve (Shrincs.games.tcrx.TCRX_game T target_class partner p b)
    (XQUERY, (th_T T × th_M T, th_N T)) (t, m)) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.lib.guard.tcrx.tcrx_query_after_reveal_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool)
  (partner : th_T T -> th_T T) (p : nat) (t : th_T T) (m : th_M T)
    (answer : bool),
  AdvOf (Shrincs.games.tcrx.TCRX_game T target_class partner p)
    (guard_then (XGETPP, ('unit, th_PP T)) tt
      (XQUERY, (th_T T × th_M T, th_N T)) (t, m) erefl answer) = 0%R).

End Paired_tweak_pins.

Module Wots_hybrid_pins.
Import PackageNotation.

Check (Shrincs.internal.ssprove.wots.guard.hybrids.sampledkey_commit_no_setup :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.games.G_forge_sampledkey P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.sampledkey_commit_over_budget :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.games.G_forge_sampledkey P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.sampledkey_forge_no_setup :
  forall (P : wc_params) (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.games.G_forge_sampledkey P)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.uniformchains_commit_no_setup :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.uniformchains_commit_over_budget :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.uniformchains_forge_no_setup :
  forall (P : wc_params) (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.keyed_commit_no_setup :
  forall (P : wc_params) (K : choice_type) (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P)
    (dK : dist K)
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.hop.prf.G_forge_keyed P K PRF dK)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.keyed_commit_over_budget :
  forall (P : wc_params) (K : choice_type) (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P)
    (dK : dist K)
    (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.hop.prf.G_forge_keyed P K PRF dK)
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.keyed_forge_no_setup :
  forall (P : wc_params) (K : choice_type) (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P)
    (dK : dist K)
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.hop.prf.G_forge_keyed P K PRF dK)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.ud_hybrid_forge_no_setup :
  forall (P : wc_params) (s : nat)
    (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf (Shrincs.internal.ssprove.wots.hop.ud.HGw P s)
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.grind_commit_no_setup :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_grind P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.grind_commit_over_budget :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_grind P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.grind_forge_no_setup :
  forall (P : wc_params) (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_grind P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.compress_commit_no_setup :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_compress P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.compress_commit_over_budget :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_compress P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.compress_forge_no_setup :
  forall (P : wc_params) (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_compress P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.chain_commit_no_setup :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_chain P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.chain_commit_over_budget :
  forall (P : wc_params) (x : SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_chain P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (COMMIT, (SParam (shrincs_wots_scheme P) ×
      Msg (shrincs_wots_scheme P), Pk (shrincs_wots_scheme P) ×
      'option (Sig (shrincs_wots_scheme P)))) x 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.hybrids.chain_forge_no_setup :
  forall (P : wc_params) (x : Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P))
    (answer : bool),
  AdvOf ((fun b => if b then Shrincs.internal.ssprove.wots.hop.intermediates.G_post_chain P else Shrincs.internal.ssprove.wots.games.G_forge_uniformchains P false))
    (guard_calls (KFORGE, (Msg (shrincs_wots_scheme P) ×
      Sig (shrincs_wots_scheme P), 'bool)) x 1 answer) = 0%R).

End Wots_hybrid_pins.

Module Concrete_kots_pins.
Import PackageNotation kots.

Check (Shrincs.internal.ssprove.wots.guard.public.wots_c_kots_vc_commit_no_setup :
  forall (node_height : spec.UInt8) (node_index : spec.UInt64)
  (tree_balanced : bool) (tree_depth : spec.UInt8) (sp : SParam (wots_c_scheme node_height node_index tree_balanced tree_depth)) (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (answer : bool),
  AdvOf (Shrincs.schemes.wots_c_kots_game node_height node_index tree_balanced tree_depth)
    (guard_calls (COMMIT, (SParam (wots_c_scheme node_height node_index tree_balanced tree_depth) × Msg (wots_c_scheme node_height node_index tree_balanced tree_depth), Pk (wots_c_scheme node_height node_index tree_balanced tree_depth) × 'option (Sig (wots_c_scheme node_height node_index tree_balanced tree_depth)))) (sp, m) 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.public.wots_c_kots_vc_commit_over_budget :
  forall (node_height : spec.UInt8) (node_index : spec.UInt64)
  (tree_balanced : bool) (tree_depth : spec.UInt8) (sp : SParam (wots_c_scheme node_height node_index tree_balanced tree_depth)) (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (answer : bool),
  AdvOf (Shrincs.schemes.wots_c_kots_game node_height node_index tree_balanced tree_depth)
    (guard_calls (COMMIT, (SParam (wots_c_scheme node_height node_index tree_balanced tree_depth) × Msg (wots_c_scheme node_height node_index tree_balanced tree_depth), Pk (wots_c_scheme node_height node_index tree_balanced tree_depth) × 'option (Sig (wots_c_scheme node_height node_index tree_balanced tree_depth)))) (sp, m) 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.public.wots_c_kots_vc_kforge_no_setup :
  forall (node_height : spec.UInt8) (node_index : spec.UInt64)
  (tree_balanced : bool) (tree_depth : spec.UInt8) (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (sig : Sig (wots_c_scheme node_height node_index tree_balanced tree_depth))
    (answer : bool),
  AdvOf (Shrincs.schemes.wots_c_kots_game node_height node_index tree_balanced tree_depth)
    (guard_calls (KFORGE, (Msg (wots_c_scheme node_height node_index tree_balanced tree_depth) × Sig (wots_c_scheme node_height node_index tree_balanced tree_depth), 'bool))
      (m, sig) 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.wots.guard.public.wots_c_kots_vc_commit_phase_abort :
  forall (node_height : spec.UInt8) (node_index : spec.UInt64)
  (tree_balanced : bool) (tree_depth : spec.UInt8) (b : bool) (sp : SParam (wots_c_scheme node_height node_index tree_balanced tree_depth))
    (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (pk : Pk (wots_c_scheme node_height node_index tree_balanced tree_depth)) (h : heap),
  get_heap h (kots_pk_loc (wots_c_scheme node_height node_index tree_balanced tree_depth)) = Some pk ->
  Pr_code (resolve (Shrincs.schemes.wots_c_kots_game node_height node_index tree_balanced tree_depth b)
    (COMMIT, (SParam (wots_c_scheme node_height node_index tree_balanced tree_depth) × Msg (wots_c_scheme node_height node_index tree_balanced tree_depth), Pk (wots_c_scheme node_height node_index tree_balanced tree_depth) × 'option (Sig (wots_c_scheme node_height node_index tree_balanced tree_depth)))) (sp, m)) h =
    Pr_code fail h).

End Concrete_kots_pins.

Module Guard_adversary_pins.

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_repeat_valid :
  forall (o : opsig) (x : src o) (n : nat) (answer : bool),
         ValidCode emptym [fmap o] (guard_repeat o x n answer)).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_calls_disj :
  forall (o : opsig) (x : src o) (n : nat) (answer : bool) (G : nom_package),
         disj (guard_calls o x n answer : nom_package) G).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_adv_eq :
  forall (G0 G1 : nom_package) (o : opsig) (x : src o) (n : nat) (answer : bool),
         Pr_code (code_link (guard_repeat o x n answer) G0) empty_heap =
         Pr_code (code_link (guard_repeat o x n answer) G1) empty_heap
         -> Adv G0 G1 (guard_calls o x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_repeat_link_eq :
  forall (G0 G1 : raw_package) (o : opsig) (x : src o) (n : nat) (answer : bool),
         resolve G0 o x = resolve G1 o x
         -> code_link (guard_repeat o x n answer) G0 = code_link (guard_repeat o x n answer) G1).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_adv_oracle_eq :
  forall (G0 G1 : nom_package) (o : opsig) (x : src o) (n : nat) (answer : bool),
         resolve G0 o x = resolve G1 o x -> Adv G0 G1 (guard_calls o x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_adv_fst_eq :
  forall (G0 G1 : nom_package) (o : opsig) (x : src o) (n : nat) (answer : bool),
         dfst (Pr_code (code_link (guard_repeat o x n answer) G0) empty_heap) =
         dfst (Pr_code (code_link (guard_repeat o x n answer) G1) empty_heap)
         -> Adv G0 G1 (guard_calls o x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_then_disj :
  forall (o0 : opsig) (x0 : src o0) (o1 : opsig) (x1 : src o1) (hneq : o0.1 != o1.1)
         (answer : bool) (G : nom_package), disj (guard_then o0 x0 o1 x1 hneq answer : nom_package) G).

Check (@Shrincs.internal.ssprove.lib.guard.common.guard_then_adv_eq :
  forall (G0 G1 : nom_package) (o0 : opsig) (x0 : src o0) (o1 : opsig)
         (x1 : src o1) (hneq : o0.1 != o1.1) (answer : bool),
         Pr_code (resolve G0 o0 x0 ;;
                  resolve G0 o1 x1 ;;
                  ret answer) empty_heap =
         Pr_code (resolve G1 o0 x0 ;;
                  resolve G1 o1 x1 ;;
                  ret answer) empty_heap
         -> Adv G0 G1 (guard_then o0 x0 o1 x1 hneq answer) = 0%R).

End Guard_adversary_pins.

Module Stateful_experiment_pins.

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_gen_no_setup :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (sp : stateful_rom.sf_Setup S0) (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.GEN, (stateful_rom.sf_Setup S0, stateful_rom.sf_Pk S0)) sp 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_gen_over_budget :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (sp : stateful_rom.sf_Setup S0) (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.GEN, (stateful_rom.sf_Setup S0, stateful_rom.sf_Pk S0)) sp 2 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_sign_no_setup :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (cm : stateful_rom.sf_Msg S0) (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.SIGN, (stateful_rom.sf_Msg S0, 'option (stateful_rom.sf_Sig S0))) cm 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_sign_repeated_no_setup :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (cm : stateful_rom.sf_Msg S0) (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.SIGN, (stateful_rom.sf_Msg S0, 'option (stateful_rom.sf_Sig S0))) cm q_s.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_hash_no_setup :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (x : stateful_rom.sf_Hin S0) (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.HASH, (stateful_rom.sf_Hin S0, 'option (stateful_rom.sf_Hout S0))) x 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_hash_over_budget :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (x : stateful_rom.sf_Hin S0) (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.HASH, (stateful_rom.sf_Hin S0, 'option (stateful_rom.sf_Hout S0))) x q_h.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_forge_no_setup :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (candidate :
                                                           stateful_rom.sf_Msg S0 ×
                                                           stateful_rom.sf_Sig S0)
         (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.FORGE, (stateful_rom.sf_Msg S0 × stateful_rom.sf_Sig S0, 'bool)) candidate 1
              answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_terminal_no_key :
  forall (S : stateful_rom.stateful_rom_scheme) (bit : bool) (candidate : stateful_rom.sf_Msg S × stateful_rom.sf_Sig S)
         (T : choiceType) (k : bool -> raw_code T) (h : heap),
         get_heap h (stateful_rom.sf_st_loc S) = None
         -> Pr_code (x ← stateful_rom.forge_body S bit candidate ;;
                    k x) h = dnull).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_forge_repeated_no_setup :
  forall (S0 : stateful_rom.stateful_rom_scheme) (q_s q_h : nat) (candidate :
                                                           stateful_rom.sf_Msg S0 ×
                                                           stateful_rom.sf_Sig S0)
         (answer : bool),
         AdvOf (Shrincs.games.stateful_rom.EUCMA_game S0 q_s q_h)
           (guard_calls (stateful_rom.FORGE, (stateful_rom.sf_Msg S0 × stateful_rom.sf_Sig S0, 'bool)) candidate 2
              answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_sign_budget_abort :
  forall (S : stateful_rom.stateful_rom_scheme) (q_s : nat) (cm : stateful_rom.sf_Msg S)
         (h : heap) (st : stateful_rom.sf_Sk S × stateful_rom.sf_Pk S),
         get_heap h (stateful_rom.sf_st_loc S) = Some st
         -> get_heap h stateful_rom.sf_done_loc = false
           -> q_s <= get_heap h stateful_rom.sf_scnt_loc
             -> Pr_code (stateful_rom.sign_body S q_s cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_hash_budget_abort :
  forall (S : stateful_rom.stateful_rom_scheme) (q_h : nat) (x : stateful_rom.sf_Hin S)
         (h : heap) (st : stateful_rom.sf_Sk S × stateful_rom.sf_Pk S),
         get_heap h (stateful_rom.sf_st_loc S) = Some st
         -> get_heap h stateful_rom.sf_done_loc = false
           -> q_h <= get_heap h stateful_rom.sf_hcnt_loc
             -> Pr_code (stateful_rom.hash_body S q_h x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_forge_budget_abort :
  forall (S : stateful_rom.stateful_rom_scheme) (bit : bool) (candidate : stateful_rom.sf_Msg S × stateful_rom.sf_Sig S)
         (h : heap) (st : stateful_rom.sf_Sk S × stateful_rom.sf_Pk S),
         get_heap h (stateful_rom.sf_st_loc S) = Some st
         -> get_heap h stateful_rom.sf_done_loc = true
           -> Pr_code (stateful_rom.forge_body S bit candidate) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_gen_invalid :
  forall (S : stateful_rom.stateful_rom_scheme) (sp : stateful_rom.sf_Setup S),
         ~~ stateful_rom.sf_setup_valid S sp -> stateful_rom.gen_body S sp = fail).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_gen_twice_abort :
  forall (S : stateful_rom.stateful_rom_scheme) (sp : stateful_rom.sf_Setup S) (h : heap)
         (st : stateful_rom.sf_Sk S × stateful_rom.sf_Pk S),
         get_heap h (stateful_rom.sf_st_loc S) = Some st
         -> Pr_code (stateful_rom.gen_body S sp) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_sign_no_key :
  forall (S : stateful_rom.stateful_rom_scheme) (q_s : nat) (cm : stateful_rom.sf_Msg S) (h : heap),
         get_heap h (stateful_rom.sf_st_loc S) = None
         -> Pr_code (stateful_rom.sign_body S q_s cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_hash_only :
  forall (S : stateful_rom.stateful_rom_scheme) (q_s q_h : nat)
    (x : stateful_rom.sf_Hin S) (n : nat) (answer : bool),
  AdvOf (Shrincs.games.stateful_rom.EUCMA_game S q_s q_h)
    (guard_calls (stateful_rom.HASH, (stateful_rom.sf_Hin S, 'option (stateful_rom.sf_Hout S))) x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_gen_after_forge :
  forall (S : stateful_rom.stateful_rom_scheme) (sp : stateful_rom.sf_Setup S) (h : heap),
         get_heap h stateful_rom.sf_done_loc = true -> Pr_code (stateful_rom.gen_body S sp) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_sign_after_forge :
  forall (S : stateful_rom.stateful_rom_scheme) (q_s : nat) (cm : stateful_rom.sf_Msg S) (h : heap),
         get_heap h stateful_rom.sf_done_loc = true
         -> Pr_code (stateful_rom.sign_body S q_s cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_hash_after_forge :
  forall (S : stateful_rom.stateful_rom_scheme) (q_h : nat) (x : stateful_rom.sf_Hin S) (h : heap),
         get_heap h stateful_rom.sf_done_loc = true -> Pr_code (stateful_rom.hash_body S q_h x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.lib.guard.stateful_rom.sf_forge_after_forge :
  forall (S : stateful_rom.stateful_rom_scheme) (b : bool) (candidate : stateful_rom.sf_Msg S × stateful_rom.sf_Sig S)
         (h : heap),
         get_heap h stateful_rom.sf_done_loc = true
         -> Pr_code (stateful_rom.forge_body S b candidate) h = Pr_code fail h).

End Stateful_experiment_pins.

Module Separated_reprogramming_pins.

Check (@Shrincs.internal.ssprove.lib.guard.reprogram_sep.ro_sep_query_no_setup :
  forall (Pfx X R0 I : choice_type) (sep : X -> I) (dPfx : dist Pfx) (dR : dist R0)
         (qh : nat) (x : Pfx × X) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.reprogram_sep.RO_repro_sep Pfx X R0 I sep dPfx dR qh)
           (guard_calls (QUERY, (Pfx × X, R0)) x 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.reprogram_sep.ro_sep_query_over_budget :
  forall (Pfx X R0 I : choice_type) (sep : X -> I) (dPfx : dist Pfx) (dR : dist R0)
         (qh : nat) (x : Pfx × X) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.reprogram_sep.RO_repro_sep Pfx X R0 I sep dPfx dR qh)
           (guard_calls (QUERY, (Pfx × X, R0)) x qh.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.reprogram_sep.ro_sep_repro_no_setup :
  forall (Pfx X R0 I : choice_type) (sep : X -> I) (dPfx : dist Pfx) (dR : dist R0)
         (qh : nat) (x : X) (answer : bool),
         LosslessCode dR
         -> AdvOf (Shrincs.internal.ssprove.lib.toolkit.reprogram_sep.RO_repro_sep Pfx X R0 I sep dPfx dR qh)
             (guard_calls (REPRO, (X, Pfx)) x 1 answer) =
           0%R).

Check (@Shrincs.internal.ssprove.lib.guard.reprogram_sep.ro_sep_repro_over_budget :
  forall (Pfx X R0 I : choice_type) (sep : X -> I) (dPfx : dist Pfx) (dR : dist R0)
         (qh : nat) (x : X) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.reprogram_sep.RO_repro_sep Pfx X R0 I sep dPfx dR qh)
           (guard_calls (REPRO, (X, Pfx)) x 2 answer) =
         0%R).

End Separated_reprogramming_pins.

Module Reprogramming_pins.

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.guard_resolve_repro :
  forall (Pfx X R : choice_type) (dPfx : dist Pfx) (dR : dist R) (qh qp : nat) (b : bool) (x : X),
         resolve (Shrincs.internal.ssprove.lib.toolkit.ro_plus.RO_repro Pfx X R dPfx dR qh qp b) (REPRO, (X, Pfx)) x =
         (rc ← get ro_rcnt_loc ;;
          #assert rc < qp ;;
          #put ro_rcnt_loc := rc.+1 ;;
          r ← dPfx ;;
          (if b
           then
            m ← get ro_map_loc Pfx X R ;;
           y ← dR ;;
           #put ro_map_loc Pfx X R := setm m (r, x) y ;;
           ret r
           else ret r))).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_repro_exhausted :
  forall (Pfx X R0 : choice_type) (dPfx : dist Pfx) (dR : dist R0) (qh qp : nat)
         (b : bool) (x : X) (answer : bool) (n : nat) (h : heap),
         qp <= get_heap h ro_rcnt_loc + n
         -> Pr_code
             (code_link (guard_repeat (REPRO, (X, Pfx)) x n.+1 answer)
                (Shrincs.internal.ssprove.lib.toolkit.ro_plus.RO_repro Pfx X R0 dPfx dR qh qp b))
             h =
           dnull).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_repro_over_budget :
  forall (Pfx X R0 : choice_type) (dPfx : dist Pfx) (dR : dist R0) (qh qp : nat)
         (x : X) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.RO_repro Pfx X R0 dPfx dR qh qp)
           (guard_calls (REPRO, (X, Pfx)) x qp.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_query_no_setup :
  forall (Pfx X R0 : choice_type) (dPfx : dist Pfx) (dR : dist R0) (qh qp : nat)
         (x : Pfx × X) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.RO_repro Pfx X R0 dPfx dR qh qp)
           (guard_calls (QUERY, (Pfx × X, R0)) x 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_query_over_budget :
  forall (Pfx X R0 : choice_type) (dPfx : dist Pfx) (dR : dist R0) (qh qp : nat)
         (x : Pfx × X) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.RO_repro Pfx X R0 dPfx dR qh qp)
           (guard_calls (QUERY, (Pfx × X, R0)) x qh.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_repro_no_setup :
  forall (Pfx X R0 : choice_type) (dPfx : dist Pfx) (dR : dist R0) (qh qp : nat)
         (x : X) (answer : bool),
         LosslessCode dR
         -> AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.RO_repro Pfx X R0 dPfx dR qh qp)
             (guard_calls (REPRO, (X, Pfx)) x 1 answer) =
           0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_test_query_no_setup :
  forall (x : 'fin 3 × 'nat) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.ROPlusTest.test_game)
           (guard_calls (QUERY, ('fin 3 × 'nat, 'bool)) x 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_test_query_over_budget :
  forall (x : 'fin 3 × 'nat) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.ROPlusTest.test_game)
           (guard_calls (QUERY, ('fin 3 × 'nat, 'bool)) x 6 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_test_repro_no_setup :
  forall (x : nat) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.ROPlusTest.test_game)
           (guard_calls (REPRO, ('nat, 'fin 3)) x 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.lib.guard.ro_plus.ro_test_repro_over_budget :
  forall (x : nat) (answer : bool),
         AdvOf (Shrincs.internal.ssprove.lib.toolkit.ro_plus.ROPlusTest.test_game)
           (guard_calls (REPRO, ('nat, 'fin 3)) x 2 answer) =
         0%R).

End Reprogramming_pins.

Module Fxmss_hybrid_pins.

(* ------------------------------------------------------------------ *)
(** ** Generic leaf hybrids *)

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.hybrids.g_forge_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge P Q random_keys random_r preassigned keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

(* ------------------------------------------------------------------ *)
(** ** Named leaf hybrids *)

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_keyed_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_keyed P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_sampledkey_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_sampledkey P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_randomized_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.games.G_forge_randomized P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_filtered_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_keep)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_filtered P Q keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_digest_filtered_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_digest_filtered P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_known_anchor_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_known_anchor P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_matching_leaf_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_matching_leaf P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit) (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.named.g_forge_reject_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.filtered.G_forge_reject P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

End Fxmss_hybrid_pins.

Module Concrete_experiment_pins.

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_gen_no_setup :
  forall (q_s q_h : nat) (sp : stateful_rom.sf_Setup fxmss_sf_scheme) (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls (stateful_rom.GEN, (stateful_rom.sf_Setup fxmss_sf_scheme, stateful_rom.sf_Pk fxmss_sf_scheme))
              sp 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_gen_over_budget :
  forall (q_s q_h : nat) (sp : stateful_rom.sf_Setup fxmss_sf_scheme) (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls (stateful_rom.GEN, (stateful_rom.sf_Setup fxmss_sf_scheme, stateful_rom.sf_Pk fxmss_sf_scheme))
              sp 2 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_sign_no_setup :
  forall (q_s q_h : nat) (cm : stateful_rom.sf_Msg fxmss_sf_scheme) (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls
              (stateful_rom.SIGN, (stateful_rom.sf_Msg fxmss_sf_scheme, 'option (stateful_rom.sf_Sig fxmss_sf_scheme)))
              cm 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_sign_repeated_no_setup :
  forall (q_s q_h : nat) (cm : stateful_rom.sf_Msg fxmss_sf_scheme) (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls
              (stateful_rom.SIGN, (stateful_rom.sf_Msg fxmss_sf_scheme, 'option (stateful_rom.sf_Sig fxmss_sf_scheme)))
              cm q_s.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_hash_no_setup :
  forall (q_s q_h : nat) (x : stateful_rom.sf_Hin fxmss_sf_scheme) (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls
              (stateful_rom.HASH, (stateful_rom.sf_Hin fxmss_sf_scheme, 'option (stateful_rom.sf_Hout fxmss_sf_scheme)))
              x 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_hash_over_budget :
  forall (q_s q_h : nat) (x : stateful_rom.sf_Hin fxmss_sf_scheme) (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls
              (stateful_rom.HASH, (stateful_rom.sf_Hin fxmss_sf_scheme, 'option (stateful_rom.sf_Hout fxmss_sf_scheme)))
              x q_h.+1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_forge_no_setup :
  forall (q_s q_h : nat) (candidate : stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme)
         (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls
              (stateful_rom.FORGE, (stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme, 'bool))
              candidate 1 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_terminal_no_key :
  forall (bit : bool) (candidate : stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme)
         (T : choiceType) (k : bool -> raw_code T) (h : heap),
         get_heap h (stateful_rom.sf_st_loc fxmss_sf_scheme) = None
         -> Pr_code (x ← stateful_rom.forge_body fxmss_sf_scheme bit candidate ;;
                    k x) h = dnull).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_forge_repeated_no_setup :
  forall (q_s q_h : nat) (candidate : stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme)
         (answer : bool),
         AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
           (guard_calls
              (stateful_rom.FORGE, (stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme, 'bool))
              candidate 2 answer) =
         0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_sign_budget_abort :
  forall (q_s : nat) (cm : stateful_rom.sf_Msg fxmss_sf_scheme) (h : heap) (st : stateful_rom.sf_Sk fxmss_sf_scheme × stateful_rom.sf_Pk fxmss_sf_scheme),
         get_heap h (stateful_rom.sf_st_loc fxmss_sf_scheme) = Some st
         -> get_heap h stateful_rom.sf_done_loc = false
           -> q_s <= get_heap h stateful_rom.sf_scnt_loc
             -> Pr_code (stateful_rom.sign_body fxmss_sf_scheme q_s cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_hash_budget_abort :
  forall (q_h : nat) (x : stateful_rom.sf_Hin fxmss_sf_scheme) (h : heap) (st : stateful_rom.sf_Sk fxmss_sf_scheme × stateful_rom.sf_Pk fxmss_sf_scheme),
         get_heap h (stateful_rom.sf_st_loc fxmss_sf_scheme) = Some st
         -> get_heap h stateful_rom.sf_done_loc = false
           -> q_h <= get_heap h stateful_rom.sf_hcnt_loc
             -> Pr_code (stateful_rom.hash_body fxmss_sf_scheme q_h x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_forge_budget_abort :
  forall (bit : bool) (candidate : stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme)
         (h : heap) (st : stateful_rom.sf_Sk fxmss_sf_scheme × stateful_rom.sf_Pk fxmss_sf_scheme),
         get_heap h (stateful_rom.sf_st_loc fxmss_sf_scheme) = Some st
         -> get_heap h stateful_rom.sf_done_loc = true
           -> Pr_code (stateful_rom.forge_body fxmss_sf_scheme bit candidate) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_gen_invalid :
  forall sp : stateful_rom.sf_Setup fxmss_sf_scheme,
         ~~ stateful_rom.sf_setup_valid fxmss_sf_scheme sp -> stateful_rom.gen_body fxmss_sf_scheme sp = fail).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_gen_twice_abort :
  forall (sp : stateful_rom.sf_Setup fxmss_sf_scheme) (h : heap) (st : stateful_rom.sf_Sk fxmss_sf_scheme × stateful_rom.sf_Pk fxmss_sf_scheme),
         get_heap h (stateful_rom.sf_st_loc fxmss_sf_scheme) = Some st
         -> Pr_code (stateful_rom.gen_body fxmss_sf_scheme sp) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_sign_no_key :
  forall (q_s : nat) (cm : stateful_rom.sf_Msg fxmss_sf_scheme) (h : heap),
         get_heap h (stateful_rom.sf_st_loc fxmss_sf_scheme) = None
         -> Pr_code (stateful_rom.sign_body fxmss_sf_scheme q_s cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_hash_only :
  forall (q_s q_h : nat) (x : stateful_rom.sf_Hin fxmss_sf_scheme) (n : nat) (answer : bool),
  AdvOf (Shrincs.schemes.fxmss_eucma_game q_s q_h)
    (guard_calls (stateful_rom.HASH, (stateful_rom.sf_Hin fxmss_sf_scheme,
      'option (stateful_rom.sf_Hout fxmss_sf_scheme))) x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_gen_after_forge :
  forall (sp : stateful_rom.sf_Setup fxmss_sf_scheme) (h : heap),
         get_heap h stateful_rom.sf_done_loc = true
         -> Pr_code (stateful_rom.gen_body fxmss_sf_scheme sp) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_sign_after_forge :
  forall (q_s : nat) (cm : stateful_rom.sf_Msg fxmss_sf_scheme) (h : heap),
         get_heap h stateful_rom.sf_done_loc = true
         -> Pr_code (stateful_rom.sign_body fxmss_sf_scheme q_s cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_hash_after_forge :
  forall (q_h : nat) (x : stateful_rom.sf_Hin fxmss_sf_scheme) (h : heap),
         get_heap h stateful_rom.sf_done_loc = true
         -> Pr_code (stateful_rom.hash_body fxmss_sf_scheme q_h x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.experiment.fxmss_eucma_forge_after_forge :
  forall (b : bool) (candidate : stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme)
         (h : heap),
         get_heap h stateful_rom.sf_done_loc = true
         -> Pr_code (stateful_rom.forge_body fxmss_sf_scheme b candidate) h = Pr_code fail h).

End Concrete_experiment_pins.

(** PORT-12: batched leaf and committed-message guards. *)
From Shrincs.internal.ssprove.fxmss Require Import leaf.opening leaf.known_message_game guard.leaf.
Module Leaf_batch_pins.
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.leaf_opening_check_no_setup :
  forall (P : shrincs_fxmss_params) (q : leaf_opening_opening) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.opening.G_leaf_opening P)
    (guard_calls (leaf_opening_check, (leaf_opening_opening, 'bool)) q 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.leaf_opening_gen_repeated :
  forall (P : shrincs_fxmss_params) (sp : shrincs_fxmss_structure) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.opening.G_leaf_opening P)
    (guard_calls (leaf_opening_gen, (shrincs_fxmss_structure, leaf_opening_public)) sp n answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.leaf_opening_sign_repeated :
  forall (P : shrincs_fxmss_params) (q : 'nat × bytes 32) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.opening.G_leaf_opening P)
    (guard_calls (leaf_opening_sign, ('nat × bytes 32, 'option leaf_opening_signature))
      q n answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.leaf_opening_eval_repeated :
  forall (P : shrincs_fxmss_params) (q : leaf_opening_eval_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.opening.G_leaf_opening P)
    (guard_calls (leaf_opening_eval, (leaf_opening_eval_input, bytes 16)) q n answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.leaf_opening_check_budget_abort :
  forall (P : shrincs_fxmss_params) (bit : bool) (q : leaf_opening_opening)
    (st : leaf_opening_state) (h : heap),
  get_heap h leaf_opening_st_loc = Some st ->
  size (shrincs_fxmss_schedule st.2) <= q.1 ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.opening.G_leaf_opening P bit)
    (leaf_opening_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.known_message_check_no_setup :
  forall (P : shrincs_fxmss_params) (q : leaf_opening_opening) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.known_message_game.G_known_message P)
    (guard_calls (known_message_check, (leaf_opening_opening, 'bool)) q 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.known_message_check_budget_abort :
  forall (P : shrincs_fxmss_params) (bit : bool) (q : leaf_opening_opening)
    (st : leaf_opening_state) (h : heap),
  get_heap h leaf_opening_st_loc = Some st ->
  size (shrincs_fxmss_schedule st.2) <= q.1 ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.known_message_game.G_known_message P bit)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.leaf.known_message_sign_consumes_failed :
  forall (j : nat) (st : leaf_opening_state) (h : heap),
  get_heap h leaf_opening_st_loc = Some st ->
  j < size (shrincs_fxmss_schedule st.2) ->
  j \notin get_heap h leaf_opening_slog_loc ->
  nth None (get_heap h known_message_cache_loc) j = None ->
  Pr_code (known_message_sign_body j) h = Pr_code (ret None)
    (set_heap h leaf_opening_slog_loc (j :: get_heap h leaf_opening_slog_loc))).
End Leaf_batch_pins.

(** PORT-12: seed-sharing batch scheduler guards. *)
From Shrincs.internal.ssprove.lib Require Import games.scheduled_batch guard.scheduled_batch.
From Shrincs.internal.ssprove.fxmss Require Import leaf.batch leaf.fixed_batch guard.batch.
Module Scheduled_batch_pins.
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_ud_gen_invalid_pin :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (answer : bool),
  target_class pin.1 ->
  AdvOf (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_ud T target_class p pin)
    (guard_calls (scheduled_gen,
      ('list ('option (th_T T)), batch_output T)) ts 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_ud_gen_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (b : bool) (h : heap),
  get_heap h scheduled_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_ud T target_class p pin b)
    (scheduled_gen, ('list ('option (th_T T)), batch_output T)) ts) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_ud_eval_repeated :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (q : th_T T × th_M T) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_ud T target_class p pin)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) q n answer) = 0%R).
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_pre_gen_invalid_pin :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (answer : bool),
  target_class pin.1 ->
  AdvOf (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_pre T target_class p pin)
    (guard_calls (scheduled_gen,
      ('list ('option (th_T T)), batch_output T)) ts 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_pre_gen_phase_abort :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (ts : seq (option (th_T T))) (b : bool) (h : heap),
  get_heap h scheduled_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_pre T target_class p pin b)
    (scheduled_gen, ('list ('option (th_T T)), batch_output T)) ts) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_pre_eval_repeated :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (q : th_T T × th_M T) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_pre T target_class p pin)
    (guard_calls (EVAL, (th_T T × th_M T, th_N T)) q n answer) = 0%R).
Check (Shrincs.internal.ssprove.lib.guard.scheduled_batch.scheduled_pre_check_no_setup :
  forall (T : thf) (target_class : th_T T -> bool) (p : nat)
    (pin : th_T T × th_M T) (q : 'nat × th_M T) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.lib.games.scheduled_batch.G_scheduled_pre T target_class p pin)
    (guard_calls (scheduled_check, ('nat × th_M T, 'bool)) q 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.batch.leaf_batch_ud_sign_no_setup :
  forall (s : nat) (p : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.batch.G_leaf_batch_ud s p)
    (guard_calls (leaf_batch_sign, ('unit, 'option fixed_signature))
      tt 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.batch.leaf_batch_pre_sign_no_setup :
  forall (p : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.batch.G_leaf_batch_pre p)
    (guard_calls (leaf_batch_sign, ('unit, 'option fixed_signature))
      tt 1 answer) = 0%R).
Check (Shrincs.internal.ssprove.fxmss.guard.batch.leaf_batch_pre_check_no_setup :
  forall (p : nat) (q : 'nat × th_M shrincs_thf) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.leaf.batch.G_leaf_batch_pre p)
    (guard_calls (leaf_batch_check, ('nat × th_M shrincs_thf, 'bool))
      q 1 answer) = 0%R).
End Scheduled_batch_pins.

(* Full-signature and tree-classifier protocol guards. *)
From Shrincs.internal.ssprove.fxmss Require Import tree.forgery guard.forgery.

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.forgery.forge_full_signature_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (keep : shrincs_fxmss_full_keep)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.forgery.G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

From Shrincs.internal.ssprove.fxmss Require Import tree.classify guard.tree.

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_gen_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_gen_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_sign_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_hash_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_hash_over_budget :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_forge_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_gen_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_sign_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_sign_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_sign_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_hash_only :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_hash_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_hash_budget_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_forge_after_forge :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (@Shrincs.internal.ssprove.fxmss.guard.tree.gtree_gen_twice_abort :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources)
    (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.tree.classify.G_tree_free P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).


Module Leaf_context_pins.
From Shrincs.internal.ssprove.fxmss Require Import
  repro.games digest.games guard.repro guard.digest.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming context *)

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_gen_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_gen_over_budget :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_sign_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_sign_over_budget :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_hash_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_hash_over_budget :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_forge_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_gen_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_sign_no_key :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_sign_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_sign_budget_abort :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_hash_only :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_hash_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_hash_budget_abort :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_forge_no_key :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_forge_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.repro.g_forge_reprogrammed_gen_twice_abort :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.repro.games.G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

(* ------------------------------------------------------------------ *)
(** ** Digest context *)

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_gen_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_gen_over_budget :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (sp : shrincs_fxmss_setup) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp 2 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_sign_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_sign_over_budget :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm (shrincs_fxmss_sign_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_hash_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_hash_over_budget :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (x : shrincs_fxmss_hmsg_input) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x (shrincs_fxmss_hash_budget Q).+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_forge_no_setup :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls shrincs_fxmss_forge_op candidate 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_gen_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (sp : shrincs_fxmss_setup) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_sign_no_key :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_sign_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (cm : shrincs_fxmss_message) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_sign_budget_abort :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (cm : shrincs_fxmss_message) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_sign_budget Q <= get_heap h shrincs_fxmss_scnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_hash_only :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (x : shrincs_fxmss_hmsg_input) (n : nat) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter)
    (guard_calls (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x n answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_hash_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_hash_budget_abort :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (x : shrincs_fxmss_hmsg_input) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  get_heap h shrincs_fxmss_done_loc = false ->
  (shrincs_fxmss_hash_budget Q <= get_heap h shrincs_fxmss_hcnt_loc)%N ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_forge_no_key :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_forge_after_forge :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)) candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.digest_gen_twice_abort :
  forall (P : params.shrincs_fxmss_params) (Q : params.shrincs_fxmss_resources) (filter : bool) (bit : bool) (sp : shrincs_fxmss_setup) (h : heap)
    (st : shrincs_fxmss_state),
  get_heap h shrincs_fxmss_st_loc = Some st ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest P Q filter bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) sp) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.g_digest_preassigned_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (bit : bool)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest_preassigned P Q bit) shrincs_fxmss_forge_op candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.g_digest_filtered_forge_no_key :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (bit : bool)
    (candidate : shrincs_fxmss_message × shrincs_fxmss_bytes) (h : heap),
  get_heap h shrincs_fxmss_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.digest.games.G_digest_filtered P Q bit) shrincs_fxmss_forge_op candidate) h = Pr_code fail h).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.g_digest_preassigned_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest_preassigned P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.digest.g_digest_filtered_sign_no_setup :
  forall (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources) (cm : shrincs_fxmss_message) (answer : bool),
  AdvOf (Shrincs.internal.ssprove.fxmss.digest.games.G_digest_filtered P Q)
    (guard_calls (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm 1 answer) = 0%R).

End Leaf_context_pins.


Module Leaf_ud_prepared_pins.
From Shrincs.internal.ssprove.fxmss Require Import shape leaf.uniform.
From Shrincs.internal.ssprove.fxmss.guard Require Import uniform.
Check (Shrincs.internal.ssprove.fxmss.guard.uniform.leaf_roots_sign_no_setup :
  forall (r : nat) (h : heap),
  get_heap h leaf_batch_cache_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.uniform.G_leaf_roots r)
    (leaf_batch_sign, ('unit, 'option fixed_signature)) tt) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.uniform.leaf_roots_gen_phase_abort :
  forall (r : nat) (q : shrincs_fxmss_structure × shrincs_fxmss_digest_table) (h : heap),
  get_heap h leaf_prepared_done_loc = true ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.uniform.G_leaf_roots r)
    (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table, fixed_public)) q) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.uniform.leaf_roots_gen_illegal :
  forall (r : nat) (q : shrincs_fxmss_structure × shrincs_fxmss_digest_table) (h : heap),
  ~~ shrincs_fxmss_structure_legal q.1.1 q.1.2 ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.uniform.G_leaf_roots r)
    (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table, fixed_public)) q) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.uniform.leaf_roots_eval_in_class :
  forall (r : nat) (q : th_T shrincs_thf × th_M shrincs_thf) (h : heap),
  wots_c_hash_class q.1 ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.uniform.G_leaf_roots r)
    (EVAL, (th_T shrincs_thf × th_M shrincs_thf, bytes 16)) q) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.uniform.leaf_roots_sign_no_setup_adv :
  forall (r0 r1 : nat) (answer : bool),
  AdvOf (fun b => Shrincs.internal.ssprove.fxmss.leaf.uniform.G_leaf_roots
    (if b then r0 else r1))
    (guard_calls (leaf_batch_sign, ('unit, 'option fixed_signature))
      tt 1 answer) = 0%R).
End Leaf_ud_prepared_pins.
From Shrincs.internal.ssprove.fxmss Require Import guard.prf_msg.

Check (Shrincs.internal.ssprove.fxmss.guard.prf_msg.shrincs_prf_msg_query_repeated_abort :
  forall (q : nat) (m : kh_M shrincs_khf_prf_msg) (answer : bool),
  AdvOf (Shrincs.schemes.shrincs_prf_msg_game q)
    (guard_calls (prf.FQUERY,
      (kh_M shrincs_khf_prf_msg, kh_N shrincs_khf_prf_msg)) m q.+1 answer) = 0%R).

Check (Shrincs.internal.ssprove.fxmss.guard.prf_msg.shrincs_prf_msg_query_budget_abort :
  forall (q : nat) (b : bool) (m : kh_M shrincs_khf_prf_msg) (h : heap),
  (q <= size (get_heap h (prf.prf_qs_loc shrincs_khf_prf_msg)))%N ->
  Pr_code (resolve (Shrincs.schemes.shrincs_prf_msg_game q b)
    (prf.FQUERY, (kh_M shrincs_khf_prf_msg, kh_N shrincs_khf_prf_msg)) m) h =
    Pr_code fail h).

Module Leaf_primitive_pins.
From Shrincs.internal.ssprove.fxmss Require Import leaf.prepared leaf.commitments.
From Shrincs.internal.ssprove.fxmss.guard Require Import prepared.
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_gen_phase_abort :
  forall (r : nat) (sp : shrincs_fxmss_structure) (sd : shrincs_fxmss_digest_table) (h : heap),
  isSome (get_heap h prepared_leaf_st_loc) ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table, leaf_opening_public)) (sp, sd)) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_gen_illegal :
  forall (r : nat) (sp : shrincs_fxmss_structure) (sd : shrincs_fxmss_digest_table) (h : heap),
  ~~ shrincs_fxmss_structure_legal sp.1 sp.2 ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table, leaf_opening_public)) (sp, sd)) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_gen_missing_digest :
  forall (r : nat) (sp : shrincs_fxmss_structure) (sd : shrincs_fxmss_digest_table) (h : heap),
  ~~ leaf_digest_total (shrincs_fxmss_schedule sp) sd ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table, leaf_opening_public)) (sp, sd)) h =
    Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_sign_no_setup :
  forall (r : nat) (j : nat) (h : heap),
  get_heap h prepared_leaf_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j) h = Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_check_no_setup :
  forall (r : nat) (q : leaf_opening_opening) (h : heap),
  get_heap h prepared_leaf_st_loc = None ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_sign_consumed :
  forall (r : nat) (j : nat) (h : heap),
  j \in get_heap h prepared_leaf_slog_loc ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j) h = Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_sign_outside_schedule :
  forall (r : nat) (j : nat) (h : heap) (st : leaf_opening_state),
  get_heap h prepared_leaf_st_loc = Some st ->
  ~~ (j < size (shrincs_fxmss_schedule st.2)) ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j) h = Pr_code fail h).
Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_check_outside_schedule :
  forall (r : nat) (q : leaf_opening_opening) (h : heap) (st : leaf_opening_state),
  get_heap h prepared_leaf_st_loc = Some st ->
  ~~ (q.1 < size (shrincs_fxmss_schedule st.2)) ->
  Pr_code (resolve (Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf r)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h).
End Leaf_primitive_pins.

Check (Shrincs.internal.ssprove.fxmss.guard.prepared.prepared_leaf_sign_no_setup_adv :
  forall (r0 r1 : nat) (answer : bool),
  AdvOf (fun b => Shrincs.internal.ssprove.fxmss.leaf.prepared.G_prepared_leaf
    (if b then r0 else r1))
    (guard_calls (known_message_sign, ('nat, 'option leaf_opening_signature)) 0 1 answer) = 0%R).
