(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.uniform

    Prepared-leaf hybrids share the same protocol aborts at every root
    position: one legal GEN, initialized SIGN, and outside-class EVAL. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games schemes spec.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games leaf.fixed_batch leaf.batch leaf.uniform.

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma leaf_roots_sign_no_setup r h :
  get_heap h leaf_batch_cache_loc = None ->
  Pr_code (resolve (G_leaf_roots r)
    (leaf_batch_sign, ('unit, 'option fixed_signature)) tt) h =
    Pr_code fail h.
Proof.
move=> hc.
simplify_linking.
by rewrite Pr_code_get hc /=.
Qed.

Lemma leaf_roots_gen_phase_abort r q h :
  get_heap h leaf_prepared_done_loc = true ->
  Pr_code (resolve (G_leaf_roots r)
    (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      fixed_public)) q) h =
    Pr_code fail h.
Proof.
move=> hd.
simplify_linking.
by rewrite Pr_code_get hd /=.
Qed.

Lemma leaf_roots_gen_illegal r q h :
  ~~ shrincs_fxmss_structure_legal q.1.1 q.1.2 ->
  Pr_code (resolve (G_leaf_roots r)
    (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      fixed_public)) q) h =
    Pr_code fail h.
Proof.
move=> /negbTE hq.
simplify_linking.
rewrite Pr_code_get.
by case: (get_heap h leaf_prepared_done_loc) => /=; rewrite ?hq.
Qed.

Lemma leaf_roots_eval_in_class r q h :
  wots_c_hash_class q.1 ->
  Pr_code (resolve (G_leaf_roots r)
    (EVAL, (th_T shrincs_thf × th_M shrincs_thf, bytes 16)) q) h =
    Pr_code fail h.
Proof.
move=> hq.
simplify_linking.
by rewrite hq /=.
Qed.

Lemma leaf_roots_sign_no_setup_adv r0 r1 answer :
  AdvOf (fun b => G_leaf_roots (if b then r0 else r1))
    (guard_calls (leaf_batch_sign, ('unit, 'option fixed_signature))
      tt 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /=.
Qed.
