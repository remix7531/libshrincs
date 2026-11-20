(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.wots.guard.public

    Protocol-abort guards for the concrete public games in schemes.v.
    These instantiate the generic guards without a hash-security premise. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common guard.kots.
From Shrincs Require Import games schemes.

Import PackageNotation kots.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Guards.
Context (node_height : spec.UInt8) (node_index : spec.UInt64)
  (tree_balanced : bool) (tree_depth : spec.UInt8).

Lemma wots_c_kots_vc_commit_no_setup (sp : SParam (wots_c_scheme node_height node_index tree_balanced tree_depth)) (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (answer : bool) :
  AdvOf (wots_c_kots_game node_height node_index tree_balanced tree_depth)
    (guard_calls (COMMIT, (SParam (wots_c_scheme node_height node_index tree_balanced tree_depth) × Msg (wots_c_scheme node_height node_index tree_balanced tree_depth), Pk (wots_c_scheme node_height node_index tree_balanced tree_depth) × 'option (Sig (wots_c_scheme node_height node_index tree_balanced tree_depth)))) (sp, m) 1 answer) = 0%R.
Proof. exact: kots_vc_commit_no_setup. Qed.

Lemma wots_c_kots_vc_commit_over_budget (sp : SParam (wots_c_scheme node_height node_index tree_balanced tree_depth)) (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (answer : bool) :
  AdvOf (wots_c_kots_game node_height node_index tree_balanced tree_depth)
    (guard_calls (COMMIT, (SParam (wots_c_scheme node_height node_index tree_balanced tree_depth) × Msg (wots_c_scheme node_height node_index tree_balanced tree_depth), Pk (wots_c_scheme node_height node_index tree_balanced tree_depth) × 'option (Sig (wots_c_scheme node_height node_index tree_balanced tree_depth)))) (sp, m) 2 answer) = 0%R.
Proof. exact: kots_vc_commit_over_budget. Qed.

Lemma wots_c_kots_vc_kforge_no_setup (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (sig : Sig (wots_c_scheme node_height node_index tree_balanced tree_depth))
    (answer : bool) :
  AdvOf (wots_c_kots_game node_height node_index tree_balanced tree_depth)
    (guard_calls (KFORGE, (Msg (wots_c_scheme node_height node_index tree_balanced tree_depth) × Sig (wots_c_scheme node_height node_index tree_balanced tree_depth), 'bool))
      (m, sig) 1 answer) = 0%R.
Proof. exact: kots_vc_kforge_no_setup. Qed.

Lemma wots_c_kots_vc_commit_phase_abort (b : bool) (sp : SParam (wots_c_scheme node_height node_index tree_balanced tree_depth))
    (m : Msg (wots_c_scheme node_height node_index tree_balanced tree_depth)) (pk : Pk (wots_c_scheme node_height node_index tree_balanced tree_depth)) (h : heap) :
  get_heap h (kots_pk_loc (wots_c_scheme node_height node_index tree_balanced tree_depth)) = Some pk ->
  Pr_code (resolve (wots_c_kots_game node_height node_index tree_balanced tree_depth b)
    (COMMIT, (SParam (wots_c_scheme node_height node_index tree_balanced tree_depth) × Msg (wots_c_scheme node_height node_index tree_balanced tree_depth), Pk (wots_c_scheme node_height node_index tree_balanced tree_depth) × 'option (Sig (wots_c_scheme node_height node_index tree_balanced tree_depth)))) (sp, m)) h =
    Pr_code fail h.
Proof. exact: kots_vc_commit_phase_abort. Qed.

End Guards.
