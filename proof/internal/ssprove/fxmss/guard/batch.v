(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.batch

    Signing a batch needs its initialized cache. EVAL does not consult
    the distinguishing bit, including when it is called before GEN. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude guard.common games.scheduled_batch games.static_pre_batch.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import leaf.batch leaf.fixed_batch.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma leaf_batch_ud_sign_no_setup s p answer :
  AdvOf (G_leaf_batch_ud s p)
    (guard_calls (leaf_batch_sign, ('unit, 'option fixed_signature))
      tt 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
rewrite /G_leaf_batch_ud !sep_linkE !resolve_link.
simplify_linking.
by rewrite !Pr_code_get /=.
Qed.

Lemma leaf_batch_pre_sign_no_setup p answer :
  AdvOf (G_leaf_batch_pre p)
    (guard_calls (leaf_batch_sign, ('unit, 'option fixed_signature))
      tt 1 answer) = 0%R.
Proof.
apply: guard_adv_eq.
simplify_linking.
rewrite /G_leaf_batch_pre !sep_linkE !resolve_link.
simplify_linking.
by rewrite !Pr_code_get /=.
Qed.

Lemma leaf_batch_pre_check_no_setup p q answer :
  AdvOf (G_leaf_batch_pre p)
    (guard_calls (leaf_batch_check, ('nat × th_M shrincs_thf, 'bool))
      q 1 answer) = 0%R.
Proof.
rewrite /G_leaf_batch_pre.
ssprove_share.
apply: guard_adv_eq.
simplify_linking.
by rewrite !Pr_code_get /=.
Qed.
