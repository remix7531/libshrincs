(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.batch

    The UD/PRE hybrid interface accepts the complete prepared leaf list at
    GEN. Outside-class EVAL is available before GEN and uses the batch's
    seed. Successful and failed leaf slots retain their original positions.
    The interface exposes prepared leaf roots to the grinding and tree contexts. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.static_batch games.scheduled_batch.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games leaf.fixed_batch leaf.known_message.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_batch_gen : nat := 1530.
Definition leaf_batch_sign : nat := 1531.
Definition leaf_batch_check : nat := 1532.
Definition leaf_batch_cache_loc :=
  mkloc 1530 (None : option (seq (option fixed_signature))).
Definition leaf_batch_slot_loc := mkloc 1531 0.

Definition I_leaf_batch_ud :=
  [interface
    [ leaf_batch_gen ] : { 'list fixed_leaf ~> fixed_public };
    [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature };
    [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 }
  ].

Definition C_leaf_batch_ud (s : nat) :
    package (I_scheduled_ud shrincs_thf) I_leaf_batch_ud :=
  [package [fmap leaf_batch_cache_loc; leaf_batch_slot_loc];
    [ leaf_batch_gen ] : { 'list fixed_leaf ~> fixed_public } (leaves) {
      r ← call [ scheduled_gen ] :
        { 'list ('option (th_T shrincs_thf)) ~> batch_output shrincs_thf }
        (fixed_ud_requests s leaves) ;;
      let cache := fixed_complete true s leaves r in
      #put leaf_batch_cache_loc := Some [seq entry.2 | entry <- cache] ;;
      ret (r.1, [seq entry.1 | entry <- cache])
    };
    [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature } (_) {
      cache ← getSome leaf_batch_cache_loc ;;
      i ← get leaf_batch_slot_loc ;;
      #put leaf_batch_slot_loc := i.+1 ;;
      ret (nth None cache i)
    };
    [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } (q) {
      call [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } q
    }
  ].

Definition R_leaf_batch_ud s :=
  C_leaf_batch_ud s ∘ R_scheduled_ud shrincs_thf known_message_pin.
Definition G_leaf_batch_ud s p b :=
  C_leaf_batch_ud s ∘ G_scheduled_ud shrincs_thf
    wots_c_hash_class p known_message_pin b.

Lemma R_leaf_batch_ud_perfect s p b :
  perfect I_leaf_batch_ud (G_leaf_batch_ud s p b)
    (R_leaf_batch_ud s ∘ SMUD_game shrincs_thf wots_c_hash_class p b).
Proof.
rewrite /G_leaf_batch_ud /R_leaf_batch_ud -sep_link_assoc.
apply batch_context_perfect.
exact: R_scheduled_ud_perfect.
Qed.

Lemma leaf_batch_ud_advantage s p (A : adversary I_leaf_batch_ud) :
  Adv (G_leaf_batch_ud s p true) (G_leaf_batch_ud s p false) A =
  AdvOf (SMUD_game shrincs_thf wots_c_hash_class p)
    (A ∘ R_leaf_batch_ud s).
Proof.
rewrite (Adv_perfect_l (R_leaf_batch_ud_perfect s p true)).
rewrite (Adv_perfect_r (R_leaf_batch_ud_perfect s p false)).
exact: Adv_reduction.
Qed.

Definition I_leaf_batch_pre :=
  [interface
    [ leaf_batch_gen ] : { 'list fixed_leaf ~> fixed_public };
    [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature };
    [ leaf_batch_check ] : { 'nat × th_M shrincs_thf ~> 'bool };
    [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 }
  ].

Definition C_leaf_batch_pre :
    package (I_scheduled_pre shrincs_thf) I_leaf_batch_pre :=
  [package [fmap leaf_batch_cache_loc; leaf_batch_slot_loc];
    [ leaf_batch_gen ] : { 'list fixed_leaf ~> fixed_public } (leaves) {
      r ← call [ scheduled_gen ] :
        { 'list ('option (th_T shrincs_thf)) ~> batch_output shrincs_thf }
        (fixed_pre_requests leaves) ;;
      let cache := fixed_complete false 0 leaves r in
      #put leaf_batch_cache_loc := Some [seq entry.2 | entry <- cache] ;;
      ret (r.1, [seq entry.1 | entry <- cache])
    };
    [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature } (_) {
      cache ← getSome leaf_batch_cache_loc ;;
      i ← get leaf_batch_slot_loc ;;
      #put leaf_batch_slot_loc := i.+1 ;;
      ret (nth None cache i)
    };
    [ leaf_batch_check ] : { 'nat × th_M shrincs_thf ~> 'bool } (q) {
      call [ scheduled_check ] : { 'nat × th_M shrincs_thf ~> 'bool } q
    };
    [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } (q) {
      call [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } q
    }
  ].

Definition R_leaf_batch_pre :=
  C_leaf_batch_pre ∘ R_scheduled_pre shrincs_thf known_message_pin.
Definition G_leaf_batch_pre p b :=
  C_leaf_batch_pre ∘ G_scheduled_pre shrincs_thf
    wots_c_hash_class p known_message_pin b.

Lemma R_leaf_batch_pre_perfect p b :
  perfect I_leaf_batch_pre (G_leaf_batch_pre p b)
    (R_leaf_batch_pre ∘ SMPRE_game shrincs_thf wots_c_hash_class p b).
Proof.
rewrite /G_leaf_batch_pre /R_leaf_batch_pre -sep_link_assoc.
apply batch_context_perfect.
exact: R_scheduled_pre_perfect.
Qed.

Lemma leaf_batch_pre_advantage p (A : adversary I_leaf_batch_pre) :
  Adv (G_leaf_batch_pre p true) (G_leaf_batch_pre p false) A =
  AdvOf (SMPRE_game shrincs_thf wots_c_hash_class p)
    (A ∘ R_leaf_batch_pre).
Proof.
rewrite (Adv_perfect_l (R_leaf_batch_pre_perfect p true)).
rewrite (Adv_perfect_r (R_leaf_batch_pre_perfect p false)).
exact: Adv_reduction.
Qed.

(** The fixed-list contract remains available when descriptors really are
    fixed independently of the core seed. It is not a proof that grinding
    metadata can be computed with a different, independently sampled seed. *)
Lemma leaf_fixed_ud_advantage P sp pp sd s (A : adversary I_fixed_ud) :
  Adv (G_fixed_ud s (known_message_prepared P sp pp sd) true)
      (G_fixed_ud s (known_message_prepared P sp pp sd) false) A =
  AdvOf (SMUD_game shrincs_thf wots_c_hash_class
    (32 * size (shrincs_fxmss_schedule sp)))
    (A ∘ R_fixed_ud s (known_message_prepared P sp pp sd)).
Proof. by rewrite fixed_ud_advantage known_message_prepared_budget. Qed.

Lemma leaf_fixed_pre_advantage P sp pp sd (A : adversary I_fixed_pre) :
  Adv (G_fixed_pre (known_message_prepared P sp pp sd) true)
      (G_fixed_pre (known_message_prepared P sp pp sd) false) A =
  AdvOf (SMPRE_game shrincs_thf wots_c_hash_class
    (32 * size (shrincs_fxmss_schedule sp)))
    (A ∘ R_fixed_pre (known_message_prepared P sp pp sd)).
Proof. by rewrite fixed_pre_advantage known_message_prepared_budget. Qed.

Lemma leaf_ud_target_budget P sp pp sd s :
  count isSome (fixed_ud_requests s (known_message_prepared P sp pp sd)) <=
    32 * size (shrincs_fxmss_schedule sp).
Proof. rewrite -(known_message_prepared_budget P sp pp sd). exact:
  fixed_ud_target_budget. Qed.

Lemma leaf_pre_target_budget P sp pp sd :
  count isSome (fixed_pre_requests (known_message_prepared P sp pp sd)) <=
    32 * size (shrincs_fxmss_schedule sp).
Proof. rewrite -(known_message_prepared_budget P sp pp sd). exact:
  fixed_pre_target_budget. Qed.
