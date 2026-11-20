(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bound.leaf

    The uniform-guess telescope and the chain collision/preimage terms close the
    leaf bound. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp Require Import reals.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  leaf.uniform params games instance leaf.known_message_game leaf.known_message
    leaf.context
  leaf.endpoints leaf.prepared leaf.chain_tcr.reduction leaf.chain_tcr.hop
  leaf.chain_pre.reduction leaf.chain_pre.hop bridge.adapter bound.canonical.

(* ------------------------------------------------------------------ *)
(** ** Leaf uniform guesses bound *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma leaf_ud_step_valid s (A : nom_package)
    (VA : ValidPackage (loc A) I_leaf_prepared_ud A_export A) :
  (s < 14)%nat ->
  Adv (G_leaf_roots s) (G_leaf_roots s.+1) A =
  AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
    (A ∘ R_leaf_prepared_ud s).
Proof.
move=> hs.
rewrite (Adv_perfect_l (leaf_prepared_ud_perfect true s hs)).
rewrite (Adv_perfect_r (leaf_prepared_ud_perfect false s hs)).
exact: Adv_reduction.
Qed.

Lemma leaf_ud_telescope_valid (A : nom_package)
    (VA : ValidPackage (loc A) I_leaf_prepared_ud A_export A) :
  (Adv (G_leaf_roots 0) (G_leaf_roots 14) A <=
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (A ∘ R_leaf_prepared_ud s))%R.
Proof.
have h := Adv_hybrid_dep (IGame := I_leaf_prepared_ud) (n := 14)
  (Multi := fun b => as_nom (G_leaf_roots (if b then 0 else 14)))
  (Game := fun s b => as_nom (G_leaf_roots (if b then s else s.+1)))
  (A := A).
have ht : (Adv (G_leaf_roots 0) (G_leaf_roots 14) A <=
    \sum_(0 <= s < 14) Adv (G_leaf_roots s) (G_leaf_roots s.+1) A)%R.
{ apply: h; first exact: perfect_refl.
  - exact: perfect_refl.
  - by move=> i hi; apply: perfect_refl. }
have he : (\sum_(0 <= s < 14)
    Adv (G_leaf_roots s) (G_leaf_roots s.+1) A =
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (A ∘ R_leaf_prepared_ud s))%R.
{ apply: eq_big_nat => s /andP[_ hs].
  exact: leaf_ud_step_valid VA hs. }
by rewrite -he.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages bound *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.
Local Opaque R_known_message known_message_coll_filter G_prepared_leaf R_chain_tcr
  R_chain_pre
  SMTCR_game SMPRE_game R_leaf_roots G_leaf_roots fxmss_forger shrincs_fxmss_rom_adapter
    Adv.

Lemma prepared_leaf_context_chain_tcr Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 2)
      (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 3) A =
    AdvOf (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget)
      (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_chain_tcr).
Proof.
rewrite Adv_reduction.
rewrite (Adv_perfect_l (r_chain_tcr_perfect true)) (Adv_perfect_r (r_chain_tcr_perfect
  false)).
rewrite Adv_reduction.
by rewrite -!sep_link_assoc.
Qed.

Lemma prepared_leaf_context_preimage Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 3)
      (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 4) A =
    AdvOf (SMPRE_game shrincs_thf wots_c_hash_class r_chain_pre_budget)
      (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_chain_pre).
Proof.
rewrite Adv_reduction.
rewrite (Adv_perfect_l (r_chain_pre_perfect true)) (Adv_perfect_r (r_chain_pre_perfect
  false)).
rewrite Adv_reduction.
by rewrite -!sep_link_assoc.
Qed.

Lemma prepared_leaf_context_endpoint Q LA c vc :
  Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 4)
      (R_leaf_roots Q false ∘ G_leaf_roots 14)
      (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) = 0.
Proof.
have hzrule (G H A : nom_package) :
    distr.mu (Pr' (A ∘ G)%sep) true = 0 ->
    distr.mu (Pr' (A ∘ H)%sep) true = 0 -> Adv G H A = 0.
{ move=> hg hh. by rewrite AdvE hg hh subr0 normr0. }
apply: hzrule.
- exact: prepared_leaf_canonical_reject_zero.
- exact: leaf_ctx_roots_canonical_ideal_zero.
Qed.

Lemma prepared_leaf_chain_costs Q LA c vc :
  Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 2)
      (R_leaf_roots Q false ∘ G_leaf_roots 14)
      (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) <=
    AdvOf (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget)
      ((fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) ∘
        R_known_message Q ∘ known_message_coll_filter ∘ R_chain_tcr) +
    AdvOf (SMPRE_game shrincs_thf wots_c_hash_class r_chain_pre_budget)
      ((fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) ∘
        R_known_message Q ∘ known_message_coll_filter ∘ R_chain_pre).
Proof.
eapply le_trans; first exact: (Adv_triangle
  (G2 := R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 3)).
apply: lerD.
- by rewrite prepared_leaf_context_chain_tcr.
- eapply le_trans; first exact: (Adv_triangle
    (G2 := R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 4)).
  have hsum0 (x y z : R) : x = z -> y = 0 -> x + y <= z.
  { by move=> -> ->; rewrite addr0. }
  apply: hsum0.
  + exact: (prepared_leaf_context_preimage Q
      (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) (ltac:(typeclasses eauto))).
  + exact: (prepared_leaf_context_endpoint Q LA c vc).
Qed.
