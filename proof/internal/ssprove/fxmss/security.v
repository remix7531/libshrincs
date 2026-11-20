(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.security

    The primitive losses and leaf-context couplings assemble the concrete FXMSS
    reduction bound through one uniform-guess telescope. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.stateful_rom.
From mathcomp Require Import reals.
From Shrincs Require Import games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance bridge.adapter bridge.sign prf.reduction prf.hop repro.games
  repro.hop digest.games digest.alignment bound.digest digest.filtered bound.canonical
  tree.classify tree.reduction tree.hop tree.forgery paired.reduction paired.hop
    leaf.known_message_game
  leaf.known_message leaf.context leaf.endpoints leaf.uniform leaf.prepared
  leaf.compress.reduction leaf.compress.hop leaf.grind.reduction leaf.grind.hop
  leaf.outer_hop leaf.initial_coupling leaf.prepared_coupling leaf.chain_tcr.reduction
  leaf.chain_pre.reduction bound.leaf.

(* ------------------------------------------------------------------ *)
(** ** Primitive losses *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Local Opaque G_forge_keyed G_forge_sampledkey G_forge_randomized G_forge_reprogrammed
  G_digest_preassigned G_digest_filtered G_forge_digest_filtered G_forge_reject
  G_tree_free
  prf.PRF_game R_prf R_prf_msg R_tree G_forge_full_signature R_paired fxmss_tcrx_game.

(** Proved primitive losses, including the exact digest-filter cost.
    The tree hop ends at [G_tree_free]. *)
Definition shrincs_fxmss_bound_prefix (Q : shrincs_fxmss_resources) (A : nom_package) :
  R :=
  AdvOf (prf.PRF_game shrincs_khf_prf
      (shrincs_fxmss_leaf_capacity Q * wots_c_chain_count).+1) (A ∘ R_prf Q true) +
  (AdvOf (prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_sign_budget Q).+1)
      (A ∘ R_prf_msg Q true) +
  ((shrincs_fxmss_hash_budget Q + shrincs_fxmss_sign_budget Q + 1)%:R / ((2 ^
    128)%nat)%:R +
  ((shrincs_fxmss_leaf_capacity Q)%:R * ((shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^
    256)%nat)%:R) +
   AdvOf (fxmss_tree_game (shrincs_fxmss_leaf_capacity Q - 1)) (A ∘ R_tree
     shrincs_fxmss_sha256 Q)))).

(** For arbitrary distinguishers the final hop removes only the G_forge_reject bit
    switch. The canonical theorem below also eliminates the ideal defect. *)
Lemma shrincs_fxmss_bound_reject Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_tree_free shrincs_fxmss_sha256 Q true) (G_forge_keyed shrincs_fxmss_sha256 Q
    false) A <=
    Adv (G_tree_free shrincs_fxmss_sha256 Q true) (G_forge_reject shrincs_fxmss_sha256 Q
      true) A +
    Adv (G_forge_reject shrincs_fxmss_sha256 Q false) (G_forge_keyed
      shrincs_fxmss_sha256 Q false) A.
Proof.
eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_reject shrincs_fxmss_sha256 Q
  true)).
rewrite (Adv_perfect_l (forge_reject_perfect shrincs_fxmss_sha256 Q)).
exact: lexx.
Qed.

(** Eager/lazy alignment is exact; only the preassigned filter contributes loss. *)
Lemma shrincs_fxmss_bound_digest Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_forge_reprogrammed shrincs_fxmss_sha256 Q true) (G_digest_filtered
    shrincs_fxmss_sha256 Q true) A <=
    (shrincs_fxmss_leaf_capacity Q)%:R * ((shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^
      256)%nat)%:R).
Proof.
pose B := mkpackage (loc A) A VA.
have eB : as_nom B = A by apply: eq_nom_package; reflexivity.
have ha := digest_alignment_sha256 Q true B.
have hd := digest_filter_sha256_bound Q true B.
rewrite eB in ha hd.
have hzrule (x y z : R) : x = 0 -> y <= z -> x + y <= z.
{ move=> -> hy. by rewrite add0r. }
eapply le_trans; first exact: (Adv_triangle (G2 := G_digest_preassigned
  shrincs_fxmss_sha256 Q true)).
exact: hzrule ha hd.
Qed.

Lemma shrincs_fxmss_bound_real Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_forge_keyed shrincs_fxmss_sha256 Q true) (G_tree_free shrincs_fxmss_sha256 Q
    true) A <=
    shrincs_fxmss_bound_prefix Q A.
Proof.
pose B := mkpackage (loc A) A VA.
have eB : as_nom B = A by apply: eq_nom_package; reflexivity.
have hr := repro_hop_sha256_bound Q true B.
have ht := tree_sha256_advantage Q B.
rewrite eB in hr ht.
rewrite /shrincs_fxmss_bound_prefix.
eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_sampledkey
  shrincs_fxmss_sha256 Q true)).
apply: lerD; first by rewrite (prf_key_advantage Q true A VA).
eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_randomized
  shrincs_fxmss_sha256 Q true)).
apply: lerD; first by rewrite (prf_msg_advantage Q true A VA).
eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_reprogrammed
  shrincs_fxmss_sha256 Q true)).
apply: lerD; first exact: hr.
eapply le_trans; first exact: (Adv_triangle (G2 := G_digest_filtered
  shrincs_fxmss_sha256 Q true)).
apply: lerD; first exact: shrincs_fxmss_bound_digest Q A VA.
rewrite (Adv_perfect_l (grind_hop_eq shrincs_fxmss_sha256 Q true)) ht.
exact: lexx.
Qed.

(** Remove paired collisions once, with the exact 2L-1 target budget. *)
Lemma shrincs_fxmss_bound_paired Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_tree_free shrincs_fxmss_sha256 Q true) (G_forge_reject shrincs_fxmss_sha256 Q
    true) A <=
    AdvOf (fxmss_tcrx_game (2 * shrincs_fxmss_leaf_capacity Q - 1)) (A ∘ R_paired
      shrincs_fxmss_sha256 Q) +
    Adv (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
      shrincs_fxmss_sha256) true)
      (G_forge_reject shrincs_fxmss_sha256 Q true) A.
Proof.
pose B := mkpackage (loc A) A VA.
have eB : as_nom B = A by apply: eq_nom_package; reflexivity.
have hp := paired_sha256_advantage Q B.
rewrite eB in hp.
eapply le_trans; first exact: (Adv_triangle
  (G2 := G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
    shrincs_fxmss_sha256) true)).
apply: lerD; last exact: lexx.
by rewrite hp.
Qed.

(** The canonical terminal forger turns the public advantage into one
    real-side distance. Both ideal success probabilities are zero. *)
Lemma shrincs_fxmss_canonical_single_leg q_s q_h LA c vc :
  let Q := shrincs_fxmss_resources_of q_s q_h in
  let B := (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter)%sep in
  AdvOf (fxmss_eucma_game q_s q_h) (fxmss_forger LA c vc) =
    Adv (G_forge_keyed shrincs_fxmss_sha256 Q true) (G_forge_reject shrincs_fxmss_sha256
      Q true) B.
Proof.
cbn zeta.
rewrite /fxmss_eucma_game /fxmss_forger sf_advantage_success.
rewrite (perfect_Pr (shrincs_fxmss_rom_public_internal_perfect q_s q_h true)).
rewrite sep_link_assoc.
rewrite (Adv_perfect_r (forge_reject_perfect shrincs_fxmss_sha256
  (shrincs_fxmss_resources_of q_s
  q_h))).
symmetry.
have hzrule (G H A : nom_package) :
    distr.mu (Pr' (A ∘ H)%sep) true = 0 ->
    Adv G H A = distr.mu (Pr' (A ∘ G)%sep) true.
{ move=> hz. by rewrite AdvE hz subr0 ger0_norm. }
apply: hzrule.
exact: (shrincs_fxmss_canonical_reject_zero (shrincs_fxmss_resources_of q_s q_h) false
  LA
  c vc).
Qed.

Theorem shrincs_fxmss_bound_bound q_s q_h (LA : Locations)
    (c : raw_code (stateful_rom.sf_Msg fxmss_sf_scheme ×
                   stateful_rom.sf_Sig fxmss_sf_scheme))
    (vc : ValidCode LA (stateful_rom.I_EUCMA_prefix fxmss_sf_scheme) c) :
  let Q := shrincs_fxmss_resources_of q_s q_h in
  let B := (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter)%sep in
  AdvOf (fxmss_eucma_game q_s q_h) (fxmss_forger LA c vc) <=
    shrincs_fxmss_bound_prefix Q B +
    (AdvOf (fxmss_tcrx_game (2 * shrincs_fxmss_leaf_capacity Q - 1)) (B ∘ R_paired
      shrincs_fxmss_sha256 Q) +
     Adv (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
       shrincs_fxmss_sha256) true)
       (G_forge_reject shrincs_fxmss_sha256 Q true) B).
Proof.
cbn zeta.
rewrite shrincs_fxmss_canonical_single_leg.
eapply le_trans; first exact: (Adv_triangle
  (G2 := G_tree_free shrincs_fxmss_sha256 (shrincs_fxmss_resources_of q_s q_h) true)).
apply: lerD.
- apply: shrincs_fxmss_bound_real.
- apply: shrincs_fxmss_bound_paired.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf context bounds *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Local Opaque R_known_message known_message_coll_filter G_prepared_leaf R_compress
  SMTCR_game
  R_leaf_roots G_leaf_roots G_forge_full_signature G_forge_reject fxmss_tcrx_game
    R_paired
  SMUD_game R_leaf_prepared_ud fxmss_forger shrincs_fxmss_rom_adapter Adv.

Lemma leaf_ctx_compression Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 1)
      (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 2) A =
    AdvOf (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64))
      (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_compress).
Proof.
rewrite Adv_reduction.
rewrite (Adv_perfect_l (r_compress_perfect true)) (Adv_perfect_r (r_compress_perfect
  false)).
rewrite Adv_reduction.
by rewrite -!sep_link_assoc.
Qed.

Definition leaf_ctx_middle Q (A : nom_package) : R :=
  Adv (R_leaf_roots Q true ∘ G_leaf_roots 14)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 0) A +
  (Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 0)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 1) A +
  (AdvOf (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64))
    (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_compress) +
   Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 2)
     (R_leaf_roots Q false ∘ G_leaf_roots 14) A)).

Lemma leaf_ctx_middle_bound Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_leaf_roots Q true ∘ G_leaf_roots 14)
    (R_leaf_roots Q false ∘ G_leaf_roots 14) A <=
    leaf_ctx_middle Q A.
Proof.
rewrite /leaf_ctx_middle.
eapply le_trans; first exact: (Adv_triangle
  (G2 := R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 0)).
apply: lerD; first exact: lexx.
eapply le_trans; first exact: (Adv_triangle
  (G2 := R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 1)).
apply: lerD; first exact: lexx.
eapply le_trans; first exact: (Adv_triangle
  (G2 := R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 2)).
apply: lerD; last exact: lexx.
by rewrite (leaf_ctx_compression Q A VA).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf bound *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Local Opaque R_known_message known_message_coll_filter G_known_message G_prepared_leaf
  R_compress R_grind
  SMTCR_game fxmss_grind_game R_leaf_roots G_leaf_roots G_forge_full_signature
    G_forge_reject
  fxmss_tcrx_game R_paired SMUD_game R_leaf_prepared_ud fxmss_forger
  shrincs_fxmss_rom_adapter Adv.

Lemma leaf_outer_roots_perfect Q :
  perfect I_forge (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
    shrincs_fxmss_sha256)
    true)
    (R_leaf_roots Q true ∘ G_leaf_roots 0).
Proof.
exact (perfect_trans (leaf_outer_perfect Q) (leaf_inner_first_perfect Q true)).
Qed.

Lemma leaf_ctx_outer_endpoint Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
    shrincs_fxmss_sha256) true)
    (R_leaf_roots Q true ∘ G_leaf_roots 0) A = 0.
Proof.
exact: (leaf_outer_roots_perfect Q A VA).
Qed.

Lemma leaf_ctx_inner_endpoint Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_leaf_roots Q true ∘ G_leaf_roots 14)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 0) A = 0.
Proof.
exact: (leaf_inner_last_perfect Q A VA).
Qed.

Definition leaf_ctx_middle_grind Q (A : nom_package) : R :=
  AdvOf (fxmss_grind_game (2 ^ 64))
    (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_grind) +
  (AdvOf (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64))
    (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_compress) +
   Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 2)
     (R_leaf_roots Q false ∘ G_leaf_roots 14) A).

Lemma leaf_ctx_middle_grindE Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  leaf_ctx_middle Q A = leaf_ctx_middle_grind Q A.
Proof.
rewrite /leaf_ctx_middle /leaf_ctx_middle_grind
  (leaf_ctx_inner_endpoint Q A VA) add0r.
exact: (congr1 (fun x : R => x + _) (leaf_ctx_grinding Q A VA)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reduction packages *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Definition R_prf Q (B : nom_package) : nom_package :=
  B ∘ prf.reduction.R_prf Q true.
Definition R_prf_msg Q (B : nom_package) : nom_package :=
  B ∘ prf.reduction.R_prf_msg Q true.
Definition R_grind Q (B : nom_package) : nom_package :=
  B ∘ R_known_message Q ∘ known_message_coll_filter ∘ leaf.grind.reduction.R_grind.
Definition R_chain_tcr Q (B : nom_package) : nom_package :=
  B ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.chain_tcr.reduction.R_chain_tcr.
Definition R_chain_pre Q (B : nom_package) : nom_package :=
  B ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.chain_pre.reduction.R_chain_pre.
Definition R_compress Q (B : nom_package) : nom_package :=
  B ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.compress.reduction.R_compress.
Definition R_tree Q (B : nom_package) : nom_package :=
  B ∘ tree.reduction.R_tree shrincs_fxmss_sha256 Q.
Definition R_paired Q (B : nom_package) : nom_package :=
  B ∘ paired.reduction.R_paired shrincs_fxmss_sha256 Q.

Lemma shrincs_fxmss_pre_budget_eq : r_chain_pre_budget = (2 ^ 69)%N.
Proof.
change (2 ^ 64 * 2 ^ 5 = 2 ^ (64 + 5))%N.
by rewrite expnD.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Uniform-guess telescope *)

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Local Opaque Adv fxmss_forger shrincs_fxmss_rom_adapter R_known_message
  known_message_coll_filter
  G_prepared_leaf R_leaf_roots G_leaf_roots G_forge_full_signature G_forge_reject
    SMTCR_game
    SMPRE_game SMUD_game
  prf.PRF_game fxmss_grind_game fxmss_tree_game fxmss_tcrx_game
  prf.reduction.R_prf prf.reduction.R_prf_msg leaf.grind.reduction.R_grind
    leaf.compress.reduction.R_compress leaf.chain_tcr.reduction.R_chain_tcr
    leaf.chain_pre.reduction.R_chain_pre
  R_leaf_prepared_ud tree.reduction.R_tree paired.reduction.R_paired r_chain_tcr_budget
    r_chain_pre_budget
    shrincs_fxmss_leaf_capacity.

Definition R_ud Q s (B : nom_package) : nom_package :=
  B ∘ R_leaf_roots Q true ∘ R_leaf_prepared_ud s.

Lemma leaf_context_ud_advantage Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_leaf_roots Q true ∘ G_leaf_roots 0)
    (R_leaf_roots Q true ∘ G_leaf_roots 14) A <=
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (R_ud Q s A).
Proof.
rewrite Adv_reduction /R_ud.
under eq_big_nat do rewrite sep_link_assoc.
exact: (leaf_ud_telescope_valid (A ∘ R_leaf_roots Q true) (valid_adv_link VA)).
Qed.

Definition shrincs_fxmss_leaf_residual Q (A : nom_package) : R :=
  Adv (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
    shrincs_fxmss_sha256) true)
    (R_leaf_roots Q true ∘ G_leaf_roots 0) A +
  (leaf_ctx_middle Q A +
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (R_ud Q s A)).

Lemma shrincs_fxmss_leaf_refinement Q LA c vc :
  let B := (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter)%sep in
  Adv (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
    shrincs_fxmss_sha256) true)
    (G_forge_reject shrincs_fxmss_sha256 Q true) B <= shrincs_fxmss_leaf_residual Q B.
Proof.
cbn zeta.
set B := (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter)%sep.
have VB : ValidPackage (loc B) I_forge A_export B by subst B; exact _.
have hz : Adv (R_leaf_roots Q false ∘ G_leaf_roots 14)
    (G_forge_reject shrincs_fxmss_sha256 Q true) B = 0 by exact:
      leaf_ctx_roots_ideal_endpoint.
rewrite /shrincs_fxmss_leaf_residual.
eapply le_trans; first exact: (Adv_triangle
  (G2 := R_leaf_roots Q true ∘ G_leaf_roots 0)).
apply: lerD; first exact: lexx.
eapply le_trans; first exact: (Adv_triangle
  (G2 := R_leaf_roots Q true ∘ G_leaf_roots 14)).
eapply le_trans.
{ apply: lerD; first exact: lexx.
  exact: (Adv_triangle (G2 := R_leaf_roots Q false ∘ G_leaf_roots 14)). }
have hfinish (a m u v z : R) :
    z = 0 -> a <= u -> m <= v -> a + (m + z) <= v + u.
{ move=> -> ha hm. rewrite addr0 addrC. exact: lerD hm ha. }
apply: hfinish.
- exact: hz.
- exact: leaf_context_ud_advantage Q B VB.
- exact: leaf_ctx_middle_bound Q B VB.
Qed.

(** Close the remaining scalar costs without rewriting inside games. *)
Lemma shrincs_fxmss_leaf_sum_bound (p m r d g u c t e h x z o y : R) :
  o = 0 -> y = g + (c + z) -> z <= t + e ->
  p + (m + (r + (d + h))) + (x + (o + (y + u))) <=
  p + m + d + r + g + u + t + e + c + h + x.
Proof.
move=> -> -> hz.
rewrite add0r.
have he : p + m + d + r + g + u + t + e + c + h + x =
    p + (m + (r + (d + h))) + (x + ((g + (c + (t + e))) + u)).
{ ring. }
rewrite he.
apply: lerD; first exact: lexx.
apply: lerD; first exact: lexx.
apply: lerD; last exact: lexx.
apply: lerD; first exact: lexx.
apply: lerD; first exact: lexx.
exact: hz.
Qed.

Theorem shrincs_fxmss_eucma_bound q_s q_h (LA : Locations)
    (c : raw_code (stateful_rom.sf_Msg fxmss_sf_scheme ×
                   stateful_rom.sf_Sig fxmss_sf_scheme))
    (vc : ValidCode LA (stateful_rom.I_EUCMA_prefix fxmss_sf_scheme) c) :
  let Q := shrincs_fxmss_resources_of q_s q_h in
  let B := (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter)%sep in
  AdvOf (fxmss_eucma_game q_s q_h) (fxmss_forger LA c vc) <=
    AdvOf (prf.PRF_game shrincs_khf_prf
      (shrincs_fxmss_leaf_capacity Q * wots_c_chain_count).+1) (R_prf Q B) +
    AdvOf (prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_sign_budget Q).+1)
      (R_prf_msg Q B) +
    (shrincs_fxmss_leaf_capacity Q)%:R * ((q_h + 1)%:R / ((2 ^ 256)%nat)%:R) +
    (q_h + q_s + 1)%:R / ((2 ^ 128)%nat)%:R +
    AdvOf (fxmss_grind_game (2 ^ 64)) (R_grind Q B) +
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (R_ud Q s B) +
    AdvOf (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget)
      (R_chain_tcr Q B) +
    AdvOf (SMPRE_game shrincs_thf wots_c_hash_class (2 ^ 69))
      (R_chain_pre Q B) +
    AdvOf (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64))
      (R_compress Q B) +
    AdvOf (fxmss_tree_game (shrincs_fxmss_leaf_capacity Q - 1)) (R_tree Q B)
      +
    AdvOf (fxmss_tcrx_game (2 * shrincs_fxmss_leaf_capacity Q - 1)) (R_paired
      Q B).
Proof.
cbn zeta.
eapply le_trans; first exact: shrincs_fxmss_bound_bound.
eapply le_trans.
{ apply: lerD; first exact: lexx.
  apply: lerD; first exact: lexx.
  exact: shrincs_fxmss_leaf_refinement. }
rewrite /shrincs_fxmss_bound_prefix /shrincs_fxmss_leaf_residual.
rewrite /R_prf /R_prf_msg /R_grind
  /R_chain_tcr /R_chain_pre /R_compress
  /R_tree /R_paired.
apply: shrincs_fxmss_leaf_sum_bound.
- exact: leaf_ctx_outer_endpoint.
- exact: leaf_ctx_middle_grindE.
- have hc := prepared_leaf_chain_costs (shrincs_fxmss_resources_of q_s q_h) LA c vc.
  rewrite shrincs_fxmss_pre_budget_eq in hc.
  exact: hc.
Qed.
