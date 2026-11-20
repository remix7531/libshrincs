(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.endpoints

    The canonical-forger zero-success endpoint and exact grinding hop lift through
    the prepared-leaf contexts. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.stateful_rom.
From mathcomp Require Import reals distr realsum.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance leaf.opening leaf.known_message_game leaf.known_message
    leaf.context
  bridge.adapter bound.canonical leaf.uniform digest.filtered leaf.prepared
  leaf.grind.reduction leaf.grind.hop.

(* ------------------------------------------------------------------ *)
(** ** Leaf context zero *)

Import PackageNotation GRing.Theory Num.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Lemma leaf_ctx_check_false q h :
  dfst (Pr_code (resolve (G_known_message shrincs_fxmss_sha256 false)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h) true = 0.
Proof.
rewrite resolve_known_message_check.
apply: sf_bind_zero => v h'.
by rewrite Pr_code_ret (dmargin_dunit (false, _) fst) dunit1E.
Qed.

Lemma leaf_ctx_filter_check (G : raw_package) q :
  resolve (known_message_coll_filter ∘ G)%pack (known_message_check,
    (leaf_opening_opening, 'bool)) q =
  resolve G (known_message_check, (leaf_opening_opening, 'bool)) q.
Proof.
rewrite resolve_link /known_message_coll_filter /resolve /= coerce_kleisliE.
cbn [code_link].
exact: bind_ret.
Qed.

Lemma leaf_ctx_forge_zero (G : raw_package) cm sg h :
  (forall q h', dfst (Pr_code
    (resolve G (known_message_check, (leaf_opening_opening, 'bool)) q) h') true = 0) ->
  dfst (Pr_code (code_link (leaf_ctx_forge cm sg) G) h) true = 0.
Proof.
move=> hz.
rewrite /leaf_ctx_forge code_link_bind.
apply: sf_bind_zero => -[q|] h'.
- cbn [code_link]. rewrite bind_ret. exact: hz.
- by rewrite Pr_code_ret (dmargin_dunit (false, _) fst) dunit1E.
Qed.

(* Keep oracle bodies folded while resolving the reduction package. *)
Local Opaque leaf_ctx_forge leaf_ctx_gen leaf_ctx_sign leaf_ctx_hash.

Lemma leaf_ctx_resolve_forge Q cm sg :
  resolve (R_known_message Q) shrincs_fxmss_forge_op (cm, sg) = leaf_ctx_forge cm sg.
Proof.
by rewrite /R_known_message /resolve /= coerce_kleisliE.
Qed.

(* Keep linked games folded while reducing the canonical forger. *)
Local Opaque R_known_message G_known_message known_message_coll_filter.

Lemma leaf_ctx_canonical_ideal_zero Q LA c vc :
  Pr' ((fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) ∘
    (R_known_message Q ∘ known_message_coll_filter ∘ G_known_message
      shrincs_fxmss_sha256 false))%sep true =
      0.
Proof.
rewrite -!sep_link_assoc.
have hf : disj (known_message_coll_filter : nom_package)
    (G_known_message shrincs_fxmss_sha256 false : nom_package) by
      ssprove_separate_solve.
rewrite -(share_link_sep_link hf).
have hr : disj (R_known_message Q : nom_package)
    (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 false)%share
  by ssprove_separate_solve.
rewrite -(share_link_sep_link hr).
have ha : disj (shrincs_fxmss_rom_adapter : nom_package)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_known_message
      shrincs_fxmss_sha256 false)%share by
      ssprove_separate_solve.
rewrite -(share_link_sep_link ha).
apply: shrincs_fxmss_canonical_zero.
move=> [cm sg] h.
rewrite resolve_link.
rewrite /shrincs_fxmss_rom_adapter /resolve /= coerce_kleisliE.
cbn [code_link].
rewrite Pr_code_get.
rewrite bind_ret resolve_link leaf_ctx_resolve_forge.
apply: leaf_ctx_forge_zero => q h'.
rewrite leaf_ctx_filter_check.
exact: leaf_ctx_check_false.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf context uniform guesses zero *)

Import PackageNotation GRing.Theory Num.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.
Local Opaque leaf_ctx_ud_gen leaf_ctx_ud_sign leaf_ctx_ud_check.
Lemma leaf_ctx_ud_false (G : raw_package) q h :
  dfst (Pr_code (resolve (C_leaf_roots false ∘ G)%pack
    (known_message_check, (leaf_opening_opening, 'bool)) q) h) true = 0.
Proof.
rewrite resolve_link /C_leaf_roots /resolve /= coerce_kleisliE.
rewrite code_link_bind.
apply: sf_bind_zero => v h'.
by rewrite Pr_code_ret (dmargin_dunit (false, _) fst) dunit1E.
Qed.
(* Keep the root games folded while reducing the canonical forger. *)
Local Opaque R_known_message C_leaf_roots G_leaf_roots known_message_coll_filter.

Lemma leaf_ctx_roots_canonical_ideal_zero Q r LA c vc :
  Pr' ((fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) ∘
    (R_leaf_roots Q false ∘ G_leaf_roots r))%sep true = 0.
Proof.
rewrite R_leaf_roots_nom -!sep_link_assoc.
have hc : disj (C_leaf_roots false : nom_package)
    (G_leaf_roots r : nom_package) by ssprove_separate_solve.
rewrite -(share_link_sep_link hc).
have hf : disj (known_message_coll_filter : nom_package)
    (C_leaf_roots false ∘ G_leaf_roots r)%share by ssprove_separate_solve.
rewrite -(share_link_sep_link hf).
have hr : disj (R_known_message Q : nom_package)
    (known_message_coll_filter ∘ C_leaf_roots false ∘ G_leaf_roots r)%share
  by ssprove_separate_solve.
rewrite -(share_link_sep_link hr).
have ha : disj (shrincs_fxmss_rom_adapter : nom_package)
    (R_known_message Q ∘ known_message_coll_filter ∘ C_leaf_roots false ∘ G_leaf_roots
      r)%share by ssprove_separate_solve.
rewrite -(share_link_sep_link ha).
apply: shrincs_fxmss_canonical_zero.
move=> [cm sg] h.
rewrite resolve_link.
rewrite /shrincs_fxmss_rom_adapter /resolve /= coerce_kleisliE.
cbn [code_link].
rewrite Pr_code_get.
rewrite bind_ret resolve_link leaf_ctx_resolve_forge.
apply: leaf_ctx_forge_zero => q h'.
rewrite leaf_ctx_filter_check.
exact: leaf_ctx_ud_false.
Qed.
Lemma leaf_ctx_roots_ideal_endpoint Q r LA c vc :
  Adv (R_leaf_roots Q false ∘ G_leaf_roots r)
    (G_forge_reject shrincs_fxmss_sha256 Q true)
    (fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) = 0.
Proof.
have hzrule (G H A : nom_package) :
    distr.mu (Pr' (A ∘ G)%sep) true = 0 ->
    distr.mu (Pr' (A ∘ H)%sep) true = 0 -> Adv G H A = 0.
{ move=> hg hh. by rewrite AdvE hg hh subr0 normr0. }
apply: hzrule.
- exact: leaf_ctx_roots_canonical_ideal_zero.
- exact: shrincs_fxmss_canonical_reject_zero.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf context grind *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque R_known_message known_message_coll_filter G_prepared_leaf R_grind
  fxmss_grind_game Adv.

Lemma leaf_ctx_grinding Q (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  Adv (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 0)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 1) A =
  AdvOf (fxmss_grind_game (2 ^ 64))
    (A ∘ R_known_message Q ∘ known_message_coll_filter ∘ R_grind).
Proof.
pose C := (A ∘ R_known_message Q)%sep.
have VC : ValidPackage (loc C) I_known_message A_export C by subst C; exact _.
pose D := mkpackage (loc C) C VC.
have eD : as_nom D = C by apply: eq_nom_package; reflexivity.
have hg := prepared_leaf_grind_adv D.
rewrite eD /C -!sep_link_assoc in hg.
rewrite !Adv_reduction -sep_link_assoc.
exact hg.
Qed.
