(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.preservation

    SIGN and HASH preserve the committed tree state: they read the key and tree
    but write only counters, logs and random-oracle tables. Per-oracle simulations
    for the tree reduction and the full-signature preassigned experiment. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape scheme games tree.forgery tree.reduction.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** Tree preservation *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_tree_inv shrincs_fxmss_tree_rel.

Lemma shrincs_fxmss_tree_lookup_stable P x :
  code_stable (shrincs_fxmss_tree_inv P) (shrincs_fxmss_lookup P x).
Proof.
rewrite /shrincs_fxmss_lookup.
split.
- apply: shrincs_fxmss_tree_inv_get.
  by rewrite /shrincs_fxmss_tree_service_locs; fmap_solve.
- move=> mp.
  case: (getm mp x) => [md|]; first by [].
  apply: code_stable_bind.
  + apply: (code_stable_valid emptym).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + move=> md.
    split; last by [].
    apply: shrincs_fxmss_tree_inv_put.
    by [].
Qed.

Lemma shrincs_fxmss_tree_hash_stable P Q keep bit x :
  code_stable (shrincs_fxmss_tree_inv P) (resolve (G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x).
Proof.
rewrite /G_forge_full_signature /resolve /= coerce_kleisliE.
cbn [code_stable].
split.
- apply: shrincs_fxmss_tree_inv_get.
  by rewrite /shrincs_fxmss_tree_service_locs; fmap_solve.
- move=> done.
  case: done.
  + by [].
  + cbn [negb assert code_stable].
    split.
    * apply: shrincs_fxmss_tree_inv_get.
      by rewrite /shrincs_fxmss_tree_service_locs; fmap_solve.
    * move=> hc.
      case: (hc < shrincs_fxmss_hash_budget Q).
      -- cbn [assert code_stable].
         split.
         ++ apply: shrincs_fxmss_tree_inv_put.
            by [].
         ++ (* A valid hash input preserves the committed tree state. *)
            case: (Z.leb _ _) => //.
            change (code_stable (shrincs_fxmss_tree_inv P)
              (bind (shrincs_fxmss_lookup P x) (fun md => ret (Some md)))).
            apply: code_stable_bind; first exact: shrincs_fxmss_tree_lookup_stable.
            by move=> md.
      -- by [].
Qed.

Local Opaque shrincs_fxmss_sign shrincs_fxmss_select_leaf shrincs_fxmss_lookup_keys.

Local Ltac tree_access := first
  [ apply: shrincs_fxmss_tree_inv_get; rewrite /shrincs_fxmss_tree_service_locs;
    fmap_solve
  | apply: shrincs_fxmss_tree_inv_put; done ].

Lemma shrincs_fxmss_tree_sign_stable P Q keep bit cm :
  code_stable (shrincs_fxmss_tree_inv P) (resolve (G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm).
Proof.
rewrite /G_forge_full_signature /resolve /= coerce_kleisliE.
cbn [code_stable].
split; first tree_access.
move=> sto.
case: sto => [st|]; last by [].
simpl.
split; first tree_access.
move=> done.
case: done; first by [].
simpl.
split; first tree_access.
move=> sc.
case: (sc < shrincs_fxmss_sign_budget Q); last by [].
simpl.
split; first tree_access.
move=> lg.
split; first tree_access.
split; first tree_access.
case: (shrincs_fxmss_message_valid cm); last by [].
simpl.
split; first tree_access.
move=> q.
case: (shrincs_fxmss_select_leaf _ _ _) => [a|]; last by [].
simpl.
split; first tree_access.
split; first tree_access.
move=> kso.
case: kso => [ks|]; last by [].
simpl.
split; first tree_access.
move=> kpo.
case: kpo => [kp|]; last by [].
simpl.
split; first tree_access.
move=> kt.
split; first tree_access.
move=> rt.
apply: code_stable_bind.
- case: (rt _) => [r|]; first by [].
  apply: code_stable_bind.
  + apply: (code_stable_valid emptym).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + by move=> r.
- move=> ro.
  case: ro => [r|]; last by [].
  simpl.
  split; first tree_access.
  split; first tree_access.
  move=> sd.
  apply: code_stable_bind.
  + apply: code_stable_bind.
    * case: (sd a) => [md|]; first by [].
      apply: code_stable_bind.
      -- apply: (code_stable_valid emptym).
         ++ by move=> l /fhas_empty.
         ++ by move=> l v /fhas_empty.
      -- by move=> md.
    * (* The sampled digest is recorded outside the service locations. *)
      move=> md.
      simpl.
      split; first tree_access.
      move=> mp.
      split; first tree_access.
      by [].
  + move=> md.
    case: (shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|]; by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree simulation *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_tree_inv shrincs_fxmss_tree_rel smtcr.SMTCR_game.

Lemma shrincs_fxmss_tree_sign_resolve P Q keep bit cm :
  resolve (R_tree P Q) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
    shrincs_fxmss_bytes)) cm =
  resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
    (shrincs_fxmss_message, 'option
    shrincs_fxmss_bytes)) cm.
Proof. reflexivity. Qed.

Lemma shrincs_fxmss_tree_hash_resolve P Q keep bit x :
  resolve (R_tree P Q) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes
    32))) x =
  resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_hash,
    (shrincs_fxmss_hmsg_input,
    'option (bytes 32))) x.
Proof. reflexivity. Qed.

Lemma shrincs_fxmss_tree_sign_sim P Q keep bit (G : raw_package) cm :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_tree_inv P (s0,s1) ⦄
    resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm
    ≈ code_link (resolve (R_tree P Q)
        (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes))
          cm) G
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_tree_inv P (s0,s1) ⦄.
Proof.
rewrite (shrincs_fxmss_tree_sign_resolve P Q keep bit).
have hv : ValidCode shrincs_fxmss_locs [interface]
    (resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message,
      'option shrincs_fxmss_bytes)) cm).
  eapply valid_resolve.
  exact (pack_valid (G_forge_full_signature P Q keep bit)).
  by rewrite /I_forge; fmap_solve.
rewrite (code_link_scheme _ _ _ _ hv).
apply: r_code_stable.
exact: shrincs_fxmss_tree_sign_stable.
Qed.

Lemma shrincs_fxmss_tree_hash_sim P Q keep bit (G : raw_package) x :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_tree_inv P (s0,s1) ⦄
    resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_hash,
      (shrincs_fxmss_hmsg_input,
      'option (bytes 32))) x
    ≈ code_link (resolve (R_tree P Q)
        (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) G
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_tree_inv P (s0,s1) ⦄.
Proof.
rewrite (shrincs_fxmss_tree_hash_resolve P Q keep bit).
have hv : ValidCode shrincs_fxmss_locs [interface]
    (resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_hash,
      (shrincs_fxmss_hmsg_input,
      'option (bytes 32))) x).
  eapply valid_resolve.
  exact (pack_valid (G_forge_full_signature P Q keep bit)).
  by rewrite /I_forge; fmap_solve.
rewrite (code_link_scheme _ _ _ _ hv).
apply: r_code_stable.
exact: shrincs_fxmss_tree_hash_stable.
Qed.
