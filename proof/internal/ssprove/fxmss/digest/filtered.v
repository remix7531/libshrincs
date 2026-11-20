(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.digest.filtered

    Digest-filtered experiments preassign one digest per scheduled leaf.
      G_forge_digest_filtered keeps all
    forgeries, G_forge_known_anchor keeps claimed anchors present in the honest leaf
      table,
    G_forge_matching_leaf additionally keeps a recovered WOTS+C key equal to that leaf's
      key,
    and G_forge_reject keeps none. All reject a digest in the preassigned table when
    its randomizer is not the one recorded at the forged coordinate/message. A dropped
      G_forge_known_anchor/G_forge_matching_leaf case needs a tree-collision
    extraction proof in a later hop. No collision assumption is made here. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import params games scheme.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Definition keep_anchor : shrincs_fxmss_keep :=
  fun st kt a md sg => isSome (getm kt a).

Definition keep_leaf (P : shrincs_fxmss_params) : shrincs_fxmss_keep :=
  fun st kt a md sg =>
    match getm kt a with
    | None => false
    | Some xs =>
        shrincs_fxmss_leaf_recover P a st.2.1 (uint U8 st.2.2) st.1.1.1 md sg ==
          Some (shrincs_fxmss_leaf_pubkey P a st.2.1 (uint U8 st.2.2) st.1.1.1 xs)
    end.

Definition keep_none : shrincs_fxmss_keep := fun _ _ _ _ _ => false.

Definition G_forge_filtered P Q (keep : shrincs_fxmss_keep) := G_forge P Q true true
  true keep.
Definition G_forge_digest_filtered P Q := G_forge_filtered P Q (fun _ _ _ _ _ => true).
Definition G_forge_known_anchor P Q := G_forge_filtered P Q keep_anchor.
Definition G_forge_matching_leaf P Q := G_forge_filtered P Q (keep_leaf P).
Definition G_forge_reject P Q := G_forge_filtered P Q keep_none.

Lemma keep_leaf_anchor P st kt a md sg :
  keep_leaf P st kt a md sg -> keep_anchor st kt a md sg.
Proof.
rewrite /keep_leaf /keep_anchor.
by case: (getm kt a).
Qed.

Lemma keep_none_eq st kt a md sg : keep_none st kt a md sg = false.
Proof. by []. Qed.
