(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.digest.games

    The digest intermediate keeps preassignment and the sequential signer
    separate from the digest-collision filter in FORGE. G_digest_preassigned omits that
    filter; G_digest_filtered applies it. Both use the refusal-preserving signer of
      G_forge_digest_filtered:
    a failed grind returns None after the message and leaf were consumed. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import params games digest.filtered.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section DigestGames.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Definition digest_gen_body (setup : shrincs_fxmss_setup) : raw_code (bytes 48) :=
  resolve (G_forge_digest_filtered P Q true) (shrincs_fxmss_op_gen,
    (shrincs_fxmss_setup, bytes 48)) setup.

Definition digest_sign_body (cm : shrincs_fxmss_message) : raw_code ('option
  shrincs_fxmss_bytes) :=
  resolve (G_forge_digest_filtered P Q true) (shrincs_fxmss_op_sign,
    (shrincs_fxmss_message, 'option
    shrincs_fxmss_bytes)) cm.

Definition digest_hash_body (x : shrincs_fxmss_hmsg_input) :
    raw_code ('option (bytes 32)) :=
  resolve (G_forge_digest_filtered P Q true)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x.

#[export] Instance digest_gen_valid setup :
  ValidCode shrincs_fxmss_locs [interface] (digest_gen_body setup).
Proof.
rewrite /digest_gen_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve
  /= coerce_kleisliE.
ssprove_valid.
- exact: shrincs_fxmss_sample_keys_valid.
- exact: shrincs_fxmss_sample_digests_valid.
Qed.

#[export] Instance digest_sign_valid cm :
  ValidCode shrincs_fxmss_locs [interface] (digest_sign_body cm).
Proof.
rewrite /digest_sign_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve
  /= coerce_kleisliE.
ssprove_valid.
Qed.

#[export] Instance digest_hash_valid x :
  ValidCode shrincs_fxmss_locs [interface] (digest_hash_body x).
Proof.
rewrite /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge /resolve
  /= coerce_kleisliE.
ssprove_valid.
Qed.

Definition G_digest (filter bit : bool) : game I_forge :=
  [package shrincs_fxmss_locs;
    [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
      digest_gen_body setup
    };
    [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
      (cm) {
      digest_sign_body cm
    };
    [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
      digest_hash_body x
    };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      } '(cm, sg) {
      verdict ← shrincs_fxmss_forge_body P filter (fun _ _ _ _ _ => true) cm sg ;;
      ret (bit && verdict)
    }
  ].

Definition G_digest_preassigned := G_digest false.
Definition G_digest_filtered := G_digest true.

Lemma grind_hop_eq (bit : bool) :
  perfect I_forge (G_digest_filtered bit) (G_forge_digest_filtered P Q bit).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (fun '(h0, h1) => h0 = h1)).
{ ssprove_invariant. }
simplify_eq_rel arg.
- rewrite /digest_gen_body /G_forge_digest_filtered /G_forge_filtered /G_forge
  /resolve /= coerce_kleisliE.
  eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
- rewrite /digest_sign_body /G_forge_digest_filtered /G_forge_filtered /G_forge
  /resolve /= coerce_kleisliE.
  eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
- rewrite /digest_hash_body /G_forge_digest_filtered /G_forge_filtered /G_forge
  /resolve /= coerce_kleisliE.
  eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
- case: arg => cm sg.
  eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
Qed.

End DigestGames.
