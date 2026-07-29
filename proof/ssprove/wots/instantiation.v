(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.instantiation

    The headline theorem at the spec's parameters: w = 16 (4-bit
    chains), chain_count = 32, constant_sum = 240, a 16-bit grinding
    counter, 16-byte hash values / seeds and a 32-byte message digest,
    all with uniform samplers — packaged as the parameter record
    [P_shrincs : wc_params].  Demonstrates that the side conditions
    of [shrincs_wots_secure] are dischargeable at the shrincs-bip numbers —
    [grind_range P_shrincs] holds by construction (a 16-byte digest IS
    32 base-16 digits) — so the abstract bound is non-vacuous.

    The hash functions stay ABSTRACT over the concrete types here;
    axioms.v instantiates them with the spec's real
    truncated-SHA-256 construction (via Model.shrincs), yielding the
    unconditional [shrincs_wots_secure_sha256]. *)

From Sec.lib Require Import prelude games.thf games.smtcr games.smpre games.smud
  games.stcrp games.prf sig.scheme sig.kots.
From Sec.lib Require Import chain.core.
From Sec Require Import addressing.
From Sec.wots Require Import scheme games
  hop.grind hop.compress hop.chain_tcr hop.chain_pre hop.ud hop.prf.
Require Import Sec.wots.theorem.
From mathcomp Require Import reals.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section BIPInstantiation.

(* ------------------------------------------------------------------ *)
(** ** Concrete types and parameters (big-nat discipline: bounds stay
       the TERMS [2 ^ k], never computed) *)

(** 16-byte strings (n = 16): hash values, PKseed, SKseed; the
    32-byte message digest fed to grinding (the H_msg_sf output). *)
Definition PP_shrincs : choice_type := 'fin (2 ^ 128).
Definition N_shrincs  : choice_type := 'fin (2 ^ 128).
Definition K_shrincs  : choice_type := 'fin (2 ^ 128).
Definition M_shrincs  : choice_type := 'fin (2 ^ 256).

(** The spec's WOTS+C parameters. *)
Definition w_shrincs            : nat := 16.      (* 2 ^ SHRINCS_WOTS_CHAIN_BITS *)
Definition chain_count_shrincs  : nat := 32.      (* SHRINCS_WOTS_CHAIN_COUNT    *)
Definition constant_sum_shrincs : nat := 240.     (* SHRINCS_WOTS_CONSTANT_SUM   *)
Definition c_max_shrincs        : nat := 2 ^ 16.  (* 16-bit counter        *)

(** Sanity: pinned to the spec's derived forms. *)
Lemma w_shrincsE : w_shrincs = (2 ^ 4)%N.
Proof. by []. Qed.

Lemma constant_sum_shrincsE :
  constant_sum_shrincs = ((chain_count_shrincs * (w_shrincs - 1)) %/ 2)%N.
Proof. by []. Qed.

(** Uniform samplers over the concrete types. *)
Definition dPP_shrincs : dist PP_shrincs :=
  {code x ← sample uniform (2 ^ 128) ;; ret x}.
Definition dN_shrincs : dist N_shrincs :=
  {code x ← sample uniform (2 ^ 128) ;; ret x}.
Definition dK_shrincs : dist K_shrincs :=
  {code x ← sample uniform (2 ^ 128) ;; ret x}.
Definition dM_shrincs : dist M_shrincs :=
  {code x ← sample uniform (2 ^ 256) ;; ret x}.

Lemma two_pow_pos (k : nat) : (0 < 2 ^ k)%N.
Proof. by rewrite expn_gt0. Qed.

(** Hash-domain inhabitant used as a default value in sequence lemmas. *)
Definition n0_shrincs : N_shrincs := Ordinal (two_pow_pos 128).

(* ------------------------------------------------------------------ *)
(** ** The abstract hashes over the concrete types *)

Context (F_shrincs : PP_shrincs -> address.adrs chain_count_shrincs w_shrincs.-1 -> N_shrincs -> N_shrincs).
Context (T_sf_shrincs : PP_shrincs -> address.adrs chain_count_shrincs w_shrincs.-1 -> seq N_shrincs -> N_shrincs).
Context (PRF_shrincs : PP_shrincs -> address.adrs chain_count_shrincs w_shrincs.-1 -> K_shrincs -> N_shrincs).

(** H_grind outputs ARE 16-byte strings, read as a nat digest. *)
Context (H_grind0 : PP_shrincs -> address.adrs chain_count_shrincs w_shrincs.-1 -> M_shrincs * nat -> N_shrincs).

Definition H_grind_shrincs (pp : PP_shrincs) (a : address.adrs chain_count_shrincs w_shrincs.-1)
    (x : M_shrincs * nat) : nat :=
  nat_of_ord (H_grind0 pp a x).

(** The instance anchor stays arbitrary (any leaf position), and
    carries NO range hypothesis: [Sec.addressing] places both anchor
    components exact-or-zero, so the headline theorem below holds at
    every [(zstar, istar)]. *)
Context (zstar istar : nat).

(* ------------------------------------------------------------------ *)
(** ** The side conditions hold by construction *)

Lemma shrincs_Hcc : (0 < chain_count_shrincs)%N.
Proof. by []. Qed.

Lemma shrincs_Hw : (1 < w_shrincs)%N.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** The parameter record at the spec's numbers *)

Definition P_shrincs : wc_params := {|
  wcp_PP := PP_shrincs ;
  wcp_N  := N_shrincs ;
  wcp_M  := M_shrincs ;
  wcp_w := w_shrincs ;
  wcp_chain_count := chain_count_shrincs ;
  wcp_Hcc := shrincs_Hcc ;
  wcp_Hw  := shrincs_Hw ;
  wcp_zstar := zstar ;
  wcp_istar := istar ;
  wcp_F       := F_shrincs ;
  wcp_T_sf    := T_sf_shrincs ;
  wcp_H_grind := H_grind_shrincs ;
  wcp_dPP := dPP_shrincs ;
  wcp_dN  := dN_shrincs ;
  wcp_dM  := dM_shrincs ;
  wcp_constant_sum := constant_sum_shrincs ;
  wcp_c_max        := c_max_shrincs ;
|}.

Lemma pow16_32 : (16 ^ 32)%N = (2 ^ 128)%N.
Proof. by rewrite -[16%N]/(2 ^ 4)%N -expnM. Qed.

(** A 16-byte digest is exactly [chain_count = 32] base-16 digits. *)
Lemma shrincs_Hrange : grind_range P_shrincs.
Proof.
move=> pp' a x.
by rewrite [(wcp_w P_shrincs ^ wcp_chain_count P_shrincs)%N]pow16_32 /= /H_grind_shrincs ltn_ord.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The headline bound at the spec's numbers *)

(** [shrincs_wots_secure] at the spec's numbers; the side conditions
    are discharged by construction, and the SM-UD sums have
    [w - 2 = 14] summands each. *)
Theorem shrincs_wots_secure_shrincs
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P_shrincs)) A_export A) :
  Adv (G_forge_keyed P_shrincs K_shrincs PRF_shrincs dK_shrincs true)
      (G_forge_keyed P_shrincs K_shrincs PRF_shrincs dK_shrincs false) A
    <= AdvOf (PRF_game (khf_prf P_shrincs K_shrincs PRF_shrincs dK_shrincs) chain_count_shrincs)
             (A ∘ R_prf P_shrincs K_shrincs PRF_shrincs dK_shrincs true)
     + \sum_(0 <= s < w_shrincs.-2)
          AdvOf (SMUD_game (thf_chain P_shrincs) (coll_chain P_shrincs) chain_count_shrincs)
                (A ∘ R_ud P_shrincs true s)
     + AdvOf (STCRP_game (thf_grind P_shrincs) (coll_grind P_shrincs) M_shrincs
                (grind_enc P_shrincs) (grind_prp P_shrincs) c_max_shrincs 1)
             (A ∘ R_grind P_shrincs)
     + AdvOf (SMTCR_game (thf_pkcompress P_shrincs) (coll_pkcompress P_shrincs) 1)
             (A ∘ R_compress P_shrincs)
     + AdvOf (SMTCR_game (thf_chain P_shrincs) (coll_chain P_shrincs)
                (tcr_budget chain_count_shrincs w_shrincs))
             (A ∘ R_chain_tcr P_shrincs)
     + AdvOf (SMPRE_game (thf_chain P_shrincs) (coll_chain P_shrincs) chain_count_shrincs)
             (A ∘ R_chain_pre P_shrincs)
     + \sum_(0 <= s < w_shrincs.-2)
          AdvOf (SMUD_game (thf_chain P_shrincs) (coll_chain P_shrincs) chain_count_shrincs)
                (A ∘ R_ud P_shrincs false s)
     + AdvOf (PRF_game (khf_prf P_shrincs K_shrincs PRF_shrincs dK_shrincs) chain_count_shrincs)
             (A ∘ R_prf P_shrincs K_shrincs PRF_shrincs dK_shrincs false).
Proof.
exact: (shrincs_wots_secure P_shrincs K_shrincs PRF_shrincs dK_shrincs
          shrincs_Hrange A VA).
Qed.

End BIPInstantiation.
