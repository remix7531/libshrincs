(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.analysis

    The PURE forgery-analysis facts the WOTS+C hops share.

    The argument: an adversary who observes a valid pair (mes, sigma)
    and attempts to forge must, if every a_i' is at least a_i (so
    equality of sums forces a_i' = a_i for all i), find a target
    collision for H_grind; otherwise some a_i' < a_i and the forger
    must invert F at some position.  The hops refine this into four
    cases, one reduction each: GRIND (Shrincs.internal.ssprove.wots.hop.grind),
    COMPRESS (hop.compress), CHAIN COLLISION (hop.chain_tcr) and CHAIN
    MEET (hop.chain_pre).  The per-chain case split itself is the chain
    library's [tcr_decision] / [pre_decision]
    (Shrincs.internal.ssprove.lib.chain.core) at the address-wrapped
    chain hash [Fw].

    This file holds what those hops need beyond the chain library:

    - [wcendsE], [vdigest_valid_msg]: the scheme's completed ends and
      grinded digests in the chain library's vocabulary.
    - [wdigest_inj]: GRIND's pure step.  Equal digit VECTORS give equal
      H_grind OUTPUTS, because the instance's digit reading is
      injective ([wcp_digits_inj]).
    - [shrincs_wots_tweak] and its injectivity: the SM-TCR(F) and
      SM-PRE(F) games take encoded addresses as tweaks, so a committed
      (chain, position) pair is re-tagged by
      [shrincs_wots_tweak (i, k) := chain_tweak P i k]. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.sample_seq.
From Shrincs.internal.ssprove.lib Require Import chain.core.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.wots Require Import scheme games.


Import PackageNotation.
#[local] Open Scope package_scope.

Section WOTSCAnalysis.

(** The WOTS+C parameter record (see Shrincs.internal.ssprove.wots.params); the same context
    as Shrincs.internal.ssprove.wots.scheme.  This layer is pure. *)
Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** *** Bridges into the chain-library analysis

    All by conversion ([Fw] beta-reduces to [F] at [chain_adrs], and
    shrincs_wots_scheme's verifier-side [complete_ends] is the chain library's
    [ends_from_sig] at [FW]); stated once so the proofs below can
    rewrite instead of relying on implicit conversion. *)

Lemma wcendsE pp (ds : seq nat) (ys : seq (wcp_N P)) :
  complete_ends P pp ds ys = ends_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp ds ys.
Proof. by []. Qed.

(** A grinded digest is a valid chain-library message (digit vector
    of size chain_count, digits < w, digit sum constant_sum) — the digit-selector
    lemmas [forged_digit_lt] / [valid_msg_digit] apply to digests. *)
Lemma vdigest_valid_msg pp (m : wcp_M P) c :
  valid_digest P (digest_of P pp m c) ->
  valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c).
Proof.
case/andP=> h1 h2.
by rewrite /valid_msg (size_digest_of P) eqxx h1 h2.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Case 1 (GRIND): digit-vector equality lifts to H_grind-output
    equality *)

Lemma wdigest_inj pp (m1 : wcp_M P) (c1 : nat) (m2 : wcp_M P) (c2 : nat) :
  digest_of P pp m1 c1 = digest_of P pp m2 c2 ->
  wcp_H_grind P pp (grind_adrs P) (m1, c1) = wcp_H_grind P pp (grind_adrs P) (m2, c2).
Proof. exact: wcp_digits_inj. Qed.

(** KFORGE's log freshness in the form the GRIND hop consumes (the
    log of G_forge_sampledkey/G_forge_uniformchains is the single signed message). *)
Lemma notin_log_neq (m mstar : wcp_M P) : mstar \notin [:: m] -> mstar != m.
Proof. by rewrite inE. Qed.

(* ------------------------------------------------------------------ *)
(** *** Committed (chain, position) pairs as encoded chain addresses *)

Definition shrincs_wots_tweak (ik : nat * nat) : wc_adrs_ch P :=
  chain_tweak P ik.1 ik.2.

(** Distinct in-range (chain, position) pairs are distinct tweaks — the
    TQUERY freshness asserts and the CHECK index mapping rest on this.
    The record only promises distinct tweaks for indices the scheme
    reaches ([wcp_tw_chain_inj]), so injectivity is CONDITIONAL on the
    indices being in range; the consumers discharge those ranges at
    each use (every committed target is in range). *)
Lemma shrincs_wots_tweak_inj (ik ik' : nat * nat) :
  (ik.1 < wcp_chain_count P)%nat -> (ik'.1 < wcp_chain_count P)%nat ->
  (ik.2 < (wcp_w P).-1)%nat -> (ik'.2 < (wcp_w P).-1)%nat ->
  shrincs_wots_tweak ik = shrincs_wots_tweak ik' -> ik = ik'.
Proof.
move: ik ik' => [i k] [i' k'] /= hi hi' hk hk'.
rewrite /shrincs_wots_tweak /= => Heq.
by have [-> ->] := chain_tweak_inj P i k i' k' hi hi' hk hk' Heq.
Qed.

End WOTSCAnalysis.
