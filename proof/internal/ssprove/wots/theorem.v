(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.theorem

    The end-to-end one-time security bound for WOTS+C — the
    chain/grinding/compression layer.

    THE HEADLINE [shrincs_wots_secure]: for the KEYED valid-commit
    known-message experiment G_forge_keyed (chain starts PRF-derived from a
    hidden SKseed, grinding success asserted at COMMIT):

      Adv (G_forge_keyed true) (G_forge_keyed false) A
        <=   AdvOf PRF(SKseed)             (A ∘ R_prf true)    (PrfHop)
           + \sum_(s < w-2) AdvOf SMUD(F)  (A ∘ R_ud true s)    (UDHop)
           + AdvOf STCRP(H_grind)          (A ∘ R_grind)          (GrindHop)
           + AdvOf SMTCR(T_sf)             (A ∘ R_compress)          (CompressHop)
           + AdvOf SMTCR(F)                (A ∘ R_chain_tcr)        (ChainHop)
           + AdvOf SMPRE(F)                (A ∘ R_chain_pre)        (ChainHop)
           + \sum_(s < w-2) AdvOf SMUD(F)  (A ∘ R_ud false s)   (UDHop)
           + AdvOf PRF(SKseed)             (A ∘ R_prf false).  (PrfHop)

    Game chain: G_forge_keyed true -PRF-> G_forge_sampledkey true -UD->
    G_forge_uniformchains true -GRIND-> G_post_grind -COMPRESS->
    G_post_compress -CHAINTCR-> G_post_chain -CHAINPRE->
    G_forge_uniformchains false -UD(sym)-> G_forge_sampledkey false
    -PRF(sym)-> G_forge_keyed false.

    The ideal-key theorem [shrincs_wots_secure_ideal_sk] (chain starts
    sampled, the middle six terms) is the stepping stone: the PRF hop
    composes with it by the advantage triangle, so the ideal-key
    proof stack is never reopened.

    Side conditions: [grind_range P] (H_grind outputs below
    w^chain_count — discharged at instantiation when H_grind is an
    (chain_count*log2 w)-bit hash), [wcp_Hcc] (at least one chain; see
    Sec.wots.hop.prf) and the data sampler [wcp_dM]. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.thf games.smtcr games.smpre games.smud
  games.stcrp games.prf sig.scheme sig.kots.
From Shrincs.internal.ssprove.lib Require Import chain.core.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import scheme games analysis
  hop.grind hop.compress hop.chain_tcr hop.chain_pre hop.ud hop.prf
  bound.grind bound.compress bound.chain_tcr bound.chain_pre bound.prf kots_link.
From mathcomp Require Import reals.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section WOTSCTheorem.

(** The WOTS+C parameter record (see Sec.wots.params) and the keyed
    derivation data (Sec.wots.hop.prf):
    SKseed space, derivation function and SKseed sampler. *)
Context (P : wc_params).
Context (K : choice_type).
Context (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P).
Context (dK : dist K).

(** The IDEAL-KEY stepping theorem (chain starts sampled rather than
    PRF-derived); the headline [shrincs_wots_secure] composes the PRF hop
    with this by the advantage triangle.  Reading the statement:

    - LHS [Adv (G_forge_sampledkey P true) (G_forge_sampledkey P false) A]
      IS A's WOTS+C forgery probability against the ideal-key game:
      the [true] game is the known-message forgery game whose KFORGE
      returns [verify && (mst ∉ log)], the [false] game returns
      [false] from KFORGE; by the THF real/ideal convention their
      advantage equals A's success probability.
    - Each RHS summand is one assumption's advantage [AdvOf _ (A ∘ R_)]
      at an EXPLICIT, constructed reduction — no advantage or
      reduction-existence is assumed (assumptions/check.sh enforces this).
    - [grind_range P] is the SOLE data side condition: H_grind's output
      fits in [chain_count] base-w digits.  Satisfiable when H_grind is
      an n-bit hash read as [chain_count] base-w digits; note it needs
      [w >= 2] so that [w^chain_count > 0] — otherwise the bound is
      [False] and the theorem is vacuous. *)
Theorem shrincs_wots_secure_ideal_sk
    (Hrange : grind_range P)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A) :
  Adv (G_forge_sampledkey P true) (G_forge_sampledkey P false) A
    (* [w.-2] = number of internal chain positions hybridised by SM-UD;
       a truncated subtraction, so this sum is empty when [w < 2]. *)
    <= \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P true s)
     + AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P)
     + AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
     + AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
     + AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
     + \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s).
Proof.
(* The four hop-equalities are proved in dedicated files
   (Sec.wots.Bound.{Grind,Compress,ChainTCR,ChainPRE}) so their heavy
   Adv_perfect_l/r rewrites type-check in parallel; here we only
   instantiate the resulting opaque lemmas.

   Performance note: the UD sums are kept inline (NOT named with
   [set]/[pose]) and the final reassociation is discharged by the
   pure-arithmetic lemma [le6] applied with [exact:]. [set] and a
   goal-wide [rewrite]/[lexx] each force a convertibility pass over
   the whole package-laden inequality (its Adv terms carry huge
   ValidPackage proof terms) and cost minutes; [exact: le6] binds the
   six Adv summands to abstract reals by structural unification and
   is instantaneous. *)
have le6 : forall a b c d e f : R,
    a + (b + (c + (d + (e + f)))) <= a + b + c + d + e + f.
  by move=> a b c d e f; rewrite !GRing.addrA; exact: lexx.
have hGR : Adv (G_forge_uniformchains P true) (intermediates.G_post_grind P) A
           = AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                      (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P).
  by apply: grind_hop_eq; assumption.
have hCP : Adv (intermediates.G_post_grind P) (intermediates.G_post_compress P) A
           = AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P).
  by apply: compress_hop_eq; assumption.
have hCT : Adv (intermediates.G_post_compress P) (intermediates.G_post_chain P) A
           = AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                      (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P).
  by apply: ctcr_hop_eq; assumption.
have hPR : Adv (intermediates.G_post_chain P) (G_forge_uniformchains P false) A
           = AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P).
  by apply: cpre_hop_eq; assumption.
have hUD1 : Adv (G_forge_sampledkey P true) (G_forge_uniformchains P true) A
            <= \sum_(0 <= s < (wcp_w P).-2)
                  AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P true s).
  exact: (UDw_telescope P true A VA).
have hUD0 : Adv (G_forge_uniformchains P false) (G_forge_sampledkey P false) A
            <= \sum_(0 <= s < (wcp_w P).-2)
                  AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s).
  by rewrite Adv_sym; exact: (UDw_telescope P false A VA).
have h5 : Adv (intermediates.G_post_chain P) (G_forge_sampledkey P false) A
          <= AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
           + \sum_(0 <= s < (wcp_w P).-2)
                AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s).
  eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_uniformchains P false)).
  by rewrite hPR; apply: lerD; [exact: lexx | exact: hUD0].
have h4 : Adv (intermediates.G_post_compress P) (G_forge_sampledkey P false) A
          <= AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                      (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
           + (AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
              + \sum_(0 <= s < (wcp_w P).-2)
                   AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s)).
  eapply le_trans; first exact: (Adv_triangle (G2 := intermediates.G_post_chain P)).
  by rewrite hCT; apply: lerD; [exact: lexx | exact: h5].
have h3 : Adv (intermediates.G_post_grind P) (G_forge_sampledkey P false) A
          <= AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
           + (AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                       (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
              + (AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
                 + \sum_(0 <= s < (wcp_w P).-2)
                      AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s))).
  eapply le_trans; first exact: (Adv_triangle (G2 := intermediates.G_post_compress P)).
  by rewrite hCP; apply: lerD; [exact: lexx | exact: h4].
have h2 : Adv (G_forge_uniformchains P true) (G_forge_sampledkey P false) A
          <= AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                      (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P)
           + (AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
              + (AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                          (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
                 + (AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
                    + \sum_(0 <= s < (wcp_w P).-2)
                         AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s)))).
  eapply le_trans; first exact: (Adv_triangle (G2 := intermediates.G_post_grind P)).
  by rewrite hGR; apply: lerD; [exact: lexx | exact: h3].
eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_uniformchains P true)).
eapply le_trans; first by apply: lerD; [exact: hUD1 | exact: h2].
exact: le6.
Qed.

(** THE HEADLINE: one-time known-message security of KEYED WOTS+C
    (chain starts PRF-derived from a hidden SKseed, as in the spec).
    Reading the statement:

    - LHS [Adv (G_forge_keyed … true) (G_forge_keyed … false) A] IS A's
      forgery probability against the keyed game (Sec.wots.hop.prf).
    - The middle six terms are [shrincs_wots_secure_ideal_sk]'s; the two
      PRF terms are the price of replacing the ideal chain starts by
      the PRF derivation, once on each side of the pair.
    - [wcp_Hcc] (at least one chain) is the PRF hop's data side
      condition (Sec.wots.hop.prf header); [grind_range P] as above. *)
Theorem shrincs_wots_secure
    (Hrange : grind_range P)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A) :
  Adv (G_forge_keyed P K PRF dK true) (G_forge_keyed P K PRF dK false) A
    <= AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK true)
     + \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P true s)
     + AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P)
     + AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
     + AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
     + AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
     + \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s)
     + AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK false).
Proof.
(* Same assembly discipline as [shrincs_wots_secure_ideal_sk] (performance
   note there): no [set]/[pose] on Adv terms, reassociation by
   [exact: le8]. *)
have le8 : forall p1 u1 gr cp ct pr u0 p0 : R,
    p1 + (u1 + gr + cp + ct + pr + u0 + p0)
    <= p1 + u1 + gr + cp + ct + pr + u0 + p0.
  by move=> *; rewrite !GRing.addrA; exact: lexx.
have hP1 : Adv (G_forge_keyed P K PRF dK true) (G_forge_sampledkey P true) A
           = AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK true).
  by apply: prf_hop_eq; assumption.
have hP0 : Adv (G_forge_sampledkey P false) (G_forge_keyed P K PRF dK false) A
           = AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK false).
  by rewrite Adv_sym; apply: prf_hop_eq; assumption.
have hMID := shrincs_wots_secure_ideal_sk Hrange A VA.
have h2 : Adv (G_forge_sampledkey P true) (G_forge_keyed P K PRF dK false) A
          <= \sum_(0 <= s < (wcp_w P).-2)
                AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P true s)
           + AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                      (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P)
           + AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
           + AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                      (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
           + AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
           + \sum_(0 <= s < (wcp_w P).-2)
                AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s)
           + AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK false).
  eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_sampledkey P false)).
  by apply: lerD; [exact: hMID | rewrite hP0; exact: lexx].
eapply le_trans; first exact: (Adv_triangle (G2 := G_forge_sampledkey P true)).
eapply le_trans; first by apply: lerD; [rewrite hP1; exact: lexx | exact: h2].
exact: le8.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The headline restated over the standard KOTS notion

    [Sec.wots.kots_link] proves [G_forge_sampledkey]/[G_forge_keyed] are
    PERFECTLY, and UNCONDITIONALLY, the generic valid-commit KOTS
    experiment [KOTS_vc_game] (Sec.lib.sig.kots) at
    [shrincs_wots_scheme P] / the keyed scheme [shrincs_wots_keyed P K PRF dK]
    (no [Hrange] side condition on the linking lemmas themselves — see
    that file's header). [AdvOf_perfect] swaps BOTH game bits (true and
    false) of an [AdvOf] term at once given a [perfect] equivalence at
    each bit, so composing it with [shrincs_wots_secure_ideal_sk] /
    [shrincs_wots_secure] below carries the same bound over to the
    standard notion's advantage, unchanged and with no new hop. *)

(** [shrincs_wots_secure_ideal_sk], restated as a bound on A's forgery
    advantage against the STANDARD known-message valid-commit
    experiment [KOTS_vc_game (shrincs_wots_scheme P)] (ideal chain
    starts) rather than the bespoke [G_forge_sampledkey]. *)
Theorem shrincs_wots_secure_kots_ideal_sk
    (Hrange : grind_range P)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A) :
  AdvOf (KOTS_vc_game (shrincs_wots_scheme P)) A
    <= \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P true s)
     + AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P)
     + AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
     + AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
     + AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
     + \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s).
Proof.
rewrite -(AdvOf_perfect (G_forge_sampledkey_KOTS_vc P)).
exact: shrincs_wots_secure_ideal_sk Hrange A VA.
Qed.

(** THE HEADLINE OVER THE STANDARD NOTION: [shrincs_wots_secure], restated
    as a bound on A's forgery advantage against [KOTS_vc_game
    (shrincs_wots_keyed P K PRF dK)] — the SAME 8-term bound, unchanged,
    since [G_forge_keyed_KOTS_vc] links the two games perfectly at every
    bit. A referee who only trusts the standard notion (Sec.lib.sig.kots)
    reads this statement, not [shrincs_wots_secure]'s. *)
Theorem shrincs_wots_secure_kots
    (Hrange : grind_range P)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_KOTS (shrincs_wots_scheme P)) A_export A) :
  AdvOf (KOTS_vc_game (shrincs_wots_keyed P K PRF dK)) A
    <= AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK true)
     + \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P true s)
     + AdvOf (STCRP_game (thf_grind P) (coll_grind P) (wcp_M P)
                (grind_enc P) (grind_prp P) (wcp_c_max P) 1) (A ∘ R_grind P)
     + AdvOf (SMTCR_game (thf_pkcompress P) (coll_pkcompress P) 1) (A ∘ R_compress P)
     + AdvOf (SMTCR_game (thf_chain P) (coll_chain P)
                (tcr_budget (wcp_chain_count P) (wcp_w P))) (A ∘ R_chain_tcr P)
     + AdvOf (SMPRE_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_chain_pre P)
     + \sum_(0 <= s < (wcp_w P).-2)
          AdvOf (SMUD_game (thf_chain P) (coll_chain P) (wcp_chain_count P)) (A ∘ R_ud P false s)
     + AdvOf (PRF_game (khf_prf P K PRF dK) (wcp_chain_count P)) (A ∘ R_prf P K PRF dK false).
Proof.
rewrite -(AdvOf_perfect (G_forge_keyed_KOTS_vc P K PRF dK)).
exact: shrincs_wots_secure Hrange A VA.
Qed.

End WOTSCTheorem.
