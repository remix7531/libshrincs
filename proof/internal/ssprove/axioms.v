(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.axioms

    Connects the abstract, unconditionally-proved headline theorem
    (Sec.instantiation's [shrincs_wots_secure_shrincs], itself built on
    Sec.theorem's [shrincs_wots_secure]) to the CONCRETE
    hash construction from [Model.wots] (truncated SHA-256, pk_seed ||
    zeros(48) || ADRS || M), yielding [shrincs_wots_secure_sha256]: an
    unconditional bound on WOTS+C-with-real-SHA256's one-time forgery
    advantage in terms of 6 named hardness-assumption constants.

    ** The choice_type encoding

    [instantiation.v]'s concrete numbers use [N_shrincs := 'fin (2^128)]
    (16-byte hash values) and [M_shrincs := 'fin (2^256)] (the 32-byte
    grinding message) as bare mathcomp ordinals -- SSProve's [chFin n]
    IS ['I_n], transparently (confirmed: [instantiation.v]'s own
    [n0_shrincs] is built as a bare [Ordinal]).  [Model.wots]'s hash
    functions live over [Model.sha256.block = list Model.byte.byte]
    instead, with no length invariant in the TYPE (lengths are proven
    facts, e.g. [Model.theory.wots.H_grind_length]).  The encoding
    bridges these:

    - [decode_block bits n]: the [bits]-byte big-endian rendering of
      [n < 256 ^ bits], built directly from [Model.math.encoding]'s
      already-proved [be_num]/[digits_w] machinery rather than
      [Model.address.to_byte], since staying in [digits_w] vocabulary
      throughout makes the round-trip ([encode16_decode16] below) a
      direct corollary of [Model.math.encoding.be_num_rev_digits]
      instead of needing a second, independent Z-side bridge.
    - [decode16]/[decode32]: [decode_block] at [N_shrincs]/[M_shrincs]'s own
      ordinal value -- used to turn a games-layer hash VALUE into a
      [Model.wots]-shaped argument.
    - [encode16]: the reverse direction (a [Model.wots] hash OUTPUT
      back into [N_shrincs]), made TOTAL over every [block] (not just
      16-byte ones) by clipping/zero-padding to exactly 16 bytes
      first ([block16_norm]) -- harmless in practice, since every
      value [encode16] is ever applied to (a call to [Model.wots.F] /
      [T_sf] / [PRF] / [H_grind]) already has length exactly 16 by
      construction, so the normalization is a no-op there.
    - [encode16_decode16]: the CRITICAL soundness property --
      decode-then-encode is the identity on [N_shrincs], i.e. every
      possible 16-byte-string value the games layer can sample
      corresponds to an actual byte string, encoded back losslessly.
      Without this, "uniform N_shrincs" and "uniform 16-byte string"
      could disagree.  (The other direction, encode-then-decode, is
      not needed: nothing here reconstructs an arbitrary [block] from
      its own encoding.)

    IMPORT DISCIPLINE (see Sec.bridge's header for the full
    explanation): [BinInt] stays a plain [Import] (Z literals/infix
    notation) and [Znat] a plain [Require] (qualified [Znat.Z2Nat.foo]
    access) -- `Require Import ZArith`/`Require Import Znat` both
    silently shadow mathcomp's nat "^" (turning [expn] into
    [Nat.pow]), breaking every [digits_w]/[expn] lemma with no
    warning.  Also load-bearing: numeric comparisons need an explicit
    [%nat] annotation in this file (Order.POrderTheory / GRing.Theory,
    imported for [instantiation.v]'s own [ring_scope] conventions,
    otherwise capture bare "<"/exponent notation).

    ** The concrete hash instantiation

    [F_sha256]/[T_sf_sha256]/[PRF_sha256]/[H_grind0_sha256] wrap
    [Model.wots.F]/[T_sf]/[PRF]/[H_grind] through [decode16]/[decode32]
    on the way in and [encode16] on the way out; [T_sf_sha256]
    additionally flattens its [seq N_shrincs] argument into one [block]
    with [flatten], matching [Model.wots]'s own
    [T_sf pk_seed pk_adrs (concat (chain_tips ...))] convention.
    [H_grind0_sha256] keeps its output as an [N_shrincs] ordinal rather
    than projecting to [nat] -- [instantiation.v]'s own
    [H_grind_shrincs := nat_of_ord \o H_grind0] does that projection, and
    at THIS instantiation [nat_of_ord (H_grind0_sha256 pp a (m, c))]
    is exactly [Model.math.encoding]'s [be_num (nat_bytes
    (Model.wots.H_grind ...))] -- i.e. [scheme.v]'s abstract nat-digest
    [H_grind] reads the concrete SHA-256 grinding output as a
    big-endian number, matching
    [Sec.bridge.digest_of_bridge]/[good_counter_bridge]'s own
    [Model.math.encoding.be_num] reading.  (The digit orders are now
    ALIGNED: the games' [scheme.digest_of] reads MSB-first ([rev
    (digits_w ...)]), the same
    order as [Model.wots.base_2b], so the earlier MSB/LSB re-indexing
    caveat is gone -- [Sec.wots.model_bridge.digest_of_modelE] proves the
    games digest EQUALS the model digest on the nose, and the whole
    games<->model correspondence is discharged there, not merely up to a
    relabeling.)

    [grind_range]/[Hcc] ([instantiation.v]'s [shrincs_Hrange]/[shrincs_Hcc])
    carry over completely UNCHANGED regardless of which concrete functions
    instantiate the record: they only use [H_grind_shrincs]'s CODOMAIN
    shape ([nat_of_ord] of some ['fin (2^128)] value is always
    [< 2^128 = 16^32] by [ltn_ord]), never its definition.  So
    connecting the model doesn't require re-proving them --
    instantiating [P_shrincs]'s hash parameters below (the transparent
    [wc_sha256] record) is the WHOLE connection.

    ** The 6 hash-game assumptions

    [shrincs_wots_secure_shrincs]'s conclusion is a sum of 8 [AdvOf] terms
    over 6 DISTINCT game families (PRF-security and the SM-UD chain
    game each appear twice, at the two symmetric hops of the game
    sequence, composed with different reductions): PRF-security,
    SM-UD (chain-hash under-determinedness), STCRP (grinding),
    SM-TCR at the pk-compression hash, SM-TCR at the chain hash
    (different [tcr_budget] parameter), and SM-PRE (chain preimage).  Each
    is SCOPED to valid adversaries: the [VB] premise bounds [AdvOf G B]
    only for packages that honestly implement the game's adversary
    interface -- strictly WEAKER than an unconditional bound over every
    [nom_package B] (each application pays a one-line discharge,
    [valid_adv_link] in Sec.lib.prelude, from the reduction's own
    bundled validity).  Mirrors how the VST tree already axiomatizes
    SHA-256's own properties ([SHA256], [body_sha256] in
    proof/vst/contract/gprog.v) rather than proving them -- this is the
    SSProve tree's analogous, now-visible expansion of trust surface
    (previously zero axioms; see proof/assumptions/check.sh gate 2,
    updated alongside this file).

    REVIEWER NOTE (assumption minimality): each axiom's game terms are
    built from [wc_sha256_core] -- the anchor-free core record
    ([params.wc_params_core]) at the SHA-256 hashes, spelled out field
    by field below.  No axiom mentions the imaginary-tree anchor, its
    range proofs, or any term containing them, AT ANY DEPTH: the
    anchor's absence is a syntactic fact about the statements, not an
    argument about the games' semantics.  [wc_sha256_coreE] machine-
    checks that the core record is definitionally the core projection
    of every [wc_sha256 zs is_ hz hi], which is what lets the final
    theorem (stated over full instances) consume the axioms by pure
    conversion.  The count stays exactly 6 [Axiom] plus the 1
    [Parameter] line of bound constants (audit gate 2).

    ** The payoff

    [shrincs_wots_secure_sha256]: composing the 6 axioms with
    [shrincs_wots_secure_shrincs] via real-number [<=] transitivity/
    additivity gives an unconditional, closed-form bound on
    WOTS+C-with-truncated-SHA256's forgery advantage. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib Require Import prelude games.thf games.smtcr games.smpre games.smud
  games.stcrp games.prf sig.scheme sig.kots.
From Shrincs.internal.ssprove.lib Require Import chain.core.
From Shrincs.internal.common Require Import math.encoding.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import scheme games
  hop.grind hop.compress hop.chain_tcr hop.chain_pre hop.ud hop.prf kots_link.
Require Import Shrincs.internal.ssprove.wots.theorem.
From mathcomp Require Import reals.
Require Import Shrincs.internal.ssprove.wots.instantiation.
From Shrincs.internal.ssprove Require Import bridge.
From Shrincs.internal.common Require wots byte address.
(* See header IMPORT DISCIPLINE: BinInt (Import) + Znat (plain
   Require) keep Z literals/infix notation without shadowing
   mathcomp's nat "^". *)
From Stdlib Require Import BinInt Lia.
From Stdlib Require Znat.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** ** Digit/byte <-> ordinal encoding *)

Definition digit_byte (d : nat) : byte.byte := byte.byte_mod256 (Z.of_nat d).

Lemma digit_byte_val (d : nat) : (d < 256)%nat -> byte.byte_val (digit_byte d) = Z.of_nat d.
Proof.
move=> /ltP hd.
rewrite /digit_byte.
have hrange : (0 <= Z.of_nat d < 256)%Z by lia.
by rewrite (byte.byte_mod256_small (Z.of_nat d) hrange).
Qed.

Definition decode_block (bits n : nat) : sha256.block := rev (map digit_byte (digits_w 256 bits n)).

Lemma nat_bytes_decode_block (bits n : nat) : nat_bytes (decode_block bits n) = rev (digits_w 256 bits n).
Proof.
rewrite /decode_block /nat_bytes -map_rev -map_comp.
rewrite -{2}(map_id (rev (digits_w 256 bits n))).
apply: (proj1 (eq_in_map _ _ _)) => d hd.
rewrite /=.
have hw := wf_digits_w (w:=256) bits n isT.
move: hd; rewrite mem_rev => hd.
move/allP: hw => /(_ d hd) /ltP hd256.
rewrite byte.byte_modulus.
rewrite Z.mod_small; [lia |].
by rewrite Znat.Nat2Z.id.
Qed.

Lemma size_decode_block (bits n : nat) : size (decode_block bits n) = bits.
Proof. by rewrite /decode_block size_rev size_map size_digits_w. Qed.

Lemma encode_decode_block (bits n : nat) : (n < 256 ^ bits)%nat ->
  be_num (nat_bytes (decode_block bits n)) = n.
Proof. move=> hn. by rewrite nat_bytes_decode_block be_num_rev_digits. Qed.

Lemma pow256_16 : (256 ^ 16 : nat) = (2 ^ 128 : nat).
Proof. have -> : (256 : nat) = (2 ^ 8 : nat) by []. by rewrite -expnM. Qed.

Lemma pow256_32 : (256 ^ 32 : nat) = (2 ^ 256 : nat).
Proof. have -> : (256 : nat) = (2 ^ 8 : nat) by []. by rewrite -expnM. Qed.

Definition decode16 (x : N_shrincs) : sha256.block := decode_block 16 (nat_of_ord x).
Definition decode32 (x : M_shrincs) : sha256.block := decode_block 32 (nat_of_ord x).

Definition block16_norm (X : sha256.block) : sha256.block :=
  List.firstn 16 (X ++ nseq 16 byte.zero_byte).

Lemma size_block16_norm (X : sha256.block) : size (block16_norm X) = 16.
Proof.
rewrite /block16_norm firstn_take size_takel //.
by rewrite size_cat size_nseq leq_addl.
Qed.

Lemma block16_norm_id (X : sha256.block) : size X = 16 -> block16_norm X = X.
Proof.
move=> hX.
rewrite /block16_norm firstn_take.
by rewrite (take_size_cat) //.
Qed.

Lemma be_num_lt16 (Y : sha256.block) :
  size Y = 16 -> all (fun v => (v < 256)%nat) (nat_bytes Y) ->
  (be_num (nat_bytes Y) < 2 ^ 128)%nat.
Proof.
move=> hsz hall.
have h1 := be_num_lt hall.
rewrite size_map hsz pow256_16 in h1.
exact: h1.
Qed.

(** The reverse direction: any [Model.wots] hash output, normalized to
    exactly 16 bytes (a no-op on every value this file actually
    applies it to), read as an [N_shrincs] ordinal. *)
Definition encode16 (X : sha256.block) : N_shrincs.
apply: (Ordinal (n:=2 ^ 128) (m:=be_num (nat_bytes (block16_norm X)))).
apply: be_num_lt16; first exact: size_block16_norm.
apply/allP => v hv.
case/mapP: hv => c hc ->.
have [h0 h256] := byte.byte_val_range c.
apply/ltP; lia.
Defined.

Lemma val_encode16 (X : sha256.block) : nat_of_ord (encode16 X) = be_num (nat_bytes (block16_norm X)).
Proof. by []. Qed.

(** THE soundness property: every possible [N_shrincs] value round-trips
    through its 16-byte rendering (header). *)
Lemma encode16_decode16 (n : N_shrincs) : encode16 (decode16 n) = n.
Proof.
case: n => [m hm].
apply: ord_inj.
rewrite val_encode16.
rewrite /decode16.
have -> : decode_block 16 (Ordinal (n:=2 ^ 128) (m:=m) hm) = decode_block 16 m by [].
rewrite block16_norm_id; first exact: size_decode_block.
apply: encode_decode_block.
rewrite pow256_16.
exact: hm.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The concrete truncated-SHA256 hash instantiation

    All four are anchor-free: the WOTS+C address type at the shrincs
    numbers ([address.adrs chain_count_shrincs w_shrincs.-1]) is
    convertible to [Model.wots]'s own [adrs = address.adrs 32 15]. *)

Definition F_sha256 (pp : PP_shrincs)
    (a : address.adrs chain_count_shrincs w_shrincs.-1) (x : N_shrincs) : N_shrincs :=
  encode16 (wots.F (decode16 pp) a (decode16 x)).

Definition T_sf_sha256 (pp : PP_shrincs)
    (a : address.adrs chain_count_shrincs w_shrincs.-1) (xs : seq N_shrincs) : N_shrincs :=
  encode16 (wots.T_sf (decode16 pp) a (flatten (map decode16 xs))).

Definition PRF_sha256 (pp : PP_shrincs)
    (a : address.adrs chain_count_shrincs w_shrincs.-1) (k : K_shrincs) : N_shrincs :=
  encode16 (wots.PRF (decode16 pp) a (decode16 k)).

Definition H_grind0_sha256 (pp : PP_shrincs)
    (a : address.adrs chain_count_shrincs w_shrincs.-1) (mc : M_shrincs * nat) : N_shrincs :=
  encode16 (wots.H_grind (decode16 pp) a (decode32 mc.1) (Z.of_nat mc.2)).

(* ------------------------------------------------------------------ *)
(** ** The concrete parameter record

    [instantiation.P_shrincs] at the SHA-256 hashes, one anchor per
    [(zs, is_)] leaf position.  TRANSPARENT (a [Definition]): the 6
    axioms below read through it, one delta-unfold away from the
    fully-applied game spellings. *)

Definition wc_sha256 (zs is_ : nat)
    (hz : (zs < 256)%nat) (hi : anchor_idx_bound is_) : wc_params :=
  P_shrincs F_sha256 T_sf_sha256 H_grind0_sha256 zs is_ hz hi.

(** The anchor-free core (params.wc_params_core) of [wc_sha256],
    spelled field by field so the record is MANIFESTLY anchor-free --
    the 6 axioms below quantify over game instances built from THIS
    record, so no anchor (and no anchor range proof) can appear in any
    assumption, at any depth. *)
Definition wc_sha256_core : wc_params_core := {|
  wcc_PP := PP_shrincs ;
  wcc_N  := N_shrincs ;
  wcc_M  := M_shrincs ;
  wcc_w := w_shrincs ;
  wcc_chain_count := chain_count_shrincs ;
  wcc_Hcc := shrincs_Hcc ;
  wcc_Hw  := shrincs_Hw ;
  wcc_F       := F_sha256 ;
  wcc_T_sf    := T_sf_sha256 ;
  wcc_H_grind := H_grind_shrincs H_grind0_sha256 ;
  wcc_dPP := dPP_shrincs ;
  wcc_dN  := dN_shrincs ;
  wcc_dM  := dM_shrincs ;
  wcc_constant_sum := constant_sum_shrincs ;
  wcc_c_max        := c_max_shrincs ;
|}.

(** Machine-checked transparency witness: [wc_sha256_core] IS the core
    projection of [wc_sha256], at every anchor, definitionally -- the
    final theorem's axiom applications close by this conversion. *)
Lemma wc_sha256_coreE (zs is_ : nat)
    (hz : (zs < 256)%nat) (hi : anchor_idx_bound is_) :
  wc_core_of (wc_sha256 zs is_ hz hi) = wc_sha256_core.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** The 6 hash-game assumptions

    Stated over the anchor-free core instances ([*_core] of
    Sec.wots.games / Sec.wots.hop.prf at [wc_sha256_core]): the anchor
    is PROVABLY absent from every assumption statement.  Each is also
    SCOPED to valid adversaries -- the [VB] premise asks the bound only
    for packages that honestly implement the game's adversary
    interface, a strictly weaker assumption than an unconditional
    bound; the theorem below pays the discharge at every application
    site via [valid_adv_link] (Sec.lib.prelude). *)

Parameter eps_prf eps_smud eps_stcrp eps_tcr_pk eps_tcr_chain eps_pre : R.

Axiom sha256_prf_secure : forall (B : nom_package)
    (VB : ValidPackage (loc B)
            (I_PRF (khf_prf_core wc_sha256_core K_shrincs PRF_sha256 dK_shrincs))
            A_export B),
  AdvOf (PRF_game (khf_prf_core wc_sha256_core K_shrincs PRF_sha256 dK_shrincs)
           chain_count_shrincs) B <= eps_prf.

Axiom sha256_smud_secure : forall (B : nom_package)
    (VB : ValidPackage (loc B)
            (I_SMUD (thf_chain_core wc_sha256_core) (coll_chain_core wc_sha256_core))
            A_export B),
  AdvOf (SMUD_game (thf_chain_core wc_sha256_core) (coll_chain_core wc_sha256_core)
           chain_count_shrincs) B <= eps_smud.

Axiom sha256_stcrp_secure : forall (B : nom_package)
    (VB : ValidPackage (loc B)
            (I_STCRP (thf_grind_core wc_sha256_core) (coll_grind_core wc_sha256_core)
               M_shrincs)
            A_export B),
  AdvOf (STCRP_game (thf_grind_core wc_sha256_core) (coll_grind_core wc_sha256_core)
           M_shrincs (grind_enc_core wc_sha256_core) (grind_prp_core wc_sha256_core)
           c_max_shrincs 1) B <= eps_stcrp.

Axiom sha256_tcr_pk_secure : forall (B : nom_package)
    (VB : ValidPackage (loc B)
            (I_SMTCR (thf_pkcompress_core wc_sha256_core) (coll_pkcompress_core wc_sha256_core))
            A_export B),
  AdvOf (SMTCR_game (thf_pkcompress_core wc_sha256_core)
           (coll_pkcompress_core wc_sha256_core) 1) B <= eps_tcr_pk.

Axiom sha256_tcr_chain_secure : forall (B : nom_package)
    (VB : ValidPackage (loc B)
            (I_SMTCR (thf_chain_core wc_sha256_core) (coll_chain_core wc_sha256_core))
            A_export B),
  AdvOf (SMTCR_game (thf_chain_core wc_sha256_core) (coll_chain_core wc_sha256_core)
           (tcr_budget chain_count_shrincs w_shrincs)) B <= eps_tcr_chain.

Axiom sha256_pre_secure : forall (B : nom_package)
    (VB : ValidPackage (loc B)
            (I_SMPRE (thf_chain_core wc_sha256_core) (coll_chain_core wc_sha256_core))
            A_export B),
  AdvOf (SMPRE_game (thf_chain_core wc_sha256_core) (coll_chain_core wc_sha256_core)
           chain_count_shrincs) B <= eps_pre.

(* ------------------------------------------------------------------ *)
(** ** The headline corollary *)

Section HashAssumptions.

(** The instance anchor (any leaf position; see Sec.wots.scheme). *)
Context (zstar istar : nat) (zstar_range : (zstar < 256)%nat).
Context (istar_range : anchor_idx_bound istar).

(** THE payoff: WOTS+C over truncated-SHA256 (pk_seed || zeros(48) ||
    ADRS || M, [Model.wots]'s construction) is one-time
    known-message-secure, unconditionally, at a bound built from the
    6 axioms above. *)
Theorem shrincs_wots_secure_sha256
    (A : nom_package)
    (VA : ValidPackage (loc A)
            (I_KOTS (shrincs_wots_scheme (wc_sha256 zstar istar zstar_range istar_range)))
            A_export A) :
  Adv (G_forge_keyed (wc_sha256 zstar istar zstar_range istar_range)
         K_shrincs PRF_sha256 dK_shrincs true)
      (G_forge_keyed (wc_sha256 zstar istar zstar_range istar_range)
         K_shrincs PRF_sha256 dK_shrincs false)
      A
  <= eps_prf + \sum_(0 <= s < w_shrincs.-2) eps_smud + eps_stcrp + eps_tcr_pk + eps_tcr_chain + eps_pre
     + \sum_(0 <= s < w_shrincs.-2) eps_smud + eps_prf.
Proof.
apply: le_trans.
exact: (shrincs_wots_secure_shrincs F_sha256 T_sf_sha256 PRF_sha256 H_grind0_sha256
          zstar istar zstar_range istar_range A VA).
apply: lerD; first apply: lerD; first apply: lerD; first apply: lerD;
  first apply: lerD; first apply: lerD; first apply: lerD.
- exact: sha256_prf_secure (valid_adv_link VA).
- apply: ler_sum => s _; exact: sha256_smud_secure (valid_adv_link VA).
- exact: sha256_stcrp_secure (valid_adv_link VA).
- exact: sha256_tcr_pk_secure (valid_adv_link VA).
- exact: sha256_tcr_chain_secure (valid_adv_link VA).
- exact: sha256_pre_secure (valid_adv_link VA).
- apply: ler_sum => s _; exact: sha256_smud_secure (valid_adv_link VA).
- exact: sha256_prf_secure (valid_adv_link VA).
Qed.

(** [shrincs_wots_secure_sha256] restated over the STANDARD known-message
    valid-commit experiment [KOTS_vc_game] (Sec.lib.sig.kots): the same
    unconditional bound, modulo the same 6 named hash-hardness axioms,
    on A's forgery advantage against [KOTS_vc_game (shrincs_wots_keyed
    (wc_sha256 zstar istar zstar_range istar_range) K_shrincs PRF_sha256
    dK_shrincs)] rather than the bespoke [G_forge_keyed] -- the two are
    PERFECTLY, unconditionally, the same game
    ([Sec.wots.kots_link.G_forge_keyed_KOTS_vc]), so [AdvOf_perfect]
    carries the bound over unchanged. This is the referee-facing
    surface: [KOTS_vc_game], [shrincs_wots_keyed], [wc_sha256] and the
    6 [eps_*] constants. *)
Theorem shrincs_wots_secure_kots_sha256
    (A : nom_package)
    (VA : ValidPackage (loc A)
            (I_KOTS (shrincs_wots_scheme (wc_sha256 zstar istar zstar_range istar_range)))
            A_export A) :
  AdvOf (KOTS_vc_game (shrincs_wots_keyed (wc_sha256 zstar istar zstar_range istar_range)
           K_shrincs PRF_sha256 dK_shrincs)) A
  <= eps_prf + \sum_(0 <= s < w_shrincs.-2) eps_smud + eps_stcrp + eps_tcr_pk + eps_tcr_chain + eps_pre
     + \sum_(0 <= s < w_shrincs.-2) eps_smud + eps_prf.
Proof.
rewrite -(AdvOf_perfect (G_forge_keyed_KOTS_vc (wc_sha256 zstar istar zstar_range istar_range)
            K_shrincs PRF_sha256 dK_shrincs)).
exact: shrincs_wots_secure_sha256 A VA.
Qed.

End HashAssumptions.
