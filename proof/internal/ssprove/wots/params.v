(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.params

    The WOTS+C parameter record [wc_params]: one value carrying every
    section parameter the scheme, games, hops and bounds used to thread
    individually (types, Winternitz data, hash functions, samplers,
    grinding data, and the imaginary-tree anchor with its range proofs).
    Downstream files take a single [Context (P : wc_params)] instead of
    a 19-line Context block, and every scheme/game constant is a plain
    definition applied to [P] -- no [Local Notation] preamble.

    ** Letter key (the three hashes under attack)

    - [wcp_F]       the chain hash F        (SF_SHRINCS_WOTS_HASH, type 16);
    - [wcp_T_sf]    the pk compression T_sf (SF_SHRINCS_WOTS_PK, type 17) --
                    [_sf] = stateful single-function: one keyed hash
                    family serving the whole stateful (SF_) address
                    range, distinguished only by the ADRS tweak;
    - [wcp_H_grind] the grinding hash H_grind (SF_SHRINCS_WOTS_GRIND,
                    type 22), output read as [chain_count] base-w digits.

    ** Proof fields and definitional transparency (load-bearing)

    [wc_anchor_tagZ] / [wc_anchor_idxZ] below are DEFINITIONS, never
    opaque lemmas ([Qed]), and must stay that way: every smart
    constructor across the whole development receives the anchor bound
    proofs through these two names, so all call sites share literally
    the same proof term -- the exact address must stay DEFINITIONALLY
    equal wherever it is rebuilt (e.g. the chain address reached via
    the fold vs via the decoded tweak); [fin] has no definitional proof
    irrelevance, so two opaque witnesses would break that. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import addressing.
From Shrincs.internal.common Require address.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(** ** The parameter record *)

Record wc_params := {
  (* Spaces: public parameter (PKseed), hash domain (n-byte strings),
     message space (the 2n-bit output of Hmsg^sf feeding grinding). *)
  wcp_PP : choice_type ;
  wcp_N  : choice_type ;
  wcp_M  : choice_type ;

  (* Winternitz parameter and chain count, with positivity.  Declared
     before the hash functions because the exact address type
     [address.adrs chain_count w.-1] depends on them. *)
  wcp_w           : nat ;
  wcp_chain_count : nat ;
  wcp_Hcc : (0 < wcp_chain_count)%nat ;
  wcp_Hw  : (1 < wcp_w)%nat ;

  (* Imaginary-tree anchor (z_star, i_star) of this WOTS+C instance:
     the (node height, node index) ADRS fields of all its addresses.
     [wcp_zstar] is the wire format's 1-byte height field, so it must
     be byte-range for the ADRS round-trip to hold; [wcp_istar] is a
     2^64-bounded ADRS field ([anchor_idx_bound]). *)
  wcp_zstar : nat ;
  wcp_istar : nat ;
  wcp_zstar_range : (wcp_zstar < 256)%nat ;
  wcp_istar_range : anchor_idx_bound wcp_istar ;

  (* The three tweakable hashes (letter key in the header). *)
  wcp_F       : wcp_PP -> address.adrs wcp_chain_count wcp_w.-1 -> wcp_N -> wcp_N ;
  wcp_T_sf    : wcp_PP -> address.adrs wcp_chain_count wcp_w.-1 -> seq wcp_N -> wcp_N ;
  wcp_H_grind : wcp_PP -> address.adrs wcp_chain_count wcp_w.-1 -> wcp_M * nat -> nat ;

  (* Samplers: key generation (dPP, dN) and the dummy message sampler
     consumed only by the grinding thf instance's data fields. *)
  wcp_dPP : dist wcp_PP ;
  wcp_dN  : dist wcp_N ;
  wcp_dM  : dist wcp_M ;

  (* Target chain-sum and grinding-counter bound (c_max = 2^{8c}). *)
  wcp_constant_sum : nat ;
  wcp_c_max        : nat ;
}.

(* ================================================================== *)
(** ** The anchor-free core

    [wc_params_core] is [wc_params] minus the four anchor fields
    (z_star, i_star and their range proofs) -- everything a hash GAME
    can see.  The game instances (Shrincs.internal.ssprove.wots.games, Shrincs.internal.ssprove.wots.hop.prf's
    khf) are defined over the core and only wrapped back to
    [wc_params] for the scheme, so the 6 hash assumptions
    (Shrincs.internal.ssprove.axioms) can be stated with ZERO anchor
    quantification: the anchor is PROVABLY absent from their
    statements, not argued inert.  [wc_core_of] is the transparent
    projection; core and full spellings of every instance coincide by
    conversion (machine-checked at the SHA-256 instantiation by
    [axioms.wc_sha256_coreE]). *)

Record wc_params_core := {
  wcc_PP : choice_type ;
  wcc_N  : choice_type ;
  wcc_M  : choice_type ;

  wcc_w           : nat ;
  wcc_chain_count : nat ;
  wcc_Hcc : (0 < wcc_chain_count)%nat ;
  wcc_Hw  : (1 < wcc_w)%nat ;

  wcc_F       : wcc_PP -> address.adrs wcc_chain_count wcc_w.-1 -> wcc_N -> wcc_N ;
  wcc_T_sf    : wcc_PP -> address.adrs wcc_chain_count wcc_w.-1 -> seq wcc_N -> wcc_N ;
  wcc_H_grind : wcc_PP -> address.adrs wcc_chain_count wcc_w.-1 -> wcc_M * nat -> nat ;

  wcc_dPP : dist wcc_PP ;
  wcc_dN  : dist wcc_N ;
  wcc_dM  : dist wcc_M ;

  wcc_constant_sum : nat ;
  wcc_c_max        : nat ;
}.

Definition wc_core_of (P : wc_params) : wc_params_core := {|
  wcc_PP := wcp_PP P ;
  wcc_N  := wcp_N P ;
  wcc_M  := wcp_M P ;
  wcc_w := wcp_w P ;
  wcc_chain_count := wcp_chain_count P ;
  wcc_Hcc := wcp_Hcc P ;
  wcc_Hw  := wcp_Hw P ;
  wcc_F       := wcp_F P ;
  wcc_T_sf    := wcp_T_sf P ;
  wcc_H_grind := wcp_H_grind P ;
  wcc_dPP := wcp_dPP P ;
  wcc_dN  := wcp_dN P ;
  wcc_dM  := wcp_dM P ;
  wcc_constant_sum := wcp_constant_sum P ;
  wcc_c_max        := wcp_c_max P ;
|}.

(** The core's address type, tweak space and tweak decoder -- the only
    address vocabulary a hash game touches (decoding is total and
    anchor-free; see addressing.v). *)
Definition wc_adrs_core (H : wc_params_core) :=
  address.adrs (wcc_chain_count H) (wcc_w H).-1.

Definition wc_adrs_ch_core (H : wc_params_core) : choice_type :=
  addressing.adrs_sf_ch (wcc_chain_count H) (wcc_w H).

Definition decode_tweak_core (H : wc_params_core) (t : wc_adrs_ch_core H) :
    wc_adrs_core H :=
  addressing.decode_adrs (wcc_chain_count H) (wcc_w H) t.

(* ================================================================== *)
(** ** Derived address vocabulary

    The exact address type and tweak space of an instance, and the
    Addressing smart constructors specialized to it, as plain
    definitions over [P]. *)

(** The exact stateful address type of the instance. *)
Definition wc_adrs (P : wc_params) := address.adrs (wcp_chain_count P) (wcp_w P).-1.

(** Its encoded tweak space (a [choice_type], for the thf games). *)
Definition wc_adrs_ch (P : wc_params) : choice_type :=
  addressing.adrs_sf_ch (wcp_chain_count P) (wcp_w P).

(** The instance anchor and its two bound proofs.  TRANSPARENT -- see
    the header; do not turn these into [Qed] lemmas. *)
Definition wc_anchor (P : wc_params) : nat * nat := (wcp_zstar P, wcp_istar P).

Definition wc_anchor_tagZ (P : wc_params) :
  (Z.of_nat (wc_anchor P).1 < 256)%Z :=
  anchor_tag_bound_lt _ (wcp_zstar_range P).

Definition wc_anchor_idxZ (P : wc_params) :
  (Z.of_nat (wc_anchor P).2 < 2 ^ 64)%Z :=
  wcp_istar_range P.

(** ADRS^g, the grinding address (type 22). *)
Definition grind_adrs (P : wc_params) : wc_adrs P :=
  addressing.shrincs_wots_grind_adrs (wcp_chain_count P) (wcp_w P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P).

(** ADRS^pk, the pk-compression address (type 17). *)
Definition pk_adrs (P : wc_params) : wc_adrs P :=
  addressing.shrincs_wots_pk_adrs (wcp_chain_count P) (wcp_w P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P).

(** The EXACT chain address (type 16) at chain [i], position [pos],
    from their range proofs -- no clamp. *)
Definition chain_adrs_exact (P : wc_params) (i pos : nat)
    (Hi : (i < wcp_chain_count P)%nat) (Hpos : (pos < (wcp_w P).-1)%nat) : wc_adrs P :=
  addressing.shrincs_wots_chain_adrs (wcp_chain_count P) (wcp_w P) (wcp_Hcc P) (wcp_Hw P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P) i pos Hi Hpos.

(** ADRS^h, total and clamp-free: the exact chain address on in-range
    [(i, pos)] (the only pairs any fold reaches), a dummy (the pk
    address) out of range -- a [bool_dec] guard, not a clamp. *)
Definition chain_adrs (P : wc_params) (i pos : nat) : wc_adrs P :=
  addressing.shrincs_wots_chain_adrs_tot (wcp_chain_count P) (wcp_w P) (wcp_Hcc P) (wcp_Hw P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P) i pos.

(** On every reachable (in-range) index and position, [chain_adrs] IS
    the exact chain address, independent of the range proofs. *)
Lemma chain_adrs_exactE (P : wc_params) (i pos : nat)
    (Hi : (i < wcp_chain_count P)%nat) (Hpos : (pos < (wcp_w P).-1)%nat) :
  chain_adrs P i pos = chain_adrs_exact P i pos Hi Hpos.
Proof. exact: addressing.shrincs_wots_chain_adrs_totE. Qed.

(** ADRS^prf (type 21), total on the bare chain index. *)
Definition prf_adrs (P : wc_params) (i : nat) : wc_adrs P :=
  addressing.shrincs_wots_prf_adrs (wcp_chain_count P) (wcp_w P) (wcp_Hcc P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P) i.

(* ================================================================== *)
(** ** Tweak encoding

    [encode_tweak]/[decode_tweak]: the structural bijection between the
    instance's addresses and its encoded tweak space, plus the two
    per-hash-call tweaks (encoded chain / prf addresses) and their
    reconciliation and injectivity lemmas -- the Addressing facts
    restated over [P] so consumers rewrite without arity pins. *)

Definition encode_tweak (P : wc_params) (a : wc_adrs P) : wc_adrs_ch P :=
  addressing.encode_adrs (wcp_chain_count P) (wcp_w P) a.

Definition decode_tweak (P : wc_params) (t : wc_adrs_ch P) : wc_adrs P :=
  addressing.decode_adrs (wcp_chain_count P) (wcp_w P) t.

Lemma encode_tweakK (P : wc_params) : cancel (encode_tweak P) (decode_tweak P).
Proof. exact: addressing.encode_adrsK. Qed.

Lemma encode_tweak_inj (P : wc_params) : injective (encode_tweak P).
Proof. exact: addressing.encode_adrs_inj. Qed.

(** The per-hash-call chain tweak (encoded total chain address). *)
Definition chain_tweak (P : wc_params) (i pos : nat) : wc_adrs_ch P :=
  addressing.chain_tweak (wcp_chain_count P) (wcp_w P) (wcp_Hcc P) (wcp_Hw P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P) i pos.

Definition prf_tweak (P : wc_params) (i : nat) : wc_adrs_ch P :=
  addressing.prf_tweak (wcp_chain_count P) (wcp_w P) (wcp_Hcc P)
    (wc_anchor P) (wc_anchor_tagZ P) (wc_anchor_idxZ P) i.

Lemma decode_chain_tweak (P : wc_params) (i pos : nat) :
  decode_tweak P (chain_tweak P i pos) = chain_adrs P i pos.
Proof. exact: addressing.decode_adrs_chain_tweak. Qed.

Lemma decode_prf_tweak (P : wc_params) (i : nat) :
  decode_tweak P (prf_tweak P i) = prf_adrs P i.
Proof. exact: addressing.decode_adrs_prf_tweak. Qed.

Lemma chain_tweak_inj (P : wc_params) (i pos i' pos' : nat) :
  (i < wcp_chain_count P)%nat -> (i' < wcp_chain_count P)%nat ->
  (pos < (wcp_w P).-1)%nat -> (pos' < (wcp_w P).-1)%nat ->
  chain_tweak P i pos = chain_tweak P i' pos' -> i = i' /\ pos = pos'.
Proof. exact: addressing.chain_tweak_inj. Qed.

Lemma prf_tweak_inj (P : wc_params) (i i' : nat) :
  (i < wcp_chain_count P)%nat -> (i' < wcp_chain_count P)%nat ->
  prf_tweak P i = prf_tweak P i' -> i = i'.
Proof. exact: addressing.prf_tweak_inj. Qed.

(* ================================================================== *)
(** ** Shared side condition

    The sole data side condition of the security theorem: H_grind's
    output fits in [chain_count] base-w digits (digest injectivity via
    [digits_w] needs its argument below [w ^ chain_count]). *)

Definition grind_range (P : wc_params) : Prop :=
  forall (pp : wcp_PP P) (a : wc_adrs P) (x : wcp_M P * nat),
    (wcp_H_grind P pp a x < expn (wcp_w P) (wcp_chain_count P))%nat.
