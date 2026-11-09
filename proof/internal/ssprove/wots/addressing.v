(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.addressing

    The WOTS+C-specific tweak layer, split off [Sec.addressing] (the
    scheme-neutral address core: the flat coproduct [adrs_sum]/[Finite]
    instance, the exact tweak space [adrs_sf_ch] with its
    [encode_adrs]/[decode_adrs] bijection, and the anchor smart
    constructor [anchor_adrs] -- see that file's header for why the
    split runs there).  Everything in THIS file is specific to WOTS+C's
    chains and grinding, so a future scheme (the FXMSS hypertree) can
    import [Sec.addressing] alone and build its own tweaks without
    pulling this file in.

    ** Exact [nat -> fin] placement at the SSProve boundary

    The reachable-states model is EXACT: every [fin] field is built from
    a bound proof (no saturating totalizer).  So the SSProve boundary
    places the WOTS+C chain INDEX and POSITION EXACTLY too, via
    [fin_of_nat] / [fin_of_Z] from the field's [< chain_count] / [< w.-1]
    range proof -- see [shrincs_wots_chain_adrs].  The chain-index and
    position boundaries where a bare [nat] is handed in with no bound in
    scope (game code, the [nat * nat] tweak) are totalized by an
    EXACT-in-range / dummy-out-of-range wrapper ([shrincs_wots_chain_adrs_tot]
    / [shrincs_wots_prf_adrs]): a [Bool.bool_dec] guard, NOT a clamp -- an
    unreachable out-of-range index names a distinct unused address
    rather than truncating a value.

    The two per-hash-call tweaks ([chain_tweak], [prf_tweak]) are the
    encoded chain/prf addresses; [decode_adrs_chain_tweak] /
    [decode_adrs_prf_tweak] reconcile them with the concrete addresses
    (trivially, by [otf_fto]).  Their index-injectivity
    ([chain_tweak_inj], [prf_tweak_inj]) is CONDITIONAL on the chain
    INDEX (and position) being in range ([< chain_count] / [< w.-1]):
    BOTH fields are placed EXACTLY (their range proofs are builder
    arguments, [fin_of_nat]/[fin_of_Z], NO clamp), and the [nat]-boundary
    total wrapper reduces to that exact address only for in-range
    indices -- an out-of-range index is a distinct unused (dummy)
    address, need not be distinguished, so injectivity is stated on
    in-range indices, which is all the consumers ever need. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.common Require address.
From Shrincs.internal.common Require Import fin.
From Stdlib Require Import ZArith Lia Bool.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ================================================================== *)
Section WcTweak.

(** The WOTS+C chain count and Winternitz parameter, with their
    positivity hypotheses (mathcomp [ltn]).  [pos_bound := w.-1] is the
    position field bound. *)
Context (chain_count w : nat).
Context (Hcc : (0 < chain_count)%nat) (Hw : (1 < w)%nat).
Local Abbreviation pos_bound := (w.-1).

(** Positivity of [pos_bound], in the Peano [lt] shape the model's
    [shrincs_wots_hash_adrs] expects (the model is Stdlib-only). *)
Local Lemma Hpb : (0 < pos_bound)%coq_nat.
Proof. apply/ltP. by case: w Hw => [|[|w']]. Qed.

(** The [Z]-side positivity of the chain-count bound. *)
Local Lemma HccZ : (0 < Z.of_nat chain_count)%Z.
Proof. move/ltP: Hcc; lia. Qed.

(** Z-side range of the EXACT chain-index [fin] field, from the mathcomp
    bound [Hi].  The ambient positivity [HccZ] is kept in the proof term
    so this lemma (and every builder that uses it) carries [Hcc] in its
    section footprint -- the downstream [Addressing.* chain_count w Hcc ..]
    notation pins depend on that arity. *)
Local Lemma chain_idx_boundZ (i : nat) (Hi : (i < chain_count)%nat) :
  (0 <= Z.of_nat i < Z.of_nat chain_count)%Z.
Proof. move/ltP: Hi => Hi; move: HccZ; lia. Qed.

Local Abbreviation adrs_sf := (address.adrs chain_count pos_bound).

(** The core file's per-(chain_count,w) specializations, brought back
    into unqualified scope (the idiom every [Sec.wots.*] consumer of
    [Sec.addressing] already uses -- see e.g. [Sec.wots.scheme]). *)
Local Abbreviation adrs_sf_ch := (addressing.adrs_sf_ch chain_count w).
Local Abbreviation encode_adrs := (addressing.encode_adrs chain_count w).
Local Abbreviation decode_adrs := (addressing.decode_adrs chain_count w).
Local Abbreviation encode_adrs_inj := (addressing.encode_adrs_inj chain_count w).
Local Abbreviation anchor_adrs := (addressing.anchor_adrs chain_count w).

(** The EXACT chain-index [fin] field: [i] placed at bound [chain_count]
    from its range proof [Hi], NO clamp ([fin_val] is [Z.of_nat i]). *)
Definition chain_fin (i : nat) (Hi : (i < chain_count)%nat) : fin (Z.of_nat chain_count) :=
  fin_of_Z (Z.of_nat chain_count) (Z.of_nat i) (chain_idx_boundZ i Hi).

(* ------------------------------------------------------------------ *)
(** ** The WOTS+C smart constructors, built from the anchor

    [Sec.addressing.anchor_adrs] gives any carrier holding the
    [(zstar, istar)] anchor; the WOTS+C sibling addresses of one
    instance (grind / chain / pk / prf) are derived by typing that
    anchor and, for the chain address, placing the chain index and
    position EXACTLY. *)

Definition shrincs_wots_grind_adrs (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z) : adrs_sf :=
  address.shrincs_wots_grind_adrs (anchor_adrs t Htag Hidx).

(** The EXACT chain address: BOTH the chain index [i] ([< chain_count])
    and the position [pos] ([< pos_bound]) are placed EXACTLY from their
    range proofs ([chain_fin] / [fin_of_nat]), NO clamp. *)
Definition shrincs_wots_chain_adrs (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z)
    (i pos : nat) (Hi : (i < chain_count)%nat) (Hpos : (pos < pos_bound)%nat) : adrs_sf :=
  address.set_hash_pos
    (address.shrincs_wots_hash_adrs Hpb (anchor_adrs t Htag Hidx) (chain_fin i Hi))
    (fin_of_nat (Z.of_nat pos_bound) pos (natZ_lt pos pos_bound Hpos)).

(** Proof irrelevance of the exact chain address: the built address
    depends on [i]/[pos] only through their values, not through WHICH
    range proof was supplied ([fin_val_inj] on each field).  The bridges
    that meet a chain address built at two different range proofs (fold
    step vs decoded tweak) reconcile here. *)
Lemma shrincs_wots_chain_adrs_pirr t Htag Hidx i pos Hi Hpos Hi' Hpos' :
  shrincs_wots_chain_adrs t Htag Hidx i pos Hi Hpos
  = shrincs_wots_chain_adrs t Htag Hidx i pos Hi' Hpos'.
Proof.
rewrite /shrincs_wots_chain_adrs.
have -> : chain_fin i Hi = chain_fin i Hi'
  by apply: fin_val_inj; rewrite /chain_fin !fin_val_of_Z.
have -> : fin_of_nat (Z.of_nat pos_bound) pos (natZ_lt pos pos_bound Hpos)
        = fin_of_nat (Z.of_nat pos_bound) pos (natZ_lt pos pos_bound Hpos').
  by apply: fin_val_inj; rewrite !fin_val_of_nat.
by [].
Qed.

(** Index/position injectivity of the exact chain address (address
    level): both fields are placed EXACTLY (recovered [Z] values
    [Z.of_nat i] / [Z.of_nat pos], no clamp), so injectivity is
    unconditional -- the range proofs are the builder arguments.
    Consumed by [chain_tweak_inj] and by [Sec.analysis]. *)
Lemma shrincs_wots_chain_adrs_inj
    {t Htag Hidx i pos Hi Hpos i' pos' Hi' Hpos'} :
  shrincs_wots_chain_adrs t Htag Hidx i pos Hi Hpos
    = shrincs_wots_chain_adrs t Htag Hidx i' pos' Hi' Hpos' ->
  i = i' /\ pos = pos'.
Proof.
move=> hEq.
have hcv : Z.of_nat i = Z.of_nat i'.
  by move: (congr1 (@address.payload_b_z _ _) hEq); rewrite /shrincs_wots_chain_adrs /chain_fin /= => ->.
have hpv : Z.of_nat pos = Z.of_nat pos'.
  by move: (congr1 (@address.payload_c_z _ _) hEq); rewrite /shrincs_wots_chain_adrs /= => ->.
by split; [exact: Nat2Z.inj hcv | exact: Nat2Z.inj hpv].
Qed.

Definition shrincs_wots_pk_adrs (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z) : adrs_sf :=
  address.shrincs_wots_pk_adrs (anchor_adrs t Htag Hidx).

(** TOTAL, clamp-free chain address for the [nat]-indexed boundary (game
    code and the [nat * nat] tweak re-tagging cannot supply index/position
    range proofs): the EXACT chain address when BOTH the index
    ([i < chain_count]) and position ([pos < pos_bound]) are in range (the
    only indices/positions any chain fold ever reaches), and a dummy (the
    pk address) out of range.  A [Bool.bool_dec] guard, NOT a saturating
    clamp -- no index/position value is truncated; an unreachable
    out-of-range index just names a distinct unused address.  Every
    REACHABLE use is in range ([shrincs_wots_chain_adrs_totE]). *)
Definition shrincs_wots_chain_adrs_tot (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z)
    (i pos : nat) : adrs_sf :=
  match Bool.bool_dec (i < chain_count)%nat true with
  | left Hi =>
      match Bool.bool_dec (pos < pos_bound)%nat true with
      | left Hpos => shrincs_wots_chain_adrs t Htag Hidx i pos Hi Hpos
      | right _ => shrincs_wots_pk_adrs t Htag Hidx
      end
  | right _ => shrincs_wots_pk_adrs t Htag Hidx
  end.

Lemma shrincs_wots_chain_adrs_totE t Htag Hidx i pos
    (Hi : (i < chain_count)%nat) (Hpos : (pos < pos_bound)%nat) :
  shrincs_wots_chain_adrs_tot t Htag Hidx i pos
  = shrincs_wots_chain_adrs t Htag Hidx i pos Hi Hpos.
Proof.
rewrite /shrincs_wots_chain_adrs_tot.
case: (Bool.bool_dec (i < chain_count)%nat true) => [Hi'|n]; last by rewrite Hi in n.
case: (Bool.bool_dec (pos < pos_bound)%nat true) => [Hpos'|n]; last by rewrite Hpos in n.
exact: shrincs_wots_chain_adrs_pirr.
Qed.

(** TOTAL, clamp-free prf address: the EXACT prf address for an in-range
    chain index ([i < chain_count], the only indices game code ever
    reaches), and a dummy (the pk address) out of range.  A [Bool.bool_dec]
    guard, NOT a clamp; every reachable index is in range. *)
Definition shrincs_wots_prf_adrs (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z)
    (i : nat) : adrs_sf :=
  match Bool.bool_dec (i < chain_count)%nat true with
  | left Hi => address.shrincs_wots_prf_adrs (anchor_adrs t Htag Hidx) (chain_fin i Hi)
  | right _ => shrincs_wots_pk_adrs t Htag Hidx
  end.

(* ------------------------------------------------------------------ *)
(** ** The per-hash-call tweaks (encoded chain / prf addresses) *)

(** The per-hash-call chain tweak is the encoded TOTAL chain address, so
    it is a plain function of the [nat * nat] index with no range proof
    (game code passes bare indices); it decodes back to the same total
    address unconditionally, and is index-injective on in-range indices. *)
Definition chain_tweak (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z)
    (i pos : nat) : adrs_sf_ch :=
  encode_adrs (shrincs_wots_chain_adrs_tot t Htag Hidx i pos).

Definition prf_tweak (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z)
    (i : nat) : adrs_sf_ch :=
  encode_adrs (shrincs_wots_prf_adrs t Htag Hidx i).

Lemma decode_adrs_chain_tweak t Htag Hidx i pos :
  decode_adrs (chain_tweak t Htag Hidx i pos) = shrincs_wots_chain_adrs_tot t Htag Hidx i pos.
Proof. by rewrite /chain_tweak /decode_adrs /encode_adrs otf_fto. Qed.

Lemma decode_adrs_prf_tweak t Htag Hidx i :
  decode_adrs (prf_tweak t Htag Hidx i) = shrincs_wots_prf_adrs t Htag Hidx i.
Proof. by rewrite /prf_tweak /decode_adrs /encode_adrs otf_fto. Qed.

(** The chain field of a chain address, as a [Z], recovered by the flat
    [payload_b_z] projection ([Z.of_nat i], the exact index -- no clamp). *)
Lemma chain_adrs_chainZ t Htag Hidx i pos Hi Hpos :
  address.payload_b_z (shrincs_wots_chain_adrs t Htag Hidx i pos Hi Hpos) = Z.of_nat i.
Proof. by rewrite /shrincs_wots_chain_adrs /chain_fin /=. Qed.

Lemma chain_adrs_posZ t Htag Hidx i pos Hi Hpos :
  address.payload_c_z (shrincs_wots_chain_adrs t Htag Hidx i pos Hi Hpos) = Z.of_nat pos.
Proof. by rewrite /shrincs_wots_chain_adrs /=. Qed.

Lemma prf_adrs_chainZ t Htag Hidx i (Hi : (i < chain_count)%nat) :
  address.payload_b_z (shrincs_wots_prf_adrs t Htag Hidx i) = Z.of_nat i.
Proof.
rewrite /shrincs_wots_prf_adrs.
case: (Bool.bool_dec (i < chain_count)%nat true) => [Hi'|n]; last by rewrite Hi in n.
by rewrite /chain_fin /=.
Qed.

(** Conditional index-injectivity of the chain tweak: the tweak is the
    encoded TOTAL chain address, whose index/position fields are placed
    EXACTLY for in-range [(chain, position)] pairs (chain [< chain_count],
    position [< w.-1]) and a dummy out of range; so injectivity in the
    indices holds for in-range pairs, which is all the consumers need. *)
Lemma chain_tweak_inj t Htag Hidx i pos i' pos' :
  (i < chain_count)%nat -> (i' < chain_count)%nat ->
  (pos < pos_bound)%nat -> (pos' < pos_bound)%nat ->
  chain_tweak t Htag Hidx i pos = chain_tweak t Htag Hidx i' pos' -> i = i' /\ pos = pos'.
Proof.
move=> hi hi' hp hp' /encode_adrs_inj.
rewrite (shrincs_wots_chain_adrs_totE t Htag Hidx i pos hi hp)
        (shrincs_wots_chain_adrs_totE t Htag Hidx i' pos' hi' hp').
exact: shrincs_wots_chain_adrs_inj.
Qed.

Lemma prf_tweak_inj t Htag Hidx i i' :
  (i < chain_count)%nat -> (i' < chain_count)%nat ->
  prf_tweak t Htag Hidx i = prf_tweak t Htag Hidx i' -> i = i'.
Proof.
move=> hi hi' /encode_adrs_inj hEq.
move: (congr1 (@address.payload_b_z _ _) hEq).
rewrite /shrincs_wots_prf_adrs.
case: (Bool.bool_dec (i < chain_count)%nat true) => [Hi|n]; last by rewrite hi in n.
case: (Bool.bool_dec (i' < chain_count)%nat true) => [Hi'|n]; last by rewrite hi' in n.
rewrite /chain_fin /=.
by move=> /Nat2Z.inj.
Qed.

End WcTweak.
