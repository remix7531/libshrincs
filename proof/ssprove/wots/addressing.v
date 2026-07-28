(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.addressing

    The WOTS+C-specific tweak layer over [Sec.addressing] -- THE address
    facade, which owns the twelve smart constructors, their range
    predicates and injectivity lemmas, the [Finite] instance and the
    exact tweak space.  Only WOTS+C's two per-hash-call tweaks live
    here, so a second scheme imports the facade alone.

    ** No range proof crosses this boundary

    The facade places every [nat] component EXACT-OR-ZERO
    ([Sec.addressing.fin_of_nat_or_zero]), so a chain / prf address is a
    plain function of the anchor and the bare [nat] index -- game code
    and the [nat * nat] tweak hand over indices with no bound in scope
    and no builder threads a range proof.  Nothing has to stay
    definitionally transparent for two rebuilds of the same address (the
    fold step vs the decoded tweak) to be equal: they are the same term.

    Index-injectivity ([chain_tweak_inj], [prf_tweak_inj]) is therefore
    stated exactly where it holds and is needed -- on in-range indices
    and positions ([< chain_count] / [< w.-1]), the only ones any chain
    fold reaches.  An out-of-range component is represented by zero in
    the SAME address class: never truncated, never reached. *)

From Sec.lib Require Import prelude.
From Sec Require Import addressing.
From Model Require address.
From Model Require Import fin.
From Stdlib Require Import ZArith Lia.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ================================================================== *)
Section WcTweak.

(** The WOTS+C chain count and Winternitz parameter; [pos_bound := w.-1]
    is the chain-position field bound. *)
Context (chain_count w : nat).
Local Notation pos_bound := (w.-1).

Local Notation adrs_sf := (address.adrs chain_count pos_bound).

(** The facade's per-(chain_count, w) specializations, brought back into
    unqualified scope (the idiom every [Sec.wots.*] consumer of
    [Sec.addressing] already uses -- see e.g. [Sec.wots.scheme]). *)
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch chain_count w).
Local Notation encode_adrs := (addressing.encode_adrs chain_count w).
Local Notation decode_adrs := (addressing.decode_adrs chain_count w).
Local Notation encode_adrs_inj := (addressing.encode_adrs_inj chain_count w).

(* ------------------------------------------------------------------ *)
(** ** The per-hash-call tweaks (encoded chain / prf addresses) *)

(** ADRS^h at chain [i], position [pos], encoded (type 16). *)
Definition chain_tweak (t : nat * nat) (i pos : nat) : adrs_sf_ch :=
  encode_adrs (addressing.wc_hash_adrs t i pos).

(** ADRS^prf of chain [i], encoded (type 21). *)
Definition prf_tweak (t : nat * nat) (i : nat) : adrs_sf_ch :=
  encode_adrs (addressing.wc_prf_adrs t i).

Lemma decode_adrs_chain_tweak t i pos :
  decode_adrs (chain_tweak t i pos) = addressing.wc_hash_adrs t i pos.
Proof. exact: addressing.encode_adrsK. Qed.

Lemma decode_adrs_prf_tweak t i :
  decode_adrs (prf_tweak t i) = addressing.wc_prf_adrs t i.
Proof. exact: addressing.encode_adrsK. Qed.

(** Index/position injectivity on in-range indices: the tweak is the
    encoded chain address, whose index and position are placed exactly
    there ([Sec.addressing.wc_hash_adrs_component_inj], which needs no
    hypothesis on the anchor -- it is the same [t] on both sides). *)
Lemma chain_tweak_inj t i pos i' pos' :
  (i < chain_count)%nat -> (i' < chain_count)%nat ->
  (pos < pos_bound)%nat -> (pos' < pos_bound)%nat ->
  chain_tweak t i pos = chain_tweak t i' pos' -> i = i' /\ pos = pos'.
Proof.
move=> hi hi' hp hp' /encode_adrs_inj hEq.
apply: (addressing.wc_hash_adrs_component_inj chain_count w t i pos i' pos') hEq;
  exact: component_bounded_lt.
Qed.

Lemma prf_tweak_inj t i i' :
  (i < chain_count)%nat -> (i' < chain_count)%nat ->
  prf_tweak t i = prf_tweak t i' -> i = i'.
Proof.
move=> hi hi' /encode_adrs_inj hEq.
apply: (addressing.wc_prf_adrs_component_inj chain_count w t i i') hEq;
  exact: component_bounded_lt.
Qed.

End WcTweak.
