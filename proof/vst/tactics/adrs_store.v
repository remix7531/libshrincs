(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * tactics.adrs_store: the ADRS type-byte store macro.

    [store_type_byte] runs the direct type-byte store
    [addr[ADRS_TYPE] = v] that every WOTS+C body performs before
    re-typing the address: open the wire view of the [t_addr] conjunct
    ([open_adrs_wire] from [tactics.slot]), [forward] the store, then
    fold the stored cell into [rset_type] on the raw view
    ([zero_ext_byte] + [upd_adrs_type]).  This lives in its own module
    (not in [tactics.slot]) because [zero_ext_byte] is defined in
    [contract.lemmas.arith_counter], which loads after [tactics.slot]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import tactics.slot.
From Vst Require Import contract.lemmas.data_at.
From Vst Require Import contract.lemmas.arith_counter.

(** [store_type_byte] leaves the address conjunct holding
    [block_to_vals (radrs_bytes (rset_type (adrs_to_raw a) v))]; the
    caller then folds it to the named model address (e.g.
    [set_type_byte_prf_hash], [grind_addr_stores], [pkaddr_final_eq]). *)
Ltac store_type_byte :=
  open_adrs_wire;
  forward;
  rewrite zero_ext_byte;
  rewrite upd_adrs_type.
