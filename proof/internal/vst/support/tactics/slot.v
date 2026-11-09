(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * tactics.slot: shared Ltac for [forward_call] slot-address matching
    and tuchar load typecheck side conditions.

    These custom tactics were factored out of [contract.lemmas.data_at];
    they depend on the [data_at] bridge lemmas ([Znth_block_to_vals]) and
    on the [digits_to_vals] encoding, so this module loads after
    [contract.lemmas.data_at]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.public.
From Shrincs.internal.vst.support Require Import contract.lemmas.data_at.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Slot-address tactic for [forward_call] parameter matching. *)
Ltac solve_slot_addr p HFC :=
  entailer!; simpl; f_equal; subst p;
  rewrite field_address0_offset;
  [ simpl; f_equal; lia
  | apply arr_field_compatible0; [ exact HFC | lia ] ].

Ltac finish_slot_addr p HFC :=
  subst p;
  rewrite field_address0_offset;
  [ simpl; f_equal; lia
  | apply arr_field_compatible0; [ exact HFC | lia ] ].

Ltac solve_slot_addr_pure p HFC :=
  apply prop_right;
  simpl;
  f_equal;
  autorewrite with norm;
  finish_slot_addr p HFC.

(** [split_sc] discharges the length side conditions of
    [split2_data_at_Tarray_app] in the common cases. *)
Ltac split_sc :=
  first
    [ list_solve
    | rewrite Zlength_Zrepeat; lia
    | rewrite Zlength_app, ?Zlength_Zrepeat; lia ].

(* ================================================================= *)
(** ** ADRS-buffer wire view and payload-word stores.

    Every body that writes the address buffer first switches the
    [data_at .. t_addr (adrs_to_vals a) ..] conjunct to its raw wire
    view (the C's under-construction six-[Z]-field byte layout) so the
    per-byte / per-word stores can be modelled, then re-gathers.  These
    tactics capture the two in-scope idioms; the full type-byte store
    macro [store_type_byte] ([open_adrs_wire; forward; rewrite
    zero_ext_byte; rewrite upd_adrs_type]) lives in [tactics.adrs_store]
    because [zero_ext_byte] is defined in [contract.lemmas.arith_counter],
    which loads after this module. *)

(** [open_adrs_wire] turns the [t_addr (adrs_to_vals a)] address conjunct
    into its raw wire view [tarray tuchar 22 (block_to_vals (radrs_bytes
    (adrs_to_raw a)))], ready for the byte-level type/word stores. *)
Ltac open_adrs_wire :=
  unfold t_addr;
  rewrite adrs_to_vals_raw.

(** [store_pk_words aptr sh X] runs the two [shrincs_adrs_put32] stores
    that PK-type a hash address -- zero the chain word (ADRS_CHAIN=14) and
    the hash word (ADRS_HASH=18) -- over the wire view of a type-17 address
    [X] at pointer [aptr] with share [sh], folding each store back to its
    [rset_payload_*] form.  Leaves the buffer holding [radrs_bytes
    (rset_payload_b (rset_type (adrs_to_raw X) 17) 0)] with the hash word
    zeroed; the caller then folds to [shrincs_wots_pk_adrs] via the
    [pkaddr_final_*] bridge (in [contract.lemmas.chain_blocks], out of scope
    here). *)
Ltac store_pk_words aptr sh X :=
  forward_call (aptr, 14, 0, radrs_bytes (rset_type (adrs_to_raw X) 17), sh);
  rewrite shrincs_adrs_put32_chain;
  forward_call (aptr, 18, 0,
                radrs_bytes (rset_payload_b (rset_type (adrs_to_raw X) 17) 0), sh);
  rewrite shrincs_adrs_put32_hash.

(** [close_tc_byte] closes the [tc_val tuchar ...] obligation left
    behind by [forward.] on a tuchar load over [block_to_vals]. *)
Ltac close_tc_byte :=
  entailer!;
  rewrite Znth_block_to_vals by lia;
  unfold Vubyte; simpl;
  match goal with
  | |- context [Byte.unsigned (Byte.repr ?X)] =>
      pose proof (Byte.unsigned_range (Byte.repr X))
  end;
  rewrite Int.unsigned_repr by rep_lia;
  rep_lia.

(** [close_tc_byte_cons] closes one side goal that [forward.] leaves on a
    tuchar load over an explicit head-cons list ([[c0; c1] ++ _], e.g. the
    reassembled 2-byte counter prefix), where the loaded cell is a concrete
    [Vubyte (Byte.repr X)].  Such a load leaves two entailments -- an index
    bound and a [tc_val] -- ahead of the continuation; [entailer!!] closes
    the bound outright and reduces the [tc_val] to a byte range, which the
    [Byte.unsigned_range] fact plus [rep_lia] then discharge.  Invoke as
    [all: try close_tc_byte_cons] after the [forward.] to clear both side
    goals in one shot, leaving the load's continuation. *)
Ltac close_tc_byte_cons :=
  entailer!!;
  try (match goal with
       | |- context [Byte.unsigned (Byte.repr ?X)] =>
           pose proof (Byte.unsigned_range (Byte.repr X))
       end;
       rep_lia).

(** Variant for [digits_to_vals _] loads (unfolds the [map] layer). *)
Ltac close_tc_byte_digit :=
  entailer!;
  unfold digits_to_vals;
  rewrite Znth_map by lia;
  unfold Vubyte; simpl;
  match goal with
  | |- context [Byte.unsigned (Byte.repr ?X)] =>
      pose proof (Byte.unsigned_range (Byte.repr X))
  end;
  rewrite Int.unsigned_repr by rep_lia;
  rep_lia.
