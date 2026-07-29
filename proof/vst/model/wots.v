(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * wots.model.wots: the VST tree's model surface.

    The C-refinement proof is stated against [Model.shrincs] -- the
    definition-for-definition port of the normative Python spec
    (model/PORTING.md) -- and the per-chain views above it in
    [Model.theory.shrincs] section 5 ([wc_chain], [derive_sk],
    [digest_of], [find_counter], [chain_tips] / [sign_chains] /
    [complete_ends], [wc_verify]).  This file is what every
    [From Vst Require Import model.wots.] line in the tree resolves to.

    IMPORT DISCIPLINE (load-bearing).  [Model.shrincs] is reached
    QUALIFIED ([shrincs.wots_c_pubkey_gen], [shrincs.T_sf], ...) and is
    deliberately NOT re-exported unqualified: the port defines [len] as
    Python's [len] builtin (a byte string's LENGTH, at [Z]), which would
    silently shadow this tree's [len = 32] chain count and make every
    [address.adrs len w_pred] mention resolve to something else.  The
    same applies to [index], [concat], [repeat] and [zeros].  Export
    only what is collision-free; qualify the rest.

    What IS exported unqualified: [Model.address] (the dependent ADRS
    the C mutates in place -- it survives the port, which addresses at
    the byte level), its theory, [Model.sha256]'s [block], and
    [Model.theory.shrincs]'s own names (collision-free by construction:
    section 5 was written to sit ABOVE the port, not inside it).

    [PRF]'s argument order is the spec's own, [pk_seed -> sk_seed ->
    ADRS] -- address LAST, unlike [F] / [T_sf] / [H_grind]. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Export address sha256 iteration theory.address.
From Model Require Export theory.shrincs.
From Model Require shrincs.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The WOTS+C row of the parametric ADRS.

    [Model.address.adrs] is parameterized by a chain count and a
    position bound; WOTS+C instantiates it at [len] / [w_pred].  The
    port carries those as [Z] constants under the spec's own names, so
    each [nat] here is pinned to its port counterpart by a lemma rather
    than restated as a bare numeral. *)

Definition n      : nat := 16.
Definition len    : nat := 32.
Definition w_pred : nat := 15.

Lemma len_port    : Z.of_nat len = shrincs.WOTS_C_CHAIN_COUNT.
Proof. reflexivity. Qed.

Lemma w_pred_port : Z.of_nat w_pred = 2 ^ shrincs.WOTS_C_CHAIN_BITS - 1.
Proof. reflexivity. Qed.

Lemma n_port      : Z.of_nat (len * n) = shrincs.WOTS_C_CHAINS_SIZE.
Proof. reflexivity. Qed.

(** Positivity of the instantiated position bound -- discharges the
    [0 < pos_bound] side condition of [shrincs_wots_hash_adrs]. *)
Lemma w_pred_pos : (0 < w_pred)%nat.
Proof. unfold w_pred; lia. Qed.

(** [i < len] gives the chain-index field bound. *)
Lemma chain_idx_lt (i : nat) (Hi : (i < len)%nat) : Z.of_nat i < Z.of_nat len.
Proof. lia. Qed.

(* ================================================================= *)
(** ** Grinding and wire-format constants. *)

(** The grinding counter is a 16-bit field, so the search runs over
    [0 .. c_max - 1].  The port takes the same span from the spec's own
    [range(2**16)] and never abbreviates it, so the name lives here --
    at the C boundary that does need it. *)
Definition c_max : Z := 2 ^ 16.

Definition constant_sum : Z := 240.

Definition pk_bytes  : Z := Z.of_nat n.               (* 16 = single T_sf hash *)
Definition sig_bytes : Z := 2 + Z.of_nat (len * n).   (* 514 = 2-byte counter ++ chains *)

Lemma constant_sum_port : constant_sum = shrincs.WOTS_C_CONSTANT_SUM.
Proof. reflexivity. Qed.

Lemma sig_bytes_port : sig_bytes = 2 + shrincs.WOTS_C_CHAINS_SIZE.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** [block] at WOTS+C's width.

    [Model.sha256.block] and the port's [bytes] are both [list byte] --
    definitionally the same type -- so a port function's result drops
    straight into a [block_to_vals] with no conversion. *)

Definition zero_block : block := List.repeat zero_byte n.
#[global] Instance default_block : Default block := zero_block.

(* ================================================================= *)
(** ** The anchor a WOTS+C address is read at.

    Every section-5 view is parameterized by the two ANCHOR fields the
    WOTS+C algorithms never touch (the 1-byte tag and the 8-byte index);
    the C carries the whole 22-byte ADRS.  These two projections are the
    dictionary, and [adrs_bytes_mk_adrs] (section 4) is what turns a
    [data_at]'s [adrs_bytes a] into the [mk_adrs] normal form section 5
    is stated at. *)

Notation anchor_nh a := (adrs_anchor_tag_z a).
Notation anchor_ni a := (adrs_anchor_idx_z a).
