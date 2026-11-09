(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.repr: scheme-neutral C-representation plumbing.

    The VST representation bridges shared by every SHRINCS scheme's
    contracts -- byte/block <-> [val] encoders, the 22-byte ADRS wire type,
    the width constants, and [CompSpecs] -- factored out of
    [contract.public] so the reusable tweakable-hash contract
    ([contract.helpers_thash]) and the coming FXMSS/stateless layers reach
    them WITHOUT importing the WOTS+C-specific funspecs.

    Residual coupling (deliberate, interim): [CompSpecs] is
    [make_compspecs clight.wots.prog], so this file still depends on the
    WOTS+C Clight program -- but NOT on any funspec. A fully scheme-neutral
    thash contract would need [src/thash.c]'s own clightgen'd program and
    its own [CompSpecs]; that is a separate, larger step.

    [CompSpecs] comes from [Vst.base]. The SHA-256 contract and its
    callers must elaborate [data_at] against the same instance. *)

From VST Require Export floyd.proofauto.
From Vst Require Export base.
From Vst Require Export model.wots contract.radrs.
From Vst.clight Require Export wots.
From Model Require Import theory.address.

Open Scope Z_scope.

Local Abbreviation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** C-level representation bridges. *)

(** A [block] (list of [Z]-bytes) as a list of VST [val]s. *)
Definition block_to_vals (b : block) : list val :=
  map (fun x : byte => Vubyte (Byte.repr x)) b.

Definition blocks_to_vals (bs : list block) : list val :=
  map (fun x : byte => Vubyte (Byte.repr x)) (concat bs).

(** A 22-byte ADRS as the [uint8_t[22]] the C expects. *)
Definition adrs_to_vals (a : adrs) : list val :=
  block_to_vals (adrs_bytes a).

Definition t_addr : type := tarray tuchar 22.

(** Byte-size constants.  [n_bytes] is the hash / seed / node / pk width
    ([= n = 16]); the message digest is a separate [msg_bytes = 32]. *)
Definition n_bytes   : Z := Z.of_nat n.        (* 16 *)
Definition seed_bytes : Z := Z.of_nat n.       (* 16 *)
Definition msg_bytes : Z := 32.

(** A [list nat] of base-16 digits as a list of VST byte [val]s. *)
Definition digits_to_vals (ds : list nat) : list val :=
  map (fun d : nat => Vubyte (Byte.repr (Z.of_nat d))) ds.

(* ================================================================= *)
(** ** [Inhabitant] instances for VST's [Znth] / [nth_Znth]. *)

#[export] Instance Inhabitant_byte  : Inhabitant byte  := zero_byte.
#[export] Instance Inhabitant_block : Inhabitant block := zero_block.
#[export] Instance Inhabitant_adrs  : Inhabitant adrs  :=
  Wc_pk (fin_of_Z 256 0 ltac:(lia)) (fin_of_Z (2 ^ 64) 0 ltac:(lia)).

(* ================================================================= *)
(** ** Scheme-neutral width equalities for [rep_lia]. *)

Lemma n_bytes_eq          : n_bytes          = 16.     Proof. reflexivity. Qed.
Lemma seed_bytes_eq       : seed_bytes       = 16.     Proof. reflexivity. Qed.
Lemma msg_bytes_eq        : msg_bytes        = 32.     Proof. reflexivity. Qed.
Lemma Byte_modulus_eq     : Byte.modulus     = 256.    Proof. reflexivity. Qed.
Lemma Byte_max_unsigned_eq: Byte.max_unsigned = 255.   Proof. reflexivity. Qed.
Lemma Int_max_unsigned_eq : Int.max_unsigned = 4294967295. Proof. reflexivity. Qed.

#[export] Hint Rewrite
  n_bytes_eq seed_bytes_eq msg_bytes_eq
  Byte_modulus_eq Byte_max_unsigned_eq Int_max_unsigned_eq
  : rep_lia.
