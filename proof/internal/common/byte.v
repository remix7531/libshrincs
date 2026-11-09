(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.byte: [byte], the model's flat scalar type.

    [byte] is the 8-bit modular integer [model.machine.Byte.int] -- our
    CompCert-shaped, CompCert-free, axiom-free [Make(WORDSIZE)] clone --
    exposed here under the model's own byte API: [byte_val] (the [Z]
    projection, also a [byte >-> Z] coercion), [byte_of]/[byte_mod256]
    (the in-range and total-modular constructors, both
    [machine.Byte.repr]), [zero_byte], and the range / equality facts
    every byte-string proof uses.

    Keeping these names on the model side (rather than calling
    [machine.Byte.unsigned]/[machine.Byte.repr] at every use site) is
    deliberate: the VST refinement tree imports CompCert, whose own
    [Byte] module would otherwise collide -- the model's [byte_val] /
    [byte_mod256] names carry no [Byte.] prefix, so there is nothing to
    disambiguate. *)

From Stdlib Require Import ZArith Lia.
(** [Require] (not [Export]/[Import]): [machine.Byte] is reached only
    through its qualified name here, so it never enters downstream
    scope -- crucial for the VST tree, whose CompCert [Byte] would
    otherwise be shadowed. *)
From Model Require machine.
#[local] Open Scope Z_scope.

(* ================================================================= *)
(** ** [byte]: the 8-bit modular integer, i.e. a [Z] in [[0, 256)]. *)

Definition byte : Type := machine.Byte.int.

Definition byte_val (b : byte) : Z := machine.Byte.unsigned b.
Coercion byte_val : byte >-> Z.

(** [machine.Byte]'s modulus [2 ^ 8] computes to [256]. *)
Lemma byte_modulus : machine.Byte.modulus = 256.
Proof. reflexivity. Qed.

Lemma byte_val_range (x : byte) : 0 <= byte_val x < 256.
Proof. apply machine.Byte.unsigned_range. Qed.

(** Equality is by [Z] value ([machine.Byte.unsigned_inj], axiom-free). *)
Lemma byte_eq (x y : byte) : byte_val x = byte_val y -> x = y.
Proof. exact (machine.Byte.unsigned_inj x y). Qed.

Definition byte_eq_dec : forall x y : byte, {x = y} + {x <> y} := machine.Byte.eq_dec.

Lemma byte_of_range (v : Z) : 0 <= v < 256 -> -1 < v < machine.Byte.modulus.
Proof. rewrite byte_modulus. lia. Qed.

(** Build a [byte] from an in-range [Z], preserving the value exactly:
    [byte_val (byte_of v _) = v] holds definitionally (via
    [machine.Byte.mkint], not [repr]) -- unlike [byte_mod256], which
    genuinely truncates. *)
Definition byte_of (v : Z) (pf : 0 <= v < 256) : byte :=
  machine.Byte.mkint v (byte_of_range v pf).

Lemma byte_val_of (v : Z) (pf : 0 <= v < 256) : byte_val (byte_of v pf) = v.
Proof. reflexivity. Qed.

(** [x mod 256] as a [byte] (total; [machine.Byte.repr] already reduces
    mod [256]) -- what [model.address]'s [to_byte] needs. *)
Definition byte_mod256 (x : Z) : byte := machine.Byte.repr x.

Definition zero_byte : byte := byte_of 0 ltac:(lia).

(** [byte_mod256] agrees with [byte_of] on an already-in-range value
    (both are [machine.Byte.repr], regardless of the range proof). *)
Lemma byte_mod256_small (x : Z) (Hx : 0 <= x < 256) : byte_mod256 x = byte_of x Hx.
Proof.
  apply byte_eq. rewrite byte_val_of.
  unfold byte_val, byte_mod256.
  rewrite machine.Byte.unsigned_repr_eq, byte_modulus.
  apply Z.mod_small; exact Hx.
Qed.
