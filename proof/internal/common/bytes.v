(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.common.bytes: word bounds for the C proofs

    The public SHA definition owns the big-endian codecs. These facts
    relate MathComp powers to the integer bounds used by CompCert. *)

From Shrincs Require Export sha256.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.
From Stdlib Require Zpower Znat.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope Z_scope.

Lemma expn_Nat_pow (a b : nat) : (a ^ b)%nat = Nat.pow a b.
Proof. by elim: b => //= b IH; rewrite expnS IH multE. Qed.

Lemma wbaseE (ws : wsize) : wbase ws = Z.of_nat (2 ^ wbits ws)%nat.
Proof.
rewrite /wbase /modulus Zpower.two_power_nat_equiv expn_Nat_pow
        Znat.Nat2Z.inj_pow //.
Qed.
