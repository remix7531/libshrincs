(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * The shared half of the specification vector check

    test/spec/kat_to_v.awk turns every case of test/spec/vectors/wots_c.kat into one file that states [actual == expected] over the helpers below and closes it with [run]. The functions under test are Shrincs.spec's own, evaluated by the kernel's virtual machine. *)

From Stdlib Require Import BinInt.
From mathcomp Require Import boot algebra.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs Require Import spec.

(* A byte string of the vector file, as the fixed-length and the free-length type. *)
Definition free (bytes : seq nat) : seq (word U8) := [seq uint U8 b | b <- bytes].
Definition fixed (n : nat) (bytes : seq nat) : n.-tuple (word U8) := slice (free bytes) 0 n.

(* Results, back as the numbers the vector file prints. *)
Definition bytes_of (x : seq (word U8)) : seq nat := [seq Z.to_nat (wunsigned b) | b <- x].
Definition optional_bytes_of {n : nat} (x : option (n.-tuple (word U8))) : option (seq nat) :=
  omap (fun y : n.-tuple (word U8) => bytes_of y) x.
Definition grinded_of (r : word U16 * seq nat) : nat * seq nat := (Z.to_nat (wunsigned r.1), r.2).

(* [sha256] is locked, so the hash calls are exposed and unlocked before
   the virtual machine runs. The cast is checked once, at [Qed]. Signer
   refusal cases return before hashing and need no executable hash adapter. *)
Ltac run :=
  unfold shrincs_sf_verify, shrincs_sf_parse, fxmss_pubkey_from_sig, H_msg_sf, H,
    wots_c_pubkey_from_sig, wots_c_sign, wots_c_pubkey_gen, wots_c_map_digest,
    wots_c_grind_to_constant_sum, wots_c_chain_iter, PRF, H_grind, F, T_sf;
  rewrite ?sha256.unlock;
  vm_cast_no_check (erefl true).
