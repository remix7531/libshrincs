(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.hash: the specification hashes as Th

    [tweak_of] gives the six tweak fields of an address. The lemmas after it show that the hash calls of Shrincs.spec are [Th] at that tweak, with the grinding input in its tweak and message encoding, and that this encoding keeps the target class. They hold for every address class and are shared by the schemes built on these hashes. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(*  Addresses as tweaks  *)

(* The six fields that Address.to_bytes hands to pack, per address class. *)
Definition tweak_of (ADRS : Address) : tweak :=
  match ADRS with
  | WotsCHash height index chain_index hash_index =>
      (height, index, SF_WOTS_C_HASH, uint U32 0, chain_index, hash_index)
  | WotsCPrf height index tree_balanced tree_depth chain_index =>
      (height, index, SF_WOTS_C_PRF,
       wrepr U32 (Z.add (Z.mul (Z.b2z tree_balanced) (Z.pow 2 24))
                        (Z.mul (wunsigned tree_depth) (Z.pow 2 16))),
       chain_index, uint U32 0)
  | WotsCPk height index =>
      (height, index, SF_WOTS_C_PK, uint U32 0, uint U32 0, uint U32 0)
  | WotsCGrind height index =>
      (height, index, SF_WOTS_C_GRIND, uint U32 0, uint U32 0, uint U32 0)
  | FxmssTree height index =>
      (height, index, SF_FXMSS_TREE, uint U32 0, uint U32 0, uint U32 0)
  end.

Lemma to_bytes_tweak_of (ADRS : Address) :
  to_bytes ADRS
  = (let: (height, index, address_type, word1, word2, word3) := tweak_of ADRS in
     Shrincs.spec.pack height index address_type word1 word2 word3).
Proof. by case: ADRS. Qed.

(* The specification hash calls use Th at the tweak of their address, with the grinding byte encoding proved below. *)
Lemma F_Th (pk_seed : Bytes 16) (ADRS : Address) (M_1 : Bytes 16) :
  F pk_seed ADRS M_1 = Th pk_seed (tweak_of ADRS) M_1.
Proof. by case: ADRS. Qed.

Lemma PRF_Th (pk_seed sk_seed : Bytes 16) (ADRS : Address) :
  PRF pk_seed sk_seed ADRS = Th pk_seed (tweak_of ADRS) sk_seed.
Proof. by case: ADRS. Qed.

Lemma T_sf_Th (pk_seed : Bytes 16) (ADRS : Address) (M_l : Bytes WOTS_C_CHAINS_SIZE) :
  T_sf pk_seed ADRS M_l = Th pk_seed (tweak_of ADRS) M_l.
Proof. by case: ADRS. Qed.

(* This literal packed form is used only to prove the byte encoding equation. *)
Definition Th_grind (pk_seed : Bytes 16) (t : tweak) (digest : Bytes 32) (counter : UInt16)
    : Bytes 16 :=
  let: (height, index, address_type, word1, word2, word3) := t in
  slice (sha256 (pk_seed ++ zeros 48 ++ slice (Shrincs.spec.pack height index address_type word1 word2 word3) 0 10
                 ++ digest ++ zeros 4 ++ int_to_bytes counter 2)) 0 16.

Lemma H_grind_Th_grind (pk_seed : Bytes 16) (ADRS : Address) (digest : Bytes 32)
    (counter : UInt16) :
  H_grind pk_seed ADRS digest counter = Th_grind pk_seed (tweak_of ADRS) digest counter.
Proof. by case: ADRS. Qed.

(* The address payload carries the first twelve digest bytes, so this Th input is exactly the grinding preimage of the specification. *)
Lemma grinding_encoding_Th (pk_seed : Bytes 16) (t : tweak)
    (digest : Bytes 32) (counter : UInt16) :
  Th_grind pk_seed t digest counter
  = Th pk_seed (grinding_tweak t digest) (grinding_message digest counter).
Proof.
case: t => [[[[[height index] address_type] word1] word2] word3].
rewrite /Th_grind /Th /grinding_tweak /grinding_message.
congr (slice (sha256 _) 0 16).
have hpack : tval (Shrincs.spec.pack height index address_type word1 word2 word3)
    = [tuple of int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1]
      ++ (int_to_bytes word1 4 ++ int_to_bytes word2 4 ++ int_to_bytes word3 4).
  by [].
have hprefix : slice (Shrincs.spec.pack height index address_type word1 word2 word3) 0 10
    = [tuple of int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1].
  by rewrite hpack slice_cat_head.
have hdigest :
    slice digest 0 4 ++ slice digest 4 4 ++ slice digest 8 4 ++ slice digest 12 20
    = tval digest.
  by rewrite -!slice_cat slice_all.
rewrite hprefix.
change ((pk_seed ++ zeros 48
         ++ (int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1)
         ++ digest ++ zeros 4 ++ int_to_bytes counter 2)
    = (pk_seed ++ zeros 48
         ++ (int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1
             ++ int_to_bytes (int_from_bytes U32 (slice digest 0 4)) 4
             ++ int_to_bytes (int_from_bytes U32 (slice digest 4 4)) 4
             ++ int_to_bytes (int_from_bytes U32 (slice digest 8 4)) 4)
         ++ (slice digest 12 20 ++ zeros 4 ++ int_to_bytes counter 2))).
rewrite !int_to_from_bytes_4 -hdigest.
by rewrite !catA.
Qed.

Lemma H_grind_encoding_Th (pk_seed : Bytes 16) (ADRS : Address)
    (digest : Bytes 32) (counter : UInt16) :
  H_grind pk_seed ADRS digest counter
  = Th pk_seed (grinding_tweak (tweak_of ADRS) digest) (grinding_message digest counter).
Proof. by rewrite H_grind_Th_grind grinding_encoding_Th. Qed.

Lemma grinding_tweak_chain_class (t : tweak) (digest : Bytes 32) :
  wots_c_hash_class (grinding_tweak t digest) = wots_c_hash_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

Lemma grinding_tweak_pkcompress_class (t : tweak) (digest : Bytes 32) :
  wots_c_pk_class (grinding_tweak t digest) = wots_c_pk_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

Lemma grinding_tweak_grind_class (t : tweak) (digest : Bytes 32) :
  wots_c_grind_class (grinding_tweak t digest) = wots_c_grind_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.
