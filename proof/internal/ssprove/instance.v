(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.instance: encodings and static address classes

    The specification hash calls use one packed tweak and byte-message interface. These lemmas identify its grinding encoding and prove the injective node and chain-end encodings. At one node of one tree, the chain, compression and grinding tweaks satisfy their static address classes and the chain and PRF tweaks are injective over their bounded indexes. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games.
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
  shrincs_wots_chain_class (grinding_tweak t digest) = shrincs_wots_chain_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

Lemma grinding_tweak_pkcompress_class (t : tweak) (digest : Bytes 32) :
  shrincs_wots_pkcompress_class (grinding_tweak t digest) = shrincs_wots_pkcompress_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

Lemma grinding_tweak_grind_class (t : tweak) (digest : Bytes 32) :
  shrincs_wots_grind_class (grinding_tweak t digest) = shrincs_wots_grind_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

(*  Digits  *)

(* The digits of a grinding hash output, as wots_c_grind_to_constant_sum and wots_c_map_digest read them. *)
Definition spec_digits (g : bytes 16) : seq nat :=
  base_2b g WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT.

Lemma spec_digitsE (g : bytes 16) : spec_digits g = nibbles g.
Proof.
rewrite /spec_digits -[WOTS_C_CHAIN_COUNT]/(16.*2) -[X in X.*2](size_tuple g).
exact: base_2b_nibbles.
Qed.

Lemma size_spec_digits (g : bytes 16) : size (spec_digits g) = chain_count_shrincs.
Proof. by rewrite spec_digitsE size_nibbles size_tuple. Qed.

Lemma spec_digits_wf (g : bytes 16) : all (fun d => d < w_shrincs) (spec_digits g).
Proof. by rewrite spec_digitsE; exact: nibbles_lt. Qed.

Lemma spec_digits_inj : injective spec_digits.
Proof. by move=> g1 g2; rewrite !spec_digitsE => /nibbles_inj h; exact: val_inj. Qed.

Lemma wots_c_Hcc : 0 < chain_count_shrincs.
Proof. by []. Qed.

Lemma wots_c_Hw : 1 < w_shrincs.
Proof. by []. Qed.

Section AtTheAnchor.

Context (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8).

(*  The tweaks of one key  *)

Definition tw_chain (i pos : nat) : tweak :=
  tweak_of (WotsCHash node_height node_index (uint U32 i) (uint U32 pos)).

Definition tw_prf (i : nat) : tweak :=
  tweak_of (WotsCPrf node_height node_index tree_balanced tree_depth (uint U32 i)).

Definition tw_pk : tweak := tweak_of (WotsCPk node_height node_index).

Definition tw_grind : tweak := tweak_of (WotsCGrind node_height node_index).

Lemma tw_chain_class (i pos : nat) : shrincs_wots_chain_class (tw_chain i pos).
Proof. by []. Qed.

Lemma tw_chain_not_pkcompress_class (i pos : nat) :
  ~~ shrincs_wots_pkcompress_class (tw_chain i pos).
Proof. by []. Qed.

Lemma tw_pk_class : shrincs_wots_pkcompress_class tw_pk.
Proof. by []. Qed.

Lemma tw_grind_class : shrincs_wots_grind_class tw_grind.
Proof. by []. Qed.

Lemma tw_grind_not_chain_class : ~~ shrincs_wots_chain_class tw_grind.
Proof. by []. Qed.

Lemma tw_grind_not_pkcompress_class : ~~ shrincs_wots_pkcompress_class tw_grind.
Proof. by []. Qed.

Lemma tw_grind_encoded_not_chain_class (digest : Bytes 32) :
  ~~ shrincs_wots_chain_class (grinding_tweak tw_grind digest).
Proof. by rewrite grinding_tweak_chain_class tw_grind_not_chain_class. Qed.

Lemma tw_grind_encoded_class (digest : Bytes 32) :
  shrincs_wots_grind_class (grinding_tweak tw_grind digest).
Proof. by rewrite grinding_tweak_grind_class tw_grind_class. Qed.

Lemma tw_grind_encoded_not_pkcompress_class (digest : Bytes 32) :
  ~~ shrincs_wots_pkcompress_class (grinding_tweak tw_grind digest).
Proof. by rewrite grinding_tweak_pkcompress_class tw_grind_not_pkcompress_class. Qed.

(* A chain index and a chain position fit a 32 bit word, so distinct ones give distinct tweaks. *)
Lemma chain_index_lt (i : nat) : i < chain_count_shrincs -> i < 2 ^ 32.
Proof. exact: (@ltn_2_32 i 5 isT). Qed.

Lemma chain_position_lt (pos : nat) : pos < w_shrincs.-1 -> pos < 2 ^ 32.
Proof. by move=> hp; apply: (@ltn_2_32 pos 4 isT); exact: (ltn_trans hp). Qed.

Lemma tw_chain_inj (i pos i' pos' : nat) :
  i < chain_count_shrincs -> i' < chain_count_shrincs ->
  pos < w_shrincs.-1 -> pos' < w_shrincs.-1 ->
  tw_chain i pos = tw_chain i' pos' -> i = i' /\ pos = pos'.
Proof.
move=> hi hi' hp hp' h.
have hc : uint U32 i = uint U32 i' := congr1 (fun t : tweak => t.1.2) h.
have hh : uint U32 pos = uint U32 pos' := congr1 (fun t : tweak => t.2) h.
split.
- exact: (@uint32_inj i i' (chain_index_lt i hi) (chain_index_lt i' hi') hc).
- exact: (@uint32_inj pos pos' (chain_position_lt pos hp) (chain_position_lt pos' hp') hh).
Qed.

Lemma tw_prf_inj (i i' : nat) :
  i < chain_count_shrincs -> i' < chain_count_shrincs -> tw_prf i = tw_prf i' -> i = i'.
Proof.
move=> hi hi' h.
have hc : uint U32 i = uint U32 i' := congr1 (fun t : tweak => t.1.2) h.
exact: (@uint32_inj i i' (chain_index_lt i hi) (chain_index_lt i' hi') hc).
Qed.

End AtTheAnchor.
