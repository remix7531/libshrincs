(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.spec: the WOTS+C slice of the SHRINCS reference

    A transcription of impl/shrincs.py from shrincs-bip, commit 4fe68e3a68fd58be6b0e19436ff6fb7a3357a291. Read it side by side with that file. Sections, names, parameter order and loop structure are the Python's. Only what WOTS+C uses is transcribed: the stateless path, FXMSS, HMAC and [xor] are left out.

    How the Python is rendered:

    - [UInt8] to [UInt64] are the machine words [u8] to [u64], [Bytes n] is [n.-tuple u8], and a Python [bytes] of no fixed length is [seq u8]. [Optional] is [option].
    - A [UIntN] that is only stored or serialised is a word. Loop counters, chain positions and base-2^b digits, which the Python counts with, are [nat]. [uint] converts one where it enters an address or a byte string.
    - [for i in range(n): out[i] = e] is [[tuple of [seq e | i <- iota 0 n]]], a loop that updates one variable is a [foldl], and the grinding loop that returns on its first hit is [for_first].
    - [x[a : a + n]] is [slice x a n].

    [sha256] is Shrincs.sha256's FIPS 180-4 transcription behind a lock, so nothing below can compute through it. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.
Require Shrincs.sha256.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Python built-ins  *)

Abbreviation UInt8 := (word U8) (only parsing).
Abbreviation UInt16 := (word U16) (only parsing).
Abbreviation UInt32 := (word U32) (only parsing).
Abbreviation UInt64 := (word U64) (only parsing).
Abbreviation Bytes n := (n.-tuple (word U8)) (only parsing).

Section Integers.
Local Open Scope Z_scope.

(* A Python int entering a UIntN position. It is exact below 2^N, and every use below stays under that. *)
Definition uint (ws : wsize) (x : nat) : word ws := wrepr ws (Z.of_nat x).

(* x.to_bytes(length), big-endian. *)
Definition int_to_bytes (ws : wsize) (x : word ws) (length : nat) : Bytes length :=
  [tuple of [seq wrepr U8 (wunsigned x / 256 ^ Z.of_nat (length - 1 - i)%nat) | i <- iota 0 length]].

(* int.from_bytes(x), big-endian. *)
Definition int_from_bytes (ws : wsize) (x : seq UInt8) : word ws :=
  wrepr ws (foldl (fun acc b => acc * 256 + wunsigned b) 0 x).

End Integers.

(* x[start : start + length] *)
Definition slice (x : seq UInt8) (start length : nat) : Bytes length :=
  [tuple of [seq nth (uint U8 0) x i | i <- iota start length]].

(* range(start, stop) *)
Definition range (start stop : nat) : seq nat := iota start (stop - start).

(* A while loop needs a bound in Rocq. The one use below runs at most [fuel] times. *)
Fixpoint while (S : Type) (fuel : nat) (cond : S -> bool) (body : S -> S) (s : S) : S :=
  if fuel is fuel'.+1 then if cond s then while fuel' cond body (body s) else s else s.

(* A for loop whose body returns on its first hit, and None if it runs out. *)
Fixpoint for_first (A B : Type) (f : A -> option B) (s : seq A) : option B :=
  if s is x :: s' then if f x is Some y then Some y else for_first f s' else None.

(*  Helper functions  *)

Definition ceildiv (a b : nat) : nat := (a + b - 1) %/ b.

Definition replicate (b : UInt8) (n : nat) : Bytes n := [tuple of nseq n b].

Definition zeros (n : nat) : Bytes n := replicate (uint U8 0) n.

(* mathcomp has no canonical tuple for [flatten], so [concat] carries the one size proof of this file. *)
Lemma concat_size (m n : nat) (array : m.-tuple (Bytes n)) :
  size (flatten [seq tval b | b <- array]) == m * n.
Proof.
rewrite size_flatten /shape -map_comp -[X in _ == X * n](size_tuple array).
by elim: (tval array) => //= b s /eqP ->; rewrite size_tuple mulSn.
Qed.

Definition concat (m n : nat) (array : m.-tuple (Bytes n)) : Bytes (m * n) :=
  Tuple (concat_size array).

(* Equal lengths are intrinsic to the two tuples. *)
Definition xor (n : nat) (s1 s2 : Bytes n) : Bytes n :=
  [tuple of [seq wxor (nth (uint U8 0) s1 i) (nth (uint U8 0) s2 i)
             | i <- iota 0 n]].

Definition base_2b (x : seq UInt8) (b outlen : nat) : seq nat :=
  let: (baseb, _, _, _) :=
    foldl (fun '(baseb, j, acc, bits_filled) i =>
        let: (j, acc, bits_filled) :=
          while b (fun '(_, _, bits_filled) => bits_filled < b)
            (fun '(j, acc, bits_filled) =>
               (j + 1, acc * 2 ^ 8 + Z.to_nat (wunsigned (nth (uint U8 0) x j)), bits_filled + 8))
            (j, acc, bits_filled) in
        let bits_filled := bits_filled - b in
        (set_nth 0 baseb i (acc %/ 2 ^ bits_filled), j, acc %% 2 ^ bits_filled, bits_filled))
      (nseq outlen 0, 0, 0, 0) (iota 0 outlen) in
  baseb.

(*  Parameters  *)
Definition WOTS_C_CHAIN_BITS : nat := 4.

(*  Derived constants  *)
Definition WOTS_C_CHAIN_COUNT : nat := ceildiv 128 WOTS_C_CHAIN_BITS.
Definition WOTS_C_CHAINS_SIZE : nat := WOTS_C_CHAIN_COUNT * 16.
Definition WOTS_C_CONSTANT_SUM : nat :=
  ceildiv (WOTS_C_CHAIN_COUNT * (2 ^ WOTS_C_CHAIN_BITS - 1)) 2.

(*  ADRS type flags  *)
Definition SF_WOTS_C_HASH : UInt8 := uint U8 16.
Definition SF_WOTS_C_PK : UInt8 := uint U8 17.
Definition SF_FXMSS_TREE : UInt8 := uint U8 18.
Definition SF_WOTS_C_PRF : UInt8 := uint U8 21.
Definition SF_WOTS_C_GRIND : UInt8 := uint U8 22.

(*  Addresses  *)

Section Addresses.
Local Open Scope Z_scope.

(* Address.pack, with the two fields of the base class as its first two arguments. *)
Definition pack (height : UInt8) (index : UInt64) (address_type : UInt8)
    (word1 word2 word3 : UInt32) : Bytes 22 :=
  [tuple of int_to_bytes height 1
         ++ int_to_bytes index 8
         ++ int_to_bytes address_type 1
         ++ int_to_bytes word1 4
         ++ int_to_bytes word2 4
         ++ int_to_bytes word3 4].

(* One constructor per address class, its fields in the order of the Python dataclass. *)
Inductive Address :=
  | WotsCHash (height : UInt8) (index : UInt64) (chain_index hash_index : UInt32)
  | WotsCPrf (height : UInt8) (index : UInt64) (tree_balanced : bool) (tree_depth : UInt8)
      (chain_index : UInt32)
  | WotsCPk (height : UInt8) (index : UInt64)
  | WotsCGrind (height : UInt8) (index : UInt64)
  | FxmssTree (height : UInt8) (index : UInt64).

Definition to_bytes (self : Address) : Bytes 22 :=
  match self with
  | WotsCHash height index chain_index hash_index =>
      pack height index SF_WOTS_C_HASH (uint U32 0) chain_index hash_index
  | WotsCPrf height index tree_balanced tree_depth chain_index =>
      pack height index SF_WOTS_C_PRF
        (wrepr U32 (Z.b2z tree_balanced * 2 ^ 24 + wunsigned tree_depth * 2 ^ 16))
        chain_index (uint U32 0)
  | WotsCPk height index =>
      pack height index SF_WOTS_C_PK (uint U32 0) (uint U32 0) (uint U32 0)
  | WotsCGrind height index =>
      pack height index SF_WOTS_C_GRIND (uint U32 0) (uint U32 0) (uint U32 0)
  | FxmssTree height index =>
      pack height index SF_FXMSS_TREE (uint U32 0) (uint U32 0) (uint U32 0)
  end.

End Addresses.

(*  Primitive cryptographic functions  *)

(* The Python bounds the message at 2^61 - 1 bytes. The type here does not, and the C contract restates the bound. *)
HB.lock Definition sha256 (message : seq UInt8) : Bytes 32 :=
  int_to_bytes (Shrincs.sha256.sha256 [seq wunsigned b | b <- message]) 32.

(* The HMAC computation, separated from its input
   domain check so the keyed-function experiment can use a total function. *)
Definition hmac_sha256_total (key message : seq UInt8) : Bytes 32 :=
  let padded_key := slice (key ++ zeros (64 - size key)) 0 64 in
  let inner := sha256 (xor padded_key (replicate (uint U8 54) 64) ++ message) in
  sha256 (xor padded_key (replicate (uint U8 92) 64) ++ inner).

(* The Python domain permits no long-key hashing branch. *)
Definition hmac_sha256 (key message : seq UInt8) : option (Bytes 32) :=
  if (size key <= 64) && Z.leb (Z.of_nat (size message)) (Z.sub (Z.pow 2 61) 65) then
    Some (hmac_sha256_total key message)
  else None.

Definition T_sf (pk_seed : Bytes 16) (ADRS : Address) (M_l : Bytes WOTS_C_CHAINS_SIZE)
    : Bytes 16 :=
  slice (sha256 (pk_seed ++ zeros 48 ++ to_bytes ADRS ++ M_l)) 0 16.

Definition F (pk_seed : Bytes 16) (ADRS : Address) (M_1 : Bytes 16) : Bytes 16 :=
  slice (sha256 (pk_seed ++ zeros 48 ++ to_bytes ADRS ++ M_1)) 0 16.

Definition H (pk_seed : Bytes 16) (ADRS : Address) (M_2 : Bytes 32) : Bytes 16 :=
  slice (sha256 (pk_seed ++ zeros 48 ++ to_bytes ADRS ++ M_2)) 0 16.

Definition H_grind (pk_seed : Bytes 16) (ADRS : Address) (digest : Bytes 32) (counter : UInt16)
    : Bytes 16 :=
  slice (sha256 (pk_seed ++ zeros 48 ++ slice (to_bytes ADRS) 0 10 ++ digest ++ zeros 4
                 ++ int_to_bytes counter 2)) 0 16.

Definition PRF (pk_seed sk_seed : Bytes 16) (ADRS : Address) : Bytes 16 :=
  slice (sha256 (pk_seed ++ zeros 48 ++ to_bytes ADRS ++ sk_seed)) 0 16.

(* As for sha256, the domain bound is checked by callers:
   the inner preimage has 57 bytes before M. *)
Definition H_msg_sf (R pk_seed sf_root : Bytes 16) (leaf_height : UInt8)
    (leaf_index : UInt64) (M : seq UInt8) : Bytes 32 :=
  let leaf := int_to_bytes leaf_height 1 ++ int_to_bytes leaf_index 8 in
  sha256 (R ++ pk_seed ++ sha256 (R ++ pk_seed ++ sf_root ++ leaf ++ M) ++ leaf).

Definition PRF_msg_sf (sk_prf pk_seed : Bytes 16) (leaf_height : UInt8)
    (leaf_index : UInt64) (M : seq UInt8) : option (Bytes 16) :=
  let leaf := int_to_bytes leaf_height 1 ++ int_to_bytes leaf_index 8 in
  if hmac_sha256 (sk_prf ++ replicate (uint U8 255) 48) (pk_seed ++ leaf ++ M)
    is Some digest then Some (slice digest 0 16) else None.

(*  WOTS+C algorithms  *)

Definition wots_c_chain_iter (node : Bytes 16) (start stop : nat) (pk_seed : Bytes 16)
    (node_height : UInt8) (node_index : UInt64) (chain_index : UInt32) : Bytes 16 :=
  foldl (fun node j => F pk_seed (WotsCHash node_height node_index chain_index (uint U32 j)) node)
    node (range start stop).

Definition wots_c_grind_to_constant_sum (pk_seed : Bytes 16) (message_digest : Bytes 32)
    (node_height : UInt8) (node_index : UInt64) : option (UInt16 * seq nat) :=
  let ADRS := WotsCGrind node_height node_index in
  for_first (fun i =>
      let hashed := H_grind pk_seed ADRS message_digest (uint U16 i) in
      let indexes := base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT in
      if sumn indexes == WOTS_C_CONSTANT_SUM then Some (uint U16 i, indexes) else None)
    (range 0 (2 ^ 16)).

Definition wots_c_map_digest (pk_seed : Bytes 16) (message_digest : Bytes 32)
    (node_height : UInt8) (node_index : UInt64) (counter : UInt16) : option (seq nat) :=
  let hashed := H_grind pk_seed (WotsCGrind node_height node_index) message_digest counter in
  let indexes := base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT in
  if sumn indexes == WOTS_C_CONSTANT_SUM then Some indexes else None.

Definition wots_c_pubkey_gen (sk_seed pk_seed : Bytes 16) (node_height : UInt8)
    (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8) : Bytes 16 :=
  let wots_pk := [tuple of [seq
      let sk := PRF pk_seed sk_seed
                  (WotsCPrf node_height node_index tree_balanced tree_depth (uint U32 i)) in
      wots_c_chain_iter sk 0 (2 ^ WOTS_C_CHAIN_BITS - 1) pk_seed node_height node_index (uint U32 i)
    | i <- iota 0 WOTS_C_CHAIN_COUNT]] in
  T_sf pk_seed (WotsCPk node_height node_index) (concat wots_pk).

Definition wots_c_sign (message_digest : Bytes 32) (sk_seed pk_seed : Bytes 16)
    (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8)
    : option (Bytes (2 + WOTS_C_CHAINS_SIZE)) :=
  if wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index
    is Some (counter, indexes) then
    let signature := [tuple of [seq
        let sk := PRF pk_seed sk_seed
                    (WotsCPrf node_height node_index tree_balanced tree_depth (uint U32 i)) in
        wots_c_chain_iter sk 0 (nth 0 indexes i) pk_seed node_height node_index (uint U32 i)
      | i <- iota 0 WOTS_C_CHAIN_COUNT]] in
    Some [tuple of int_to_bytes counter 2 ++ concat signature]
  else None.

Definition wots_c_pubkey_from_sig (signature : Bytes (2 + WOTS_C_CHAINS_SIZE))
    (message_digest : Bytes 32) (pk_seed : Bytes 16) (node_height : UInt8) (node_index : UInt64)
    : option (Bytes 16) :=
  let counter := int_from_bytes U16 (slice signature 0 2) in
  if wots_c_map_digest pk_seed message_digest node_height node_index counter is Some indexes then
    let wots_pk := [tuple of [seq
        wots_c_chain_iter (slice signature (2 + i * 16) 16) (nth 0 indexes i)
          (2 ^ WOTS_C_CHAIN_BITS - 1) pk_seed node_height node_index (uint U32 i)
      | i <- iota 0 WOTS_C_CHAIN_COUNT]] in
    Some (T_sf pk_seed (WotsCPk node_height node_index) (concat wots_pk))
  else None.
