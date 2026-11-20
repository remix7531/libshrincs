(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.spec: the WOTS+C and stateful FXMSS reference

    A transcription of impl/shrincs.py from shrincs-bip, commit
    4fe68e3a68fd58be6b0e19436ff6fb7a3357a291.

    WOTS+C preserves the reference names, parameter order and loop
    structure. The stateful tree functions preserve their reference
    argument order; decreasing byte heights bound recursion. The
    [shrincs_sf_keygen], [shrincs_sf_sign] and [shrincs_sf_verify] functions
    project the corresponding [shrincs_*] reference functions onto the
    stateful path. Key generation takes the partner root as input, and
    signing and verification omit the stateless fallback. The envelope
    helpers factor expressions from those functions.

    How the Python is rendered:

    - [UInt8] to [UInt64] are the machine words [u8] to [u64], [Bytes n] is [n.-tuple u8], and a Python [bytes] of no fixed length is [seq u8]. [Optional] is [option].
    - A [UIntN] that is only stored or serialised is a word. Loop counters, chain positions and base-2^b digits, which the Python counts with, are [nat]. [uint] converts one where it enters an address or a byte string.
    - [for i in range(n): out[i] = e] is [[tuple of [seq e | i <- iota 0 n]]], a loop that updates one variable is a [foldl], and the grinding loop that returns on its first hit is [for_first].
    - [x[a : a + n]] is [slice x a n].
    - For the new stateful functions, failed assertions, input-domain
      checks and out-of-range recursive coordinates return [None] (or
      [false] in verification). Thus [option] also totalizes reference-domain
      rejection; it does not always correspond to a Python [Optional]
      annotation. [hmac_sha256_total] is the unchecked computation used by
      the PRF game; reference callers use [hmac_sha256] and enforce its domain.

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

Definition FXMSS_HEIGHT : nat := 255.

(*  Derived constants  *)
Definition WOTS_C_CHAIN_COUNT : nat := ceildiv 128 WOTS_C_CHAIN_BITS.
Definition WOTS_C_CHAINS_SIZE : nat := WOTS_C_CHAIN_COUNT * 16.
Definition WOTS_C_CONSTANT_SUM : nat :=
  ceildiv (WOTS_C_CHAIN_COUNT * (2 ^ WOTS_C_CHAIN_BITS - 1)) 2.

Definition FXMSS_SIGNATURE_SIZE_MIN : nat := 2 + WOTS_C_CHAINS_SIZE + 16.
Definition FXMSS_SIGNATURE_SIZE_MAX : nat := 2 + WOTS_C_CHAINS_SIZE + 16 * FXMSS_HEIGHT.
Definition SHRINCS_SF_SIGNATURE_SIZE_MIN : nat := 1 + 16 + 1 + FXMSS_SIGNATURE_SIZE_MIN.
Definition SHRINCS_SF_SIGNATURE_SIZE_MAX : nat := 1 + 16 + 8 + FXMSS_SIGNATURE_SIZE_MAX.

Definition FXMSS_SHAPE_UNBALANCED : UInt8 := uint U8 0.
Definition FXMSS_SHAPE_BALANCED : UInt8 := uint U8 1.

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

(*  FXMSS algorithms  *)

(* Fuel bounds decreasing byte heights. Check the leaf case
   before the Python assertions; check child coordinates before word conversion. *)
Fixpoint fxmss_node_at (fuel : nat) (sk_seed : Bytes 16) (node_index : UInt64)
    (node_height : UInt8) (pk_seed : Bytes 16) (tree_balanced : bool)
    (tree_depth : UInt8) : option (Bytes 16) :=
  if fuel is fuel'.+1 then
    let height := Z.to_nat (wunsigned node_height) in
    let node_depth := FXMSS_HEIGHT - height in
    if (node_depth == Z.to_nat (wunsigned tree_depth)) ||
       (~~ tree_balanced && (node_index == uint U64 1)) then
      Some (wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth)
    else if (if tree_balanced then node_depth < Z.to_nat (wunsigned tree_depth)
             else node_index == uint U64 0) then
      let lchild_index := Z.mul 2 (wunsigned node_index) in
      if (0 < height) && Z.ltb (Z.add lchild_index 1) (Z.pow 2 64) then
        let child_height := uint U8 (height - 1) in
        if fxmss_node_at fuel' sk_seed (wrepr U64 lchild_index) child_height
             pk_seed tree_balanced tree_depth is Some lchild then
          if fxmss_node_at fuel' sk_seed (wrepr U64 (Z.add lchild_index 1)) child_height
               pk_seed tree_balanced tree_depth is Some rchild then
            Some (H pk_seed (FxmssTree node_height node_index) [tuple of lchild ++ rchild])
          else None
        else None
      else None
    else None
  else None.

Definition fxmss_node (sk_seed : Bytes 16) (node_index : UInt64) (node_height : UInt8)
    (pk_seed : Bytes 16) (tree_balanced : bool) (tree_depth : UInt8) : option (Bytes 16) :=
  fxmss_node_at (Z.to_nat (wunsigned node_height)).+1
    sk_seed node_index node_height pk_seed tree_balanced tree_depth.

(* Authentication siblings are appended bottom-up. *)
Definition fxmss_sign (message_digest : Bytes 32) (sk_seed : Bytes 16)
    (leaf_index : UInt64) (leaf_height : UInt8) (pk_seed : Bytes 16)
    (tree_balanced : bool) (tree_depth : UInt8) : option (seq UInt8) :=
  let height := Z.to_nat (wunsigned leaf_height) in
  let leaf_depth := FXMSS_HEIGHT - height in
  if (if tree_balanced then leaf_depth == Z.to_nat (wunsigned tree_depth)
      else (leaf_index == uint U64 1) || (leaf_depth == Z.to_nat (wunsigned tree_depth))) then
    if wots_c_sign message_digest sk_seed pk_seed leaf_height leaf_index
         tree_balanced tree_depth is Some sig then
      foldl (fun sig j =>
        if sig is Some sig then
          let sibling_index := Z.lxor (Z.div (wunsigned leaf_index) (Z.pow 2 (Z.of_nat j))) 1 in
          let sibling_height := height + j in
          if Z.ltb sibling_index (Z.pow 2 64) && (sibling_height < 256) then
            if fxmss_node sk_seed (wrepr U64 sibling_index) (uint U8 sibling_height)
                 pk_seed tree_balanced tree_depth is Some sibling then
              Some (sig ++ sibling)
            else None
          else None
        else None) (Some (tval sig)) (range 0 leaf_depth)
    else None
  else None.

(* The exact length check precedes every padded slice. *)
Definition fxmss_pubkey_from_sig (leaf_index : UInt64) (leaf_height : UInt8)
    (signature : seq UInt8) (message_digest : Bytes 32) (pk_seed : Bytes 16)
    : option (Bytes 16) :=
  let height := Z.to_nat (wunsigned leaf_height) in
  let leaf_depth := FXMSS_HEIGHT - height in
  if (size signature == 2 + WOTS_C_CHAINS_SIZE + leaf_depth * 16) &&
     Z.ltb (wunsigned leaf_index) (Z.pow 2 (Z.of_nat (minn 64 leaf_depth))) then
    let wots_sig := slice signature 0 (2 + WOTS_C_CHAINS_SIZE) in
    let xmss_auth := drop (2 + WOTS_C_CHAINS_SIZE) signature in
    if wots_c_pubkey_from_sig wots_sig message_digest pk_seed leaf_height leaf_index
      is Some node then
      Some (foldl (fun (node : Bytes 16) k =>
        let parent := FxmssTree (uint U8 (height + k + 1))
          (wrepr U64 (Z.div (wunsigned leaf_index) (Z.pow 2 (Z.of_nat (k + 1))))) in
        let sibling := slice xmss_auth (k * 16) 16 in
        if Z.eqb (Z.modulo (Z.div (wunsigned leaf_index) (Z.pow 2 (Z.of_nat k))) 2) 1 then
          H pk_seed parent [tuple of sibling ++ node]
        else H pk_seed parent [tuple of node ++ sibling]) node (range 0 leaf_depth))
    else None
  else None.

(*  SHRINCS stateful path  *)

(* Stateful projection: the stateless root is supplied as
   partner. This does not implement the stateless root computation. *)
Definition shrincs_sf_keygen (seed : Bytes 48) (sf_structure : Bytes 2)
    (partner : Bytes 16) : option (Bytes 82 * Bytes 48) :=
  let tree_shape := nth (uint U8 0) sf_structure 0 in
  if (tree_shape == FXMSS_SHAPE_UNBALANCED) || (tree_shape == FXMSS_SHAPE_BALANCED) then
    let sk_seed := slice seed 0 16 in
    let sk_prf := slice seed 16 16 in
    let pk_seed := slice seed 32 16 in
    let sl_root := partner in
    let tree_balanced := tree_shape == FXMSS_SHAPE_BALANCED in
    if fxmss_node sk_seed (uint U64 0) (uint U8 FXMSS_HEIGHT) pk_seed
         tree_balanced (nth (uint U8 0) sf_structure 1) is Some sf_root then
      Some ([tuple of sk_seed ++ sk_prf ++ pk_seed ++ sl_root ++ sf_structure ++ sf_root],
            [tuple of pk_seed ++ sl_root ++ sf_root])
    else None
  else None.

Definition shrincs_extract_pubkey (shrincs_seckey : Bytes 82) : Bytes 48 :=
  [tuple of slice shrincs_seckey 32 32 ++ slice shrincs_seckey 66 16].

(* The result retains Python's (index, height) order. *)
Definition shrincs_sf_leaf_select (sf_structure : Bytes 2) (state_ctr : option UInt64)
    : option (UInt64 * UInt8) :=
  if state_ctr is Some state_ctr then
    let tree_shape := nth (uint U8 0) sf_structure 0 in
    let tree_depth := Z.to_nat (wunsigned (nth (uint U8 0) sf_structure 1)) in
    if tree_depth == 0 then None
    else if tree_shape == FXMSS_SHAPE_UNBALANCED then
      if Z.eqb (wunsigned state_ctr) (Z.of_nat tree_depth) then
        Some (uint U64 0, uint U8 (FXMSS_HEIGHT - tree_depth))
      else if Z.ltb (wunsigned state_ctr) (Z.of_nat tree_depth) then
        Some (uint U64 1, uint U8 (FXMSS_HEIGHT - 1 - Z.to_nat (wunsigned state_ctr)))
      else None
    else if tree_shape == FXMSS_SHAPE_BALANCED then
      if Z.ltb (wunsigned state_ctr) (Z.pow 2 (Z.of_nat tree_depth)) then
        Some (state_ctr, uint U8 (FXMSS_HEIGHT - tree_depth))
      else None
    else None
  else None.

(* Validate variable-length inputs before byte conversion
   and before the SHA/HMAC preimages are formed. *)
Definition shrincs_sf_message_domain (message ctx : seq UInt8) : bool :=
  Z.leb (Z.of_nat (size message)) (Z.sub (Z.pow 2 61) 384) && (size ctx <= 255).

(* Callers check shrincs_sf_message_domain first. *)
Definition shrincs_sf_bound_message (message ctx : seq UInt8) (sl_root : Bytes 16)
    : seq UInt8 :=
  int_to_bytes (uint U8 0) 1 ++ int_to_bytes (uint U8 (size ctx)) 1 ++ ctx ++ sl_root ++ message.

Definition shrincs_sf_index_size (leaf_height : UInt8) : nat :=
  ceildiv (minn (FXMSS_HEIGHT - Z.to_nat (wunsigned leaf_height)) 64) 8.

Definition shrincs_sf_signature_size (leaf_height : UInt8) : nat :=
  17 + shrincs_sf_index_size leaf_height + 2 + WOTS_C_CHAINS_SIZE
    + (FXMSS_HEIGHT - Z.to_nat (wunsigned leaf_height)) * 16.

(* Check the integer-to-bytes domain before serialization. *)
Definition shrincs_sf_encode (leaf_height : UInt8) (R : Bytes 16) (leaf_index : UInt64)
    (fxmss_signature : seq UInt8) : option (seq UInt8) :=
  let leaf_index_size := shrincs_sf_index_size leaf_height in
  if Z.ltb (wunsigned leaf_index) (Z.pow 2 (Z.of_nat (8 * leaf_index_size))) then
    Some (int_to_bytes leaf_height 1 ++ R ++ int_to_bytes leaf_index leaf_index_size ++ fxmss_signature)
  else None.

(* Stateful projection: unavailable leaves return None.
   The experiment in schemes.v supplies persistent state consumption. *)
Definition shrincs_sf_sign (message ctx : seq UInt8) (shrincs_seckey : Bytes 82)
    (state_ctr : option UInt64) : option (seq UInt8) :=
  if shrincs_sf_message_domain message ctx then
    let sk_seed := slice shrincs_seckey 0 16 in
    let sk_prf := slice shrincs_seckey 16 16 in
    let pk_seed := slice shrincs_seckey 32 16 in
    let sl_root := slice shrincs_seckey 48 16 in
    let sf_structure := slice shrincs_seckey 64 2 in
    let sf_root := slice shrincs_seckey 66 16 in
    if shrincs_sf_leaf_select sf_structure state_ctr is Some (leaf_index, leaf_height) then
      let bound_message := shrincs_sf_bound_message message ctx sl_root in
      if PRF_msg_sf sk_prf pk_seed leaf_height leaf_index bound_message is Some R then
        let message_digest := H_msg_sf R pk_seed sf_root leaf_height leaf_index bound_message in
        let tree_balanced := nth (uint U8 0) sf_structure 0 == FXMSS_SHAPE_BALANCED in
        if fxmss_sign message_digest sk_seed leaf_index leaf_height pk_seed tree_balanced
             (nth (uint U8 0) sf_structure 1) is Some fxmss_signature then
          shrincs_sf_encode leaf_height R leaf_index fxmss_signature
        else None
      else None
    else None
  else None.

(* Parsing refuses the stateless indicator, validates the
   full length, then reads fixed-width fields. No short input is zero-padded. *)
Definition shrincs_sf_parse (signature : seq UInt8)
    : option (UInt8 * Bytes 16 * UInt64 * seq UInt8) :=
  if signature is indicator :: _ then
    if indicator == uint U8 FXMSS_HEIGHT then None
    else if (SHRINCS_SF_SIGNATURE_SIZE_MIN <= size signature) &&
            (size signature <= SHRINCS_SF_SIGNATURE_SIZE_MAX) then
      let leaf_height := indicator in
      let leaf_depth := FXMSS_HEIGHT - Z.to_nat (wunsigned leaf_height) in
      let leaf_index_size := shrincs_sf_index_size leaf_height in
      if size signature == shrincs_sf_signature_size leaf_height then
        let R := slice signature 1 16 in
        let leaf_index := int_from_bytes U64 (slice signature 17 leaf_index_size) in
        if Z.ltb (wunsigned leaf_index) (Z.pow 2 (Z.of_nat (minn 64 leaf_depth))) then
          Some (leaf_height, R, leaf_index, drop (17 + leaf_index_size) signature)
        else None
      else None
    else None
  else None.

(* The fixed key tuple enforces the 48-byte public-key check;
   this projection rejects the stateless branch. *)
Definition shrincs_sf_verify (message signature ctx : seq UInt8) (shrincs_pubkey : Bytes 48)
    : bool :=
  if shrincs_sf_message_domain message ctx then
    let pk_seed := slice shrincs_pubkey 0 16 in
    let sl_root := slice shrincs_pubkey 16 16 in
    let sf_root := slice shrincs_pubkey 32 16 in
    if shrincs_sf_parse signature is Some (leaf_height, R, leaf_index, fxmss_signature) then
      let bound_message := shrincs_sf_bound_message message ctx sl_root in
      let message_digest := H_msg_sf R pk_seed sf_root leaf_height leaf_index bound_message in
      if fxmss_pubkey_from_sig leaf_index leaf_height fxmss_signature message_digest pk_seed
        is Some root then root == sf_root else false
    else false
  else false.
