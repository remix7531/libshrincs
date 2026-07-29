(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Model.shrincs: the normative Python spec, ported to Gallina.

    A definition-for-definition port of the SHRINCS reference
    implementation (`shrincs-bip/impl/shrincs.py`, the normative spec).
    Same function names, same argument names, same order, same section
    structure; the docstrings are the spec's own docstrings.  Where the
    two differ, Gallina forced it -- the exhaustive list of forced
    differences, one row per Python construct, is
    proof/model/PORTING.md, and every one of them is visible here as a
    [fold_left] over a [range], a [_loop] helper recursing on the
    quantity the spec itself decrements, or a doc comment saying so.
    There are no fuel parameters and no invented budgets anywhere in
    this file.

    This file is DEFINITIONS ONLY, deliberately: no lemmas, no
    dependent types, no invariants in types.  It is a transcription, and
    a reviewer's job on it is to read it side by side with shrincs.py
    and see nothing new.  Everything one may CONCLUDE about it belongs
    in a theory file above it.

    ONE global convention is worth stating before the code, because it
    is the only place the port is not a literal transcription.  The
    spec's [ADRS] is a caller-owned [bytearray(22)] scratch buffer that
    every callee mutates IN PLACE; a ported function keeps the spec's
    signature, so a callee's mutations are not visible to its caller.
    That is sound throughout the spec because no [ADRS] field is ever
    read across a call boundary: every consumer writes each field it
    hashes before hashing it.  Sites where a caller does use [ADRS]
    after such a call carry a comment naming the fields; a loop that
    mutates [ADRS] carries it in its [fold_left] accumulator, so within
    a function the mutation is never lost (see [wots_c_pubkey_gen]).

    COMPLETE: all 50 of the spec's functions are here, in the spec's
    order, under the spec's own section headings.  Nothing is
    paraphrased and nothing is left out -- including
    [wots_tw_message_to_indexes_alt], which the spec carries only as an
    alternative formulation, and including the depth-0 bug in
    [shrincs_sf_leaf_select]. *)

From Stdlib Require Import Bool List ZArith Lia.
From Model Require Import bounded byte.
From Model Require sha256.

Import ListNotations.
#[local] Open Scope Z_scope.

(* ================================================================= *)
(** ** Python-to-Gallina plumbing.

    The only definitions in this file with no counterpart in
    shrincs.py: the byte-string reader/writer primitives Python gets
    from [bytes] / [bytearray] syntax, and the two builtins whose
    obvious Rocq spellings would shadow stdlib names.  Everything
    after this section mirrors the spec one definition at a time, in
    the spec's own order. *)

(** Python [bytes] and [bytearray] both port here.  [bytearray]'s
    in-place mutation becomes a functional update ([set_index] /
    [set_slice]) threaded through the definition by hand, so a
    mutation is visible to the statements after it and to nothing
    else. *)
Notation bytes := (list byte).

(** Python [x[i]] at a byte string: the byte's integer value.  Python
    raises [IndexError] out of range; this reads 0. *)
Definition index (x : bytes) (i : Z) : Z :=
  byte_val (nth (Z.to_nat i) x zero_byte).

(** Python [l[i]] at a list of ints (the [base_2b] index vectors).
    Same out-of-range convention as [index]. *)
Definition index_int (l : list Z) (i : Z) : Z := nth (Z.to_nat i) l 0.

(** Python [x[i:j]].  Out-of-range endpoints clip, as Python's own
    slicing does. *)
Definition slice (x : bytes) (i j : Z) : bytes :=
  firstn (Z.to_nat (j - i)) (skipn (Z.to_nat i) x).

(** Python [x[i:j] = v] on a [bytearray], at the equal lengths every
    slice assignment in the spec uses ([len v = j - i]).  The slice
    indices are the Python ones, unchanged. *)
Definition set_slice (x : bytes) (i j : Z) (v : bytes) : bytes :=
  firstn (Z.to_nat i) x ++ v ++ skipn (Z.to_nat j) x.

(** Python [x[i] = v] on a [bytearray]. *)
Definition set_index (x : bytes) (i : Z) (v : Z) : bytes :=
  set_slice x i (i + 1) [byte_mod256 v].

(** Python [x.to_bytes(n)]: the big-endian [n]-byte encoding of [x]
    (big-endian is [int.to_bytes]'s default byte order).  Python raises
    [OverflowError] when [x] does not fit in [n] bytes; this
    truncates. *)
Fixpoint to_bytes_loop (n : nat) (x : Z) : bytes :=
  match n with
  | O   => []
  | S n => to_bytes_loop n (x / 256) ++ [byte_mod256 x]
  end.

Definition to_bytes (x : Z) (n : Z) : bytes := to_bytes_loop (Z.to_nat n) x.

(** Python [int.from_bytes(x)]: big-endian, matching [to_bytes]. *)
Definition from_bytes (x : bytes) : Z :=
  fold_left (fun (acc : Z) (b : byte) => acc * 256 + b) x 0.

(** Python [x == y] at two byte strings. *)
Definition bytes_eqb (x y : bytes) : bool :=
  if list_eq_dec byte_eq_dec x y then true else false.

(** Python's [range(a, b)]: [a], [a+1], ..., [b-1], empty when
    [b <= a].  Python's one-argument [range(n)] is [range 0 n]. *)
Definition range (a b : Z) : list Z :=
  map (fun k => a + Z.of_nat k) (seq 0 (Z.to_nat (b - a))).

(** Python's [len] builtin at a byte string. *)
Definition len (x : bytes) : Z := Z.of_nat (length x).

(** Python's [sum] builtin at a list of ints.  Not named [sum]: that is
    Rocq's disjoint-union type former. *)
Definition sum_list (l : list Z) : Z := fold_right Z.add 0 l.

(* ================================================================= *)
(** ** Helper functions *)

Definition repeat (b : Z) (n : Z) : bytes :=
  List.repeat (byte_mod256 b) (Z.to_nat n).

Definition zeros (n : Z) : bytes := repeat 0 n.

Definition concat (array : list bytes) : bytes := List.concat array.

(** Returns the XOR of two arrays of bytes which must have equal
    length.

    [assert len(s1) == len(s2)] is a caller obligation: at unequal
    lengths [combine] (Python's [zip]) stops at the shorter, as Python
    does. *)
Definition xor (s1 s2 : bytes) : bytes :=
  map (fun '((b1, b2) : byte * byte) => byte_mod256 (Z.lxor b1 b2)) (combine s1 s2).

(** The [while bits_filled < b] loop inside [base_2b].  The quantity
    the loop decrements is [bytes_to_read = ceil((b - bits_filled) / 8)]:
    the loop runs while [bits_filled < b] and each iteration reads one
    byte, i.e. adds exactly 8 bits, so that is the loop's exact
    remaining trip count -- not a budget, the trip count itself.  The
    caller recomputes it from its own [bits_filled] on entry. *)
Fixpoint base_2b_fill (bytes_to_read : nat) (x : bytes) (b j acc bits_filled : Z)
  : Z * Z * Z :=
  match bytes_to_read with
  | O               => (j, acc, bits_filled)
  | S bytes_to_read =>
      if bits_filled <? b then
        base_2b_fill bytes_to_read x b (j + 1) (Z.shiftl acc 8 + index x j) (bits_filled + 8)
      else
        (j, acc, bits_filled)
  end.

(** Decomposes the bytes [x] into [outlen] groups of [b] bits which are
    each parsed as an integer in the range [[0, 2**b)].  The leading
    [outlen * b] bits of [x] are parsed, and so [x] must have
    accordingly sufficient length.

    The [for i in range(outlen)] loop is a fold over that range, whose
    accumulator is the spec's own loop-carried state: the output array
    [baseb] plus [j], [acc] and [bits_filled].

    [assert len(x) >= ceil(outlen * b / 8)] is a caller obligation: a
    short [x] reads as zero bytes rather than raising. *)
Definition base_2b (x : bytes) (b : Z) (outlen : Z) : list Z :=
  let '(baseb, j, acc, bits_filled) :=
    fold_left
      (fun '(baseb, j, acc, bits_filled) i =>
         let '(j, acc, bits_filled) :=
           base_2b_fill (Z.to_nat ((b - bits_filled + 7) / 8)) x b j acc bits_filled in
         let bits_filled := bits_filled - b in
         (baseb ++ [Z.shiftr acc bits_filled], j, acc mod 2 ^ bits_filled, bits_filled))
      (range 0 outlen)
      ([], 0, 0, 0) in
  baseb.

(* ================================================================= *)
(** ** Parameters *)

Definition WOTS_C_CHAIN_BITS    : Z := 4.
Definition WOTS_TW_CHAIN_BITS   : Z := 4.
Definition WOTS_C_CHAIN_COUNT   : Z := 32.
Definition WOTS_TW_CHAIN_COUNT1 : Z := 32.
Definition WOTS_TW_CHAIN_COUNT2 : Z := 3.
Definition WOTS_TW_CHAIN_COUNT  : Z := 35.
Definition SPHX_LAYER_COUNT     : Z := 5.
Definition SPHX_XMSS_HEIGHT     : Z := 9.
Definition SPHX_FORS_HEIGHT     : Z := 13.
Definition SPHX_FORS_COUNT      : Z := 10.
Definition FXMSS_HEIGHT         : Z := 255.

(** ** Derived constants

    [floor(a / b)] is [a / b] and [ceil(a / b)] is [(a + b - 1) / b]:
    [Z.div] rounds toward minus infinity, exactly as Python's [//]
    does, and the spec's [/] here is an exact-in-the-limit float
    division of nonnegative integers. *)

Definition WOTS_TW_CHAINS_SIZE      : Z := WOTS_TW_CHAIN_COUNT * 16.
Definition WOTS_TW_CHECKSUM_MAX     : Z := WOTS_TW_CHAIN_COUNT1 * (2 ^ WOTS_TW_CHAIN_BITS - 1).
Definition WOTS_C_CHAINS_SIZE       : Z := WOTS_C_CHAIN_COUNT * 16.
Definition WOTS_C_CONSTANT_SUM      : Z := WOTS_C_CHAIN_COUNT * (2 ^ WOTS_C_CHAIN_BITS - 1) / 2.
Definition SPHX_XMSS_SIGNATURE_SIZE : Z := WOTS_TW_CHAINS_SIZE + 16 * SPHX_XMSS_HEIGHT.
Definition HYPERTREE_SIGNATURE_SIZE : Z := SPHX_LAYER_COUNT * SPHX_XMSS_SIGNATURE_SIZE.
Definition FXMSS_SIGNATURE_SIZE_MIN : Z := 2 + WOTS_C_CHAINS_SIZE + 16.
Definition FXMSS_SIGNATURE_SIZE_MAX : Z := 2 + WOTS_C_CHAINS_SIZE + 16 * FXMSS_HEIGHT.
Definition FORS_DIGEST_SIZE         : Z := (SPHX_FORS_COUNT * SPHX_FORS_HEIGHT + 7) / 8.
Definition FORS_SIGNATURE_SIZE      : Z := 16 * SPHX_FORS_COUNT * (SPHX_FORS_HEIGHT + 1).
Definition SPHX_TREE_INDEX_BITS     : Z := SPHX_XMSS_HEIGHT * (SPHX_LAYER_COUNT - 1).
Definition SPHX_SIGNATURE_SIZE      : Z := 16 + FORS_SIGNATURE_SIZE + HYPERTREE_SIGNATURE_SIZE.

(** ** FXMSS structure types *)

Definition FXMSS_SHAPE_UNBALANCED : Z := 0.
Definition FXMSS_SHAPE_BALANCED   : Z := 1.

(** ** ADRS type flags *)

Definition SL_WOTS_TW_HASH : Z := 0.
Definition SL_WOTS_TW_PK   : Z := 1.
Definition SL_XMSS_TREE    : Z := 2.
Definition SL_FORS_TREE    : Z := 3.
Definition SL_FORS_ROOTS   : Z := 4.
Definition SL_WOTS_TW_PRF  : Z := 5.
Definition SL_FORS_PRF     : Z := 6.
Definition SF_WOTS_C_HASH  : Z := 16.
Definition SF_WOTS_C_PK    : Z := 17.
Definition SF_FXMSS_TREE   : Z := 18.
Definition SF_WOTS_C_PRF   : Z := 21.
Definition SF_WOTS_C_GRIND : Z := 22.

(* ================================================================= *)
(** ** Primitive cryptographic functions *)

(** The [sha256] hash function.

    - Inputs:
      - [message]: a message of at most [2**61 - 1] bytes.
    - Output:
      - a 32-byte hash.

    [hashlib.sha256] is [Model.sha256.SHA256], the repo's one trust
    anchor: a [Parameter] whose type already states both facts this
    docstring states (32-byte output, input of at most [2**61 - 1]
    bytes).  [BList.clip] injects a plain [bytes] into that input type;
    it never truncates anything a real SHRINCS call produces. *)
Definition sha256 (message : bytes) : bytes :=
  Vec.to_list
    (Model.sha256.SHA256
       (BList.clip Model.sha256.sha256_max_input_len
          ltac:(unfold Model.sha256.sha256_max_input_len; lia) message)).

(** The [hmac_sha256] keyed hash function.

    - Inputs:
      - [key]: a key of at most 64 bytes.
      - [message]: a message of at most [2**61 - 1 - 64] bytes.
    - Output:
      - a 32-byte hash.

    [assert len(key) <= 64] is a caller obligation: at a longer [key],
    [zeros (64 - len key)] is empty and [xor] stops at 64 bytes, where
    Python would raise. *)
Definition hmac_sha256 (key : bytes) (message : bytes) : bytes :=
  let padded_key := key ++ zeros (64 - len key) in
  let inner := sha256 (xor padded_key (repeat 0x36 64) ++ message) in
  sha256 (xor padded_key (repeat 0x5C 64) ++ inner).

(* ================================================================= *)
(** ** Tweaked hash functions *)

(** The [T_sl] tweaked hash function.  Compresses
    [WOTS_TW_CHAIN_COUNT] Winternitz chain tips into a single 16-byte
    hash.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [M_l]: a [WOTS_TW_CHAINS_SIZE]-byte concatenation of chain tips.
    - Output:
      - a 16-byte hash.

    This function is only used in the stateless path, and by both the
    signer and the verifier. *)
Definition T_sl (pk_seed : bytes) (ADRS : bytes) (M_l : bytes) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ M_l)) 0 16.

(** The [T_sf] tweaked hash function.  Compresses [WOTS_C_CHAIN_COUNT]
    Winternitz chain tips into a single 16-byte hash.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [M_l]: a [WOTS_C_CHAINS_SIZE]-byte concatenation of chain tips.
    - Output:
      - a 16-byte hash.

    This function is only used in the stateful path, and by both the
    signer and the verifier. *)
Definition T_sf (pk_seed : bytes) (ADRS : bytes) (M_l : bytes) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ M_l)) 0 16.

(** The [T_k] tweaked hash function.  Compresses [SPHX_FORS_COUNT]
    FORS tree roots into a single 16-byte hash.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [M_k]: a [SPHX_FORS_COUNT * 16]-byte concatenation of FORS tree
        roots.
    - Output:
      - a 16-byte hash.

    This function is only used in the stateless path, and by both the
    signer and the verifier. *)
Definition T_k (pk_seed : bytes) (ADRS : bytes) (M_k : bytes) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ M_k)) 0 16.

(** The [F] tweaked hash function.  Hashes a single 16-byte input, to
    generate and iterate Winternitz hash chains and to hash FORS
    leaves.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [M_1]: a 16-byte hash.
    - Output:
      - a 16-byte hash.

    This function is used in both stateful and stateless paths, and by
    both the signer and the verifier. *)
Definition F (pk_seed : bytes) (ADRS : bytes) (M_1 : bytes) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ M_1)) 0 16.

(** The [H] tweaked hash function.  Combines a pair of 16-byte Merkle
    child nodes into their 16-byte parent, building the Merkle trees in
    XMSS and FORS.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [M_2]: a 32-byte concatenation of two child node hashes.
    - Output:
      - a 16-byte hash.

    This function is used in both stateful and stateless paths, and by
    both the signer and the verifier. *)
Definition H (pk_seed : bytes) (ADRS : bytes) (M_2 : bytes) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ M_2)) 0 16.

(** The [H_grind] tweaked hash function.  Maps a 32-byte [digest] and
    grinding [counter] into the constant-sum message space for WOTS+C.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [digest]: a 32-byte digest.
      - [counter]: a 16-bit unsigned integer.
    - Output:
      - a 16-byte hash.

    This function is only used in the stateful path, and by both the
    signer and the verifier.

    [assert counter <= 0xFFFF] is a caller obligation: it is
    unreachable from the spec's own callers ([counter] is either a loop
    index below [2**16] or two bytes read off a signature), and a
    counter that did exceed it would be truncated by [to_bytes] here
    rather than raising. *)
Definition H_grind (pk_seed : bytes) (ADRS : bytes) (digest : bytes) (counter : Z) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ slice ADRS 0 10 ++ digest ++ zeros 4
                 ++ to_bytes counter 2)) 0 16.

(** The [PRF] pseudorandom function.  Derives a secret 16-byte preimage
    from [sk_seed], for signing and key generation.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [sk_seed]: a 16-byte secret.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash.

    This function is used in both stateful and stateless paths, but
    only by the signer. *)
Definition PRF (pk_seed : bytes) (sk_seed : bytes) (ADRS : bytes) : bytes :=
  slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ sk_seed)) 0 16.

(** The [H_msg_sl] message hash function.  Produces the 32-byte signing
    digest for the stateless path.

    - Inputs:
      - [R]: a 16-byte randomizer.
      - [pk_seed]: a 16-byte salt.
      - [sl_root]: the 16-byte stateless root hash.
      - [M]: a variable-length message.
    - Output:
      - a 32-byte hash.

    This function is only used in the stateless path, and by both the
    signer and the verifier.

    Note that [pk_seed] is not padded in this keyed hash function. *)
Definition H_msg_sl (R : bytes) (pk_seed : bytes) (sl_root : bytes) (M : bytes) : bytes :=
  sha256 (R ++ pk_seed ++ sha256 (R ++ pk_seed ++ sl_root ++ M) ++ zeros 4).

(** The [H_msg_sf] message hash function.  Produces the 32-byte signing
    digest for the stateful path.

    - Inputs:
      - [R]: a 16-byte randomizer.
      - [pk_seed]: a 16-byte salt.
      - [sf_root]: the 16-byte stateful root hash.
      - [ADRS]: a 22-byte address.
      - [M]: a variable-length message.
    - Output:
      - a 32-byte hash.

    This function is only used in the stateful path, and by both the
    signer and the verifier.

    Note that [pk_seed] is not padded in this tweakable hash
    function. *)
Definition H_msg_sf (R : bytes) (pk_seed : bytes) (sf_root : bytes)
                    (ADRS : bytes) (M : bytes) : bytes :=
  sha256 (R ++ pk_seed ++ slice ADRS 0 9
          ++ sha256 (R ++ pk_seed ++ sf_root ++ slice ADRS 0 9 ++ M)).

(** The [PRF_msg_sl] pseudorandom function.  Derives the per-message
    randomizer (salt) for the stateless path via HMAC-SHA256.

    - Inputs:
      - [sk_prf]: a 16-byte secret.
      - [opt_rand]: a 16-byte salt.
      - [M]: a variable-length message.
    - Output:
      - a 16-byte hash.

    This function is only used in the stateless path, and only by the
    signer.

    [opt_rand] is set to either [pk_seed] (giving the "deterministic
    variant" of SLH-DSA), or a 16-byte salt sampled from a secure RNG
    (the "hedged variant" of SLH-DSA, which increases resistance to
    side-channel attacks). *)
Definition PRF_msg_sl (sk_prf : bytes) (opt_rand : bytes) (M : bytes) : bytes :=
  slice (hmac_sha256 sk_prf (opt_rand ++ M)) 0 16.

(** The [PRF_msg_sf] function.  Derives the per-message randomizer
    (salt) for the stateful path via HMAC-SHA256.

    - Inputs:
      - [sk_prf]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [M]: a variable-length message.
    - Output:
      - a 16-byte hash.

    This function is only used in the stateful path, and only by the
    signer. *)
Definition PRF_msg_sf (sk_prf : bytes) (pk_seed : bytes) (ADRS : bytes) (M : bytes) : bytes :=
  slice (hmac_sha256 (sk_prf ++ repeat 0xFF 48) (pk_seed ++ slice ADRS 0 9 ++ M)) 0 16.

(* ================================================================= *)
(** ** Winternitz algorithms *)

(** The WOTS hash chain iteration function.  Iterates the hash chain
    from index [start] by [steps] steps, returning the node at index
    [start + steps].  The [ADRS] must be prefilled so the hashes are
    correctly tweaked.

    - Inputs:
      - [node]: a 16-byte hash.
      - [start]: a 32-bit unsigned integer, the index of [node] in its
        hash chain.
      - [steps]: a 32-bit unsigned integer, the number of steps to take
        up the chain; [start + steps] must not exceed [2**32].
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash at index [start + steps].

    This function is used in both stateful and stateless paths, and by
    both the signer and the verifier.

    The [for j in range(start, start + steps)] loop is a fold over that
    range, whose accumulator is the spec's own loop-carried state,
    [node] and [ADRS]. *)
Definition wots_chain_iter (node : bytes) (start : Z) (steps : Z)
                           (pk_seed : bytes) (ADRS : bytes) : bytes :=
  fst (fold_left
         (fun '(node, ADRS) j =>
            let ADRS := set_slice ADRS 18 22 (to_bytes j 4) in
            let node := F pk_seed ADRS node in
            (node, ADRS))
         (range start (start + steps))
         (node, ADRS)).

(** The WOTS-TW message map function.  Converts a 16-byte [message]
    into a checksummed array of [WOTS_TW_CHAIN_COUNT] chain indexes in
    [[0, 2**WOTS_TW_CHAIN_BITS)].

    - Inputs:
      - [message]: a 16-byte hash.
    - Output:
      - a checksummed array of [WOTS_TW_CHAIN_COUNT]
        [WOTS_TW_CHAIN_BITS]-bit unsigned integers.

    This function is only used in the stateless path, and by both the
    signer and the verifier.

    The spec fills [checksum_indexes] back to front
    ([checksum_indexes[COUNT2 - 1 - i]]), so the fold prepends. *)
Definition wots_tw_message_to_indexes (message : bytes) : list Z :=
  let msg_indexes := base_2b message WOTS_TW_CHAIN_BITS WOTS_TW_CHAIN_COUNT1 in
  let checksum := WOTS_TW_CHECKSUM_MAX - sum_list msg_indexes in
  let '(checksum_indexes, checksum) :=
    fold_left
      (fun '(checksum_indexes, checksum) i =>
         (checksum mod 2 ^ WOTS_TW_CHAIN_BITS :: checksum_indexes,
          Z.shiftr checksum WOTS_TW_CHAIN_BITS))
      (range 0 WOTS_TW_CHAIN_COUNT2)
      ([], checksum) in
  msg_indexes ++ checksum_indexes.

(** Alternative implementation, equivalent to
    [wots_tw_message_to_indexes] but using the more complex FIPS-205
    algorithm. *)
Definition wots_tw_message_to_indexes_alt (message : bytes) : list Z :=
  let SPHX_WOTS_CHECKSUM_SHIFT :=
    (8 - (WOTS_TW_CHAIN_BITS * WOTS_TW_CHAIN_COUNT2) mod 8) mod 8 in
  let SPHX_WOTS_CHECKSUM_BYTE_LEN :=
    (WOTS_TW_CHAIN_COUNT2 * WOTS_TW_CHAIN_BITS + 7) / 8 in
  let msg_indexes := base_2b message WOTS_TW_CHAIN_BITS WOTS_TW_CHAIN_COUNT1 in
  let checksum :=
    Z.shiftl (WOTS_TW_CHECKSUM_MAX - sum_list msg_indexes) SPHX_WOTS_CHECKSUM_SHIFT in
  let checksum_bytes := to_bytes checksum SPHX_WOTS_CHECKSUM_BYTE_LEN in
  let checksum_indexes :=
    base_2b checksum_bytes WOTS_TW_CHAIN_BITS WOTS_TW_CHAIN_COUNT2 in
  msg_indexes ++ checksum_indexes.

(** The WOTS-TW public key generation function.  Computes the 16-byte
    WOTS-TW public key at the keypair location prefilled in [ADRS].

    - Inputs:
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash representing the WOTS-TW public key.

    This function is only used in the stateless path, and only by the
    signer.

    [wots_chain_iter]'s write to [ADRS[18:22]] is dropped at its return
    (see the header): the next iteration and the post-loop
    [ADRS[14:22] = zeros(8)] both overwrite it. *)
Definition wots_tw_pubkey_gen (sk_seed : bytes) (pk_seed : bytes) (ADRS : bytes) : bytes :=
  let '(wots_pk, ADRS) :=
    fold_left
      (fun '(wots_pk, ADRS) i =>
         let ADRS := set_index ADRS 9 SL_WOTS_TW_PRF in
         let ADRS := set_slice ADRS 14 18 (to_bytes i 4) in   (* chain index *)
         let ADRS := set_slice ADRS 18 22 (zeros 4) in        (* zero hash index *)
         let sk := PRF pk_seed sk_seed ADRS in
         let ADRS := set_index ADRS 9 SL_WOTS_TW_HASH in
         (wots_pk ++ [wots_chain_iter sk 0 (2 ^ WOTS_TW_CHAIN_BITS - 1) pk_seed ADRS], ADRS))
      (range 0 WOTS_TW_CHAIN_COUNT)
      ([], ADRS) in
  let ADRS := set_index ADRS 9 SL_WOTS_TW_PK in
  let ADRS := set_slice ADRS 14 22 (zeros 8) in
  let wots_pk_hash := T_sl pk_seed ADRS (concat wots_pk) in
  wots_pk_hash.

(** The WOTS-TW signing function.  Produces a WOTS-TW signature on a
    16-byte [message], at the keypair location prefilled in [ADRS].

    - Inputs:
      - [message]: a 16-byte message to sign.
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a [WOTS_TW_CHAINS_SIZE]-byte signature.

    This function is only used in the stateless path, and only by the
    signer. *)
Definition wots_tw_sign (message : bytes) (sk_seed : bytes) (pk_seed : bytes)
                        (ADRS : bytes) : bytes :=
  let indexes := wots_tw_message_to_indexes message in
  let '(signature, ADRS) :=
    fold_left
      (fun '(signature, ADRS) i =>
         let ADRS := set_index ADRS 9 SL_WOTS_TW_PRF in
         let ADRS := set_slice ADRS 14 18 (to_bytes i 4) in   (* chain index *)
         let ADRS := set_slice ADRS 18 22 (zeros 4) in        (* zero hash index *)
         let sk := PRF pk_seed sk_seed ADRS in
         let ADRS := set_index ADRS 9 SL_WOTS_TW_HASH in
         (signature ++ [wots_chain_iter sk 0 (index_int indexes i) pk_seed ADRS], ADRS))
      (range 0 WOTS_TW_CHAIN_COUNT)
      ([], ADRS) in
  concat signature.

(** The WOTS-TW verification function.  Recovers a WOTS-TW public key
    from a [signature] on a 16-byte [message].

    - Inputs:
      - [signature]: a [WOTS_TW_CHAINS_SIZE]-byte signature.
      - [message]: a 16-byte message.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash representing the WOTS-TW public key.

    This function is only used in the stateless path, and by both the
    signer and the verifier.

    Unlike [wots_tw_sign]'s loop, this one never rewrites
    [ADRS[18:22]] itself, so [wots_chain_iter]'s dropped write there is
    load-bearing to check: no hash in the loop body reads [18:22]
    outside [wots_chain_iter] (which sets it before each of its own
    hashes), and the post-loop [ADRS[14:22] = zeros(8)] overwrites it
    before [T_sl]. *)
Definition wots_tw_pubkey_from_sig (signature : bytes) (message : bytes)
                                   (pk_seed : bytes) (ADRS : bytes) : bytes :=
  let indexes := wots_tw_message_to_indexes message in
  let ADRS := set_index ADRS 9 SL_WOTS_TW_HASH in
  let '(wots_pk, ADRS) :=
    fold_left
      (fun '(wots_pk, ADRS) i =>
         let ADRS := set_slice ADRS 14 18 (to_bytes i 4) in
         let steps := 2 ^ WOTS_TW_CHAIN_BITS - 1 - index_int indexes i in
         (wots_pk ++ [wots_chain_iter (slice signature (i * 16) ((i + 1) * 16))
                        (index_int indexes i) steps pk_seed ADRS], ADRS))
      (range 0 WOTS_TW_CHAIN_COUNT)
      ([], ADRS) in
  let ADRS := set_index ADRS 9 SL_WOTS_TW_PK in
  let ADRS := set_slice ADRS 14 22 (zeros 8) in
  let wots_pk_hash := T_sl pk_seed ADRS (concat wots_pk) in
  wots_pk_hash.

(** The [for i in range(2**16)] loop of
    [wots_c_grind_to_constant_sum].  It is not a fold: the spec returns
    out of the middle of it, and the point of the function is that it
    returns the FIRST hit.  It recurses instead on [remaining], the
    number of counters left in the spec's own [range(2**16)] span,
    which the loop decrements by one per counter tried; reaching [0] is
    the spec's [raise RuntimeError("Unreachable")]. *)
Fixpoint wots_c_grind_to_constant_sum_loop (remaining : nat) (i : Z)
                                           (pk_seed : bytes) (message_digest : bytes)
                                           (ADRS : bytes) : option (Z * list Z) :=
  match remaining with
  | O           => None
  | S remaining =>
      let hashed := H_grind pk_seed ADRS message_digest i in
      let indexes := base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT in
      if sum_list indexes =? WOTS_C_CONSTANT_SUM then
        Some (i, indexes)
      else
        wots_c_grind_to_constant_sum_loop remaining (i + 1) pk_seed message_digest ADRS
  end.

(** The WOTS+C grinding function.  Grinds up to 2^16 counters until one
    maps [message_digest] to a constant-sum index set, returning the
    lowest such counter and its index set.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [message_digest]: a 32-byte intermediate message digest (from
        [H_msg_sf]).
      - [ADRS]: a 22-byte address.
    - Outputs:
      - the smallest valid grinding [counter]: a 16-bit unsigned
        integer.
      - the constant-sum set of hash chain indexes it yields:
        [WOTS_C_CHAIN_COUNT] [WOTS_C_CHAIN_BITS]-bit unsigned integers.

    This function is only used in the stateful path, and only by the
    signer.

    [None] is the spec's [raise RuntimeError("Unreachable")] (all 2^16
    counters missed; practically impossible). *)
Definition wots_c_grind_to_constant_sum (pk_seed : bytes) (message_digest : bytes)
                                        (ADRS : bytes) : option (Z * list Z) :=
  let ADRS := set_index ADRS 9 SF_WOTS_C_GRIND in
  wots_c_grind_to_constant_sum_loop (Z.to_nat (2 ^ 16)) 0 pk_seed message_digest ADRS.


(** The WOTS+C digest validation function.  Evaluates a signature's
    grinding [counter] and returns the constant-sum index set it
    yields, or null if the counter is invalid.

    - Inputs:
      - [pk_seed]: a 16-byte salt.
      - [message_digest]: a 32-byte intermediate message digest (from
        [H_msg_sf]).
      - [ADRS]: a 22-byte address.
      - [counter]: a 16-bit unsigned integer.
    - Output:
      - a constant-sum set of hash chain indexes
        ([WOTS_C_CHAIN_COUNT] [WOTS_C_CHAIN_BITS]-bit unsigned
        integers), or null.

    This function is only used in the stateful path, and only by the
    verifier. *)
Definition wots_c_map_digest (pk_seed : bytes) (message_digest : bytes)
                             (ADRS : bytes) (counter : Z) : option (list Z) :=
  let ADRS := set_index ADRS 9 SF_WOTS_C_GRIND in
  let hashed := H_grind pk_seed ADRS message_digest counter in
  let indexes := base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT in
  if sum_list indexes =? WOTS_C_CONSTANT_SUM then
    Some indexes
  else
    None.

(** The WOTS+C public key generation function.  Computes the 16-byte
    WOTS+C public key at the keypair location prefilled in [ADRS].

    - Inputs:
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash representing the WOTS+C public key.

    This function is only used in the stateful path, and only by the
    signer.

    The [for i in range(WOTS_C_CHAIN_COUNT)] loop is a fold over that
    range; its accumulator is the output array [wots_pk] and [ADRS],
    which the three statements after the loop go on to use.
    [wots_chain_iter] also writes [ADRS[18:22]] and that write is
    dropped at its return (see the header): the next iteration and the
    post-loop [ADRS[14:22] = zeros(8)] both overwrite it. *)
Definition wots_c_pubkey_gen (sk_seed : bytes) (pk_seed : bytes) (ADRS : bytes) : bytes :=
  let ADRS := set_slice ADRS 10 14 (zeros 4) in            (* zeros reserved *)
  let '(wots_pk, ADRS) :=
    fold_left
      (fun '(wots_pk, ADRS) i =>
         let ADRS := set_index ADRS 9 SF_WOTS_C_PRF in
         let ADRS := set_slice ADRS 14 18 (to_bytes i 4) in   (* chain index *)
         let ADRS := set_slice ADRS 18 22 (zeros 4) in        (* zero hash index *)
         let sk := PRF pk_seed sk_seed ADRS in
         let ADRS := set_index ADRS 9 SF_WOTS_C_HASH in
         (wots_pk ++ [wots_chain_iter sk 0 (2 ^ WOTS_C_CHAIN_BITS - 1) pk_seed ADRS], ADRS))
      (range 0 WOTS_C_CHAIN_COUNT)
      ([], ADRS) in
  let ADRS := set_index ADRS 9 SF_WOTS_C_PK in
  let ADRS := set_slice ADRS 14 22 (zeros 8) in
  let wots_pk_hash := T_sf pk_seed ADRS (concat wots_pk) in
  wots_pk_hash.

(** The WOTS+C signing function.  Produces a WOTS+C signature on a
    32-byte [message_digest], at the keypair location prefilled in
    [ADRS].

    - Inputs:
      - [message_digest]: a 32-byte message digest to sign.
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a [2 + WOTS_C_CHAINS_SIZE]-byte signature.

    This function is only used in the stateful path, and only by the
    signer.

    The [None] arm is where the spec's
    [raise RuntimeError("Unreachable")] propagates out of
    [wots_c_grind_to_constant_sum]; it returns a signature-shaped zero
    block rather than changing this function's signature. *)
Definition wots_c_sign (message_digest : bytes) (sk_seed : bytes) (pk_seed : bytes)
                       (ADRS : bytes) : bytes :=
  match wots_c_grind_to_constant_sum pk_seed message_digest ADRS with
  | None => zeros (2 + WOTS_C_CHAINS_SIZE)
  | Some (counter, indexes) =>
      let ADRS := set_slice ADRS 10 14 (zeros 4) in            (* zeros reserved *)
      let '(signature, ADRS) :=
        fold_left
          (fun '(signature, ADRS) i =>
             let ADRS := set_index ADRS 9 SF_WOTS_C_PRF in
             let ADRS := set_slice ADRS 14 18 (to_bytes i 4) in   (* chain index *)
             let ADRS := set_slice ADRS 18 22 (zeros 4) in        (* zero hash index *)
             let sk := PRF pk_seed sk_seed ADRS in
             let ADRS := set_index ADRS 9 SF_WOTS_C_HASH in
             (signature ++ [wots_chain_iter sk 0 (index_int indexes i) pk_seed ADRS], ADRS))
          (range 0 WOTS_C_CHAIN_COUNT)
          ([], ADRS) in
      to_bytes counter 2 ++ concat signature
  end.

(** The WOTS+C verification function.  Recovers a WOTS+C public key
    from a [signature] on a 32-byte [message_digest].

    - Inputs:
      - [signature]: a [2 + WOTS_C_CHAINS_SIZE]-byte signature.
      - [message_digest]: a 32-byte message digest.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash representing the WOTS+C public key, or null.

    This function is only used in the stateful path, and only by the
    verifier.

    As in [wots_tw_pubkey_from_sig], the loop never rewrites
    [ADRS[18:22]] itself; [wots_chain_iter] sets it before each of its
    own hashes and the post-loop [ADRS[14:22] = zeros(8)] overwrites it
    before [T_sf]. *)
Definition wots_c_pubkey_from_sig (signature : bytes) (message_digest : bytes)
                                  (pk_seed : bytes) (ADRS : bytes) : option bytes :=
  let counter := from_bytes (slice signature 0 2) in
  let indexes := wots_c_map_digest pk_seed message_digest ADRS counter in

  (* Reject if counter doesn't satisfy the constant-sum requirement. *)
  match indexes with
  | None => None
  | Some indexes =>
      let ADRS := set_index ADRS 9 SF_WOTS_C_HASH in
      let ADRS := set_slice ADRS 10 14 (zeros 4) in            (* zeros reserved *)
      let '(wots_pk, ADRS) :=
        fold_left
          (fun '(wots_pk, ADRS) i =>
             let ADRS := set_slice ADRS 14 18 (to_bytes i 4) in
             let steps := 2 ^ WOTS_C_CHAIN_BITS - 1 - index_int indexes i in
             (wots_pk ++ [wots_chain_iter (slice signature (2 + i * 16) (2 + (i + 1) * 16))
                            (index_int indexes i) steps pk_seed ADRS], ADRS))
          (range 0 WOTS_C_CHAIN_COUNT)
          ([], ADRS) in
      let ADRS := set_index ADRS 9 SF_WOTS_C_PK in
      let ADRS := set_slice ADRS 14 22 (zeros 8) in
      let wots_pk_hash := T_sf pk_seed ADRS (concat wots_pk) in
      Some wots_pk_hash
  end.

(* ================================================================= *)
(** ** XMSS algorithms *)

(** [xmss_node]'s own recursion, structural on [node_height] -- the
    quantity the spec itself decrements
    ([child_height = node_height - 1]), and whose zero case is the
    spec's own base case.  [xmss_node] below converts once, on the way
    in. *)
Fixpoint xmss_node_loop (node_height : nat) (sk_seed : bytes) (node_index : Z)
                        (pk_seed : bytes) (ADRS : bytes) : bytes :=
  match node_height with
  | O =>
      (* Bottom layer: return the WOTS-TW pubkey hash. *)
      let ADRS := set_slice ADRS 10 14 (to_bytes node_index 4) in
      wots_tw_pubkey_gen sk_seed pk_seed ADRS
  | S child_height =>
      (* Recursively derive the left/right child nodes.  Their [ADRS]
         writes are dropped at the recursive return (see the header):
         the four statements below rewrite every byte of [ADRS[9:22]],
         and neither [xmss_node] nor anything it calls touches
         [ADRS[0:9]]. *)
      let lchild_index := 2 * node_index in
      let lchild := xmss_node_loop child_height sk_seed lchild_index pk_seed ADRS in
      let rchild := xmss_node_loop child_height sk_seed (lchild_index + 1) pk_seed ADRS in

      (* Compute and return the parent node. *)
      let ADRS := set_index ADRS 9 SL_XMSS_TREE in
      let ADRS := set_slice ADRS 10 14 (zeros 4) in
      let ADRS := set_slice ADRS 14 18 (to_bytes (Z.of_nat node_height) 4) in
      let ADRS := set_slice ADRS 18 22 (to_bytes node_index 4) in
      H pk_seed ADRS (lchild ++ rchild)
  end.

(** The XMSS internal node computation function.  Recursively computes
    the XMSS node at the given [node_index] and [node_height].  The
    [ADRS] must be prefilled with the location of the XMSS tree in the
    hypertree to ensure the hashes are properly tweaked.

    - Inputs:
      - [sk_seed]: a 16-byte secret.
      - [node_index]: a 32-bit unsigned integer, the index (from the
        left) of the node in the XMSS layer.
      - [node_height]: a 32-bit unsigned integer, the height (from the
        bottom) of the node in the XMSS layer.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte XMSS node hash.

    This function is only used in the stateless path, and only by the
    signer. *)
Definition xmss_node (sk_seed : bytes) (node_index : Z) (node_height : Z)
                     (pk_seed : bytes) (ADRS : bytes) : bytes :=
  xmss_node_loop (Z.to_nat node_height) sk_seed node_index pk_seed ADRS.

(** The XMSS signing function.  Produces a deterministic WOTS-TW
    signature at leaf [keypair_index] and appends the Merkle
    authentication path to form an XMSS signature.  The [ADRS] must be
    prefilled with the location of the XMSS tree in the hypertree to
    ensure the hashes are properly tweaked.

    - Inputs:
      - [message]: a 16-byte message to sign.
      - [sk_seed]: a 16-byte secret.
      - [keypair_index]: a 32-bit unsigned integer, the index of the
        WOTS-TW keypair to sign with.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a [SPHX_XMSS_SIGNATURE_SIZE]-byte signature.

    This function is only used in the stateless path, and only by the
    signer.

    [wots_tw_sign]'s and [xmss_node]'s writes to [ADRS[9:22]] are
    dropped at their returns (see the header); every [xmss_node] call
    rewrites all of [ADRS[9:22]] before it hashes, and [ADRS[10:14]] as
    set here is exactly what [xmss_node] overwrites at height 0. *)
Definition xmss_sign (message : bytes) (sk_seed : bytes) (keypair_index : Z)
                     (pk_seed : bytes) (ADRS : bytes) : bytes :=
  (* Sign the message with WOTS-TW. *)
  let ADRS := set_slice ADRS 10 14 (to_bytes keypair_index 4) in
  let sig := wots_tw_sign message sk_seed pk_seed ADRS in

  (* Append the Merkle authentication path. *)
  fold_left
    (fun sig j =>
       let sibling_index := Z.lxor (Z.shiftr keypair_index j) 1 in
       sig ++ xmss_node sk_seed sibling_index j pk_seed ADRS)
    (range 0 SPHX_XMSS_HEIGHT)
    sig.

(** The XMSS verification function.  Recovers an XMSS root from a
    [signature] on a 16-byte [message] at leaf [keypair_index].  The
    [ADRS] must be prefilled with the location of the XMSS tree in the
    hypertree to ensure the hashes are properly tweaked.

    - Inputs:
      - [keypair_index]: a 32-bit unsigned integer, the index of the
        WOTS-TW keypair to sign with.
      - [signature]: a [SPHX_XMSS_SIGNATURE_SIZE]-byte signature.
      - [message]: a 16-byte message.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte XMSS root node hash.

    This function is only used in the stateless path, and by both the
    signer and the verifier. *)
Definition xmss_pubkey_from_sig (keypair_index : Z) (signature : bytes) (message : bytes)
                                (pk_seed : bytes) (ADRS : bytes) : bytes :=
  let wots_sig := slice signature 0 WOTS_TW_CHAINS_SIZE in
  let xmss_auth := slice signature WOTS_TW_CHAINS_SIZE SPHX_XMSS_SIGNATURE_SIZE in

  let ADRS := set_slice ADRS 10 14 (to_bytes keypair_index 4) in  (* AKA keypair address *)
  let node := wots_tw_pubkey_from_sig wots_sig message pk_seed ADRS in

  let ADRS := set_index ADRS 9 SL_XMSS_TREE in
  let ADRS := set_slice ADRS 10 14 (zeros 4) in

  let '(node, ADRS) :=
    fold_left
      (fun '(node, ADRS) k =>
         let ADRS := set_slice ADRS 14 18 (to_bytes (k + 1) 4) in
         let ADRS := set_slice ADRS 18 22 (to_bytes (Z.shiftr keypair_index (k + 1)) 4) in
         let sibling := slice xmss_auth (k * 16) ((k + 1) * 16) in
         if Z.land (Z.shiftr keypair_index k) 1 =? 1 then
           (H pk_seed ADRS (sibling ++ node), ADRS)
         else
           (H pk_seed ADRS (node ++ sibling), ADRS))
      (range 0 SPHX_XMSS_HEIGHT)
      (node, ADRS) in
  node.

(* ================================================================= *)
(** ** Hypertree algorithms *)

(** The hypertree signing function.  Signs a 16-byte [message] through
    a hypertree of XMSS trees.

    - Inputs:
      - [message]: a 16-byte message to sign.
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [tree_index]: a 64-bit unsigned integer, the index (from the
        left) of the bottom-layer XMSS tree to sign with.
      - [leaf_index]: a 32-bit unsigned integer, the index (from the
        left) of the WOTS-TW key in the bottom-layer XMSS tree to sign
        with.
    - Output:
      - a [HYPERTREE_SIGNATURE_SIZE]-byte signature.

    This function is only used in the stateless path, and only by the
    signer.

    The spec reassigns its own [message], [leaf_index] and
    [tree_index] parameters inside the loop, so all three ride the
    fold's accumulator alongside [sig] and [ADRS].  Note
    [leaf_index] is recomputed from the OLD [tree_index], before the
    shift. *)
Definition hypertree_sign (message : bytes) (sk_seed : bytes) (pk_seed : bytes)
                          (tree_index : Z) (leaf_index : Z) : bytes :=
  let ADRS := zeros 22 in
  let '(sig, message, leaf_index, tree_index, ADRS) :=
    fold_left
      (fun '(sig, message, leaf_index, tree_index, ADRS) j =>
         let ADRS := set_index ADRS 0 j in
         let ADRS := set_slice ADRS 1 9 (to_bytes tree_index 8) in
         let layer_sig := xmss_sign message sk_seed leaf_index pk_seed ADRS in
         let '(message, leaf_index, tree_index) :=
           if j <? SPHX_LAYER_COUNT - 1 then
             (xmss_pubkey_from_sig leaf_index layer_sig message pk_seed ADRS,
              tree_index mod 2 ^ SPHX_XMSS_HEIGHT,
              Z.shiftr tree_index SPHX_XMSS_HEIGHT)
           else
             (message, leaf_index, tree_index) in
         (sig ++ layer_sig, message, leaf_index, tree_index, ADRS))
      (range 0 SPHX_LAYER_COUNT)
      ([], message, leaf_index, tree_index, ADRS) in
  sig.

(** The hypertree verification function.  Recovers the hypertree root
    from a [signature] and compares it against [sl_root].

    - Inputs:
      - [message]: a 16-byte message.
      - [signature]: a [HYPERTREE_SIGNATURE_SIZE]-byte signature.
      - [pk_seed]: a 16-byte salt.
      - [tree_index]: a 64-bit unsigned integer, the index (from the
        left) of the bottom-layer XMSS tree to sign with.
      - [leaf_index]: a 32-bit unsigned integer, the index (from the
        left) of the WOTS-TW key in the bottom-layer XMSS tree to sign
        with.
      - [sl_root]: the 16-byte root hash of the stateless root tree.
    - Output:
      - a boolean indicating if the signature is valid. *)
Definition hypertree_verify (message : bytes) (signature : bytes) (pk_seed : bytes)
                            (tree_index : Z) (leaf_index : Z) (sl_root : bytes) : bool :=
  let ADRS := zeros 22 in
  let '(message, leaf_index, tree_index, ADRS) :=
    fold_left
      (fun '(message, leaf_index, tree_index, ADRS) j =>
         let ADRS := set_index ADRS 0 j in
         let ADRS := set_slice ADRS 1 9 (to_bytes tree_index 8) in
         let layer_sig := slice signature (j * SPHX_XMSS_SIGNATURE_SIZE)
                            ((j + 1) * SPHX_XMSS_SIGNATURE_SIZE) in
         let message := xmss_pubkey_from_sig leaf_index layer_sig message pk_seed ADRS in
         let '(leaf_index, tree_index) :=
           if j <? SPHX_LAYER_COUNT - 1 then
             (tree_index mod 2 ^ SPHX_XMSS_HEIGHT,
              Z.shiftr tree_index SPHX_XMSS_HEIGHT)
           else
             (leaf_index, tree_index) in
         (message, leaf_index, tree_index, ADRS))
      (range 0 SPHX_LAYER_COUNT)
      (message, leaf_index, tree_index, ADRS) in
  bytes_eqb message sl_root.

(* ================================================================= *)
(** ** FXMSS algorithms *)

(** [fxmss_node]'s own recursion, structural on [node_height] -- the
    quantity the spec itself decrements by one per level
    ([child_height = node_height - 1]).  It is the same [node_height]
    the spec passes, at [nat] rather than [Z] because that is what
    makes the recursion structural; [fxmss_node] below converts once,
    on the way in. *)
Fixpoint fxmss_node_loop (node_height : nat) (sk_seed : bytes) (node_index : Z)
                         (pk_seed : bytes) (structure : bytes)
                         (ADRS : bytes) : bytes :=
  let node_depth := FXMSS_HEIGHT - Z.of_nat node_height in
  let tree_shape := index structure 0 in
  let tree_depth := index structure 1 in
  let is_uxmss_leaf :=
    (tree_shape =? FXMSS_SHAPE_UNBALANCED)
      && ((node_index =? 1) || (node_depth =? tree_depth)) in
  let is_bxmss_leaf :=
    (tree_shape =? FXMSS_SHAPE_BALANCED) && (node_depth =? tree_depth) in
  if is_uxmss_leaf || is_bxmss_leaf then
    let ADRS := set_index ADRS 0 (Z.of_nat node_height) in
    let ADRS := set_slice ADRS 1 9 (to_bytes node_index 8) in
    wots_c_pubkey_gen sk_seed pk_seed ADRS
  else
    (* Catch and throw if control would enter an infinite recursive loop. *)
    if (tree_shape =? FXMSS_SHAPE_UNBALANCED) && negb (node_index =? 0) then
      zeros 16
    else if (tree_shape =? FXMSS_SHAPE_BALANCED) && negb (node_depth <? tree_depth) then
      zeros 16
    else
      match node_height with
      (* [child_height] would be [-1]: this is exactly where the spec's
         recursion runs away, and where the two asserts above were
         meant to have stopped it. *)
      | O              => zeros 16
      | S child_height =>
          (* Recursively derive the left/right child nodes.  Their
             [ADRS] writes are dropped at the recursive return (see the
             header): the four statements below rewrite all 22 bytes. *)
          let lchild_index := 2 * node_index in
          let lchild :=
            fxmss_node_loop child_height sk_seed lchild_index pk_seed structure ADRS in
          let rchild :=
            fxmss_node_loop child_height sk_seed (lchild_index + 1) pk_seed structure ADRS in

          (* Compute and return the parent node. *)
          let ADRS := set_index ADRS 0 (Z.of_nat node_height) in
          let ADRS := set_slice ADRS 1 9 (to_bytes node_index 8) in
          let ADRS := set_index ADRS 9 SF_FXMSS_TREE in
          let ADRS := set_slice ADRS 10 22 (zeros 12) in
          H pk_seed ADRS (lchild ++ rchild)
      end.

(** The FXMSS internal node computation function.  Recursively computes
    the FXMSS node at the given [node_index] and [node_height] for the
    tree [structure].

    - Inputs:
      - [sk_seed]: a 16-byte secret.
      - [node_index]: a 64-bit unsigned integer, the index (from the
        left) of the node in the FXMSS layer.
      - [node_height]: an 8-bit unsigned integer, the height (from the
        bottom) of the node in the FXMSS tree.
      - [pk_seed]: a 16-byte salt.
      - [structure]: a 2-byte identifier describing the FXMSS tree
        structure.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte FXMSS node hash.

    This function is only used in the stateful path, and only by the
    signer.

    The spec's two [assert]s (UXMSS [node_index == 0], BXMSS
    [node_depth < tree_depth]) fire only on a [structure] the spec's
    own keygen would not produce; where Python raises, this returns
    [zeros 16]. *)
Definition fxmss_node (sk_seed : bytes) (node_index : Z) (node_height : Z)
                      (pk_seed : bytes) (structure : bytes) (ADRS : bytes) : bytes :=
  fxmss_node_loop (Z.to_nat node_height) sk_seed node_index pk_seed structure ADRS.

(** The FXMSS signing function.  Produces a deterministic WOTS+C
    signature at the leaf given by [leaf_index]/[leaf_height] and
    appends the Merkle authentication path to form an FXMSS signature.

    - Inputs:
      - [message_digest]: a 32-byte message digest.
      - [sk_seed]: a 16-byte secret.
      - [leaf_index]: a 64-bit unsigned integer, the index (from the
        left) of the signing leaf in the FXMSS layer.
      - [leaf_height]: an 8-bit unsigned integer, the height (from the
        bottom) of the signing leaf in the FXMSS tree.
      - [pk_seed]: a 16-byte salt.
      - [structure]: a 2-byte identifier describing the FXMSS tree
        structure.
    - Output:
      - a [2 + 16 * (WOTS_C_CHAIN_COUNT + FXMSS_HEIGHT - leaf_height)]-byte
        signature.

    This function is only used in the stateful path, and only by the
    signer.

    The spec's two leaf-position [assert]s fire only on a
    [(structure, leaf_index, leaf_height)] triple that
    [shrincs_sf_leaf_select] would not produce; where Python raises,
    this returns a signature-shaped zero block of the length the
    docstring states. *)
Definition fxmss_sign (message_digest : bytes) (sk_seed : bytes) (leaf_index : Z)
                      (leaf_height : Z) (pk_seed : bytes) (structure : bytes) : bytes :=
  let leaf_depth := FXMSS_HEIGHT - leaf_height in

  (* Validate the leaf is positioned correctly for the specified tree structure. *)
  let tree_shape := index structure 0 in
  let tree_depth := index structure 1 in
  if (tree_shape =? FXMSS_SHAPE_UNBALANCED)
       && negb ((leaf_index =? 1) || (leaf_depth =? tree_depth)) then
    zeros (2 + WOTS_C_CHAINS_SIZE + 16 * leaf_depth)
  else if (tree_shape =? FXMSS_SHAPE_BALANCED) && negb (leaf_depth =? tree_depth) then
    zeros (2 + WOTS_C_CHAINS_SIZE + 16 * leaf_depth)
  else
    let ADRS := zeros 22 in
    let ADRS := set_index ADRS 0 leaf_height in
    let ADRS := set_slice ADRS 1 9 (to_bytes leaf_index 8) in
    let sig := wots_c_sign message_digest sk_seed pk_seed ADRS in

    (* Append the Merkle authentication path. *)
    fold_left
      (fun sig j =>
         let sibling_index := Z.lxor (Z.shiftr leaf_index j) 1 in
         let sibling_height := leaf_height + j in
         sig ++ fxmss_node sk_seed sibling_index sibling_height pk_seed structure ADRS)
      (range 0 leaf_depth)
      sig.

(** The FXMSS verification function.  Recovers an FXMSS root from a
    [signature] on a 32-byte [message_digest].  The signature length
    implies the leaf depth; [leaf_index] gives its left-to-right
    position.

    - Inputs:
      - [leaf_index]: a 64-bit unsigned integer, the left-to-right
        position of the WOTS+C signing leaf.
      - [signature]: a variable-length signature of at least
        [FXMSS_SIGNATURE_SIZE_MIN] bytes and at most
        [FXMSS_SIGNATURE_SIZE_MAX] bytes, with length 2 more than a
        multiple of 16.
      - [message_digest]: a 32-byte message digest.
      - [pk_seed]: a 16-byte salt.
    - Output:
      - a 16-byte FXMSS root node hash, or null.

    This function is only used in the stateful path, and by the
    verifier.

    The spec's [assert leaf_index < 2 ** min(64, leaf_depth)] is a
    [None] here: the function is already [Optional].

    The loop's [ADRS[0] += 1] is the ONE place in the spec where a
    caller reads an [ADRS] byte after passing [ADRS] to a callee.  It
    is sound: [wots_c_pubkey_from_sig] writes [ADRS[9]], [ADRS[10:14]]
    and [ADRS[14:22]] and never [ADRS[0]], so the read sees the
    [leaf_height] set above, exactly as in Python.  See the
    drop-at-boundary appendix in proof/model/PORTING.md. *)
Definition fxmss_pubkey_from_sig (leaf_index : Z) (signature : bytes)
                                 (message_digest : bytes) (pk_seed : bytes) : option bytes :=
  let wots_sig := slice signature 0 (2 + WOTS_C_CHAINS_SIZE) in
  let xmss_auth := slice signature (2 + WOTS_C_CHAINS_SIZE) (len signature) in

  let leaf_depth := len xmss_auth / 16 in

  (* Ensure leaf_index describes a valid position in the FXMSS tree. *)
  if negb (leaf_index <? 2 ^ Z.min 64 leaf_depth) then
    None
  else
    let leaf_height := FXMSS_HEIGHT - leaf_depth in

    let ADRS := zeros 22 in
    let ADRS := set_index ADRS 0 leaf_height in
    let ADRS := set_slice ADRS 1 9 (to_bytes leaf_index 8) in
    match wots_c_pubkey_from_sig wots_sig message_digest pk_seed ADRS with
    | None => None
    | Some node =>
        let ADRS := set_index ADRS 9 SF_FXMSS_TREE in
        let ADRS := set_slice ADRS 10 22 (zeros 12) in

        let '(node, ADRS) :=
          fold_left
            (fun '(node, ADRS) k =>
               let ADRS := set_index ADRS 0 (index ADRS 0 + 1) in
               let ADRS := set_slice ADRS 1 9 (to_bytes (Z.shiftr leaf_index (k + 1)) 8) in
               let sibling := slice xmss_auth (k * 16) ((k + 1) * 16) in
               if Z.land (Z.shiftr leaf_index k) 1 =? 1 then
                 (H pk_seed ADRS (sibling ++ node), ADRS)
               else
                 (H pk_seed ADRS (node ++ sibling), ADRS))
            (range 0 leaf_depth)
            (node, ADRS) in
        Some node
    end.

(* ================================================================= *)
(** ** FORS algorithms *)

(** The FORS secret preimage generation function.  Generates the secret
    16-byte preimage of the FORS leaf at forest-wide index
    [node_index].  The [ADRS] must be prefilled with the location of
    the FORS keypair to ensure the hashes are properly tweaked.

    - Inputs:
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [node_index]: a 32-bit unsigned integer, a forest-wide leaf
        index in [[0, SPHX_FORS_COUNT * 2**SPHX_FORS_HEIGHT)].
    - Output:
      - a 16-byte preimage.

    This function is only used in the stateless path, and only by the
    signer.

    Note the [node_index] of a FORS leaf or node is indexed across the
    entire forest, not just within a single tree.  The index of leaf
    [l] in tree [t] is [t * 2**SPHX_FORS_HEIGHT + l]. *)
Definition fors_sk_gen (sk_seed : bytes) (pk_seed : bytes) (ADRS : bytes)
                       (node_index : Z) : bytes :=
  let ADRS := set_index ADRS 9 SL_FORS_PRF in
  let ADRS := set_slice ADRS 14 18 (zeros 4) in
  let ADRS := set_slice ADRS 18 22 (to_bytes node_index 4) in
  PRF pk_seed sk_seed ADRS.

(** [fors_node]'s own recursion, structural on [node_height] -- the
    quantity the spec itself decrements
    ([child_height = node_height - 1]), and whose zero case is the
    spec's own base case.  [fors_node] below converts once, on the way
    in. *)
Fixpoint fors_node_loop (node_height : nat) (sk_seed : bytes) (node_index : Z)
                        (pk_seed : bytes) (ADRS : bytes) : bytes :=
  match node_height with
  | O =>
      let preimage := fors_sk_gen sk_seed pk_seed ADRS node_index in
      let ADRS := set_index ADRS 9 SL_FORS_TREE in
      let ADRS := set_slice ADRS 14 18 (zeros 4) in
      let ADRS := set_slice ADRS 18 22 (to_bytes node_index 4) in
      F pk_seed ADRS preimage
  | S child_height =>
      (* The recursive calls' [ADRS] writes are dropped at their return
         (see the header): the three statements below rewrite
         [ADRS[9]] and [ADRS[14:22]], which is every byte
         [fors_node]/[fors_sk_gen] touch. *)
      let lchild_index := 2 * node_index in
      let lchild := fors_node_loop child_height sk_seed lchild_index pk_seed ADRS in
      let rchild := fors_node_loop child_height sk_seed (lchild_index + 1) pk_seed ADRS in

      let ADRS := set_index ADRS 9 SL_FORS_TREE in
      let ADRS := set_slice ADRS 14 18 (to_bytes (Z.of_nat node_height) 4) in
      let ADRS := set_slice ADRS 18 22 (to_bytes node_index 4) in
      H pk_seed ADRS (lchild ++ rchild)
  end.

(** The FORS internal node computation function.  Recursively computes
    the FORS node at the forest-wide [node_index] and [node_height].
    The [ADRS] must be prefilled with the location of the FORS keypair
    to ensure the hashes are properly tweaked.

    - Inputs:
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
      - [node_index]: a 32-bit unsigned integer, a forest-wide node
        index in
        [[0, SPHX_FORS_COUNT * 2**(SPHX_FORS_HEIGHT - node_height))].
      - [node_height]: a 32-bit unsigned integer, a node height in
        [[0, SPHX_FORS_HEIGHT]].
    - Output:
      - a 16-byte FORS node hash.

    This function is only used in the stateless path, and only by the
    signer.

    Note the [node_index] of a FORS leaf or node is indexed across the
    entire forest, not just within a single tree.  The index of node
    [l] in tree [t] at height [h] is
    [t * 2**(SPHX_FORS_HEIGHT - h) + l]. *)
Definition fors_node (sk_seed : bytes) (node_index : Z) (node_height : Z)
                     (pk_seed : bytes) (ADRS : bytes) : bytes :=
  fors_node_loop (Z.to_nat node_height) sk_seed node_index pk_seed ADRS.

(** The FORS signing function.  Produces a FORS signature on a
    [message_digest].  The [ADRS] must be prefilled with the location
    of the FORS keypair to ensure the hashes are properly tweaked.

    - Inputs:
      - [message_digest]: a [FORS_DIGEST_SIZE]-byte message digest.
      - [sk_seed]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a [FORS_SIGNATURE_SIZE]-byte signature.

    This function is only used in the stateless path, and only by the
    signer.

    Two nested [for] loops become two nested folds over the same two
    [range]s; [sig] is the shared accumulator. *)
Definition fors_sign (message_digest : bytes) (sk_seed : bytes) (pk_seed : bytes)
                     (ADRS : bytes) : bytes :=
  let index_set := base_2b message_digest SPHX_FORS_HEIGHT SPHX_FORS_COUNT in
  fold_left
    (fun sig i =>
       let leaf_index := i * 2 ^ SPHX_FORS_HEIGHT + index_int index_set i in
       let sig := sig ++ fors_sk_gen sk_seed pk_seed ADRS leaf_index in
       fold_left
         (fun sig j =>
            let sibling_index :=
              i * 2 ^ (SPHX_FORS_HEIGHT - j)
                + Z.lxor (Z.shiftr (index_int index_set i) j) 1 in
            sig ++ fors_node sk_seed sibling_index j pk_seed ADRS)
         (range 0 SPHX_FORS_HEIGHT)
         sig)
    (range 0 SPHX_FORS_COUNT)
    [].

(** The FORS verification function.  Recovers a FORS public key from a
    [signature] on a [message_digest].  The [ADRS] must be prefilled
    with the location of the FORS keypair to ensure the hashes are
    properly tweaked.

    - Inputs:
      - [signature]: a [FORS_SIGNATURE_SIZE]-byte signature.
      - [message_digest]: a [FORS_DIGEST_SIZE]-byte message digest.
      - [pk_seed]: a 16-byte salt.
      - [ADRS]: a 22-byte address.
    - Output:
      - a 16-byte hash of the FORS public key.

    This function is only used in the stateless path, and by both the
    signer and the verifier.

    The spec's running [offset] into [signature] rides both folds'
    accumulators, so the two loops consume the signature in exactly the
    spec's order. *)
Definition fors_pubkey_from_sig (signature : bytes) (message_digest : bytes)
                                (pk_seed : bytes) (ADRS : bytes) : bytes :=
  let index_set := base_2b message_digest SPHX_FORS_HEIGHT SPHX_FORS_COUNT in

  let '(offset, roots, ADRS) :=
    fold_left
      (fun '(offset, roots, ADRS) i =>
         let preimage := slice signature offset (offset + 16) in
         let offset := offset + 16 in
         let tree_index := i * 2 ^ SPHX_FORS_HEIGHT + index_int index_set i in

         let ADRS := set_index ADRS 9 SL_FORS_TREE in
         let ADRS := set_slice ADRS 14 18 (zeros 4) in
         let ADRS := set_slice ADRS 18 22 (to_bytes tree_index 4) in
         let node := F pk_seed ADRS preimage in
         let '(offset, node, ADRS) :=
           fold_left
             (fun '(offset, node, ADRS) j =>
                let ADRS := set_slice ADRS 14 18 (to_bytes (j + 1) 4) in
                let ADRS := set_slice ADRS 18 22 (to_bytes (Z.shiftr tree_index (j + 1)) 4) in

                let sibling := slice signature offset (offset + 16) in
                let offset := offset + 16 in

                if Z.land (Z.shiftr (index_int index_set i) j) 1 =? 1 then
                  (offset, H pk_seed ADRS (sibling ++ node), ADRS)
                else
                  (offset, H pk_seed ADRS (node ++ sibling), ADRS))
             (range 0 SPHX_FORS_HEIGHT)
             (offset, node, ADRS) in
         (offset, roots ++ node, ADRS))
      (range 0 SPHX_FORS_COUNT)
      (0, [], ADRS) in

  let ADRS := set_index ADRS 9 SL_FORS_ROOTS in
  let ADRS := set_slice ADRS 14 22 (zeros 8) in
  T_k pk_seed ADRS roots.

(* ================================================================= *)
(** ** SLH-DSA algorithms *)

(** The SLH-DSA message hashing function.  Derives the FORS message
    digest, bottom-layer XMSS tree index, and FORS leaf index from
    [message] under [H_msg_sl].

    - Inputs:
      - [R]: a 16-byte randomizer.
      - [pk_seed]: a 16-byte salt.
      - [sl_root]: the 16-byte root hash of the stateless root tree.
      - [message]: a variable-length message.
    - Outputs:
      - a [FORS_DIGEST_SIZE]-byte message digest, ready for use by
        FORS.
      - a pseudorandomly selected index of a bottom-layer XMSS tree: an
        unsigned integer in [[0, 2**SPHX_TREE_INDEX_BITS)].
      - a pseudorandomly selected index of a FORS key within an XMSS
        tree: an unsigned integer in [[0, 2**SPHX_XMSS_HEIGHT)].

    This function is only used in the stateless path, and by both the
    signer and the verifier. *)
Definition slh_dsa_digest_message (R : bytes) (pk_seed : bytes) (sl_root : bytes)
                                  (message : bytes) : bytes * Z * Z :=
  let digest := H_msg_sl R pk_seed sl_root message in

  let fors_digest := slice digest 0 FORS_DIGEST_SIZE in
  let offset := FORS_DIGEST_SIZE in

  let tree_index_digest := slice digest offset (offset + (SPHX_TREE_INDEX_BITS + 7) / 8) in
  let offset := offset + len tree_index_digest in

  let leaf_index_digest := slice digest offset (offset + (SPHX_XMSS_HEIGHT + 7) / 8) in

  let tree_index :=
    from_bytes tree_index_digest mod 2 ^ (SPHX_XMSS_HEIGHT * (SPHX_LAYER_COUNT - 1)) in
  let leaf_index := from_bytes leaf_index_digest mod 2 ^ SPHX_XMSS_HEIGHT in
  (fors_digest, tree_index, leaf_index).

(** The SLH-DSA internal signing function.  Signs [message] with
    [sk_seed], salting all hashes with [pk_seed], deriving the
    randomizer from [sk_prf]/[opt_rand], and binding the signature to
    [sl_root].

    The optional additional data [opt_rand] is used to further salt the
    randomizer.  If omitted, the algorithm uses [pk_seed] in its place,
    resulting in the deterministic variant of SLH-DSA.

    The resulting signature is composed of (1) a randomizer, (2) a FORS
    signature, and (3) a hypertree signature, all concatenated
    together.

    - Inputs:
      - [message]: a variable-length message.
      - [sk_seed]: a 16-byte secret.
      - [sk_prf]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [sl_root]: the 16-byte root hash of the stateless root tree.
      - [opt_rand]: an optional 16-byte salt for the randomizer.
    - Output:
      - a [SPHX_SIGNATURE_SIZE]-byte signature.

    This function is only used in the stateless path, and only by the
    signer.

    [fors_sign]'s and [fors_pubkey_from_sig]'s writes to [ADRS[9]] and
    [ADRS[14:22]] are dropped at their returns (see the header):
    [fors_pubkey_from_sig] rewrites all of them before it hashes, and
    [hypertree_sign] builds its own [ADRS] from scratch. *)
Definition slh_dsa_sign_internal (message : bytes) (sk_seed : bytes) (sk_prf : bytes)
                                 (pk_seed : bytes) (sl_root : bytes)
                                 (opt_rand : option bytes) : bytes :=
  let opt_rand := match opt_rand with
                  | None          => pk_seed   (* deterministic mode *)
                  | Some opt_rand => opt_rand
                  end in

  let R := PRF_msg_sl sk_prf opt_rand message in
  let '(fors_digest, tree_index, leaf_index) :=
    slh_dsa_digest_message R pk_seed sl_root message in

  let ADRS := zeros 22 in
  let ADRS := set_slice ADRS 1 9 (to_bytes tree_index 8) in
  let ADRS := set_slice ADRS 10 14 (to_bytes leaf_index 4) in

  let fors_signature := fors_sign fors_digest sk_seed pk_seed ADRS in
  let fors_pubkey := fors_pubkey_from_sig fors_signature fors_digest pk_seed ADRS in
  let hypertree_signature := hypertree_sign fors_pubkey sk_seed pk_seed tree_index leaf_index in

  R ++ fors_signature ++ hypertree_signature.

(** The SLH-DSA internal verification function.  Recovers the root-tree
    root from a [signature] on [message] and checks it against
    [sl_root].

    - Inputs:
      - [message]: a variable-length message.
      - [signature]: a [SPHX_SIGNATURE_SIZE]-byte signature.
      - [pk_seed]: a 16-byte salt.
      - [sl_root]: the 16-byte root hash of the stateless root tree.
    - Output:
      - a boolean indicating if the signature is valid.

    This function is only used in the stateless path, and only by the
    verifier. *)
Definition slh_dsa_verify_internal (message : bytes) (signature : bytes)
                                   (pk_seed : bytes) (sl_root : bytes) : bool :=
  if negb (len signature =? SPHX_SIGNATURE_SIZE) then
    false
  else
    let R := slice signature 0 16 in
    let fors_signature := slice signature 16 (16 + FORS_SIGNATURE_SIZE) in
    let hypertree_signature :=
      slice signature (16 + FORS_SIGNATURE_SIZE)
        (16 + FORS_SIGNATURE_SIZE + HYPERTREE_SIGNATURE_SIZE) in

    let '(fors_digest, tree_index, leaf_index) :=
      slh_dsa_digest_message R pk_seed sl_root message in

    let ADRS := zeros 22 in
    let ADRS := set_slice ADRS 1 9 (to_bytes tree_index 8) in
    let ADRS := set_slice ADRS 10 14 (to_bytes leaf_index 4) in

    let fors_pubkey := fors_pubkey_from_sig fors_signature fors_digest pk_seed ADRS in
    hypertree_verify fors_pubkey hypertree_signature pk_seed tree_index leaf_index sl_root.

(** The SLH-DSA external signing function.  Signs [message] with
    [sk_seed], prepending the context [ctx]; salts all hashes with
    [pk_seed], derives the randomizer from [sk_prf]/[opt_rand], and
    binds to [sl_root].

    - Inputs:
      - [message]: a variable-length message.
      - [ctx]: a context of at most 255 bytes.
      - [sk_seed]: a 16-byte secret.
      - [sk_prf]: a 16-byte secret.
      - [pk_seed]: a 16-byte salt.
      - [sl_root]: the 16-byte root hash of the stateless root tree.
      - [opt_rand]: an optional 16-byte salt for the randomizer.
    - Output:
      - a [SPHX_SIGNATURE_SIZE]-byte signature.

    This function is only used in the stateless path, and only by the
    signer.

    This is a simple wrapper around [slh_dsa_sign_internal] which
    prepends an optional context [ctx] to every message.  Verifiers
    must use [slh_dsa_verify] with the same [ctx].

    [assert len(ctx) < 256] is a caller obligation: at a longer [ctx],
    [to_bytes (len ctx) 1] truncates where Python raises. *)
Definition slh_dsa_sign (message : bytes) (ctx : bytes) (sk_seed : bytes) (sk_prf : bytes)
                        (pk_seed : bytes) (sl_root : bytes)
                        (opt_rand : option bytes) : bytes :=
  let contextualized_msg := to_bytes 0 1 ++ to_bytes (len ctx) 1 ++ ctx ++ message in
  slh_dsa_sign_internal contextualized_msg sk_seed sk_prf pk_seed sl_root opt_rand.

(** The SLH-DSA verification function.  Recovers the root-tree root
    from a [signature] on [message] (with context [ctx]) and checks it
    against [sl_root].

    - Inputs:
      - [message]: a variable-length message.
      - [signature]: a [SPHX_SIGNATURE_SIZE]-byte signature.
      - [ctx]: a context of at most 255 bytes.
      - [pk_seed]: a 16-byte salt.
      - [sl_root]: the 16-byte root hash of the stateless root tree.
    - Output:
      - a boolean indicating if the signature is valid.

    This function is only used in the stateless path, and only by the
    verifier.

    This is a simple wrapper around [slh_dsa_verify_internal] which
    prepends an optional context [ctx] to every message.  Signatures
    must be produced via [slh_dsa_sign] with the same [ctx].

    [assert len(ctx) < 256] is a caller obligation, as in
    [slh_dsa_sign]. *)
Definition slh_dsa_verify (message : bytes) (signature : bytes) (ctx : bytes)
                          (pk_seed : bytes) (sl_root : bytes) : bool :=
  let contextualized_msg := to_bytes 0 1 ++ to_bytes (len ctx) 1 ++ ctx ++ message in
  slh_dsa_verify_internal contextualized_msg signature pk_seed sl_root.

(* ================================================================= *)
(** ** SHRINCS algorithms *)

(** The SHRINCS key generation function.  Computes the secret and
    public keys from a 48-byte [seed] and the stateful tree
    [sf_structure].

    - Inputs:
      - [seed]: a 48-byte random seed.  Must be sampled from a CSRNG.
      - [sf_structure]: a 2-byte identifier describing the shape and
        depth of the stateful FXMSS tree.
    - Outputs:
      - an 82-byte SHRINCS secret key.
      - a 48-byte SHRINCS public key.

    This function is used only during key generation.

    WARNING: the [sf_structure] argument must come from a trusted
    source or else be validated.  If an adversary can control
    [sf_structure] they may cause key-generation to fail, or hang
    consuming compute resources by making the implementation generate a
    very large BXMSS tree.

    [assert len(seed) == 48] and [assert len(sf_structure) == 2] are
    caller obligations: a short [seed] slices to fewer bytes and a
    short [sf_structure] reads as zeros, where Python raises. *)
Definition shrincs_keygen (seed : bytes) (sf_structure : bytes) : bytes * bytes :=
  let sk_seed := slice seed 0 16 in
  let sk_prf  := slice seed 16 32 in
  let pk_seed := slice seed 32 48 in

  let ADRS := zeros 22 in
  let ADRS := set_index ADRS 0 (SPHX_LAYER_COUNT - 1) in
  let sl_root := xmss_node sk_seed 0 SPHX_XMSS_HEIGHT pk_seed ADRS in
  let sf_root := fxmss_node sk_seed 0 FXMSS_HEIGHT pk_seed sf_structure (zeros 22) in

  let shrincs_seckey := sk_seed ++ sk_prf ++ pk_seed ++ sl_root ++ sf_structure ++ sf_root in
  let shrincs_pubkey := pk_seed ++ sl_root ++ sf_root in
  (shrincs_seckey, shrincs_pubkey).

(** The SHRINCS stateful-path leaf-selection function.  Computes the
    position [(index, height)] of the next WOTS+C leaf for the given
    [structure] and [state_ctr].

    - Inputs:
      - [structure]: a 2-byte identifier describing the FXMSS tree
        structure.
      - [state_ctr]: a signed integer, the number of stateful
        signatures the keypair has previously issued (a negative value
        is permitted, and makes the function return [None]).
    - Outputs:
      - a 64-bit unsigned integer, the left-to-right index of the next
        WOTS+C leaf in the FXMSS tree.
      - an 8-bit unsigned integer, the bottom-to-top height of the next
        WOTS+C leaf in the FXMSS tree.

    Returns [None] if [state_ctr] is set to any negative number, or if
    [state_ctr + 1] exceeds the number of WOTS+C leaves in the FXMSS
    tree (as defined by its structure).

    This function is only used in the stateful path, and only by the
    signer. *)
Definition shrincs_sf_leaf_select (structure : bytes) (state_ctr : Z) : option (Z * Z) :=
  let tree_shape := index structure 0 in
  let tree_depth := index structure 1 in
  if tree_shape =? FXMSS_SHAPE_UNBALANCED then
    if (state_ctr =? tree_depth) && (tree_depth >? 0) then
      Some (0, FXMSS_HEIGHT - tree_depth)
    else if (state_ctr >=? 0) && (state_ctr <? tree_depth + 1) then
      (* Ported as written, WITHOUT a [tree_depth > 0] guard: at depth 0
         this returns [(1, 254)] where [None] was meant -- the "Upstream
         spec bug" entry in proof/README.md. *)
      Some (1, FXMSS_HEIGHT - 1 - state_ctr)
    else
      None
  else if tree_shape =? FXMSS_SHAPE_BALANCED then
    if (state_ctr >=? 0) && (state_ctr <? 2 ^ tree_depth) && (tree_depth >? 0) then
      Some (state_ctr, FXMSS_HEIGHT - tree_depth)
    else
      None
  else
    (* - unknown FXMSS tree shape
       - depth-zero tree
       - no more signatures left
       - state is negative *)
    None.

(** The SHRINCS signing function.  Signs [message] with the serialized
    secret key [shrincs_seckey]: uses the stateful FXMSS path when
    [state_ctr] is valid for the key's tree structure, otherwise falls
    back to the stateless SLH-DSA path.

    - Inputs:
      - [message]: a message of at most [2**61 - 128] bytes.
      - [shrincs_seckey]: an 82-byte SHRINCS secret key.
      - [state_ctr]: a signed integer, the number of stateful
        signatures the keypair has previously issued (a negative value
        is permitted, and forces the stateless path).
      - [opt_rand]: an optional 16-byte salt for the randomizer in
        SLH-DSA (unused in the stateful path; if omitted, the stateless
        path uses the deterministic variant of SLH-DSA).
    - Output:
      - a variable-length SHRINCS signature.

    This function is used only by the signer.

    CAUTION: using the same key to sign different [message] values with
    the same [state_ctr] is a security vulnerability.  SHRINCS
    implementations must wrap [shrincs_sign] with code which increments
    and saves the state counter as [state_ctr + 1] on a persistent,
    non-recoverable storage medium before the signature is returned to
    the caller.  The only exception is for negative values of
    [state_ctr], which explicitly force the stateless path. *)
Definition shrincs_sign (message : bytes) (shrincs_seckey : bytes) (state_ctr : Z)
                        (opt_rand : option bytes) : bytes :=
  let sk_seed      := slice shrincs_seckey 0 16 in
  let sk_prf       := slice shrincs_seckey 16 32 in
  let pk_seed      := slice shrincs_seckey 32 48 in
  let sl_root      := slice shrincs_seckey 48 64 in
  let sf_structure := slice shrincs_seckey 64 66 in
  let sf_root      := slice shrincs_seckey 66 82 in

  let leaf_position := shrincs_sf_leaf_select sf_structure state_ctr in

  match leaf_position with
  (* Stateless signing path. *)
  | None =>
      (* Bind the stateless signature to the stateful keypair. *)
      slh_dsa_sign (sf_root ++ message) [] sk_seed sk_prf pk_seed sl_root opt_rand

  (* Stateful signing path. *)
  | Some (leaf_index, leaf_height) =>
      let ADRS := zeros 22 in
      let ADRS := set_index ADRS 0 leaf_height in
      let ADRS := set_slice ADRS 1 9 (to_bytes leaf_index 8) in
      let R := PRF_msg_sf sk_prf pk_seed ADRS message in

      (* Bind the stateful signature to the stateless keypair. *)
      let message_digest := H_msg_sf R pk_seed sf_root ADRS (sl_root ++ message) in
      let fxmss_signature :=
        fxmss_sign message_digest sk_seed leaf_index leaf_height pk_seed sf_structure in

      (* TODO: compact encoding for leaf index *)
      R ++ to_bytes leaf_index 8 ++ fxmss_signature
  end.

(** The SHRINCS verification function.  Returns true iff [signature] is
    a valid stateful or stateless SHRINCS signature on [message] under
    [shrincs_pubkey].

    Based on the length of [signature], the verifier either recomputes
    [sf_root] (stateful path) or recomputes [sl_root] (stateless path),
    and compares the result against the public key.

    - Inputs:
      - [message]: a message of at most [2**61 - 128] bytes.
      - [signature]: a purported SHRINCS signature of arbitrary length.
      - [shrincs_pubkey]: a 48-byte SHRINCS public key.
    - Output:
      - a boolean indicating if the signature is valid.

    This function is used only by the verifier. *)
Definition shrincs_verify (message : bytes) (signature : bytes)
                          (shrincs_pubkey : bytes) : bool :=
  let pk_seed := slice shrincs_pubkey 0 16 in
  let sl_root := slice shrincs_pubkey 16 32 in
  let sf_root := slice shrincs_pubkey 32 48 in

  (* Stateless verification path. *)
  if len signature =? SPHX_SIGNATURE_SIZE then
    (* Stateless signatures must be bound to the stateful keypair. *)
    slh_dsa_verify (sf_root ++ message) signature [] pk_seed sl_root

  (* Stateful verification path. *)
  else if len signature <? 24 then
    false
  else
    let R := slice signature 0 16 in
    let leaf_index := from_bytes (slice signature 16 24) in
    let fxmss_signature := slice signature 24 (len signature) in

    (* FXMSS signature length must fall within expected bounds. *)
    if negb ((FXMSS_SIGNATURE_SIZE_MIN <=? len fxmss_signature)
               && (len fxmss_signature <=? FXMSS_SIGNATURE_SIZE_MAX)) then
      false

    (* Signature length must be 2 more than a multiple of 16. *)
    else if negb ((len fxmss_signature - 2) mod 16 =? 0) then
      false
    else
      let leaf_depth := (len fxmss_signature - 2) / 16 - WOTS_C_CHAIN_COUNT in
      let leaf_height := FXMSS_HEIGHT - leaf_depth in

      (* Reject a leaf_index that names no position in a tree of this depth. *)
      if leaf_index >=? 2 ^ Z.min 64 leaf_depth then
        false
      else
        let ADRS := zeros 22 in
        let ADRS := set_index ADRS 0 leaf_height in
        let ADRS := set_slice ADRS 1 9 (to_bytes leaf_index 8) in

        (* Stateful signatures must be bound to the stateless keypair. *)
        let message_digest := H_msg_sf R pk_seed sf_root ADRS (sl_root ++ message) in
        let root := fxmss_pubkey_from_sig leaf_index fxmss_signature message_digest pk_seed in
        match root with
        | None      => false
        | Some root => bytes_eqb root sf_root
        end.
