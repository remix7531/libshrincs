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

    THIS FILE IS A VALIDATION SAMPLE (phase P12a): it carries the
    constants block, the spec's own helper section, and the six
    functions the design had to be tested against ([base_2b],
    [wots_chain_iter], [wots_c_grind_to_constant_sum],
    [wots_c_map_digest], [fxmss_node], [shrincs_sf_leaf_select]) plus
    everything those transitively call.  The remaining ~35 spec
    functions land in the same order, in the same file. *)

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

(* ================================================================= *)
(** ** Tweaked hash functions *)

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

(* ================================================================= *)
(** ** SHRINCS algorithms *)

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
