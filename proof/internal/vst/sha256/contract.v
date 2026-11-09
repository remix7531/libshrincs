(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.sha256.contract: what each function of src/sha256.c promises

    Twelve funspecs, one per C function, each stating the FIPS
    180-4 step the function performs in terms of Shrincs.sha256. Read
    together they are the design of the proof: the interesting content
    is which model function appears in which POSTcondition, because
    that is where the C's structure is asserted to match the
    standard's.

    THE TABLES ARE NOT A RESOURCE, and that is what makes the exported
    contract below a function of its bytes and nothing else.
    K (SS 4.2.2) and H^(0) (SS 5.3.3) are function LOCALS in
    src/sha256.c, not file-scope arrays, so they are not Clight globals
    and no caller has to own them: no [gv : globals], no SEP conjunct,
    and nothing about the round constants of a hash reaching any
    caller's own contract. Shrincs.internal.vst.sha256.tables
    says why the C is written that way and what it cost.

    K APPEARS ONLY IN THE TWO INTERNAL CONTRACTS, and there as a
    PARAMETER: [sha256_compress_words] and [sha256_compress_blocks]
    both receive the table rather than declaring it. The exported
    function owns it -- once per call -- so it never crosses the
    interface.

    Argument order is output first, matching include/sha256.h.

    SIZES ARE 64-BIT. The target is [bitsize 64] (check the [Module
    Info] block of Shrincs.clight.sha256), so [size_t] is [tulong], a
    length parameter is [Vlong (Int64.repr n)], and its bound is
    [Int64.max_unsigned]. Passing [Vint] here is the classic 64-bit
    mistake: it does not fail at definition time, it fails much later
    at a [forward_call] that will not match. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import bridge.
From Shrincs.internal.vst.sha256 Require Import tables.
From Shrincs.internal.vst.sha256 Require Import clone.

(* The sha256 translation unit's AST. Imported (not merely Required)
   so the identifiers below are unqualified; this shadows
   Shrincs.clight.wots's [prog] and [composites], which Shrincs.internal.vst.support.base
   exports. The composite environments agree, as explained in
   Shrincs.internal.vst.support.base's header, where the situation is created. *)
From Shrincs.clight Require Import sha256.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.
Local Open Scope logic.

(* ================================================================= *)
(** ** SS 4.1.2: the six logical functions

    Pure functions of their arguments: no SEP clause, no globals. Each
    POSTcondition is its FIPS equation, so proving these six is
    proving that the C's bit-twiddling is the standard's. *)

Definition spec_Ch : ident * funspec :=
  DECLARE _Ch
  WITH x : Int.int, y : Int.int, z : Int.int
  PRE [ tuint, tuint, tuint ]
    PROP () PARAMS (Vint x; Vint y; Vint z) SEP ()
  POST [ tuint ]
    PROP ()
    RETURN (Vint (int_of_w32 (Ch (w32_of_int x) (w32_of_int y) (w32_of_int z))))
    SEP ().

Definition spec_Maj : ident * funspec :=
  DECLARE _Maj
  WITH x : Int.int, y : Int.int, z : Int.int
  PRE [ tuint, tuint, tuint ]
    PROP () PARAMS (Vint x; Vint y; Vint z) SEP ()
  POST [ tuint ]
    PROP ()
    RETURN (Vint (int_of_w32 (Maj (w32_of_int x) (w32_of_int y) (w32_of_int z))))
    SEP ().

Definition spec_Sigma0 : ident * funspec :=
  DECLARE _Sigma0
  WITH x : Int.int
  PRE [ tuint ] PROP () PARAMS (Vint x) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (int_of_w32 (Sigma0 (w32_of_int x)))) SEP ().

Definition spec_Sigma1 : ident * funspec :=
  DECLARE _Sigma1
  WITH x : Int.int
  PRE [ tuint ] PROP () PARAMS (Vint x) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (int_of_w32 (Sigma1 (w32_of_int x)))) SEP ().

Definition spec_sigma0 : ident * funspec :=
  DECLARE _sigma0
  WITH x : Int.int
  PRE [ tuint ] PROP () PARAMS (Vint x) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (int_of_w32 (sigma0 (w32_of_int x)))) SEP ().

Definition spec_sigma1 : ident * funspec :=
  DECLARE _sigma1
  WITH x : Int.int
  PRE [ tuint ] PROP () PARAMS (Vint x) SEP ()
  POST [ tuint ]
    PROP () RETURN (Vint (int_of_w32 (sigma1 (w32_of_int x)))) SEP ().

(* ================================================================= *)
(** ** SS 3.1 (2): the big-endian word codec

    The only two functions in the file that decide byte order. Both
    are stated over the shared codec in [Shrincs.internal.common.bytes]. *)

Definition spec_load_be32 : ident * funspec :=
  DECLARE _load_be32
  WITH sh : share, p : Values.val, bs : list byte
  PRE [ tptr tuchar ]
    PROP (readable_share sh; Zlength bs = 4)
    PARAMS (p)
    SEP (data_at sh (tarray tuchar 4) (List.map Vubyte bs) p)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (int_of_w32 (word_of_bytes U32 (List.map Byte.unsigned bs))))
    SEP (data_at sh (tarray tuchar 4) (List.map Vubyte bs) p).

Definition spec_store_be32 : ident * funspec :=
  DECLARE _store_be32
  WITH sh : share, p : Values.val, x : Int.int
  PRE [ tptr tuchar, tuint ]
    PROP (writable_share sh)
    PARAMS (p; Vint x)
    SEP (data_at_ sh (tarray tuchar 4) p)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar 4)
           (List.map (fun z => Vubyte (Byte.repr z))
                     (bytes_of_word U32 (w32_of_int x))) p).

(* ================================================================= *)
(** ** SS 5.2.1 and SS 6.2.2: parsing and compressing one block *)

Definition spec_sha256_parse : ident * funspec :=
  DECLARE _sha256_parse
  WITH shm : share, shb : share, mp : Values.val, bp : Values.val, blk : list byte
  PRE [ tptr tuint, tptr tuchar ]
    PROP (writable_share shm; readable_share shb; Zlength blk = 64)
    PARAMS (mp; bp)
    SEP (data_at_ shm (tarray tuint 16) mp;
         data_at shb (tarray tuchar 64) (List.map Vubyte blk) bp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shm (tarray tuint 16)
           (words_to_vals (parse_block (List.map Byte.unsigned blk))) mp;
         data_at shb (tarray tuchar 64) (List.map Vubyte blk) bp).

(** The expensive one, and the one the whole design is arranged
    around: its POSTcondition is exactly the compression function of
    SS 6.2.2, with the schedule and the sixty-four rounds hidden
    inside it. RustCrypto sha2's [compress_u32]. *)
Definition spec_sha256_compress_words : ident * funspec :=
  DECLARE _sha256_compress_words
  WITH shh : share, shm : share, shk : share,
       hp : Values.val, mp : Values.val, kp : Values.val,
       Hs : seq w32c, Ms : seq w32c
  PRE [ tptr tuint, tptr tuint, tptr tuint ]
    PROP (writable_share shh; readable_share shm; readable_share shk;
          size Hs = 8%nat; size Ms = 16%nat)
    PARAMS (hp; mp; kp)
    SEP (data_at shh (tarray tuint 8) (words_to_vals Hs) hp;
         data_at shm (tarray tuint 16) (words_to_vals Ms) mp;
         data_at shk (tarray tuint 64) (words_to_vals K) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shh (tarray tuint 8) (words_to_vals (compress_words Hs Ms)) hp;
         data_at shm (tarray tuint 16) (words_to_vals Ms) mp;
         data_at shk (tarray tuint 64) (words_to_vals K) kp).

(** The same function over a run of [n] consecutive blocks, advancing
    the state in place. RustCrypto sha2's [compress(state, blocks)],
    and the only thing shrincs_sha256() below does with the message
    bytes.

    Internal to the translation unit -- include/sha256.h exports one
    function and this is not it -- but it still needs a contract,
    because shrincs_sha256's body calls it twice. *)
(* [Z.mul 64 n] spelled out rather than [64 * n]: with floyd's [logic]
   scope open for the separating [*] in SEP, a bare [*] here parses as
   the type product, and the [%Z] escape does not help because in this
   import context [%Z] is MATHCOMP's int_scope and not Stdlib's
   Z_scope (the trap Shrincs.internal.common.bytes documents for hex literals). *)
Definition spec_sha256_compress_blocks : ident * funspec :=
  DECLARE _sha256_compress_blocks
  WITH shs : share, shb : share, shk : share,
       sp : Values.val, bp : Values.val, kp : Values.val,
       Hs : seq w32c, bs : list byte, n : Z
  PRE [ tptr tuint, tptr tuchar, tulong, tptr tuint ]
    PROP (writable_share shs; readable_share shb; readable_share shk;
          size Hs = 8%nat; Zlength bs = Z.mul 64 n; 0 <= n <= Int64.max_unsigned)
    PARAMS (sp; bp; Vlong (Int64.repr n); kp)
    SEP (data_at shs (tarray tuint 8) (words_to_vals Hs) sp;
         data_at shb (tarray tuchar (Z.mul 64 n)) (List.map Vubyte bs) bp;
         data_at shk (tarray tuint 64) (words_to_vals K) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at shs (tarray tuint 8)
           (words_to_vals (compress_blocks Hs (List.map Byte.unsigned bs))) sp;
         data_at shb (tarray tuchar (Z.mul 64 n)) (List.map Vubyte bs) bp;
         data_at shk (tarray tuint 64) (words_to_vals K) kp).

(* ================================================================= *)
(** ** The exported entry point

    Non-overlap of [in] and [out] is
    the separating [;] between the SEP clauses -- the formal
    counterpart of the [restrict] on the C parameters
    (include/sha256.h), which CompCert drops during elaboration. *)

(** SS 6.2 in general. [inlen < 2^61] is what makes the message length
    in BITS fit the 64-bit field SS 5.1.1 appends; include/sha256.h
    states the same bound in the same words. *)
Definition spec_sha256 : ident * funspec :=
  DECLARE _shrincs_sha256
  WITH msg : list byte, out_ptr : Values.val, in_ptr : Values.val,
       sh_in : share, sh_out : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sh_in; writable_share sh_out;
          0 <= Zlength msg < two_p 61)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr (Zlength msg)))
    SEP (data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
         out_ptr |->_32[sh_out])
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
         out_ptr |->32[sh_out] (clone.sha256 (List.map Byte.unsigned msg))).

(* ================================================================= *)
(** ** The proof context

    [Vprog_sha] is empty: src/sha256.c has no globals at all now that
    the two tables are locals. [Gprog_sha] is every funspec above, in
    call order: a [forward_call] resolves against this list, so a
    function missing from it is a body proof that cannot step over its
    own call. *)

Definition Vprog_sha : varspecs. mk_varspecs sha256.prog. Defined.

Definition Gprog_sha : funspecs :=
  [ spec_Ch; spec_Maj; spec_Sigma0; spec_Sigma1; spec_sigma0; spec_sigma1;
    spec_load_be32; spec_store_be32;
    spec_sha256_parse; spec_sha256_compress_words; spec_sha256_compress_blocks;
    spec_sha256 ].

(** Reviewability, by [reflexivity]: the contract list covers exactly
    the twelve functions src/sha256.c defines, in the AST's own
    identifiers. If a function is added to the C and not specified, or
    renamed, this stops compiling. *)
Lemma Gprog_sha_idents :
  map fst Gprog_sha =
  [ _Ch; _Maj; _Sigma0; _Sigma1; _sigma0; _sigma1;
    _load_be32; _store_be32; _sha256_parse; _sha256_compress_words;
    _sha256_compress_blocks; _shrincs_sha256 ].
Proof. reflexivity. Qed.
