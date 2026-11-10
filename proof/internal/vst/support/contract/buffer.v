(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.buffer: a byte buffer being filled from the left

    Every buffer [src/thash.c] and [src/wots.c] build is written front to back: a hash preimage one field after the other, a signature one chain after the other, the chain tips one tip after the other. [filled sh md f p] is such a buffer of [md] bytes at [p] in the middle of that: its first bytes are the byte string [f] of the specification and the rest is not written yet. *)

From Shrincs.internal.vst.support Require Import base settings.
From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.support Require Import contract.helpers contract.trusted.
Require Shrincs.sha256.
Require Shrincs.clight.sha256.
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

Definition filled (sh : share) (md : Z) (f : seq UInt8) (p : Values.val) : mpred :=
  data_at sh (tarray tuchar md) (app (vals f) (Zrepeat Vundef (md - Zlength f))) p.

(** [shrincs_memcpy] appending the window [ks, ks + n) of a byte string to the buffer.

    The two pointers the C passes are quantified as they are, [q_d] and [q_s], and tied to the buffers by a premise each. A call that starts at the head of a buffer passes the buffer's own pointer, which is [offset_val 0] of itself only once it is known to be a pointer, so the tie is a proof obligation and not a syntactic match. The bytes copied are a witness too, [x], so the caller names them in the vocabulary of the specification. *)
Definition memcpy_fill_spec : ident * funspec :=
  DECLARE util._shrincs_memcpy
  WITH sh_d : share, sh_s : share, p_d : Values.val, p_s : Values.val,
       q_d : Values.val, q_s : Values.val,
       md : Z, ms : Z, k : Z, ks : Z, n : Z,
       f : seq UInt8, src : seq UInt8, x : seq UInt8
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (writable_share sh_d; readable_share sh_s;
          q_d = offset_val k p_d; q_s = offset_val ks p_s;
          Zlength f = k; Zlength src = ms; sublist ks (ks + n) src = x;
          0 <= ks; 0 <= n; ks + n <= ms; k + n <= md; md <= Int64.max_unsigned)
    PARAMS (q_d; q_s; Vlong (Int64.repr n))
    SEP (filled sh_d md f p_d; data_at sh_s (tarray tuchar ms) (vals src) p_s)
  POST [ tptr tvoid ]
    PROP () RETURN (q_d)
    SEP (filled sh_d md (cat f x) p_d; data_at sh_s (tarray tuchar ms) (vals src) p_s).

(** [shrincs_memset] appending [n] zero bytes. *)
Definition memset_fill_spec : ident * funspec :=
  DECLARE util._shrincs_memset
  WITH sh : share, p : Values.val, q : Values.val, md : Z, k : Z, n : Z,
       f : seq UInt8, x : seq UInt8
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; q = offset_val k p;
          Zlength f = k; nseq (Z.to_nat n) (uint U8 0) = x;
          0 <= n; k + n <= md; md <= Int64.max_unsigned)
    PARAMS (q; Vint (Int.repr 0); Vlong (Int64.repr n))
    SEP (filled sh md f p)
  POST [ tptr tvoid ]
    PROP () RETURN (q)
    SEP (filled sh md (cat f x) p).

(** [shrincs_sha256] over the written part of a buffer, with the digest as the bytes [Shrincs.spec]'s [sha256] returns. The bound is SHA-256's own, far above any buffer here. *)
Definition sha256_fill_spec : ident * funspec :=
  DECLARE Shrincs.clight.sha256._shrincs_sha256
  WITH out_ptr : Values.val, in_ptr : Values.val, md : Z, n : Z, f : seq UInt8,
       sh_o : share, sh_i : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_i;
          Zlength f = n; n <= md; md < 2305843009213693952)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr n))
    SEP (data_at_ sh_o (tarray tuchar 32) out_ptr; filled sh_i md f in_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 32) (vals (sha256 f)) out_ptr;
         filled sh_i md f in_ptr).
