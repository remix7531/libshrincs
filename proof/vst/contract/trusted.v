(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.trusted: externally-specified / axiomatic funspecs.

    These specs describe functions that are NOT proved against C code in
    this repo -- they are assumed correct by construction.  Currently
    exactly one entry:

    - [sha256_spec]: the only cryptographic primitive.  [model.sha256.SHA256]
      is a [Parameter] and [body_sha256] is an [Axiom] in [contract.gprog]
      by design, since [src/sha256.c] is a direct FIPS 180-4 port verified
      elsewhere.

    The in-tree libc alternatives ([shrincs_memcpy], [shrincs_memset],
    [shrincs_ct_memcmp], [shrincs_panic]) are NOT trusted -- their funspecs
    live in [contract.helpers] and their bodies are proved in
    [proof/verif].

    When auditing: the trusted FUNSPECS are exactly this file; the two
    trust anchors themselves are [Parameter SHA256] (proof/model/sha256.v)
    and [Axiom body_sha256] (contract/gprog.v -- its statement mentions
    [Gprog], so it must live where [Gprog] is defined).  `make audit`
    checks that those two (plus machine.v's Module-Type fields, which are
    discharged at instantiation) are the only Axiom/Parameter lines in
    the vst + model trees. *)

From VST Require Export floyd.proofauto.
From Vst Require Export clight.sha256 contract.public.

Open Scope Z_scope.

(** [sha256(out, in, inlen)]: writes the 32-byte digest of [in] to [out].
    [inlen]'s bound is [sha256_max_input_len] (not [Int64.max_unsigned],
    [tulong]'s own range) -- the real function's valid domain is
    SHA-256's own 2^61-byte limit, per [model.sha256]. *)
Definition sha256_spec : ident * funspec :=
  DECLARE _shrincs_sha256
  WITH out_ptr : val, in_ptr : val, inlen : Z,
       input : list byte,
       sh_o : share, sh_i : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_i;
          Zlength input = inlen;
          0 <= inlen <= sha256_max_input_len)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr inlen))
    SEP (data_at_ sh_o (tarray tuchar 32) out_ptr;
         data_at  sh_i (tarray tuchar inlen) (block_to_vals input) in_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 32) (block_to_vals (sha256' input)) out_ptr;
         data_at sh_i (tarray tuchar inlen) (block_to_vals input) in_ptr).
