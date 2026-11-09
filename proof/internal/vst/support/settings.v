(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.settings: the settings every sha256 body proof needs

    Small, and load-bearing. Everything here exists because a
    [forward] misbehaves without it.

    THE DIVERGING BYTE STORE. src/sha256.c's store_be32 writes
    [p[0] = (uint8_t)(x >> 24)] into a [tarray tuchar]. Stepping that
    with [forward] does not fail, it HANGS: floyd evaluates the stored
    value, [simpl] unfolds [Int.Z_mod_modulus] and [Z.shiftr], and at
    a shift of 24 or more the resulting term is large enough that the
    tactic never returns. The symptom is a Rocq [Timeout] with no
    indication of the cause.

    The four [Arguments] below stop the unfolding. They must be in
    scope BEFORE the [forward] chain, which is why this is a file and
    not a comment: [Arguments] is global on Import, so any verif file
    that imports this one is protected by all four.

    [Z.shiftl] is included as well: the combining loads in load_be32
    and sha256_parse are the same shape in the other direction.
    [Int64.Z_mod_modulus] is the same hazard at [tulong], where
    sha256's message-length arithmetic lives. *)

From Shrincs.internal.vst.support Require Import base.

Arguments Int.Z_mod_modulus : simpl never.
Arguments Int64.Z_mod_modulus : simpl never.
Arguments Z.shiftr : simpl never.
Arguments Z.shiftl : simpl never.

(** [rep_lia] is floyd's arithmetic workhorse, but it only knows the
    bounds it has been told about. The three sizes that recur in every
    sha256 loop bound are registered here so a body proof does not
    have to [change] them by hand. *)
#[export] Hint Rewrite Int.unsigned_repr using rep_lia : norm.
