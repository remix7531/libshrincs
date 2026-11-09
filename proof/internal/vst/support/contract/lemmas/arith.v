(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.arith: byte / nibble / xor / [to_byte] arithmetic bridges.

    Aggregates the ad-hoc VST-friendly arithmetic bridges, split by topic:
      [contract.lemmas.arith_counter] -- 2-byte counter shift/or reassembly
      [contract.lemmas.arith_nibble]  -- nibble extraction + base-16 digit facts
      [contract.lemmas.arith_xor]     -- [Int.xor] / [Int.or] byte facts
    The pure-Z [to_byte] shape, byte-extraction and [list_sum] facts these
    bridges build on live in [theory.pure]. *)

From Vst Require Export contract.lemmas.arith_counter.
From Vst Require Export contract.lemmas.arith_nibble.
From Vst Require Export contract.lemmas.arith_xor.
