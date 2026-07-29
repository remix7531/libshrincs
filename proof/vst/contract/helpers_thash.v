(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.helpers_thash: VST funspecs for the shared tweakable-hash TU
    ([src/thash.c]).

    Each funspec relates a C step function to its pure counterpart in
    the spec port: [shrincs_adrs_put32], [shrincs_thash].  Bodies are proved
    in [verif/*].  This is the shared tweakable-hash layer's spec home --
    the FXMSS expansion imports these specs (via [contract.helpers]) without
    pulling in the WOTS-specific specs of [contract.helpers_wots]. Bundled
    with the libc funspecs ([contract.helpers_libc]) and the WOTS+C helper
    funspecs ([contract.helpers_wots]) as [Gprog_thash] in
    [contract.gprog]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.repr.

Open Scope Z_scope.
Open Scope logic.

Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** [shrincs_adrs_put32(addr, off, v)] -- store [v] as 4 big-endian bytes at
    [addr[off .. off+4)].  Stated over the raw 22-byte content; the
    bridge lemmas in [lemmas/data_at.v] connect the [sublist] splice to
    the [set_payload_a] / [set_payload_b] / [set_payload_c] setters. *)

Definition shrincs_adrs_put32_spec : ident * funspec :=
  DECLARE _shrincs_adrs_put32
  WITH a_ptr : val, off : Z, v : Z, content : list byte, sh : share
  PRE [ tptr tuchar, tuint, tuint ]
    PROP (writable_share sh; Zlength content = 22;
          0 <= off; off + 4 <= 22; 0 <= v <= Int.max_unsigned)
    PARAMS (a_ptr; Vint (Int.repr off); Vint (Int.repr v))
    SEP (data_at sh (tarray tuchar 22) (block_to_vals content) a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar 22)
           (block_to_vals (sublist 0 off content ++ to_byte v 4 ++ sublist (off + 4) 22 content))
           a_ptr).

(* ================================================================= *)
(** ** [shrincs_thash(out, pk_seed, addr, msg, msglen)] -- the SHRINCS
    tweakable hash, generalized to any message length:
    [out := SHA256(pk_seed || zeros(48) || ADRS || msg[:msglen])[:16]
          = F pk_seed (adrs_bytes A) msg].  Reads [addr] and [msg]; [out]
    must not alias [msg].

    The port spells this construction FIVE times -- [F], [PRF], [T_sf],
    [T_sl], [T_k], [H] -- because shrincs.py does (model/PORTING.md:
    "five separate definitions, as in the spec, even though they are
    convertible").  They are definitionally equal, so this one funspec
    serves every WOTS+C hash use; [F] is named here because the chain
    hash is the C's own primary caller. *)

Definition shrincs_thash_spec : ident * funspec :=
  DECLARE _shrincs_thash
  WITH out_ptr : val, ps_ptr : val, a_ptr : val, m_ptr : val, msglen : Z,
       A : adrs, pk_seed : block, msg : block,
       sh_o : share, sh_ps : share, sh_a : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_ps; readable_share sh_a; readable_share sh_m;
          Zlength pk_seed = n_bytes; Zlength msg = msglen; 0 <= msglen <= 512)
    PARAMS (out_ptr; ps_ptr; a_ptr; m_ptr; Vlong (Int64.repr msglen))
    SEP (data_at_ sh_o (tarray tuchar n_bytes) out_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals A)         a_ptr;
         data_at sh_m  (tarray tuchar msglen)  (block_to_vals msg)      m_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes)
           (block_to_vals (shrincs.F pk_seed (adrs_bytes A) msg)) out_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals A)         a_ptr;
         data_at sh_m  (tarray tuchar msglen)  (block_to_vals msg)      m_ptr).
