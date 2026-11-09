(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.helpers_libc: VST funspecs for the in-tree libc alternatives.

    The [shrincs_memset] / [shrincs_memcpy] / [shrincs_ct_memcmp] /
    [shrincs_panic] helpers from [include/util.h].  These are NOT trusted --
    their bodies are proved under [proof/internal/vst/util/]. Bundled
    with the tweakable-hash funspecs ([contract.helpers_thash]) and the
    WOTS+C step funspecs ([contract.helpers_wots]) as [Gprog_libc] in
    [contract.gprog]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.repr.

Open Scope Z_scope.
Open Scope logic.

Definition shrincs_memset_spec : ident * funspec :=
  DECLARE _shrincs_memset
  WITH sh : share, p : val, n : Z, c : int
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned;
          0 <= Int.unsigned c < 256)
    PARAMS (p; Vint c; Vlong (Int64.repr n))
    SEP (memory_block sh n p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at sh (tarray tuchar n)
           (repeat (Vint c) (Z.to_nat n)) p).

Definition shrincs_memcpy_spec : ident * funspec :=
  DECLARE _shrincs_memcpy
  WITH qsh : share, psh : share, p : val, q : val,
       n : Z, contents : list int
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share qsh; writable_share psh;
          0 <= n <= Int64.max_unsigned)
    PARAMS (p; q; Vlong (Int64.repr n))
    SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
         memory_block psh n p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
         data_at psh (tarray tuchar n) (map Vint contents) p).

(** [shrincs_ct_memcmp(a, b, n)]: returns 0 iff the [n] bytes at [a]
    and [b] agree. *)
Definition shrincs_ct_memcmp_spec : ident * funspec :=
  DECLARE _shrincs_ct_memcmp
  WITH psh : share, qsh : share, p : val, q : val,
       n : Z, p_contents : list int, q_contents : list int
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share psh; readable_share qsh;
          0 <= n <= Int64.max_unsigned;
          Zlength p_contents = n; Zlength q_contents = n;
          Forall (fun i => 0 <= Int.unsigned i < 256) p_contents;
          Forall (fun i => 0 <= Int.unsigned i < 256) q_contents)
    PARAMS (p; q; Vlong (Int64.repr n))
    SEP (data_at psh (tarray tuchar n) (map Vint p_contents) p;
         data_at qsh (tarray tuchar n) (map Vint q_contents) q)
  POST [ tint ]
    EX r : int,
    PROP (r = Int.zero <-> p_contents = q_contents)
    RETURN (Vint r)
    SEP (data_at psh (tarray tuchar n) (map Vint p_contents) p;
         data_at qsh (tarray tuchar n) (map Vint q_contents) q).

(** [shrincs_panic()]: unreachable from valid callers. *)
Definition shrincs_panic_spec : ident * funspec :=
  DECLARE _shrincs_panic
  WITH u : unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().
