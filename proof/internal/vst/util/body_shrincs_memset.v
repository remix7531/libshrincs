(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_memset: VST body proof for [shrincs_memset]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog.
From Shrincs.clight Require Import util.

Open Scope Z_scope.

Lemma body_shrincs_memset : semax_body Vprog Gprog_util f_shrincs_memset shrincs_memset_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.

  (* ===== Convert [memory_block] to [data_at_] over [tarray tuchar n] ===== *)

  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.

  (* ===== Cast d = (uint8_t ptr) dst ===== *)

  forward.

  (* ===== Cast [_b = (uint8_t) byte] ===== *)

  forward.
  (* clightgen emits a double uchar cast; collapse the nested
     [Int.zero_ext 8] so [_b] matches the loop invariant. *)
  rewrite Int.zero_ext_idem by lia.

  (* ===== Loop: invariant builds [repeat (Vint c) i] prefix ===== *)

  forward_for_simple_bound n
    (EX i : Z,
      PROP ()
      LOCAL (temp _d p; temp _b (Vint (Int.zero_ext 8 c));
             temp _dst p; temp _n (Vlong (Int64.repr n)))
      SEP (data_at sh (tarray tuchar n)
             (repeat (Vint c) (Z.to_nat i) ++
              Zrepeat Vundef (n - i)) p)).

  (* Loop entry: i = 0 *)

  - rewrite data_at__tarray.
    entailer!!.
    list_solve.

  (* Loop body: write byte b at index i *)

  - (* d[i] = b *)
    forward.
    entailer!.
    (* The stored [zero_ext 8 c] is just [c] since [c < 256]. *)
    assert (Hbyte : Int.zero_ext 8 c = c).
    { apply zero_ext_inrange.
      change (two_p 8) with 256.
      lia. }
    rewrite Hbyte.
    list_solve.

  (* ===== Loop exit ===== *)

  - rewrite Z.sub_diag, Zrepeat_0, app_nil_r.

    (* ===== Return [dst] ===== *)

    forward.
Qed.
