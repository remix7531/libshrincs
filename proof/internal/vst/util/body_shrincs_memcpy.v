(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_memcpy: VST body proof for [shrincs_memcpy]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.

Open Scope Z_scope.

Lemma body_shrincs_memcpy :
  semax_body Vprog Gprog f_shrincs_memcpy shrincs_memcpy_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.

  (* Recover [Zlength contents = n] from the source [data_at]. *)

  assert_PROP (Zlength contents = n) as Hlen by (entailer!; list_solve).

  (* ===== Convert [memory_block] on dst to [data_at_] over uchars ===== *)

  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.

  (* ===== Cast d and s to (uint8_t ptr) ===== *)

  (* d = (uint8_t ptr) dst *)
  forward.
  (* s = (const uint8_t ptr) src *)
  forward.

  (* ===== Main loop: byte-wise copy ===== *)

  forward_for_simple_bound n
    (EX i : Z,
      PROP ()
      LOCAL (temp _d p; temp _s q; temp _dst p; temp _src q;
             temp _n (Vlong (Int64.repr n)))
      SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
           data_at psh (tarray tuchar n)
             (sublist 0 i (map Vint contents) ++
              Zrepeat Vundef (n - i)) p)).

  (* Loop entry: i = 0 *)

  - rewrite data_at__tarray, sublist_nil, app_nil_l, Z.sub_0_r.
    change (default_val tuchar) with Vundef.
    entailer!.

  (* Loop body: read s[i] into _t'1, then write d[i] *)

  - (* The load needs [s[i]] byte-ranged; extract that from the
       [value_fits] fact carried by the source [data_at]. *)
    assert_PROP (Forall (value_fits tuchar) (map Vint contents))
      as Hfit by entailer!.
    assert (Hrng : 0 <= Int.unsigned (Znth i contents) <= Byte.max_unsigned).
    { pose proof (proj1 (Forall_Znth _ _) Hfit i
                    ltac:(rewrite Zlength_map; lia)) as Hfit_i.
      rewrite Znth_map in Hfit_i by lia.
      rewrite value_fits_eq in Hfit_i.
      simpl in Hfit_i.
      specialize (Hfit_i ltac:(discriminate)).
      simpl in Hfit_i.
      rep_lia. }

    (* _t'1 = s[i] *)
    forward.
    (* d[i] = _t'1 *)
    forward.

    (* Re-establish the invariant at i+1: the [upd_Znth] extends the
       copied prefix by one byte. *)
    entailer!.
    apply derives_refl'.
    f_equal.
    list_solve.

  (* ===== Loop exit: collapse to [map Vint contents] ===== *)

  - rewrite sublist_same, Z.sub_diag, Zrepeat_0, app_nil_r
      by (rewrite ?Zlength_map; lia).

    (* ===== Return [dst] ===== *)

    forward.
Qed.
