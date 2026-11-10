(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_adrs_pack: VST body proof for [shrincs_adrs_pack].

    Twenty-two byte stores, one per byte of [Address.pack]. Each stored
    byte is a narrowed shift of a parameter, and [pack_bytes] spells the
    specification's [pack] as the same twenty-two bytes, so the proof
    reduces both lists to remainders modulo 256 and compares them. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import settings contract.gprog theory.values.
From Shrincs.internal.vst Require Import shape.
From Shrincs.clight Require Import thash.
Import ListNotations.

Open Scope Z_scope.

(** Twenty-two stores into a fresh array leave exactly the stored values. *)
Lemma upd_Znth_22 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19
                     v20 v21 : val) :
  upd_Znth 21 (upd_Znth 20 (upd_Znth 19 (upd_Znth 18 (upd_Znth 17 (upd_Znth 16
    (upd_Znth 15 (upd_Znth 14 (upd_Znth 13 (upd_Znth 12 (upd_Znth 11 (upd_Znth 10
    (upd_Znth 9 (upd_Znth 8 (upd_Znth 7 (upd_Znth 6 (upd_Znth 5 (upd_Znth 4
    (upd_Znth 3 (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (default_val (tarray tuchar 22))
    v0) v1) v2) v3) v4) v5) v6) v7) v8) v9) v10) v11) v12) v13) v14) v15) v16) v17) v18)
    v19) v20) v21
  = [v0; v1; v2; v3; v4; v5; v6; v7; v8; v9; v10; v11; v12; v13; v14; v15; v16; v17; v18;
     v19; v20; v21].
Proof. reflexivity. Qed.

Lemma body_shrincs_adrs_pack :
  semax_body Vprog Gprog_thash f_shrincs_adrs_pack shrincs_adrs_pack_spec.
Proof.
  start_function.
  pose proof (wunsigned_u64_range index) as Hindex.
  pose proof (wunsigned_u32_range word1) as Hword1.
  pose proof (wunsigned_u32_range word2) as Hword2.
  pose proof (wunsigned_u32_range word3) as Hword3.

  (* addr[0] = height *)
  forward.
  (* addr[1 .. 9) = index, big-endian *)
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  (* addr[9] = address_type *)
  forward.
  (* addr[10 .. 14) = word1, big-endian *)
  forward.
  forward.
  forward.
  forward.
  (* addr[14 .. 18) = word2, big-endian *)
  forward.
  forward.
  forward.
  forward.
  (* addr[18 .. 22) = word3, big-endian *)
  forward.
  forward.
  forward.
  forward.

  (* ===== Both sides as twenty-two remainders modulo 256 ===== *)
  rewrite upd_Znth_22.
  rewrite pack_bytes.
  unfold vals.
  cbn [List.map rep_val rep_u8].
  rewrite !wunsigned_wrepr_u8.
  rewrite !zero_ext8_shru64 by (first [exact Hindex | lia]).
  rewrite !zero_ext8_low64.
  rewrite !zero_ext8_shru by (first [assumption | lia]).
  rewrite !zero_ext8_repr.
  rewrite !Zmod_mod.
  change (256 ^ 0) with 1.
  rewrite !Z.div_1_r.
  entailer!.
Qed.
