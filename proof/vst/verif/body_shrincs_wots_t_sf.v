(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_wots_t_sf: VST body proof for [shrincs_wots_t_sf]. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.gprog contract.lemmas.
Import ListNotations.
Open Scope Z_scope.

(** [t_sf] is now a thin wrapper: it just calls the shared tweakable hash
    [shrincs_thash(out, pk_seed, addr, ends, 512)] over the [len * n = 512]
    concatenated chain tips.  The port spells [T_sf] and [F] separately
    (as the spec does) but they are the same construction, so the
    generalized [shrincs_thash_spec] discharges the whole body. *)
Lemma body_shrincs_wots_t_sf : semax_body Vprog Gprog f_shrincs_wots_t_sf shrincs_wots_t_sf_spec.
Proof.
  start_function.
  unfold n_bytes in *.
  change (Z.of_nat (len * n)) with 512 in *.
  change (Z.of_nat n) with 16 in *.
  (* shrincs_thash(out, pk_seed, addr, ends, 512) *)
  forward_call (out_ptr, ps_ptr, a_ptr, e_ptr, 512, A, pk_seed, ends,
                sh_o, sh_ps, sh_a, sh_e).
  (* [T_sf] and the callee's [F] are convertible (model/PORTING.md). *)
  change (shrincs.T_sf pk_seed (adrs_bytes A) ends)
    with (shrincs.F pk_seed (adrs_bytes A) ends).
  entailer!!.
Qed.
