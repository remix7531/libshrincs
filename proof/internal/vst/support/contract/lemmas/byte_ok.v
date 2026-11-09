(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.byte_ok: facts about [byte]'s VST bridge.

    [Int.repr] injectivity on [byte] and the unconditional [mod 256]
    no-op, both genuinely needed by [contract.lemmas.shrincs_wots_verify]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.public.

Open Scope Z_scope.

(** [Int.repr] is injective on [byte]s (always in [[0, 256)], so
    always in [Int]'s representable range). *)
Lemma Int_repr_inj_byte : forall x y : byte, Int.repr x = Int.repr y -> x = y.
Proof.
  intros x y Heq.
  apply byte_eq.
  apply (f_equal Int.unsigned) in Heq.
  pose proof (byte_val_range x); pose proof (byte_val_range y).
  rewrite !Int.unsigned_repr in Heq by rep_lia.
  exact Heq.
Qed.

Lemma byte_mod256_id : forall x : byte, (x : Z) mod 256 = x.
Proof. intros x. apply Z.mod_small, byte_val_range. Qed.
