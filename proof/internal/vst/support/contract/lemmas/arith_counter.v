(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.arith_counter: 2-byte big-endian counter reassembly.

    VST bridges for the grinding counter's shift/or store: [Int.zero_ext 8]
    byte extraction, big-endian halfword reassembly, and the [upd_Znth] shape
    lemmas the counter-store body proof needs.  The pure-Z [to_byte] facts
    these build on live in [theory.pure] (imported below). *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.data_at.
From Vst Require Import theory.pure.

Open Scope Z_scope.

(* ================================================================= *)
(** ** 2-byte big-endian counter shift/or reassembly. *)

(** The two big-endian bytes reassembled by shift/or (as clightgen emits the
    [| << ] chain in [shrincs_wots_pubkey_from_sig]) equal their weighted sum. *)
Lemma bytes_be_to_halfword : forall b0 b1 : Z,
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Int.or (Int.shl (Int.repr b0) (Int.repr 8)) (Int.repr b1)
  = Int.repr (b0 * 2 ^ 8 + b1).
Proof.
  intros b0 b1 Hb0 Hb1.
  assert (S: forall b k, 0 <= k < 32 ->
             Int.shl (Int.repr b) (Int.repr k) = Int.repr (b * 2^k)).
  { intros b k Hk.
    rewrite Int.shl_mul_two_p.
    rewrite Int.unsigned_repr by rep_lia.
    rewrite two_p_equiv.
    rewrite mul_repr.
    reflexivity. }
  rewrite (S b0 8) by lia.
  rewrite or_repr.
  f_equal.
  assert (disj: forall x y, Z.land x y = 0 -> Z.lor x y = x + y).
  { intros x y Hxy. pose proof (Z.add_lor_land x y). lia. }
  assert (LAND: forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> (2 ^ k | b) ->
                Z.land a b = 0).
  { intros a b k Hk [Ha0 Hak] [m Hm]. subst b.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hlt|Hge].
    - rewrite (Z.mul_pow2_bits_low m k i Hlt). apply andb_false_r.
    - rewrite (Zbits.Ztestbit_above (Z.to_nat k) a i).
      + apply andb_false_l.
      + rewrite two_power_nat_two_p, two_p_equiv, Z2Nat.id by lia. lia.
      + rewrite Z2Nat.id by lia. lia. }
  assert (L1: Z.land (b0*2^8) b1 = 0).
  { rewrite Z.land_comm. apply (LAND b1 (b0*2^8) 8).
    - lia.
    - change (2^8) with 256. lia.
    - exists b0. ring. }
  rewrite (disj _ _ L1).
  ring.
Qed.

Lemma zero_ext_shru_byte : forall (v k : Z),
  k = 0 \/ k = 8 \/ k = 16 \/ k = 24 ->
  Vint (Int.zero_ext 8 (Int.shru (Int.repr v) (Int.repr k))) =
  Vubyte (Byte.repr ((v / 2^k) mod 256)).
Proof.
  intros v k Hk.

  assert (Hrng : 0 <= k <= 24)
    by (destruct Hk as [H|[H|[H|H]]]; lia).
  unfold Vubyte.
  f_equal.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  rewrite Zmod_mod.
  unfold Int.zero_ext.
  rewrite Zbits.Zzero_ext_mod by lia.
  change (two_p 8) with 256.
  unfold Int.shru.
  rewrite !Int.unsigned_repr_eq.
  change Int.modulus with (2^32).

  assert (Hkmod : k mod 2^32 = k) by (apply Zmod_small; lia).
  rewrite Hkmod.
  rewrite Z.shiftr_div_pow2 by lia.

  assert (Hlt : (v mod 2^32) / 2^k < 2^32).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    apply Z.lt_le_trans with (2^32); [apply Z.mod_pos_bound; lia|].
    rewrite <- (Z.mul_1_l (2^32)) at 1.
    apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia|].
    destruct Hk as [Hc|[Hc|[Hc|Hc]]]; lia. }
  assert (Hge : 0 <= (v mod 2^32) / 2^k).
  { apply Z.div_pos; [apply Z.mod_pos_bound; lia | apply Z.pow_pos_nonneg; lia]. }

  rewrite (Zmod_small _ (2^32)) by lia.
  apply Int.eqm_samerepr.
  unfold Int.eqm, Zbits.eqmod.
  exists 0.
  rewrite Z.mul_0_l, Z.add_0_l.
  apply div_mod256_mod2pow32.
  exact Hk.
Qed.

Lemma zero_ext_byte : forall (v : Z),
  Vint (Int.zero_ext 8 (Int.repr v)) = Vubyte (Byte.repr (v mod 256)).
Proof.
  intros v.
  replace (Int.repr v) with (Int.shru (Int.repr v) (Int.repr 0))
    by (rewrite Int.shru_zero; reflexivity).
  rewrite zero_ext_shru_byte by auto.
  rewrite Z.pow_0_r, Z.div_1_r.
  reflexivity.
Qed.

(** The two big-endian counter bytes assembled by a
    [buf[k] = (uint8_t)(counter >> 8); buf[k+1] = (uint8_t)(counter >> 0)]
    store pair equal [block_to_vals (to_byte counter 2)].  The low byte
    carries the explicit [>> 0] shift ([shrincs_wots_h_grind]'s store shape). *)
Lemma counter_bytes_eq : forall counter,
  0 <= counter < 2 ^ 16 ->
  [Vint (Int.zero_ext 8 (Int.shru (Int.repr counter) (Int.repr 8)));
   Vint (Int.zero_ext 8 (Int.shru (Int.repr counter) (Int.repr 0)))]
  = block_to_vals (to_byte counter 2).
Proof.
  intros counter Hcounter.
  rewrite to_byte_2_eq.
  unfold block_to_vals. simpl map.
  rewrite (zero_ext_shru_byte counter 8) by auto.
  rewrite (zero_ext_shru_byte counter 0) by auto.
  change (2 ^ 8) with 256.
  change (2 ^ 0) with 1. rewrite Z.div_1_r.
  reflexivity.
Qed.

(** Plain-low-byte twin of [counter_bytes_eq]: the low byte is a bare
    [(uint8_t)counter] cast (no shift), hence [Int.repr counter] rather
    than [Int.shru _ 0] ([shrincs_wots_sign]'s store shape). *)
Lemma counter_bytes_eq' : forall counter,
  0 <= counter < 2 ^ 16 ->
  [Vint (Int.zero_ext 8 (Int.shru (Int.repr counter) (Int.repr 8)));
   Vint (Int.zero_ext 8 (Int.repr counter))]
  = block_to_vals (to_byte counter 2).
Proof.
  intros counter Hcounter.
  rewrite to_byte_2_eq.
  unfold block_to_vals. simpl map.
  rewrite (zero_ext_shru_byte counter 8) by auto.
  rewrite zero_ext_byte.
  change (2 ^ 8) with 256.
  reflexivity.
Qed.


