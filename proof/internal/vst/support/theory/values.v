(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * theory.values: the C values of words and byte strings

    The specification computes with machine words and tuples of bytes. The C computes with [Int.int] and [Int64.int] and stores one [unsigned char] at a time. This file is the dictionary between the two at the level of single values and of lists of values: no memory predicate appears in it.

    Three groups. Ranges of [wunsigned], which is all [lia] needs to know about a word. The list algebra of [vals], so a floyd list lemma applies to a byte string of the specification. And the byte a C expression stores when it narrows a shifted integer, as a remainder modulo 256, which is also what [wunsigned (wrepr U8 _)] is. *)

From Shrincs.internal.vst.support Require Import base settings.
From Shrincs.internal.vst.support.repr Require Import seqlist.
From Shrincs.internal.vst.support Require Import contract.helpers.
From Shrincs.internal.vst Require Import shape.
(* MathComp last: every file above re-exports floyd, whose [seq] is Stdlib's list of naturals. Single files, and not [boot]: [boot] exports the ssreflect tactic language, which takes [rewrite ... by ...] away. [ssralg] is there for the coercion from a ring to its carrier, which a word type needs. *)
From mathcomp Require Import ssrbool ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Ranges *)

Lemma wunsigned_u8_range (x : UInt8) : 0 <= wunsigned x < 256.
Proof. exact (wunsigned_range x). Qed.

Lemma wunsigned_u16_range (x : UInt16) : 0 <= wunsigned x < 65536.
Proof. exact (wunsigned_range x). Qed.

Lemma wunsigned_u32_range (x : UInt32) : 0 <= wunsigned x < 4294967296.
Proof. exact (wunsigned_range x). Qed.

Lemma wunsigned_u64_range (x : UInt64) : 0 <= wunsigned x < 18446744073709551616.
Proof. exact (wunsigned_range x). Qed.

Lemma wunsigned_wrepr_u8 (z : Z) : wunsigned (wrepr U8 z) = z mod 256.
Proof. exact (wunsigned_repr U8 z). Qed.

(* ================================================================= *)
(** ** [vals] as a list *)

#[export] Instance Inhabitant_u8 : Inhabitant UInt8 := uint U8 0.

Lemma vals_cat (x y : seq UInt8) : vals (cat x y) = app (vals x) (vals y).
Proof.
unfold vals.
rewrite <- catE.
apply List.map_app.
Qed.

Lemma Zlength_vals (x : seq UInt8) : Zlength (vals x) = Zlength x.
Proof. apply Zlength_map. Qed.

Lemma Zlength_tuple (n : nat) (x : Bytes n) : Zlength (tval x) = Z.of_nat n.
Proof.
rewrite Zlength_size.
rewrite size_tuple.
reflexivity.
Qed.

Lemma Zlength_cat (x y : seq UInt8) : Zlength (cat x y) = Zlength x + Zlength y.
Proof.
rewrite <- catE.
apply Zlength_app.
Qed.

Lemma Zlength_rcons (x : seq UInt8) (b : UInt8) : Zlength (rcons x b) = Zlength x + 1.
Proof.
rewrite <- (cats1 x b).
rewrite Zlength_cat.
reflexivity.
Qed.

(** The length of a concatenation of tuples, as a number. *)
Ltac bytes_length :=
  rewrite ?Zlength_rcons, ?Zlength_cat, ?Zlength_tuple;
  try reflexivity;
  rep_lia.

Lemma sublist_vals (lo hi : Z) (x : seq UInt8) :
  sublist lo hi (vals x) = vals (sublist lo hi x).
Proof.
unfold vals.
rewrite sublist_map.
reflexivity.
Qed.

(** Stated for any default value: floyd reads an array cell with the default of the C type, which is not the default a [list val] gets on its own. *)
Lemma Znth_vals (d : Inhabitant Values.val) (i : Z) (x : seq UInt8) :
  0 <= i < Zlength x ->
  @Znth Values.val d i (vals x) = Vint (Int.repr (wunsigned (Znth i x))).
Proof.
intros Hi.
unfold Znth.
destruct (Z_lt_dec i 0) as [Hneg|_].
- lia.
- unfold vals.
  rewrite (List.nth_indep _ d (Vint (Int.repr (wunsigned (uint U8 0))))).
  + exact (List.map_nth (fun b : UInt8 => Vint (Int.repr (wunsigned b))) x (uint U8 0)
             (Z.to_nat i)).
  + rewrite List.length_map.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma Znth_seq_nth (i : Z) (x : seq UInt8) :
  0 <= i -> Znth i x = nth (uint U8 0) x (Z.to_nat i).
Proof.
intros Hi.
unfold Znth.
destruct (Z_lt_dec i 0) as [Hneg|_].
- lia.
- symmetry.
  apply nth_seq_list.
Qed.

(** A whole tuple, as the window a copy of all of it reads. *)
Lemma sublist_tuple (n : nat) (x : Bytes n) (hi : Z) :
  hi = Z.of_nat n -> sublist 0 hi (tval x) = tval x.
Proof.
intros Hhi.
apply sublist_same.
- reflexivity.
- rewrite Zlength_tuple.
  exact Hhi.
Qed.

(** A window of a byte string is the specification's [slice] of it. *)
Lemma sublist_slice (x : seq UInt8) (lo hi : Z) :
  0 <= lo <= hi -> hi <= Zlength x ->
  sublist lo hi x = tval (slice x (Z.to_nat lo) (Z.to_nat (hi - lo))).
Proof.
intros Hlo Hhi.
rewrite slice_take_drop.
- replace hi with (lo + (hi - lo)) at 1 by lia.
  apply sublist_take_drop.
  + lia.
  + lia.
- apply (introT leP).
  rewrite Zlength_size in Hhi.
  rewrite <- plusE.
  lia.
Qed.

(** The memory clauses of [Shrincs.contracts], as the [data_at] floyd works on. *)
Ltac open_rep :=
  unfold at_, space_for;
  cbn [rep_type rep_val rep_bytes rep_option];
  change (Z.of_nat 16) with 16;
  change (Z.of_nat 32) with 32;
  change (Z.of_nat (2 + WOTS_C_CHAINS_SIZE)) with 514.

(** An array filled with sixteen-byte blocks, after [k] of them. *)
Lemma Zlength_blocks (f : nat -> seq UInt8) (k : Z) :
  (forall i : nat, Zlength (f i) = 16) -> 0 <= k ->
  Zlength (blocks f (Z.to_nat k)) = 16 * k.
Proof.
intros Hf Hk.
rewrite Zlength_size.
rewrite (@size_blocks f 16%nat).
- rewrite <- multE.
  lia.
- intros i.
  apply Nat2Z.inj.
  rewrite <- Zlength_size.
  exact (Hf i).
Qed.

Lemma blocks_step (f : nat -> seq UInt8) (k : Z) :
  0 <= k -> blocks f (Z.to_nat (k + 1)) = cat (blocks f (Z.to_nat k)) (f (Z.to_nat k)).
Proof.
intros Hk.
replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
apply blocksS.
Qed.

(** The premises a call on a buffer leaves: lengths of byte strings, the window a copy reads, and bounds. [forward_call] discharges some of the conjuncts itself, and which ones depends on the hypotheses in scope, so this takes whatever conjunction is left. *)
Ltac bytes_side_condition :=
  lazymatch goal with
  | |- Zlength _ = _ => bytes_length
  | |- sublist 0 _ (tval ?x) = tval ?x => apply sublist_tuple; reflexivity
  | |- sublist ?lo ?hi ?x = _ =>
      apply (sublist_slice x lo hi); [ lia | rewrite ?Zlength_tuple; rep_lia ]
  | |- _ => rep_lia
  end.

Ltac bytes_side_conditions :=
  repeat match goal with |- _ /\ _ => split end;
  bytes_side_condition.

(** The two shapes the contracts of [src/util.c] and [src/sha256.c] ask for. *)
Lemma vals_ints (x : seq UInt8) :
  vals x = List.map Vint (List.map (fun b : UInt8 => Int.repr (wunsigned b)) x).
Proof.
unfold vals.
rewrite List.map_map.
reflexivity.
Qed.

Lemma vals_bytes (x : seq UInt8) :
  vals x = List.map Vubyte (List.map (fun b : UInt8 => Byte.repr (wunsigned b)) x).
Proof.
unfold vals.
rewrite List.map_map.
apply List.map_ext.
intros b.
unfold Vubyte.
rewrite Byte.unsigned_repr.
- reflexivity.
- pose proof (wunsigned_u8_range b) as Hb.
  rep_lia.
Qed.

(** A byte of a byte string is a well-typed [unsigned char]. *)
Lemma tc_val_Znth_vals (d : Inhabitant Values.val) (i : Z) (x : seq UInt8) :
  0 <= i < Zlength x -> tc_val tuchar (@Znth Values.val d i (vals x)).
Proof.
intros Hi.
rewrite Znth_vals by exact Hi.
pose proof (wunsigned_u8_range (Znth i x)) as Hb.
simpl.
rewrite Int.unsigned_repr by rep_lia.
rep_lia.
Qed.

(* ================================================================= *)
(** ** [index_vals] as a list *)

Lemma Zlength_index_vals (indexes : seq nat) : Zlength (index_vals indexes) = Zlength indexes.
Proof. apply Zlength_map. Qed.

Lemma Zlength_base_2b (x : seq UInt8) (b outlen : nat) :
  Zlength (base_2b x b outlen) = Z.of_nat outlen.
Proof.
rewrite Zlength_size.
rewrite size_base_2b.
reflexivity.
Qed.

Lemma Znth_index_vals (d : Inhabitant Values.val) (i : Z) (indexes : seq nat) :
  0 <= i < Zlength indexes ->
  @Znth Values.val d i (index_vals indexes)
  = Vint (Int.repr (Z.of_nat (nth 0%nat indexes (Z.to_nat i)))).
Proof.
intros Hi.
unfold Znth.
destruct (Z_lt_dec i 0) as [Hneg|_].
- lia.
- unfold index_vals.
  rewrite (List.nth_indep _ d (Vint (Int.repr (Z.of_nat 0%nat)))).
  + rewrite (List.map_nth (fun k : nat => Vint (Int.repr (Z.of_nat k)))).
    rewrite <- nth_seq_list.
    reflexivity.
  + rewrite List.length_map.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

(** An index is at most 15, so it is a well-typed [unsigned char]. *)
Lemma nth_indexes_Z_le (hashed : Bytes 16) (m : nat) :
  Z.of_nat (nth 0%nat (base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) m) <= 15.
Proof.
pose proof (nth_indexes_le hashed m) as Hle.
apply (elimT leP) in Hle.
lia.
Qed.

Lemma tc_val_Znth_index_vals (d : Inhabitant Values.val) (i : Z) (indexes : seq nat) :
  0 <= i < Zlength indexes ->
  Z.of_nat (nth 0%nat indexes (Z.to_nat i)) <= 15 ->
  tc_val tuchar (@Znth Values.val d i (index_vals indexes)).
Proof.
intros Hi Hle.
rewrite Znth_index_vals by exact Hi.
simpl.
rewrite Int.unsigned_repr by rep_lia.
rep_lia.
Qed.

(** The running sum of the C loop over the indexes. *)
Lemma sumn_take_Z (indexes : seq nat) (j : Z) :
  0 <= j < Zlength indexes ->
  Z.of_nat (sumn (take (Z.to_nat (j + 1)) indexes))
  = Z.of_nat (sumn (take (Z.to_nat j) indexes)) + Z.of_nat (nth 0%nat indexes (Z.to_nat j)).
Proof.
intros Hj.
rewrite Zlength_size in Hj.
replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
rewrite sumn_take_S.
- rewrite <- plusE.
  lia.
- apply (introT ltP).
  lia.
Qed.

Lemma take_all_Z (indexes : seq nat) (n : Z) :
  Zlength indexes = n -> take (Z.to_nat n) indexes = indexes.
Proof.
intros Hn.
rewrite Zlength_size in Hn.
rewrite <- Hn.
rewrite Nat2Z.id.
apply take_size.
Qed.

(** The two cells the C fills from byte [i]: its high and its low nibble. *)
Lemma Znth_index_vals_base_2b (d : Inhabitant Values.val) (x : Bytes 16) (i : Z) :
  0 <= i < 16 ->
  let digits := index_vals (base_2b x WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) in
  @Znth Values.val d (2 * i) digits = Vint (Int.repr (wunsigned (Znth i (tval x)) / 16))
  /\ @Znth Values.val d (2 * i + 1) digits
     = Vint (Int.repr (wunsigned (Znth i (tval x)) mod 16)).
Proof.
intros Hi digits.
assert (Hlen : Zlength (base_2b x WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) = 32).
{ rewrite Zlength_size.
  rewrite size_base_2b.
  reflexivity. }
pose proof (wunsigned_u8_range (Znth i (tval x))) as Hbyte.
assert (Hlt : (Z.to_nat i < 16)%nat = true) by (apply (introT ltP); lia).
pose proof (@nth_indexes x (Z.to_nat i) Hlt) as Hnibbles.
cbv zeta in Hnibbles.
destruct Hnibbles as [Hhi Hlo].
rewrite <- (Znth_seq_nth i (tval x)) in Hhi by lia.
rewrite <- (Znth_seq_nth i (tval x)) in Hlo by lia.
assert (Heven : Z.to_nat (2 * i) = (2 * Z.to_nat i)%nat).
{ rewrite <- multE.
  lia. }
assert (Hodd : Z.to_nat (2 * i + 1) = S (2 * Z.to_nat i)%nat).
{ rewrite <- multE.
  lia. }
unfold digits.
split.
- rewrite Znth_index_vals by lia.
  rewrite Heven.
  rewrite Hhi.
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  reflexivity.
- rewrite Znth_index_vals by lia.
  rewrite Hodd.
  rewrite Hlo.
  rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** The byte a C expression stores

    A store into an [unsigned char] narrows its right-hand side with [Int.zero_ext 8], once for the cast in the source and once for the store. Each lemma below reduces one shape floyd leaves to [Int.repr (_ mod 256)]. *)

Lemma zero_ext8_repr (z : Z) : Int.zero_ext 8 (Int.repr z) = Int.repr (z mod 256).
Proof.
unfold Int.zero_ext.
rewrite Zbits.Zzero_ext_mod by lia.
rewrite Int.unsigned_repr_eq.
change (two_p 8) with 256.
rewrite Z.mod_mod_divide.
- reflexivity.
- exists 16777216.
  reflexivity.
Qed.

Lemma zero_ext8_mod256 (z : Z) : Int.zero_ext 8 (Int.repr (z mod 256)) = Int.repr (z mod 256).
Proof.
rewrite zero_ext8_repr.
rewrite Zmod_mod.
reflexivity.
Qed.

(** [(uint8_t)(x >> s)] for a 32-bit [x]. *)
Lemma zero_ext8_shru (x s : Z) :
  0 <= x < 4294967296 -> 0 <= s < 32 ->
  Int.zero_ext 8 (Int.shru (Int.repr x) (Int.repr s)) = Int.repr ((x / 2 ^ s) mod 256).
Proof.
intros Hx Hs.
unfold Int.shru.
rewrite !Int.unsigned_repr by rep_lia.
rewrite Z.shiftr_div_pow2 by lia.
apply zero_ext8_repr.
Qed.

(** [(uint8_t)(x >> s)] for a 64-bit [x], in the shape floyd leaves it. *)
Lemma zero_ext8_shru64 (x s : Z) :
  0 <= x < 18446744073709551616 -> 0 <= s < 64 ->
  Int.zero_ext 8
    (Int.repr
       (Int64.Z_mod_modulus
          (Z.shiftr (Int64.Z_mod_modulus x)
             (Int64.Z_mod_modulus (Int.unsigned (Int.repr s))))))
  = Int.repr ((x / 2 ^ s) mod 256).
Proof.
intros Hx Hs.
rewrite !Int64.Z_mod_modulus_eq.
rewrite Int.unsigned_repr by rep_lia.
change Int64.modulus with 18446744073709551616.
rewrite (Z.mod_small x) by lia.
rewrite (Z.mod_small s) by lia.
rewrite Z.shiftr_div_pow2 by lia.
rewrite zero_ext8_repr.
rewrite Z.mod_mod_divide.
- reflexivity.
- exists 72057594037927936.
  reflexivity.
Qed.

(** [(uint8_t)x] for a 64-bit [x]. *)
Lemma zero_ext8_low64 (x : Z) :
  Int.zero_ext 8 (Int.repr (Int64.Z_mod_modulus x)) = Int.repr (x mod 256).
Proof.
rewrite Int64.Z_mod_modulus_eq.
change Int64.modulus with 18446744073709551616.
rewrite zero_ext8_repr.
rewrite Z.mod_mod_divide.
- reflexivity.
- exists 72057594037927936.
  reflexivity.
Qed.

(** A byte of the specification, as the same remainder. *)
Lemma rep_val_wrepr_u8 (z : Z) :
  Vint (Int.repr (wunsigned (wrepr U8 z))) = Vint (Int.repr (z mod 256)).
Proof.
rewrite wunsigned_wrepr_u8.
reflexivity.
Qed.

(** [x << s] for a 32-bit shift below the word size is a multiplication. *)
Lemma shl_repr (x s : Z) :
  0 <= s < 32 -> Int.shl (Int.repr x) (Int.repr s) = Int.repr (x * 2 ^ s).
Proof.
intros Hs.
rewrite Int.shl_mul_two_p.
rewrite Int.unsigned_repr by rep_lia.
rewrite two_p_equiv.
rewrite mul_repr.
reflexivity.
Qed.

(* ================================================================= *)
(** ** Words the C computes *)

(** The first payload word of the PRF address, as the C computes it and as [WotsCPrf.to_bytes] defines it. *)
Lemma prf_word1 (tree_balanced : bool) (tree_depth : UInt8) :
  Int.add (Int.shl (Int.repr (Z.b2z tree_balanced)) (Int.repr 24))
          (Int.shl (Int.repr (wunsigned tree_depth)) (Int.repr 16))
  = Int.repr (wunsigned
                (wrepr U32 (Z.b2z tree_balanced * 2 ^ 24 + wunsigned tree_depth * 2 ^ 16))).
Proof.
pose proof (wunsigned_u8_range tree_depth) as Hdepth.
rewrite !shl_repr by lia.
rewrite add_repr.
f_equal.
symmetry.
apply wunsigned_repr_small.
change (wbase U32) with 4294967296.
destruct tree_balanced.
- change (Z.b2z true) with 1.
  lia.
- change (Z.b2z false) with 0.
  lia.
Qed.

(** The two bytes of [counter.to_bytes(2)], as the C stores them. *)
Lemma counter_hi_byte (counter : UInt16) :
  Int.zero_ext 8 (Int.zero_ext 8 (Int.shru (Int.repr (wunsigned counter)) (Int.repr 8)))
  = Int.repr (wunsigned (wrepr U8 (wunsigned counter / 256 ^ 1))).
Proof.
pose proof (wunsigned_u16_range counter) as Hcounter.
rewrite zero_ext8_shru by lia.
rewrite zero_ext8_mod256.
rewrite wunsigned_wrepr_u8.
reflexivity.
Qed.

Lemma counter_lo_byte (counter : UInt16) :
  Int.zero_ext 8 (Int.zero_ext 8 (Int.repr (wunsigned counter)))
  = Int.repr (wunsigned (wrepr U8 (wunsigned counter / 256 ^ 0))).
Proof.
rewrite zero_ext8_repr.
rewrite zero_ext8_mod256.
rewrite wunsigned_wrepr_u8.
change (256 ^ 0) with 1.
rewrite Z.div_1_r.
reflexivity.
Qed.

(** A [bool] argument passed on to a callee is cast to [bool] again, which normalises it to 0 or 1. It is one of the two already. Registered for floyd's normaliser, so a call that forwards a [bool] parameter matches its contract without help. *)
Lemma bool_cast_b2z (b : bool) :
  (if Int.eq (Int.repr (Z.b2z b)) Int.zero then Int.zero else Int.one) = Int.repr (Z.b2z b).
Proof. destruct b; reflexivity. Qed.

#[export] Hint Rewrite bool_cast_b2z : norm.

(** The two nibbles of a byte, as the C computes and stores them. The byte is promoted to [int], so the shift is the signed one. *)
Lemma index_hi_store (b : UInt8) :
  Int.zero_ext 8 (Int.zero_ext 8 (Int.shr (Int.repr (wunsigned b)) (Int.repr 4)))
  = Int.repr (wunsigned b / 16).
Proof.
pose proof (wunsigned_u8_range b) as Hb.
assert (Hq : 0 <= wunsigned b / 16 < 16).
{ split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia. }
rewrite Int.shr_div_two_p.
rewrite Int.signed_repr by rep_lia.
rewrite Int.unsigned_repr by rep_lia.
change (two_p 4) with 16.
rewrite zero_ext8_repr.
rewrite zero_ext8_mod256.
rewrite Z.mod_small by lia.
reflexivity.
Qed.

Lemma index_lo_store (b : UInt8) :
  Int.zero_ext 8 (Int.zero_ext 8 (Int.and (Int.repr (wunsigned b)) (Int.repr 15)))
  = Int.repr (wunsigned b mod 16).
Proof.
pose proof (wunsigned_u8_range b) as Hb.
pose proof (Z.mod_pos_bound (wunsigned b) 16 ltac:(lia)) as Hr.
rewrite and_repr.
change 15 with (Z.ones 4).
rewrite Z.land_ones by lia.
change (2 ^ 4) with 16.
rewrite zero_ext8_repr.
rewrite zero_ext8_mod256.
rewrite Z.mod_small by lia.
reflexivity.
Qed.

(** A loop counter below the word size is the word of its value. *)
Lemma wunsigned_uint_u32 (i : Z) :
  0 <= i < 4294967296 -> wunsigned (uint U32 (Z.to_nat i)) = i.
Proof.
intros Hi.
rewrite wunsigned_uint.
- apply Z2Nat.id.
  lia.
- rewrite Z2Nat.id by lia.
  exact (proj2 Hi).
Qed.

Lemma wunsigned_uint_u16 (i : Z) :
  0 <= i < 65536 -> wunsigned (uint U16 (Z.to_nat i)) = i.
Proof.
intros Hi.
rewrite wunsigned_uint.
- apply Z2Nat.id.
  lia.
- rewrite Z2Nat.id by lia.
  exact (proj2 Hi).
Qed.
