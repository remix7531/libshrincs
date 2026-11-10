(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.shape: the loops of Shrincs.spec in closed form

    Shrincs.spec transcribes the Python loop by loop. The security model states the same algorithms by recursion over lists. This file holds the facts about the specification alone that relate the two shapes: the first hit of a search, the base-16 digits of a byte string, slices of a concatenation, and the layout of a signature. Nothing here mentions a game or the model. *)

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.
From Shrincs Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*  Searches  *)

(* A loop that returns on its first hit is the head of a filter. *)
Lemma for_first_filter (A B : Type) (p : A -> bool) (g : A -> B) (s : seq A) :
  for_first (fun x => if p x then Some (g x) else None) s = omap g (ohead (filter p s)).
Proof. by elim: s => [|x s IH] //=; case: (p x). Qed.

(*  Integers  *)

Section Integers.
Local Open Scope Z_scope.

Lemma Z_of_nat_expn2 (n : nat) : Z.of_nat (2 ^ n)%nat = 2 ^ Z.of_nat n.
Proof.
elim: n => [|n IH] //.
rewrite expnS Znat.Nat2Z.inj_mul IH [in RHS]Znat.Nat2Z.inj_succ Z.pow_succ_r //.
exact: Znat.Nat2Z.is_nonneg.
Qed.

(* A word that came from a natural number goes back to it. *)
Lemma uint_to_nat (ws : wsize) (w : word ws) : uint ws (Z.to_nat (wunsigned w)) = w.
Proof.
have [h0 _] := wunsigned_range w.
by rewrite /uint Znat.Z2Nat.id // wrepr_unsigned.
Qed.

Lemma to_nat_uint16 (c : nat) : (c < 2 ^ 16)%nat -> Z.to_nat (wunsigned (uint U16 c)) = c.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt; rewrite Z_of_nat_expn2 => hc.
rewrite /uint wunsigned_repr_small ?Znat.Nat2Z.id //.
by split; [exact: Znat.Nat2Z.is_nonneg | exact: hc].
Qed.

Lemma uint32_inj (i j : nat) :
  (i < 2 ^ 32)%nat -> (j < 2 ^ 32)%nat -> uint U32 i = uint U32 j -> i = j.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt hi /ltP /Znat.Nat2Z.inj_lt hj /(congr1 (@wunsigned U32)).
rewrite Z_of_nat_expn2 in hi; rewrite Z_of_nat_expn2 in hj.
rewrite /uint !wunsigned_repr_small; try by split; [exact: Znat.Nat2Z.is_nonneg|].
exact: Znat.Nat2Z.inj.
Qed.

(* The two-byte big-endian rendering of a 16 bit word reads back as the word. *)
Lemma int_from_to_bytes_2 (w : word U16) : int_from_bytes U16 (int_to_bytes w 2) = w.
Proof.
rewrite -[RHS]wrepr_unsigned /int_from_bytes; congr wrepr.
have [h0 h1] := wunsigned_range w.
change (wbase U16) with 65536 in h1.
change (tval (int_to_bytes w 2))
  with [:: wrepr U8 (wunsigned w / 256); wrepr U8 (wunsigned w / 1)].
cbn [foldl].
rewrite !wunsigned_repr.
change (modulus (wsize_size_minus_1 U8).+1) with 256.
move: (wunsigned w) h0 h1 => z h0 h1.
rewrite Z.div_1_r Z.mul_0_l Z.add_0_l (Z.mod_small (z / 256)).
  by split; [apply: Z.div_pos; lia | apply: Z.div_lt_upper_bound; lia].
by rewrite Z.mul_comm -Z.div_mod.
Qed.

(* Four bytes read as a 32 bit word retain every byte when written back. *)
Lemma int_to_from_bytes_4 (x : Bytes 4) :
  int_to_bytes (int_from_bytes U32 x) 4 = x.
Proof.
case/tupleP: x => b0 x.
case/tupleP: x => b1 x.
case/tupleP: x => b2 x.
case/tupleP: x => b3 x.
rewrite (tuple0 x).
have h0 := wunsigned_range b0.
have h1 := wunsigned_range b1.
have h2 := wunsigned_range b2.
have h3 := wunsigned_range b3.
change (wbase U8) with 256 in h0, h1, h2, h3.
set z := ((wunsigned b0 * 256 + wunsigned b1) * 256 + wunsigned b2) * 256 + wunsigned b3.
have hz : 0 <= z < wbase U32.
  change (wbase U32) with 4294967296.
  rewrite /z; lia.
have hword : wunsigned (int_from_bytes U32 [tuple b0; b1; b2; b3]) = z.
  change (wunsigned (wrepr U32 z) = z).
  exact: (wunsigned_repr_small hz).
have hd0 : z / 16777216 = wunsigned b0.
  symmetry; apply: (Z.div_unique_pos _ _ _
    ((wunsigned b1 * 256 + wunsigned b2) * 256 + wunsigned b3)); rewrite /z; lia.
have hd1 : z / 65536 = wunsigned b0 * 256 + wunsigned b1.
  symmetry; apply: (Z.div_unique_pos _ _ _ (wunsigned b2 * 256 + wunsigned b3)); rewrite /z; lia.
have hd2 : z / 256 = (wunsigned b0 * 256 + wunsigned b1) * 256 + wunsigned b2.
  symmetry; apply: (Z.div_unique_pos _ _ _ (wunsigned b3)); rewrite /z; lia.
have hm1 : (wunsigned b0 * 256 + wunsigned b1) mod 256 = wunsigned b1.
  symmetry; apply: (Z.mod_unique_pos _ _ (wunsigned b0)); lia.
have hm2 : ((wunsigned b0 * 256 + wunsigned b1) * 256 + wunsigned b2) mod 256 = wunsigned b2.
  symmetry; apply: (Z.mod_unique_pos _ _ (wunsigned b0 * 256 + wunsigned b1)); lia.
have hm3 : z mod 256 = wunsigned b3.
  symmetry; apply: (Z.mod_unique_pos _ _ ((wunsigned b0 * 256 + wunsigned b1) * 256 + wunsigned b2)); rewrite /z; lia.
apply: val_inj.
change ([:: wrepr U8 (wunsigned (int_from_bytes U32 [tuple b0; b1; b2; b3]) / 16777216);
            wrepr U8 (wunsigned (int_from_bytes U32 [tuple b0; b1; b2; b3]) / 65536);
            wrepr U8 (wunsigned (int_from_bytes U32 [tuple b0; b1; b2; b3]) / 256);
            wrepr U8 (wunsigned (int_from_bytes U32 [tuple b0; b1; b2; b3]) / 1)]
  = [:: b0; b1; b2; b3]).
rewrite hword hd0 hd1 hd2 Z.div_1_r.
congr [:: _; _; _; _].
- exact: wrepr_unsigned.
- apply: wunsigned_inj; rewrite wunsigned_repr.
  change (modulus (wsize_size_minus_1 U8).+1) with 256.
  exact: hm1.
- apply: wunsigned_inj; rewrite wunsigned_repr.
  change (modulus (wsize_size_minus_1 U8).+1) with 256.
  exact: hm2.
- apply: wunsigned_inj; rewrite wunsigned_repr.
  change (modulus (wsize_size_minus_1 U8).+1) with 256.
  exact: hm3.
Qed.

End Integers.

(* A bound below 2^k for k at most 32 is a bound below 2^32, with no power computed. *)
Lemma ltn_2_32 (i k : nat) : k <= 32 -> i < 2 ^ k -> i < 2 ^ 32.
Proof. by move=> hk hi; apply: (leq_trans hi); rewrite leq_exp2l. Qed.

(*  Base-16 digits  *)

Definition byte_val (b : UInt8) : nat := Z.to_nat (wunsigned b).

Lemma byte_val_lt (b : UInt8) : byte_val b < 256.
Proof.
rewrite /byte_val; have [h0 h1] := wunsigned_range b.
change (wbase U8) with 256%Z in h1.
apply/ltP; lia.
Qed.

Lemma byte_val_inj : injective byte_val.
Proof.
move=> a b h; apply: wunsigned_inj.
have [ha _] := wunsigned_range a; have [hb _] := wunsigned_range b.
exact: Znat.Z2Nat.inj.
Qed.

(* The high and the low half of every byte, in order. *)
Definition nibbles (x : seq UInt8) : seq nat :=
  flatten [seq [:: byte_val b %/ 16; byte_val b %% 16] | b <- x].

Lemma size_nibbles (x : seq UInt8) : size (nibbles x) = (size x).*2.
Proof. by rewrite /nibbles; elim: x => [|b x IH] //=; rewrite IH. Qed.

Lemma nibbles_lt (x : seq UInt8) : all (fun d => d < 16) (nibbles x).
Proof.
rewrite /nibbles; elim: x => [|b x IH] //=.
rewrite ltn_pmod // IH !andbT.
by rewrite ltn_divLR // (byte_val_lt b).
Qed.

Lemma nibbles_inj : injective nibbles.
Proof.
elim=> [|a s IH] [|b t] //= [h1 h2 h3].
congr (_ :: _); last exact: IH.
apply: byte_val_inj.
by rewrite (divn_eq (byte_val a) 16) h1 h2 -divn_eq.
Qed.

(* One iteration of base_2b's outer loop, with the byte values abstracted so that the loop can be run on a symbolic state. *)
Definition base_2b_step (v : nat -> nat) (b : nat) :=
  fun '(baseb, j, acc, bits_filled) i =>
    let: (j, acc, bits_filled) :=
      while b (fun '(_, _, bits_filled) => bits_filled < b)
        (fun '(j, acc, bits_filled) => (j + 1, acc * 2 ^ 8 + v j, bits_filled + 8))
        (j, acc, bits_filled) in
    let bits_filled := bits_filled - b in
    (set_nth 0 baseb i (acc %/ 2 ^ bits_filled), j, acc %% 2 ^ bits_filled, bits_filled).

Lemma base_2bE (x : seq UInt8) (b outlen : nat) :
  base_2b x b outlen
  = (let: (baseb, _, _, _) :=
       foldl (base_2b_step (fun j => byte_val (nth (uint U8 0) x j)) b)
         (nseq outlen 0, 0, 0, 0) (iota 0 outlen) in baseb).
Proof. by []. Qed.

(* At four bits, two iterations consume one byte and leave the accumulator empty. *)
Lemma base_2b_step_pair (v : nat -> nat) (bs : seq nat) (k i : nat) :
  foldl (base_2b_step v 4) (bs, k, 0, 0) [:: i; i.+1]
  = (set_nth 0 (set_nth 0 bs i (v k %/ 16)) i.+1 (v k %% 16), k.+1, 0, 0).
Proof.
rewrite /= /base_2b_step /=.
by rewrite mul0n !add0n addn1 -[8 - 4]/4 subnn expn0 divn1 modn1 -[2 ^ 4]/16.
Qed.

Lemma set_nth_cat_head (pre : seq nat) (y : nat) (rest : seq nat) (a : nat) :
  set_nth 0 (pre ++ y :: rest) (size pre) a = pre ++ a :: rest.
Proof. by elim: pre => [|x pre IH] //=; rewrite IH. Qed.

Lemma base_2b_foldl (v : nat -> nat) (r : nat) (pre : seq nat) (k : nat) :
  foldl (base_2b_step v 4) (pre ++ nseq r.*2 0, k, 0, 0) (iota (size pre) r.*2)
  = (pre ++ flatten [seq [:: v j %/ 16; v j %% 16] | j <- iota k r], k + r, 0, 0).
Proof.
elim: r pre k => [|r IH] pre k; first by rewrite /= cats0 addn0.
rewrite doubleS.
rewrite -[iota (size pre) r.*2.+2]/([:: size pre; (size pre).+1] ++ iota (size pre).+2 r.*2).
rewrite foldl_cat base_2b_step_pair.
rewrite -[nseq r.*2.+2 0]/(0 :: 0 :: nseq r.*2 0).
rewrite set_nth_cat_head -cat_rcons -(size_rcons pre (v k %/ 16)) set_nth_cat_head.
rewrite -cat_rcons -(size_rcons (rcons pre (v k %/ 16)) (v k %% 16)) IH.
by rewrite /= !cat_rcons addSn addnS.
Qed.

(* base_2b at four bits, asked for two digits per byte, is the nibble split. *)
Lemma base_2b_nibbles (x : seq UInt8) : base_2b x 4 (size x).*2 = nibbles x.
Proof.
rewrite base_2bE (base_2b_foldl _ (size x) [::] 0) /nibbles.
rewrite -[X in _ = flatten [seq _ | b <- X]](mkseq_nth (uint U8 0) x) /mkseq -map_comp.
by [].
Qed.

(*  Slices  *)

Lemma nth_slice (x : seq UInt8) (a n i : nat) :
  i < n -> nth (uint U8 0) (slice x a n) i = nth (uint U8 0) x (a + i).
Proof. by move=> hi; rewrite /= (nth_map 0) ?size_iota // nth_iota. Qed.

Lemma slice_cat (x : seq UInt8) (start n m : nat) :
  tval (slice x start (n + m))
  = slice x start n ++ slice x (start + n) m.
Proof. by rewrite /slice /= iotaD map_cat. Qed.

Lemma slice_all (n : nat) (t : Bytes n) : slice t 0 n = t.
Proof.
apply: val_inj; rewrite /= -[X in iota 0 X](size_tuple t).
exact: mkseq_nth.
Qed.

Lemma slice_slice (x : seq UInt8) (a n b m : nat) :
  b + m <= n -> slice (slice x a n) b m = slice x (a + b) m.
Proof.
move=> hbm; apply: val_inj; rewrite /= iotaDl -map_comp.
apply/eq_in_map => j; rewrite mem_iota => /andP[_ hj] /=.
by rewrite (nth_map 0) ?size_iota ?nth_iota ?(leq_trans hj hbm).
Qed.

Lemma slice_cat_head (n : nat) (a : Bytes n) (b : seq UInt8) : slice (a ++ b) 0 n = a.
Proof.
apply: val_inj; apply: (@eq_from_nth _ (uint U8 0)); first by rewrite !size_tuple.
move=> i; rewrite size_tuple => hi.
by rewrite nth_slice // add0n nth_cat size_tuple hi.
Qed.

Lemma slice_cat_tail (n : nat) (a : Bytes n) (b : seq UInt8) (s m : nat) :
  slice (a ++ b) (n + s) m = slice b s m.
Proof.
apply: val_inj; rewrite /= iotaDl -map_comp.
by apply/eq_map => j /=; rewrite nth_cat size_tuple ltnNge leq_addr /= addKn.
Qed.

Lemma nth_flatten_rows (n : nat) (bs : seq (Bytes n)) (i j : nat) :
  j < n ->
  nth (uint U8 0) (flatten [seq tval b | b <- bs]) (i * n + j)
  = nth (uint U8 0) (nth (zeros n) bs i) j.
Proof.
move=> hj; elim: bs i => [|b bs IH] i /=.
- by rewrite !nth_nil nth_nseq hj.
- case: i => [|i]; first by rewrite mul0n add0n nth_cat size_tuple hj.
  by rewrite mulSn -addnA nth_cat size_tuple ltnNge leq_addr /= addKn IH.
Qed.

(* Row i of a flattened list of n-byte rows. *)
Lemma slice_flatten_rows (n : nat) (bs : seq (Bytes n)) (i : nat) :
  slice (flatten [seq tval b | b <- bs]) (i * n) n = nth (zeros n) bs i.
Proof.
apply: val_inj; apply: (@eq_from_nth _ (uint U8 0)); first by rewrite !size_tuple.
move=> j; rewrite size_tuple => hj.
by rewrite nth_slice // nth_flatten_rows.
Qed.

Lemma flatten_rows_size (n : nat) (rows : seq (Bytes n)) :
  size (flatten [seq tval row | row <- rows]) = size rows * n.
Proof.
elim: rows => [|row rows IH] //=.
by rewrite size_cat size_tuple IH mulSn.
Qed.

(* Positive fixed row width makes concatenation injective even when the two row counts are not known to agree. *)
Lemma flatten_rows_inj (n : nat) :
  0 < n ->
  injective (fun rows : seq (Bytes n) =>
    flatten [seq tval row | row <- rows]).
Proof.
move=> hn xs ys h.
have hsz : size xs = size ys.
  apply/eqP; rewrite -(eqn_pmul2r hn).
  apply/eqP.
  by rewrite -!flatten_rows_size h.
apply: (@eq_from_nth _ (zeros n)); first exact: hsz.
move=> i hi.
have hs := congr1 (fun encoded => slice encoded (i * n) n) h.
by rewrite !slice_flatten_rows in hs.
Qed.

(*  The signature layout  *)

(* A signature from its counter and chain values. The slice makes it total: it pads or cuts a list of the wrong length, which wots_c_sign never produces. *)
Definition sig_of (bs : seq (Bytes 16)) (c : nat) : Bytes (2 + WOTS_C_CHAINS_SIZE) :=
  slice (int_to_bytes (uint U16 c) 2 ++ flatten [seq tval b | b <- bs]) 0 (2 + WOTS_C_CHAINS_SIZE).

(* The chain values and the counter of a signature, read as wots_c_pubkey_from_sig reads them. *)
Definition sig_blocks (sg : Bytes (2 + WOTS_C_CHAINS_SIZE)) : seq (Bytes 16) :=
  [seq slice sg (2 + i * 16) 16 | i <- iota 0 WOTS_C_CHAIN_COUNT].

Definition sig_ctr (sg : Bytes (2 + WOTS_C_CHAINS_SIZE)) : nat :=
  Z.to_nat (wunsigned (int_from_bytes U16 (slice sg 0 2))).

Lemma sig_of_tuple (blocks : WOTS_C_CHAIN_COUNT.-tuple (Bytes 16)) (c : nat) :
  sig_of blocks c = [tuple of int_to_bytes (uint U16 c) 2 ++ concat blocks].
Proof. exact: (slice_all [tuple of int_to_bytes (uint U16 c) 2 ++ concat blocks]). Qed.

Lemma sig_ctr_of (bs : seq (Bytes 16)) (c : nat) : c < 2 ^ 16 -> sig_ctr (sig_of bs c) = c.
Proof.
move=> hc; rewrite /sig_ctr /sig_of slice_slice // addn0.
by rewrite slice_cat_head int_from_to_bytes_2 to_nat_uint16.
Qed.

Lemma sig_blocks_of (bs : seq (Bytes 16)) (c : nat) :
  size bs = WOTS_C_CHAIN_COUNT -> sig_blocks (sig_of bs c) = bs.
Proof.
move=> hbs; apply: (@eq_from_nth _ (zeros 16)); first by rewrite size_map size_iota hbs.
move=> i; rewrite size_map size_iota => hi.
rewrite (nth_map 0) ?size_iota // nth_iota // add0n /sig_of slice_slice.
  by rewrite -addnA leq_add2l -mulSnr /WOTS_C_CHAINS_SIZE leq_mul2r hi orbT.
by rewrite add0n slice_cat_tail slice_flatten_rows.
Qed.
