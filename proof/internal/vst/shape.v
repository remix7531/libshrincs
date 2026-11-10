(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.shape: the loops of the specification in the shape the C runs them

    Shrincs.spec transcribes the reference: a comprehension per output array, a fold per loop, one general digit conversion. src/wots.c computes the same values one array cell, one loop turn and one nibble at a time. Each lemma below states one such correspondence over the specification alone, with no C and no memory in it. The body proofs under Shrincs.internal.vst rewrite with them and never unfold a function of the specification themselves.

    The file is plain MathComp. It is listed under the VST tree because the VST proofs are its only users. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.
From Stdlib Require Znat.
From Shrincs.internal.common Require Import bytes.
From Shrincs Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------ *)
(** ** Constants *)

Lemma WOTS_C_CHAIN_COUNT_eq : WOTS_C_CHAIN_COUNT = 32.
Proof. by []. Qed.

Lemma WOTS_C_CHAIN_MAX_eq : 2 ^ WOTS_C_CHAIN_BITS - 1 = 15.
Proof. by []. Qed.

Lemma WOTS_C_CONSTANT_SUM_eq : WOTS_C_CONSTANT_SUM = 240.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Integers and bytes *)

Section Integers.
Local Open Scope Z_scope.

(** A bound stated in [Z], where it is a binary number, gives the bound in [nat]. *)
Lemma ltn_pow2 (k e : nat) : Z.of_nat k < 2 ^ Z.of_nat e -> (k < 2 ^ e)%nat.
Proof.
move=> hk; apply/ltP; apply: (proj2 (Znat.Nat2Z.inj_lt _ _)).
by rewrite expn_Nat_pow Znat.Nat2Z.inj_pow.
Qed.

Lemma wunsigned_uint (ws : wsize) (x : nat) :
  Z.of_nat x < wbase ws -> wunsigned (uint ws x) = Z.of_nat x.
Proof.
move=> hx; apply: wunsigned_repr_small; split=> //.
exact: Znat.Nat2Z.is_nonneg.
Qed.

(** MathComp's division and remainder on [nat] are the ones of [Z]. *)
Lemma Z_of_nat_divn (m d : nat) : (0 < d)%nat -> Z.of_nat (m %/ d) = Z.of_nat m / Z.of_nat d.
Proof.
move=> hd.
have hr : (m %% d < d)%nat by rewrite ltn_mod.
apply: (Z.div_unique_pos _ _ _ (Z.of_nat (m %% d))).
  split; first exact: Znat.Nat2Z.is_nonneg.
  exact/Znat.Nat2Z.inj_lt/ltP.
rewrite [in LHS](divn_eq m d) -plusE -multE Znat.Nat2Z.inj_add Znat.Nat2Z.inj_mul.
by rewrite Z.mul_comm.
Qed.

Lemma Z_of_nat_modn (m d : nat) : (0 < d)%nat -> Z.of_nat (m %% d) = Z.of_nat m mod Z.of_nat d.
Proof.
move=> hd.
have hr : (m %% d < d)%nat by rewrite ltn_mod.
apply: (Z.mod_unique_pos _ _ (Z.of_nat (m %/ d))).
  split; first exact: Znat.Nat2Z.is_nonneg.
  exact/Znat.Nat2Z.inj_lt/ltP.
rewrite [in LHS](divn_eq m d) -plusE -multE Znat.Nat2Z.inj_add Znat.Nat2Z.inj_mul.
by rewrite Z.mul_comm.
Qed.

(** [Address.pack], byte by byte. *)
Lemma pack_bytes (height : UInt8) (index : UInt64) (address_type : UInt8)
    (word1 word2 word3 : UInt32) :
  tval (pack height index address_type word1 word2 word3) =
  [:: wrepr U8 (wunsigned height / 256 ^ 0);
      wrepr U8 (wunsigned index / 256 ^ 7); wrepr U8 (wunsigned index / 256 ^ 6);
      wrepr U8 (wunsigned index / 256 ^ 5); wrepr U8 (wunsigned index / 256 ^ 4);
      wrepr U8 (wunsigned index / 256 ^ 3); wrepr U8 (wunsigned index / 256 ^ 2);
      wrepr U8 (wunsigned index / 256 ^ 1); wrepr U8 (wunsigned index / 256 ^ 0);
      wrepr U8 (wunsigned address_type / 256 ^ 0);
      wrepr U8 (wunsigned word1 / 256 ^ 3); wrepr U8 (wunsigned word1 / 256 ^ 2);
      wrepr U8 (wunsigned word1 / 256 ^ 1); wrepr U8 (wunsigned word1 / 256 ^ 0);
      wrepr U8 (wunsigned word2 / 256 ^ 3); wrepr U8 (wunsigned word2 / 256 ^ 2);
      wrepr U8 (wunsigned word2 / 256 ^ 1); wrepr U8 (wunsigned word2 / 256 ^ 0);
      wrepr U8 (wunsigned word3 / 256 ^ 3); wrepr U8 (wunsigned word3 / 256 ^ 2);
      wrepr U8 (wunsigned word3 / 256 ^ 1); wrepr U8 (wunsigned word3 / 256 ^ 0)].
Proof. by []. Qed.

(** [counter.to_bytes(2)], byte by byte. *)
Lemma int_to_bytes_2 (counter : UInt16) :
  tval (int_to_bytes counter 2)
  = [:: wrepr U8 (wunsigned counter / 256 ^ 1); wrepr U8 (wunsigned counter / 256 ^ 0)].
Proof. by []. Qed.

(** [int.from_bytes] of two bytes. *)
Lemma int_from_bytes_2 (b0 b1 : UInt8) :
  int_from_bytes U16 [:: b0; b1] = wrepr U16 (wunsigned b0 * 256 + wunsigned b1).
Proof. by []. Qed.

End Integers.

Lemma tval_zeros (n : nat) : tval (zeros n) = nseq n (uint U8 0).
Proof. by []. Qed.

(** A slice inside its source is a [take] of a [drop]. *)
Lemma slice_take_drop (x : seq UInt8) (start length : nat) :
  start + length <= size x -> tval (slice x start length) = take length (drop start x).
Proof.
move=> hsz.
have ha : start <= size x := leq_trans (leq_addr length start) hsz.
have hn : length <= size (drop start x) by rewrite size_drop leq_subRL.
apply: (@eq_from_nth _ (uint U8 0)); first by rewrite size_tuple size_takel.
move=> k; rewrite size_tuple => hk.
by rewrite (nth_map 0) ?size_iota // nth_iota // nth_take // nth_drop.
Qed.

Lemma slice_take (x : seq UInt8) (length : nat) :
  length <= size x -> tval (slice x 0 length) = take length x.
Proof. by move=> hsz; rewrite slice_take_drop ?drop0. Qed.

(* ------------------------------------------------------------------ *)
(** ** One tweakable hash

    The C has one hash function over a packed address and a message of any length, [shrincs_thash]. The reference spells that expression three times, once per address class. *)

Definition th (pk_seed : Bytes 16) (adrs : Bytes 22) (msg : seq UInt8) : Bytes 16 :=
  slice (sha256 (pk_seed ++ zeros 48 ++ adrs ++ msg)) 0 16.

Section OneHash.
Local Open Scope Z_scope.
Variables (pk_seed : Bytes 16) (height : UInt8) (index : UInt64).

Lemma T_sf_th (M_l : Bytes WOTS_C_CHAINS_SIZE) :
  T_sf pk_seed (WotsCPk height index) M_l
  = th pk_seed (pack height index SF_WOTS_C_PK (uint U32 0) (uint U32 0) (uint U32 0)) M_l.
Proof. by []. Qed.

Lemma F_th (chain_index hash_index : UInt32) (M_1 : Bytes 16) :
  F pk_seed (WotsCHash height index chain_index hash_index) M_1
  = th pk_seed (pack height index SF_WOTS_C_HASH (uint U32 0) chain_index hash_index) M_1.
Proof. by []. Qed.

Lemma PRF_th (sk_seed : Bytes 16) (tree_balanced : bool) (tree_depth : UInt8)
    (chain_index : UInt32) :
  PRF pk_seed sk_seed (WotsCPrf height index tree_balanced tree_depth chain_index)
  = th pk_seed
      (pack height index SF_WOTS_C_PRF
         (wrepr U32 (Z.b2z tree_balanced * 2 ^ 24 + wunsigned tree_depth * 2 ^ 16))
         chain_index (uint U32 0))
      sk_seed.
Proof. by []. Qed.

(** The grinding hash over its preimage as the C assembles it: five appends, then the two bytes of the counter one after the other. *)
Lemma H_grind_preimage (digest : Bytes 32) (counter : UInt16) :
  let adrs := pack height index SF_WOTS_C_GRIND (uint U32 0) (uint U32 0) (uint U32 0) in
  H_grind pk_seed (WotsCGrind height index) digest counter
  = slice (sha256 (rcons (rcons ((((pk_seed ++ zeros 48) ++ slice adrs 0 10) ++ digest)
                                   ++ zeros 4)
                            (wrepr U8 (wunsigned counter / 256 ^ 1)))
                     (wrepr U8 (wunsigned counter / 256 ^ 0)))) 0 16.
Proof. by rewrite /H_grind -!cats1 -!catA. Qed.

End OneHash.

(* ------------------------------------------------------------------ *)
(** ** Arrays filled one block at a time

    The C fills an output array of [n] blocks in a loop. [blocks f k] is its content after [k] turns. *)

Definition blocks (f : nat -> seq UInt8) (k : nat) : seq UInt8 :=
  flatten [seq f i | i <- iota 0 k].

Lemma blocks0 (f : nat -> seq UInt8) : blocks f 0 = [::].
Proof. by []. Qed.

Lemma blocksS (f : nat -> seq UInt8) (k : nat) : blocks f k.+1 = blocks f k ++ f k.
Proof. by rewrite /blocks -addn1 iotaD map_cat flatten_cat /= cats0. Qed.

Lemma size_blocks (f : nat -> seq UInt8) (n k : nat) :
  (forall i, size (f i) = n) -> size (blocks f k) = k * n.
Proof.
move=> hf; elim: k => [|k IH] //.
by rewrite blocksS size_cat IH hf mulSn addnC.
Qed.

(** [concat] of a comprehension is the array after all its turns. *)
Lemma blocks_concat (m n : nat) (f : nat -> Bytes n) :
  blocks (fun i => tval (f i)) m = tval (concat [tuple of [seq f i | i <- iota 0 m]]).
Proof. by rewrite /blocks /= -map_comp. Qed.

(* ------------------------------------------------------------------ *)
(** ** The hash chain, one step at a time *)

Section Chain.
Variables (pk_seed : Bytes 16) (node_height : UInt8) (node_index : UInt64) (chain_index : UInt32).

Lemma wots_c_chain_iter_nil (node : Bytes 16) (start : nat) :
  wots_c_chain_iter node start start pk_seed node_height node_index chain_index = node.
Proof. by rewrite /wots_c_chain_iter /range subnn. Qed.

Lemma wots_c_chain_iter_step (node : Bytes 16) (start j : nat) :
  start <= j ->
  wots_c_chain_iter node start j.+1 pk_seed node_height node_index chain_index
  = F pk_seed (WotsCHash node_height node_index chain_index (uint U32 j))
      (wots_c_chain_iter node start j pk_seed node_height node_index chain_index).
Proof.
move=> hsj.
by rewrite /wots_c_chain_iter /range subSn // -[(j - start).+1]addn1 iotaD foldl_cat /= subnKC.
Qed.

End Chain.

(* ------------------------------------------------------------------ *)
(** ** [base_2b] at four bits is the nibble split

    At [b = 4] the general conversion consumes one byte for every two digits: the high nibble, then the low nibble. *)

Lemma while_true (S : Type) (fuel : nat) (cond : S -> bool) (body : S -> S) (s : S) :
  cond s -> while fuel.+1 cond body s = while fuel cond body (body s).
Proof. by move=> /= ->. Qed.

Lemma while_false (S : Type) (fuel : nat) (cond : S -> bool) (body : S -> S) (s : S) :
  ~~ cond s -> while fuel cond body s = s.
Proof. by case: fuel => //= fuel /negbTE ->. Qed.

Lemma size_base_2b (x : seq UInt8) (b outlen : nat) : size (base_2b x b outlen) = outlen.
Proof.
rewrite /base_2b.
set step := (X in foldl X).
have: size (nseq outlen 0, 0, 0, 0).1.1.1 = outlen by rewrite /= size_nseq.
have: all (fun i => i < outlen) (iota 0 outlen) by apply/allP => i; rewrite mem_iota.
elim: (iota 0 outlen) (nseq outlen 0, 0, 0, 0) => [|i s IH] [[[baseb j] acc] bf] //=.
case/andP=> hi hs hsz.
case: (while _ _ _ _) => [[j0 acc0] bf0].
apply: IH => //=.
by rewrite size_set_nth hsz; apply/maxn_idPr.
Qed.

(** Digit [m] of the nibble split: byte [m %/ 2], its high half for an even [m] and its low half for an odd one. *)
Definition nibble (x : seq UInt8) (m : nat) : nat :=
  let v := Z.to_nat (wunsigned (nth (uint U8 0) x (m %/ 2))) in
  if odd m then v %% 16 else v %/ 16.

Lemma nth_base_2b_4 (x : seq UInt8) (k m : nat) :
  m < 2 * k -> nth 0 (base_2b x 4 (2 * k)) m = nibble x m.
Proof.
rewrite /base_2b; set step := (X in foldl X); set n := 2 * k.
pose bn j := Z.to_nat (wunsigned (nth (uint U8 0) x j)).
(* Two digits consume one byte and leave no bits behind. *)
have pair B j i : foldl step (B, j, 0, 0) [:: i; i.+1]
    = (set_nth 0 (set_nth 0 B i (bn j %/ 16)) i.+1 (bn j %% 16), j.+1, 0, 0).
  change (step (step (B, j, 0, 0) i) i.+1
          = (set_nth 0 (set_nth 0 B i (bn j %/ 16)) i.+1 (bn j %% 16), j.+1, 0, 0)).
  rewrite /step.
  rewrite (@while_true _ 3) // (@while_false _ 3) // while_false //.
  rewrite mul0n add0n addn1.
  rewrite (_ : 0 + 8 - 4 - 4 = 0) // (_ : 2 ^ (0 + 8 - 4) = 16) //.
  by rewrite expn0 divn1 modn1.
have claim k' : exists B,
    foldl step (nseq n 0, 0, 0, 0) (iota 0 (2 * k')) = (B, k', 0, 0)
    /\ forall m', m' < 2 * k' -> nth 0 B m' = nibble x m'.
  elim: k' => [|k' [B [hB hnth]]]; first by exists (nseq n 0).
  exists (set_nth 0 (set_nth 0 B (2 * k') (bn k' %/ 16)) (2 * k').+1 (bn k' %% 16)).
  split; first by rewrite mulnS addnC iotaD foldl_cat hB add0n [iota _ 2]/= pair.
  have half1 : (2 * k').+1 %/ 2 = k' by rewrite -addn1 mulnC divnMDl // divn_small // addn0.
  have half0 : (2 * k') %/ 2 = k' by rewrite mulKn.
  have odd1 : odd (2 * k').+1 by rewrite /= mul2n odd_double.
  have odd0 : odd (2 * k') = false by rewrite mul2n odd_double.
  move=> m' hm'; rewrite !nth_set_nth [LHS]/=.
  have [->|hne1] := eqVneq m' (2 * k').+1; first by rewrite /nibble half1 odd1.
  rewrite nth_set_nth [LHS]/=.
  have [->|hne0] := eqVneq m' (2 * k'); first by rewrite /nibble half0 odd0.
  apply: hnth.
  move: hm'; rewrite mulnS addnC addn2 ltnS leq_eqVlt (negbTE hne1) /= ltnS leq_eqVlt (negbTE hne0).
  by [].
have [B [-> hnth]] := claim k.
exact: hnth.
Qed.

Section Indexes.
Local Open Scope Z_scope.

(** The indexes the C writes from byte [i] of the hash: its two halves. *)
Lemma nth_indexes (hashed : Bytes 16) (i : nat) :
  (i < 16)%nat ->
  let indexes := base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT in
  let byte := wunsigned (nth (uint U8 0) hashed i) in
  nth 0%nat indexes (2 * i)%nat = Z.to_nat (byte / 16)
  /\ nth 0%nat indexes (2 * i).+1 = Z.to_nat (byte mod 16).
Proof.
move=> hi indexes byte.
have [hb0 hb1] : 0 <= byte < 256 by exact: (wunsigned_range (nth (uint U8 0) hashed i)).
have hlt : ((2 * i).+1 < 2 * 16)%nat by rewrite mulnS addnC addn2 !ltnS leq_pmul2l.
have half1 : ((2 * i).+1 %/ 2 = i)%nat by rewrite -addn1 mulnC divnMDl // divn_small // addn0.
have half0 : ((2 * i) %/ 2 = i)%nat by rewrite mulKn.
have odd1 : odd (2 * i).+1 by rewrite /= mul2n odd_double.
have odd0 : odd (2 * i) = false by rewrite mul2n odd_double.
have hnib m : (m < 2 * 16)%nat -> nth 0%nat indexes m = nibble hashed m.
  exact: (@nth_base_2b_4 hashed 16%nat).
rewrite (hnib _ hlt) (hnib _ (ltnW hlt)).
rewrite /nibble half0 half1 odd0 odd1 -/byte.
split; apply: Znat.Nat2Z.inj.
- by rewrite Z_of_nat_divn // !Znat.Z2Nat.id //; apply: Z.div_pos.
- by rewrite Z_of_nat_modn // !Znat.Z2Nat.id //; case: (Z.mod_pos_bound byte 16).
Qed.

Lemma nibble_le (x : seq UInt8) (m : nat) : (nibble x m <= 15)%nat.
Proof.
rewrite /nibble; set v := Z.to_nat _.
have hv : (v < 256)%nat.
  apply/ltP/(proj2 (Znat.Nat2Z.inj_lt _ _)).
  have [h0 h1] := wunsigned_range (nth (uint U8 0) x (m %/ 2)).
  by rewrite Znat.Z2Nat.id.
case: ifP => _; first by rewrite -ltnS ltn_mod.
by rewrite -ltnS ltn_divLR.
Qed.

Lemma nth_indexes_le (hashed : Bytes 16) (m : nat) :
  (nth 0%nat (base_2b hashed WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) m <= 15)%nat.
Proof.
have [hm|hm] := ltnP m (2 * 16)%nat; first by rewrite (@nth_base_2b_4 hashed 16%nat) // nibble_le.
by rewrite nth_default // size_base_2b.
Qed.

End Indexes.

(* ------------------------------------------------------------------ *)
(** ** The index sum, one index at a time *)

Lemma sumn_take_S (s : seq nat) (j : nat) :
  j < size s -> sumn (take j.+1 s) = sumn (take j s) + nth 0 s j.
Proof. by move=> hj; rewrite (take_nth 0) // sumn_rcons. Qed.

Lemma sumn_le (s : seq nat) (bound : nat) :
  (forall m, nth 0 s m <= bound) -> sumn s <= size s * bound.
Proof.
elim: s => [|d s IH] hle //=.
rewrite mulSn leq_add //; first exact: (hle 0).
by apply: IH => m; exact: (hle m.+1).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest mapping and grinding

    The C grinding loop calls the digest mapping once per counter and stops at the first constant sum. The reference spells the same body twice. *)

Section Grinding.
Variables (pk_seed : Bytes 16) (message_digest : Bytes 32)
          (node_height : UInt8) (node_index : UInt64).

(** The indexes of the digest at one counter, constant sum or not. *)
Definition digest_indexes (counter : UInt16) : seq nat :=
  base_2b (H_grind pk_seed (WotsCGrind node_height node_index) message_digest counter)
    WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT.

Lemma size_digest_indexes (counter : UInt16) : size (digest_indexes counter) = 32.
Proof. by rewrite /digest_indexes size_base_2b. Qed.

Lemma wots_c_map_digest_eq (counter : UInt16) :
  wots_c_map_digest pk_seed message_digest node_height node_index counter
  = if sumn (digest_indexes counter) == WOTS_C_CONSTANT_SUM
    then Some (digest_indexes counter) else None.
Proof. by []. Qed.

Lemma wots_c_map_digest_indexes (counter : UInt16) (indexes : seq nat) :
  wots_c_map_digest pk_seed message_digest node_height node_index counter = Some indexes ->
  indexes = digest_indexes counter.
Proof.
rewrite wots_c_map_digest_eq.
by case: ifP => // _ [<-].
Qed.

Lemma wots_c_grind_indexes (counter : UInt16) (indexes : seq nat) :
  wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index
  = Some (counter, indexes) -> indexes = digest_indexes counter.
Proof.
rewrite /wots_c_grind_to_constant_sum.
change (for_first
          (fun i => if sumn (digest_indexes (uint U16 i)) == WOTS_C_CONSTANT_SUM
                    then Some (uint U16 i, digest_indexes (uint U16 i)) else None)
          (range 0 (2 ^ 16)) = Some (counter, indexes) -> indexes = digest_indexes counter).
elim: (range 0 (2 ^ 16)) => [|i counters IH]; first by [].
cbn [for_first].
case: ifP => _; last exact: IH.
by move=> [<- <-].
Qed.

Lemma for_first_iota_some (B : Type) (f : nat -> option B) (a n k : nat) (y : B) :
  a <= k < a + n -> (forall i, a <= i < k -> f i = None) -> f k = Some y ->
  for_first f (iota a n) = Some y.
Proof.
elim: n a => [|n IH] a /andP[hak hkn] hnone hsome.
  by move: hkn; rewrite addn0 ltnNge hak.
rewrite /=; have [hk|hne] := eqVneq a k; first by rewrite hk hsome.
have hlt : a < k by rewrite ltn_neqAle hne hak.
rewrite hnone ?leqnn //.
apply: IH => //; first by rewrite hlt addSnnS.
by move=> i /andP[hai hik]; apply: hnone; rewrite hik andbT ltnW.
Qed.

Lemma for_first_iota_none (B : Type) (f : nat -> option B) (a n : nat) :
  (forall i, a <= i < a + n -> f i = None) -> for_first f (iota a n) = None.
Proof.
elim: n a => [|n IH] a hnone //=.
rewrite hnone ?leqnn -?addSnnS ?ltn_addr //.
by apply: IH => i /andP[hai hin]; apply: hnone; rewrite ltnW //= -addSnnS.
Qed.

Section Counters.
Local Open Scope Z_scope.

Lemma wots_c_map_digest_some (counter : UInt16) :
  Z.of_nat (sumn (digest_indexes counter)) = 240 ->
  wots_c_map_digest pk_seed message_digest node_height node_index counter
  = Some (digest_indexes counter).
Proof.
move=> hsum; rewrite wots_c_map_digest_eq WOTS_C_CONSTANT_SUM_eq.
by rewrite (Znat.Nat2Z.inj _ 240%nat hsum).
Qed.

Lemma wots_c_map_digest_none (counter : UInt16) :
  Z.of_nat (sumn (digest_indexes counter)) <> 240 ->
  wots_c_map_digest pk_seed message_digest node_height node_index counter = None.
Proof.
move=> hsum; rewrite wots_c_map_digest_eq WOTS_C_CONSTANT_SUM_eq.
by case: eqP => // heq; case: hsum; rewrite heq.
Qed.

Lemma sumn_digest_indexes_le (counter : UInt16) :
  Z.of_nat (sumn (digest_indexes counter)) <= 480.
Proof.
have hle := sumn_le (s := digest_indexes counter) (bound := 15)
              (nth_indexes_le (H_grind _ _ _ _)).
rewrite size_digest_indexes in hle.
exact: (proj1 (Znat.Nat2Z.inj_le _ 480%nat)) (elimT leP hle).
Qed.

(** The first counter with a constant sum is the one grinding returns. *)
Lemma wots_c_grind_some (k : nat) (indexes : seq nat) :
  Z.of_nat k < 2 ^ 16 ->
  (forall c, (c < k)%nat ->
     wots_c_map_digest pk_seed message_digest node_height node_index (uint U16 c) = None) ->
  wots_c_map_digest pk_seed message_digest node_height node_index (uint U16 k) = Some indexes ->
  wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index
  = Some (uint U16 k, indexes).
Proof.
move=> hk hnone hsome.
rewrite /wots_c_grind_to_constant_sum /range subn0.
apply: (@for_first_iota_some _ _ 0%nat _ k); first by rewrite add0n; exact: ltn_pow2.
- move=> c /andP[_ hc]; move: (hnone c hc); rewrite wots_c_map_digest_eq.
  by rewrite /digest_indexes; case: ifP.
- move: hsome; rewrite wots_c_map_digest_eq /digest_indexes.
  by case: ifP => // _ [->].
Qed.

Lemma wots_c_grind_none :
  (forall c, Z.of_nat c < 2 ^ 16 ->
     wots_c_map_digest pk_seed message_digest node_height node_index (uint U16 c) = None) ->
  wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index = None.
Proof.
move=> hnone.
rewrite /wots_c_grind_to_constant_sum /range subn0.
apply: for_first_iota_none => c /andP[_ hc].
have hcZ : Z.of_nat c < 2 ^ 16.
  have -> : 2 ^ 16 = Z.of_nat (2 ^ 16)%nat by rewrite expn_Nat_pow Znat.Nat2Z.inj_pow.
  exact/Znat.Nat2Z.inj_lt/ltP.
move: (hnone c hcZ); rewrite wots_c_map_digest_eq /digest_indexes.
by case: ifP.
Qed.

End Counters.
End Grinding.

(* ------------------------------------------------------------------ *)
(** ** The three algorithms, with their arrays as blocks *)

Section Algorithms.
Variables (sk_seed pk_seed : Bytes 16) (node_height : UInt8) (node_index : UInt64)
          (tree_balanced : bool) (tree_depth : UInt8).

(** Chain [i] from its secret start to position [stop]: one turn of the loops of key generation and signing. *)
Definition chain_from_seed (stop i : nat) : Bytes 16 :=
  wots_c_chain_iter
    (PRF pk_seed sk_seed
       (WotsCPrf node_height node_index tree_balanced tree_depth (uint U32 i)))
    0 stop pk_seed node_height node_index (uint U32 i).

(** The chain tips of key generation, concatenated: what the C's [wots_pk] holds after its loop. The tip of a chain is its position 15. *)
Definition pubkey_gen_tips : Bytes WOTS_C_CHAINS_SIZE :=
  concat [tuple of [seq chain_from_seed 15 i | i <- iota 0 WOTS_C_CHAIN_COUNT]].

Lemma wots_c_pubkey_gen_eq :
  wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth
  = T_sf pk_seed (WotsCPk node_height node_index) pubkey_gen_tips.
Proof. by []. Qed.

Lemma tval_pubkey_gen_tips :
  tval pubkey_gen_tips = blocks (fun i => tval (chain_from_seed 15 i)) 32.
Proof. by rewrite blocks_concat. Qed.

(** The signature for a grinding result: the two bytes of the counter, then the chains. *)
Definition signature_of (counter : UInt16) (indexes : seq nat)
    : Bytes (2 + WOTS_C_CHAINS_SIZE) :=
  [tuple of int_to_bytes counter 2
     ++ concat [tuple of [seq chain_from_seed (nth 0 indexes i) i
                         | i <- iota 0 WOTS_C_CHAIN_COUNT]]].

Lemma wots_c_sign_some (message_digest : Bytes 32) (counter : UInt16) (indexes : seq nat) :
  wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index
  = Some (counter, indexes) ->
  wots_c_sign message_digest sk_seed pk_seed node_height node_index tree_balanced tree_depth
  = Some (signature_of counter indexes).
Proof. by rewrite /wots_c_sign => ->. Qed.

Lemma wots_c_sign_none (message_digest : Bytes 32) :
  wots_c_grind_to_constant_sum pk_seed message_digest node_height node_index = None ->
  wots_c_sign message_digest sk_seed pk_seed node_height node_index tree_balanced tree_depth
  = None.
Proof. by rewrite /wots_c_sign => ->. Qed.

Lemma tval_signature_of (counter : UInt16) (indexes : seq nat) :
  tval (signature_of counter indexes)
  = int_to_bytes counter 2
    ++ blocks (fun i => tval (chain_from_seed (nth 0 indexes i) i)) 32.
Proof. by rewrite blocks_concat. Qed.

(** Chain [i] of a signature, completed from its index to the tip: one turn of the loop of public key recovery. *)
Definition chain_from_sig (signature : Bytes (2 + WOTS_C_CHAINS_SIZE)) (indexes : seq nat)
    (i : nat) : Bytes 16 :=
  wots_c_chain_iter (slice signature (2 + i * 16) 16) (nth 0 indexes i) 15
    pk_seed node_height node_index (uint U32 i).

(** The recovered chain tips, concatenated. *)
Definition recovered_tips (signature : Bytes (2 + WOTS_C_CHAINS_SIZE)) (indexes : seq nat)
    : Bytes WOTS_C_CHAINS_SIZE :=
  concat [tuple of [seq chain_from_sig signature indexes i
                   | i <- iota 0 WOTS_C_CHAIN_COUNT]].

Lemma wots_c_pubkey_from_sig_some (signature : Bytes (2 + WOTS_C_CHAINS_SIZE))
    (message_digest : Bytes 32) (indexes : seq nat) :
  wots_c_map_digest pk_seed message_digest node_height node_index
    (int_from_bytes U16 (slice signature 0 2)) = Some indexes ->
  wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index
  = Some (T_sf pk_seed (WotsCPk node_height node_index)
            (recovered_tips signature indexes)).
Proof. by rewrite /wots_c_pubkey_from_sig => ->. Qed.

Lemma tval_recovered_tips (signature : Bytes (2 + WOTS_C_CHAINS_SIZE)) (indexes : seq nat) :
  tval (recovered_tips signature indexes)
  = blocks (fun i => tval (chain_from_sig signature indexes i)) 32.
Proof. by rewrite blocks_concat. Qed.

Lemma wots_c_pubkey_from_sig_none (signature : Bytes (2 + WOTS_C_CHAINS_SIZE))
    (message_digest : Bytes 32) :
  wots_c_map_digest pk_seed message_digest node_height node_index
    (int_from_bytes U16 (slice signature 0 2)) = None ->
  wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index = None.
Proof. by rewrite /wots_c_pubkey_from_sig => ->. Qed.

End Algorithms.
