(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.repr.int32: CompCert [Int.int] against mathcomp [word U32]

    The C computes in [Int.int]; the specification computes in
    [word U32]. This file is the dictionary between the two carriers --
    the maps both ways, that they are mutually inverse, the [list val]
    view of an array of words, and the big-endian byte codec's
    round-trips.

    NOTHING HERE KNOWS ABOUT SHA-256. What the two carriers do to a
    FIPS operation -- that the C's shift-shift-or IS the model's
    [ROTR], that its [&] is [wand] -- is Vst.sha256.bridge, which
    is stated in terms of this file. The split is the same one
    Vst.repr.words makes on the byte side. *)

From Shrincs.internal.vst.support.repr Require Export words.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

(* ================================================================= *)
(** ** The two directions

    [w32c] is the universe-small carrier, the same trick Vst.base
    plays at U256: a funspec WITH-telescope must not swallow the HB
    [comRingType] pack. *)

Definition w32c : Type := wcarrier U32.

Definition w32_of_int (i : Int.int) : word U32 := wrepr U32 (Int.unsigned i).
Definition int_of_w32 (w : word U32) : Int.int := Int.repr (wunsigned w).

(** The two moduli are the same number. Every proof below goes through
    this. *)
Lemma wbase_U32 : wbase U32 = Int.modulus.
Proof.
now vm_compute.
Qed.

(** [Int.repr] already reduces modulo [Int.modulus], so an inner
    reduction is invisible to it. This absorbs the [mod] that
    mathcomp-word's [wrepr] leaves behind. *)
Lemma Int_repr_mod (z : Z) : Int.repr (z mod Int.modulus) = Int.repr z.
Proof.
apply Int.eqm_samerepr.
apply Int.eqm_sym.
apply Zbits.eqmod_mod.
(* the modulus is positive *)
apply Int.modulus_pos.
Qed.

Lemma wunsigned_w32_of_int (i : Int.int) : wunsigned (w32_of_int i) = Int.unsigned i.
Proof.
unfold w32_of_int.
rewrite wunsigned_repr_small.
- (* [Int.unsigned] lands in [0, 2^32), and that is [wbase U32] *)
  rewrite wbase_U32.
  exact (Int.unsigned_range i).
- reflexivity.
Qed.

Lemma int_of_w32K (w : word U32) : w32_of_int (int_of_w32 w) = w.
Proof.
apply wunsigned_inj.
rewrite wunsigned_w32_of_int.
unfold int_of_w32.
rewrite Int.unsigned_repr.
- (* the word's own range is the CompCert range *)
  assert (H := wunsigned_range w).
  rewrite wbase_U32 in H.
  change Int.max_unsigned with (Int.modulus - 1).
  lia.
- reflexivity.
Qed.

Lemma w32_of_intK (i : Int.int) : int_of_w32 (w32_of_int i) = i.
Proof.
unfold int_of_w32.
rewrite wunsigned_w32_of_int.
apply Int.repr_unsigned.
Qed.

Lemma int_of_w32_inj (x y : word U32) : int_of_w32 x = int_of_w32 y -> x = y.
Proof.
intros H.
rewrite <- (int_of_w32K x).
rewrite <- (int_of_w32K y).
rewrite H.
reflexivity.
Qed.

(** The list form every funspec and loop invariant over a
    [tarray tuint] uses. *)
Definition words_to_vals (ws : seq (word U32)) : list Values.val :=
  List.map (fun w => Vint (int_of_w32 w)) ws.

Lemma words_to_vals_Zlength (ws : seq (word U32)) :
  Zlength (words_to_vals ws) = Z.of_nat (size ws).
Proof.
unfold words_to_vals.
rewrite Zlength_map.
rewrite Zlength_correct.
rewrite <- size_length.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The byte codec round-trip

    WHY THESE ARE NEEDED. Vst.sha256.clone defines the
    digest twice over: [sha256_bytes] is the thirty-two bytes the C
    stores, and [sha256] is [word_of_bytes] of them. The POSTcondition of
    [spec_sha256] is phrased in the word, the C writes the bytes, and
    these lemmas are the step between.

    HOW THEY GO. Induct on the prefix length [k <= wnbytes ws],
    showing
      foldl f 0 [seq byte_of_word w i | i <- iota 0 k]
        = Z.shiftr (wunsigned w) (8 * (wnbytes ws - k)).
    The step reduces to [lor_shiftl_shiftr_byte] below, which is the
    whole bit-level content of the round trip; the converse direction
    additionally needs [size bs = wnbytes ws] and every byte in
    [0, 256), and [Z.mod_pow2_bits_low] to see past the modulus
    [wrepr] leaves behind. *)

(** [wnbytes U32] is a closed [nat], so the [iota] in [bytes_of_word]
    and the [8 * (wnbytes ws - 1 - i)] in [byte_of_word] both reduce by
    conversion: the four shift amounts 24/16/8/0 are literally what the
    definition unfolds to. Both the store loop and the digest bound
    read the four bytes off this. *)
Lemma bytes_of_word_U32_eq (w : word U32) :
  bytes_of_word U32 w
  = [:: Z.land (Z.shiftr (wunsigned w) 24) 255;
        Z.land (Z.shiftr (wunsigned w) 16) 255;
        Z.land (Z.shiftr (wunsigned w) 8) 255;
        Z.land (Z.shiftr (wunsigned w) 0) 255].
Proof. reflexivity. Qed.

(** Every jasmin [wsize] is a whole number of bytes, so [wnbytes] loses
    nothing: this is the fact that lets a bit index be counted in bytes. *)
Lemma wbits_wnbytesE (ws : wsize) : (8 * wnbytes ws)%nat = wbits ws.
Proof.
destruct ws.
all: reflexivity.
Qed.

(** The modulus as a [Z] power of two. [wbaseE] states it with mathcomp's
    [expn]; the byte arithmetic below needs Stdlib's [Z.pow]. *)
Lemma wbase_pow2E (ws : wsize) : wbase ws = 2 ^ Z.of_nat (8 * wnbytes ws).
Proof.
rewrite wbits_wnbytesE.
rewrite wbaseE.
rewrite expn_Nat_pow.
rewrite Znat.Nat2Z.inj_pow.
reflexivity.
Qed.

(** Splitting the low byte off a value and shifting it back in is the
    identity. This is the whole content of the round trip: one bit index
    is either below 8, where only the mask contributes, or at least 8,
    where only the shifted part does. *)
Lemma lor_shiftl_shiftr_byte (v : Z) :
  Z.lor (Z.shiftl (Z.shiftr v 8) 8) (Z.land v 255) = v.
Proof.
assert (H255 : 255 = Z.ones 8) by reflexivity.
apply Z.bits_inj'.
intros n Hn.
rewrite Z.lor_spec.
rewrite Z.land_spec.
rewrite H255.
rewrite Z.testbit_ones; [lia |].
assert (Hnn : (0 <=? n) = true) by (apply Z.leb_le; exact Hn).
rewrite Hnn.
rewrite andTb.
rewrite Z.shiftl_spec; [exact Hn |].
destruct (Z.ltb_spec0 n 8) as [Hn8 | Hn8].
- (* below the byte boundary only the mask contributes *)
  rewrite Z.testbit_neg_r; [lia |].
  rewrite andbT.
  rewrite orFb.
  reflexivity.
- (* at or above it only the shifted part does *)
  rewrite Z.shiftr_spec; [lia |].
  rewrite andbF.
  rewrite orbF.
  rewrite Z.sub_add.
  reflexivity.
Qed.

Lemma word_of_bytes_of_word (ws : wsize) (w : word ws) :
  word_of_bytes ws (bytes_of_word ws w) = w.
Proof.
(* folding the first k rendered bytes leaves the top wnbytes ws - k bytes *)
assert (Hprefix : forall k : nat, (k <= wnbytes ws)%nat ->
  foldl (fun acc b => Z.lor (Z.shiftl acc 8) b) 0
        [seq byte_of_word ws w i | i <- iota 0 k]
  = Z.shiftr (wunsigned w) (Z.of_nat (8 * (wnbytes ws - k)))).
{ intros k.
  induction k as [|k IH].
  - (* no bytes read yet: the whole word has been shifted out *)
    intros _.
    rewrite subn0.
    assert (Hempty : foldl (fun acc b => Z.lor (Z.shiftl acc 8) b) 0
                           [seq byte_of_word ws w i | i <- iota 0 0] = 0)
      by reflexivity.
    rewrite Hempty.
    destruct (wunsigned_range w) as [Hlo Hhi].
    rewrite (Z.shiftr_div_pow2 _ _ (Znat.Nat2Z.is_nonneg _)).
    symmetry.
    apply Z.div_small.
    split.
    + exact Hlo.
    + rewrite <- wbase_pow2E.
      exact Hhi.
  - (* one more byte shifts the accumulator up and ors byte k in *)
    intros Hk.
    assert (Hiota : iota 0 k.+1 = iota 0 k ++ [:: k]).
    { rewrite <- addn1.
      rewrite iotaD.
      rewrite add0n.
      reflexivity. }
    assert (Hone : forall (acc : Z) (j : nat),
      foldl (fun a b => Z.lor (Z.shiftl a 8) b) acc
            [seq byte_of_word ws w i | i <- [:: j]]
      = Z.lor (Z.shiftl acc 8) (byte_of_word ws w j))
      by (intros acc j; reflexivity).
    assert (Hidx : (wnbytes ws - 1 - k)%nat = (wnbytes ws - k.+1)%nat).
    { rewrite <- subnDA.
      rewrite add1n.
      reflexivity. }
    assert (Hshift : Z.of_nat (8 * (wnbytes ws - k))
                     = Z.of_nat (8 * (wnbytes ws - k.+1)) + 8).
    { rewrite <- (subnSK Hk).
      rewrite mulnSr.
      rewrite Znat.Nat2Z.inj_add.
      reflexivity. }
    rewrite Hiota.
    rewrite map_cat.
    rewrite foldl_cat.
    rewrite Hone.
    rewrite (IH (ltnW Hk)).
    unfold byte_of_word.
    rewrite Hidx.
    rewrite Hshift.
    rewrite <- Z.shiftr_shiftr; [| lia].
    apply lor_shiftl_shiftr_byte. }
unfold word_of_bytes.
unfold bytes_of_word.
rewrite (Hprefix (wnbytes ws) (leqnn _)).
rewrite subnn.
rewrite muln0.
rewrite Z.shiftr_0_r.
rewrite wrepr_unsigned.
reflexivity.
Qed.

Lemma bytes_of_word_of_bytes (ws : wsize) (bs : seq Z) :
  size bs = wnbytes ws ->
  (forall b, b \in bs -> 0 <= b < 256) ->
  bytes_of_word ws (word_of_bytes ws bs) = bs.
Proof.
intros Hsize Hrange.
assert (H255 : 255 = Z.ones 8) by reflexivity.
(* the fold puts byte i exactly where byte_of_word reads it back off *)
assert (Hnth : forall l : seq Z, (forall b, b \in l -> 0 <= b < 256) ->
  forall i : nat, (i < size l)%nat ->
  Z.land (Z.shiftr (foldl (fun acc b => Z.lor (Z.shiftl acc 8) b) 0 l)
                   (Z.of_nat (8 * (size l - 1 - i)))) 255 = nth 0 l i).
{ intros l.
  induction l as [| l b IH] using last_ind.
  - (* the empty list has no index to read *)
    intros _ i Hi.
    rewrite ltn0 in Hi.
    discriminate.
  - intros Hall i Hi.
    assert (Hall' : forall x, x \in l -> 0 <= x < 256).
    { intros x Hx.
      apply Hall.
      rewrite mem_rcons.
      rewrite inE.
      rewrite Hx.
      rewrite orbT.
      reflexivity. }
    assert (Hb : 0 <= b < 256).
    { apply Hall.
      rewrite mem_rcons.
      rewrite inE.
      rewrite eqxx.
      reflexivity. }
    assert (Hfold : foldl (fun acc c => Z.lor (Z.shiftl acc 8) c) 0 (rcons l b)
      = Z.lor (Z.shiftl (foldl (fun acc c => Z.lor (Z.shiftl acc 8) c) 0 l) 8) b).
    { rewrite <- cats1.
      rewrite foldl_cat.
      reflexivity. }
    revert Hi.
    rewrite size_rcons.
    rewrite ltnS.
    intros Hi.
    (* i is either the index of the byte just appended, or an earlier one *)
    destruct (i == size l) eqn:Heq.
    + (* the last byte is the low byte of the fold *)
      assert (Hieq : i = size l) by (apply (elimT eqP); exact Heq).
      rewrite Hieq.
      rewrite subSS.
      rewrite subn0.
      rewrite subnn.
      rewrite muln0.
      rewrite Z.shiftr_0_r.
      rewrite Hfold.
      rewrite nth_rcons.
      rewrite ltnn.
      rewrite eqxx.
      rewrite Z.land_lor_distr_l.
      assert (Hhigh :
        Z.land (Z.shiftl (foldl (fun acc c => Z.lor (Z.shiftl acc 8) c) 0 l) 8) 255
        = 0).
      { rewrite H255.
        rewrite Z.land_ones; [lia |].
        rewrite Z.shiftl_mul_pow2; [lia |].
        rewrite Z.mod_mul; [lia |].
        reflexivity. }
      rewrite Hhigh.
      assert (Hlow : Z.land b 255 = b).
      { rewrite H255.
        rewrite Z.land_ones; [lia |].
        apply Z.mod_small.
        assert (Hpow : 2 ^ 8 = 256) by reflexivity.
        rewrite Hpow.
        exact Hb. }
      rewrite Hlow.
      rewrite Z.lor_0_l.
      reflexivity.
    + (* an earlier byte: shift the last one out and use the hypothesis *)
      assert (Hilt : (i < size l)%nat).
      { rewrite leq_eqVlt in Hi.
        rewrite Heq in Hi.
        exact Hi. }
      assert (Hidx : (size l - 1 - i)%nat = (size l - i.+1)%nat).
      { rewrite <- subnDA.
        rewrite add1n.
        reflexivity. }
      assert (Hshift : Z.of_nat (8 * (size l - i))
                       = 8 + Z.of_nat (8 * (size l - 1 - i))).
      { rewrite Hidx.
        rewrite <- (subnSK Hilt).
        rewrite mulnS.
        rewrite Znat.Nat2Z.inj_add.
        reflexivity. }
      assert (Hdrop :
        Z.shiftr (foldl (fun acc c => Z.lor (Z.shiftl acc 8) c) 0 (rcons l b)) 8
        = foldl (fun acc c => Z.lor (Z.shiftl acc 8) c) 0 l).
      { rewrite Hfold.
        rewrite Z.shiftr_lor.
        rewrite Z.shiftr_shiftl_l; [lia |].
        rewrite Z.sub_diag.
        rewrite Z.shiftl_0_r.
        assert (Hbtop : Z.shiftr b 8 = 0).
        { rewrite Z.shiftr_div_pow2; [lia |].
          apply Z.div_small.
          assert (Hpow : 2 ^ 8 = 256) by reflexivity.
          rewrite Hpow.
          exact Hb. }
        rewrite Hbtop.
        rewrite Z.lor_0_r.
        reflexivity. }
      rewrite subSS.
      rewrite subn0.
      rewrite Hshift.
      rewrite <- Z.shiftr_shiftr; [| lia].
      rewrite Hdrop.
      rewrite nth_rcons.
      rewrite Hilt.
      exact (IH Hall' i Hilt). }
(* the reduction wrepr leaves behind clears no bit any byte reads *)
assert (Hmod : forall (a : Z) (j : nat), (j < wnbytes ws)%nat ->
  Z.land (Z.shiftr (a mod 2 ^ Z.of_nat (8 * wnbytes ws)) (Z.of_nat (8 * j))) 255
  = Z.land (Z.shiftr a (Z.of_nat (8 * j))) 255).
{ intros a j Hj.
  (* byte j and its eight bits sit strictly inside the word *)
  assert (Hbnd : Z.of_nat (8 * j) + 8 <= Z.of_nat (8 * wnbytes ws)).
  { assert (Hmul : forall x y : nat, Z.of_nat (x * y)%nat = Z.of_nat x * Z.of_nat y)
      by (intros x y; apply Znat.Nat2Z.inj_mul).
    assert (Hj' : Z.of_nat j.+1 <= Z.of_nat (wnbytes ws)).
    { apply Znat.inj_le.
      apply (elimT leP).
      exact Hj. }
    assert (HjS : Z.of_nat j.+1 = Z.of_nat j + 1).
    { rewrite Znat.Nat2Z.inj_succ.
      lia. }
    rewrite HjS in Hj'.
    rewrite !Hmul.
    assert (H8 : Z.of_nat 8 = 8) by reflexivity.
    rewrite H8.
    lia. }
  apply Z.bits_inj'.
  intros n Hn.
  rewrite !Z.land_spec.
  rewrite H255.
  rewrite Z.testbit_ones; [lia |].
  assert (Hnn : (0 <=? n) = true) by (apply Z.leb_le; exact Hn).
  rewrite Hnn.
  rewrite andTb.
  rewrite !(Z.shiftr_spec _ _ n Hn).
  destruct (Z.ltb_spec0 n 8) as [Hn8 | Hn8].
  - (* a bit the byte reads: it sits below the modulus *)
    rewrite !andbT.
    apply Z.mod_pow2_bits_low.
    lia.
  - (* a bit the byte masks away *)
    rewrite !andbF.
    reflexivity. }
assert (Hunsigned : wunsigned (word_of_bytes ws bs)
  = foldl (fun acc b => Z.lor (Z.shiftl acc 8) b) 0 bs
    mod 2 ^ Z.of_nat (8 * wnbytes ws)).
{ unfold word_of_bytes.
  rewrite wunsigned_repr.
  rewrite <- wbase_pow2E.
  reflexivity. }
apply (@eq_from_nth _ 0).
- (* both sides carry wnbytes ws entries *)
  rewrite bytes_of_word_size.
  rewrite Hsize.
  reflexivity.
- intros i Hi.
  rewrite bytes_of_word_size in Hi.
  assert (Hi' : (i < size bs)%nat) by (rewrite Hsize; exact Hi).
  unfold bytes_of_word.
  rewrite (nth_map 0%nat); [rewrite size_iota; exact Hi |].
  rewrite nth_iota; [exact Hi |].
  rewrite add0n.
  unfold byte_of_word.
  rewrite Hunsigned.
  rewrite Hmod.
  + (* byte i lives inside the word *)
    apply (leq_ltn_trans (leq_subr i (wnbytes ws - 1))).
    rewrite subn1.
    rewrite ltn_predL.
    exact (leq_ltn_trans (leq0n i) Hi).
  + rewrite <- Hsize.
    exact (Hnth bs Hrange i Hi').
Qed.
