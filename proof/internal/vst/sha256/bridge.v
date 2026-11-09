(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.sha256.bridge: the C's expressions ARE the standard's

    FIPS 180-4 SS 3.2 read through Vst.repr.int32's carrier map:
    each lemma says that one CompCert expression the C compiles to is
    the model operation of the same name. The six logical-function
    proofs of verif/logical.v are nothing but these, applied.

    Each is stated twice, once in each direction. The [int_*] form
    reads the way the C does -- "this Int expression is that word
    operation" -- and the [w32_of_int_*] form is the one a body proof
    actually rewrites with, pushing [w32_of_int] inwards to the leaves
    where [w32_of_intK] cancels it.

    The carrier maps themselves, the array view and the byte codec are
    Vst.repr.int32; this file adds only what mentions a SHA-256
    operation. *)

From Vst.repr Require Export int32.
From Vst.sha256 Require Import clone.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

(* ================================================================= *)
(** ** The zero word, and indexing an array of words

    These need [w32_0], which is the standard's notation and lives in
    the model, so they sit on this side of the split. *)

Lemma int_of_w32_zero : int_of_w32 w32_0 = Int.zero.
Proof.
unfold int_of_w32.
unfold w32_0.
rewrite wunsigned_repr.
rewrite Zmod_0_l.
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

(** One entry of such an array. Every [forward] over a [tarray tuint]
    produces a [Znth] into a [words_to_vals], and the model speaks
    [nth]; this is that index, once. *)
Lemma Znth_words_to_vals (ws : seq (word U32)) (i : Z) :
  0 <= i < Z.of_nat (size ws) ->
  Znth i (words_to_vals ws) = Vint (int_of_w32 (nth w32_0 ws (Z.to_nat i))).
Proof.
intros Hi.
assert (Hlt : (Z.to_nat i < size ws)%nat) by (apply (introT ltP); lia).
unfold words_to_vals.
unfold Znth.
destruct (Z_lt_dec i 0) as [Hneg | _].
- (* a negative index contradicts the range hypothesis *)
  exfalso.
  lia.
- rewrite <- nth_seq_list.
  rewrite map_seq_list.
  rewrite (nth_map w32_0).
  + exact Hlt.
  + reflexivity.
Qed.

(** The same at a [nat] literal. The [i = Z.of_nat k] argument is what
    lets a call site write [k] once and have both the [Z] index floyd
    produced and the [nat] index the model speaks come out right. *)
Lemma Znth_words_to_vals_nat (ws : seq (word U32)) (k : nat) (i : Z) :
  (k < size ws)%nat -> i = Z.of_nat k ->
  Znth i (words_to_vals ws) = Vint (int_of_w32 (nth w32_0 ws k)).
Proof.
intros Hk Hi.
(* the boolean [<] of the hypothesis, as the [Z] bound [lia] needs *)
assert (Hk' : (k < size ws)%coq_nat) by (apply (elimT ltP); exact Hk).
rewrite Hi.
rewrite (Znth_words_to_vals ws (Z.of_nat k) ltac:(lia)).
rewrite Nat2Z.id.
reflexivity.
Qed.

(** An eight-word array written out. A loop-free run of reads and
    writes at eight literal indices resolves every [Znth] by
    conversion with the array in this shape, and generates no [tc_val]
    side condition. *)
Lemma words_to_vals_8 (ws : seq (word U32)) :
  size ws = 8%nat ->
  words_to_vals ws =
  [:: Vint (int_of_w32 (nth w32_0 ws 0)); Vint (int_of_w32 (nth w32_0 ws 1));
      Vint (int_of_w32 (nth w32_0 ws 2)); Vint (int_of_w32 (nth w32_0 ws 3));
      Vint (int_of_w32 (nth w32_0 ws 4)); Vint (int_of_w32 (nth w32_0 ws 5));
      Vint (int_of_w32 (nth w32_0 ws 6)); Vint (int_of_w32 (nth w32_0 ws 7))].
Proof.
(* every length but eight contradicts the hypothesis; eight computes *)
destruct ws as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 ws]]]]]]]]].
all: easy.
Qed.


(* ================================================================= *)
(** ** SS 3.2 (1): the bitwise operations

    mathcomp-word states these about [urepr]; [wunsigned] is [urepr],
    so the three restatements below are one [apply] each and not
    rewrites. Each C-side lemma is then one rewrite plus the fact that
    CompCert DEFINES the operation as [Int.repr] of the same [Z]
    operation. *)

Lemma wunsigned_wand (x y : word U32) :
  wunsigned (wand x y) = Z.land (wunsigned x) (wunsigned y).
Proof.
apply urepr_wand.
Qed.

Lemma wunsigned_wor (x y : word U32) :
  wunsigned (wor x y) = Z.lor (wunsigned x) (wunsigned y).
Proof.
apply urepr_wor.
Qed.

Lemma wunsigned_wxor (x y : word U32) :
  wunsigned (wxor x y) = Z.lxor (wunsigned x) (wunsigned y).
Proof.
apply urepr_wxor.
Qed.

Lemma int_and_wand (a b : Int.int) :
  Int.and a b = int_of_w32 (wand (w32_of_int a) (w32_of_int b)).
Proof.
unfold int_of_w32.
rewrite wunsigned_wand.
rewrite !wunsigned_w32_of_int.
reflexivity.
Qed.

Lemma int_or_wor (a b : Int.int) :
  Int.or a b = int_of_w32 (wor (w32_of_int a) (w32_of_int b)).
Proof.
unfold int_of_w32.
rewrite wunsigned_wor.
rewrite !wunsigned_w32_of_int.
reflexivity.
Qed.

Lemma int_xor_wxor (a b : Int.int) :
  Int.xor a b = int_of_w32 (wxor (w32_of_int a) (w32_of_int b)).
Proof.
unfold int_of_w32.
rewrite wunsigned_wxor.
rewrite !wunsigned_w32_of_int.
reflexivity.
Qed.

Lemma w32_of_int_mone : w32_of_int Int.mone = (-1)%R.
Proof.
apply wunsigned_inj.
rewrite wunsigned_w32_of_int.
now vm_compute.
Qed.

Lemma int_not_wnot (a : Int.int) :
  Int.not a = int_of_w32 (wnot (w32_of_int a)).
Proof.
unfold Int.not.
rewrite int_xor_wxor.
rewrite w32_of_int_mone.
reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 3.2 (2): addition modulo 2^32

    [+%R] on [word U32] and [Int.add] are the same operation; the
    [mod] that [wrepr] leaves behind is absorbed by [Int_repr_mod]. *)

Lemma wunsigned_wadd (x y : word U32) :
  wunsigned (x + y)%R = (wunsigned x + wunsigned y) mod Int.modulus.
Proof.
(* put both summands back under [wrepr] so [wrepr_add] applies *)
rewrite <- (wrepr_unsigned x) at 1.
rewrite <- (wrepr_unsigned y) at 1.
rewrite <- wrepr_add.
rewrite wunsigned_repr.
(* the modulus [wunsigned_repr] left is [Int.modulus] unfolded *)
rewrite <- wbase_U32.
reflexivity.
Qed.

Lemma int_add_wadd (a b : Int.int) :
  Int.add a b = int_of_w32 (w32_of_int a + w32_of_int b)%R.
Proof.
unfold int_of_w32.
rewrite wunsigned_wadd.
rewrite !wunsigned_w32_of_int.
rewrite Int_repr_mod.
reflexivity.
Qed.

(** The same read in the direction a body proof needs when both
    operands already come from the model: the [w32_of_int] the bridge
    lemma introduces cancels immediately. This is what turns the
    four-deep [Int.add] tower the C builds for T1 into the standard's
    own [(h + Sigma1 e + Ch e f g + K_t + W_t)]. *)
Lemma int_add_of_w32 (x y : word U32) :
  Int.add (int_of_w32 x) (int_of_w32 y) = int_of_w32 (x + y)%R.
Proof.
rewrite int_add_wadd.
rewrite !int_of_w32K.
reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 3.2 (3),(4): the shifts and the rotation

    mathcomp-word's [wshr] / [wshl] ARE [wrepr] of the corresponding
    [Z] shift -- definitionally, hence the two [reflexivity] proofs.
    The side condition on each C-side lemma is FIPS 180-4 SS 3.2's own
    [0 <= n < w], which is what makes [Int.unsigned (Int.repr n) = n].
    ROTR additionally needs [0 < n]: at n = 0 the C would shift by the
    full width, which is undefined (src/sha256.c says the same). *)

Lemma wshr_wrepr (x : word U32) (n : Z) :
  wshr x n = wrepr U32 (Z.shiftr (wunsigned x) n).
Proof. reflexivity. Qed.

Lemma wshl_wrepr (x : word U32) (n : Z) :
  wshl x n = wrepr U32 (Z.shiftl (wunsigned x) n).
Proof. reflexivity. Qed.

Lemma int_shru_SHR (a : Int.int) (n : Z) :
  0 <= n < 32 ->
  Int.shru a (Int.repr n) = int_of_w32 (SHR n (w32_of_int a)).
Proof.
intros Hn.
unfold int_of_w32.
unfold SHR.
rewrite wshr_wrepr.
rewrite wunsigned_repr.
(* the modulus [wunsigned_repr] left is [Int.modulus], which [Int.repr] absorbs *)
fold (wbase U32).
rewrite wbase_U32.
rewrite Int_repr_mod.
rewrite wunsigned_w32_of_int.
unfold Int.shru.
rewrite Int.unsigned_repr.
- (* the shift amount is a legal [Int] *)
  change Int.max_unsigned with 4294967295.
  lia.
- reflexivity.
Qed.

Lemma int_shl_wshl (a : Int.int) (n : Z) :
  0 <= n < 32 ->
  Int.shl a (Int.repr n) = int_of_w32 (wshl (w32_of_int a) n).
Proof.
intros Hn.
unfold int_of_w32.
rewrite wshl_wrepr.
rewrite wunsigned_repr.
(* the modulus [wunsigned_repr] left is [Int.modulus], which [Int.repr] absorbs *)
fold (wbase U32).
rewrite wbase_U32.
rewrite Int_repr_mod.
rewrite wunsigned_w32_of_int.
unfold Int.shl.
rewrite Int.unsigned_repr.
- (* the shift amount is a legal [Int] *)
  change Int.max_unsigned with 4294967295.
  lia.
- reflexivity.
Qed.

(** THE lemma the six logical-function proofs are built on: the
    shift-shift-or the C macro expands to IS the model's [ROTR]. Without
    it every [Sigma]/[sigma] proof would have to argue about bits. *)
Lemma int_ROTR (a : Int.int) (n : Z) :
  0 < n < 32 ->
  Int.or (Int.shru a (Int.repr n)) (Int.shl a (Int.repr (32 - n)))
  = int_of_w32 (ROTR n (w32_of_int a)).
Proof.
intros Hn.
rewrite (int_shru_SHR a n); [lia |].
rewrite (int_shl_wshl a (32 - n)); [lia |].
rewrite int_or_wor.
rewrite !int_of_w32K.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The same dictionary, read the other way

    The lemmas above are stated C-side-first, which is how they read;
    the body proofs need them applied in the other direction, pushing
    [w32_of_int] through a CompCert expression until it reaches the
    leaves. Each is its counterpart plus [int_of_w32K], and together
    they turn a [semax_body] for one of the six logical functions into
    a single rewrite chain. *)

Lemma w32_of_int_and (a b : Int.int) :
  w32_of_int (Int.and a b) = wand (w32_of_int a) (w32_of_int b).
Proof.
rewrite int_and_wand.
rewrite int_of_w32K.
reflexivity.
Qed.

Lemma w32_of_int_or (a b : Int.int) :
  w32_of_int (Int.or a b) = wor (w32_of_int a) (w32_of_int b).
Proof.
rewrite int_or_wor.
rewrite int_of_w32K.
reflexivity.
Qed.

Lemma w32_of_int_xor (a b : Int.int) :
  w32_of_int (Int.xor a b) = wxor (w32_of_int a) (w32_of_int b).
Proof.
rewrite int_xor_wxor.
rewrite int_of_w32K.
reflexivity.
Qed.

Lemma w32_of_int_not (a : Int.int) :
  w32_of_int (Int.not a) = wnot (w32_of_int a).
Proof.
rewrite int_not_wnot.
rewrite int_of_w32K.
reflexivity.
Qed.

Lemma w32_of_int_add (a b : Int.int) :
  w32_of_int (Int.add a b) = (w32_of_int a + w32_of_int b)%R.
Proof.
rewrite int_add_wadd.
rewrite int_of_w32K.
reflexivity.
Qed.

Lemma w32_of_int_shru (a : Int.int) (n : Z) :
  0 <= n < 32 -> w32_of_int (Int.shru a (Int.repr n)) = SHR n (w32_of_int a).
Proof.
intros Hn.
rewrite (int_shru_SHR a n); [exact Hn |].
rewrite int_of_w32K.
reflexivity.
Qed.

Lemma w32_of_int_shl (a : Int.int) (n : Z) :
  0 <= n < 32 -> w32_of_int (Int.shl a (Int.repr n)) = wshl (w32_of_int a) n.
Proof.
intros Hn.
rewrite (int_shl_wshl a n); [exact Hn |].
rewrite int_of_w32K.
reflexivity.
Qed.

(** The rotation, pushed inwards. [0 < n < 32] as in [int_ROTR]. *)
Lemma w32_of_int_ROTR (a : Int.int) (n : Z) :
  0 < n < 32 ->
  w32_of_int (Int.or (Int.shru a (Int.repr n)) (Int.shl a (Int.repr (32 - n))))
  = ROTR n (w32_of_int a).
Proof.
intros Hn.
rewrite (int_ROTR a n); [exact Hn |].
rewrite int_of_w32K.
reflexivity.
Qed.
