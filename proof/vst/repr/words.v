(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Vst.repr.words: words as C byte arrays

    The 32-byte codec both C modules speak: [w256] and its [list val] /
    [list byte] views, the lengths and indexed-access lemmas that let a
    [Znth] pass through the codec, the surgery that cuts a
    [tarray tuchar] into pieces for a call and puts it back, and the
    funspec notations built on all of it.

    [w256] carries the complete SHA-256 digest. The model-side bridge
    in [Vst.contract.trusted] connects that word to model byte lists. *)

From Vst Require Export base.
From Vst.repr Require Export seqlist.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Words as C byte arrays *)

(* The WITH-telescope carrier for 256-bit words: DEFINITIONALLY the
   carrier of [word U256], but universe-small, so veric's rmaps.TypeTree
   machinery does not swallow the HB comRingType pack (whose universes
   clash with any .vo that loaded [deriving]). The spelling is now
   UPSTREAM:
   [wcarrier] ships in SSProve's jasmin_word (branch interop-vst,
   commit 379cba1); this alias only keeps the local name. *)
Definition w256 : Type := wcarrier U256.

Definition word_to_vals (w : word U256) : list Values.val :=
  List.map (fun z : Z => Vubyte (Byte.repr z)) (bytes_of_word U256 w).

(* The same 32 bytes as a [list byte]. [data_at] over a [tarray
   tuchar] in the canonical [List.map Vubyte] shape is what all of
   floyd's load/store automation expects, so the body proofs work with
   this view and convert at the boundaries via [word_to_vals_map]. *)
Definition word_bytes (w : word U256) : list byte :=
  List.map Byte.repr (bytes_of_word U256 w).


(* ================================================================= *)
(** ** Lengths *)

Lemma bytes_of_word_Zlength (w : word U256) : Zlength (bytes_of_word U256 w) = 32.
Proof.
rewrite Zlength_correct.
rewrite <- size_length.
now rewrite bytes_of_word_size.
Qed.

Lemma word_to_vals_Zlength (w : word U256) : Zlength (word_to_vals w) = 32.
Proof.
unfold word_to_vals.
rewrite Zlength_map.
apply bytes_of_word_Zlength.
Qed.

Lemma word_bytes_Zlength (w : word U256) : Zlength (word_bytes w) = 32.
Proof.
unfold word_bytes.
rewrite Zlength_map.
apply bytes_of_word_Zlength.
Qed.

(* The canonical floyd shape for a 32-byte [tuchar] array. *)
Lemma word_to_vals_map (w : word U256) :
  word_to_vals w = List.map Vubyte (word_bytes w).
Proof.
unfold word_to_vals, word_bytes.
rewrite List.map_map.
reflexivity.
Qed.

(* The length side condition every byte-buffer hash contract carries
   ([Zlength msg] must fit the sixty-four-bit length field FIPS 180-4
   SS 5.1.1 appends). At 32 bytes it is arithmetic, but [two_p] is not
   something [lia] evaluates, so it is discharged once here. *)
Lemma word_bytes_len_ok (w : word U256) :
  0 <= Zlength (word_bytes w) < two_p 61.
Proof.
rewrite word_bytes_Zlength.
change (two_p 61) with 2305843009213693952.
lia.
Qed.

(* THE SAME [data_at] IN THE VARIABLE-LENGTH SHAPE a byte-buffer
   contract is written in. src/sha256.c's hash takes a pointer and a
   length, so its funspec quantifies over [msg : list byte] and its
   array is [tarray tuchar (Zlength msg)]; a caller holding one 32-byte
   WORD has [tarray tuchar 32] over [word_to_vals]. The two are the
   same predicate, but not syntactically, and the difference is exactly
   what stops [cancel] at such a call.

   Stated as an EQUALITY so a body proof can go either way across a
   call, and stated so that the [32] appears only on the left: rewriting
   [word_bytes_Zlength] backwards in the goal instead would hit every
   [32] there, including the halves' offsets.

   Apply it WITHOUT naming its arguments. [rewrite] matches
   syntactically, and the callers' halves are spelled
   [@fst (GRing.ComNzRing.sort (word U256)) _ sk] while [fst sk] written
   in a tactic elaborates to [@fst w256 w256 sk] -- convertible, so the
   two print identically, but the explicit form then fails with "Found
   no subterm matching" against a goal that visibly contains it.
   Unification finds it. *)
Lemma word_data_at_bytes (sh : share) (w : word U256) (p : Values.val) :
  data_at sh (tarray tuchar 32) (word_to_vals w) p
  = data_at sh (tarray tuchar (Zlength (word_bytes w)))
            (List.map Vubyte (word_bytes w)) p.
Proof.
rewrite word_bytes_Zlength.
rewrite word_to_vals_map.
reflexivity.
Qed.


(* ================================================================= *)
(** ** Indexed access

    These accessors connect the indexed and whole-list views of the
    big-endian word codec. *)

Lemma nth_bytes_of_word (w : word U256) (i : nat) :
  (i < 32)%nat -> nth 0 (bytes_of_word U256 w) i = byte_of_word U256 w i.
Proof.
intros Hi.
unfold bytes_of_word.
rewrite (nth_map 0%nat).
- (* [nth_map]'s side condition: [i] indexes the iota *)
  rewrite size_iota.
  exact Hi.
- (* entry [i] of [iota 0 32] is [i] itself *)
  rewrite nth_iota.
  + exact Hi.
  + rewrite add0n.
    reflexivity.
Qed.

Lemma Znth_bytes_of_word (w : word U256) (j : Z) :
  0 <= j < 32 -> Znth j (bytes_of_word U256 w) = byte_of_word U256 w (Z.to_nat j).
Proof.
intros Hj.
(* [lia] cannot see mathcomp's boolean [<]; [ltP] bridges the two *)
assert (Hlt : (Z.to_nat j < 32)%nat).
{ apply (introT ltP).
  lia. }
unfold Znth.
destruct (Z_lt_dec j 0) as [Hneg|_].
- (* a negative index contradicts the range hypothesis *)
  exfalso.
  lia.
- rewrite <- nth_seq_list.
  apply nth_bytes_of_word.
  exact Hlt.
Qed.

Lemma Znth_word_bytes (w : word U256) (j : Z) :
  0 <= j < 32 ->
  Byte.unsigned (Znth j (word_bytes w)) = byte_of_word U256 w (Z.to_nat j).
Proof.
intros Hj.
unfold word_bytes.
rewrite Znth_map.
- (* [Znth_map]'s side condition: [j] indexes the 32 bytes *)
  rewrite bytes_of_word_Zlength.
  exact Hj.
- (* [Byte.unsigned] undoes [Byte.repr] because the model's byte is in range *)
  rewrite (Znth_bytes_of_word w j Hj).
  rewrite Byte.unsigned_repr.
  + pose proof (byte_of_word_range U256 w (Z.to_nat j)) as Hrange.
    change Byte.max_unsigned with 255.
    lia.
  + reflexivity.
Qed.

(* The [list byte] view of a word carries exactly the model's [seq Z]
   of its bytes: [word_bytes] is [Byte.repr] of them and every one is
   in range, so [Byte.unsigned] undoes it pointwise. *)
Lemma map_unsigned_word_bytes (w : word U256) :
  List.map Byte.unsigned (word_bytes w) = bytes_of_word U256 w.
Proof.
apply Znth_eq_ext.
- (* both sides are 32 entries long *)
  rewrite Zlength_map.
  rewrite word_bytes_Zlength.
  rewrite bytes_of_word_Zlength.
  reflexivity.
- (* entry [i] of either side is the model's byte [i] *)
  intros i Hi.
  rewrite Zlength_map in Hi.
  rewrite word_bytes_Zlength in Hi.
  rewrite Znth_map.
  + rewrite word_bytes_Zlength.
    exact Hi.
  + rewrite (Znth_word_bytes w i Hi).
    rewrite (Znth_bytes_of_word w i Hi).
    reflexivity.
Qed.


Lemma is_int_Vubyte (c : byte) : is_int I8 Ctypes.Unsigned (Vubyte c).
Proof.
pose proof (Byte.unsigned_range_2 c) as Hr.
change (Int.unsigned (Int.repr (Byte.unsigned c)) <= Byte.max_unsigned).
rewrite Int.unsigned_repr.
- rep_lia.
- rep_lia.
Qed.


(* ================================================================= *)
(** ** Cutting a [tarray tuchar] into pieces

    Every callee in this development takes a window of a buffer its
    caller owns whole, so each call is bracketed by a cut and a join.
    These are floyd's [split2_data_at_Tarray_tuchar] and
    [split3_data_at_Tarray_tuchar] with the [field_address0]s resolved
    to the [offset_val] the Clight expression actually evaluates to,
    which is the shape [forward_call] has to match.
    [field_compatible_array_smaller0] is what lets a cut be applied
    again to a piece.

    [tuchar_split3] carries the window width [w] as a parameter, so the
    windows the C takes -- 4 bytes out of 64 in sha256_parse, 64 out of
    m in sha256_compress_blocks, and 4 out of 32 in the digest store of
    sha256 are instances of one lemma. The [_bytes] variants are the
    same cut seen through the [List.map Vubyte] view the byte-array
    funspecs are stated in. *)

(* [field_compatible_array_smaller0] with the arguments in the order a
   cut of a cut needs them: having split a buffer once, the piece a
   further cut applies to is a PREFIX of the original, and its
   compatibility is what the next [tuchar_split] asks for. *)
Lemma field_compatible_tuchar_prefix (p : Values.val) (m n : Z) :
  0 <= n <= m ->
  field_compatible (tarray tuchar m) [] p ->
  field_compatible (tarray tuchar n) [] p.
Proof.
intros Hn Hfc.
apply (field_compatible_array_smaller0 tuchar n m).
- exact Hfc.
- lia.
Qed.

Lemma tuchar_split (sh : share) (p : Values.val) (v : list Values.val) (m k : Z) :
  Zlength v = m -> 0 <= k <= m ->
  field_compatible (tarray tuchar m) [] p ->
  data_at sh (tarray tuchar m) v p =
  (data_at sh (tarray tuchar k) (sublist 0 k v) p *
   data_at sh (tarray tuchar (m - k)) (sublist k m v) (offset_val k p))%logic.
Proof.
intros Hv Hk Hfc.
rewrite (split2_data_at_Tarray_tuchar sh m k v p Hk Hv).
(* resolve floyd's [field_address0] to the [offset_val] the C computes *)
rewrite (arr_field_address0 tuchar m p k Hfc Hk).
change (sizeof tuchar) with 1.
rewrite Z.mul_1_l.
reflexivity.
Qed.

Lemma tuchar_split_bytes (sh : share) (p : Values.val) (bs : list byte) (m k : Z) :
  Zlength bs = m -> 0 <= k <= m ->
  field_compatible (tarray tuchar m) [] p ->
  data_at sh (tarray tuchar m) (List.map Vubyte bs) p =
  (data_at sh (tarray tuchar k) (List.map Vubyte (sublist 0 k bs)) p *
   data_at sh (tarray tuchar (m - k)) (List.map Vubyte (sublist k m bs))
     (offset_val k p))%logic.
Proof.
intros Hbs Hk Hfc.
rewrite (tuchar_split sh p (List.map Vubyte bs) m k
  ltac:(rewrite Zlength_map; exact Hbs) Hk Hfc).
rewrite !sublist_map.
reflexivity.
Qed.

(* The three-way cut: the [w]-byte window at offset [k], with the
   prefix before it and the remainder after it. *)
Lemma tuchar_split3 (sh : share) (p : Values.val) (v : list Values.val) (m w k : Z) :
  Zlength v = m -> 0 <= w -> 0 <= k -> k + w <= m ->
  field_compatible (tarray tuchar m) [] p ->
  data_at sh (tarray tuchar m) v p =
  (data_at sh (tarray tuchar k) (sublist 0 k v) p *
   data_at sh (tarray tuchar w) (sublist k (k + w) v) (offset_val k p) *
   data_at sh (tarray tuchar (m - (k + w))) (sublist (k + w) m v)
     (offset_val (k + w) p))%logic.
Proof.
intros Hv Hw Hk0 Hkm Hfc.
rewrite (split3_data_at_Tarray_tuchar sh m k (k + w) v p
  ltac:(lia) ltac:(lia) Hv).
replace (k + w - k) with w by lia.
(* resolve both [field_address0]s to the [offset_val]s the C computes *)
rewrite (arr_field_address0 tuchar m p k Hfc ltac:(lia)).
rewrite (arr_field_address0 tuchar m p (k + w) Hfc ltac:(lia)).
change (sizeof tuchar) with 1.
rewrite !Z.mul_1_l.
reflexivity.
Qed.

Lemma tuchar_split3_bytes (sh : share) (p : Values.val) (bs : list byte) (m w k : Z) :
  Zlength bs = m -> 0 <= w -> 0 <= k -> k + w <= m ->
  field_compatible (tarray tuchar m) [] p ->
  data_at sh (tarray tuchar m) (List.map Vubyte bs) p =
  (data_at sh (tarray tuchar k) (List.map Vubyte (sublist 0 k bs)) p *
   data_at sh (tarray tuchar w) (List.map Vubyte (sublist k (k + w) bs))
     (offset_val k p) *
   data_at sh (tarray tuchar (m - (k + w))) (List.map Vubyte (sublist (k + w) m bs))
     (offset_val (k + w) p))%logic.
Proof.
intros Hbs Hw Hk0 Hkm Hfc.
rewrite (tuchar_split3 sh p (List.map Vubyte bs) m w k
  ltac:(rewrite Zlength_map; exact Hbs) Hw Hk0 Hkm Hfc).
rewrite !sublist_map.
reflexivity.
Qed.


(* ================================================================= *)
(** ** The funspec notations *)

Notation "p '|->32' [ sh ] w" :=
  (data_at sh (tarray tuchar 32) (word_to_vals w) p)
  (at level 30, sh at level 0, w at level 30) : assert.

Notation "p '|->_32' [ sh ]" :=
  (data_at_ sh (tarray tuchar 32) p)
  (at level 30, sh at level 0) : assert.

Notation "'Vuint' n" := (Vint (Int.repr n)) (at level 10, n at level 9).
