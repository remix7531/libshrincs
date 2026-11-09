(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_sha256: proof of body_sha256

    SS 6.2 in general: the arbitrary-length entry point. The only
    place in src/sha256.c where the padding of SS 5.1.1 is computed
    rather than known, and the only place with 64-bit arithmetic.

    THERE IS NO BLOCK LOOP HERE. Both runs of blocks -- the message
    proper and the padded tail -- go through [sha256_compress_blocks],
    so this file has two [forward_call]s where an earlier version had
    two loops, and the fold-prefix invariant lives in
    Verif_compress_blocks instead. What is left of the first call is
    the obligation that the caller's array, viewed as [nblocks] whole
    blocks, is [sublist 0 (64 * nblocks)] of it: one split, and the
    same equation run backwards to put it together again.

    THE TAIL. Two fixed-shape loops (zero-fill 128, copy [rem]) and
    one store (the 0x80 byte), then the length field, then one more
    [forward_call]. The obligation is that the bytes the C assembles
    in [tail] are the last one or two blocks of [pad msgZ] -- i.e.
    that

      rem < 56  <->  the padding fits one block

    matches [padzeros]. [padzeros_tail] is that arithmetic, in the
    form the C's [if] hands it over: [(55 - n) mod 64] against
    [n mod 64]. [sha256_split] is the whole correspondence, and it is
    the one lemma in this file worth reading.

    THE LENGTH FIELD. The C stores [inlen >> 29] and
    [(uint32_t)inlen << 3] as the two halves of the 64-bit bit-length.
    Exactness of the high half is what [0 <= Zlength msg < 2^61] in
    the funspec (and include/sha256.h) is for; [len_bytes_split] is
    where that bound is discharged, and it is 64-bit reasoning, so the
    bounds are [Int64.max_unsigned] and NOT [Int.max_unsigned].

    SCOPE TRAP, and the reason every list below carries an explicit
    [%list]. With mathcomp's seq_scope on top of the stack a bare [++]
    is mathcomp's [cat], not [List.app] -- the two are different
    constants, Vst.base's [catE] is the bridge, and floyd's
    [list_solve] only knows [app]. [pad] is built with [cat]; every
    loop invariant is built with [app]. *)

From Vst.repr Require Import words.
From Vst.sha256 Require Import bridge.
From Vst.sha256 Require Import tables.
From Vst.sha256 Require Import contract.
From Vst Require Import settings.
From Vst.sha256 Require Import clone.
From Vst.clight Require Import sha256.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

(** [Znth] over a [seq w32] needs a default element; every index this
    file takes is in range, so any word will do. *)

#[local] Instance Inhabitant_w32 : Inhabitant w32 := w32_0.

(* ================================================================= *)
(** ** Bytes as [Byte.repr] of a [seq Z]

    The model's byte lists are [seq Z]; a [data_at] over a
    [tarray tuchar] holds [byte]s. These two say the round trip is the
    identity on the ranges the padding produces. The seq/list spelling
    bridges the proof also needs ([catE], [repeatE], [take_firstn],
    [sublist_take_drop], ...) are Vst.base's. *)

Lemma map_Vubyte_repr (l : seq Z) :
  List.map (fun z : Z => Vubyte (Byte.repr z)) l = List.map Vubyte (List.map Byte.repr l).
Proof. now rewrite List.map_map. Qed.

Lemma map_unsigned_repr (l : seq Z) :
  (forall z, List.In z l -> 0 <= z < 256) ->
  List.map Byte.unsigned (List.map Byte.repr l) = l.
Proof.
induction l as [|z l IH]; intros Hall.
- reflexivity.
- assert (Hz : 0 <= z <= Byte.max_unsigned).
  { assert (Hz256 : 0 <= z < 256) by (apply Hall; left; reflexivity).
    change Byte.max_unsigned with 255.
    lia. }
  assert (Hl : forall y, List.In y l -> 0 <= y < 256).
  { intros y Hy.
    apply Hall.
    right.
    exact Hy. }
  simpl.
  rewrite (Byte.unsigned_repr z Hz).
  rewrite (IH Hl).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 5.1.1: how many zero bytes, and one tail block or two

    The C decides on [rem < 56]; the specification says [padzeros].
    This is the one equation that reconciles them, and the [if] on the
    right is literally the C's. *)

Lemma padzeros_tail (n : Z) :
  0 <= n ->
  n mod 64 + 9 + padzeros n = (if n mod 64 <? 56 then 64 else 128).
Proof.
intros Hn.
assert (Hr := Z.mod_pos_bound n 64 ltac:(lia)).
assert (H55 : 55 mod 64 = 55) by reflexivity.
assert (He : (55 - n) mod 64 = (55 - n mod 64) mod 64).
{ rewrite Zminus_mod.
  rewrite H55.
  rewrite <- Zminus_mod_idemp_r.
  reflexivity. }
unfold padzeros.
rewrite He.
destruct (Z.ltb_spec0 (n mod 64) 56) as [Hc | Hc].
- (* the 0x80 byte, the zeros and the length field fit one block *)
  rewrite (Z.mod_small (55 - n mod 64) 64); lia.
- (* they need a second block, so the zero run wraps past 64 *)
  assert ((55 - n mod 64) mod 64 = 119 - n mod 64) as ->.
  { assert (55 - n mod 64 = (119 - n mod 64) + (-1) * 64) as -> by lia.
    rewrite Z_mod_plus_full.
    rewrite (Z.mod_small (119 - n mod 64) 64); lia. }
  lia.
Qed.

(* ================================================================= *)
(** ** SS 5.1.1: the 64-bit length field as the two halves the C stores

    [len_bytes] renders 8*n as eight big-endian bytes; the C stores it
    as [inlen >> 29] and [(uint32_t)inlen << 3] through two
    [store_be32] calls. [len_bytes_split] says those are the same
    eight bytes, and it is where [Zlength msg < 2^61] is spent. *)

Lemma bytes_of_word_U64_eq (w : word U64) :
  bytes_of_word U64 w
  = [:: Z.land (Z.shiftr (wunsigned w) 56) 255;
        Z.land (Z.shiftr (wunsigned w) 48) 255;
        Z.land (Z.shiftr (wunsigned w) 40) 255;
        Z.land (Z.shiftr (wunsigned w) 32) 255;
        Z.land (Z.shiftr (wunsigned w) 24) 255;
        Z.land (Z.shiftr (wunsigned w) 16) 255;
        Z.land (Z.shiftr (wunsigned w) 8) 255;
        Z.land (Z.shiftr (wunsigned w) 0) 255].
Proof. reflexivity. Qed.

Lemma Zlength_bytes_of_word_U32 (w : word U32) : Zlength (bytes_of_word U32 w) = 4.
Proof.
rewrite Zlength_size.
rewrite bytes_of_word_size.
reflexivity.
Qed.

Lemma bytes_of_word_U32_range (w : word U32) (z : Z) :
  List.In z (bytes_of_word U32 w) -> 0 <= z < 256.
Proof.
assert (Hgen : forall k : Z, 0 <= Z.land (Z.shiftr (wunsigned w) k) 255 < 256).
{ intros k.
  assert (255 = Z.ones 8) as -> by reflexivity.
  rewrite (Z.land_ones (Z.shiftr (wunsigned w) k) 8 ltac:(lia)).
  apply Z.mod_pos_bound.
  reflexivity. }
rewrite bytes_of_word_U32_eq.
(* membership in a four-element list is a four-way disjunction of equations *)
intros [<- | [<- | [<- | [<- | Hfalse]]]].
- apply Hgen.
- apply Hgen.
- apply Hgen.
- apply Hgen.
- destruct Hfalse.
Qed.

Lemma map_unsigned_bytes_U32 (w : word U32) :
  List.map Byte.unsigned (List.map Byte.repr (bytes_of_word U32 w)) = bytes_of_word U32 w.
Proof.
apply map_unsigned_repr.
intros z Hz.
exact (bytes_of_word_U32_range w z Hz).
Qed.

Lemma wbase_U64_eq : wbase U64 = 2 ^ 64.
Proof. vm_compute. reflexivity. Qed.

Lemma land255_shiftr_mod (v k : Z) :
  0 <= k -> k + 8 <= 32 ->
  Z.land (Z.shiftr (v mod 2 ^ 32) k) 255 = Z.land (Z.shiftr v k) 255.
Proof.
intros Hk Hk8.
assert (H255 : 255 = Z.ones 8) by reflexivity.
apply Z.bits_inj'.
intros i Hi.
rewrite !Z.land_spec.
rewrite H255.
rewrite (Z.testbit_ones 8 i ltac:(lia)).
assert ((0 <=? i) = true) as -> by (apply Z.leb_le; exact Hi).
rewrite andTb.
rewrite (Z.shiftr_spec (v mod 2 ^ 32) k i Hi).
rewrite (Z.shiftr_spec v k i Hi).
destruct (Z.ltb_spec0 i 8) as [Hi8 | Hi8].
- (* bit [k + i] sits below the 32-bit cut, so the [mod] does not reach it *)
  rewrite !andbT.
  apply Z.mod_pow2_bits_low.
  lia.
- (* the mask has no bit there, so both sides are [false] *)
  rewrite !andbF.
  reflexivity.
Qed.

Lemma len_bytes_split (n : Z) (hi lo : Int.int) :
  0 <= n < two_p 61 ->
  Int.unsigned hi = 8 * n / 2 ^ 32 ->
  Int.unsigned lo = (8 * n) mod 2 ^ 32 ->
  len_bytes n = bytes_of_word U32 (w32_of_int hi) ++ bytes_of_word U32 (w32_of_int lo).
Proof.
intros Hn Hhi Hlo.
rewrite two_p_equiv in Hn.
assert (Hw : wunsigned (wrepr U64 (8 * n)) = 8 * n).
{ apply wunsigned_repr_small.
  rewrite wbase_U64_eq.
  lia. }
assert (Hdiv := Z.shiftr_div_pow2 (8 * n) 32 ltac:(lia)).
unfold len_bytes.
rewrite bytes_of_word_U64_eq.
rewrite !bytes_of_word_U32_eq.
rewrite !wunsigned_w32_of_int.
rewrite Hhi.
rewrite Hlo.
rewrite Hw.
rewrite <- Hdiv.
rewrite !Z.shiftr_shiftr; try lia.
rewrite !land255_shiftr_mod; try lia.
reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 5.2.1 and 6.2.2: a run of blocks splits at a block boundary

    [compress_blocks] is a [foldl] over [parse_blocks], and
    [parse_blocks] cuts its argument into 64-byte pieces. Splitting
    the argument at a multiple of 64 therefore splits the fold, which
    is what makes the C's two calls compose into one. *)

Lemma parse_blocks_cons (blk rest : seq Z) :
  size blk = 64%nat -> parse_blocks (blk ++ rest) = parse_block blk :: parse_blocks rest.
Proof.
intros Hblk.
assert (Hnb : nblocks (blk ++ rest) = (nblocks rest).+1).
{ unfold nblocks.
  rewrite size_cat.
  rewrite Hblk.
  assert ((64 + size rest = 1 * 64 + size rest)%nat) as -> by (now rewrite mul1n).
  rewrite divnMDl; [reflexivity |].
  rewrite add1n.
  reflexivity. }
unfold parse_blocks.
rewrite Hnb.
assert (Hio : iota 0 (nblocks rest).+1 = (0 :: iota 1 (nblocks rest))%nat) by reflexivity.
rewrite Hio.
rewrite map_cons.
f_equal.
- (* the first block is [blk] itself *)
  rewrite muln0.
  rewrite drop0.
  rewrite (take_size_cat rest Hblk).
  reflexivity.
- (* the rest are the blocks of [rest], their indices shifted by one *)
  assert (Hio2 : iota 1 (nblocks rest) = [seq (1 + i)%nat | i <- iota 0 (nblocks rest)]).
  { rewrite <- iotaDl.
    reflexivity. }
  rewrite Hio2.
  rewrite <- map_comp.
  apply eq_map.
  intros i.
  simpl.
  f_equal.
  assert ((64 * (1 + i) = 64 * i + 64)%nat) as ->.
  { rewrite mulnDr.
    rewrite muln1.
    rewrite addnC.
    reflexivity. }
  rewrite <- drop_drop.
  rewrite (drop_size_cat rest Hblk).
  reflexivity.
Qed.

Lemma compress_blocks_nil (Hst : seq w32) : compress_blocks Hst [::] = Hst.
Proof. reflexivity. Qed.

Lemma compress_blocks_cons (Hst : seq w32) (blk rest : seq Z) :
  size blk = 64%nat ->
  compress_blocks Hst (blk ++ rest)
  = compress_blocks (compress_words Hst (parse_block blk)) rest.
Proof.
intros Hb.
unfold compress_blocks.
rewrite (parse_blocks_cons blk rest Hb).
reflexivity.
Qed.

Lemma compress_blocks_cat (k : nat) (Hst : seq w32) (b1 b2 : seq Z) :
  size b1 = (64 * k)%nat ->
  compress_blocks Hst (b1 ++ b2) = compress_blocks (compress_blocks Hst b1) b2.
Proof.
revert Hst b1.
induction k as [|k IH]; intros Hst b1 Hs1.
- (* no whole blocks: [b1] is empty and the fold does nothing *)
  assert (b1 = [::]) as ->.
  { apply (elimT eqP).
    rewrite <- size_eq0.
    rewrite Hs1.
    rewrite muln0.
    reflexivity. }
  rewrite cat0s.
  rewrite compress_blocks_nil.
  reflexivity.
- (* peel the first block off [b1] and recurse on the other [k] *)
  assert (Hle : (64 <= size b1)%nat).
  { rewrite Hs1.
    rewrite mulnS.
    apply leq_addr. }
  assert (Hsz1 : size (take 64 b1) = 64%nat).
  { rewrite size_take_min.
    apply (elimT minn_idPl).
    exact Hle. }
  assert (Hsz2 : size (drop 64 b1) = (64 * k)%nat).
  { rewrite size_drop.
    rewrite Hs1.
    rewrite mulnS.
    rewrite addnC.
    rewrite addnK.
    reflexivity. }
  rewrite <- (cat_take_drop 64 b1).
  rewrite <- catA.
  rewrite !(compress_blocks_cons _ _ _ Hsz1).
  apply IH.
  exact Hsz2.
Qed.

Lemma compress_blocks_size (Hst : seq w32) (bs : seq Z) :
  size Hst = 8%nat -> size (compress_blocks Hst bs) = 8%nat.
Proof. exact (foldl_compress_words_size Hst (parse_blocks bs)). Qed.

Lemma pad_split (msgZ : seq Z) (K : nat) :
  pad msgZ
  = take K msgZ
    ++ (drop K msgZ ++ [:: 128] ++ nseq (Z.to_nat (padzeros (msglen msgZ))) 0
        ++ len_bytes (msglen msgZ)).
Proof.
unfold pad.
rewrite (catA (take K msgZ) (drop K msgZ)).
rewrite cat_take_drop.
reflexivity.
Qed.

(* ================================================================= *)
(** ** THE HEART: what the C compressed is [pad msgZ] *)

(** THE HEART. The bytes the C has assembled -- the whole blocks of the
    caller's array, then the 128-byte [tail] cut to its first [tl] --
    are exactly [pad msgZ], split at a whole number of blocks. *)
Lemma sha256_split (msg : list byte) (q r tl : Z) (hi lo : Int.int) :
  0 <= Zlength msg < two_p 61 ->
  0 <= q -> 0 <= r < 64 -> Zlength msg = 64 * q + r ->
  padzeros (Zlength msg) = tl - 9 - r ->
  Int.unsigned hi = 8 * Zlength msg / 2 ^ 32 ->
  Int.unsigned lo = (8 * Zlength msg) mod 2 ^ 32 ->
  compress_blocks
    (compress_blocks clone.H0 (List.map Byte.unsigned (sublist 0 (64 * q) msg)))
    (List.map Byte.unsigned
       (sublist (64 * q) (64 * q + r) msg ++ [Byte.repr 128]
        ++ Zrepeat Byte.zero (tl - 9 - r)
        ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int hi))
        ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int lo)))%list)
  = compress_blocks clone.H0 (pad (List.map Byte.unsigned msg)).
Proof.
intros Hlen Hq0 Hr Hqr Hpz Hhi Hlo.
set msgZ := List.map Byte.unsigned msg.
assert (Hsz : Z.of_nat (size msgZ) = Zlength msg).
{ unfold msgZ.
  rewrite size_map_list.
  rewrite <- Zlength_size.
  reflexivity. }
assert (Hml : msglen msgZ = Zlength msg).
{ unfold msglen.
  rewrite Hsz.
  reflexivity. }
set K := Z.to_nat (64 * q).
assert (HK : Z.of_nat K = 64 * q) by (unfold K; lia).
(* the whole blocks the first call consumed *)
assert (Htake : List.map Byte.unsigned (sublist 0 (64 * q) msg) = take K msgZ).
{ rewrite <- sublist_map.
  change (List.map Byte.unsigned msg) with msgZ.
  rewrite (sublist_0_take (64 * q) msgZ ltac:(lia)).
  reflexivity. }
(* the message bytes the tail carries: everything after the last whole block *)
assert (Hdrop : List.map Byte.unsigned (sublist (64 * q) (64 * q + r) msg) = drop K msgZ).
{ rewrite <- sublist_map.
  change (List.map Byte.unsigned msg) with msgZ.
  rewrite (sublist_take_drop (64 * q) r msgZ ltac:(lia) ltac:(lia)).
  change (Z.to_nat (64 * q)) with K.
  apply take_oversize.
  rewrite size_drop.
  rewrite <- !minusE.
  apply (introT leP).
  lia. }
assert (Hzeros : List.map Byte.unsigned (Zrepeat Byte.zero (tl - 9 - r))
                 = nseq (Z.to_nat (tl - 9 - r)) 0).
{ rewrite map_Zrepeat.
  unfold Zrepeat.
  rewrite repeatE.
  reflexivity. }
assert (H128 : List.map Byte.unsigned [Byte.repr 128] = [:: 128]) by reflexivity.
assert (Hlenb :
          cat (bytes_of_word U32 (w32_of_int hi)) (bytes_of_word U32 (w32_of_int lo))
          = len_bytes (Zlength msg)).
{ rewrite (len_bytes_split (Zlength msg) hi lo Hlen Hhi Hlo).
  reflexivity. }
assert (Hsize1 : size (take K msgZ) = (64 * Z.to_nat q)%nat).
{ rewrite size_take_min.
  assert (minn K (size msgZ) = K) as ->.
  { apply (elimT minn_idPl).
    apply (introT leP).
    lia. }
  unfold K.
  rewrite <- multE.
  lia. }
rewrite Htake.
rewrite !List.map_app.
rewrite Hdrop.
rewrite H128.
rewrite Hzeros.
rewrite !map_unsigned_bytes_U32.
rewrite !catE.
rewrite Hlenb.
rewrite (pad_split msgZ K).
rewrite Hml.
rewrite Hpz.
rewrite (compress_blocks_cat (Z.to_nat q) clone.H0 (take K msgZ) _ Hsize1).
reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 6.2.2: the digest, eight words big-endian

    The funspec's POSTcondition is one [word U256]; the C writes
    thirty-two bytes with eight [store_be32] calls. These say the two
    are the same thirty-two bytes, and where each call's four land. *)

Lemma digest_bytes_cat (l1 l2 : seq w32) :
  digest_bytes (l1 ++ l2) = digest_bytes l1 ++ digest_bytes l2.
Proof.
unfold digest_bytes.
rewrite map_cat.
rewrite flatten_cat.
reflexivity.
Qed.

Lemma bytes_of_digest (Hs : seq w32) :
  size Hs = 8%nat -> bytes_of_word U256 (digest_of Hs) = digest_bytes Hs.
Proof.
intros HHs.
unfold digest_of.
apply bytes_of_word_of_bytes.
- rewrite digest_bytes_size.
  rewrite HHs.
  reflexivity.
- exact (digest_bytes_range Hs).
Qed.

Lemma Zlength_digest_bytes (Hs : seq w32) :
  size Hs = 8%nat -> Zlength (digest_bytes Hs) = 32.
Proof.
intros HH.
rewrite Zlength_size.
rewrite digest_bytes_size.
rewrite HH.
reflexivity.
Qed.

Lemma Zlength_digest_bytes_take (Hs : seq w32) (i : Z) :
  size Hs = 8%nat -> 0 <= i <= 8 ->
  Zlength (digest_bytes (take (Z.to_nat i) Hs)) = 4 * i.
Proof.
intros HH Hi.
rewrite Zlength_size.
rewrite digest_bytes_size.
rewrite size_take_min.
rewrite HH.
assert (minn (Z.to_nat i) 8 = Z.to_nat i) as ->.
{ apply (elimT minn_idPl).
  apply (introT leP).
  lia. }
rewrite <- multE.
lia.
Qed.

Lemma digest_bytes_rcons (Hs : seq w32) (i : nat) :
  (i < size Hs)%nat ->
  digest_bytes (take i.+1 Hs)
  = digest_bytes (take i Hs) ++ bytes_of_word U32 (nth w32_0 Hs i).
Proof.
intros Hi.
unfold digest_bytes.
rewrite (take_nth w32_0 Hi).
rewrite <- cats1.
rewrite map_cat.
rewrite flatten_cat.
f_equal; reflexivity.
Qed.

(** The four digest bytes at offset 4*i are the bytes of the i-th word of
    the final chaining value: what one [store_be32] writes. *)
Lemma sublist_digest_bytes (Hs : seq w32) (i : Z) :
  size Hs = 8%nat -> 0 <= i < 8 ->
  sublist (4 * i) (4 * i + 4) (digest_bytes Hs)
  = bytes_of_word U32 (nth w32_0 Hs (Z.to_nat i)).
Proof.
intros HH Hi.
assert (Hlt : (Z.to_nat i < size Hs)%nat).
{ rewrite HH.
  apply (introT ltP).
  lia. }
assert (HL : Zlength (digest_bytes (take (Z.to_nat i) Hs)) = 4 * i).
{ apply Zlength_digest_bytes_take.
  - exact HH.
  - lia. }
assert (HB : Zlength (bytes_of_word U32 (nth w32_0 Hs (Z.to_nat i))) = 4)
  by apply Zlength_bytes_of_word_U32.
(* Cut the digest at word [i]: the first [i] words, word [i], the rest.
   [list_solve] only knows [List.app], so the cut is stated with [%list]
   and [catE] carries it over to the model's [cat]. *)
assert (Hcut : digest_bytes Hs
               = (digest_bytes (take (Z.to_nat i) Hs)
                  ++ bytes_of_word U32 (nth w32_0 Hs (Z.to_nat i))
                  ++ digest_bytes (drop (Z.to_nat i).+1 Hs))%list).
{ rewrite !catE.
  rewrite catA.
  rewrite <- (digest_bytes_rcons Hs (Z.to_nat i) Hlt).
  rewrite <- digest_bytes_cat.
  rewrite cat_take_drop.
  reflexivity. }
rewrite Hcut.
clear Hcut.
list_solve.
Qed.

(* ================================================================= *)
(** ** The C-side arrays: reads, cuts and reassembly

    Every callee below takes a [tarray tuchar 4] or a [tarray tuchar
    (64 * n)] and this proof owns whole buffers, so each call is
    bracketed by a cut and a join. Vst.base's [tuchar_split] is
    the one [split2_data_at_Tarray_tuchar] behind all of them, and
    [field_compatible_array_smaller0] is what lets it be applied again
    to a piece; what is left here is the reassembly in the shapes this
    proof's [sep_apply]s need. *)

Lemma tuchar_join_bytes (sh : share) (p : Values.val) (bs : list byte) (k : Z) :
  0 <= k <= Zlength bs ->
  field_compatible (tarray tuchar (Zlength bs)) [] p ->
  (data_at sh (tarray tuchar k) (List.map Vubyte (sublist 0 k bs)) p *
   data_at sh (tarray tuchar (Zlength bs - k))
     (List.map Vubyte (sublist k (Zlength bs) bs)) (offset_val k p))%logic
  |-- data_at sh (tarray tuchar (Zlength bs)) (List.map Vubyte bs) p.
Proof.
intros Hk Hfc.
rewrite <- (tuchar_split_bytes sh p bs (Zlength bs) k Logic.eq_refl Hk Hfc).
apply derives_refl.
Qed.

Lemma tuchar_split4 (sh : share) (p : Values.val) (v : list Values.val) (k : Z) :
  Zlength v = 128 -> 0 <= k -> k + 8 <= 128 ->
  field_compatible (tarray tuchar 128) [] p ->
  data_at sh (tarray tuchar 128) v p =
  (data_at sh (tarray tuchar k) (sublist 0 k v) p *
   data_at sh (tarray tuchar 4) (sublist k (k + 4) v) (offset_val k p) *
   data_at sh (tarray tuchar 4) (sublist (k + 4) (k + 8) v) (offset_val (k + 4) p) *
   data_at sh (tarray tuchar (128 - (k + 8))) (sublist (k + 8) 128 v)
     (offset_val (k + 8) p))%logic.
Proof.
intros Hv Hk Hk8 Hfc.
assert (Hfc8 : field_compatible (tarray tuchar (k + 8)) [] p)
  by (apply (field_compatible_tuchar_prefix p 128); [lia | exact Hfc]).
assert (Hfc4 : field_compatible (tarray tuchar (k + 4)) [] p)
  by (apply (field_compatible_tuchar_prefix p 128); [lia | exact Hfc]).
assert (E1 : sublist 0 (k + 4) (sublist 0 (k + 8) v) = sublist 0 (k + 4) v) by list_solve.
assert (E2 : sublist (k + 4) (k + 8) (sublist 0 (k + 8) v) = sublist (k + 4) (k + 8) v)
  by list_solve.
assert (E3 : sublist 0 k (sublist 0 (k + 4) v) = sublist 0 k v) by list_solve.
assert (E4 : sublist k (k + 4) (sublist 0 (k + 4) v) = sublist k (k + 4) v) by list_solve.
rewrite (tuchar_split sh p v 128 (k + 8) Hv ltac:(lia) Hfc).
rewrite (tuchar_split sh p (sublist 0 (k + 8) v) (k + 8) (k + 4) ltac:(list_solve)
                      ltac:(lia) Hfc8).
rewrite E1.
rewrite E2.
rewrite (tuchar_split sh p (sublist 0 (k + 4) v) (k + 4) k ltac:(list_solve)
                      ltac:(lia) Hfc4).
rewrite E3.
rewrite E4.
assert (k + 8 - (k + 4) = 4) as -> by lia.
assert (k + 4 - k = 4) as -> by lia.
reflexivity.
Qed.

Lemma tail_cut (sh : share) (p : Values.val) (v : list Values.val) (k : Z) :
  Zlength v = 128 -> 0 <= k -> k + 8 <= 128 ->
  field_compatible (tarray tuchar 128) [] p ->
  data_at sh (tarray tuchar 128) v p
  |-- (data_at sh (tarray tuchar k) (sublist 0 k v) p *
       data_at_ sh (tarray tuchar 4) (offset_val k p) *
       data_at_ sh (tarray tuchar 4) (offset_val (k + 4) p) *
       data_at sh (tarray tuchar (128 - (k + 8))) (sublist (k + 8) 128 v)
         (offset_val (k + 8) p))%logic.
Proof.
intros Hv Hk Hk8 Hfc.
rewrite (tuchar_split4 sh p v k Hv Hk Hk8 Hfc).
sep_apply (data_at_data_at_ sh (tarray tuchar 4) (sublist k (k + 4) v) (offset_val k p)).
sep_apply (data_at_data_at_ sh (tarray tuchar 4) (sublist (k + 4) (k + 8) v)
             (offset_val (k + 4) p)).
cancel.
Qed.

Lemma tail_glue3 (sh : share) (p : Values.val) (a b c : list Values.val) (k k4 k8 : Z) :
  0 <= k -> k4 = k + 4 -> k8 = k + 8 -> k8 <= 128 ->
  Zlength a = k -> Zlength b = 4 -> Zlength c = 4 ->
  field_compatible (tarray tuchar 128) [] p ->
  (data_at sh (tarray tuchar k) a p *
   data_at sh (tarray tuchar 4) b (offset_val k p) *
   data_at sh (tarray tuchar 4) c (offset_val k4 p))%logic
  |-- data_at sh (tarray tuchar k8) (a ++ b ++ c)%list p.
Proof.
intros Hk Hk4 Hk8 Hle Ha Hb Hc Hfc.
subst k4 k8.
assert (Hfc8 : field_compatible (tarray tuchar (k + 8)) [] p)
  by (apply (field_compatible_tuchar_prefix p 128); [lia | exact Hfc]).
assert (Hfc4 : field_compatible (tarray tuchar (k + 4)) [] p)
  by (apply (field_compatible_tuchar_prefix p 128); [lia | exact Hfc]).
rewrite (tuchar_split sh p (a ++ b ++ c)%list (k + 8) (k + 4) ltac:(list_solve)
                      ltac:(lia) Hfc8).
assert (sublist 0 (k + 4) (a ++ b ++ c)%list = (a ++ b)%list) as -> by list_solve.
assert (sublist (k + 4) (k + 8) (a ++ b ++ c)%list = c) as -> by list_solve.
rewrite (tuchar_split sh p (a ++ b)%list (k + 4) k ltac:(list_solve) ltac:(lia) Hfc4).
assert (sublist 0 k (a ++ b)%list = a) as -> by list_solve.
assert (sublist k (k + 4) (a ++ b)%list = b) as -> by list_solve.
assert (k + 8 - (k + 4) = 4) as -> by lia.
assert (k + 4 - k = 4) as -> by lia.
cancel.
Qed.

Lemma tail_rejoin (sh : share) (p : Values.val) (k : Z) :
  0 <= k <= 128 -> field_compatible (tarray tuchar 128) [] p ->
  (data_at_ sh (tarray tuchar k) p
   * data_at_ sh (tarray tuchar (128 - k)) (offset_val k p))%logic
  |-- data_at_ sh (tarray tuchar 128) p.
Proof.
intros Hk Hfc.
rewrite (split2_data_at__Tarray_tuchar sh 128 k p Hk ltac:(exact (proj1 Hfc)) Hfc).
rewrite (arr_field_address0 tuchar 128 p k Hfc Hk).
change (sizeof tuchar) with 1.
rewrite Z.mul_1_l.
cancel.
Qed.

Lemma out_glue (sh : share) (p : Values.val) (a b c : list Values.val) (k k4 : Z) :
  0 <= k -> k4 = k + 4 -> k + 4 <= 32 ->
  Zlength a = k -> Zlength b = 4 -> Zlength c = 32 - (k + 4) ->
  field_compatible (tarray tuchar 32) [] p ->
  (data_at sh (tarray tuchar k) a p *
   data_at sh (tarray tuchar 4) b (offset_val k p) *
   data_at sh (tarray tuchar (32 - k4)) c (offset_val k4 p))%logic
  |-- data_at sh (tarray tuchar 32) (a ++ b ++ c)%list p.
Proof.
intros Hk Hk4 Hk4' Ha Hb Hc Hfc.
subst k4.
rewrite (tuchar_split3 sh p (a ++ b ++ c)%list 32 4 k
           ltac:(list_solve) ltac:(lia) Hk Hk4' Hfc).
assert (sublist 0 k (a ++ b ++ c)%list = a) as -> by list_solve.
assert (sublist k (k + 4) (a ++ b ++ c)%list = b) as -> by list_solve.
assert (sublist (k + 4) 32 (a ++ b ++ c)%list = c) as -> by list_solve.
cancel.
Qed.

(* ================================================================= *)
(** ** One iteration of each fill loop

    Four arrays are filled a piece at a time, and each loop's invariant
    is "the first i entries, then what was there before". These say
    that writing entry i extends that prefix by one. *)

Lemma Vint_zext8_0 : Vint (Int.zero_ext 8 (Int.repr 0)) = Vubyte Byte.zero.
Proof. reflexivity. Qed.

Lemma Vint_zext8_128 : Vint (Int.zero_ext 8 (Int.repr 128)) = Vubyte (Byte.repr 128).
Proof. reflexivity. Qed.

Lemma copy_step (bs : list byte) (K i : Z) :
  0 <= K -> 0 <= i -> K + i < Zlength bs -> i + 1 <= 128 ->
  upd_Znth i ((List.map Vubyte (sublist K (K + i) bs)
               ++ Zrepeat (Vubyte Byte.zero) (128 - i))%list)
           (Vubyte (Znth (K + i) bs))
  = (List.map Vubyte (sublist K (K + (i + 1)) bs)
     ++ Zrepeat (Vubyte Byte.zero) (128 - (i + 1)))%list.
Proof. intros HK Hi HKi H128. list_solve. Qed.

Lemma mark_step (bs : list byte) (K r : Z) :
  0 <= K -> 0 <= r < 64 -> K + r = Zlength bs ->
  upd_Znth r ((List.map Vubyte (sublist K (K + r) bs)
               ++ Zrepeat (Vubyte Byte.zero) (128 - r))%list)
           (Vubyte (Byte.repr 128))
  = (List.map Vubyte (sublist K (K + r) bs) ++ [Vubyte (Byte.repr 128)]
     ++ Zrepeat (Vubyte Byte.zero) (127 - r))%list.
Proof. intros HK Hr HKr. list_solve. Qed.

Lemma tail_marked_map (bs : list byte) (K r : Z) :
  (List.map Vubyte (sublist K (K + r) bs) ++ [Vubyte (Byte.repr 128)]
   ++ Zrepeat (Vubyte Byte.zero) (127 - r))%list
  = List.map Vubyte (sublist K (K + r) bs ++ [Byte.repr 128]
                     ++ Zrepeat Byte.zero (127 - r))%list.
Proof.
rewrite !List.map_app.
rewrite map_Zrepeat.
reflexivity.
Qed.

Lemma tail_head_prefix (bs : list byte) (K r m : Z) :
  0 <= K -> 0 <= r -> K + r <= Zlength bs -> 0 <= m -> r + 1 + m <= 128 ->
  sublist 0 (r + 1 + m) ((sublist K (K + r) bs ++ [Byte.repr 128]
                          ++ Zrepeat Byte.zero (127 - r))%list)
  = (sublist K (K + r) bs ++ [Byte.repr 128] ++ Zrepeat Byte.zero m)%list.
Proof. intros HK Hr HKr Hm Hrm. list_solve. Qed.

Lemma tail_full_map (bs : list byte) (K r m t8 : Z) (hi lo : Int.int) :
  0 <= K -> 0 <= r -> K + r <= Zlength bs -> 0 <= m -> r + 1 + m <= 128 ->
  t8 = r + 1 + m ->
  (sublist 0 t8 (List.map Vubyte (sublist K (K + r) bs ++ [Byte.repr 128]
                                  ++ Zrepeat Byte.zero (127 - r))%list)
   ++ List.map (fun z : Z => Vubyte (Byte.repr z)) (bytes_of_word U32 (w32_of_int hi))
   ++ List.map (fun z : Z => Vubyte (Byte.repr z)) (bytes_of_word U32 (w32_of_int lo)))%list
  = List.map Vubyte
      (sublist K (K + r) bs ++ [Byte.repr 128] ++ Zrepeat Byte.zero m
       ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int hi))
       ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int lo)))%list.
Proof.
intros HK Hr HKr Hm Hrm Ht8.
subst t8.
rewrite sublist_map.
rewrite (tail_head_prefix bs K r m HK Hr HKr Hm Hrm).
rewrite !map_Vubyte_repr.
rewrite !List.map_app.
rewrite <- !List.app_assoc.
reflexivity.
Qed.

(** One iteration of the digest loop: storing word i extends the written
    prefix of the digest by four bytes. [D] is the finished digest as
    [val]s; it is a parameter rather than the term itself so that the loop
    body can carry it under one name instead of four copies. *)
Lemma digest_out_step (Hs : seq w32) (D : list Values.val) (i : Z) :
  D = List.map (fun z : Z => Vubyte (Byte.repr z)) (digest_bytes Hs) ->
  size Hs = 8%nat -> 0 <= i < 8 ->
  (sublist 0 (4 * i) ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list)
   ++ List.map (fun z : Z => Vubyte (Byte.repr z))
        (bytes_of_word U32 (nth w32_0 Hs (Z.to_nat i)))
   ++ sublist (4 * i + 4) 32
        ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list))%list
  = (sublist 0 (4 * (i + 1)) D ++ Zrepeat Vundef (32 - 4 * (i + 1)))%list.
Proof.
intros HDdef HH Hi.
subst D.
assert (HD : Zlength (List.map (fun z : Z => Vubyte (Byte.repr z)) (digest_bytes Hs)) = 32).
{ rewrite Zlength_map.
  rewrite (Zlength_digest_bytes Hs HH).
  reflexivity. }
assert (HB : List.map (fun z : Z => Vubyte (Byte.repr z))
               (bytes_of_word U32 (nth w32_0 Hs (Z.to_nat i)))
             = sublist (4 * i) (4 * i + 4)
                 (List.map (fun z : Z => Vubyte (Byte.repr z)) (digest_bytes Hs))).
{ rewrite sublist_map.
  rewrite (sublist_digest_bytes Hs i HH Hi).
  reflexivity. }
rewrite HB.
list_solve.
Qed.

(* ================================================================= *)
(** ** The body proof *)
Lemma body_sha256 : semax_body Vprog_sha Gprog_sha f_shrincs_sha256 spec_sha256.
Proof.
start_function.
rename H into Hlen.

(* ===== Setup: the standing facts every stage below stands on =====
   [Htp] is the funspec's [two_p 61] in the literal form [rep_lia] and
   [lia] can use; it is spent again at [sha256_split]. The three
   [field_compatible] facts are what lets each buffer be cut apart for a
   call and put back after, and all three are derivable from the
   precondition, so they are taken once here rather than mid-proof. *)
assert (Htp : two_p 61 = 2305843009213693952) by (vm_compute; reflexivity).
rewrite Htp in Hlen.
assert_PROP (field_compatible (tarray tuchar (Zlength msg)) [] in_ptr)
  as Hfcin by entailer!.
assert_PROP (field_compatible (tarray tuchar 128) [] v_tail) as Hfct by entailer!.
assert_PROP (field_compatible (tarray tuchar 32) [] out_ptr) as Hfco by entailer!.
assert (Hptr : isptr v_tail) by (exact (proj1 Hfct)).

(* ===== Stage 1: the two FIPS tables, as C initialisers =====
     uint32_t H[8] = SHA256_H0_INIT;               (SS 5.3.3)
     const uint32_t sha256_K[64] = SHA256_K_INIT;  (SS 4.2.2)
   Both are function locals, so clightgen expands each braced
   initialiser into a run of straight-line stores and the array reaches
   the first call as an [upd_Znth] chain over [default_val] rather than
   as a table. [replace_SEP] renames the chain as the model's table;
   [entailer!] leaves exactly the two [data_at] to be reconciled.

   The step across is [K_C_is_K] / [H0_C_is_H0] and NOT [reflexivity]:
   clightgen renders an entry above 2^31 as a negative literal, and
   [Int.repr] carries an opaque range proof beside its residue, so two
   equal [Int.int] are not convertible. Those two lemmas are the only
   place the C's numerals and FIPS's meet. *)
do 8 forward.
do 64 forward.
replace_SEP 1 (data_at Tsh (tarray tuint 64) (words_to_vals K) v_sha256_K).
{ entailer!.
  apply derives_refl'.
  f_equal.
  symmetry.
  rewrite K_C_is_K.
  vm_compute.
  reflexivity. }
replace_SEP 2 (data_at Tsh (tarray tuint 8) (words_to_vals clone.H0) v_H).
{ entailer!.
  apply derives_refl'.
  f_equal.
  symmetry.
  rewrite H0_C_is_H0.
  vm_compute.
  reflexivity. }

(* ===== Stage 2: the block count and the remainder ===== *)
(* nblocks = inlen / 64; *)
forward.
(* rem = inlen % 64; *)
forward.
(* [nblocks] and [rem] are named opaquely. Left as [Zlength msg / 64], floyd's
   value evaluation unfolds [Z.div] into its [Z.div_eucl] let-form and every
   later index goal arrives in that spelling instead of this one. *)
assert (Hqr : exists q r : Z,
          0 <= q /\ 0 <= r < 64 /\ Zlength msg = 64 * q + r /\
          Int64.divu (Int64.repr (Zlength msg))
                     (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr q /\
          Int64.modu (Int64.repr (Zlength msg))
                     (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr r).
{ exists (Zlength msg / 64), (Zlength msg mod 64).
  change (Int.signed (Int.repr 64)) with 64.
  assert (Hd := Z.div_mod (Zlength msg) 64 ltac:(lia)).
  assert (Hm := Z.mod_pos_bound (Zlength msg) 64 ltac:(lia)).
  assert (Hdp : 0 <= Zlength msg / 64) by (apply Z.div_pos; lia).
  split; [exact Hdp |].
  split; [exact Hm |].
  split; [lia |].
  split.
  - unfold Int64.divu.
    rewrite !Int64.unsigned_repr; [rep_lia .. | reflexivity].
  - unfold Int64.modu.
    rewrite !Int64.unsigned_repr; [rep_lia .. | reflexivity]. }
destruct Hqr as [q [r [Hq0 [Hr [Hqr [Hdiv Hmod]]]]]].
rewrite Hdiv.
rewrite Hmod.
clear Hdiv Hmod.

(* ===== Stage 3: SS 6.2.2 on the whole blocks =====
   The caller owns the whole array and the callee wants [nblocks] whole
   blocks, so the call is bracketed by one cut at [64 * q] and the same
   equation run backwards. *)
rewrite (tuchar_split_bytes sh_in in_ptr msg (Zlength msg) (64 * q));
  [reflexivity | lia | exact Hfcin |].
(* sha256_compress_blocks(H, in, nblocks); *)
forward_call (Tsh, sh_in, Tsh, v_H, in_ptr, v_sha256_K,
              clone.H0, sublist 0 (64 * q) msg, q).
(* the cut left the two SEP clauses nested, so the frame is not inferred *)
{ cancel. }
{ rewrite Zlength_sublist; lia. }
sep_apply (tuchar_join_bytes sh_in in_ptr msg (64 * q) ltac:(lia) Hfcin).
clear Hfcin.

(* ===== Stage 4: SS 5.1.1, build the tail buffer =====
   for (i = 0; i < 128; i++) tail[i] = 0; *)
forward_for_simple_bound 128
  (EX i : Z,
   PROP ()
   LOCAL (temp _rem (Vlong (Int64.repr r)); temp _nblocks (Vlong (Int64.repr q));
          lvar _tail (tarray tuchar 128) v_tail;
          lvar _sha256_K (tarray tuint 64) v_sha256_K;
          lvar _H (tarray tuint 8) v_H;
          temp _out out_ptr; temp _in in_ptr;
          temp _inlen (Vlong (Int64.repr (Zlength msg))))
   SEP (data_at Tsh (tarray tuint 8)
          (words_to_vals (compress_blocks clone.H0
             (List.map Byte.unsigned (sublist 0 (64 * q) msg)))) v_H;
        data_at Tsh (tarray tuchar 128)
          ((Zrepeat (Vubyte Byte.zero) i ++ Zrepeat Vundef (128 - i))%list) v_tail;
        data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
        data_at_ sh_out (tarray tuchar 32) out_ptr;
        data_at Tsh (tarray tuint 64) (words_to_vals K) v_sha256_K)).
{ (* entry: the whole 128 bytes are still [Vundef] *)
  entailer!. }
{ (* one iteration *)
  rename H into Hi.
  (* tail[i] = 0; *)
  forward.
  entailer!.
  apply derives_refl'.
  f_equal.
  rewrite Vint_zext8_0.
  list_solve. }
assert ((Zrepeat (Vubyte Byte.zero) 128 ++ Zrepeat Vundef (128 - 128))%list
        = Zrepeat (Vubyte Byte.zero) 128) as -> by list_solve.

(* for (i = 0; i < rem; i++) tail[i] = in[nblocks * 64 + i]; *)
forward_for_simple_bound r
  (EX i : Z,
   PROP ()
   LOCAL (temp _rem (Vlong (Int64.repr r)); temp _nblocks (Vlong (Int64.repr q));
          lvar _tail (tarray tuchar 128) v_tail;
          lvar _sha256_K (tarray tuint 64) v_sha256_K;
          lvar _H (tarray tuint 8) v_H;
          temp _out out_ptr; temp _in in_ptr;
          temp _inlen (Vlong (Int64.repr (Zlength msg))))
   SEP (data_at Tsh (tarray tuint 8)
          (words_to_vals (compress_blocks clone.H0
             (List.map Byte.unsigned (sublist 0 (64 * q) msg)))) v_H;
        data_at Tsh (tarray tuchar 128)
          ((List.map Vubyte (sublist (64 * q) (64 * q + i) msg)
            ++ Zrepeat (Vubyte Byte.zero) (128 - i))%list) v_tail;
        data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
        data_at_ sh_out (tarray tuchar 32) out_ptr;
        data_at Tsh (tarray tuint 64) (words_to_vals K) v_sha256_K)).
{ (* entry: no message byte copied yet, so the prefix is empty *)
  entailer!.
  apply derives_refl'.
  f_equal.
  list_solve. }
{ (* one iteration *)
  rename H into Hi.
  (* t'2 = in[nblocks * 64 + i]; *)
  forward.
  { entailer!.
    apply is_int_Vubyte. }
  assert (q * 64 + i = 64 * q + i) as -> by lia.
  rewrite Znth_map; [lia |].
  (* tail[i] = t'2; *)
  forward.
  entailer!.
  apply derives_refl'.
  f_equal.
  apply copy_step; lia. }

(* SS 5.1.1: tail[rem] = 0x80; the single 1 bit that ends the message *)
forward.
rewrite Vint_zext8_128.
rewrite (mark_step msg (64 * q) r ltac:(lia) Hr ltac:(lia)).
assert (Hpz : r + 9 + padzeros (Zlength msg) = (if r <? 56 then 64 else 128)).
{ assert (Hpt := padzeros_tail (Zlength msg) ltac:(lia)).
  assert (Hmodr : Zlength msg mod 64 = r).
  { rewrite Hqr.
    assert (64 * q + r = r + q * 64) as -> by lia.
    rewrite Z_mod_plus_full.
    rewrite (Z.mod_small r 64); lia. }
  rewrite Hmodr in Hpt.
  exact Hpt. }

(* ===== Stage 5: SS 5.1.1, one tail block or two =====
   if (rem < 56) { tlen = 64; ntail = 1; } else { tlen = 128; ntail = 2; }
   [Hpz] above is [padzeros_tail] specialised to this [r]; each branch
   reduces its [if] and hands the surviving equation to the join. *)
forward_if
  (EX tl : Z, EX nt : Z,
   PROP (tl = Z.mul 64 nt; 1 <= nt <= 2; padzeros (Zlength msg) = tl - 9 - r)
   LOCAL (temp _ntail (Vlong (Int64.repr nt)); temp _tlen (Vlong (Int64.repr tl));
          temp _rem (Vlong (Int64.repr r)); temp _nblocks (Vlong (Int64.repr q));
          lvar _tail (tarray tuchar 128) v_tail;
          lvar _sha256_K (tarray tuint 64) v_sha256_K;
          lvar _H (tarray tuint 8) v_H;
          temp _out out_ptr; temp _in in_ptr;
          temp _inlen (Vlong (Int64.repr (Zlength msg))))
   SEP (data_at Tsh (tarray tuint 8)
          (words_to_vals (compress_blocks clone.H0
             (List.map Byte.unsigned (sublist 0 (64 * q) msg)))) v_H;
        data_at Tsh (tarray tuchar 128)
          ((List.map Vubyte (sublist (64 * q) (64 * q + r) msg)
            ++ [Vubyte (Byte.repr 128)]
            ++ Zrepeat (Vubyte Byte.zero) (127 - r))%list) v_tail;
        data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
        data_at_ sh_out (tarray tuchar 32) out_ptr;
        data_at Tsh (tarray tuint 64) (words_to_vals K) v_sha256_K)).
{ (* rem < 56: the padding and the length field fit one block *)
  assert (Hlt : r < 56).
  { revert H.
    rewrite !Int64.unsigned_repr; rep_lia. }
  rewrite (proj2 (Z.ltb_lt r 56) Hlt) in Hpz.
  (* tlen = 64; *)
  forward.
  (* ntail = 1; *)
  forward.
  Exists 64 1.
  entailer!. }
{ (* rem >= 56: they need a second block *)
  assert (Hge : 56 <= r).
  { revert H.
    rewrite !Int64.unsigned_repr; rep_lia. }
  rewrite (proj2 (Z.ltb_ge r 56) Hge) in Hpz.
  (* tlen = 128; *)
  forward.
  (* ntail = 2; *)
  forward.
  Exists 128 2.
  entailer!. }
Intros tl nt.
(* [Hnt] is never cited by name; it is what makes [64 * nt - 8] nonnegative
   in the [ltac:(lia)] side conditions of every cut below. *)
rename H0 into Hnt.
rename H1 into Hpad.
subst tl.
clear Hpz.

(* ===== Stage 6: SS 5.1.1's 64-bit length field =====
   The C stores the bit-length as [inlen >> 29] and [(uint32_t)inlen << 3].
   [Hhi] and [Hlo] read those two C expressions as the high and low halves
   of [8 * Zlength msg]; exactness of the high half is the whole point of
   [Zlength msg < 2^61] in the funspec, and it is spent in [Hd29]. This is
   64-bit reasoning, so the bounds are [Int64.max_unsigned]. *)
assert (E29 : (2:Z) ^ 29 = 536870912) by (vm_compute; reflexivity).
assert (E32 : (2:Z) ^ 32 = 4294967296) by (vm_compute; reflexivity).
assert (Hd29 : 0 <= Zlength msg / 536870912 < 4294967296).
{ split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia. }
assert (Hhi : Int.unsigned (Int.repr (Int64.unsigned
                (Int64.shru (Int64.repr (Zlength msg)) (Int64.repr 29))))
              = 8 * Zlength msg / 2 ^ 32).
{ unfold Int64.shru.
  rewrite (Int64.unsigned_repr (Zlength msg)); [rep_lia |].
  rewrite (Int64.unsigned_repr 29); [rep_lia |].
  rewrite Z.shiftr_div_pow2; [lia |].
  rewrite E29.
  rewrite (Int64.unsigned_repr (Zlength msg / 536870912)); [rep_lia |].
  rewrite (Int.unsigned_repr (Zlength msg / 536870912)); [rep_lia |].
  rewrite E32.
  assert (4294967296 = 8 * 536870912) as -> by lia.
  rewrite Z.div_mul_cancel_l; [lia | lia | reflexivity]. }
assert (Hlo : Int.unsigned (Int.shl (Int.repr (Zlength msg)) (Int.repr 3))
              = (8 * Zlength msg) mod 2 ^ 32).
{ unfold Int.shl.
  rewrite (Int.unsigned_repr 3); [rep_lia |].
  rewrite !Int.unsigned_repr_eq.
  rewrite Z.shiftl_mul_pow2; [lia |].
  assert ((2:Z) ^ 3 = 8) as -> by (vm_compute; reflexivity).
  change Int.modulus with 4294967296.
  rewrite E32.
  rewrite Z.mul_mod_idemp_l; [lia |].
  rewrite (Z.mul_comm (Zlength msg) 8).
  reflexivity. }
(* Cut the eight bytes of the length field out of [tail] for the two stores. *)
sep_apply (tail_cut Tsh v_tail
  ((List.map Vubyte (sublist (64 * q) (64 * q + r) msg) ++ [Vubyte (Byte.repr 128)]
    ++ Zrepeat (Vubyte Byte.zero) (127 - r))%list) (64 * nt - 8)
  ltac:(list_solve) ltac:(lia) ltac:(lia) Hfct).
Intros.
replace (64 * nt - 8 + 4) with (64 * nt - 4) by lia.
replace (64 * nt - 8 + 8) with (64 * nt) by lia.
rewrite tail_marked_map.
(* store_be32(tail + tlen - 8, (uint32_t)(inlen >> 29)); *)
forward_call (Tsh, offset_val (64 * nt - 8) v_tail,
              Int.repr (Int64.unsigned (Int64.shru (Int64.repr (Zlength msg))
                                                   (Int64.repr 29)))).
{ entailer!.
  rewrite sem_sub_pi_offset; [exact Hptr | reflexivity | rep_lia |].
  change (sizeof tuchar) with 1.
  rewrite Z.mul_1_l.
  reflexivity. }
(* store_be32(tail + tlen - 4, (uint32_t)inlen << 3); *)
forward_call (Tsh, offset_val (64 * nt - 4) v_tail,
              Int.shl (Int.repr (Zlength msg)) (Int.repr 3)).
{ entailer!.
  rewrite sem_sub_pi_offset; [exact Hptr | reflexivity | rep_lia |].
  change (sizeof tuchar) with 1.
  rewrite Z.mul_1_l.
  rewrite Int64.Z_mod_modulus_eq.
  rewrite (Z.mod_small (Zlength msg) Int64.modulus); [rep_lia |].
  reflexivity. }

(* Both stores have matched their C expressions, so the two halves can be
   named. Everything downstream needs only [Hhi] and [Hlo], and the raw
   terms are five constructors deep and appear seven more times below. *)
remember (Int.repr (Int64.unsigned (Int64.shru (Int64.repr (Zlength msg))
                                               (Int64.repr 29)))) as hi eqn:Hhidef.
remember (Int.shl (Int.repr (Zlength msg)) (Int.repr 3)) as lo eqn:Hlodef.
(* [remember] rewrites the hypotheses too, so [Hhi] and [Hlo] already speak
   of [hi] and [lo] and the defining equations are dead weight. *)
clear Hhidef Hlodef E29 E32 Hd29 Hptr.

(* ===== Stage 7: SS 6.2.2 on the padded tail =====
   The tail's first [tlen] bytes are one or two whole blocks again: the
   message remainder, the 0x80 byte, the zero run and the eight length
   bytes, glued back into a single [data_at] for the call. *)
assert (Hm0 : 0 <= 64 * nt - 9 - r)
  by (assert (Hpr := padzeros_range (Zlength msg)); lia).
assert (HCURB : Zlength (sublist (64 * q) (64 * q + r) msg ++ [Byte.repr 128]
                         ++ Zrepeat Byte.zero (127 - r))%list = 128) by list_solve.
sep_apply (tail_glue3 Tsh v_tail
  (sublist 0 (64 * nt - 8)
     (List.map Vubyte (sublist (64 * q) (64 * q + r) msg ++ [Byte.repr 128]
                       ++ Zrepeat Byte.zero (127 - r))%list))
  (List.map (fun z : Z => Vubyte (Byte.repr z)) (bytes_of_word U32 (w32_of_int hi)))
  (List.map (fun z : Z => Vubyte (Byte.repr z)) (bytes_of_word U32 (w32_of_int lo)))
  (64 * nt - 8) (64 * nt - 4) (64 * nt)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(list_solve)
  ltac:(rewrite Zlength_map; rewrite Zlength_bytes_of_word_U32; reflexivity)
  ltac:(rewrite Zlength_map; rewrite Zlength_bytes_of_word_U32; reflexivity)
  Hfct).
rewrite (tail_full_map msg (64 * q) r (64 * nt - 9 - r) (64 * nt - 8) hi lo
           ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).

assert (HB1 : Zlength (List.map Byte.repr (bytes_of_word U32 (w32_of_int hi))) = 4)
  by (rewrite Zlength_map; apply Zlength_bytes_of_word_U32).
assert (HB2 : Zlength (List.map Byte.repr (bytes_of_word U32 (w32_of_int lo))) = 4)
  by (rewrite Zlength_map; apply Zlength_bytes_of_word_U32).

(* sha256_compress_blocks(H, tail, ntail); *)
forward_call (Tsh, Tsh, Tsh, v_H, v_tail, v_sha256_K,
              compress_blocks clone.H0
                (List.map Byte.unsigned (sublist 0 (64 * q) msg)),
              (sublist (64 * q) (64 * q + r) msg ++ [Byte.repr 128]
               ++ Zrepeat Byte.zero (64 * nt - 9 - r)
               ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int hi))
               ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int lo)))%list,
              nt).
{ split.
  - apply compress_blocks_size.
    exact H0_size.
  - list_solve. }
(* THE HEART: the bytes the C compressed are exactly [pad msgZ]. *)
rewrite (sha256_split msg q r (64 * nt) hi lo
           ltac:(rewrite Htp; exact Hlen) Hq0 Hr Hqr Hpad Hhi Hlo).

(* The chaining value is opaque from here on: left as [compress_blocks _ (pad _)],
   the digest loop's array load reduces it through the sixty-four rounds and the
   term is exponential. *)
remember (compress_blocks clone.H0 (pad (List.map Byte.unsigned msg))) as Hs
  eqn:HHs.
assert (HsSize : size Hs = 8%nat)
  by (rewrite HHs; apply compress_blocks_size; exact H0_size).
assert (HDlen : Zlength (List.map (fun z : Z => Vubyte (Byte.repr z))
                                  (digest_bytes Hs)) = 32)
  by (rewrite Zlength_map; apply Zlength_digest_bytes; exact HsSize).
assert (Hdig : List.map (fun z : Z => Vubyte (Byte.repr z)) (digest_bytes Hs)
               = word_to_vals (clone.sha256 (List.map Byte.unsigned msg))).
{ unfold word_to_vals.
  unfold clone.sha256.
  unfold sha256_words.
  rewrite <- HHs.
  rewrite (bytes_of_digest Hs HsSize).
  reflexivity. }
clear HHs.
(* The tail has done its work; only the space is still owned. *)
sep_apply (data_at_data_at_ Tsh (tarray tuchar (64 * nt))
             (List.map Vubyte
                (sublist (64 * q) (64 * q + r) msg ++ [Byte.repr 128]
                 ++ Zrepeat Byte.zero (64 * nt - 9 - r)
                 ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int hi))
                 ++ List.map Byte.repr (bytes_of_word U32 (w32_of_int lo)))%list) v_tail).
sep_apply (data_at_data_at_ Tsh (tarray tuchar (128 - 64 * nt))
             (sublist (64 * nt) 128
                (List.map Vubyte (sublist (64 * q) (64 * q + r) msg ++ [Byte.repr 128]
                                  ++ Zrepeat Byte.zero (127 - r))%list))
             (offset_val (64 * nt) v_tail)).
(* Nothing below is about the padding or the length field any more. *)
clear Hhi Hlo HB1 HB2 HCURB Hm0 Htp.

(* ===== Stage 8: SS 6.2.2, the digest stored big-endian =====
   for (i = 0; i < 8; i++) store_be32(out + 4 * i, H[i]);
   [out] is owned whole, so each iteration cuts the four bytes at [4 * i]
   out for the call and glues them back; [digest_out_step] is the
   arithmetic that the written prefix grew by exactly those four.
   [D] names the finished digest as the C sees it, thirty-two [val]s: the
   loop body cuts and re-glues it four times per iteration and the raw
   term is three lines each time. [remember] rewrites [HDlen] and [Hdig]
   with it, which is all the loop and the exit need. *)
remember (List.map (fun z : Z => Vubyte (Byte.repr z)) (digest_bytes Hs)) as D
  eqn:HDdef.
forward_for_simple_bound 8
  (EX i : Z,
   PROP ()
   LOCAL (temp _ntail (Vlong (Int64.repr nt));
          temp _tlen (Vlong (Int64.repr (64 * nt))); temp _rem (Vlong (Int64.repr r));
          temp _nblocks (Vlong (Int64.repr q));
          lvar _tail (tarray tuchar 128) v_tail;
          lvar _sha256_K (tarray tuint 64) v_sha256_K;
          lvar _H (tarray tuint 8) v_H;
          temp _out out_ptr; temp _in in_ptr;
          temp _inlen (Vlong (Int64.repr (Zlength msg))))
   SEP (data_at Tsh (tarray tuint 8) (words_to_vals Hs) v_H;
        data_at_ Tsh (tarray tuchar (64 * nt)) v_tail;
        data_at_ Tsh (tarray tuchar (128 - 64 * nt)) (offset_val (64 * nt) v_tail);
        data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
        data_at sh_out (tarray tuchar 32)
          ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list) out_ptr;
        data_at Tsh (tarray tuint 64) (words_to_vals K) v_sha256_K)).
{ (* entry: no digest byte stored yet *)
  entailer!. }
{ (* one iteration *)
  rename H into Hi.
  (* t'1 = H[i]; *)
  forward.
  { rewrite (Znth_words_to_vals Hs i); [rewrite HsSize; lia |].
    entailer!. }
  rewrite (Znth_words_to_vals Hs i); [rewrite HsSize; lia |].
  (* Cut the four output bytes at offset 4*i out for the call. *)
  rewrite (tuchar_split3 sh_out out_ptr
             ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list) 32 4 (4 * i)
             ltac:(list_solve) ltac:(lia) ltac:(lia) ltac:(lia) Hfco).
  Intros.
  sep_apply (data_at_data_at_ sh_out (tarray tuchar 4)
               (sublist (4 * i) (4 * i + 4)
                  ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list))
               (offset_val (4 * i) out_ptr)).
  (* store_be32(out + 4 * i, H[i]); *)
  forward_call (sh_out, offset_val (4 * i) out_ptr,
                int_of_w32 (nth w32_0 Hs (Z.to_nat i))).
  rewrite int_of_w32K.
  sep_apply (out_glue sh_out out_ptr
               (sublist 0 (4 * i)
                  ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list))
               (List.map (fun z : Z => Vubyte (Byte.repr z))
                  (bytes_of_word U32 (nth w32_0 Hs (Z.to_nat i))))
               (sublist (4 * i + 4) 32
                  ((sublist 0 (4 * i) D ++ Zrepeat Vundef (32 - 4 * i))%list))
               (4 * i) (4 * i + 4)
               ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(list_solve)
               ltac:(rewrite Zlength_map; rewrite Zlength_bytes_of_word_U32; reflexivity)
               ltac:(list_solve) Hfco).
  rewrite (digest_out_step Hs D i HDdef HsSize Hi).
  entailer!. }

(* ===== Stage 9: exit =====
   All thirty-two digest bytes are written, and the two local arrays go
   back to the stack frame. *)
assert ((sublist 0 (4 * 8) D ++ Zrepeat Vundef (32 - 4 * 8))%list = D) as ->
  by list_solve.
rewrite Hdig.
sep_apply (tail_rejoin Tsh v_tail (64 * nt) ltac:(lia) Hfct).
sep_apply (data_at_data_at_ Tsh (tarray tuint 8) (words_to_vals Hs) v_H).
sep_apply (data_at_data_at_ Tsh (tarray tuint 64) (words_to_vals K) v_sha256_K).
entailer!.
Qed.
