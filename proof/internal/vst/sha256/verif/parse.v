(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_parse: proof of body_sha256_parse

    SS 5.2.1: sixteen big-endian words read out of one 512-bit block.

    One [forward_for_simple_bound 16] over a [forward_call
    spec_load_be32]. The invariant is the straightforward prefix one:
    after t iterations the first t entries of M are the first t words
    of [parse_block], and the remaining 16 - t are still undefined. M
    is a plain sixteen-word array written in index order, so a prefix
    is all the invariant has to say. That is precisely what the
    sibling sha256_compress_words does NOT get: its schedule is the
    sliding window W[t % 16], whose array holds the sixteen most
    recent schedule words rather than a prefix, and its invariant has
    to carry that window relation instead.

    The only real work per iteration is handing [load_be32] the four
    bytes at offset [4*t]: Vst.base's [tuchar_split3_bytes] at
    width 4 out of 64 is that split, and the same equation run
    backwards puts the 64-byte block together again for the next
    iteration. The model side is [nth_map]/[nth_iota] through
    [parse_block], which is [Znth_words_to_vals_parse_block].

    SCOPE TRAP, and the reason every list below carries an explicit
    [%list]. With mathcomp's seq_scope on top of the stack, a bare
    [++] is mathcomp's [cat], not [List.app] -- the two are different
    constants -- and floyd's [list_solve] only knows [app]. The
    symptom is a "list_solve cannot solve this goal" on a goal that is
    manifestly true, with no hint that the culprit is a notation.

    IMPORT DISCIPLINE, and why this file keeps the wide mathcomp
    surface where its sibling verif/logical.v narrows it. The
    statements below are typed in mathcomp's seq vocabulary -- [seq
    Z], [[::]], [take] and [drop] -- and the narrow [ssralg
    word.word] import supplies none of it; [seq] and [[::]] are
    notations, so they cannot even be qualified. The wide surface
    therefore stays, and with it ssreflect's [rewrite], which has no
    [by] clause: side conditions below are discharged by an explicit
    bullet or a trailing [; [| lia | lia]]; the stdlib form
    [rewrite L by lia] does not parse in this file. *)
From Vst.repr Require Import words.
From Vst.sha256 Require Import bridge.
From Vst.sha256 Require Import contract.
From Vst Require Import settings.
From Vst.sha256 Require Import clone.
From Vst.clight Require Import sha256.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

(* ================================================================= *)
(** ** SS 5.2.1 indexed: the t-th word of a parsed block

    [Znth] over a [seq w32] needs a default element; any word will do,
    since every index the proof takes is in range. *)

#[local] Instance Inhabitant_w32 : Inhabitant w32 := word_of_bytes U32 [::].

Lemma parse_block_Zlength (bs : seq Z) : Zlength (parse_block bs) = 16.
Proof.
rewrite Zlength_correct.
rewrite <- size_length.
rewrite parse_block_size.
reflexivity.
Qed.

Lemma Znth_parse_block (bs : seq Z) (t : Z) :
  0 <= t < 16 ->
  Znth t (parse_block bs) = word_of_bytes U32 (take 4%nat (drop (4 * Z.to_nat t)%nat bs)).
Proof.
intros Ht.
unfold Znth.
destruct (Z_lt_dec t 0) as [Hneg|_].
- (* t < 0 is ruled out by the range hypothesis *)
  exfalso.
  lia.
- rewrite <- nth_seq_list.
  unfold parse_block.
  rewrite (nth_map 0%nat).
  + (* side condition of nth_map: t indexes the iota *)
    rewrite size_iota.
    apply (introT ltP).
    lia.
  + (* the t-th entry of [iota 0 16] is t itself *)
    rewrite nth_iota.
    * apply (introT ltP).
      lia.
    * rewrite add0n.
      reflexivity.
Qed.

(** The same fact in the shape the loop meets it: the value
    [load_be32] returns for the four bytes at offset [4*t] is exactly
    the t-th entry of the array [spec_sha256_parse] promises. *)
Lemma Znth_words_to_vals_parse_block (blk : list byte) (t : Z) :
  0 <= t < 16 ->
  Znth t (words_to_vals (parse_block (List.map Byte.unsigned blk)))
  = Vint (int_of_w32 (word_of_bytes U32
      (List.map Byte.unsigned (sublist (4 * t) (4 * t + 4) blk)))).
Proof.
intros Ht.
unfold words_to_vals.
rewrite Znth_map.
- (* side condition of Znth_map: t indexes the parsed block *)
  rewrite parse_block_Zlength.
  exact Ht.
- (* the t-th parsed word IS load_be32's four bytes at offset 4*t *)
  rewrite (Znth_parse_block _ t Ht).
  rewrite <- sublist_map.
  rewrite (sublist_word4 t); [lia |].
  reflexivity.
Qed.

(** One iteration of the invariant: storing the t-th word into the
    first still-undefined slot extends the parsed prefix by one. *)
Lemma parse_step (blk : list byte) (t : Z) :
  0 <= t < 16 ->
  upd_Znth t
    ((sublist 0 t (words_to_vals (parse_block (List.map Byte.unsigned blk)))
      ++ Zrepeat Vundef (16 - t))%list)
    (Vint (int_of_w32 (word_of_bytes U32
       (List.map Byte.unsigned (sublist (4 * t) (4 * t + 4) blk)))))
  = (sublist 0 (t + 1) (words_to_vals (parse_block (List.map Byte.unsigned blk)))
     ++ Zrepeat Vundef (16 - (t + 1)))%list.
Proof.
intros Ht.
assert (HL : Zlength (words_to_vals (parse_block (List.map Byte.unsigned blk))) = 16).
{ rewrite words_to_vals_Zlength.
  rewrite parse_block_size.
  reflexivity. }
rewrite <- (Znth_words_to_vals_parse_block blk t Ht).
list_solve.
Qed.

(* ================================================================= *)
(** ** The body proof *)

Lemma body_sha256_parse : semax_body Vprog_sha Gprog_sha f_sha256_parse spec_sha256_parse.
Proof.
start_function.
rename H into Hblk.
(* The window cut needs the block to be a well-formed 64-byte array. *)
assert_PROP (field_compatible (tarray tuchar 64) [] bp) as Hfc by entailer!.
(* for (t = 0; t < 16; t++): M holds the first t words of the block. *)
forward_for_simple_bound 16
  (EX t : Z,
   PROP ()
   LOCAL (temp _M mp; temp _block bp)
   SEP (data_at shm (tarray tuint 16)
          ((sublist 0 t (words_to_vals (parse_block (List.map Byte.unsigned blk)))
            ++ Zrepeat Vundef (16 - t))%list) mp;
        data_at shb (tarray tuchar 64) (List.map Vubyte blk) bp)).
- (* entry: nothing parsed yet, all sixteen slots undefined *)
  entailer!.
- (* one iteration *)
  rename H into Hi.
  (* Cut the four bytes at offset 4*i out of the block for the call. *)
  rewrite (tuchar_split3_bytes shb bp blk 64 4 (4 * i));
    [exact Hblk | lia | lia | lia | exact Hfc |].
  (* t'1 = load_be32(block + 4 * t); *)
  forward_call (shb, offset_val (4 * i) bp, sublist (4 * i) (4 * i + 4) blk).
  { cancel. }
  { list_solve. }
  (* M[t] = t'1; *)
  forward.
  (* The parsed prefix grows by one and the block goes back together. *)
  rewrite (parse_step blk i Hi).
  rewrite (tuchar_split3_bytes shb bp blk 64 4 (4 * i));
    [exact Hblk | lia | lia | lia | exact Hfc |].
  entailer!.
- (* exit: t = 16, so M holds all sixteen words *)
  entailer!.
Qed.
