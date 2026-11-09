(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_compress_blocks: proof of body_sha256_compress_blocks

    The compression function over a run of consecutive 64-byte blocks
    -- RustCrypto sha2's [compress(state, blocks)]. Internal to the
    translation unit, but it carries the block loop for the whole
    file: shrincs_sha256() calls it twice and has none of its own.

    ONE [forward_for_simple_bound n] whose body is
    [forward_call spec_sha256_parse] then
    [forward_call spec_sha256_compress_words]. The invariant is the
    fold prefix, which is what [compress_blocks] being a [foldl] over
    [parse_blocks] is for: after i iterations the state array holds

      foldl compress_words Hs (take i (parse_blocks bsZ))

    and the two lemmas that make the loop go are [compress_blocks_step]
    (one more block extends the prefix by one [compress_words]) and
    [compress_blocks_take_all] (at i = n the prefix is everything).

    The one piece of real work per iteration is handing
    [sha256_parse] the 64 bytes at offset [64*i] of the caller's
    array: Vst.base's [tuchar_split3_bytes] there and back. That
    is the only place in the file where the input's block structure is
    taken apart, which is the point of having this function at all.

    THE C SPELLS THE OFFSET [blocks + i * 64], so Clight evaluates the
    argument to [offset_val (i * 64) bp] and not [offset_val (64 * i)
    bp]. Every pointer below is therefore written [Z.mul i 64] while
    every length is [Z.mul 64 _]; with the two spellings swapped the
    [forward_call] does not match and [entailer!] stops on a bare
    commutativity of [Z.mul] with nothing pointing at the cause. *)

From Vst.repr Require Import words.
From Vst.sha256 Require Import bridge.
From Vst.sha256 Require Import tables.
From Vst.sha256 Require Import contract.
From Vst Require Import settings.
From Vst.sha256 Require Import clone.
From Vst.clight Require Import sha256.

(* IMPORT DISCIPLINE. The wide mathcomp surface stays. The lemmas below
   are stated in the model's own vocabulary -- [seq], [size], [take],
   [drop], [nth], [foldl], [iota] -- and those names are only unqualified
   under it. Narrowing the import would leave [nth] resolving to
   [List.nth], whose argument order is the reverse, so every statement
   here would have to change. The proofs are ordinary Rocq tactics; the
   two places where a mathcomp-only step is unavoidable ([muln] and the
   boolean [<] of [ssrnat], neither of which [lia] can see through) are
   commented where they occur. *)
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

(* ================================================================= *)
(** ** SS 5.2.1 indexed: the i-th block of the message

    [parse_blocks] indexes the message with mathcomp's [take] and
    [drop]; a [data_at] over the same bytes is cut with VST's
    [sublist]. Vst.base's seq/list bridges are that dictionary;
    this is the one instance of it the file needs. *)

(** The i-th block of the message, as the two sides name it: VST's
    [sublist] of the byte list on the left, the model's
    [take 64 (drop (64*i) _)] of the [Z] list on the right. *)
Lemma map_unsigned_block (bs : list byte) (i : Z) :
  0 <= i ->
  List.map Byte.unsigned (sublist (Z.mul i 64) (Z.mul i 64 + 64) bs)
  = take 64 (drop (64 * Z.to_nat i) (List.map Byte.unsigned bs)).
Proof.
intros Hi.
rewrite <- sublist_map.
rewrite (sublist_take_drop (Z.mul i 64) 64); [lia | lia |].
(* The window width and offset, as [take] and [drop] index them. *)
assert (Hwidth : Z.to_nat 64 = 64%nat) by reflexivity.
assert (Hoffset : Z.to_nat (Z.mul i 64) = (64 * Z.to_nat i)%nat).
{ (* [multE] restates ssrnat's [muln] as Stdlib's [Nat.mul], which is
     the only form [lia] recognises. *)
  rewrite <- multE.
  lia. }
rewrite Hwidth.
rewrite Hoffset.
reflexivity.
Qed.

(* ================================================================= *)
(** ** SS 6.2.2 over a run of blocks: the fold, one block at a time

    [compress_blocks H bs] is [foldl compress_words H (parse_blocks
    bs)]. A loop that advances the state one block at a time proves
    that fold by its two structural facts: the prefix of length i+1 is
    the prefix of length i with one more [compress_words] applied, and
    at i = n the prefix is the whole list. *)

Lemma nblocks_sizeE (bsZ : seq Z) (n : Z) :
  0 <= n -> Z.of_nat (size bsZ) = Z.mul 64 n -> nblocks bsZ = Z.to_nat n.
Proof.
intros Hn Hsz.
assert (Hs : size bsZ = (64 * Z.to_nat n)%nat).
{ (* [multE] restates ssrnat's [muln] as Stdlib's [Nat.mul]. *)
  rewrite <- multE.
  apply Nat2Z.inj.
  rewrite Hsz.
  lia. }
unfold nblocks.
rewrite Hs.
(* [mulKn] cancels the division, leaving only its 0 < 64 side condition. *)
now rewrite mulKn.
Qed.

Lemma foldl_take_S {R T : Type} (f : R -> seq T -> R) (z : R) (s : seq (seq T)) (m : nat) :
  (m < size s)%nat ->
  foldl f z (take m.+1 s) = f (foldl f z (take m s)) (nth [::] s m).
Proof.
intros Hm.
rewrite (take_nth [::] Hm).
rewrite foldl_rcons.
reflexivity.
Qed.

Lemma nth_parse_blocks (bsZ : seq Z) (m : nat) :
  (m < nblocks bsZ)%nat ->
  nth [::] (parse_blocks bsZ) m = parse_block (take 64 (drop (64 * m) bsZ)).
Proof.
intros Hm.
unfold parse_blocks.
rewrite (nth_map 0%nat).
- (* the index is in range for the map *)
  rewrite size_iota.
  exact Hm.
- (* the m-th index of [iota 0 (nblocks bsZ)] is m itself *)
  rewrite nth_iota.
  + exact Hm.
  + reflexivity.
Qed.

(** One iteration: compressing block i into the fold over the first i
    blocks gives the fold over the first i+1. *)
Lemma compress_blocks_step (Hst : seq w32) (bsZ : seq Z) (n i : Z) :
  0 <= i < n -> Z.of_nat (size bsZ) = Z.mul 64 n ->
  foldl compress_words Hst (take (Z.to_nat (i + 1)) (parse_blocks bsZ))
  = compress_words (foldl compress_words Hst (take (Z.to_nat i) (parse_blocks bsZ)))
                   (parse_block (take 64 (drop (64 * Z.to_nat i) bsZ))).
Proof.
intros Hi Hsz.
assert (Hnb : nblocks bsZ = Z.to_nat n).
{ apply nblocks_sizeE.
  - lia.
  - exact Hsz. }
(* Block i is in range, so [take] of i+1 blocks really does add one. *)
assert (Hlt : (Z.to_nat i < size (parse_blocks bsZ))%nat).
{ rewrite parse_blocks_size.
  rewrite Hnb.
  (* [ltP] reflects the boolean [<] of ssrnat into the [<] [lia] knows. *)
  apply (introT ltP).
  lia. }
assert (Hnth : nth [::] (parse_blocks bsZ) (Z.to_nat i)
               = parse_block (take 64 (drop (64 * Z.to_nat i) bsZ))).
{ apply nth_parse_blocks.
  rewrite Hnb.
  apply (introT ltP).
  lia. }
assert (He : Z.to_nat (i + 1) = (Z.to_nat i).+1) by lia.
rewrite He.
rewrite (foldl_take_S compress_words Hst (parse_blocks bsZ) (Z.to_nat i) Hlt).
rewrite Hnth.
reflexivity.
Qed.

(** Loop exit: n blocks is all of them, so the prefix is [compress_blocks]. *)
Lemma compress_blocks_take_all (Hst : seq w32) (bsZ : seq Z) (n : Z) :
  0 <= n -> Z.of_nat (size bsZ) = Z.mul 64 n ->
  foldl compress_words Hst (take (Z.to_nat n) (parse_blocks bsZ)) = compress_blocks Hst bsZ.
Proof.
intros Hn Hsz.
assert (He : take (Z.to_nat n) (parse_blocks bsZ) = parse_blocks bsZ).
{ apply take_oversize.
  rewrite parse_blocks_size.
  rewrite (nblocks_sizeE bsZ n Hn Hsz).
  apply leqnn. }
rewrite He.
unfold compress_blocks.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The body proof *)

Lemma body_sha256_compress_blocks :
  semax_body Vprog_sha Gprog_sha f_sha256_compress_blocks spec_sha256_compress_blocks.
Proof.
start_function.
rename H into HHs.
rename H0 into Hbs.
rename H1 into Hn.
(* The message length as the model states it: a [size], not a [Zlength]. *)
assert (Hbsz : Z.of_nat (size (List.map Byte.unsigned bs)) = Z.mul 64 n).
{ rewrite size_map_list.
  rewrite <- Zlength_size.
  exact Hbs. }
(* The window cut needs the input to be a well-formed 64*n-byte array. *)
assert_PROP (field_compatible (tarray tuchar (Z.mul 64 n)) [] bp) as Hfc by entailer!.
(* for (i = 0; i < nblocks; i++): state holds the fold over blocks 0..i. *)
forward_for_simple_bound n
  (EX i : Z,
   PROP ()
   LOCAL (lvar _M (tarray tuint 16) v_M; temp _state sp; temp _blocks bp;
          temp _nblocks (Vlong (Int64.repr n)); temp _sha256_K kp)
   SEP (data_at_ Tsh (tarray tuint 16) v_M;
        data_at shs (tarray tuint 8)
          (words_to_vals (foldl compress_words Hs
             (take (Z.to_nat i) (parse_blocks (List.map Byte.unsigned bs))))) sp;
        data_at shb (tarray tuchar (Z.mul 64 n)) (List.map Vubyte bs) bp;
        data_at shk (tarray tuint 64) (words_to_vals K) kp)).
- (* entry: no block compressed yet, so the state is still Hs *)
  rewrite Z2Nat.inj_0.
  rewrite take0.
  entailer!.
- (* one iteration *)
  rename H into Hi.
  (* Cut the 64 bytes of block i out of the caller's array for the call. *)
  rewrite (tuchar_split3_bytes shb bp bs (Z.mul 64 n) 64 (Z.mul i 64));
    [exact Hbs | lia | lia | lia | exact Hfc |].
  (* sha256_parse(M, blocks + i * 64); *)
  forward_call (Tsh, shb, v_M, offset_val (Z.mul i 64) bp,
                sublist (Z.mul i 64) (Z.mul i 64 + 64) bs).
  { cancel. }
  { list_solve. }
  (* sha256_compress_words(state, M, sha256_K); *)
  forward_call (shs, Tsh, shk, sp, v_M, kp,
                foldl compress_words Hs
                  (take (Z.to_nat i) (parse_blocks (List.map Byte.unsigned bs))),
                parse_block (List.map Byte.unsigned
                  (sublist (Z.mul i 64) (Z.mul i 64 + 64) bs))).
  { apply foldl_compress_words_size.
    exact HHs. }
  (* The fold prefix grows by one block and the array goes back together. *)
  rewrite (map_unsigned_block bs i); [lia |].
  rewrite <- (compress_blocks_step Hs (List.map Byte.unsigned bs) n i Hi Hbsz).
  rewrite (tuchar_split3_bytes shb bp bs (Z.mul 64 n) 64 (Z.mul i 64));
    [exact Hbs | lia | lia | lia | exact Hfc |].
  entailer!.
- (* exit: i = n, so the fold has consumed every block *)
  rewrite (compress_blocks_take_all Hs (List.map Byte.unsigned bs) n).
  + lia.
  + exact Hbsz.
  + entailer!.
Qed.
