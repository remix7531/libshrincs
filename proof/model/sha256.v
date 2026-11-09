(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.sha256: a sealed SHA-256 definition in the model byte types.

    The canonical FIPS definition is in [Model.sha256_spec]. The codec
    preserves its digest bytes and the sealed wrapper keeps length
    clipping out of unification. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Export address bounded.
(** [Import], not [Export]: the mathcomp-flavoured word/byte codec is
    used in the proofs below and in no consumer's statements. *)
From Model Require Import bytes.
(** The specification has its own name beside this model wrapper. *)
Require Import Model.sha256_spec.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

#[local] Open Scope Z_scope.

Definition block : Type := list byte.

Definition hash_bytes : Z := 32.

Definition sha256_max_input_len : Z := 2 ^ 61 - 1.

(* ================================================================= *)
(** ** Derived: the digest is eight words, hence thirty-two bytes.

    One chain: the compression function preserves the eight-word
    chaining value, so the fold over the padded message's blocks does
    too, and the big-endian rendering of eight words is thirty-two
    bytes. *)

Lemma size_list_of_state (st : state) : size (list_of_state st) = 8%nat.
Proof. by case: st => [[[[[[[a b] c] d] e] f] g] h]. Qed.

Lemma size_compress_words (Hs Ms : seq w32) :
  size Hs = 8%nat -> size (compress_words Hs Ms) = 8%nat.
Proof.
by move=> H8; rewrite /compress_words size_map size_zip size_list_of_state H8 minnn.
Qed.

Lemma size_compress_blocks (Hs : seq w32) (bs : seq Z) :
  size Hs = 8%nat -> size (compress_blocks Hs bs) = 8%nat.
Proof.
rewrite /compress_blocks.
move: (parse_blocks bs) => L.
elim: L Hs => [|M L IH] Hs //= H8.
by apply: IH; apply: size_compress_words.
Qed.

Lemma size_sha256_words (msg : seq Z) : size (sha256_words msg) = 8%nat.
Proof. by apply: size_compress_blocks. Qed.

Lemma digest_bytes_cons (w : w32) (Hs : seq w32) :
  digest_bytes (w :: Hs) = bytes_of_word U32 w ++ digest_bytes Hs.
Proof. reflexivity. Qed.

Lemma size_digest_bytes (Hs : seq w32) : size (digest_bytes Hs) = (4 * size Hs)%nat.
Proof.
elim: Hs => [|w Hs IH] //.
rewrite digest_bytes_cons size_cat bytes_of_word_size IH mulnS.
reflexivity.
Qed.

Lemma size_sha256_bytes (msg : seq Z) : size (sha256_bytes msg) = 32%nat.
Proof. by rewrite /sha256_bytes size_digest_bytes size_sha256_words. Qed.

(** mathcomp's [size] and Stdlib's [length] are the same fixpoint on
    the same type, so this is [exact:] and not a rewrite. *)
Lemma length_sha256_bytes (msg : seq Z) : length (sha256_bytes msg) = 32%nat.
Proof. exact: size_sha256_bytes. Qed.

(* ================================================================= *)
(** ** Derived: every digest byte really is a byte.

    The digest is the big-endian rendering of eight words, and
    [model.bytes]' renderer masks each byte it emits. *)

Lemma digest_bytes_range (Hs : seq w32) (b : Z) :
  b \in digest_bytes Hs -> 0 <= b < 256.
Proof.
elim: Hs => [|w Hs IH] //.
rewrite digest_bytes_cons mem_cat => /orP[Hin|Hin].
- (* one of the four bytes the leading word contributes *)
  by case/mapP: Hin => j _ ->; apply: byte_of_word_range.
- (* or one from the remaining words *)
  exact: IH.
Qed.

Lemma sha256_bytes_range (msg : seq Z) (b : Z) :
  b \in sha256_bytes msg -> 0 <= b < 256.
Proof. exact: digest_bytes_range. Qed.

(* ================================================================= *)
(** ** SHA-256, in the model's bytes. *)

(** The thirty-two digest bytes of [l], as [byte]s. *)
Definition sha256_out (l : list byte) : list byte :=
  List.map byte_mod256 (sha256_bytes (List.map byte_val l)).

Lemma length_sha256_out (l : list byte) :
  Z.of_nat (length (sha256_out l)) = hash_bytes.
Proof.
rewrite /sha256_out List.length_map length_sha256_bytes.
reflexivity.
Qed.

(** [byte_mod256] does not truncate here: pointwise on a list whose
    every element is already in range, it is the identity. *)
Lemma map_byte_val_mod256 (l : seq Z) :
  (forall b, b \in l -> 0 <= b < 256) ->
  List.map byte_val (List.map byte_mod256 l) = l.
Proof.
elim: l => [|z l IH] Hall; first by [].
(* [cbn [List.map]] and not [simpl]: the latter unfolds [byte_mod256]
   to its [machine.Byte.repr] body, and then there is nothing left for
   [byte_mod256_small] to rewrite. *)
cbn [List.map].
rewrite (byte_mod256_small z (Hall z (mem_head z l))) byte_val_of.
f_equal.
by apply: IH => b Hb; apply: Hall; rewrite in_cons Hb orbT.
Qed.

(** THE HONESTY STATEMENT for the codec above: [sha256_out]'s bytes
    carry exactly [Model.sha256_spec]'s digest values. *)
Lemma map_byte_val_sha256_out (l : list byte) :
  List.map byte_val (sha256_out l) = sha256_bytes (List.map byte_val l).
Proof.
rewrite /sha256_out.
by apply: map_byte_val_mod256 => b; apply: sha256_bytes_range.
Qed.

(** SEALED, and the seal is load-bearing. [model.wots]'s [sha256']
    applies [SHA256] to a [BList.clip sha256_max_input_len _], whose
    body contains [firstn (Z.to_nat (2 ^ 61 - 1))] -- a unary [nat]
    with 2^61 successors. As a [Parameter], [SHA256] blocked every
    reduction path into that argument by construction. [Opaque] does
    NOT reproduce that: it stops [simpl]/[cbn]/[reflexivity], but
    [apply]/[trivial]-style unification runs with full delta and
    can unfold an [Opaque] constant anyway.
    So the body is locked behind a [Qed] and the only way through it is
    [to_list_SHA256] below. *)
Definition SHA256_sealed :
  { f : BList.t byte sha256_max_input_len -> Vec.t byte hash_bytes
  | forall bl, Vec.to_list (f bl) = sha256_out (BList.to_list bl) }.
Proof.
  exists (fun bl => Vec.of (sha256_out (BList.to_list bl)) (length_sha256_out _)).
  intros bl. reflexivity.
Qed.

Definition SHA256 : BList.t byte sha256_max_input_len -> Vec.t byte hash_bytes :=
  proj1_sig SHA256_sealed.

(** The one step through [SHA256] any consumer needs. *)
Lemma to_list_SHA256 (bl : BList.t byte sha256_max_input_len) :
  Vec.to_list (SHA256 bl) = sha256_out (BList.to_list bl).
Proof. exact (proj2_sig SHA256_sealed bl). Qed.
