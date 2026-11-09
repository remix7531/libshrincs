(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.sha256: SHA-256, a defined function.

    [SHA256] is [Shrincs.sha256]'s [sha256_bytes] -- the FIPS 180-4
    transcription a reviewer reads, pinned by eleven known-answer tests
    against sha256sum(1) and python3 hashlib -- re-typed into the
    model's own byte vocabulary. The hash computation is defined here.
    Hash-game security remains an assumption of [Shrincs.internal.ssprove.axioms].

    THE TYPE IS UNCHANGED, so no consumer changed with it, and it still
    states the two properties every consumer needs intrinsically rather
    than as separate axioms: the output is exactly [hash_bytes = 32]
    bytes ([Vec.t]) -- now the proved [length_sha256_out] rather than a
    promise -- and the input is at most [sha256_max_input_len] bytes
    ([BList.t]) -- SHA-256's real limit, 2^64 - 1 *bits*, i.e.
    [(2^64 - 1) / 8 = 2^61 - 1] bytes (the message length is padded
    into a 64-bit field). [Z]'s binary representation makes this
    literal cheap to reason about with [lia]; a [nat] this large would
    not be (see [model.bounded]'s header comment).

    No hash call in this repo comes remotely close to that bound --
    [model.wots]'s [thash]/[H_grind] wrap the real [SHA256] behind a
    clip to [sha256_max_input_len] ([bounded.BList.clip]) so every
    caller can keep passing a plain [list byte] without threading a
    length invariant through the whole model; the clip only exists to
    satisfy [SHA256]'s type -- it never actually truncates anything a
    real WOTS+C call produces.

    WHAT THE DEFINITION COSTS: this file's Stdlib-only import list.
    Reaching [Shrincs.sha256] pulls in mathcomp and -- loaded, never
    imported -- floyd. That invariant is retired deliberately: an
    axiom-free hash is worth more than a short dependency list. Nothing
    below re-exports any of it, so the model's own vocabulary
    downstream ([model.wots] and on) is exactly what it was.

    THE BYTE CODEC. [Shrincs.sha256] speaks [seq Z]; the model speaks
    [byte]. [sha256_out] maps [byte_val] in and [byte_mod256] out.
    [byte_mod256] is total, so the definition needs no per-element
    range proof threaded through a dependent map -- and that the mod
    never actually truncates is then proved separately
    ([map_byte_val_sha256_out], from [sha256_bytes_range]), so the
    model's bytes ARE the standard's bytes and not their residues.

    THE DERIVED FACTS BELOW restate, over [Shrincs.sha256]'s canonical
    spelling, the handful of size and range facts the definition needs.
    [Shrincs.internal.vst.sha256.clone] proves the same facts over its own
    private copy of the specification, for its own consumers; the model
    does not reach into the VST tree for them.

    [SHA256] IS STILL IRREDUCIBLE, deliberately: its body is sealed
    behind a [Qed] at the bottom of this file and released only by
    [to_list_SHA256]. See the comment there -- reproducing the
    [Parameter]'s irreducibility is not optional, and [Opaque] does not
    do it.

    Generic, not scheme-specific -- reusable by any future SHRINCS
    scheme model that hashes with SHA-256, mirroring the
    src/sha256.c / src/wots.c split at the C-source level. *)

From Stdlib Require Import List ZArith Lia.
From Shrincs.internal.common Require Export address bounded.
(** [Import], not [Export]: the mathcomp-flavoured word/byte codec is
    used in the proofs below and in no consumer's statements. *)
From Shrincs.internal.common Require Import bytes.
(** The specification has its own name beside this model wrapper. *)
Require Import Shrincs.sha256.
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
    carry exactly [Shrincs.sha256]'s digest values. *)
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
