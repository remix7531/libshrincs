(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.trusted: the SHA-256 contract, and its model-side view.

    NOTHING IN THIS FILE IS TRUSTED ANYMORE, and the name is kept only
    because every [Require] in the tree points at it. What used to live
    here was an axiomatic funspec for [src/sha256.c] plus, in
    [contract.gprog], an [Axiom body_sha256] asserting the C satisfies
    it. Both are gone:

    - [sha256_spec] IS the sha256 translation unit's own contract,
      [Shrincs.internal.vst.sha256.contract.spec_sha256] -- the one
      [Shrincs.internal.vst.sha256.vsu]'s verified component exports and
      [Shrincs.internal.vst.sha256.verif.sha256] proves the C body against.
      [sha256_spec_canonical] then says, by the kernel, that it is the
      SAME TERM as the reviewer-facing [Shrincs.sha256.spec_sha256]
      (the same statement [Shrincs.internal.vst.sha256.correct] makes about the
      component's Exports slot), so what [Gprog] promises about
      [shrincs_sha256] is FIPS 180-4 as transcribed in the file a
      reviewer reads.
    - [contract.gprog]'s [body_sha256] is now a [Lemma], proved from
      that body proof by context subsumption.

    THE MODEL-SIDE VIEW. The two callers of [shrincs_sha256]
    ([verif.body_shrincs_thash], [verif.body_shrincs_wots_h_grind])
    speak the model's vocabulary: a [block] in, [block_to_vals
    (sha256' _)] out. [sha256_block_spec] is exactly that contract, and
    [sha256_block_spec_sub] proves it is subsumed by [sha256_spec] --
    the codec change of variable, nothing else. Each call site then
    reads [forward_call sha256_block_spec_sub (...)], floyd's
    call-with-a-subsumed-spec form, and the bodies are otherwise
    unchanged.

    The in-tree libc alternatives ([shrincs_memcpy], [shrincs_memset],
    [shrincs_ct_memcmp], [shrincs_panic]) have their funspecs in
    [contract.helpers] and their bodies proved in [proof/internal/vst].

    When auditing: `make audit` checks that the model + vst trees
    declare no [Axiom]/[Parameter] at all (beyond [machine.v]'s
    Module-Type fields, discharged at instantiation) and that the
    [Print Assumptions] cone of every body proof is the classical
    CompCert/Coq-stdlib baseline and nothing else. *)

From VST Require Export floyd.proofauto.

(** [Import], not [Export], and BEFORE [contract.public]: each of these
    re-imports floyd, whose CompCert [Notation byte := Byte.int] would
    otherwise shadow the model's [byte] in [sha256_block_spec] below.
    None of them reaches the 17 body proofs downstream. *)
From Shrincs.internal.vst.support.repr Require Import int32.
From SSProve.Crypt Require Import jasmin_wsize.
From Shrincs.internal.vst.sha256 Require Import contract.
From Shrincs.internal.vst.sha256 Require sync.
Require Shrincs.sha256.

From Shrincs.internal.vst.support Require Export contract.public.
From Shrincs.clight Require Export sha256.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The contract [Gprog] carries. *)

(** [sha256(out, in, inlen)]: writes the 32-byte digest of [in] to
    [out]. Not restated here -- it IS the sha256 unit's exported
    contract, so there is exactly one funspec for [shrincs_sha256] in
    the repository and no second description of it to keep in sync. *)
Definition sha256_spec : ident * funspec := Shrincs.internal.vst.sha256.contract.spec_sha256.

(** ... and it is the reviewer-facing one, by [reflexivity] once the
    clone's hash name is rewritten to the canonical one. Same content
    as [Shrincs.internal.vst.sha256.correct]'s [sha256_ASI_canonical], restated
    here because THIS is the funspec [Gprog] hands to every caller. *)
Lemma sha256_spec_canonical : sha256_spec = Shrincs.sha256.spec_sha256.
Proof.
unfold sha256_spec, Shrincs.internal.vst.sha256.contract.spec_sha256,
       Shrincs.sha256.spec_sha256.
rewrite Shrincs.internal.vst.sha256.sync.sync_sha256.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The model's [block] as the contract's [list byte]. *)

(** [block_to_vals] with the [Vubyte] peeled off: the same 32-or-more
    bytes, as the [list byte] the contract above quantifies over. *)
Definition block_bytes (b : block) : list Byte.int :=
  List.map (fun x : byte => Byte.repr (byte_val x)) b.

Lemma map_Vubyte_block_bytes (b : block) :
  List.map Vubyte (block_bytes b) = block_to_vals b.
Proof. unfold block_bytes, block_to_vals. now rewrite List.map_map. Qed.

Lemma Zlength_block_bytes (b : block) : Zlength (block_bytes b) = Zlength b.
Proof. unfold block_bytes. apply Zlength_map. Qed.

(** [Byte.repr] does not truncate a model [byte]: it is already in range. *)
Lemma map_unsigned_block_bytes (b : block) :
  List.map Byte.unsigned (block_bytes b) = List.map byte_val b.
Proof.
unfold block_bytes.
rewrite List.map_map.
apply List.map_ext.
intros x.
apply Byte.unsigned_repr.
pose proof (byte_val_range x).
rep_lia.
Qed.

(** The digest word, back to its thirty-two bytes: [word_of_bytes] is
    injective on in-range byte lists of the right length, and
    [Shrincs.internal.common.sha256] proves the digest is one. *)
Lemma bytes_of_sha256 (msg : list Z) :
  bytes_of_word U256 (Shrincs.sha256.sha256 msg) = Shrincs.sha256.sha256_bytes msg.
Proof.
unfold Shrincs.sha256.sha256, Shrincs.sha256.digest_of.
apply bytes_of_word_of_bytes.
- rewrite size_sha256_bytes. reflexivity.
- exact (sha256_bytes_range msg).
Qed.

(** THE POSTCONDITION BRIDGE: the thirty-two bytes the SHA-256 contract
    promises at [out] are the model's [sha256'] of the same input.
    [BList.clip] is the only step with a side condition, and it is the
    one the model's header calls never-actually-truncating. *)
Lemma word_to_vals_sha256 (b : block) :
  Zlength b <= sha256_max_input_len ->
  word_to_vals (Shrincs.sha256.sha256 (List.map Byte.unsigned (block_bytes b)))
  = block_to_vals (sha256' b).
Proof.
intros Hb.
unfold word_to_vals, block_to_vals.
rewrite map_unsigned_block_bytes.
rewrite bytes_of_sha256.
rewrite (sha256'_eq b) by (rewrite Zlength_correct in Hb; exact Hb).
rewrite <- map_byte_val_sha256_out.
now rewrite List.map_map.
Qed.

(* ================================================================= *)
(** ** The same contract in the model's vocabulary. *)

(** [inlen]'s bound is [sha256_max_input_len] (not [Int64.max_unsigned],
    [tulong]'s own range) -- the real function's valid domain is
    SHA-256's own 2^61-byte limit, per [model.sha256].

    A separate [inlen] rather than [Zlength input] throughout: the C
    computes the length from its own locals, and a [forward_call] has
    to match that expression, not a [Zlength]. *)
Definition sha256_block_spec : ident * funspec :=
  DECLARE _shrincs_sha256
  WITH out_ptr : val, in_ptr : val, inlen : Z,
       input : list byte,
       sh_o : share, sh_i : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_i;
          Zlength input = inlen;
          0 <= inlen <= sha256_max_input_len)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr inlen))
    SEP (data_at_ sh_o (tarray tuchar 32) out_ptr;
         data_at  sh_i (tarray tuchar inlen) (block_to_vals input) in_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 32) (block_to_vals (sha256' input)) out_ptr;
         data_at sh_i (tarray tuchar inlen) (block_to_vals input) in_ptr).

Lemma sha256_block_spec_sub :
  funspec_sub (snd sha256_spec) (snd sha256_block_spec).
Proof.
do_funspec_sub.
destruct w as [[[[[out_ptr in_ptr] inlen] input] sh_o] sh_i].
clear H.
simpl.
Intros.
Exists (block_bytes input, out_ptr, in_ptr, sh_i, sh_o) emp.
rewrite map_Vubyte_block_bytes, Zlength_block_bytes.
entailer!.
split.
- (* the digest the SHA-256 contract writes at [out] IS the model's
     [sha256'] of the same bytes *)
  intros rho'.
  apply andp_left2.
  rewrite Shrincs.internal.vst.sha256.sync.sync_sha256.
  rewrite word_to_vals_sha256 by lia.
  cancel.
- (* SHA-256's own 2^61-byte domain sits inside the contract's bound *)
  assert (Htp : two_power_pos 61 = 2 ^ 61) by reflexivity.
  unfold sha256_max_input_len in H2.
  rewrite Htp.
  lia.
Qed.
