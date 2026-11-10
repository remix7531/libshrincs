(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.sha256.sync: the clone is the original

    A GATE, not a development. Shrincs.internal.vst.sha256.clone keeps a
    private copy of the SHA-256 specification so that Shrincs.sha256,
    a reviewer-facing file, can contain definitions, one faithfulness lemma and
    known-answer tests, and nothing else. This file is what makes that
    arrangement safe.

    Every lemma below says that one definition of Shrincs.sha256 and the
    correspondingly named definition of the clone are THE SAME TERM.
    Edit one spelling and not the other and the build stops here,
    naming the definition that drifted.

    THE CONSEQUENCE WORTH SPELLING OUT. Shrincs.sha256's known-answer
    tests transfer. They pin the canonical spelling; these lemmas pin
    the clone to it; so the vectors are evidence about both, and the
    VST proofs are about a function that has been tested against
    sha256sum.

    WHY THE PROOFS ARE NOT ALL BARE [reflexivity]. On a composite
    definition -- [schedule], [rounds], [sha256] -- bare [reflexivity]
    lets conversion choose what to unfold, and it will expand
    [iter 48 sched_step] or a sixty-four-element [foldl] before
    noticing that the two sides differ only in which module a leaf
    constant came from. The file then takes minutes or does not
    terminate at all. Each lemma below therefore unfolds exactly the
    two definitions it is about and rewrites with the sync lemmas of
    their COMPONENTS, after which the two sides are syntactically
    identical and [reflexivity] is immediate. The order of the
    sections is the dependency order of the specification.

    [Shrincs.internal.vst.sha256.correct] and [Shrincs.internal.vst.support.contract.trusted] use
    [sync_sha256] to restate the C contract over the canonical hash. *)

Require Shrincs.sha256.
From Shrincs.internal.vst.sha256 Require clone.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Module M := Shrincs.internal.vst.sha256.clone.
Module S := Shrincs.sha256.

(* ================================================================= *)
(** ** SS 3: word operations *)

Lemma sync_w32_0 : M.w32_0 = S.w32_0.
Proof. reflexivity. Qed.

Lemma sync_SHR : M.SHR = S.SHR.
Proof. reflexivity. Qed.

Lemma sync_ROTR : M.ROTR = S.ROTR.
Proof. unfold M.ROTR, S.ROTR. rewrite sync_SHR. reflexivity. Qed.

(* ================================================================= *)
(** ** SS 4: the six logical functions and the constants *)

Lemma sync_Ch : M.Ch = S.Ch.
Proof. reflexivity. Qed.

Lemma sync_Maj : M.Maj = S.Maj.
Proof. reflexivity. Qed.

Lemma sync_Sigma0 : M.Sigma0 = S.Sigma0.
Proof. unfold M.Sigma0, S.Sigma0. rewrite sync_ROTR. reflexivity. Qed.

Lemma sync_Sigma1 : M.Sigma1 = S.Sigma1.
Proof. unfold M.Sigma1, S.Sigma1. rewrite sync_ROTR. reflexivity. Qed.

Lemma sync_sigma0 : M.sigma0 = S.sigma0.
Proof. unfold M.sigma0, S.sigma0. rewrite sync_ROTR, sync_SHR. reflexivity. Qed.

Lemma sync_sigma1 : M.sigma1 = S.sigma1.
Proof. unfold M.sigma1, S.sigma1. rewrite sync_ROTR, sync_SHR. reflexivity. Qed.

Lemma sync_K_Z : M.K_Z = S.K_Z.
Proof. reflexivity. Qed.

Lemma sync_K : M.K = S.K.
Proof. unfold M.K, S.K. rewrite sync_K_Z. reflexivity. Qed.

(* ================================================================= *)
(** ** SS 5: preprocessing *)

Lemma sync_msglen : M.msglen = S.msglen.
Proof. reflexivity. Qed.

Lemma sync_padzeros : M.padzeros = S.padzeros.
Proof. reflexivity. Qed.

Lemma sync_len_bytes : M.len_bytes = S.len_bytes.
Proof. reflexivity. Qed.

Lemma sync_pad : M.pad = S.pad.
Proof.
unfold M.pad, S.pad. rewrite sync_msglen, sync_padzeros, sync_len_bytes. reflexivity.
Qed.

Lemma sync_parse_block : M.parse_block = S.parse_block.
Proof. reflexivity. Qed.

Lemma sync_nblocks : M.nblocks = S.nblocks.
Proof. reflexivity. Qed.

Lemma sync_parse_blocks : M.parse_blocks = S.parse_blocks.
Proof.
unfold M.parse_blocks, S.parse_blocks. rewrite sync_parse_block, sync_nblocks. reflexivity.
Qed.

Lemma sync_H0_Z : M.H0_Z = S.H0_Z.
Proof. reflexivity. Qed.

Lemma sync_H0 : M.H0 = S.H0.
Proof. unfold M.H0, S.H0. rewrite sync_H0_Z. reflexivity. Qed.

(* ================================================================= *)
(** ** SS 6: the hash computation *)

Lemma sync_sched_step : M.sched_step = S.sched_step.
Proof.
unfold M.sched_step, S.sched_step. rewrite sync_sigma0, sync_sigma1, sync_w32_0. reflexivity.
Qed.

Lemma sync_schedule : M.schedule = S.schedule.
Proof. unfold M.schedule, S.schedule. rewrite sync_sched_step. reflexivity. Qed.

Lemma sync_state : M.state = S.state.
Proof. reflexivity. Qed.

Lemma sync_round : M.round = S.round.
Proof.
unfold M.round, S.round. rewrite sync_Sigma0, sync_Sigma1, sync_Ch, sync_Maj. reflexivity.
Qed.

Lemma sync_state_of : M.state_of = S.state_of.
Proof. unfold M.state_of, S.state_of. rewrite sync_w32_0. reflexivity. Qed.

Lemma sync_list_of_state : M.list_of_state = S.list_of_state.
Proof. reflexivity. Qed.

Lemma sync_rounds : M.rounds = S.rounds.
Proof.
unfold M.rounds, S.rounds. rewrite sync_round, sync_state_of, sync_K, sync_schedule. reflexivity.
Qed.

(** The compression function, at both of the seams RustCrypto splits
    it: sixteen parsed words, and a run of byte blocks. *)

Lemma sync_compress_words : M.compress_words = S.compress_words.
Proof.
unfold M.compress_words, S.compress_words. rewrite sync_list_of_state, sync_rounds. reflexivity.
Qed.

Lemma sync_compress_blocks : M.compress_blocks = S.compress_blocks.
Proof.
unfold M.compress_blocks, S.compress_blocks. rewrite sync_compress_words, sync_parse_blocks.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The digest and the exported function *)

Lemma sync_digest_bytes : M.digest_bytes = S.digest_bytes.
Proof. reflexivity. Qed.

Lemma sync_digest_of : M.digest_of = S.digest_of.
Proof. unfold M.digest_of, S.digest_of. rewrite sync_digest_bytes. reflexivity. Qed.

Lemma sync_sha256_words : M.sha256_words = S.sha256_words.
Proof.
unfold M.sha256_words, S.sha256_words. rewrite sync_compress_blocks, sync_H0, sync_pad.
reflexivity.
Qed.

Lemma sync_sha256_bytes : M.sha256_bytes = S.sha256_bytes.
Proof.
unfold M.sha256_bytes, S.sha256_bytes. rewrite sync_digest_bytes, sync_sha256_words. reflexivity.
Qed.

Lemma sync_sha256 : M.sha256 = S.sha256.
Proof. unfold M.sha256, S.sha256. rewrite sync_digest_of, sync_sha256_words. reflexivity. Qed.
