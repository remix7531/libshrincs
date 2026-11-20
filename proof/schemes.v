(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.schemes: the experiments at the functions of Shrincs.spec

    The byte carriers and their samplers, the tweakable hash [Th] with its target classes, and the concrete WOTS+C scheme with its KOTS game. The experiments themselves are in Shrincs.games, which names no specification function. *)

From Shrincs Require Import games.
From mathcomp Require Import word_ssrZ word.
From mathcomp.experimental_reals Require Import distr.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.
From Shrincs Require Import spec.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* The games below instantiate the experiments at the functions and byte strings of Shrincs.spec. *)

Definition bytes (n : nat) : choice_type := chTuple (chWord U8) n.

(* Every seed, hash value and message digest the games sample consists of independent uniform bytes. *)
Definition dByte : dist ('word U8) :=
  {code x ← sample uniform 256 ;; ret (uint U8 x)}.

Fixpoint sample_bytes (n : nat) : raw_code (bytes n) :=
  match n with
  | 0 => ret (nil_tuple _)
  | n'.+1 => b ← dByte ;; bs ← sample_bytes n' ;; ret (cons_tuple b bs)
  end.

Lemma sample_bytes_valid (n : nat) : ValidCode emptym emptym (sample_bytes n).
Proof.
elim: n => [|n IH] /=.
- apply valid_ret.
- apply valid_sampler => a.
  eapply valid_bind; [exact: IH | move=> bs; apply valid_ret].
Qed.

Definition dBytes (n : nat) : dist (bytes n) :=
  {code sample_bytes n #with sample_bytes_valid n}.

(* A tweak carries the six fields that Address.pack serialises: height, index, address type and three words. *)
Definition tweak : choice_type :=
  'word U8 × 'word U64 × 'word U8 × 'word U32 × 'word U32 × 'word U32.

(* The address type fixes each target class before the public seed is sampled. *)
Definition wots_c_hash_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_HASH.

Definition wots_c_pk_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_PK.

Definition wots_c_grind_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_GRIND.

(* Grinding puts the first twelve digest bytes in the tweak payload and the remaining bytes in the message. The anchor and address type stay fixed. *)
Definition grinding_tweak (t : tweak) (digest : Bytes 32) : tweak :=
  let: (height, index, address_type, word1, word2, word3) := t in
  (height, index, address_type,
   int_from_bytes U32 (slice digest 0 4),
   int_from_bytes U32 (slice digest 4 4),
   int_from_bytes U32 (slice digest 8 4)).

Definition grinding_message (digest : Bytes 32) (counter : UInt16) : seq UInt8 :=
  slice digest 12 20 ++ zeros 4 ++ int_to_bytes counter 2.

(* F, PRF and T_sf use this hash at their address fields. Grinding uses the encoded tweak and message. Every result has sixteen bytes. *)
Definition Th (pk_seed : Bytes 16) (t : tweak) (M : seq UInt8) : Bytes 16 :=
  let: (height, index, address_type, word1, word2, word3) := t in
  slice (sha256 (pk_seed ++ zeros 48 ++ pack height index address_type word1 word2 word3 ++ M)) 0 16.

(* The PRF key is the secret seed. Its input contains the public seed and the tweak. *)
Definition shrincs_prf (pk_seed : bytes 16) (t : tweak) (sk_seed : bytes 16) : bytes 16 :=
  Th pk_seed t sk_seed.

Definition wots_c_w : nat := 2 ^ WOTS_C_CHAIN_BITS.
Definition wots_c_chain_count : nat := WOTS_C_CHAIN_COUNT.
Definition wots_c_counter_max : nat := 2 ^ 16.

Lemma dByte_lossless : LosslessCode dByte.
Proof.
  rewrite /dByte.
  apply Lossless_sample.
  - exact: LosslessOp_uniform.
  - move=> x; apply Lossless_ret.
Qed.

Lemma dBytes_lossless n : LosslessCode (dBytes n).
Proof.
  rewrite /dBytes /=.
  elim: n => [|n ih].
  - apply Lossless_ret.
  - rewrite /= /dByte /=.
    apply Lossless_sample.
    + exact: LosslessOp_uniform.
    + move=> x.
      rewrite /LosslessCode (Pr_fst_bind (sample_bytes_valid n)).
      under eq_dlet do rewrite Pr_fst_ret.
      rewrite -pr_predT pr_dlet.
      under eq_exp do rewrite pr_dunit /=.
      by rewrite exp_cst pr_predT ih GRing.mulr1.
Qed.

Lemma dBytes_map_lossless n (A : choice_type)
    (f : bytes n -> A) :
  LosslessCode (x ← dBytes n ;; ret (f x)).
Proof.
  rewrite /LosslessCode (Pr_fst_bind (prog_valid (dBytes n))).
  under eq_dlet do rewrite Pr_fst_ret.
  rewrite -pr_predT pr_dlet.
  under eq_exp do rewrite pr_dunit /=.
  by rewrite exp_cst pr_predT (dBytes_lossless n) GRing.mulr1.
Qed.

(* The chain games sample hidden sixteen-byte inputs and encode them as byte sequences. Compression and grinding choose their target messages. *)
Definition shrincs_thf : thf := {|
  th_PP := bytes 16; th_T := tweak; th_M := 'list ('word U8); th_N := bytes 16;
  th_eval := Th;
  th_dPP := dBytes 16;
  th_dM := {code x ← dBytes 16 ;; ret (tval x)};
  th_dN := dBytes 16 |}.

Definition shrincs_khf_prf : khf := {|
  kh_K := bytes 16; kh_M := bytes 16 × tweak; kh_N := bytes 16;
  kh_eval := fun k pt => shrincs_prf pt.1 pt.2 k;
  kh_dK := dBytes 16; kh_dN := dBytes 16 |}.

Definition wots_c_grind_enc (t : tweak) (m : bytes 32) (c : nat)
    : tweak * seq UInt8 :=
  (grinding_tweak t m, grinding_message m (uint U16 c)).

(* This is the digit-sum test used by grinding and recovery in the specification. *)
Definition wots_c_grind_prp (g : bytes 16) : bool :=
  sumn (base_2b g WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) == WOTS_C_CONSTANT_SUM.

Section AtTheAnchor.

(* The node height and index locate the WOTS+C key. Its anchor and tree shape are fixed within the experiment and universally quantified in the theorem. *)
Context (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8).

(* The three operations are the specification entry points. Both keys carry the public seed, and signing leaves the secret key unchanged. *)
Definition wots_c_scheme : sig_scheme := {|
  Pk := bytes 16 × bytes 16;
  Sk := bytes 16 × bytes 16;
  Msg := bytes 32;
  Sig := bytes (2 + WOTS_C_CHAINS_SIZE);
  SParam := 'unit;
  keygen := fun _ => {code
    pk_seed ← dBytes 16 ;;
    sk_seed ← dBytes 16 ;;
    ret ((pk_seed, sk_seed),
         (pk_seed, wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth))};
  sign := fun sk message_digest => {code
    ret (omap (fun signature => (signature, sk))
           (wots_c_sign message_digest sk.2 sk.1 node_height node_index tree_balanced tree_depth))};
  verify := fun pk message_digest signature =>
    wots_c_pubkey_from_sig signature message_digest pk.1 node_height node_index == Some pk.2
|}.

Definition wots_c_kots_game := KOTS_vc_game wots_c_scheme.

End AtTheAnchor.

(* FXMSS grinding consumes a target even when the bounded search fails. *)
Definition fxmss_grind_game (p : nat) :=
  stcrp_option.STCRP_option_game shrincs_thf wots_c_grind_class
    (bytes 32) wots_c_grind_enc wots_c_grind_prp wots_c_counter_max p.

(* Tree and compression targets share paired address coordinates. *)
Definition fxmss_tree_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_FXMSS_TREE.

Definition fxmss_paired_class (t : tweak) : bool :=
  wots_c_pk_class t || fxmss_tree_class t.

Definition fxmss_partner (t : tweak) : tweak :=
  let: (h, i, tag, a, b, c) := t in
  if tag == SF_WOTS_C_PK then (h, i, SF_FXMSS_TREE, a, b, c)
  else if tag == SF_FXMSS_TREE then (h, i, SF_WOTS_C_PK, a, b, c)
  else t.

Definition fxmss_tcrx_game (p : nat) :=
  tcrx.TCRX_game shrincs_thf fxmss_paired_class fxmss_partner p.

(* Tree collision resistance is an instance of the existing SM-TCR game. *)
Definition fxmss_tree_game (p : nat) :=
  smtcr.SMTCR_game shrincs_thf fxmss_tree_class p.

(* Stateful-only EU-CMA instance. Setup commits only the shape and partner;
   messages remain adaptive pairs (ctx, M). No stateless fallback is used. *)
Definition fxmss_sf_setup : choice_type := ('bool × 'nat) × bytes 16.
Definition fxmss_sf_message : choice_type := 'list ('word U8) × 'list ('word U8).
Definition fxmss_sf_signature : choice_type := 'list ('word U8).
Definition fxmss_sf_secret : choice_type := bytes 82 × 'option ('word U64).

(* The full logical Hmsg key includes both leaf coordinates and the bound
   payload. Natural coordinates retain invalid external requests explicitly. *)
Definition fxmss_sf_hash_input : choice_type :=
  bytes 16 × ((bytes 16 × bytes 16) × (('nat × 'nat) × 'list ('word U8))).

Definition fxmss_sf_setup_valid (sp : fxmss_sf_setup) : bool :=
  (1 <= sp.1.2) && (sp.1.2 <= if sp.1.1 then 64 else 255).

Definition fxmss_sf_message_valid (cm : fxmss_sf_message) : bool :=
  shrincs_sf_message_domain cm.2 cm.1.

Definition fxmss_sf_hash_valid (x : fxmss_sf_hash_input) : bool :=
  (x.2.2.1.1 < 256) && Z.ltb (Z.of_nat x.2.2.1.2) (Z.pow 2 64) &&
  Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111).

Definition fxmss_sf_keygen (sp : fxmss_sf_setup) :
    dist (fxmss_sf_secret × bytes 48).
Proof.
  notypeclasses refine {code
    sk_seed ← dBytes 16 ;;
    sk_prf ← dBytes 16 ;;
    pk_seed ← dBytes 16 ;;
    let seed := [tuple of sk_seed ++ sk_prf ++ pk_seed] in
    let structure := [tuple (if sp.1.1 then FXMSS_SHAPE_BALANCED
                            else FXMSS_SHAPE_UNBALANCED); uint U8 sp.1.2] in
    match shrincs_sf_keygen seed structure sp.2 with
    | Some (sk, pk) => ret ((sk, Some (uint U64 0)), pk)
    | None => @fail (fxmss_sf_secret × bytes 48)
    end }.
  ssprove_valid.
  exact: valid_fail.
Defined.

(* ------------------------------------------------------------------ *)
(** ** Stateful signing and random-oracle adapters *)

(* Select and consume before signing.
   Exhaustion is None, including the successor of the last UInt64 counter. *)
Definition shrincs_sf_consume (sf_structure : Bytes 2) (state_ctr : option UInt64)
    : option UInt64 * option (UInt64 * UInt8) :=
  if shrincs_sf_leaf_select sf_structure state_ctr is Some leaf then
    if state_ctr is Some state_ctr then
      let successor := Z.add (wunsigned state_ctr) 1 in
      let next :=
        if Z.ltb successor (Z.pow 2 64) then
          let next := Some (wrepr U64 successor) in
          if shrincs_sf_leaf_select sf_structure next is Some _ then next else None
        else None in
      (next, Some leaf)
    else (None, None)
  else (None, None).

(* The successor survives signing failure;
   inputs outside the message domain do not consume a leaf. *)
Definition shrincs_sf_sign_transition (message ctx : seq UInt8) (shrincs_seckey : Bytes 82)
    (state_ctr : option UInt64) : option UInt64 * option (seq UInt8) :=
  if shrincs_sf_message_domain message ctx then
    let: (successor, leaf) := shrincs_sf_consume (slice shrincs_seckey 64 2) state_ctr in
    (successor, if leaf is Some _ then shrincs_sf_sign message ctx shrincs_seckey state_ctr
                else None)
  else (state_ctr, None).

(* Use the supplied message digest after
   deriving the same randomizer and selecting the same leaf as the signer. *)
Definition shrincs_sf_sign_with_digest (message ctx : seq UInt8) (shrincs_seckey : Bytes 82)
    (state_ctr : option UInt64) (message_digest : Bytes 32) : option (seq UInt8) :=
  if shrincs_sf_message_domain message ctx then
    let sk_seed := slice shrincs_seckey 0 16 in
    let sk_prf := slice shrincs_seckey 16 16 in
    let pk_seed := slice shrincs_seckey 32 16 in
    let sl_root := slice shrincs_seckey 48 16 in
    let sf_structure := slice shrincs_seckey 64 2 in
    if shrincs_sf_leaf_select sf_structure state_ctr is Some (leaf_index, leaf_height) then
      let bound_message := shrincs_sf_bound_message message ctx sl_root in
      if PRF_msg_sf sk_prf pk_seed leaf_height leaf_index bound_message is Some R then
        let tree_balanced := nth (uint U8 0) sf_structure 0 == FXMSS_SHAPE_BALANCED in
        if fxmss_sign message_digest sk_seed leaf_index leaf_height pk_seed tree_balanced
             (nth (uint U8 0) sf_structure 1) is Some fxmss_signature then
          shrincs_sf_encode leaf_height R leaf_index fxmss_signature
        else None
      else None
    else None
  else None.

(* Digest-based recovery retains every wire check. *)
Definition shrincs_sf_recover_with_digest (signature : seq UInt8) (message_digest : Bytes 32)
    (pk_seed : Bytes 16) : option (Bytes 16) :=
  if shrincs_sf_parse signature is Some (leaf_height, R, leaf_index, fxmss_signature) then
    fxmss_pubkey_from_sig leaf_index leaf_height fxmss_signature message_digest pk_seed
  else None.

(* Replace H_msg_sf with the supplied digest after checking the message domain. *)
Definition shrincs_sf_verify_with_digest (message signature ctx : seq UInt8)
    (shrincs_pubkey : Bytes 48) (message_digest : Bytes 32) : bool :=
  if shrincs_sf_message_domain message ctx then
    if shrincs_sf_recover_with_digest signature message_digest (slice shrincs_pubkey 0 16)
      is Some root then root == slice shrincs_pubkey 32 16 else false
  else false.

Definition fxmss_sf_sign_next (sk : fxmss_sf_secret) (_ : fxmss_sf_message) :
    fxmss_sf_secret :=
  (sk.1, (shrincs_sf_consume (slice sk.1 64 2) sk.2).1).

Definition fxmss_sf_sign_query (sk : fxmss_sf_secret) (cm : fxmss_sf_message) :
    option fxmss_sf_hash_input :=
  if shrincs_sf_leaf_select (slice sk.1 64 2) sk.2 is Some (i, h) then
    let payload := shrincs_sf_bound_message cm.2 cm.1 (slice sk.1 48 16) in
    if PRF_msg_sf (slice sk.1 16 16) (slice sk.1 32 16) h i payload is Some R then
      Some (R, ((slice sk.1 32 16, slice sk.1 66 16),
        ((Z.to_nat (wunsigned h), Z.to_nat (wunsigned i)), payload)))
    else None
  else None.

Definition fxmss_sf_verify_query (pk : bytes 48) (cm : fxmss_sf_message)
    (signature : seq UInt8) : option fxmss_sf_hash_input :=
  if shrincs_sf_parse signature is Some (h, R, i, _) then
    Some (R, ((slice pk 0 16, slice pk 32 16),
      ((Z.to_nat (wunsigned h), Z.to_nat (wunsigned i)),
        shrincs_sf_bound_message cm.2 cm.1 (slice pk 16 16))))
  else None.

(* The concrete SHA recipe remains in spec.v. This experiment instead draws
   a uniform 32-byte digest at each fresh logical key in its shared table. *)
Definition fxmss_sf_scheme : stateful_rom.stateful_rom_scheme := {|
  stateful_rom.sf_Sk := fxmss_sf_secret;
  stateful_rom.sf_Pk := bytes 48;
  stateful_rom.sf_Setup := fxmss_sf_setup;
  stateful_rom.sf_Msg := fxmss_sf_message;
  stateful_rom.sf_Sig := fxmss_sf_signature;
  stateful_rom.sf_Hin := fxmss_sf_hash_input;
  stateful_rom.sf_Hout := bytes 32;
  stateful_rom.sf_setup_valid := fxmss_sf_setup_valid;
  stateful_rom.sf_message_valid := fxmss_sf_message_valid;
  stateful_rom.sf_hash_valid := fxmss_sf_hash_valid;
  stateful_rom.sf_keygen := fxmss_sf_keygen;
  stateful_rom.sf_digest := dBytes 32;
  stateful_rom.sf_sign_next := fxmss_sf_sign_next;
  stateful_rom.sf_sign_query := fxmss_sf_sign_query;
  stateful_rom.sf_sign_finish := fun sk cm md =>
    shrincs_sf_sign_with_digest cm.2 cm.1 sk.1 sk.2 md;
  stateful_rom.sf_verify_query := fxmss_sf_verify_query;
  stateful_rom.sf_verify_finish := fun pk cm sig md =>
    shrincs_sf_verify_with_digest cm.2 sig cm.1 pk md
|}.

Definition fxmss_eucma_game (q_s q_h : nat) :=
  stateful_rom.EUCMA_game fxmss_sf_scheme q_s q_h.

Definition fxmss_forger (LA : Locations)
    (c : raw_code (fxmss_sf_message × fxmss_sf_signature))
    (vc : ValidCode LA (stateful_rom.I_EUCMA_prefix fxmss_sf_scheme) c) :=
  stateful_rom.canonical_forger fxmss_sf_scheme LA c vc.

(* Both randomizer paths share sk_prf, so their PRF replacement must use
   one keyed function: a reduction for either path cannot evaluate the other
   without that secret. The selector chooses the HMAC key padding: true uses
   sk_prf || ff^48 for stateful data pk_seed || height || index || bound_message;
   false uses sk_prf || 00^48 for stateless data opt_rand || message.
   Both branches use the specification's HMAC computation. The stateless
   PRF_msg_sl is not otherwise transcribed here. The specification's length
   guard is discharged for every honest query by the internal adapter. *)
Definition shrincs_khf_prf_msg : khf := {|
  kh_K := bytes 16; kh_M := 'bool × 'list ('word U8); kh_N := bytes 16;
  kh_eval := fun k m =>
    let key := if m.1 then k ++ replicate (uint U8 255) 48 else k in
    slice (hmac_sha256_total key m.2) 0 16;
  kh_dK := dBytes 16; kh_dN := dBytes 16 |}.

Definition shrincs_prf_msg_game (q : nat) :=
  prf.PRF_game shrincs_khf_prf_msg q.
