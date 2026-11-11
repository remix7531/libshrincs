(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.instance: the model at the functions of Shrincs.spec

    [wc_sha256] is the parameter record of the security proof with the carriers, hashes and tweaks of the specification, at one node of one tree. The lemmas after it show that the model's key generation, signing and verification at this record are [wots_c_pubkey_gen], [wots_c_sign] and [wots_c_pubkey_from_sig]. Shrincs.internal.ssprove.security concludes from them that the model's keyed scheme is the scheme of the public statement, so no second scheme definition stands between the two. *)

From Shrincs.internal.ssprove.lib Require Import prelude chain.core.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.wots Require Import scheme games hop.prf.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(*  Addresses as tweaks  *)

(* The six fields that Address.to_bytes hands to pack, per address class. *)
Definition tweak_of (ADRS : Address) : tweak :=
  match ADRS with
  | WotsCHash height index chain_index hash_index =>
      (height, index, SF_WOTS_C_HASH, uint U32 0, chain_index, hash_index)
  | WotsCPrf height index tree_balanced tree_depth chain_index =>
      (height, index, SF_WOTS_C_PRF,
       wrepr U32 (Z.add (Z.mul (Z.b2z tree_balanced) (Z.pow 2 24))
                        (Z.mul (wunsigned tree_depth) (Z.pow 2 16))),
       chain_index, uint U32 0)
  | WotsCPk height index =>
      (height, index, SF_WOTS_C_PK, uint U32 0, uint U32 0, uint U32 0)
  | WotsCGrind height index =>
      (height, index, SF_WOTS_C_GRIND, uint U32 0, uint U32 0, uint U32 0)
  end.

Lemma to_bytes_tweak_of (ADRS : Address) :
  to_bytes ADRS
  = (let: (height, index, address_type, word1, word2, word3) := tweak_of ADRS in
     Shrincs.spec.pack height index address_type word1 word2 word3).
Proof. by case: ADRS. Qed.

(* The specification hash calls use Th at the tweak of their address, with the grinding byte encoding proved below. *)
Lemma F_Th (pk_seed : Bytes 16) (ADRS : Address) (M_1 : Bytes 16) :
  F pk_seed ADRS M_1 = Th pk_seed (tweak_of ADRS) M_1.
Proof. by case: ADRS. Qed.

Lemma PRF_Th (pk_seed sk_seed : Bytes 16) (ADRS : Address) :
  PRF pk_seed sk_seed ADRS = Th pk_seed (tweak_of ADRS) sk_seed.
Proof. by case: ADRS. Qed.

Lemma T_sf_Th (pk_seed : Bytes 16) (ADRS : Address) (M_l : Bytes WOTS_C_CHAINS_SIZE) :
  T_sf pk_seed ADRS M_l = Th pk_seed (tweak_of ADRS) M_l.
Proof. by case: ADRS. Qed.

(* This literal packed form is used only to prove the byte encoding equation. *)
Definition Th_grind (pk_seed : Bytes 16) (t : tweak) (digest : Bytes 32) (counter : UInt16)
    : Bytes 16 :=
  let: (height, index, address_type, word1, word2, word3) := t in
  slice (sha256 (pk_seed ++ zeros 48 ++ slice (Shrincs.spec.pack height index address_type word1 word2 word3) 0 10
                 ++ digest ++ zeros 4 ++ int_to_bytes counter 2)) 0 16.

Lemma H_grind_Th_grind (pk_seed : Bytes 16) (ADRS : Address) (digest : Bytes 32)
    (counter : UInt16) :
  H_grind pk_seed ADRS digest counter = Th_grind pk_seed (tweak_of ADRS) digest counter.
Proof. by case: ADRS. Qed.

(* The address payload carries the first twelve digest bytes, so this Th input is exactly the grinding preimage of the specification. *)
Lemma grinding_encoding_Th (pk_seed : Bytes 16) (t : tweak)
    (digest : Bytes 32) (counter : UInt16) :
  Th_grind pk_seed t digest counter
  = Th pk_seed (grinding_tweak t digest) (grinding_message digest counter).
Proof.
case: t => [[[[[height index] address_type] word1] word2] word3].
rewrite /Th_grind /Th /grinding_tweak /grinding_message.
congr (slice (sha256 _) 0 16).
have hpack : tval (Shrincs.spec.pack height index address_type word1 word2 word3)
    = [tuple of int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1]
      ++ (int_to_bytes word1 4 ++ int_to_bytes word2 4 ++ int_to_bytes word3 4).
  by [].
have hprefix : slice (Shrincs.spec.pack height index address_type word1 word2 word3) 0 10
    = [tuple of int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1].
  by rewrite hpack slice_cat_head.
have hdigest :
    slice digest 0 4 ++ slice digest 4 4 ++ slice digest 8 4 ++ slice digest 12 20
    = tval digest.
  by rewrite -!slice_cat slice_all.
rewrite hprefix.
change ((pk_seed ++ zeros 48
         ++ (int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1)
         ++ digest ++ zeros 4 ++ int_to_bytes counter 2)
    = (pk_seed ++ zeros 48
         ++ (int_to_bytes height 1 ++ int_to_bytes index 8 ++ int_to_bytes address_type 1
             ++ int_to_bytes (int_from_bytes U32 (slice digest 0 4)) 4
             ++ int_to_bytes (int_from_bytes U32 (slice digest 4 4)) 4
             ++ int_to_bytes (int_from_bytes U32 (slice digest 8 4)) 4)
         ++ (slice digest 12 20 ++ zeros 4 ++ int_to_bytes counter 2))).
rewrite !int_to_from_bytes_4 -hdigest.
by rewrite !catA.
Qed.

Lemma H_grind_encoding_Th (pk_seed : Bytes 16) (ADRS : Address)
    (digest : Bytes 32) (counter : UInt16) :
  H_grind pk_seed ADRS digest counter
  = Th pk_seed (grinding_tweak (tweak_of ADRS) digest) (grinding_message digest counter).
Proof. by rewrite H_grind_Th_grind grinding_encoding_Th. Qed.

Lemma grinding_tweak_chain_class (t : tweak) (digest : Bytes 32) :
  wots_c_hash_class (grinding_tweak t digest) = wots_c_hash_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

Lemma grinding_tweak_pkcompress_class (t : tweak) (digest : Bytes 32) :
  wots_c_pk_class (grinding_tweak t digest) = wots_c_pk_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

Lemma grinding_tweak_grind_class (t : tweak) (digest : Bytes 32) :
  wots_c_grind_class (grinding_tweak t digest) = wots_c_grind_class t.
Proof. by case: t => [[[[[height index] address_type] word1] word2] word3]. Qed.

(*  Digits  *)

(* The digits of a grinding hash output, as wots_c_grind_to_constant_sum and wots_c_map_digest read them. *)
Definition spec_digits (g : bytes 16) : seq nat :=
  base_2b g WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT.

Lemma spec_digitsE (g : bytes 16) : spec_digits g = nibbles g.
Proof.
rewrite /spec_digits -[WOTS_C_CHAIN_COUNT]/(16.*2) -[X in X.*2](size_tuple g).
exact: base_2b_nibbles.
Qed.

Lemma size_spec_digits (g : bytes 16) : size (spec_digits g) = wots_c_chain_count.
Proof. by rewrite spec_digitsE size_nibbles size_tuple. Qed.

Lemma spec_digits_wf (g : bytes 16) : all (fun d => d < wots_c_w) (spec_digits g).
Proof. by rewrite spec_digitsE; exact: nibbles_lt. Qed.

Lemma spec_digits_inj : injective spec_digits.
Proof. by move=> g1 g2; rewrite !spec_digitsE => /nibbles_inj h; exact: val_inj. Qed.

Lemma wots_c_Hcc : 0 < wots_c_chain_count.
Proof. by []. Qed.

Lemma wots_c_Hw : 1 < wots_c_w.
Proof. by []. Qed.

Section AtTheAnchor.

Context (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8).

(*  The tweaks of one key  *)

Definition tw_chain (i pos : nat) : tweak :=
  tweak_of (WotsCHash node_height node_index (uint U32 i) (uint U32 pos)).

Definition tw_prf (i : nat) : tweak :=
  tweak_of (WotsCPrf node_height node_index tree_balanced tree_depth (uint U32 i)).

Definition tw_pk : tweak := tweak_of (WotsCPk node_height node_index).

Definition tw_grind : tweak := tweak_of (WotsCGrind node_height node_index).

Lemma tw_chain_class (i pos : nat) : wots_c_hash_class (tw_chain i pos).
Proof. by []. Qed.

Lemma tw_chain_not_pkcompress_class (i pos : nat) :
  ~~ wots_c_pk_class (tw_chain i pos).
Proof. by []. Qed.

Lemma tw_pk_class : wots_c_pk_class tw_pk.
Proof. by []. Qed.

Lemma tw_grind_class : wots_c_grind_class tw_grind.
Proof. by []. Qed.

Lemma tw_grind_not_chain_class : ~~ wots_c_hash_class tw_grind.
Proof. by []. Qed.

Lemma tw_grind_not_pkcompress_class : ~~ wots_c_pk_class tw_grind.
Proof. by []. Qed.

Lemma tw_grind_encoded_not_chain_class (digest : Bytes 32) :
  ~~ wots_c_hash_class (grinding_tweak tw_grind digest).
Proof. by rewrite grinding_tweak_chain_class tw_grind_not_chain_class. Qed.

Lemma tw_grind_encoded_class (digest : Bytes 32) :
  wots_c_grind_class (grinding_tweak tw_grind digest).
Proof. by rewrite grinding_tweak_grind_class tw_grind_class. Qed.

Lemma tw_grind_encoded_not_pkcompress_class (digest : Bytes 32) :
  ~~ wots_c_pk_class (grinding_tweak tw_grind digest).
Proof. by rewrite grinding_tweak_pkcompress_class tw_grind_not_pkcompress_class. Qed.

(* A chain index and a chain position fit a 32 bit word, so distinct ones give distinct tweaks. *)
Lemma chain_index_lt (i : nat) : i < wots_c_chain_count -> i < 2 ^ 32.
Proof. exact: (@ltn_2_32 i 5 isT). Qed.

Lemma chain_position_lt (pos : nat) : pos < wots_c_w.-1 -> pos < 2 ^ 32.
Proof. by move=> hp; apply: (@ltn_2_32 pos 4 isT); exact: (ltn_trans hp). Qed.

Lemma tw_chain_inj (i pos i' pos' : nat) :
  i < wots_c_chain_count -> i' < wots_c_chain_count ->
  pos < wots_c_w.-1 -> pos' < wots_c_w.-1 ->
  tw_chain i pos = tw_chain i' pos' -> i = i' /\ pos = pos'.
Proof.
move=> hi hi' hp hp' h.
have hc : uint U32 i = uint U32 i' := congr1 (fun t : tweak => t.1.2) h.
have hh : uint U32 pos = uint U32 pos' := congr1 (fun t : tweak => t.2) h.
split.
- exact: (@uint32_inj i i' (chain_index_lt i hi) (chain_index_lt i' hi') hc).
- exact: (@uint32_inj pos pos' (chain_position_lt pos hp) (chain_position_lt pos' hp') hh).
Qed.

Lemma tw_prf_inj (i i' : nat) :
  i < wots_c_chain_count -> i' < wots_c_chain_count -> tw_prf i = tw_prf i' -> i = i'.
Proof.
move=> hi hi' h.
have hc : uint U32 i = uint U32 i' := congr1 (fun t : tweak => t.1.2) h.
exact: (@uint32_inj i i' (chain_index_lt i hi) (chain_index_lt i' hi') hc).
Qed.

(*  The parameter record  *)

Definition wc_sha256 : wc_params := {|
  wcp_PP := bytes 16 ;
  wcp_N  := bytes 16 ;
  wcp_M  := bytes 32 ;
  wcp_Tw := tweak ;
  wcp_HM := 'list ('word U8) ;
  wcp_w := wots_c_w ;
  wcp_chain_count := wots_c_chain_count ;
  wcp_Hcc := wots_c_Hcc ;
  wcp_Hw  := wots_c_Hw ;
  wcp_tw_chain := tw_chain ;
  wcp_tw_prf   := tw_prf ;
  wcp_tw_pk    := tw_pk ;
  wcp_tw_grind := tw_grind ;
  wcp_tw_chain_inj := tw_chain_inj ;
  wcp_tw_prf_inj := tw_prf_inj ;
  wcp_Th := Th ;
  wcp_encode_node := fun x => tval x ;
  wcp_encode_node_inj := fun x y h => val_inj h ;
  wcp_encode_ends := fun xs => flatten [seq tval x | x <- xs] ;
  wcp_encode_ends_inj := @flatten_rows_inj 16 isT ;
  wcp_encode_grind := wots_c_grind_enc ;
  wcp_chain_class := wots_c_hash_class ;
  wcp_pk_class := wots_c_pk_class ;
  wcp_grind_class := wots_c_grind_class ;
  wcp_tw_chain_class := tw_chain_class ;
  wcp_tw_pk_class := tw_pk_class ;
  wcp_tw_grind_class := tw_grind_class ;
  wcp_tw_chain_not_pk := tw_chain_not_pkcompress_class ;
  wcp_encode_grind_class := fun m c => tw_grind_encoded_class m ;
  wcp_encode_grind_not_chain := fun m c => tw_grind_encoded_not_chain_class m ;
  wcp_encode_grind_not_pk := fun m c => tw_grind_encoded_not_pkcompress_class m ;
  wcp_digits := spec_digits ;
  wcp_digits_size := size_spec_digits ;
  wcp_digits_wf := spec_digits_wf ;
  wcp_digits_inj := spec_digits_inj ;
  wcp_G0 := zeros 16 ;
  wcp_Sig := bytes (2 + WOTS_C_CHAINS_SIZE) ;
  wcp_sig_encode := fun sg => sig_of sg.1 sg.2 ;
  wcp_sig_decode := fun sg => (sig_blocks sg, sig_ctr sg) ;
  wcp_dPP := dBytes 16 ;
  wcp_dN  := dBytes 16 ;
  wcp_constant_sum := WOTS_C_CONSTANT_SUM ;
  wcp_c_max        := wots_c_counter_max ;
|}.

Local Abbreviation P := wc_sha256.
Local Abbreviation model_chain :=
  (chainc (wcp_PP P) (wcp_N P) (wcp_w P) (chainf P)).

Lemma H_grind_model (pp : bytes 16) (ADRS : Address) (m : bytes 32) (c : nat) :
  H_grind pp ADRS m (uint U16 c) = wcp_H_grind P pp (tweak_of ADRS) (m, c).
Proof. by rewrite H_grind_encoding_Th. Qed.

(*  Chains  *)

(* The model's fold over a chain is the specification's loop. The bound keeps every position under the guard of the model's step. *)
Lemma chainc_chain_iter (pp : bytes 16) (i : nat) (x : bytes 16) (s n : nat) :
  s + n <= wots_c_w ->
  model_chain pp i x s n
  = wots_c_chain_iter x s (s + n) pp node_height node_index (uint U32 i).
Proof.
elim: n x s => [|n IH] x s hs.
- by rewrite /wots_c_chain_iter /range addn0 subnn.
- have hsw : s < wots_c_w.
    by apply: (leq_trans _ hs); rewrite addnS ltnS leq_addr.
  rewrite (chainc_shift (wcp_PP P) (wcp_N P) (wcp_w P) (chainf P) pp i x s n).
  rewrite (FcE (wcp_PP P) (wcp_N P) (wcp_w P) (chainf P) pp i s x hsw).
  have hs' : s.+1 + n <= wots_c_w by rewrite addSnnS.
  rewrite (IH _ _ hs') /wots_c_chain_iter /range.
  have -> : s.+1 + n - s.+1 = n by rewrite addKn.
  have -> : s + n.+1 - s = n.+1 by rewrite addKn.
  by [].
Qed.

(* A digit of a digest is at most w - 1. *)
Lemma digit_le (pp : bytes 16) (m : bytes 32) (c i : nat) :
  nth 0 (digest_of P pp m c) i <= (wcp_w P).-1.
Proof. by have := nth_digest_of_lt P pp m c i. Qed.

(*  Key generation  *)

Lemma pubkey_adapter (pp k : bytes 16) :
  wots_c_pubkey_gen k pp node_height node_index tree_balanced tree_depth
  = shrincs_wots_pubkey_gen P (bytes 16) shrincs_prf pp k.
Proof.
rewrite /shrincs_wots_pubkey_gen /shrincs_wots_pubkey /derive_sk chain_ends_mkseq.
rewrite /wots_c_pubkey_gen T_sf_Th /wcp_T_sf.
apply: (congr1 (fun xs : seq (bytes 16) => Th pp tw_pk (flatten [seq tval x | x <- xs]))).
apply/eq_in_map => i _.
have hd : 0 + (wcp_w P).-1 <= wots_c_w by rewrite add0n leq_pred.
by rewrite (chainc_chain_iter pp i _ 0 _ hd) ?add0n PRF_Th.
Qed.

(*  Signing  *)

(* The grinding loop of the specification is the model's search for the first good counter. *)
Lemma grind_adapter (pp : bytes 16) (m : bytes 32) :
  wots_c_grind_to_constant_sum pp m node_height node_index
  = omap (fun c => (uint U16 c, digest_of P pp m c)) (find_counter P pp m).
Proof.
rewrite /wots_c_grind_to_constant_sum /find_counter /range subn0 for_first_filter.
congr omap.
- apply: functional_extensionality => c.
  by rewrite H_grind_model.
- congr ohead; apply: eq_filter => c.
  by rewrite H_grind_model /good_counter -(grind_prpE P).
Qed.

Lemma sign_adapter (pp k : bytes 16) (m : bytes 32) :
  wots_c_sign m k pp node_height node_index tree_balanced tree_depth
  = omap (wcp_sig_encode P)
      (shrincs_wots_sign P pp (derive_sk P (bytes 16) shrincs_prf pp k) m).
Proof.
rewrite /wots_c_sign grind_adapter /shrincs_wots_sign.
case: (find_counter P pp m) => [c|]; last by [].
cbn [omap Option.map Option.bind Option.apply].
congr Some.
have -> : wcp_sig_encode P = fun sg => sig_of sg.1 sg.2 by [].
cbn [fst snd].
rewrite /derive_sk (sign_chains_mkseq P pp _ _ (size_digest_of P pp m c)).
rewrite -sig_of_tuple.
congr (sig_of _ c).
apply/eq_in_map => i _.
have hd : 0 + nth 0 (digest_of P pp m c) i <= wots_c_w.
  exact: (leq_trans (digit_le pp m c i) (leq_pred _)).
by rewrite (chainc_chain_iter pp i _ 0 _ hd) PRF_Th.
Qed.

(*  Verification  *)

(* The model's verifier on a decoded signature, with its chain completions written as the specification's loops. Stated apart from the specification's verifier: a rewrite in a goal that holds a tuple's size proof can land inside that proof. *)
Lemma model_verifyE (pp root : bytes 16) (m : bytes 32) (sg : bytes (2 + WOTS_C_CHAINS_SIZE)) :
  shrincs_wots_verify P pp root m (wcp_sig_decode P sg)
  = (sumn (digest_of P pp m (sig_ctr sg)) == WOTS_C_CONSTANT_SUM)
    && (Th pp tw_pk (flatten [seq tval x | x <-
          [seq wots_c_chain_iter (slice sg (2 + i * 16) 16)
                 (nth 0 (digest_of P pp m (sig_ctr sg)) i)
                 (2 ^ WOTS_C_CHAIN_BITS - 1) pp node_height node_index (uint U32 i)
          | i <- iota 0 WOTS_C_CHAIN_COUNT]]) == root).
Proof.
have -> : wcp_sig_decode P sg = (sig_blocks sg, sig_ctr sg) by [].
rewrite /shrincs_wots_verify; cbn [fst snd].
rewrite -(grind_prpE P) size_map size_iota eqxx andTb.
congr (_ && (_ == root)).
rewrite /sig_blocks (complete_ends_mkseq P pp _ _ (size_digest_of P pp m (sig_ctr sg))).
congr (Th pp tw_pk (flatten [seq tval x | x <- _])).
apply/eq_in_map => i _.
have hle := digit_le pp m (sig_ctr sg) i.
have hd : nth 0 (digest_of P pp m (sig_ctr sg)) i
          + ((wcp_w P).-1 - nth 0 (digest_of P pp m (sig_ctr sg)) i) <= wots_c_w.
  by rewrite (subnKC hle) leq_pred.
by rewrite (chainc_chain_iter pp i _ _ _ hd) (subnKC hle).
Qed.

Lemma verify_adapter (pp root : bytes 16) (m : bytes 32) (sg : bytes (2 + WOTS_C_CHAINS_SIZE)) :
  (wots_c_pubkey_from_sig sg m pp node_height node_index == Some root)
  = shrincs_wots_verify P pp root m (wcp_sig_decode P sg).
Proof.
have hds : base_2b (H_grind pp (WotsCGrind node_height node_index) m
                      (int_from_bytes U16 (slice sg 0 2)))
             WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT
           = digest_of P pp m (sig_ctr sg).
  by rewrite /digest_of /sig_ctr -[X in _ = wcp_digits P (wcp_H_grind P pp _ (m, X))]/(sig_ctr sg)
             -{1}(uint_to_nat (int_from_bytes U16 (slice sg 0 2))) H_grind_model.
rewrite model_verifyE /wots_c_pubkey_from_sig /wots_c_map_digest hds.
case: (sumn (digest_of P pp m (sig_ctr sg)) == WOTS_C_CONSTANT_SUM); last by [].
by rewrite T_sf_Th.
Qed.

End AtTheAnchor.
