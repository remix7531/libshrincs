(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.inputs

    The chain-start and message-randomizer inputs encode the specification PRFs at
    their full leaf coordinates. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  params model.wire bridge.model shape games instance scheme.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.
From Shrincs.internal.ssprove.wots Require Import hop.prf.

(* ------------------------------------------------------------------ *)
(** ** Message-PRF inputs *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

(** The stateless selector uses ordinary HMAC zero-padding of the 16-byte
    secret, with the same message-length guard as the specification. *)
Lemma shrincs_prf_msg_stateless_eq (k : bytes 16) (m : seq UInt8) :
  Z.leb (Z.of_nat (size m)) (Z.sub (Z.pow 2 61) 65) ->
  omap (fun digest : Bytes 32 => slice digest 0 16) (hmac_sha256 k m) =
    Some (kh_eval shrincs_khf_prf_msg k (false, m)).
Proof.
by move=> hdom; rewrite /hmac_sha256 size_tuple hdom.
Qed.

Definition shrincs_fxmss_prf_msg_input (pp : bytes 16) (a : shrincs_fxmss_coord)
    (m : shrincs_fxmss_bytes) : kh_M shrincs_khf_prf_msg :=
  (true, pp ++ (int_to_bytes a.1 1 ++ int_to_bytes a.2 8) ++ m).

Lemma shrincs_fxmss_prf_msg_input_size pp a m :
  size (shrincs_fxmss_prf_msg_input pp a m).2 = 25 + size m.
Proof. by rewrite /shrincs_fxmss_prf_msg_input !size_cat !size_tuple. Qed.

Lemma shrincs_fxmss_prf_msg_input_domain pp a m :
  Z.leb (Z.of_nat (size m)) (Z.sub (Z.pow 2 61) 111) ->
  Z.leb (Z.of_nat (size (shrincs_fxmss_prf_msg_input pp a m).2))
    (Z.sub (Z.pow 2 61) 65).
Proof.
move/Z.leb_le=> hm.
apply/Z.leb_le.
rewrite shrincs_fxmss_prf_msg_input_size Znat.Nat2Z.inj_add.
lia.
Qed.

Lemma shrincs_fxmss_prf_msg_eval_eq k pp a m :
  Z.leb (Z.of_nat (size m)) (Z.sub (Z.pow 2 61) 111) ->
  PRF_msg_sf k pp a.1 a.2 m =
    Some (kh_eval shrincs_khf_prf_msg k (shrincs_fxmss_prf_msg_input pp a m)).
Proof.
by move=> hm; rewrite /PRF_msg_sf /hmac_sha256
  -/((shrincs_fxmss_prf_msg_input pp a m).2) (shrincs_fxmss_prf_msg_input_domain pp a m
    hm)
    size_cat !size_tuple.
Qed.

Lemma shrincs_fxmss_prf_msg_height_encodeK (h : UInt8) :
  int_from_bytes U8 (int_to_bytes h 1) = h.
Proof.
change (wrepr U8 (0 * 256 + wunsigned (wrepr U8 (wunsigned h / 1)))%Z = h).
rewrite Z.div_1_r wrepr_unsigned.
change (wrepr U8 (wunsigned h) = h).
exact: wrepr_unsigned.
Qed.

Lemma shrincs_fxmss_prf_msg_index_encodeK (i : UInt64) :
  int_from_bytes U64 (int_to_bytes i 8) = i.
Proof.
apply: shrincs_fxmss_spec_int_from_to_bytes64; first lia.
exact: wunsigned_range.
Qed.

Lemma shrincs_fxmss_prf_msg_input_inj pp a m pp' a' m' :
  shrincs_fxmss_prf_msg_input pp a m = shrincs_fxmss_prf_msg_input pp' a' m' ->
  (pp, (a, m)) = (pp', (a', m')).
Proof.
case: a => h i.
case: a' => h' i'.
move/(congr1 snd).
rewrite /shrincs_fxmss_prf_msg_input -!catA => he.
have hpp := congr1 (fun s => slice s 0 16) he.
rewrite !slice_cat_head in hpp.
subst pp'.
have ht := jasmin_util.cat_inj_head he.
have hh := congr1 (fun s => slice s 0 1) ht.
rewrite !slice_cat_head in hh.
have hh' := congr1 (fun x : Bytes 1 => int_from_bytes U8 x) hh.
rewrite !shrincs_fxmss_prf_msg_height_encodeK in hh'.
change (h = h') in hh'.
subst h'.
have hi := jasmin_util.cat_inj_head ht.
have hi' := congr1 (fun s => slice s 0 8) hi.
rewrite !slice_cat_head in hi'.
have hii := congr1 (fun x : Bytes 8 => int_from_bytes U64 x) hi'.
rewrite !shrincs_fxmss_prf_msg_index_encodeK in hii.
change (i = i') in hii.
subst i'.
by rewrite (jasmin_util.cat_inj_head hi).
Qed.

Lemma shrincs_fxmss_prf_msg_bound_message_domain cm :
  shrincs_fxmss_message_valid cm ->
  Z.leb (Z.of_nat (size (shrincs_fxmss_bound_message cm)))
    (Z.sub (Z.pow 2 61) 111).
Proof.
rewrite /shrincs_fxmss_message_valid.
move/andP=> [/leP hc /Z.leb_le hm].
apply/Z.leb_le.
rewrite /shrincs_fxmss_bound_message !size_cat.
change (Z.of_nat (1 + (1 + (size cm.1 + size cm.2)))
  <= 2^61 - 111)%Z.
rewrite !Znat.Nat2Z.inj_add.
have hcZ : (Z.of_nat (@size UInt8 cm.1) <= 255)%Z.
{ exact: (proj1 (Znat.Nat2Z.inj_le _ _) hc). }
change (Z.of_nat (@size UInt8 cm.2) <= 2^61 - 368)%Z in hm.
change (1 + (1 + (Z.of_nat (@size UInt8 cm.1) +
  Z.of_nat (@size UInt8 cm.2))) <= 2^61 - 111)%Z.
lia.
Qed.

Lemma shrincs_fxmss_prf_msg_eval_bound_message k pp a cm :
  shrincs_fxmss_message_valid cm ->
  PRF_msg_sf k pp a.1 a.2 (shrincs_fxmss_bound_message cm) =
    Some (kh_eval shrincs_khf_prf_msg k
      (shrincs_fxmss_prf_msg_input pp a (shrincs_fxmss_bound_message cm))).
Proof.
move=> hm.
apply: shrincs_fxmss_prf_msg_eval_eq.
exact: shrincs_fxmss_prf_msg_bound_message_domain.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF inputs *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_prf_budget (Q : shrincs_fxmss_resources) : nat :=
  (shrincs_fxmss_leaf_capacity Q * wots_c_chain_count).+1.
Definition shrincs_fxmss_q_prf_msg (Q : shrincs_fxmss_resources) : nat :=
  (shrincs_fxmss_sign_budget Q).+1.

Definition shrincs_fxmss_prf_input (pp : bytes 16) (a : shrincs_fxmss_coord) b d j :
    kh_M shrincs_khf_prf := (pp, shrincs_fxmss_prf_tweak a b d j).
Definition shrincs_fxmss_prf_pin (pp : bytes 16) : kh_M shrincs_khf_prf :=
  (pp, shrincs_fxmss_grind_tweak (uint U8 0, uint U64 0)).
Definition shrincs_fxmss_prf_msg_pin : kh_M shrincs_khf_prf_msg := (true, [::]).

Lemma shrincs_fxmss_prf_input_inj pp pp' a a' b d j j' :
  j < wots_c_chain_count -> j' < wots_c_chain_count ->
  shrincs_fxmss_prf_input pp a b d j = shrincs_fxmss_prf_input pp' a' b d j' ->
  (pp, (a, j)) = (pp', (a', j')).
Proof.
move=> hj hj' he.
have hpp := congr1 fst he.
have ht := congr1 snd he.
have [ha hindex] := shrincs_fxmss_prf_tweak_inj a a' b d j j' hj hj' ht.
change (pp = pp') in hpp.
by rewrite hpp ha hindex.
Qed.

Lemma shrincs_fxmss_prf_pin_neq pp pp' a b d j :
  shrincs_fxmss_prf_input pp a b d j <> shrincs_fxmss_prf_pin pp'.
Proof.
move/(congr1 (fun x : kh_M shrincs_khf_prf => x.2.1.1.1.2)).
by [].
Qed.

Lemma shrincs_fxmss_prf_msg_pin_neq pp a m : shrincs_fxmss_prf_msg_input pp a m <>
  shrincs_fxmss_prf_msg_pin.
Proof.
move/(congr1 (fun x : kh_M shrincs_khf_prf_msg => size x.2)).
by rewrite shrincs_fxmss_prf_msg_input_size.
Qed.

Lemma shrincs_fxmss_prf_eval_eq k pp a b d j :
  kh_eval shrincs_khf_prf k (shrincs_fxmss_prf_input pp a b d j) =
  PRF pp k (WotsCPrf a.1 a.2 b d (uint U32 j)).
Proof. by []. Qed.

Lemma shrincs_fxmss_prf_leaf_keys_eq k pp a b d :
  shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k =
  [seq kh_eval shrincs_khf_prf k (shrincs_fxmss_prf_input pp a b d j) |
    j <- iota 0 wots_c_chain_count].
Proof. by []. Qed.

Lemma shrincs_fxmss_prf_query_budget Q b d :
  shrincs_fxmss_structure_legal b d ->
  (size (shrincs_fxmss_schedule (b, d)) * wots_c_chain_count).+1 <=
    shrincs_fxmss_prf_budget Q.
Proof.
move=> hlegal.
rewrite /shrincs_fxmss_prf_budget ltnS.
apply: leq_mul => //.
apply: leq_trans (shrincs_fxmss_leaf_count_bound b d hlegal).
rewrite /shrincs_fxmss_schedule size_pmap.
have hcount := count_size
  (fun q => isSome (shrincs_fxmss_select_leaf b d q))
  (iota 0 (shrincs_fxmss_leaf_count b d)).
by rewrite size_iota in hcount.
Qed.

Lemma shrincs_fxmss_prf_msg_query_budget Q calls sc :
  calls <= sc.+1 -> sc < shrincs_fxmss_sign_budget Q -> calls <
    shrincs_fxmss_q_prf_msg Q.
Proof.
move=> hcalls hsc.
apply: leq_ltn_trans hcalls _.
by rewrite /shrincs_fxmss_q_prf_msg ltnS.
Qed.
