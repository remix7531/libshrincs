(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.model.wire

    Fixed-width big-endian fields and the stateful wire envelope. *)

From mathcomp Require Import boot algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Bool Lia ZArith.
From Shrincs Require Import spec.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import model.nodes.

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

Local Ltac shrincs_fxmss_spec_codec_arithmetic x hx bound :=
  let z := fresh "decoded" in
  cbn [foldl];
  rewrite !wunsigned_repr;
  change (modulus (wsize_size_minus_1 U8).+1) with 256%Z;
  move: (wunsigned x) hx => z hx;
  rewrite !Z.mod_eq; try lia;
  rewrite !Z.div_div; try lia;
  rewrite Z.div_1_r (Z.div_small z bound hx);
  try change (1 * 256)%Z with 256%Z;
  try change (256 * 256)%Z with 65536%Z;
  try change (65536 * 256)%Z with 16777216%Z;
  try change (16777216 * 256)%Z with 4294967296%Z;
  try change (4294967296 * 256)%Z with 1099511627776%Z;
  try change (1099511627776 * 256)%Z with 281474976710656%Z;
  try change (281474976710656 * 256)%Z with 72057594037927936%Z;
  ring.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_1 (x : UInt64) :
  (0 <= wunsigned x < 256)%Z ->
  int_from_bytes U64 (int_to_bytes x 1) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 256%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_2 (x : UInt64) :
  (0 <= wunsigned x < 65536)%Z ->
  int_from_bytes U64 (int_to_bytes x 2) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 65536%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_3 (x : UInt64) :
  (0 <= wunsigned x < 16777216)%Z ->
  int_from_bytes U64 (int_to_bytes x 3) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 65536);
    wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 16777216%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_4 (x : UInt64) :
  (0 <= wunsigned x < 4294967296)%Z ->
  int_from_bytes U64 (int_to_bytes x 4) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 16777216);
    wrepr U8 (wunsigned x / 65536);
    wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 4294967296%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_5 (x : UInt64) :
  (0 <= wunsigned x < 1099511627776)%Z ->
  int_from_bytes U64 (int_to_bytes x 5) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 4294967296);
    wrepr U8 (wunsigned x / 16777216);
    wrepr U8 (wunsigned x / 65536);
    wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 1099511627776%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_6 (x : UInt64) :
  (0 <= wunsigned x < 281474976710656)%Z ->
  int_from_bytes U64 (int_to_bytes x 6) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 1099511627776);
    wrepr U8 (wunsigned x / 4294967296);
    wrepr U8 (wunsigned x / 16777216);
    wrepr U8 (wunsigned x / 65536);
    wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 281474976710656%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_7 (x : UInt64) :
  (0 <= wunsigned x < 72057594037927936)%Z ->
  int_from_bytes U64 (int_to_bytes x 7) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 281474976710656);
    wrepr U8 (wunsigned x / 1099511627776);
    wrepr U8 (wunsigned x / 4294967296);
    wrepr U8 (wunsigned x / 16777216);
    wrepr U8 (wunsigned x / 65536);
    wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 72057594037927936%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64_8 (x : UInt64) :
  (0 <= wunsigned x < 18446744073709551616)%Z ->
  int_from_bytes U64 (int_to_bytes x 8) = x.
Proof.
move=> hx.
rewrite -[RHS]wrepr_unsigned /int_from_bytes.
congr wrepr.
change (foldl (fun acc b => (acc * 256 + wunsigned b)%Z) 0%Z
  [:: wrepr U8 (wunsigned x / 72057594037927936);
    wrepr U8 (wunsigned x / 281474976710656);
    wrepr U8 (wunsigned x / 1099511627776);
    wrepr U8 (wunsigned x / 4294967296);
    wrepr U8 (wunsigned x / 16777216);
    wrepr U8 (wunsigned x / 65536);
    wrepr U8 (wunsigned x / 256);
    wrepr U8 (wunsigned x / 1)] = wunsigned x).
shrincs_fxmss_spec_codec_arithmetic x hx 18446744073709551616%Z.
Qed.

Lemma shrincs_fxmss_spec_int_from_to_bytes64 (width : nat) (x : UInt64) :
  Nat.le width 8 -> (0 <= wunsigned x < 256 ^ Z.of_nat width)%Z ->
  int_from_bytes U64 (int_to_bytes x width) = x.
Proof.
move=> hw hx.
do 9 (destruct width as [|width];
  [first [
    exact: shrincs_fxmss_spec_int_from_to_bytes64_1 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_2 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_3 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_4 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_5 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_6 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_7 hx
  | exact: shrincs_fxmss_spec_int_from_to_bytes64_8 hx
  | apply: wunsigned_inj; change (0 = wunsigned x)%Z; change (0 <= wunsigned x < 1)%Z in hx; lia]
  | ]).
lia.
Qed.

Lemma shrincs_fxmss_spec_index_size_bounds z :
  (z < 255)%coq_nat ->
  let width := shrincs_sf_index_size (uint U8 z) in
  (0 < width) /\ (width <= 8) /\ (minn 64 (255-z) <= 8 * width).
Proof.
move=> hz.
have hz256 : (z < 256)%coq_nat by lia.
rewrite /shrincs_sf_index_size shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT minnC
  /ceildiv.
set bits := minn 64 (255-z).
have hlo : 0 < bits.
  rewrite /bits leq_min.
  apply/andP; split; first by [].
  apply/ltP.
  rewrite subnE.
  lia.
have hhi : bits <= 64 by exact: geq_minl.
have he : bits + 8 - 1 = bits + 7 by rewrite !addnE subnE; lia.
rewrite he.
have hdiv := divn_eq (bits+7) 8.
have hmod : (bits+7) %% 8 < 8 by rewrite ltn_mod.
move/ltP: hlo => hlo.
move/leP: hhi => hhi.
move/ltP: hmod => hmod.
rewrite !addnE !mulnE in hdiv.
rewrite addnE in hmod.
repeat split; apply/leP; rewrite ?addnE ?mulnE; lia.
Qed.

Lemma shrincs_fxmss_spec_index_fits z (i : UInt64) :
  (z < 255)%coq_nat ->
  (wunsigned i < 2 ^ Z.of_nat (minn 64 (255-z)))%Z ->
  (0 <= wunsigned i < 256 ^ Z.of_nat (shrincs_sf_index_size (uint U8 z)))%Z.
Proof.
move=> hz hi.
have [_ [_ /leP hbits]] := shrincs_fxmss_spec_index_size_bounds hz.
split; first exact (wunsigned_range i).1.
apply (Z.lt_le_trans _ _ _ hi).
change 256%Z with (2^8)%Z.
rewrite -Z.pow_mul_r; try lia.
apply Z.pow_le_mono_r; first lia.
rewrite mulnE in hbits.
lia.
Qed.

Lemma shrincs_fxmss_spec_int_to_byte (h : UInt8) : tval (int_to_bytes h 1) = [::h].
Proof.
change ([:: wrepr U8 (wunsigned h / 1)] = [::h]).
by rewrite Z.div_1_r wrepr_unsigned.
Qed.

Lemma shrincs_fxmss_spec_encode_eq z R i fsig :
  (z < 255)%coq_nat ->
  (wunsigned i < 2 ^ Z.of_nat (minn 64 (255-z)))%Z ->
  shrincs_sf_encode (uint U8 z) R i fsig =
    Some ([:: uint U8 z] ++ R ++
      int_to_bytes i (shrincs_sf_index_size (uint U8 z)) ++ fsig).
Proof.
move=> hz hi.
have hfits := shrincs_fxmss_spec_index_fits hz hi.
have hp : (256 ^ Z.of_nat (shrincs_sf_index_size (uint U8 z)) =
    2 ^ Z.of_nat (8 * shrincs_sf_index_size (uint U8 z)))%Z.
  change 256%Z with (2^8)%Z.
  rewrite -Z.pow_mul_r; try lia.
  by rewrite mulnE Znat.Nat2Z.inj_mul.
have htest : Z.ltb (wunsigned i)
    (2 ^ Z.of_nat (8 * shrincs_sf_index_size (uint U8 z))) = true.
  apply Z.ltb_lt.
  rewrite -hp.
  exact hfits.2.
by rewrite /shrincs_sf_encode htest shrincs_fxmss_spec_int_to_byte.
Qed.

Lemma shrincs_fxmss_spec_parse_encode z R i fsig signature :
  (z < 255)%coq_nat ->
  (wunsigned i < 2 ^ Z.of_nat (minn 64 (255-z)))%Z ->
  size fsig = 2 + WOTS_C_CHAINS_SIZE + (255-z)*16 ->
  shrincs_sf_encode (uint U8 z) R i fsig = Some signature ->
  shrincs_sf_parse signature = Some (uint U8 z, R, i, fsig).
Proof.
move=> hz hi hfs.
rewrite (shrincs_fxmss_spec_encode_eq R fsig hz hi).
move=> [<-].
have hz256 : (z < 256)%coq_nat by lia.
have [hw0 [hw8 hbits]] := shrincs_fxmss_spec_index_size_bounds hz.
have hfits := shrincs_fxmss_spec_index_fits hz hi.
set width := shrincs_sf_index_size (uint U8 z).
set encoded := [:: uint U8 z] ++ R ++ int_to_bytes i width ++ fsig.
have hsize : size encoded = shrincs_sf_signature_size (uint U8 z).
  rewrite /encoded !size_cat !size_tuple hfs /shrincs_sf_signature_size
    shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT.
  rewrite /width !addnE !mulnE.
  lia.
have hbounds : (SHRINCS_SF_SIGNATURE_SIZE_MIN <= size encoded) &&
    (size encoded <= SHRINCS_SF_SIGNATURE_SIZE_MAX).
  rewrite hsize /shrincs_sf_signature_size shrincs_fxmss_spec_uint8_nat //
    /FXMSS_HEIGHT.
  change ((548 <= 17 + width + 2 + 512 + (255-z)*16) &&
    (17 + width + 2 + 512 + (255-z)*16 <= 4619)).
  move/ltP: hw0 => hw0.
  move/leP: hw8 => hw8.
  apply/andP; split; apply/leP; rewrite !addnE !mulnE subnE; lia.
have hheight : (uint U8 z == uint U8 FXMSS_HEIGHT) = false.
  rewrite shrincs_fxmss_spec_word_eq shrincs_fxmss_spec_uint8_unsigned //.
  apply Z.eqb_neq.
  change (Z.of_nat z <> 255)%Z.
  lia.
have hr : slice encoded 1 16 = R.
  change (slice ([tuple uint U8 z] ++ R ++ int_to_bytes i width ++ fsig)
    (1+0) 16 = R).
  by rewrite slice_cat_tail slice_cat_head.
have hiwire : slice encoded 17 width = int_to_bytes i width.
  change (slice ([tuple uint U8 z] ++ R ++ int_to_bytes i width ++ fsig)
    (1+(16+0)) width = int_to_bytes i width).
  by rewrite !slice_cat_tail slice_cat_head.
have hprefix : size (([::uint U8 z] ++ R) ++ int_to_bytes i width) = 17+width.
  by rewrite !size_cat !size_tuple.
have hdrop : drop (17+width) encoded = fsig.
  rewrite /encoded !catA.
  exact: drop_size_cat fsig hprefix.
have hdecode : int_from_bytes U64 (int_to_bytes i width) = i.
  apply shrincs_fxmss_spec_int_from_to_bytes64; last exact hfits.
  by move/leP: hw8.
have hindex : Z.ltb (wunsigned i) (2 ^ Z.of_nat (minn 64 (255-z))) = true.
  by apply Z.ltb_lt.
rewrite /shrincs_sf_parse.
change ((if uint U8 z == uint U8 FXMSS_HEIGHT then None else
  if (SHRINCS_SF_SIGNATURE_SIZE_MIN <= size encoded) &&
     (size encoded <= SHRINCS_SF_SIGNATURE_SIZE_MAX) then
    if size encoded == shrincs_sf_signature_size (uint U8 z) then
      if Z.ltb (wunsigned (int_from_bytes U64 (slice encoded 17 width)))
        (2 ^ Z.of_nat (minn 64 (FXMSS_HEIGHT - Z.to_nat (wunsigned (uint U8 z))))) then
        Some (uint U8 z, slice encoded 1 16,
          int_from_bytes U64 (slice encoded 17 width), drop (17+width) encoded)
      else None
    else None
  else None) = Some (uint U8 z, R, i, fsig)).
rewrite hheight hbounds hsize eqxx hr hiwire hdecode hdrop.
by rewrite shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT hindex.
Qed.
