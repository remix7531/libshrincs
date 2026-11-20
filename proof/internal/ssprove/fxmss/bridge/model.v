(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bridge.model

    Byte encodings and the public oracle bodies identify the specification
    experiment with the internal tree model. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  model.nodes params model.wire scheme instance.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Lia.

(* ------------------------------------------------------------------ *)
(** ** Bridge hash *)

#[local] Close Scope Z_scope.

Definition shrincs_fxmss_rom_hash_args :=
  (Bytes 16 * ((Bytes 16 * Bytes 16) * ((UInt8 * UInt64) * seq UInt8)))%type.

Definition shrincs_fxmss_rom_hash_decode (x : fxmss_sf_hash_input) :
  shrincs_fxmss_rom_hash_args :=
  (x.1, (x.2.1, ((uint U8 x.2.2.1.1, uint U64 x.2.2.1.2), x.2.2.2))).

Definition shrincs_fxmss_rom_hash_encode (x : shrincs_fxmss_rom_hash_args) :
  fxmss_sf_hash_input :=
  (x.1, (x.2.1,
    ((Z.to_nat (wunsigned x.2.2.1.1), Z.to_nat (wunsigned x.2.2.1.2)), x.2.2.2))).

Definition shrincs_fxmss_rom_hash_eval (x : fxmss_sf_hash_input) : Bytes 32 :=
  let a := shrincs_fxmss_rom_hash_decode x in
  H_msg_sf a.1 a.2.1.1 a.2.1.2 a.2.2.1.1 a.2.2.1.2 a.2.2.2.

Lemma shrincs_fxmss_rom_hash_encodeK : cancel shrincs_fxmss_rom_hash_encode
  shrincs_fxmss_rom_hash_decode.
Proof.
move=> [r [[pp root] [[h i] m]]].
by rewrite /shrincs_fxmss_rom_hash_encode /shrincs_fxmss_rom_hash_decode /=
  !uint_to_nat.
Qed.

Lemma shrincs_fxmss_rom_hash_decodeK x :
  fxmss_sf_hash_valid x -> shrincs_fxmss_rom_hash_encode (shrincs_fxmss_rom_hash_decode
    x) = x.
Proof.
case: x => [r [[pp root] [[h i] m]]].
rewrite /fxmss_sf_hash_valid /=.
move/andP=> [/andP [/ltP hh /Z.ltb_lt hi] hm].
have hiK : Z.to_nat (wunsigned (uint U64 i)) = i.
{ rewrite /uint wunsigned_repr_small.
  - change (0 <= Z.of_nat i < 2^64)%Z.
    lia.
  - exact: Znat.Nat2Z.id. }
change ((r, ((pp, root),
  ((Z.to_nat (wunsigned (uint U8 h)), Z.to_nat (wunsigned (uint U64 i))), m))) =
  (r, ((pp, root), ((h, i), m)))).
by rewrite shrincs_fxmss_spec_uint8_nat // hiK.
Qed.

Lemma shrincs_fxmss_rom_hash_decode_inj x y :
  fxmss_sf_hash_valid x -> fxmss_sf_hash_valid y ->
  shrincs_fxmss_rom_hash_decode x = shrincs_fxmss_rom_hash_decode y -> x = y.
Proof.
move=> hx hy he.
by rewrite -(shrincs_fxmss_rom_hash_decodeK x hx) he (shrincs_fxmss_rom_hash_decodeK y
  hy).
Qed.

Lemma shrincs_fxmss_rom_bound_message_valid (cm : fxmss_sf_message) (partner : Bytes 16)
  :
  fxmss_sf_message_valid cm ->
  Z.leb (Z.of_nat (size (shrincs_sf_bound_message cm.2 cm.1 partner)))
    (Z.sub (Z.pow 2 61) 111).
Proof.
rewrite /fxmss_sf_message_valid /shrincs_sf_message_domain.
move/andP=> [/Z.leb_le hm /leP hc].
apply/Z.leb_le.
rewrite /shrincs_sf_bound_message !size_cat !size_tuple.
change (Z.of_nat (1 + (1 + (size cm.1 + (16 + size cm.2))))
  <= 2^61 - 111)%Z.
rewrite !Znat.Nat2Z.inj_add.
have hcZ : (Z.of_nat (@size UInt8 cm.1) <= 255)%Z.
{ exact: (proj1 (Znat.Nat2Z.inj_le _ _) hc). }
change (Z.of_nat (@size UInt8 cm.2) <= 2^61 - 384)%Z in hm.
change (1 + (1 + (Z.of_nat (@size UInt8 cm.1) +
  (16 + Z.of_nat (@size UInt8 cm.2)))) <= 2^61 - 111)%Z.
lia.
Qed.

Lemma shrincs_fxmss_rom_hash_encode_valid (a : shrincs_fxmss_rom_hash_args) :
  Z.leb (Z.of_nat (size a.2.2.2)) (Z.sub (Z.pow 2 61) 111) ->
  fxmss_sf_hash_valid (shrincs_fxmss_rom_hash_encode a).
Proof.
case: a => [r [[pp root] [[h i] m]]].
rewrite /shrincs_fxmss_rom_hash_encode /fxmss_sf_hash_valid /= => hm.
rewrite hm andbT.
apply/andP; split.
- apply/ltP.
  have hh := wunsigned_range h.
  change (0 <= wunsigned h < 256)%Z in hh.
  lia.
- apply/Z.ltb_lt.
  rewrite (Znat.Z2Nat.id _ (wunsigned_range i).1).
  exact: (wunsigned_range i).2.
Qed.

Lemma shrincs_fxmss_rom_verify_query_valid pk cm signature x :
  fxmss_sf_message_valid cm ->
  fxmss_sf_verify_query pk cm signature = Some x -> fxmss_sf_hash_valid x.
Proof.
move=> hm.
rewrite /fxmss_sf_verify_query.
case: shrincs_sf_parse => [[[[h r] i] fsig]|] //.
move=> [<-].
apply: (shrincs_fxmss_rom_hash_encode_valid
  (r, ((slice pk 0 16, slice pk 32 16),
    ((h, i), shrincs_sf_bound_message cm.2 cm.1 (slice pk 16 16))))).
exact: shrincs_fxmss_rom_bound_message_valid.
Qed.

Lemma shrincs_fxmss_rom_verify_bridge pk cm signature :
  shrincs_sf_verify cm.2 signature cm.1 pk =
  if fxmss_sf_message_valid cm then
    if fxmss_sf_verify_query pk cm signature is Some x then
      stateful_rom.sf_verify_finish fxmss_sf_scheme pk cm signature
        (shrincs_fxmss_rom_hash_eval x)
    else false
  else false.
Proof.
change (shrincs_sf_verify cm.2 signature cm.1 pk =
  if fxmss_sf_message_valid cm then
    if fxmss_sf_verify_query pk cm signature is Some x then
      shrincs_sf_verify_with_digest cm.2 signature cm.1 pk
        (shrincs_fxmss_rom_hash_eval x)
    else false
  else false).
rewrite /shrincs_sf_verify /fxmss_sf_message_valid.
case hm: shrincs_sf_message_domain => //.
rewrite /fxmss_sf_verify_query /shrincs_sf_verify_with_digest
  /shrincs_sf_recover_with_digest hm.
case: shrincs_sf_parse => [[[[h r] i] fsig]|] //.
by rewrite /shrincs_fxmss_rom_hash_eval /shrincs_fxmss_rom_hash_decode /=
  !uint_to_nat.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge sign *)

#[local] Close Scope Z_scope.

Lemma shrincs_fxmss_rom_sign_query_valid sk cm x :
  fxmss_sf_message_valid cm ->
  fxmss_sf_sign_query sk cm = Some x -> fxmss_sf_hash_valid x.
Proof.
move=> hm.
rewrite /fxmss_sf_sign_query.
case: shrincs_sf_leaf_select => [[i h]|] //.
case: PRF_msg_sf => [r|] //.
move=> [<-].
apply: (shrincs_fxmss_rom_hash_encode_valid
  (r, ((slice sk.1 32 16, slice sk.1 66 16),
    ((h, i), shrincs_sf_bound_message cm.2 cm.1 (slice sk.1 48 16))))).
exact: shrincs_fxmss_rom_bound_message_valid.
Qed.

(* Keep the cryptographic computations abstract while splitting their guards. *)
Local Opaque fxmss_sign shrincs_sf_encode PRF_msg_sf H_msg_sf.

Lemma shrincs_fxmss_rom_sign_bridge sk cm :
  shrincs_sf_sign cm.2 cm.1 sk.1 sk.2 =
  if fxmss_sf_message_valid cm then
    if stateful_rom.sf_sign_query fxmss_sf_scheme sk cm is Some x then
      stateful_rom.sf_sign_finish fxmss_sf_scheme sk cm (shrincs_fxmss_rom_hash_eval x)
    else None
  else None.
Proof.
change (shrincs_sf_sign cm.2 cm.1 sk.1 sk.2 =
  if fxmss_sf_message_valid cm then
    if fxmss_sf_sign_query sk cm is Some x then
      shrincs_sf_sign_with_digest cm.2 cm.1 sk.1 sk.2
        (shrincs_fxmss_rom_hash_eval x)
    else None
  else None).
rewrite /shrincs_sf_sign /fxmss_sf_message_valid.
case hm: shrincs_sf_message_domain => //.
rewrite /fxmss_sf_sign_query /shrincs_sf_sign_with_digest hm.
case: shrincs_sf_leaf_select => [[i h]|] //.
case: PRF_msg_sf => [r|]; last reflexivity.
by rewrite /shrincs_fxmss_rom_hash_eval /shrincs_fxmss_rom_hash_decode /=
  !uint_to_nat.
Qed.

Lemma shrincs_fxmss_spec_sign_transition_pair message ctx sk state :
  shrincs_sf_sign_transition message ctx sk state =
  if shrincs_sf_message_domain message ctx then
    ((shrincs_sf_consume (slice sk 64 2) state).1,
      shrincs_sf_sign message ctx sk state)
  else (state, None).
Proof.
rewrite /shrincs_sf_sign_transition.
case hm: shrincs_sf_message_domain; last reflexivity.
rewrite /shrincs_sf_consume.
case hs: state => [ctr|].
- case hl: shrincs_sf_leaf_select => [[i h]|].
  + reflexivity.
  + by rewrite /shrincs_sf_sign hm hl.
- by rewrite /shrincs_sf_sign hm /shrincs_sf_leaf_select.
Qed.

Lemma shrincs_fxmss_rom_sign_transition_bridge sk cm :
  shrincs_sf_sign_transition cm.2 cm.1 sk.1 sk.2 =
  if fxmss_sf_message_valid cm then
    ((stateful_rom.sf_sign_next fxmss_sf_scheme sk cm).2,
      if stateful_rom.sf_sign_query fxmss_sf_scheme sk cm is Some x then
        stateful_rom.sf_sign_finish fxmss_sf_scheme sk cm (shrincs_fxmss_rom_hash_eval
          x)
      else None)
  else (sk.2, None).
Proof.
rewrite shrincs_fxmss_spec_sign_transition_pair shrincs_fxmss_rom_sign_bridge.
rewrite /fxmss_sf_message_valid.
by case: shrincs_sf_message_domain.
Qed.

Lemma shrincs_fxmss_rom_sign_invalid sk cm :
  ~~ fxmss_sf_message_valid cm ->
  shrincs_sf_sign_transition cm.2 cm.1 sk.1 sk.2 = (sk.2, None).
Proof.
by move=> /negbTE hm; rewrite shrincs_fxmss_rom_sign_transition_bridge hm.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge message *)

Definition shrincs_fxmss_rom_embed_message (partner : bytes 16) (cm :
  shrincs_fxmss_message) :
    shrincs_fxmss_message := (cm.1, partner ++ cm.2).

Lemma shrincs_fxmss_rom_embed_message_inj partner :
  injective (shrincs_fxmss_rom_embed_message partner).
Proof.
move=> [ctx m] [ctx' m'] /= [-> hm].
by rewrite (jasmin_util.cat_inj_head hm).
Qed.

Lemma shrincs_fxmss_rom_embed_message_valid partner cm :
  (size (shrincs_fxmss_rom_embed_message partner cm).1 <= 255) &&
    Z.leb (Z.of_nat (size (shrincs_fxmss_rom_embed_message partner cm).2))
      (Z.sub (Z.pow 2 61) 368) = fxmss_sf_message_valid cm.
Proof.
rewrite /shrincs_fxmss_rom_embed_message /fxmss_sf_message_valid
  /shrincs_sf_message_domain /= size_cat size_tuple andbC.
congr andb.
apply Bool.eq_true_iff_eq.
rewrite !Z.leb_le Znat.Nat2Z.inj_add.
lia.
Qed.

Lemma shrincs_fxmss_rom_embed_message_bound partner cm :
  [:: uint U8 0; uint U8 (size (shrincs_fxmss_rom_embed_message partner cm).1)] ++
    (shrincs_fxmss_rom_embed_message partner cm).1 ++
    (shrincs_fxmss_rom_embed_message partner cm).2 =
  shrincs_sf_bound_message cm.2 cm.1 partner.
Proof.
by rewrite /shrincs_fxmss_rom_embed_message /shrincs_sf_bound_message
  !shrincs_fxmss_spec_int_to_byte.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge internal *)

#[local] Close Scope Z_scope.

Lemma shrincs_fxmss_rom_internal_message_valid partner (cm : shrincs_fxmss_message) :
  shrincs_fxmss_message_valid (shrincs_fxmss_rom_embed_message partner cm) =
    fxmss_sf_message_valid cm.
Proof. exact: shrincs_fxmss_rom_embed_message_valid. Qed.

Lemma shrincs_fxmss_rom_internal_bound_message partner (cm : shrincs_fxmss_message) :
  shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message partner cm) =
    shrincs_sf_bound_message cm.2 cm.1 partner.
Proof. exact: shrincs_fxmss_rom_embed_message_bound. Qed.

Definition shrincs_fxmss_rom_internal_query (x : fxmss_sf_hash_input) :
  shrincs_fxmss_hmsg_input :=
  shrincs_fxmss_rom_hash_decode x.

Lemma shrincs_fxmss_rom_internal_query_inj x y :
  fxmss_sf_hash_valid x -> fxmss_sf_hash_valid y ->
  shrincs_fxmss_rom_internal_query x = shrincs_fxmss_rom_internal_query y -> x = y.
Proof. exact: shrincs_fxmss_rom_hash_decode_inj. Qed.

Definition shrincs_fxmss_rom_rom_rel
    (public_table : chMap fxmss_sf_hash_input (bytes 32))
    (internal_table : chMap shrincs_fxmss_hmsg_input (bytes 32)) : Prop :=
  forall x, fxmss_sf_hash_valid x ->
    getm public_table x = getm internal_table (shrincs_fxmss_rom_internal_query x).

Lemma shrincs_fxmss_rom_rom_rel_empty : shrincs_fxmss_rom_rom_rel emptym emptym.
Proof. by move=> x hx; rewrite !emptymE. Qed.

Lemma shrincs_fxmss_rom_rom_rel_set public_table internal_table x md :
  shrincs_fxmss_rom_rom_rel public_table internal_table -> fxmss_sf_hash_valid x ->
  shrincs_fxmss_rom_rom_rel (setm public_table x md)
    (setm internal_table (shrincs_fxmss_rom_internal_query x) md).
Proof.
move=> hr hx y hy.
rewrite !setmE.
case hxy: (y == x).
- move/eqP: hxy => ->.
  by rewrite eqxx.
- (* Distinct valid queries remain distinct under the internal encoding. *)
  have hdec :
    (shrincs_fxmss_rom_internal_query y == shrincs_fxmss_rom_internal_query x) =
      false.
  { apply/negbTE/negP=> /eqP he.
    have heq := shrincs_fxmss_rom_internal_query_inj y x hy hx he.
    by rewrite heq eqxx in hxy. }
  by rewrite hdec hr.
Qed.

Lemma shrincs_fxmss_rom_internal_hash_domain (x : shrincs_fxmss_hmsg_input) :
  fxmss_sf_hash_valid (shrincs_fxmss_rom_hash_encode x) =
    Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111).
Proof.
case hm: (Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111)).
- exact: shrincs_fxmss_rom_hash_encode_valid.
- by rewrite /fxmss_sf_hash_valid /shrincs_fxmss_rom_hash_encode /= hm andbF.
Qed.

Lemma shrincs_fxmss_rom_internal_verify pk cm signature md :
  stateful_rom.sf_verify_finish fxmss_sf_scheme pk cm signature md =
  if fxmss_sf_message_valid cm then
    if shrincs_sf_parse signature is Some (h, r, i, fsig) then
      shrincs_fxmss_verify shrincs_fxmss_sha256 (slice pk 0 16) (slice pk 32 16)
        (h, i) fsig md
    else false
  else false.
Proof.
change (shrincs_sf_verify_with_digest cm.2 signature cm.1 pk md =
  if fxmss_sf_message_valid cm then
    if shrincs_sf_parse signature is Some (h, r, i, fsig) then
      shrincs_fxmss_verify shrincs_fxmss_sha256 (slice pk 0 16) (slice pk 32 16)
        (h, i) fsig md
    else false
  else false).
rewrite /fxmss_sf_message_valid
  /shrincs_sf_verify_with_digest /shrincs_sf_recover_with_digest.
case: shrincs_sf_message_domain; last reflexivity.
case: shrincs_sf_parse => [[[[h r] i] fsig]|]; last reflexivity.
rewrite shrincs_fxmss_verify_adapter.
by case: fxmss_pubkey_from_sig.
Qed.

Local Opaque fxmss_sign shrincs_sf_encode PRF_msg_sf H_msg_sf.

Lemma shrincs_fxmss_rom_internal_sign_finish (sk : fxmss_sf_secret) cm md i h r :
  fxmss_sf_message_valid cm ->
  shrincs_sf_leaf_select (slice sk.1 64 2) sk.2 = Some (i, h) ->
  shrincs_fxmss_prf_msg_eval shrincs_fxmss_sha256 (slice sk.1 16 16) (slice sk.1 32 16)
    (h, i)
    (shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message (slice sk.1 48 16)
      cm)) = Some r ->
  stateful_rom.sf_sign_finish fxmss_sf_scheme sk cm md =
    let pp := slice sk.1 32 16 in
    let structure := slice sk.1 64 2 in
    let b := nth (uint U8 0) structure 0 == FXMSS_SHAPE_BALANCED in
    let d := nth (uint U8 0) structure 1 in
    if shrincs_fxmss_sign shrincs_fxmss_sha256 md
        (shrincs_fxmss_derived_keys shrincs_fxmss_sha256 pp (slice sk.1 0 16) b d)
        i h pp b d is Some fsig then
      shrincs_sf_encode h r i fsig
    else None.
Proof.
rewrite /fxmss_sf_message_valid.
move=> hm hl.
rewrite shrincs_fxmss_rom_internal_bound_message.
move=> hr.
change (PRF_msg_sf (slice sk.1 16 16) (slice sk.1 32 16) h i
  (shrincs_sf_bound_message cm.2 cm.1 (slice sk.1 48 16)) = Some r) in hr.
rewrite shrincs_fxmss_sign_adapter.
cbn [stateful_rom.sf_sign_finish fxmss_sf_scheme].
by rewrite /shrincs_sf_sign_with_digest hm hl hr.
Qed.
