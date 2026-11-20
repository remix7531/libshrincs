(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.correct

    Total key generation and leaf selection yield honest-signature correctness for
    the literal stateful specification. *)

From mathcomp Require Import boot algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Bool Lia.
From Shrincs Require Import spec.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.wots Require Import security.
From Shrincs.internal.ssprove.fxmss Require Import
  model.nodes model.auth model.wire bridge.keygen.

(* ------------------------------------------------------------------ *)
(** ** Signature correctness *)

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

Lemma shrincs_fxmss_spec_leaf_bounds b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i = true ->
  (z < 255)%coq_nat /\ (i < 2 ^ Z.of_nat (minn 64 (255-z)))%Z.
Proof.
move=> hd hs hl.
have [[hz hdepth] [hi hb]] := hs.
have hlt : (z < 255)%coq_nat.
  have hneq : z <> 255.
    move=> he.
    have hi0 : i = 0%Z by apply (shrincs_fxmss_spec_on_shape_root (d:=d) (b:=b));
      rewrite -he.
    rewrite /shrincs_fxmss_spec_is_leaf he hi0 subnn /= in hl.
    have hd0 : d != 0.
      apply/negP=> /eqP hd0.
      destruct b; unfold shrincs_fxmss_spec_legal_shape in hd; lia.
    by rewrite eq_sym (negbTE hd0) andbF in hl.
  lia.
split; first exact hlt.
have hindex := shrincs_fxmss_spec_index_bound hd hs.
have hfull : (i < 2 ^ Z.of_nat (Nat.sub 255 z))%Z.
  destruct b; first exact hb.
  have hp : (2 ^ 1 <= 2 ^ Z.of_nat (Nat.sub 255 z))%Z.
    apply Z.pow_le_mono_r; lia.
  case: hb => [-> | [-> _]]; lia.
case: (leqP 64 (255-z)) => hm.
- exact hindex.2.
- rewrite subnE.
  exact hfull.
Qed.

Lemma shrincs_fxmss_spec_honest_leaf sk pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i = true ->
  shrincs_fxmss_spec_honest_node sk pk b d z i =
    wots_c_pubkey_gen sk pk (uint U8 z) (wrepr U64 i) b (uint U8 d).
Proof.
move=> hd hs hl.
have hi := shrincs_fxmss_spec_index_bound hd hs.
have hz : (z < 256)%coq_nat by have [[hheight _] _] := hs; lia.
have hdf := shrincs_fxmss_spec_depth_bound hd.
by rewrite /shrincs_fxmss_spec_honest_node /fxmss_node shrincs_fxmss_spec_uint8_nat //
  shrincs_fxmss_spec_node_at_step // hl.
Qed.

Lemma shrincs_fxmss_spec_tree_correct (message_digest : Bytes 32) (sk_seed pk_seed :
  Bytes 16)
    (tree_balanced : bool) (tree_depth leaf_height : nat) (leaf_index : Z)
    (signature : seq UInt8) :
  shrincs_fxmss_spec_legal_shape tree_balanced tree_depth ->
  shrincs_fxmss_spec_on_shape tree_balanced tree_depth leaf_height leaf_index ->
  shrincs_fxmss_spec_is_leaf tree_balanced tree_depth leaf_height leaf_index = true ->
  fxmss_sign message_digest sk_seed (wrepr U64 leaf_index) (uint U8 leaf_height)
    pk_seed tree_balanced (uint U8 tree_depth) = Some signature ->
  exists root,
    fxmss_pubkey_from_sig (wrepr U64 leaf_index) (uint U8 leaf_height)
      signature message_digest pk_seed = Some root /\
    fxmss_node sk_seed (uint U64 0) (uint U8 255) pk_seed
      tree_balanced (uint U8 tree_depth) = Some root.
Proof.
move=> hd hs hl.
rewrite (shrincs_fxmss_spec_sign_eq message_digest sk_seed pk_seed hd hs hl).
case hw: (wots_c_sign _ _ _ _ _ _ _) => [ws|]; last discriminate.
move=> [<-].
have [hz hi] := shrincs_fxmss_spec_leaf_bounds hd hs hl.
have hi64 := shrincs_fxmss_spec_index_bound hd hs.
have hz256 : (leaf_height < 256)%coq_nat by lia.
have hroot : shrincs_fxmss_spec_on_shape tree_balanced tree_depth 255 0.
  rewrite /shrincs_fxmss_spec_on_shape.
  repeat split; try lia.
  by destruct tree_balanced; [change (0 < 1)%Z; lia | left].
exists (shrincs_fxmss_spec_honest_node sk_seed pk_seed tree_balanced tree_depth 255
  0).
split; last exact: (@shrincs_fxmss_spec_honest_node_eq sk_seed pk_seed
  tree_balanced tree_depth 255 0 hd hroot).
rewrite /fxmss_pubkey_from_sig shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT.
rewrite size_cat size_tuple flatten_rows_size shrincs_fxmss_spec_honest_auth_size
  eqxx.
have hindex : Z.ltb (wunsigned (wrepr U64 leaf_index))
    (2 ^ Z.of_nat (minn 64 (255-leaf_height))) = true.
  rewrite wunsigned_repr_small //.
  apply Z.ltb_lt.
  exact hi.
rewrite hindex slice_cat_head.
have hdrop : drop (2 + WOTS_C_CHAINS_SIZE)
    (ws ++ flatten [seq tval n | n <-
      shrincs_fxmss_spec_honest_auth sk_seed pk_seed tree_balanced tree_depth
        leaf_height leaf_index]) =
    flatten [seq tval n | n <-
      shrincs_fxmss_spec_honest_auth sk_seed pk_seed tree_balanced tree_depth
        leaf_height leaf_index].
  by rewrite drop_cat size_tuple ltnn subnn drop0.
rewrite hdrop (@wots_c_verify_sign (uint U8 leaf_height) (wrepr U64 leaf_index)
  tree_balanced (uint U8 tree_depth) message_digest sk_seed pk_seed ws hw).
rewrite -(shrincs_fxmss_spec_honest_leaf sk_seed pk_seed hd hs hl).
rewrite !wunsigned_repr_small //.
change (Some (foldl (shrincs_fxmss_spec_recover_step pk_seed leaf_height leaf_index
    (flatten [seq tval n | n <-
      shrincs_fxmss_spec_honest_auth sk_seed pk_seed tree_balanced tree_depth
        leaf_height leaf_index]))
  (shrincs_fxmss_spec_honest_node sk_seed pk_seed tree_balanced tree_depth leaf_height
    leaf_index)
  (range 0 (255-leaf_height))) =
  Some (shrincs_fxmss_spec_honest_node sk_seed pk_seed tree_balanced tree_depth 255
    0)).
have he := @shrincs_fxmss_spec_recover_honest_fold sk_seed pk_seed tree_balanced
  tree_depth
  leaf_height leaf_index (255-leaf_height) 0 hd hs.
rewrite !addn0 shrincs_fxmss_spec_ancestor_zero in he.
have hcount : leaf_height + (255-leaf_height) = 255.
  rewrite addnE subnE.
  lia.
by rewrite /range subn0 (he hcount).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Signature envelope *)

Lemma shrincs_fxmss_spec_sign_size message sk pk b d z i signature :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i = true ->
  fxmss_sign message sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some signature ->
  size signature = 2 + WOTS_C_CHAINS_SIZE + (255-z)*16.
Proof.
move=> hd hs hl.
rewrite (shrincs_fxmss_spec_sign_eq message sk pk hd hs hl).
case: wots_c_sign => [ws|]; last discriminate.
move=> [<-].
by rewrite size_cat size_tuple flatten_rows_size shrincs_fxmss_spec_honest_auth_size.
Qed.

Lemma shrincs_fxmss_spec_pubkey_fields (seckey : Bytes 82) :
  slice (shrincs_extract_pubkey seckey) 0 16 = slice seckey 32 16 /\
  slice (shrincs_extract_pubkey seckey) 16 16 = slice seckey 48 16 /\
  slice (shrincs_extract_pubkey seckey) 32 16 = slice seckey 66 16.
Proof.
have he : shrincs_extract_pubkey seckey =
    [tuple of slice seckey 32 16 ++ slice seckey 48 16 ++ slice seckey 66 16].
  apply: val_inj.
  change (slice seckey 32 (16+16) ++ slice seckey 66 16 =
    slice seckey 32 16 ++ slice seckey 48 16 ++ slice seckey 66 16).
  by rewrite slice_cat -catA.
rewrite he.
split; first exact: slice_cat_head.
split.
- change (slice (slice seckey 32 16 ++ slice seckey 48 16 ++ slice seckey 66 16)
    (16+0) 16 = slice seckey 48 16).
  by rewrite slice_cat_tail slice_cat_head.
- change (slice (slice seckey 32 16 ++ slice seckey 48 16 ++ slice seckey 66 16)
    (16+(16+0)) 16 = slice seckey 66 16).
  by rewrite !slice_cat_tail slice_all.
Qed.

Lemma shrincs_fxmss_spec_sign_correct (message ctx : seq UInt8) (seckey : Bytes 82)
    (state : option UInt64) (leaf_index : UInt64) (leaf_height : UInt8)
    (signature : seq UInt8) :
  let sk_seed := slice seckey 0 16 in
  let pk_seed := slice seckey 32 16 in
  let structure := slice seckey 64 2 in
  let root := slice seckey 66 16 in
  let balanced := nth (uint U8 0) structure 0 == FXMSS_SHAPE_BALANCED in
  let depth := Z.to_nat (wunsigned (nth (uint U8 0) structure 1)) in
  let z := Z.to_nat (wunsigned leaf_height) in
  let i := wunsigned leaf_index in
  shrincs_fxmss_spec_legal_shape balanced depth ->
  shrincs_fxmss_spec_on_shape balanced depth z i ->
  shrincs_fxmss_spec_is_leaf balanced depth z i = true ->
  shrincs_sf_leaf_select structure state = Some (leaf_index, leaf_height) ->
  fxmss_node sk_seed (uint U64 0) (uint U8 255) pk_seed balanced (uint U8 depth) = Some root ->
  shrincs_sf_sign message ctx seckey state = Some signature ->
  exists R fsig,
    shrincs_sf_parse signature = Some (leaf_height, R, leaf_index, fsig) /\
    fxmss_pubkey_from_sig leaf_index leaf_height fsig
      (H_msg_sf R pk_seed root leaf_height leaf_index
        (shrincs_sf_bound_message message ctx (slice seckey 48 16))) pk_seed = Some root /\
    shrincs_sf_verify message signature ctx (shrincs_extract_pubkey seckey) = true.
Proof.
cbn zeta.
move=> hd hs hl hselect hroot hsign.
rewrite /shrincs_sf_sign hselect in hsign.
case hdomain: (shrincs_sf_message_domain message ctx) in hsign; last discriminate.
case hr: (PRF_msg_sf _ _ _ _ _) => [R|] in hsign; last discriminate.
case hfs: (fxmss_sign _ _ _ _ _ _ _) => [fsig|] in hsign; last discriminate.
have [hz hi] := shrincs_fxmss_spec_leaf_bounds hd hs hl.
have hsign' := hfs.
rewrite -[leaf_height]uint_to_nat -[leaf_index]wrepr_unsigned
  -[nth (uint U8 0) (slice seckey 64 2) 1]uint_to_nat in hsign'.
have hlen := shrincs_fxmss_spec_sign_size hd hs hl hsign'.
have [recovered [hrecover hhonest]] := shrincs_fxmss_spec_tree_correct hd hs hl
  hsign'.
rewrite hroot in hhonest.
move: hhonest => [hroot_eq].
rewrite -hroot_eq !uint_to_nat !wrepr_unsigned in hrecover.
have hparse := @shrincs_fxmss_spec_parse_encode (Z.to_nat (wunsigned leaf_height))
  R leaf_index fsig signature hz hi hlen.
rewrite uint_to_nat in hparse.
have hp := hparse hsign.
exists R, fsig.
split; first exact hp.
split; first exact hrecover.
have [hpk [hpartner hrt]] := shrincs_fxmss_spec_pubkey_fields seckey.
by rewrite /shrincs_sf_verify hdomain hpk hpartner hrt hp hrecover eqxx.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Total key generation *)

Local Opaque wots_c_pubkey_gen H.

Lemma shrincs_fxmss_spec_balanced_deep_right fuel sk pk depth level :
  (level <= 64)%coq_nat ->
  (64 < Z.to_nat (wunsigned depth))%coq_nat ->
  fxmss_node_at fuel sk (wrepr U64 (2 ^ Z.of_nat level - 1))
    (uint U8 (255 - level)) pk true depth = None.
Proof.
elim: fuel level => [|fuel ih] level hlevel hdepth; first by [].
have hh : (255 - level < 256)%coq_nat by rewrite subnE; lia.
have hi : (0 <= 2 ^ Z.of_nat level - 1 < 2 ^ 64)%Z.
{ have hp : (0 < 2 ^ Z.of_nat level)%Z by apply Z.pow_pos_nonneg; lia.
  have hle : (2 ^ Z.of_nat level <= 2 ^ 64)%Z by apply Z.pow_le_mono_r; lia.
  lia. }
cbn [fxmss_node_at].
rewrite shrincs_fxmss_spec_uint8_nat // wunsigned_repr_small //.
have he : FXMSS_HEIGHT - (255 - level) = level
  by rewrite /FXMSS_HEIGHT !subnE; lia.
have hn : (level == Z.to_nat (wunsigned depth)) = false by apply/eqP; lia.
have hl : (level < Z.to_nat (wunsigned depth))%N by apply/ltP; lia.
rewrite he hn hl /=.
case hg: ((0 < 255 - level) &&
  Z.ltb (2 * (2 ^ Z.of_nat level - 1) + 1) (2 ^ 64)); last by [].
have hs : (level < 64)%coq_nat.
{ move/andP: hg => [_ /Z.ltb_lt hg].
  have hne : level <> 64.
  { move=> heq. rewrite heq in hg. vm_compute in hg. discriminate. }
  lia. }
case: fxmss_node_at => [lc|]; last by [].
have hhnext : 255 - level - 1 = 255 - level.+1 by rewrite !subnE; lia.
have hinext : (2 * (2 ^ Z.of_nat level - 1) + 1 =
    2 ^ Z.of_nat level.+1 - 1)%Z.
{ rewrite Znat.Nat2Z.inj_succ Z.pow_succ_r; last lia. lia. }
change (match fxmss_node_at fuel sk
    (wrepr U64 (2 * (2 ^ Z.of_nat level - 1) + 1))
    (uint U8 (255 - level - 1)) pk true depth with
  | Some rc => Some (H pk (FxmssTree (uint U8 (255 - level))
      (wrepr U64 (2 ^ Z.of_nat level - 1))) [tuple of lc ++ rc])
  | None => None end = None).
rewrite hhnext hinext (ih level.+1); try lia.
reflexivity.
Qed.

Local Opaque fxmss_node_at.

Lemma shrincs_fxmss_spec_root_balanced_depth sk pk depth root :
  fxmss_node sk (uint U64 0) (uint U8 255) pk true depth = Some root ->
  (Z.to_nat (wunsigned depth) <= 64)%coq_nat.
Proof.
move=> hr.
case: (Nat.le_gt_cases (Z.to_nat (wunsigned depth)) 64) => // hd.
have hn := @shrincs_fxmss_spec_balanced_deep_right 256 sk pk depth 0 (ltac:(lia)) hd.
rewrite /fxmss_node (shrincs_fxmss_spec_uint8_nat (z:=255) (ltac:(lia))) in hr.
change (fxmss_node_at 256 sk (uint U64 0) (uint U8 255) pk true depth = None) in hn.
rewrite hr in hn.
discriminate.
Qed.

Lemma shrincs_fxmss_spec_secret_fields (ks kp pp partner root : Bytes 16)
    (structure : Bytes 2) :
  let sk := [tuple of ks ++ kp ++ pp ++ partner ++ structure ++ root] in
  [ /\ slice sk 0 16 = ks,
       slice sk 32 16 = pp,
       slice sk 64 2 = structure &
       slice sk 66 16 = root ].
Proof.
cbn zeta.
split.
- change (slice (ks ++ kp ++ pp ++ partner ++ structure ++ root) 0 16 = ks).
  exact: slice_cat_head.
- change (slice (ks ++ kp ++ pp ++ partner ++ structure ++ root)
    (16+(16+0)) 16 = pp).
  by rewrite !slice_cat_tail slice_cat_head.
- change (slice (ks ++ kp ++ pp ++ partner ++ structure ++ root)
    (16+(16+(16+(16+0)))) 2 = structure).
  by rewrite !slice_cat_tail slice_cat_head.
- change (slice (ks ++ kp ++ pp ++ partner ++ structure ++ root)
    (16+(16+(16+(16+(2+0))))) 16 = root).
  by rewrite !slice_cat_tail slice_all.
Qed.

Lemma shrincs_fxmss_spec_keygen_root seed structure partner sk pk :
  shrincs_sf_keygen seed structure partner = Some (sk, pk) ->
  fxmss_node (slice sk 0 16) (uint U64 0) (uint U8 255) (slice sk 32 16)
    (nth (uint U8 0) (slice sk 64 2) 0 == FXMSS_SHAPE_BALANCED)
    (nth (uint U8 0) (slice sk 64 2) 1) = Some (slice sk 66 16).
Proof.
rewrite /shrincs_sf_keygen.
case: ifP => // hshape.
case hr: fxmss_node => [root|] //.
move=> [<- _].
have [hks hpp hst hroot] := shrincs_fxmss_spec_secret_fields
  (slice seed 0 16) (slice seed 16 16) (slice seed 32 16) partner root structure.
by rewrite hks hpp hst hroot.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf selection *)

Lemma shrincs_fxmss_spec_select_positive structure state i h :
  shrincs_sf_leaf_select structure state = Some (i, h) ->
  (0 < Z.to_nat (wunsigned (nth (uint U8 0) structure 1)))%coq_nat.
Proof.
rewrite /shrincs_sf_leaf_select.
case: state => [ctr|]; last discriminate.
case: ifP => [/eqP hz|/eqP hn]; first discriminate.
move=> _.
lia.
Qed.

Lemma shrincs_fxmss_spec_select_correct (structure : 2.-tuple UInt8) state i h :
  let b := nth (uint U8 0) structure 0 == FXMSS_SHAPE_BALANCED in
  let d := Z.to_nat (wunsigned (nth (uint U8 0) structure 1)) in
  shrincs_fxmss_spec_legal_shape b d ->
  shrincs_sf_leaf_select structure state = Some (i, h) ->
  shrincs_fxmss_spec_on_shape b d (Z.to_nat (wunsigned h)) (wunsigned i) /\
  shrincs_fxmss_spec_is_leaf b d (Z.to_nat (wunsigned h)) (wunsigned i) = true.
Proof.
cbn zeta.
set b := (_ == FXMSS_SHAPE_BALANCED).
set d := Z.to_nat _.
move=> hd.
have hd0 : (d == 0) = false.
{ apply/eqP => hz.
case: b hd => /= hd; lia.
}
have hd255 : (d <= 255)%coq_nat.
{ case: b hd => /= hd; lia.
}
rewrite /shrincs_sf_leaf_select.
case: state => [ctr|]; last discriminate.
fold d.
rewrite hd0.
case hu: (nth (uint U8 0) structure 0 == FXMSS_SHAPE_UNBALANCED).
have hb : b = false.
{ rewrite /b (eqP hu).
reflexivity.
}
rewrite hb.
case hc: (Z.eqb (wunsigned ctr) (Z.of_nat d)).
move=> [<- <-].
rewrite (shrincs_fxmss_spec_uint8_nat (z:=FXMSS_HEIGHT - d) (ltac:(rewrite /FXMSS_HEIGHT
  subnE; lia))).
change (shrincs_fxmss_spec_on_shape false d (255 - d) 0 /\ shrincs_fxmss_spec_is_leaf
  false d (255 - d) 0 = true).
have he : 255 - (255 - d) = d by rewrite !subnE; lia.
rewrite /shrincs_fxmss_spec_on_shape /shrincs_fxmss_spec_is_leaf he eqxx.
split; last reflexivity.
repeat split; try lia.
rewrite subnE.
lia.
rewrite subnE in he.
rewrite subnE.
lia.
case hc1: (Z.ltb (wunsigned ctr) (Z.of_nat d)); last discriminate.
move=> [<- <-].
have hcpos := (wunsigned_range ctr).
move/Z.ltb_lt: hc1 => hc1.
have hcn : (Z.to_nat (wunsigned ctr) < d)%coq_nat by lia.
rewrite (shrincs_fxmss_spec_uint8_nat (z:=FXMSS_HEIGHT - 1 - Z.to_nat (wunsigned ctr))
  (ltac:(rewrite /FXMSS_HEIGHT !subnE; lia))).
change (shrincs_fxmss_spec_on_shape false d (254 - Z.to_nat (wunsigned ctr)) 1 /\
  shrincs_fxmss_spec_is_leaf false d (254 - Z.to_nat (wunsigned ctr)) 1 = true).
rewrite /shrincs_fxmss_spec_on_shape /shrincs_fxmss_spec_is_leaf /= orbT.
split; last reflexivity.
rewrite !subnE.
repeat split; try lia.
change (Nat.le (Nat.sub 255 (Nat.sub 254 (Z.to_nat (wunsigned ctr)))) d).
lia.
fold b.
case hb: b; last discriminate.
case hc: (Z.ltb (wunsigned ctr) (2 ^ Z.of_nat d)); last discriminate.
move=> [<- <-].
rewrite (shrincs_fxmss_spec_uint8_nat (z:=FXMSS_HEIGHT - d) (ltac:(rewrite /FXMSS_HEIGHT
  subnE; lia))).
have he : Nat.sub 255 (Nat.sub 255 d) = d by lia.
have hcpos := wunsigned_range ctr.
move/Z.ltb_lt: hc => hc.
rewrite /FXMSS_HEIGHT /shrincs_fxmss_spec_on_shape /shrincs_fxmss_spec_is_leaf !subnE he
  eqxx.
split; last reflexivity.
repeat split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stateful signing correctness *)

Local Opaque fxmss_node fxmss_node_at.

Lemma shrincs_fxmss_spec_keygen_selected seed structure partner sk pk state i h :
  shrincs_sf_keygen seed structure partner = Some (sk, pk) ->
  shrincs_sf_leaf_select (slice sk 64 2) state = Some (i, h) ->
  shrincs_fxmss_spec_legal_shape
    (nth (uint U8 0) (slice sk 64 2) 0 == FXMSS_SHAPE_BALANCED)
    (Z.to_nat (wunsigned (nth (uint U8 0) (slice sk 64 2) 1))).
Proof.
move=> hk hs.
have hr := shrincs_fxmss_spec_keygen_root hk.
have hp := shrincs_fxmss_spec_select_positive hs.
have hb := wunsigned_range (nth (uint U8 0) (slice sk 64 2) 1).
change (0 <= wunsigned (nth (uint U8 0) (slice sk 64 2) 1) < 256)%Z in hb.
case he: (_ == FXMSS_SHAPE_BALANCED) in hr *; rewrite /shrincs_fxmss_spec_legal_shape.
split; first lia.
exact: shrincs_fxmss_spec_root_balanced_depth hr.
split; lia.
Qed.

Lemma shrincs_fxmss_spec_public_correct :
  forall seed structure partner seckey pubkey message ctx state signature,
    shrincs_sf_keygen seed structure partner = Some (seckey, pubkey) ->
    shrincs_sf_sign message ctx seckey state = Some signature ->
    shrincs_sf_verify message signature ctx pubkey = true.
Proof.
move=> seed structure partner sk pk message ctx state signature hk hs.
have hs' := hs.
rewrite /shrincs_sf_sign in hs'.
case: (shrincs_sf_message_domain message ctx) in hs'; last discriminate.
case hsel: shrincs_sf_leaf_select => [[i h]|] in hs'; last discriminate.
have hd := shrincs_fxmss_spec_keygen_selected hk hsel.
have [hon hleaf] := shrincs_fxmss_spec_select_correct hd hsel.
have hr := shrincs_fxmss_spec_keygen_root hk.
have hr' : fxmss_node (slice sk 0 16) (uint U64 0) (uint U8 255) (slice sk 32 16) (nth (uint U8 0) (slice sk 64 2) 0 == FXMSS_SHAPE_BALANCED) (uint U8 (Z.to_nat (wunsigned (nth (uint U8 0) (slice sk 64 2) 1)))) = Some (slice sk 66 16).
{ by rewrite uint_to_nat. }
have [R [fsig [_ [_ hv]]]] := shrincs_fxmss_spec_sign_correct hd hon hleaf hsel hr' hs.
rewrite (shrincs_fxmss_spec_keygen_pubkey _ _ _ _ _ hk).
exact hv.
Qed.
