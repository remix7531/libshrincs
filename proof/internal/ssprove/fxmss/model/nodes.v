(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.model.nodes

    Legal coordinates and totality of the literal tree evaluator. Coordinates
    are measured from height 255; unbalanced trees descend on the left. *)

From mathcomp Require Import boot algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Bool Lia.
From Shrincs Require Import spec.
From Shrincs.internal.ssprove Require Import shape.

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

Definition shrincs_fxmss_spec_legal_shape (b : bool) (d : nat) : Prop :=
  if b then (Nat.le 1 d /\ Nat.le d 64) else (Nat.le 1 d /\ Nat.le d 255).

Definition shrincs_fxmss_spec_on_shape (b : bool) (d z : nat) (i : Z) : Prop :=
  (Nat.le z 255 /\ Nat.le (Nat.sub 255 z) d) /\
  (0 <= i)%Z /\
  if b then (i < 2 ^ Z.of_nat (Nat.sub 255 z))%Z
  else i = 0%Z \/ (i = 1%Z /\ (z < 255)%coq_nat).

Lemma shrincs_fxmss_spec_uint8_unsigned (z : nat) :
  (z < 256)%coq_nat -> wunsigned (uint U8 z) = Z.of_nat z.
Proof.
move=> hz.
rewrite /uint wunsigned_repr_small //.
change (0 <= Z.of_nat z < 256)%Z.
lia.
Qed.

Lemma shrincs_fxmss_spec_uint8_nat (z : nat) :
  (z < 256)%coq_nat -> Z.to_nat (wunsigned (uint U8 z)) = z.
Proof.
move=> hz.
by rewrite shrincs_fxmss_spec_uint8_unsigned // Znat.Nat2Z.id.
Qed.

Lemma shrincs_fxmss_spec_index_bound b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  (0 <= i < 2 ^ 64)%Z.
Proof.
move=> hd [[hz hdepth] [hi hbound]].
split; first exact hi.
case: b hd hbound => hd hbound.
- (* Balanced tree: the depth bound keeps the index within 64 bits. *)
  have hp : (2 ^ Z.of_nat (Nat.sub 255 z) <= 2 ^ 64)%Z.
    apply Z.pow_le_mono_r; first lia.
    change (Z.of_nat (Nat.sub 255 z) <= Z.of_nat 64)%Z.
    apply (proj1 (Znat.Nat2Z.inj_le _ _)).
    exact (Nat.le_trans _ _ _ hdepth (proj2 hd)).
  exact (Z.lt_le_trans _ _ _ hbound hp).
- case: hbound => [-> | [-> _]]; lia.
Qed.

Lemma shrincs_fxmss_spec_word_eq (ws : wsize) (x y : word ws) :
  (x == y) = Z.eqb (wunsigned x) (wunsigned y).
Proof.
apply/idP/idP.
- move/eqP=> ->.
  exact: Z.eqb_refl.
- move/Z.eqb_eq=> h.
  apply/eqP.
  rewrite -[x]wrepr_unsigned -[y]wrepr_unsigned h.
  reflexivity.
Qed.

Definition shrincs_fxmss_spec_is_leaf (b : bool) (d z : nat) (i : Z) : bool :=
  (255 - z == d) || (~~ b && Z.eqb i 1).

Lemma shrincs_fxmss_spec_on_shape_children b d z i :
  shrincs_fxmss_spec_on_shape b d z.+1 i ->
  shrincs_fxmss_spec_is_leaf b d z.+1 i = false ->
  shrincs_fxmss_spec_on_shape b d z (2 * i)%Z /\
  shrincs_fxmss_spec_on_shape b d z (2 * i + 1)%Z.
Proof.
move=> [[hz hdepth] [hi hbound]].
rewrite /shrincs_fxmss_spec_is_leaf.
move/orb_false_iff=> [hne hside].
have hned : Nat.sub 255 z.+1 <> d.
  move=> he.
  by rewrite subnE he eqxx in hne.
have hzdepth : (Nat.sub 255 z = S (Nat.sub 255 z.+1)).
  lia.
case: b hbound hside => hbound hside.
- (* Balanced tree: both child indices fit the next level. *)
  have hp : (2 ^ Z.of_nat (Nat.sub 255 z) =
      2 * 2 ^ Z.of_nat (Nat.sub 255 z.+1))%Z.
    rewrite hzdepth Znat.Nat2Z.inj_succ Z.pow_succ_r //.
    exact: Znat.Nat2Z.is_nonneg.
  rewrite /shrincs_fxmss_spec_on_shape hp.
  split; repeat split; lia.
- (* Unbalanced tree: an internal node is on the left spine. *)
  have hi0 : i = 0%Z.
    case: hbound => [hi0 | [hi1 _]]; first exact hi0.
    by rewrite hi1 /= in hside.
  rewrite /shrincs_fxmss_spec_on_shape hi0.
  split; repeat split; auto; lia.
Qed.

Lemma shrincs_fxmss_spec_depth_bound b d :
  shrincs_fxmss_spec_legal_shape b d -> (d < 256)%coq_nat.
Proof. by case: b => hd; unfold shrincs_fxmss_spec_legal_shape in hd; lia. Qed.

Lemma shrincs_fxmss_spec_node_at_step fuel sk pk b d z i :
  (z < 256)%coq_nat -> (d < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  fxmss_node_at fuel.+1 sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) =
  if shrincs_fxmss_spec_is_leaf b d z i then
    Some (wots_c_pubkey_gen sk pk (uint U8 z) (wrepr U64 i) b (uint U8 d))
  else if (if b then 255 - z < d else Z.eqb i 0) then
    if (0 < z) && Z.ltb (2*i+1) (2^64) then
      if fxmss_node_at fuel sk (wrepr U64 (2*i)) (uint U8 (z-1)) pk b (uint U8 d)
        is Some l then
        if fxmss_node_at fuel sk (wrepr U64 (2*i+1)) (uint U8 (z-1)) pk b (uint U8 d)
          is Some r then
          Some (H pk (FxmssTree (uint U8 z) (wrepr U64 i)) [tuple of l ++ r])
        else None
      else None
    else None
  else None.
Proof.
move=> hz hd hi.
cbn [fxmss_node_at].
rewrite !shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT /shrincs_fxmss_spec_is_leaf.
rewrite !shrincs_fxmss_spec_word_eq wunsigned_repr_small //.
Qed.

Lemma shrincs_fxmss_spec_internal_test b d z i :
  shrincs_fxmss_spec_on_shape b d z i -> shrincs_fxmss_spec_is_leaf b d z i = false ->
  (if b then 255 - z < d else Z.eqb i 0) = true.
Proof.
move=> [[hz hdepth] [hi hbound]].
rewrite /shrincs_fxmss_spec_is_leaf.
move/orb_false_iff=> [hne hside].
case: b hbound hside => hbound hside.
- (* Balanced tree: a nonleaf is strictly above the requested depth. *)
  apply/ltP.
  rewrite subnE.
  have hned : Nat.sub 255 z <> d.
    move=> he.
    by rewrite subnE he eqxx in hne.
  lia.
- case: hbound => [-> | [hi1 _]]; first reflexivity.
  by rewrite hi1 /= in hside.
Qed.

Lemma shrincs_fxmss_spec_node_at_total sk pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  exists node,
    fxmss_node_at z.+1 sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some node.
Proof.
elim: z i => [|z ih] i hd hs.
- (* Height zero is a leaf, so evaluation returns its WOTS public key. *)
  have hzero : (0 < 256)%coq_nat by lia.
  have hi := shrincs_fxmss_spec_index_bound hd hs.
  have hdf := shrincs_fxmss_spec_depth_bound hd.
  rewrite shrincs_fxmss_spec_node_at_step //.
  have hleaf : shrincs_fxmss_spec_is_leaf b d 0 i = true.
    have [[_ hdepth] _] := hs.
    have he : d = 255 by destruct b; unfold shrincs_fxmss_spec_legal_shape in hd; lia.
    by rewrite /shrincs_fxmss_spec_is_leaf he eqxx.
  rewrite hleaf.
  eexists; reflexivity.
- have hi := shrincs_fxmss_spec_index_bound hd hs.
  have hdf := shrincs_fxmss_spec_depth_bound hd.
  have hz : (z.+1 < 256)%coq_nat by have [[hheight _] _] := hs; lia.
  rewrite shrincs_fxmss_spec_node_at_step //.
  case he: (shrincs_fxmss_spec_is_leaf b d z.+1 i).
  + eexists; reflexivity.
  + (* Internal node: both recursive children evaluate successfully. *)
    have [hl hr] := shrincs_fxmss_spec_on_shape_children hs he.
    have [l hel] := ih (2*i)%Z hd hl.
    have [r her] := ih (2*i+1)%Z hd hr.
    have hir := shrincs_fxmss_spec_index_bound hd hr.
    have htest : Z.ltb (2*i+1) (2^64) = true by apply Z.ltb_lt; exact hir.2.
    rewrite (shrincs_fxmss_spec_internal_test hs he) htest ltn0Sn subn1 hel her.
    eexists; reflexivity.
Qed.

Lemma shrincs_fxmss_spec_node_total sk pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  exists node,
    fxmss_node sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some node.
Proof.
move=> hd hs.
have hz : (z < 256)%coq_nat by have [[hheight _] _] := hs; lia.
rewrite /fxmss_node shrincs_fxmss_spec_uint8_nat //.
exact: shrincs_fxmss_spec_node_at_total hd hs.
Qed.

Lemma shrincs_fxmss_spec_on_shape_parent b d z i :
  shrincs_fxmss_spec_on_shape b d z i -> (z < 255)%coq_nat ->
  shrincs_fxmss_spec_on_shape b d z.+1 (i/2)%Z /\
  shrincs_fxmss_spec_is_leaf b d z.+1 (i/2)%Z = false.
Proof.
move=> [[hz hdepth] [hi hbound]] hlt.
have hdiff : Nat.sub 255 z = S (Nat.sub 255 z.+1) by lia.
have hneq : (255 - z.+1 == d) = false.
  apply/negbTE/negP=> /eqP he.
  rewrite subnE in he.
  lia.
case: b hbound => hbound.
- have hpos : (0 < 2 ^ Z.of_nat (Nat.sub 255 z.+1))%Z.
    apply Z.pow_pos_nonneg; lia.
  have hip : (i/2 < 2 ^ Z.of_nat (Nat.sub 255 z.+1))%Z.
    apply Z.div_lt_upper_bound; first lia.
    rewrite hdiff Znat.Nat2Z.inj_succ Z.pow_succ_r in hbound;
      first exact: Znat.Nat2Z.is_nonneg.
    exact hbound.
  split.
  + rewrite /shrincs_fxmss_spec_on_shape.
    repeat split; try lia.
    apply Z.div_pos; lia.
  + by rewrite /shrincs_fxmss_spec_is_leaf hneq.
- have hid : (i/2 = 0)%Z by case: hbound => [-> | [-> _]].
  rewrite hid.
  split.
  + rewrite /shrincs_fxmss_spec_on_shape.
    repeat split; auto; lia.
  + by rewrite /shrincs_fxmss_spec_is_leaf hneq.
Qed.

Lemma shrincs_fxmss_spec_xor_one i : (0 <= i)%Z ->
  Z.lxor i 1 =
    if Z.eqb (i mod 2) 1 then (2*(i/2))%Z else (2*(i/2)+1)%Z.
Proof.
move=> hi.
rewrite -Z.div2_div -Zdiv.Zodd_mod.
case: i hi => [|[p|p|]|p] hi; try reflexivity; try lia.
Qed.

Lemma shrincs_fxmss_spec_on_shape_sibling b d z i :
  shrincs_fxmss_spec_on_shape b d z i -> (z < 255)%coq_nat ->
  shrincs_fxmss_spec_on_shape b d z (Z.lxor i 1).
Proof.
move=> hs hz.
have [hp hl] := shrincs_fxmss_spec_on_shape_parent hs hz.
have [hleft hright] := shrincs_fxmss_spec_on_shape_children hp hl.
rewrite (shrincs_fxmss_spec_xor_one hs.2.1).
by case: Z.eqb.
Qed.

Lemma shrincs_fxmss_spec_node_internal sk pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z.+1 i ->
  shrincs_fxmss_spec_is_leaf b d z.+1 i = false ->
  fxmss_node sk (wrepr U64 i) (uint U8 z.+1) pk b (uint U8 d) =
    if fxmss_node sk (wrepr U64 (2*i)) (uint U8 z) pk b (uint U8 d) is Some l then
      if fxmss_node sk (wrepr U64 (2*i+1)) (uint U8 z) pk b (uint U8 d) is Some r then
        Some (H pk (FxmssTree (uint U8 z.+1) (wrepr U64 i)) [tuple of l ++ r])
      else None
    else None.
Proof.
move=> hd hs hl.
have [hleft hright] := shrincs_fxmss_spec_on_shape_children hs hl.
have hi := shrincs_fxmss_spec_index_bound hd hs.
have hir := shrincs_fxmss_spec_index_bound hd hright.
have hdf := shrincs_fxmss_spec_depth_bound hd.
have hz : (z < 256)%coq_nat by have [[hheight _] _] := hs; lia.
have hzs : (z.+1 < 256)%coq_nat by have [[hheight _] _] := hs; lia.
have htest : Z.ltb (2*i+1) (2^64) = true by apply Z.ltb_lt; exact hir.2.
rewrite /fxmss_node !shrincs_fxmss_spec_uint8_nat // shrincs_fxmss_spec_node_at_step
  //.
by rewrite hl (shrincs_fxmss_spec_internal_test hs hl) htest ltn0Sn subn1.
Qed.

Lemma shrincs_fxmss_spec_parent_node sk pk b d z i node sibling :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  (z < 255)%coq_nat ->
  fxmss_node sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some node ->
  fxmss_node sk (wrepr U64 (Z.lxor i 1)) (uint U8 z) pk b (uint U8 d) = Some sibling ->
  fxmss_node sk (wrepr U64 (i/2)) (uint U8 z.+1) pk b (uint U8 d) =
    Some (if Z.eqb (i mod 2) 1 then
      H pk (FxmssTree (uint U8 z.+1) (wrepr U64 (i/2))) [tuple of sibling ++ node]
    else H pk (FxmssTree (uint U8 z.+1) (wrepr U64 (i/2))) [tuple of node ++ sibling]).
Proof.
move=> hd hs hz hn hsn.
have [hp hl] := shrincs_fxmss_spec_on_shape_parent hs hz.
rewrite (shrincs_fxmss_spec_node_internal sk pk hd hp hl).
have hi : (0 <= i)%Z := hs.2.1.
rewrite (shrincs_fxmss_spec_xor_one hi) in hsn.
have hsum := Z.div_mod i 2 ltac:(lia).
have hmod := Z.mod_pos_bound i 2 ltac:(lia).
case ho: (Z.eqb (i mod 2) 1) in hsn *.
- move/Z.eqb_eq: ho => ho.
  have he : (2*(i/2)+1 = i)%Z by lia.
  by rewrite he hn hsn.
- move/Z.eqb_neq: ho => ho.
  have he : (2*(i/2) = i)%Z by lia.
  rewrite he in hsn.
  by rewrite he hn hsn.
Qed.
