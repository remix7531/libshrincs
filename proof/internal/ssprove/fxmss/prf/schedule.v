(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.schedule

    The legal leaf schedule fixes the chain-start inputs and connects sampled keys
    to tree evaluation. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games model.nodes prf.inputs scheme tree.nodes model.auth leaf.paths.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF schedule *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_prf_uint64_inj i j :
  i < 2 ^ 64 -> j < 2 ^ 64 -> uint U64 i = uint U64 j -> i = j.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt hi /ltP /Znat.Nat2Z.inj_lt hj
  /(congr1 (@wunsigned U64)).
rewrite shape.Z_of_nat_expn2 in hi; rewrite shape.Z_of_nat_expn2 in hj.
rewrite /uint !wunsigned_repr_small;
  try by split; [exact: Znat.Nat2Z.is_nonneg|].
exact: Znat.Nat2Z.inj.
Qed.

Lemma shrincs_fxmss_prf_uint64_nat i :
  i < 2 ^ 64 -> Z.to_nat (wunsigned (uint U64 i)) = i.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt hi.
rewrite shape.Z_of_nat_expn2 in hi.
rewrite /uint wunsigned_repr_small ?Znat.Nat2Z.id //.
by split; [exact: Znat.Nat2Z.is_nonneg | exact: hi].
Qed.

Definition shrincs_fxmss_prf_leaf_ordinal b d (a : shrincs_fxmss_coord) :=
  if b then Z.to_nat (wunsigned a.2)
  else if a.2 == uint U64 0 then d
       else 254 - Z.to_nat (wunsigned a.1).

Lemma shrincs_fxmss_prf_select_leaf_cancel b d :
  ocancel (shrincs_fxmss_select_leaf b d) (shrincs_fxmss_prf_leaf_ordinal b d).
Proof.
move=> q.
rewrite /shrincs_fxmss_select_leaf.
case: ifP => [/andP [hl hq]|]; last by [].
case: b hl hq => hl hq /=.
- rewrite /shrincs_fxmss_prf_leaf_ordinal /=.
apply: shrincs_fxmss_prf_uint64_nat.
exact: (leq_trans hq (shrincs_fxmss_leaf_count_bound true d hl)).
- case: eqP => [->|hne]; first by rewrite /shrincs_fxmss_prf_leaf_ordinal /= eqxx.
rewrite /shrincs_fxmss_prf_leaf_ordinal /=.
have /leP hd := shrincs_fxmss_legal_depth false d hl.
move/ltP: hq => hq.
change (q < d.+1)%coq_nat in hq.
have hq254 : (q <= 254)%coq_nat by lia.
have hz : (uint U64 1 == uint U64 0) = false by reflexivity.
have hh : (254 - q < 256)%coq_nat by rewrite subnE; lia.
change ((if uint U64 1 == uint U64 0 then d else 254 - Z.to_nat (wunsigned (uint U8 (254-q)))) = q).
rewrite hz (@shrincs_fxmss_spec_uint8_nat (254-q) hh).
rewrite !subnE.
lia.
Qed.

Lemma shrincs_fxmss_prf_schedule_uniq sp : uniq (shrincs_fxmss_schedule sp).
Proof.
rewrite /shrincs_fxmss_schedule.
apply: (pmap_uniq (shrincs_fxmss_prf_select_leaf_cancel sp.1 sp.2)).
exact: iota_uniq.
Qed.

Lemma shrincs_fxmss_prf_schedule_mem b d q a :
  shrincs_fxmss_select_leaf b d q = Some a -> a \in shrincs_fxmss_schedule (b,d).
Proof.
move=> hs.
have [hl hq] := shrincs_fxmss_select_leaf_some b d q a hs.
rewrite /shrincs_fxmss_schedule mem_pmap.
apply/mapP.
exists q; last by symmetry.
by rewrite mem_iota add0n leq0n.
Qed.

Definition shrincs_fxmss_prf_queries pp b d (as_ : seq shrincs_fxmss_coord) :=
  [seq shrincs_fxmss_prf_input pp a b d j | a <- as_, j <- iota 0 wots_c_chain_count].

Lemma shrincs_fxmss_prf_queries_uniq pp b d as_ :
  uniq as_ -> uniq (shrincs_fxmss_prf_queries pp b d as_).
Proof.
move=> hu.
rewrite /shrincs_fxmss_prf_queries.
apply: allpairs_uniq; [exact: hu | exact: iota_uniq | ].
move=> [a j] [a' j'] h0 h1 he.
case/allpairsP: h0 => [[a0 j0] /= [ha hj [he0 he1]]].
case/allpairsP: h1 => [[a1 j1] /= [ha' hj' [he2 he3]]].
subst a0 j0 a1 j1.
change (is_true (j \in iota 0 wots_c_chain_count)) in hj.
rewrite mem_iota add0n leq0n /= in hj.
change (is_true (j' \in iota 0 wots_c_chain_count)) in hj'.
rewrite mem_iota add0n leq0n /= in hj'.
exact: (congr1 snd (shrincs_fxmss_prf_input_inj pp pp a a' b d j j' hj hj' he)).
Qed.

Lemma shrincs_fxmss_prf_queries_no_pin pp pp' b d as_ :
  shrincs_fxmss_prf_pin pp' \notin shrincs_fxmss_prf_queries pp b d as_.
Proof.
apply/negP=> /allpairsP [[a j] [ha hj he]].
apply: (shrincs_fxmss_prf_pin_neq pp pp' a b d j).
by symmetry.
Qed.

Lemma shrincs_fxmss_prf_queries_size pp b d as_ :
  size (shrincs_fxmss_prf_queries pp b d as_) = size as_ * wots_c_chain_count.
Proof. by rewrite /shrincs_fxmss_prf_queries size_allpairs size_iota. Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF keys *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_prf_leaf_scheduled b d z i :
  shrincs_fxmss_structure_legal b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i ->
  (uint U8 z, wrepr U64 i) \in shrincs_fxmss_schedule (b,d).
Proof.
move=> hl hs hf.
have he : Z.of_nat (Z.to_nat i) = i by apply Znat.Z2Nat.id; exact: hs.2.1.
have hm : (uint U8 z, uint U64 (Z.to_nat i)) \in shrincs_fxmss_schedule (b,d).
{ apply: leaf_schedule_complete hl _ _; by rewrite he. }
by rewrite /uint he in hm.
Qed.

Lemma shrincs_fxmss_prf_node_at_congr P keys0 keys1 pp b d z i :
  shrincs_fxmss_structure_legal b d -> shrincs_fxmss_spec_on_shape b d z i ->
  (forall a, a \in shrincs_fxmss_schedule (b,d) -> keys0 a = keys1 a) ->
  shrincs_fxmss_node_at P z.+1 keys0 (wrepr U64 i) (uint U8 z) pp b (uint U8 d) =
  shrincs_fxmss_node_at P z.+1 keys1 (wrepr U64 i) (uint U8 z) pp b (uint U8 d).
Proof.
move=> hl.
have hd : shrincs_fxmss_spec_legal_shape b d.
{
  move: hl.
  rewrite /shrincs_fxmss_structure_legal /shrincs_fxmss_spec_legal_shape.
  case: b => /andP [/ltP h0 /leP h1]; by split.
}
move: i.
elim: z => [|z ih] i hs hk.
-
  have hz : (0 < 256)%coq_nat by lia.
  have hi := shrincs_fxmss_spec_index_bound hd hs.
  have hdf := shrincs_fxmss_spec_depth_bound hd.
  rewrite !shrincs_fxmss_node_at_step //.
  case he: (shrincs_fxmss_spec_is_leaf b d 0 i).
  + by rewrite (hk _ (@shrincs_fxmss_prf_leaf_scheduled b d 0 i hl hs he)).
  + by case: (if b then 255 - 0 < d else Z.eqb i 0).
-
  have hi := shrincs_fxmss_spec_index_bound hd hs.
  have hdf := shrincs_fxmss_spec_depth_bound hd.
  have hz : (z.+1 < 256)%coq_nat by have [[hh _] _] := hs; lia.
  rewrite (@shrincs_fxmss_node_at_step P z.+1 keys0 pp b d z.+1 i hz hdf hi)
    (@shrincs_fxmss_node_at_step P z.+1 keys1 pp b d z.+1 i hz hdf hi).
  case he: (shrincs_fxmss_spec_is_leaf b d z.+1 i).
  + by rewrite (hk _ (@shrincs_fxmss_prf_leaf_scheduled b d z.+1 i hl hs he)).
  +
    have [hlc hrc] := shrincs_fxmss_spec_on_shape_children hs he.
    rewrite (shrincs_fxmss_spec_internal_test hs he) ltn0Sn subn1.
    rewrite (ih (2*i)%Z hlc hk) (ih (2*i+1)%Z hrc hk).
    reflexivity.
Qed.

Lemma shrincs_fxmss_prf_node_congr P keys0 keys1 pp b d z i :
  shrincs_fxmss_structure_legal b d -> shrincs_fxmss_spec_on_shape b d z i ->
  (forall a, a \in shrincs_fxmss_schedule (b,d) -> keys0 a = keys1 a) ->
  shrincs_fxmss_node P keys0 (wrepr U64 i) (uint U8 z) pp b (uint U8 d) =
  shrincs_fxmss_node P keys1 (wrepr U64 i) (uint U8 z) pp b (uint U8 d).
Proof.
move=> hl hs hk.
have hz : (z < 256)%coq_nat by have [[hh _] _] := hs; lia.
rewrite /shrincs_fxmss_node !shrincs_fxmss_spec_uint8_nat //.
exact: shrincs_fxmss_prf_node_at_congr hl hs hk.
Qed.

Lemma shrincs_fxmss_prf_sign_congr P keys0 keys1 pp b d z i md :
  shrincs_fxmss_structure_legal b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i ->
  (forall a, a \in shrincs_fxmss_schedule (b,d) -> keys0 a = keys1 a) ->
  shrincs_fxmss_sign P md keys0 (wrepr U64 i) (uint U8 z) pp b (uint U8 d) =
  shrincs_fxmss_sign P md keys1 (wrepr U64 i) (uint U8 z) pp b (uint U8 d).
Proof.
move=> hl hs hf hk.
have hd : shrincs_fxmss_spec_legal_shape b d.
{
  move: hl.
  rewrite /shrincs_fxmss_structure_legal /shrincs_fxmss_spec_legal_shape.
  clear hs hf hk.
  case: b => /andP [/ltP h0 /leP h1]; by split.
}
have hz : (z < 256)%coq_nat by have [[hh _] _] := hs; lia.
have hi := shrincs_fxmss_spec_index_bound hd hs.
have hdf := shrincs_fxmss_spec_depth_bound hd.
rewrite /shrincs_fxmss_sign !shrincs_fxmss_spec_uint8_nat // wunsigned_repr_small //.
rewrite (hk _ (@shrincs_fxmss_prf_leaf_scheduled b d z i hl hs hf)).
case: (if b then FXMSS_HEIGHT - z == d else
  ((wrepr U64 i == uint U64 1) || (FXMSS_HEIGHT - z == d))%B); last reflexivity.
case: (scheme.shrincs_fxmss_leaf_sign P (uint U8 z, wrepr U64 i) b (uint U8 d) pp
  (keys1 (uint U8 z, wrepr U64 i)) md) => [sig|]; last reflexivity.
have hall : all (fun j => j < 255 - z) (range 0 (FXMSS_HEIGHT - z)).
{
  apply/allP=> j.
  rewrite /range /FXMSS_HEIGHT subn0 mem_iota add0n leq0n /=.
  by [].
}
elim: (range 0 (FXMSS_HEIGHT - z)) (Some (tval sig)) hall => [|j js ih] acc;
  first reflexivity.
move/andP=> [hj hjs].
cbn [foldl].
have hn := @shrincs_fxmss_prf_node_congr P keys0 keys1 pp b d (z+j)
  (Z.lxor (shrincs_fxmss_spec_ancestor i j) 1) hl (shrincs_fxmss_spec_sibling_shape hs
    hj) hk.
rewrite hn.
exact: ih hjs.
Qed.

Lemma shrincs_fxmss_prf_root_congr P keys0 keys1 pp b d :
  shrincs_fxmss_structure_legal b d ->
  (forall a, a \in shrincs_fxmss_schedule (b,d) -> keys0 a = keys1 a) ->
  shrincs_fxmss_node P keys0 (uint U64 0) (uint U8 255) pp b (uint U8 d) =
  shrincs_fxmss_node P keys1 (uint U64 0) (uint U8 255) pp b (uint U8 d).
Proof.
move=> hl hk.
apply: shrincs_fxmss_prf_node_congr hl _ hk.
rewrite /shrincs_fxmss_spec_on_shape.
repeat split; try lia.
by case: b; [change (0 < 1)%Z; lia | left].
Qed.

(** Signing at a selected leaf only observes scheduled keys. *)
Lemma shrincs_fxmss_prf_sign_selected_congr P keys0 keys1 pp b d q a md :
  shrincs_fxmss_select_leaf b d q = Some a ->
  (forall x, x \in shrincs_fxmss_schedule (b,d) -> keys0 x = keys1 x) ->
  shrincs_fxmss_sign P md keys0 a.2 a.1 pp b (uint U8 d) =
  shrincs_fxmss_sign P md keys1 a.2 a.1 pp b (uint U8 d).
Proof.
move=> he hk.
have [hl hq] := shrincs_fxmss_select_leaf_some _ _ _ _ he.
have hd := shrincs_fxmss_legal_depth _ _ hl.
have hp := shrincs_fxmss_legal_positive _ _ hl.
rewrite (leaf_select_eq (b,d) q hl hq) in he.
case: he => <-.
rewrite /leaf_coord_at /=.
case: b hl hq hk => hl hq hk.
-
  apply: shrincs_fxmss_prf_sign_congr hl _ _ hk.
  +
    rewrite /shrincs_fxmss_spec_on_shape.
    have hdd : (d <= 255)%coq_nat by exact/ leP.
    have he : (Nat.sub 255 (255-d) = d) by rewrite subnE; lia.
    rewrite he.
    split; first (rewrite subnE; split; lia).
    split; first exact: Znat.Nat2Z.is_nonneg.
    move/ltP/Znat.Nat2Z.inj_lt: hq.
    by rewrite /shrincs_fxmss_leaf_count shape.Z_of_nat_expn2.
  +
    rewrite /shrincs_fxmss_spec_is_leaf.
    have he : 255 - (255-d) = d by move/leP: hd; rewrite !subnE; lia.
    by rewrite he eqxx.
-
  case: ifP => hqd.
  +
    apply: shrincs_fxmss_prf_sign_congr hl _ _ hk.
    * rewrite /shrincs_fxmss_spec_on_shape.
      move/leP: hd => hd.
      rewrite !subnE; repeat split; try lia.
    * rewrite /shrincs_fxmss_spec_is_leaf.
      have he : 255 - (255-d) = d by move/leP: hd; rewrite !subnE; lia.
      by rewrite he eqxx.
  +
    have hqd' : q < d.
    { by move: hq; rewrite /shrincs_fxmss_leaf_count ltnS => hq;
        rewrite ltn_neqAle hqd hq. }
    apply: shrincs_fxmss_prf_sign_congr hl _ _ hk.
    * (* An earlier unbalanced-tree counter selects a legal right leaf. *)
      rewrite /shrincs_fxmss_spec_on_shape.
      move/ltP: hqd' => hqd'.
      move/leP: hd => hd.
      rewrite !subnE.
      repeat split; try lia.
    * by rewrite /shrincs_fxmss_spec_is_leaf /= orbT.
Qed.
