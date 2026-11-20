(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.nodes

    The operational FXMSS tree remains total with arbitrary per-coordinate chain
    starts. The operational signer appends the honest authentication siblings for
    arbitrary coordinate keys. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import params scheme model.nodes model.auth.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Bool Lia.
From Shrincs.internal.ssprove Require Import shape.

(* ------------------------------------------------------------------ *)
(** ** Tree nodes *)

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Section TreeNodes.
Context (P : shrincs_fxmss_params).

Lemma shrincs_fxmss_node_at_step fuel keys pk b d z i :
  (z < 256)%coq_nat -> (d < 256)%coq_nat -> (0 <= i < 2^64)%Z ->
  shrincs_fxmss_node_at P fuel.+1 keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d) =
  if shrincs_fxmss_spec_is_leaf b d z i then
    Some (shrincs_fxmss_leaf_pubkey P (uint U8 z, wrepr U64 i) b (uint U8 d)
      pk (keys (uint U8 z, wrepr U64 i)))
  else if (if b then 255 - z < d else Z.eqb i 0) then
    if (0 < z) && Z.ltb (2*i+1) (2^64) then
      if shrincs_fxmss_node_at P fuel keys (wrepr U64 (2*i)) (uint U8 (z-1)) pk b (uint U8 d)
        is Some l then
        if shrincs_fxmss_node_at P fuel keys (wrepr U64 (2*i+1)) (uint U8 (z-1)) pk b (uint U8 d)
          is Some r then
          Some (shrincs_fxmss_hash_node P pk (uint U8 z, wrepr U64 i) l r)
        else None
      else None
    else None
  else None.
Proof.
move=> hz hd hi.
cbn [shrincs_fxmss_node_at].
rewrite !shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT /shrincs_fxmss_spec_is_leaf.
rewrite !shrincs_fxmss_spec_word_eq wunsigned_repr_small //.
Qed.

Lemma shrincs_fxmss_node_at_total keys pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  exists node,
    shrincs_fxmss_node_at P z.+1 keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some node.
Proof.
elim: z i => [|z ih] i hd hs.
- (* A legal node at height zero is a leaf. *)
  have hzero : (0 < 256)%coq_nat by lia.
  have hi := shrincs_fxmss_spec_index_bound hd hs.
  have hdf := shrincs_fxmss_spec_depth_bound hd.
  rewrite shrincs_fxmss_node_at_step //.
  have hleaf : shrincs_fxmss_spec_is_leaf b d 0 i = true.
    have [[_ hdepth] _] := hs.
    have he : d = 255 by destruct b; unfold shrincs_fxmss_spec_legal_shape in hd; lia.
    by rewrite /shrincs_fxmss_spec_is_leaf he eqxx.
  rewrite hleaf.
  eexists; reflexivity.
- have hi := shrincs_fxmss_spec_index_bound hd hs.
  have hdf := shrincs_fxmss_spec_depth_bound hd.
  have hz : (z.+1 < 256)%coq_nat by have [[hheight _] _] := hs; lia.
  rewrite shrincs_fxmss_node_at_step //.
  case he: (shrincs_fxmss_spec_is_leaf b d z.+1 i).
  + eexists; reflexivity.
  + (* Both children of an internal node evaluate successfully. *)
    have [hl hr] := shrincs_fxmss_spec_on_shape_children hs he.
    have [l hel] := ih (2*i)%Z hd hl.
    have [r her] := ih (2*i+1)%Z hd hr.
    have hir := shrincs_fxmss_spec_index_bound hd hr.
    have htest : Z.ltb (2*i+1) (2^64) = true by apply Z.ltb_lt; exact hir.2.
    rewrite (shrincs_fxmss_spec_internal_test hs he) htest ltn0Sn subn1 hel her.
    eexists; reflexivity.
Qed.

Lemma shrincs_fxmss_node_total keys pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  exists node,
    shrincs_fxmss_node P keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some node.
Proof.
move=> hd hs.
have hz : (z < 256)%coq_nat by have [[hheight _] _] := hs; lia.
rewrite /shrincs_fxmss_node shrincs_fxmss_spec_uint8_nat //.
exact: shrincs_fxmss_node_at_total hd hs.
Qed.

Lemma shrincs_fxmss_node_internal keys pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z.+1 i ->
  shrincs_fxmss_spec_is_leaf b d z.+1 i = false ->
  shrincs_fxmss_node P keys (wrepr U64 i) (uint U8 z.+1) pk b (uint U8 d) =
    if shrincs_fxmss_node P keys (wrepr U64 (2*i)) (uint U8 z) pk b (uint U8 d) is Some l then
      if shrincs_fxmss_node P keys (wrepr U64 (2*i+1)) (uint U8 z) pk b (uint U8 d) is Some r then
        Some (shrincs_fxmss_hash_node P pk (uint U8 z.+1, wrepr U64 i) l r)
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
rewrite /shrincs_fxmss_node !shrincs_fxmss_spec_uint8_nat //
  shrincs_fxmss_node_at_step //.
by rewrite hl (shrincs_fxmss_spec_internal_test hs hl) htest ltn0Sn subn1.
Qed.

Lemma shrincs_fxmss_parent_node keys pk b d z i node sibling :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  (z < 255)%coq_nat ->
  shrincs_fxmss_node P keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d) = Some node ->
  shrincs_fxmss_node P keys (wrepr U64 (Z.lxor i 1)) (uint U8 z) pk b (uint U8 d) = Some sibling ->
  shrincs_fxmss_node P keys (wrepr U64 (i/2)) (uint U8 z.+1) pk b (uint U8 d) =
    Some (if Z.eqb (i mod 2) 1 then
      shrincs_fxmss_hash_node P pk (uint U8 z.+1, wrepr U64 (i/2)) sibling node
    else shrincs_fxmss_hash_node P pk (uint U8 z.+1, wrepr U64 (i/2)) node sibling).
Proof.
move=> hd hs hz hn hsn.
have [hp hl] := shrincs_fxmss_spec_on_shape_parent hs hz.
rewrite (shrincs_fxmss_node_internal keys pk hd hp hl).
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

End TreeNodes.

(* ------------------------------------------------------------------ *)
(** ** Tree auth *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Section TreeAuth.
Context (P : shrincs_fxmss_params).

Definition shrincs_fxmss_honest_node keys pk b d z i : Bytes 16 :=
  odflt (zeros 16) (shrincs_fxmss_node P keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d)).

Lemma shrincs_fxmss_honest_node_eq keys pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_node P keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d) =
    Some (shrincs_fxmss_honest_node keys pk b d z i).
Proof.
move=> hd hs.
have [node hn] := shrincs_fxmss_node_total P keys pk hd hs.
by rewrite /shrincs_fxmss_honest_node hn.
Qed.

Definition shrincs_fxmss_honest_sibling keys pk b d z i j :=
  shrincs_fxmss_honest_node keys pk b d (z + j) (Z.lxor (shrincs_fxmss_spec_ancestor i
    j) 1).

Definition shrincs_fxmss_honest_auth keys pk b d z i :=
  [seq shrincs_fxmss_honest_sibling keys pk b d z i j | j <- range 0 (255 - z)].

Lemma shrincs_fxmss_honest_auth_size keys pk b d z i :
  size (shrincs_fxmss_honest_auth keys pk b d z i) = 255 - z.
Proof. by rewrite /shrincs_fxmss_honest_auth size_map /range size_iota subn0. Qed.

Lemma shrincs_fxmss_honest_auth_nth keys pk b d z i j :
  j < 255 - z ->
  nth (zeros 16) (shrincs_fxmss_honest_auth keys pk b d z i) j =
    shrincs_fxmss_honest_sibling keys pk b d z i j.
Proof.
move=> hj.
rewrite /shrincs_fxmss_honest_auth /range subn0 (nth_map 0) ?size_iota //.
by rewrite nth_iota // add0n.
Qed.

Definition shrincs_fxmss_recover_step pk z i (auth : seq UInt8) (node : Bytes 16) j :=
  let parent := (uint U8 (z + j + 1),
    wrepr U64 (shrincs_fxmss_spec_ancestor i (j + 1))) in
  let sibling := slice auth (j * 16) 16 in
  if Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1 then
    shrincs_fxmss_hash_node P pk parent sibling node
  else shrincs_fxmss_hash_node P pk parent node sibling.

Lemma shrincs_fxmss_recover_honest_step keys pk b d z i j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i -> j < 255 -
    z ->
  shrincs_fxmss_recover_step pk z i
    (flatten [seq tval n | n <- shrincs_fxmss_honest_auth keys pk b d z i])
    (shrincs_fxmss_honest_node keys pk b d (z+j) (shrincs_fxmss_spec_ancestor i j)) j =
  shrincs_fxmss_honest_node keys pk b d (z+j.+1) (shrincs_fxmss_spec_ancestor i j.+1).
Proof.
move=> hd hs hj.
have hlt : (z+j < 255)%coq_nat.
  move/ltP: hj; rewrite subnE addnE; lia.
have hc := shrincs_fxmss_spec_on_shape_ancestor hs (Nat.lt_le_incl _ _ hlt).
have hsi := shrincs_fxmss_spec_sibling_shape hs hj.
have [hp _] := shrincs_fxmss_spec_on_shape_parent hc hlt.
have hn := shrincs_fxmss_honest_node_eq keys pk hd hc.
have hsn := shrincs_fxmss_honest_node_eq keys pk hd hsi.
have he := shrincs_fxmss_parent_node hd hc hlt hn hsn.
rewrite (shrincs_fxmss_honest_node_eq keys pk hd hp) in he.
rewrite /shrincs_fxmss_recover_step slice_flatten_rows (@shrincs_fxmss_honest_auth_nth
  keys pk b d z i j hj).
have ha : (uint U8 (z+j+1),
    wrepr U64 (shrincs_fxmss_spec_ancestor i (j+1))) =
    (uint U8 (z+j).+1, wrepr U64 (shrincs_fxmss_spec_ancestor i j / 2)).
  by rewrite !addn1 shrincs_fxmss_spec_ancestor_succ.
rewrite ha.
have hnxt : shrincs_fxmss_honest_node keys pk b d (z+j.+1)
  (shrincs_fxmss_spec_ancestor i j.+1) =
    shrincs_fxmss_honest_node keys pk b d (z+j).+1 (shrincs_fxmss_spec_ancestor i j /
      2).
  by rewrite addnS shrincs_fxmss_spec_ancestor_succ.
rewrite hnxt.
by case: he.
Qed.

Lemma shrincs_fxmss_recover_honest_fold keys pk b d z i count j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  z+j+count = 255 ->
  foldl (shrincs_fxmss_recover_step pk z i
      (flatten [seq tval n | n <- shrincs_fxmss_honest_auth keys pk b d z i]))
    (shrincs_fxmss_honest_node keys pk b d (z+j) (shrincs_fxmss_spec_ancestor i j))
      (iota j count) =
  shrincs_fxmss_honest_node keys pk b d 255 0.
Proof.
move=> hd hs.
elim: count j => [|count ih] j hcount.
- rewrite addn0 in hcount.
  have hc := shrincs_fxmss_spec_on_shape_ancestor hs (Nat.eq_le_incl _ _ hcount).
  rewrite hcount in hc *.
  by rewrite (shrincs_fxmss_spec_on_shape_root hc).
- (* Each remaining authentication step reaches the next ancestor. *)
  have hj : j < 255 - z.
    apply/ltP.
    rewrite addnE in hcount.
    rewrite subnE.
    lia.
  cbn [iota foldl].
  rewrite (shrincs_fxmss_recover_honest_step keys pk hd hs hj).
  apply ih.
  rewrite !addnE in hcount *.
  lia.
Qed.

Lemma shrincs_fxmss_recover_honest_prefix keys pk b d z i n :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i -> n <= 255
    - z ->
  foldl (shrincs_fxmss_recover_step pk z i
      (flatten [seq tval x | x <- shrincs_fxmss_honest_auth keys pk b d z i]))
    (shrincs_fxmss_honest_node keys pk b d z i) (iota 0 n) =
  shrincs_fxmss_honest_node keys pk b d (z+n) (shrincs_fxmss_spec_ancestor i n).
Proof.
move=> hd hs.
elim: n => [|n ih] hn.
- by rewrite /= addn0 shrincs_fxmss_spec_ancestor_zero.
- rewrite -[n.+1]addn1 iotaD foldl_cat /= add0n ih; first exact: ltnW hn.
  rewrite addn1.
  exact: (@shrincs_fxmss_recover_honest_step keys pk b d z i n hd hs hn).
Qed.

End TreeAuth.

(* ------------------------------------------------------------------ *)
(** ** Tree sign *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Section TreeSign.
Context (P : shrincs_fxmss_params).

Definition shrincs_fxmss_append_sibling keys pk b d z i (signature : option (seq UInt8))
  j :=
  if signature is Some sig then
    let sibling_index := Z.lxor (shrincs_fxmss_spec_ancestor i j) 1 in
    let sibling_height := z + j in
    if Z.ltb sibling_index (2^64) && (sibling_height < 256) then
      if shrincs_fxmss_node P keys (wrepr U64 sibling_index) (uint U8 sibling_height) pk b (uint U8 d)
        is Some sibling then Some (sig ++ sibling) else None
    else None
  else None.

Lemma shrincs_fxmss_append_honest keys pk b d z i sig j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i -> j < 255 -
    z ->
  shrincs_fxmss_append_sibling keys pk b d z i (Some sig) j =
    Some (sig ++ shrincs_fxmss_honest_sibling P keys pk b d z i j).
Proof.
move=> hd hs hj.
have hshape := shrincs_fxmss_spec_sibling_shape hs hj.
have hi := shrincs_fxmss_spec_index_bound hd hshape.
have hindex : Z.ltb (Z.lxor (shrincs_fxmss_spec_ancestor i j) 1) (2^64) = true.
  apply Z.ltb_lt; exact hi.2.
have hheight : z + j < 256.
  apply/ltP.
  have [[hz _] _] := hshape.
  lia.
rewrite /shrincs_fxmss_append_sibling hindex hheight.
by rewrite (shrincs_fxmss_honest_node_eq P keys pk hd hshape).
Qed.

Lemma shrincs_fxmss_append_fold keys pk b d z i sig js :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  all (fun j => j < 255 - z) js ->
  foldl (shrincs_fxmss_append_sibling keys pk b d z i) (Some sig) js =
    Some (sig ++ flatten [seq tval (shrincs_fxmss_honest_sibling P keys pk b d z i j) |
      j <- js]).
Proof.
move=> hd hs.
elim: js sig => [|j js ih] sig; first by rewrite /= cats0.
move/andP=> [hj hjs].
cbn [foldl map flatten].
rewrite (shrincs_fxmss_append_honest keys pk sig hd hs hj) (ih _ hjs).
by rewrite catA.
Qed.

Lemma shrincs_fxmss_sign_eq message keys pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i = true ->
  shrincs_fxmss_sign P message keys (wrepr U64 i) (uint U8 z) pk b (uint U8 d) =
    if shrincs_fxmss_leaf_sign P (uint U8 z, wrepr U64 i) b (uint U8 d) pk (keys (uint
      U8 z, wrepr U64 i)) message
      is Some ws then
        Some (ws ++ flatten [seq tval n | n <- shrincs_fxmss_honest_auth P keys pk b d z
          i])
    else None.
Proof.
move=> hd hs hl.
have hi := shrincs_fxmss_spec_index_bound hd hs.
have hz : (z < 256)%coq_nat by have [[hheight _] _] := hs; lia.
have hdf := shrincs_fxmss_spec_depth_bound hd.
have hguard : (if b then 255 - z == d else Z.eqb i 1 || (255 - z == d)) = true.
  move: hl; rewrite /shrincs_fxmss_spec_is_leaf.
  destruct b.
  - by rewrite andFb orbF.
  - by rewrite andTb orbC.
rewrite /shrincs_fxmss_sign !shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT.
rewrite !shrincs_fxmss_spec_word_eq !wunsigned_repr_small // hguard.
case hw: (shrincs_fxmss_leaf_sign _ _ _ _ _ _ _) => [ws|]; last reflexivity.
change (foldl (shrincs_fxmss_append_sibling keys pk b d z i) (Some (tval ws))
    (range 0 (255 - z)) =
    Some (ws ++ flatten [seq tval n | n <- shrincs_fxmss_honest_auth P keys pk b d z
      i])).
have hall : all (fun j => j < 255 - z) (range 0 (255 - z)).
  apply/allP=> j.
  rewrite /range subn0 mem_iota add0n.
  by move/andP=> [_ hj].
rewrite (shrincs_fxmss_append_fold keys pk (tval ws) hd hs hall).
by rewrite /shrincs_fxmss_honest_auth -map_comp.
Qed.

End TreeSign.
