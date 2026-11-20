(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.model.auth

    Honest siblings and the bottom-up path of the literal specification. *)

From mathcomp Require Import boot algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Bool Lia.
From Shrincs Require Import spec.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import model.nodes.

(* Dependent parameters use non-strict implicit inference, which imports do not set. *)
Set Implicit Arguments.
Unset Strict Implicit.

Definition shrincs_fxmss_spec_ancestor (i : Z) (j : nat) := (i / 2 ^ Z.of_nat j)%Z.

Lemma shrincs_fxmss_spec_ancestor_zero i : shrincs_fxmss_spec_ancestor i 0 = i.
Proof. exact: Z.div_1_r. Qed.

Lemma shrincs_fxmss_spec_ancestor_succ i j :
  shrincs_fxmss_spec_ancestor i j.+1 = (shrincs_fxmss_spec_ancestor i j / 2)%Z.
Proof.
rewrite /shrincs_fxmss_spec_ancestor Z.div_div; first by apply Z.pow_nonzero; lia.
- lia.
- rewrite Znat.Nat2Z.inj_succ Z.pow_succ_r; first exact: Znat.Nat2Z.is_nonneg.
  by rewrite Z.mul_comm.
Qed.

Lemma shrincs_fxmss_spec_on_shape_ancestor b d z i j :
  shrincs_fxmss_spec_on_shape b d z i -> (z + j <= 255)%coq_nat ->
  shrincs_fxmss_spec_on_shape b d (z + j) (shrincs_fxmss_spec_ancestor i j).
Proof.
move=> hs.
elim: j => [|j ih] hj.
- by rewrite addn0 shrincs_fxmss_spec_ancestor_zero.
- rewrite addnS shrincs_fxmss_spec_ancestor_succ.
  apply: (shrincs_fxmss_spec_on_shape_parent _ _).1.
  + apply ih.
    rewrite addnE in hj *.
    lia.
  + rewrite addnE in hj *.
    lia.
Qed.

Definition shrincs_fxmss_spec_honest_node sk pk b d z i : Bytes 16 :=
  odflt (zeros 16) (fxmss_node sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d)).

Lemma shrincs_fxmss_spec_honest_node_eq sk pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  fxmss_node sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) =
    Some (shrincs_fxmss_spec_honest_node sk pk b d z i).
Proof.
move=> hd hs.
have [node hn] := shrincs_fxmss_spec_node_total sk pk hd hs.
by rewrite /shrincs_fxmss_spec_honest_node hn.
Qed.

Definition shrincs_fxmss_spec_honest_sibling sk pk b d z i j :=
  shrincs_fxmss_spec_honest_node sk pk b d (z + j) (Z.lxor (shrincs_fxmss_spec_ancestor
    i j) 1).

Lemma shrincs_fxmss_spec_sibling_shape b d z i j :
  shrincs_fxmss_spec_on_shape b d z i -> j < 255 - z ->
  shrincs_fxmss_spec_on_shape b d (z + j) (Z.lxor (shrincs_fxmss_spec_ancestor i j) 1).
Proof.
move=> hs /ltP hj.
rewrite subnE in hj.
apply shrincs_fxmss_spec_on_shape_sibling.
- apply shrincs_fxmss_spec_on_shape_ancestor; first exact hs.
  rewrite addnE.
  lia.
- rewrite addnE.
  lia.
Qed.

Definition shrincs_fxmss_spec_append_sibling sk pk b d z i (signature : option (seq
  UInt8)) j :=
  if signature is Some sig then
    let sibling_index := Z.lxor (shrincs_fxmss_spec_ancestor i j) 1 in
    let sibling_height := z + j in
    if Z.ltb sibling_index (2^64) && (sibling_height < 256) then
      if fxmss_node sk (wrepr U64 sibling_index) (uint U8 sibling_height) pk b (uint U8 d)
        is Some sibling then Some (sig ++ sibling) else None
    else None
  else None.

Lemma shrincs_fxmss_spec_append_honest sk pk b d z i sig j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i -> j < 255 -
    z ->
  shrincs_fxmss_spec_append_sibling sk pk b d z i (Some sig) j =
    Some (sig ++ shrincs_fxmss_spec_honest_sibling sk pk b d z i j).
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
rewrite /shrincs_fxmss_spec_append_sibling hindex hheight.
by rewrite (shrincs_fxmss_spec_honest_node_eq sk pk hd hshape).
Qed.

Lemma shrincs_fxmss_spec_append_fold sk pk b d z i sig js :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  all (fun j => j < 255 - z) js ->
  foldl (shrincs_fxmss_spec_append_sibling sk pk b d z i) (Some sig) js =
    Some (sig ++ flatten [seq tval (shrincs_fxmss_spec_honest_sibling sk pk b d z i j) |
      j <- js]).
Proof.
move=> hd hs.
elim: js sig => [|j js ih] sig; first by rewrite /= cats0.
move/andP=> [hj hjs].
cbn [foldl map flatten].
rewrite (shrincs_fxmss_spec_append_honest sk pk sig hd hs hj) (ih _ hjs).
by rewrite catA.
Qed.

Definition shrincs_fxmss_spec_honest_auth sk pk b d z i :=
  [seq shrincs_fxmss_spec_honest_sibling sk pk b d z i j | j <- range 0 (255 - z)].

Lemma shrincs_fxmss_spec_sign_eq message sk pk b d z i :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  shrincs_fxmss_spec_is_leaf b d z i = true ->
  fxmss_sign message sk (wrepr U64 i) (uint U8 z) pk b (uint U8 d) =
    if wots_c_sign message sk pk (uint U8 z) (wrepr U64 i) b (uint U8 d)
      is Some ws then
        Some (ws ++ flatten [seq tval n | n <- shrincs_fxmss_spec_honest_auth sk pk b d
          z i])
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
rewrite /fxmss_sign !shrincs_fxmss_spec_uint8_nat // /FXMSS_HEIGHT.
rewrite !shrincs_fxmss_spec_word_eq !wunsigned_repr_small // hguard.
case hw: (wots_c_sign _ _ _ _ _ _ _) => [ws|]; last reflexivity.
change (foldl (shrincs_fxmss_spec_append_sibling sk pk b d z i) (Some (tval ws))
    (range 0 (255 - z)) =
    Some (ws ++ flatten [seq tval n | n <- shrincs_fxmss_spec_honest_auth sk pk b d z
      i])).
have hall : all (fun j => j < 255 - z) (range 0 (255 - z)).
  apply/allP=> j.
  rewrite /range subn0 mem_iota add0n.
  by move/andP=> [_ hj].
rewrite (shrincs_fxmss_spec_append_fold sk pk (tval ws) hd hs hall).
by rewrite /shrincs_fxmss_spec_honest_auth -map_comp.
Qed.

Lemma shrincs_fxmss_spec_honest_auth_size sk pk b d z i :
  size (shrincs_fxmss_spec_honest_auth sk pk b d z i) = 255 - z.
Proof. by rewrite /shrincs_fxmss_spec_honest_auth size_map /range size_iota subn0. Qed.

Lemma shrincs_fxmss_spec_honest_auth_nth sk pk b d z i j :
  j < 255 - z ->
  nth (zeros 16) (shrincs_fxmss_spec_honest_auth sk pk b d z i) j =
    shrincs_fxmss_spec_honest_sibling sk pk b d z i j.
Proof.
move=> hj.
rewrite /shrincs_fxmss_spec_honest_auth /range subn0 (nth_map 0) ?size_iota //.
by rewrite nth_iota // add0n.
Qed.

Definition shrincs_fxmss_spec_recover_step pk z i (auth : seq UInt8) (node : Bytes 16) j
  :=
  let parent := FxmssTree (uint U8 (z + j + 1))
    (wrepr U64 (shrincs_fxmss_spec_ancestor i (j + 1))) in
  let sibling := slice auth (j * 16) 16 in
  if Z.eqb (shrincs_fxmss_spec_ancestor i j mod 2) 1 then
    H pk parent [tuple of sibling ++ node]
  else H pk parent [tuple of node ++ sibling].

Lemma shrincs_fxmss_spec_recover_honest_step sk pk b d z i j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i -> j < 255 -
    z ->
  shrincs_fxmss_spec_recover_step pk z i
    (flatten [seq tval n | n <- shrincs_fxmss_spec_honest_auth sk pk b d z i])
    (shrincs_fxmss_spec_honest_node sk pk b d (z+j) (shrincs_fxmss_spec_ancestor i j)) j
      =
  shrincs_fxmss_spec_honest_node sk pk b d (z+j.+1) (shrincs_fxmss_spec_ancestor i
    j.+1).
Proof.
move=> hd hs hj.
have hlt : (z+j < 255)%coq_nat.
  move/ltP: hj; rewrite subnE addnE; lia.
have hc := shrincs_fxmss_spec_on_shape_ancestor hs (Nat.lt_le_incl _ _ hlt).
have hsi := shrincs_fxmss_spec_sibling_shape hs hj.
have [hp _] := shrincs_fxmss_spec_on_shape_parent hc hlt.
have hn := shrincs_fxmss_spec_honest_node_eq sk pk hd hc.
have hsn := shrincs_fxmss_spec_honest_node_eq sk pk hd hsi.
have he := shrincs_fxmss_spec_parent_node hd hc hlt hn hsn.
rewrite (shrincs_fxmss_spec_honest_node_eq sk pk hd hp) in he.
rewrite /shrincs_fxmss_spec_recover_step slice_flatten_rows
  (@shrincs_fxmss_spec_honest_auth_nth sk pk b d z i j hj).
have ha : FxmssTree (uint U8 (z+j+1))
    (wrepr U64 (shrincs_fxmss_spec_ancestor i (j+1))) =
    FxmssTree (uint U8 (z+j).+1) (wrepr U64 (shrincs_fxmss_spec_ancestor i j / 2)).
  by rewrite !addn1 shrincs_fxmss_spec_ancestor_succ.
rewrite ha.
have hnxt : shrincs_fxmss_spec_honest_node sk pk b d (z+j.+1)
  (shrincs_fxmss_spec_ancestor i j.+1) =
    shrincs_fxmss_spec_honest_node sk pk b d (z+j).+1 (shrincs_fxmss_spec_ancestor i j
      / 2).
  by rewrite addnS shrincs_fxmss_spec_ancestor_succ.
rewrite hnxt.
by case: he.
Qed.

Lemma shrincs_fxmss_spec_on_shape_root b d i : shrincs_fxmss_spec_on_shape b d 255 i ->
  i = 0%Z.
Proof.
move=> [_ [hi hb]].
case: b hb => hb.
- change (i < 1)%Z in hb.
  lia.
- case: hb => [// | [_ hz]].
  lia.
Qed.

Lemma shrincs_fxmss_spec_recover_honest_fold sk pk b d z i count j :
  shrincs_fxmss_spec_legal_shape b d -> shrincs_fxmss_spec_on_shape b d z i ->
  z+j+count = 255 ->
  foldl (shrincs_fxmss_spec_recover_step pk z i
      (flatten [seq tval n | n <- shrincs_fxmss_spec_honest_auth sk pk b d z i]))
    (shrincs_fxmss_spec_honest_node sk pk b d (z+j) (shrincs_fxmss_spec_ancestor i j))
      (iota j count) =
  shrincs_fxmss_spec_honest_node sk pk b d 255 0.
Proof.
move=> hd hs.
elim: count j => [|count ih] j hcount.
- rewrite addn0 in hcount.
  have hc := shrincs_fxmss_spec_on_shape_ancestor hs (Nat.eq_le_incl _ _ hcount).
  rewrite hcount in hc *.
  by rewrite (shrincs_fxmss_spec_on_shape_root hc).
- (* A remaining authentication node recovers one parent before recursing. *)
  have hj : j < 255 - z.
    apply/ltP.
    rewrite addnE in hcount.
    rewrite subnE.
    lia.
  cbn [iota foldl].
  rewrite (shrincs_fxmss_spec_recover_honest_step sk pk hd hs hj).
  apply ih.
  rewrite !addnE in hcount *.
  lia.
Qed.
