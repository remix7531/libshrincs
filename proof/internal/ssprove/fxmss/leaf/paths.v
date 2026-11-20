(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.paths

    The signing-order traversal of every legal leaf, with its inverse slot.
    Message binding and the all-attempt randomizer-log invariant used by the
    known-message population gate. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import params shape games model.nodes.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Leaf reduction paths *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition leaf_coord_at (sp : shrincs_fxmss_structure) (q : nat) : shrincs_fxmss_coord
  :=
  if sp.1 then (uint U8 (255 - sp.2), uint U64 q)
  else if q == sp.2 then (uint U8 (255 - sp.2), uint U64 0)
       else (uint U8 (254 - q), uint U64 1).

Definition leaf_slot (sp : shrincs_fxmss_structure) (a : shrincs_fxmss_coord) : nat :=
  if sp.1 then Z.to_nat (wunsigned a.2)
  else if a.2 == uint U64 0 then sp.2
       else 254 - Z.to_nat (wunsigned a.1).

Lemma leaf_select_eq sp q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  q < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  shrincs_fxmss_select_leaf sp.1 sp.2 q = Some (leaf_coord_at sp q).
Proof.
move=> hsp hq.
rewrite /shrincs_fxmss_select_leaf /leaf_coord_at hsp hq /=.
by case: sp.1; case: (q == sp.2).
Qed.

Lemma leaf_uint64_nat q :
  q < 2 ^ 64 -> Z.to_nat (wunsigned (uint U64 q)) = q.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt.
rewrite Z_of_nat_expn2 => hq.
rewrite /uint wunsigned_repr_small.
- change (0 <= Z.of_nat q < 2 ^ 64)%Z.
  split; first exact: Znat.Nat2Z.is_nonneg.
  exact hq.
- exact: Znat.Nat2Z.id.
Qed.

Lemma leaf_slot_coord_at sp q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  q < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  leaf_slot sp (leaf_coord_at sp q) = q.
Proof.
move=> hsp hq.
have hq64 := leq_trans hq (shrincs_fxmss_leaf_count_bound _ _ hsp).
case: sp hsp hq hq64 => [[|] d] hsp hq hq64 /=.
- by rewrite /leaf_slot /leaf_coord_at /= (leaf_uint64_nat _ hq64).
- rewrite /leaf_slot /leaf_coord_at /=.
  case he: (q == d) => /=.
  + by move/eqP: he => ->; rewrite eqxx.
  + change (254 - Z.to_nat (wunsigned (uint U8 (254 - q))) = q).
    have hd := shrincs_fxmss_legal_depth _ _ hsp.
    have hqd : q < d.
      move: hq; rewrite /shrincs_fxmss_leaf_count /= ltnS => hq.
      by rewrite ltn_neqAle he hq.
    rewrite shrincs_fxmss_spec_uint8_nat.
    * rewrite subnE.
      lia.
    * move/ltP: hqd; move/leP: hd => hd hqd.
      cbn in hd.
      rewrite !subnE.
      lia.
Qed.

Lemma leaf_schedule_eq sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  shrincs_fxmss_schedule sp =
    [seq leaf_coord_at sp q | q <- iota 0 (shrincs_fxmss_leaf_count sp.1 sp.2)].
Proof.
move=> hsp.
have hs : forall q, q \in iota 0 (shrincs_fxmss_leaf_count sp.1 sp.2) ->
  shrincs_fxmss_select_leaf sp.1 sp.2 q = Some (leaf_coord_at sp q).
  move=> q; rewrite mem_iota add0n /= => hq.
  exact: leaf_select_eq hsp hq.
rewrite /shrincs_fxmss_schedule.
elim: (iota _ _) hs => [|q qs ih] hs //=.
rewrite (hs q (mem_head _ _)) /= ih //.
move=> q' hq'.
apply: hs.
by rewrite in_cons hq' orbT.
Qed.

Lemma leaf_schedule_length sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size (shrincs_fxmss_schedule sp) = shrincs_fxmss_leaf_count sp.1 sp.2.
Proof.
by move=> hsp; rewrite (leaf_schedule_eq sp hsp) size_map size_iota.
Qed.

Lemma leaf_schedule_nth sp q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  q < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  nth (uint U8 0, uint U64 0) (shrincs_fxmss_schedule sp) q = leaf_coord_at sp q.
Proof.
move=> hsp hq.
rewrite (leaf_schedule_eq sp hsp) (nth_map 0) ?size_iota //.
by rewrite nth_iota // add0n.
Qed.

Lemma leaf_select_in_schedule sp q a :
  shrincs_fxmss_select_leaf sp.1 sp.2 q = Some a -> a \in shrincs_fxmss_schedule sp.
Proof.
move=> he.
have [hsp hq] := shrincs_fxmss_select_leaf_some _ _ _ _ he.
rewrite (leaf_select_eq sp q hsp hq) in he.
case: he => <-.
rewrite (leaf_schedule_eq sp hsp).
apply: map_f.
by rewrite mem_iota add0n.
Qed.

Lemma leaf_schedule_uniq sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> uniq (shrincs_fxmss_schedule sp).
Proof.
move=> hsp.
rewrite (leaf_schedule_eq sp hsp) map_inj_in_uniq ?iota_uniq //.
move=> q r.
rewrite !mem_iota !add0n /= => hq hr he.
have := congr1 (leaf_slot sp) he.
by rewrite !leaf_slot_coord_at.
Qed.

Lemma leaf_schedule_slot sp a :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  leaf_slot sp a < shrincs_fxmss_leaf_count sp.1 sp.2 /\
  leaf_coord_at sp (leaf_slot sp a) = a.
Proof.
move=> hsp.
rewrite (leaf_schedule_eq sp hsp) => /mapP[q].
rewrite mem_iota add0n /= => hq ->.
by rewrite (leaf_slot_coord_at sp q hsp hq).
Qed.

Lemma leaf_schedule_complete b d z i :
  shrincs_fxmss_structure_legal b d ->
  shrincs_fxmss_spec_on_shape b d z (Z.of_nat i) ->
  shrincs_fxmss_spec_is_leaf b d z (Z.of_nat i) ->
  (uint U8 z, uint U64 i) \in shrincs_fxmss_schedule (b, d).
Proof.
move=> hd [[hz hdepth] [hi hindex]] hleaf.
have hdb := shrincs_fxmss_legal_depth _ _ hd.
have hdp := shrincs_fxmss_legal_positive _ _ hd.
move/leP: hdb => hdb.
move/ltP: hdp => hdp.
rewrite (leaf_schedule_eq (b, d) hd).
apply/mapP.
case: b hd hindex hleaf => hd hindex hleaf.
- (* Balanced leaves all have the terminal height. *)
  have he : 255 - z = d.
    move: hleaf.
    by rewrite /shrincs_fxmss_spec_is_leaf /= orbF => /eqP.
  exists i.
  + rewrite mem_iota add0n /=.
    apply/ltP.
    apply (proj2 (Znat.Nat2Z.inj_lt _ _)).
    by rewrite /shrincs_fxmss_leaf_count /= Z_of_nat_expn2 -he subnE.
  + rewrite /leaf_coord_at /=.
    have hez : 255 - d = z by rewrite subnE in he *; lia.
    by rewrite hez.
- case: hindex => hi0.
  + (* The leftmost leaf is issued last. *)
    have hi0n : i = 0 by lia.
    move: hleaf.
    rewrite /shrincs_fxmss_spec_is_leaf hi0 /= orbF => /eqP he.
    exists d.
    * change (d \in iota 0 d.+1).
      by rewrite mem_iota add0n /= ltnSn.
    * rewrite /leaf_coord_at /= eqxx hi0n.
      have hez : 255 - d = z by rewrite subnE in he *; lia.
      by rewrite hez.
  + (* Every right sibling occupies its height's unique slot. *)
    have [hi1 hzlt] := hi0.
    have hi1n : i = 1 by lia.
    exists (254 - z).
    * rewrite mem_iota add0n /shrincs_fxmss_leaf_count /=.
      apply/ltP.
      rewrite subnE.
      lia.
    * (* A nonterminal spine coordinate recovers its original height. *)
      rewrite /leaf_coord_at /=.
      have hqd : 254 - z < d by apply/ltP; rewrite subnE; lia.
      rewrite (ltn_eqF hqd) hi1n.
      have hez : 254 - (254 - z) = z by rewrite !subnE; lia.
      by rewrite hez.
Qed.

Lemma leaf_coord_at_leaf sp q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  q < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  shrincs_fxmss_leaf_at sp.1 (uint U8 sp.2) (leaf_coord_at sp q).
Proof.
move=> hsp hq.
have hd := shrincs_fxmss_legal_depth _ _ hsp.
have hdf : (sp.2 < 256)%coq_nat by move/leP: hd; lia.
rewrite /shrincs_fxmss_leaf_at shrincs_fxmss_spec_uint8_nat //.
case: sp hsp hq hd hdf => [[|] d] hsp hq hd hdf /=.
- rewrite /leaf_coord_at /= shrincs_fxmss_spec_uint8_nat.
  + rewrite subnE; lia.
  + (* The balanced leaf height decodes to the tree depth. *)
    have he : 255 - (255 - d) = d.
      move/leP: hd => /= hd.
      rewrite !subnE.
      lia.
    by rewrite he eqxx.
- rewrite /leaf_coord_at /=.
  case: (q == d) => /=; last by rewrite eqxx orbT.
  rewrite shrincs_fxmss_spec_uint8_nat.
  + rewrite subnE; lia.
  + (* The terminal spine leaf has the required height. *)
    have he : 255 - (255 - d) = d.
      move/leP: hd => /= hd.
      rewrite !subnE.
      lia.
    by rewrite he eqxx.
Qed.

Lemma leaf_schedule_leaf sp a :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  shrincs_fxmss_leaf_at sp.1 (uint U8 sp.2) a.
Proof.
move=> hsp ha.
have [hq <-] := leaf_schedule_slot sp a hsp ha.
exact: leaf_coord_at_leaf hsp hq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf km log *)

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma shrincs_fxmss_bound_message_inj cm cm' :
  shrincs_fxmss_message_valid cm -> shrincs_fxmss_message_valid cm' ->
  shrincs_fxmss_bound_message cm = shrincs_fxmss_bound_message cm' -> cm = cm'.
Proof.
case: cm => [ctx m]; case: cm' => [ctx' m'].
rewrite /shrincs_fxmss_message_valid /= => /andP[hctx _] /andP[hctx' _].
rewrite /shrincs_fxmss_bound_message /= => -[hlen htail].
have hsize : size ctx = size ctx'.
  change (wunsigned (uint U8 (size ctx)) =
    wunsigned (uint U8 (size ctx'))) in hlen.
  have := congr1 Z.to_nat hlen.
  rewrite !shrincs_fxmss_spec_uint8_nat.
  - apply/ltP; exact: hctx.
  - apply/ltP; exact: hctx'.
  - by [].
move/eqP: htail.
rewrite (eqseq_cat _ _ hsize) => /andP[/eqP heq htail].
by move/eqP: htail => ->; rewrite heq.
Qed.

Definition known_message_log_consistent
    (rt : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16)) (lg : seq
      shrincs_fxmss_message) :=
  forall a cm r, shrincs_fxmss_message_valid cm ->
    getm rt (a, shrincs_fxmss_bound_message cm) = Some r -> cm \in lg.

Lemma known_message_log_empty : known_message_log_consistent emptym [::].
Proof. by move=> a cm r hcm; rewrite emptymE. Qed.

Lemma known_message_log_cons rt lg cm :
  known_message_log_consistent rt lg -> known_message_log_consistent rt (cm :: lg).
Proof.
move=> hlog a cm' r hcm' hr.
by rewrite in_cons (hlog a cm' r hcm' hr) orbT.
Qed.

Lemma known_message_log_set rt lg a cm r :
  shrincs_fxmss_message_valid cm -> known_message_log_consistent rt lg ->
  known_message_log_consistent (setm rt (a, shrincs_fxmss_bound_message cm) r)
    (cm :: lg).
Proof.
move=> hcm hlog a' cm' r' hcm'.
rewrite setmE.
case: ifP => [/eqP he|hne] hr.
- have hb := congr1 snd he.
  have hecm := shrincs_fxmss_bound_message_inj cm' cm hcm' hcm hb.
  by rewrite hecm in_cons eqxx.
- by rewrite in_cons (hlog a' cm' r' hcm' hr) orbT.
Qed.

Lemma known_message_log_fresh rt lg a cm r :
  known_message_log_consistent rt lg -> shrincs_fxmss_message_valid cm -> cm \notin lg
    ->
  getm rt (a, shrincs_fxmss_bound_message cm) != Some r.
Proof.
move=> hlog hcm hnot.
apply/eqP=> hr.
by move: hnot; rewrite (hlog a cm r hcm hr).
Qed.
