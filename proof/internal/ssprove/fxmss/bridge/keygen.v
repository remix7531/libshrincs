(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bridge.keygen

    Key generation and the leaf schedule establish the heap relation used by the
    public-to-internal experiment bridge. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.lossless toolkit.relational_rules.
From Shrincs Require Import spec schemes games.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  model.nodes params shape games bridge.model bridge.adapter.
From mathcomp Require Import word_ssrZ word reals.
From mathcomp.experimental_reals Require Import distr realsum.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Lia.

(* ------------------------------------------------------------------ *)
(** ** Bridge keygen *)

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.

Definition shrincs_fxmss_rom_structure (sp : fxmss_sf_setup) : Bytes 2 :=
  [tuple (if sp.1.1 then FXMSS_SHAPE_BALANCED
          else FXMSS_SHAPE_UNBALANCED); uint U8 sp.1.2].

Lemma shrincs_fxmss_rom_setup_legal sp :
  fxmss_sf_setup_valid sp -> shrincs_fxmss_spec_legal_shape sp.1.1 sp.1.2.
Proof.
rewrite /fxmss_sf_setup_valid /shrincs_fxmss_spec_legal_shape.
move/andP=> [/leP hmin /leP hmax].
by case: sp.1.1 hmax => hmax; split.
Qed.

Lemma shrincs_fxmss_spec_keygen_total (sp : fxmss_sf_setup) (seed : Bytes 48) :
  fxmss_sf_setup_valid sp ->
  exists sk pk,
    shrincs_sf_keygen seed (shrincs_fxmss_rom_structure sp) sp.2 = Some (sk, pk).
Proof.
move=> hv.
have hd := shrincs_fxmss_rom_setup_legal sp hv.
have hr : shrincs_fxmss_spec_on_shape sp.1.1 sp.1.2 255 0.
{ rewrite /shrincs_fxmss_spec_on_shape.
  case: sp.1.1 hd => hd; repeat split; try lia; auto. }
have [root hroot] :=
  shrincs_fxmss_spec_node_total (slice seed 0 16) (slice seed 32 16) hd hr.
rewrite /shrincs_sf_keygen /shrincs_fxmss_rom_structure /=.
case hb: sp.1.1 in hroot *;
  rewrite /= /FXMSS_SHAPE_BALANCED /FXMSS_SHAPE_UNBALANCED
    !eqxx /= hroot; by eexists; eexists.
Qed.

Lemma shrincs_fxmss_spec_keygen_pubkey seed structure partner sk pk :
  shrincs_sf_keygen seed structure partner = Some (sk, pk) ->
  pk = shrincs_extract_pubkey sk.
Proof.
rewrite /shrincs_sf_keygen.
case: ifP => // hshape.
case: fxmss_node => [root|] //.
move=> [<- <-].
set a := slice seed 0 16.
set b := slice seed 16 16.
set c := slice seed 32 16.
apply: val_inj.
change (c ++ partner ++ root =
  slice (a ++ b ++ c ++ partner ++ structure ++ root) 32 32 ++
  slice (a ++ b ++ c ++ partner ++ structure ++ root) 66 16).
rewrite (slice_cat _ 32 16 16).
change (c ++ partner ++ root =
  (slice (a ++ b ++ c ++ partner ++ structure ++ root) (16+(16+0)) 16 ++
   slice (a ++ b ++ c ++ partner ++ structure ++ root) (16+(16+(16+0))) 16) ++
  slice (a ++ b ++ c ++ partner ++ structure ++ root)
    (16+(16+(16+(16+(2+0))))) 16).
by rewrite !slice_cat_tail !slice_cat_head slice_all -catA.
Qed.

Lemma shrincs_fxmss_dBytes_lossless n : LosslessCode (dBytes n).
Proof.
change (LosslessCode (sample_bytes n)).
elim: n => [|n ih]; first exact: Lossless_ret.
change (LosslessCode
  (b ← dByte ;; bs ← sample_bytes n ;; ret (cons_tuple b bs))).
rewrite /dByte /=.
apply: Lossless_sample.
move=> b.
rewrite /LosslessCode (Pr_fst_bind (sample_bytes_valid n)) -pr_predT.
apply: dweight_dlet_one.
- by rewrite pr_predT.
- move=> bs.
  by rewrite Pr_fst_ret pr_dunit.
Qed.

Lemma shrincs_fxmss_rom_keygen_lossless sp :
  fxmss_sf_setup_valid sp -> LosslessCode (fxmss_sf_keygen sp).
Proof.
move=> hv.
rewrite /LosslessCode -pr_predT.
change (dweight (Pr_fst
  (ks ← dBytes 16 ;; kp ← dBytes 16 ;; pp ← dBytes 16 ;;
    match shrincs_sf_keygen [tuple of ks ++ kp ++ pp]
        (shrincs_fxmss_rom_structure sp) sp.2 with
    | Some (sk, pk) => ret ((sk, Some (uint U64 0)), pk)
    | None => @fail (fxmss_sf_secret × bytes 48)
    end)) = 1%R).
rewrite (Pr_fst_bind (prog_valid (dBytes 16))).
apply: dweight_dlet_one.
- by rewrite pr_predT; exact: shrincs_fxmss_dBytes_lossless.
- move=> ks.
  rewrite (Pr_fst_bind (prog_valid (dBytes 16))).
  apply: dweight_dlet_one.
  + by rewrite pr_predT; exact: shrincs_fxmss_dBytes_lossless.
  + move=> kp.
    rewrite (Pr_fst_bind (prog_valid (dBytes 16))).
    apply: dweight_dlet_one.
    * by rewrite pr_predT; exact: shrincs_fxmss_dBytes_lossless.
    * move=> pp.
      have [sk [pk hk]] :=
        shrincs_fxmss_spec_keygen_total sp [tuple of ks ++ kp ++ pp] hv.
      by rewrite hk Pr_fst_ret pr_dunit.
Qed.

Lemma shrincs_fxmss_rom_keygen_pubkey sp :
  fxmss_sf_setup_valid sp ->
  \P_[Pr_fst (fxmss_sf_keygen sp)]
    (fun k => k.2 == shrincs_extract_pubkey k.1.1) = 1%R.
Proof.
move=> hv.
change (\P_[Pr_fst
  (ks ← dBytes 16 ;; kp ← dBytes 16 ;; pp ← dBytes 16 ;;
    match shrincs_sf_keygen [tuple of ks ++ kp ++ pp]
        (shrincs_fxmss_rom_structure sp) sp.2 with
    | Some (sk, pk) => ret ((sk, Some (uint U64 0)), pk)
    | None => @fail (fxmss_sf_secret × bytes 48)
    end)] (fun k => k.2 == shrincs_extract_pubkey k.1.1) = 1%R).
rewrite (Pr_fst_bind (prog_valid (dBytes 16))) pr_dlet.
under eq_exp => ks.
  rewrite (Pr_fst_bind (prog_valid (dBytes 16))) pr_dlet.
  under eq_exp => kp.
    rewrite (Pr_fst_bind (prog_valid (dBytes 16))) pr_dlet.
    under eq_exp => pp.
      have [sk [pk hk]] :=
        shrincs_fxmss_spec_keygen_total sp [tuple of ks ++ kp ++ pp] hv.
      rewrite hk Pr_fst_ret pr_dunit /=
        (shrincs_fxmss_spec_keygen_pubkey _ _ _ _ _ hk) eqxx.
    over.
    rewrite exp_cst pr_predT (shrincs_fxmss_dBytes_lossless 16) GRing.mulr1.
  over.
  rewrite exp_cst pr_predT (shrincs_fxmss_dBytes_lossless 16) GRing.mulr1.
over.
by rewrite exp_cst pr_predT (shrincs_fxmss_dBytes_lossless 16) GRing.mulr1.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge heap *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_rom_counter (sp : shrincs_fxmss_structure) (q : nat) : option
  UInt64 :=
  if q < shrincs_fxmss_leaf_count sp.1 sp.2 then Some (uint U64 q) else None.

Definition shrincs_fxmss_rom_pack_secret (st : shrincs_fxmss_state) (ks kp : bytes 16) :
  bytes 82 :=
  [tuple of ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2].

Definition shrincs_fxmss_rom_state_rel
    (p : option (fxmss_sf_secret × bytes 48)) (s : option shrincs_fxmss_state)
    (ks kp : option (bytes 16)) (q : nat) : Prop :=
  match p, s with
  | None, None => [ /\ ks = None, kp = None & q = 0 ]
  | Some (sk, pk), Some st =>
      exists kseed kprf,
        [ /\ ks = Some kseed, kp = Some kprf,
             sk = (shrincs_fxmss_rom_pack_secret st kseed kprf,
                   shrincs_fxmss_rom_counter st.2 q),
             pk = [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2] &
             shrincs_fxmss_structure_legal st.2.1 st.2.2 /\
             q <= shrincs_fxmss_leaf_count st.2.1 st.2.2 ]
  | _, _ => False
  end.

Definition shrincs_fxmss_rom_private_locs : Locations :=
  unionm (stateful_rom.sf_locations fxmss_sf_scheme)
    (unionm shrincs_fxmss_rom_adapter_locs shrincs_fxmss_locs).

Definition shrincs_fxmss_rom_log_rel (st : option shrincs_fxmss_state) (partner : bytes
  16)
    (public_log internal_log : seq shrincs_fxmss_message) : Prop :=
  match st with
  | None => public_log = [::] /\ internal_log = [::]
  | Some st => partner = st.1.1.2 /\
      internal_log = map (shrincs_fxmss_rom_embed_message partner) public_log
  end.

Definition shrincs_fxmss_rom_heap_rel : precond :=
  heap_ignore shrincs_fxmss_rom_private_locs
  ⋊ rel_app [:: (lhs, stateful_rom.sf_st_loc fxmss_sf_scheme);
                (rhs, shrincs_fxmss_st_loc); (rhs, shrincs_fxmss_ks_loc); (rhs,
                  shrincs_fxmss_kp_loc);
                (rhs, shrincs_fxmss_next_loc)] shrincs_fxmss_rom_state_rel
  ⋊ rel_app [:: (rhs, shrincs_fxmss_st_loc); (rhs, shrincs_fxmss_rom_partner_loc);
                (lhs, stateful_rom.sf_log_loc fxmss_sf_scheme); (rhs,
                  shrincs_fxmss_log_loc)]
      shrincs_fxmss_rom_log_rel
  ⋊ couple_cross stateful_rom.sf_scnt_loc shrincs_fxmss_scnt_loc eq
  ⋊ couple_cross stateful_rom.sf_hcnt_loc shrincs_fxmss_hcnt_loc eq
  ⋊ couple_cross stateful_rom.sf_done_loc shrincs_fxmss_done_loc eq
  ⋊ couple_cross (stateful_rom.sf_rom_loc fxmss_sf_scheme) shrincs_fxmss_rom_loc
    shrincs_fxmss_rom_rom_rel.

Lemma shrincs_fxmss_rom_heap_rel_invariant :
  Invariant (stateful_rom.sf_locations fxmss_sf_scheme)
    (unionm shrincs_fxmss_rom_adapter_locs shrincs_fxmss_locs)
      shrincs_fxmss_rom_heap_rel.
Proof.
rewrite /shrincs_fxmss_rom_heap_rel.
ssprove_invariant;
try reflexivity.
- by split.
- by split.
- exact: shrincs_fxmss_rom_rom_rel_empty.
Qed.

Lemma shrincs_fxmss_rom_heap_rel_partner h0 h1 st :
  shrincs_fxmss_rom_heap_rel (h0, h1) -> get_heap h1 shrincs_fxmss_st_loc = Some st ->
  get_heap h1 shrincs_fxmss_rom_partner_loc = st.1.1.2.
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] ht.
by move: hl; rewrite /rel_app /get_side /= ht /shrincs_fxmss_rom_log_rel => -[].
Qed.

Lemma shrincs_fxmss_rom_heap_rel_log h0 h1 st :
  shrincs_fxmss_rom_heap_rel (h0, h1) -> get_heap h1 shrincs_fxmss_st_loc = Some st ->
  get_heap h1 shrincs_fxmss_log_loc = map (shrincs_fxmss_rom_embed_message st.1.1.2)
    (get_heap h0 (stateful_rom.sf_log_loc fxmss_sf_scheme)).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] ht.
by move: hl; rewrite /rel_app /get_side /= ht /shrincs_fxmss_rom_log_rel => -[->].
Qed.

Local Opaque shrincs_fxmss_rom_state_rel shrincs_fxmss_rom_log_rel.

Lemma shrincs_fxmss_rom_heap_rel_rom_set h0 h1 x md :
  shrincs_fxmss_rom_heap_rel (h0, h1) -> fxmss_sf_hash_valid x ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 (stateful_rom.sf_rom_loc fxmss_sf_scheme)
      (setm (get_heap h0 (stateful_rom.sf_rom_loc fxmss_sf_scheme)) x md),
     set_heap h1 shrincs_fxmss_rom_loc
      (setm (get_heap h1 shrincs_fxmss_rom_loc) (shrincs_fxmss_rom_internal_query x)
        md)).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] hx.
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption.
- apply: heap_ignore_set_r.
  + by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
      /shrincs_fxmss_locs !domm_mkfmap !inE /= ?orbT.
  + apply: heap_ignore_set_l; last exact: hi.
    by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
      /stateful_rom.sf_locations !domm_mkfmap !inE /=.
- exact: shrincs_fxmss_rom_rom_rel_set.
Qed.

Lemma shrincs_fxmss_rom_heap_rel_hcnt_set h0 h1 n :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 stateful_rom.sf_hcnt_loc n, set_heap h1 shrincs_fxmss_hcnt_loc n).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm].
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption;
try reflexivity.
apply: heap_ignore_set_r.
- by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
      /shrincs_fxmss_locs !domm_mkfmap !inE /= ?orbT.
- apply: heap_ignore_set_l; last exact: hi.
  by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
      /stateful_rom.sf_locations !domm_mkfmap !inE /=.
Qed.

Lemma shrincs_fxmss_rom_heap_rel_done_set h0 h1 b :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 stateful_rom.sf_done_loc b, set_heap h1 shrincs_fxmss_done_loc b).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm].
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption;
try reflexivity.
apply: heap_ignore_set_r.
- by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
    /shrincs_fxmss_locs !domm_mkfmap !inE /= ?orbT.
- apply: heap_ignore_set_l; last exact: hi.
  by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
    /stateful_rom.sf_locations !domm_mkfmap !inE /=.
Qed.

Transparent shrincs_fxmss_rom_state_rel.

Lemma shrincs_fxmss_rom_state_rel_isSome p s ks kp q :
  shrincs_fxmss_rom_state_rel p s ks kp q -> isSome p = isSome s.
Proof. by case: p => [[sk pk]|]; case: s => [s|]. Qed.

Lemma shrincs_fxmss_rom_state_rel_pubkey sk pk st ks kp q :
  shrincs_fxmss_rom_state_rel (Some (sk, pk)) (Some st) ks kp q ->
  pk = [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2].
Proof. by move=> [kseed [kprf [_ _ _ hp _]]]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge schedule *)

(* MathComp powers are used after the key-generation imports of PeanoNat. *)
Import ssrnat.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_rom_uint64_unsigned q :
  q < 2 ^ 64 -> wunsigned (uint U64 q) = Z.of_nat q.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt hq.
rewrite Z_of_nat_expn2 in hq.
rewrite /uint wunsigned_repr_small //.
split; first exact: Znat.Nat2Z.is_nonneg.
exact: hq.
Qed.

Lemma shrincs_fxmss_rom_counter_zero sp :
  shrincs_fxmss_rom_counter sp 0 = Some (uint U64 0).
Proof.
rewrite /shrincs_fxmss_rom_counter /shrincs_fxmss_leaf_count.
by case: sp.1; rewrite ?expn_gt0.
Qed.

Lemma shrincs_fxmss_rom_leaf_schedule sp partner q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  shrincs_sf_leaf_select (shrincs_fxmss_rom_structure (sp, partner))
    (shrincs_fxmss_rom_counter sp q) =
  omap (fun a : shrincs_fxmss_coord => (a.2, a.1))
    (shrincs_fxmss_select_leaf sp.1 sp.2 q).
Proof.
move=> hlegal.
rewrite /shrincs_fxmss_rom_counter /shrincs_fxmss_select_leaf hlegal /=.
case hq: (q < shrincs_fxmss_leaf_count sp.1 sp.2); last by [].
have hq64 := ltn_leq_trans hq (shrincs_fxmss_leaf_count_bound _ _ hlegal).
have hd := shrincs_fxmss_legal_depth _ _ hlegal.
have hd0 := shrincs_fxmss_legal_positive _ _ hlegal.
have hd8 : (sp.2 < 256)%coq_nat by move/leP: hd; lia.
rewrite /shrincs_sf_leaf_select /shrincs_fxmss_rom_structure.
cbn -[uint wunsigned].
rewrite shrincs_fxmss_spec_uint8_nat // (shrincs_fxmss_rom_uint64_unsigned q hq64).
have hdne : (sp.2 == 0) = false by apply/negbTE; rewrite -lt0n.
change (eqn sp.2 0 = false) in hdne.
rewrite hdne.
case hb: sp.1 in hlegal hq *.
- (* Balanced tree: the counter is below the number of leaves. *)
  have hqZ : (Z.of_nat q < Z.pow 2 (Z.of_nat sp.2))%Z.
  { move/ltP/Znat.Nat2Z.inj_lt: hq.
    by rewrite /shrincs_fxmss_leaf_count Z_of_nat_expn2. }
  have hz : Z.ltb (Z.of_nat q) (Z.pow 2 (Z.of_nat sp.2)) = true.
  { exact/Z.ltb_lt. }
  by rewrite /= hz.
- case hqd: (q == sp.2).
  + move/eqP: hqd => ->.
    rewrite /= Z.eqb_refl.
    change (eqn sp.2 sp.2) with (sp.2 == sp.2).
    by rewrite !eqxx.
  + (* Unbalanced tree: an earlier counter selects a right leaf. *)
    have hlt : q < sp.2.
    { move: hq; rewrite /shrincs_fxmss_leaf_count ltnS leq_eqVlt hqd /=.
      by []. }
    have heq : Z.eqb (Z.of_nat q) (Z.of_nat sp.2) = false.
    { apply/Z.eqb_neq => /Znat.Nat2Z.inj he.
      by rewrite he eqxx in hqd. }
    have hltZ : Z.ltb (Z.of_nat q) (Z.of_nat sp.2) = true.
    { apply/Z.ltb_lt.
      exact/Znat.Nat2Z.inj_lt/ltP. }
    change (eqn q sp.2) with (q == sp.2).
    by rewrite /= eqxx heq hltZ Znat.Nat2Z.id hqd.
Qed.

Lemma shrincs_fxmss_rom_leaf_word_exhausted sp partner q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  q < 2 ^ 64 -> shrincs_fxmss_leaf_count sp.1 sp.2 <= q ->
  shrincs_sf_leaf_select (shrincs_fxmss_rom_structure (sp, partner))
    (Some (uint U64 q)) = None.
Proof.
move=> hlegal hq64 hq.
have hd := shrincs_fxmss_legal_depth _ _ hlegal.
have hd0 := shrincs_fxmss_legal_positive _ _ hlegal.
have hd8 : (sp.2 < 256)%coq_nat by move/leP: hd; lia.
rewrite /shrincs_sf_leaf_select /shrincs_fxmss_rom_structure.
cbn -[uint wunsigned].
rewrite shrincs_fxmss_spec_uint8_nat // (shrincs_fxmss_rom_uint64_unsigned q hq64).
have hdne : eqn sp.2 0 = false.
{ change ((sp.2 == 0) = false).
  by apply/negbTE; rewrite -lt0n. }
rewrite hdne.
case hb: sp.1 in hq *.
- (* Balanced tree: the exhausted counter fails the leaf bound. *)
  have hqZ : (Z.pow 2 (Z.of_nat sp.2) <= Z.of_nat q)%Z.
  { move/leP/Znat.Nat2Z.inj_le: hq.
    by rewrite /shrincs_fxmss_leaf_count Z_of_nat_expn2. }
  have hz : Z.ltb (Z.of_nat q) (Z.pow 2 (Z.of_nat sp.2)) = false.
  { exact/Z.ltb_ge. }
  by rewrite /= hz.
- (* Unbalanced tree: the counter is past the final leaf. *)
  have hgt : (sp.2 < q)%coq_nat by move/leP: hq.
  have heq : Z.eqb (Z.of_nat q) (Z.of_nat sp.2) = false.
  { apply/Z.eqb_neq. lia. }
  have hlt : Z.ltb (Z.of_nat q) (Z.of_nat sp.2) = false.
  { apply/Z.ltb_ge. lia. }
  by rewrite /= eqxx heq hlt.
Qed.

Lemma shrincs_fxmss_rom_consume_schedule sp partner q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  (shrincs_sf_consume (shrincs_fxmss_rom_structure (sp, partner))
    (shrincs_fxmss_rom_counter sp q)).1 =
  shrincs_fxmss_rom_counter sp
    (if q < shrincs_fxmss_leaf_count sp.1 sp.2 then q.+1 else q).
Proof.
move=> hlegal.
rewrite /shrincs_sf_consume (shrincs_fxmss_rom_leaf_schedule sp partner q hlegal).
case hq: (q < shrincs_fxmss_leaf_count sp.1 sp.2).
2: {
  by rewrite /shrincs_fxmss_select_leaf hlegal hq /= /shrincs_fxmss_rom_counter hq.
}
have hq64 := ltn_leq_trans hq (shrincs_fxmss_leaf_count_bound _ _ hlegal).
have hsel : exists a, shrincs_fxmss_select_leaf sp.1 sp.2 q = Some a.
{
  rewrite /shrincs_fxmss_select_leaf hlegal hq /=.
  by case: sp.1; [eexists | case: (q == sp.2); eexists].
}
case: hsel => a ->.
rewrite /shrincs_fxmss_rom_counter hq.
cbn -[uint wunsigned Z.add Z.pow Z.ltb
  shrincs_sf_leaf_select shrincs_fxmss_rom_structure].
rewrite (shrincs_fxmss_rom_uint64_unsigned q hq64).
replace (Z.add (Z.of_nat q) 1) with (Z.of_nat q.+1) by lia.
change (wrepr U64 (Z.of_nat q.+1)) with (uint U64 q.+1).
case hnext: (q.+1 < shrincs_fxmss_leaf_count sp.1 sp.2).
- (* A remaining leaf advances both counters to the same position. *)
  have hn64 := ltn_leq_trans hnext (shrincs_fxmss_leaf_count_bound _ _ hlegal).
  have hz : Z.ltb (Z.of_nat q.+1) (Z.pow 2 64) = true.
  { apply/Z.ltb_lt.
    move/ltP/Znat.Nat2Z.inj_lt: hn64.
    by rewrite Z_of_nat_expn2. }
  rewrite hz.
  have hn := shrincs_fxmss_rom_leaf_schedule sp partner q.+1 hlegal.
  rewrite /shrincs_fxmss_rom_counter hnext in hn.
  rewrite hn /shrincs_fxmss_select_leaf hlegal hnext /=.
  change (eqn (q.+2 - shrincs_fxmss_leaf_count sp.1 sp.2) 0)
    with (q.+1 < shrincs_fxmss_leaf_count sp.1 sp.2).
  rewrite hnext.
  by case: sp.1; [|case: (q.+1 == sp.2)].
- (* Exhaustion makes both next counters None. *)
  change (eqn (q.+2 - shrincs_fxmss_leaf_count sp.1 sp.2) 0)
    with (q.+1 < shrincs_fxmss_leaf_count sp.1 sp.2).
  rewrite hnext.
  case hz: (Z.ltb (Z.of_nat q.+1) (Z.pow 2 64)); last by [].
  have hn64 : q.+1 < 2 ^ 64.
  { apply/ltP/Znat.Nat2Z.inj_lt.
    rewrite Z_of_nat_expn2.
    exact/Z.ltb_lt. }
  have hnq : shrincs_fxmss_leaf_count sp.1 sp.2 <= q.+1.
  { by rewrite leqNgt hnext. }
  by rewrite (shrincs_fxmss_rom_leaf_word_exhausted sp partner q.+1 hlegal hn64 hnq).
Qed.
