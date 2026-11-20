(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bridge.sign

    The signing-oracle coupling completes the exact equivalence between the public
    experiment and the internal game. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  bridge.model params shape scheme games instance bridge.adapter bridge.keygen
  bridge.oracles.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Bridge sign couple *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma shrincs_fxmss_rom_secret_slices st ks kp :
  let sk := shrincs_fxmss_rom_pack_secret st ks kp in
  [ /\ slice sk 0 16 = ks, slice sk 16 16 = kp,
       slice sk 32 16 = st.1.1.1, slice sk 48 16 = st.1.1.2 &
       slice sk 64 2 = shrincs_fxmss_rom_structure (st.2, st.1.1.2) /\
       slice sk 66 16 = st.1.2 ].
Proof.
change [ /\
  slice (ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2)
    0 16 = ks,
  slice (ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2)
    (16 + 0) 16 = kp,
  slice (ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2)
    (16 + (16 + 0)) 16 = st.1.1.1,
  slice (ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2)
    (16 + (16 + (16 + 0))) 16 = st.1.1.2 &
  slice (ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2)
    (16 + (16 + (16 + (16 + 0)))) 2 = shrincs_fxmss_rom_structure (st.2, st.1.1.2) /\
  slice (ks ++ kp ++ st.1.1.1 ++ st.1.1.2 ++
    shrincs_fxmss_rom_structure (st.2, st.1.1.2) ++ st.1.2)
    (16 + (16 + (16 + (16 + (2 + 0))))) 16 = st.1.2 ].
by rewrite !slice_cat_tail !slice_cat_head slice_all.
Qed.

Lemma shrincs_fxmss_rom_sign_next_schedule st ks kp q cm :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  fxmss_sf_sign_next
    (shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2 q) cm =
  (shrincs_fxmss_rom_pack_secret st ks kp,
    shrincs_fxmss_rom_counter st.2
      (if q < shrincs_fxmss_leaf_count st.2.1 st.2.2 then q.+1 else q)).
Proof.
move=> hl.
have [_ _ _ _ [hs _]] := shrincs_fxmss_rom_secret_slices st ks kp.
rewrite /fxmss_sf_sign_next /= hs.
by rewrite shrincs_fxmss_rom_consume_schedule.
Qed.

#[local] Arguments shrincs_fxmss_rom_state_rel : simpl never.

Lemma shrincs_fxmss_rom_heap_rel_scnt_set h0 h1 v :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 stateful_rom.sf_scnt_loc v, set_heap h1 shrincs_fxmss_scnt_loc v).
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

Lemma shrincs_fxmss_rom_heap_rel_log_set h0 h1 st v :
  shrincs_fxmss_rom_heap_rel (h0, h1) -> get_heap h1 shrincs_fxmss_st_loc = Some st ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 (stateful_rom.sf_log_loc fxmss_sf_scheme) v,
     set_heap h1 shrincs_fxmss_log_loc (map (shrincs_fxmss_rom_embed_message st.1.1.2)
       v)).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] ht.
have hp : get_heap h1 shrincs_fxmss_rom_partner_loc = st.1.1.2.
{ by move: hl; rewrite /rel_app /get_side /= ht /shrincs_fxmss_rom_log_rel => -[]. }
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption.
- apply: heap_ignore_set_r.
  + by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs /shrincs_fxmss_locs !domm_mkfmap !inE /= ?orbT.
  + apply: heap_ignore_set_l; last exact: hi.
    by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs /stateful_rom.sf_locations !domm_mkfmap !inE /=.
- by rewrite ht /shrincs_fxmss_rom_log_rel hp; split.
Qed.

Lemma shrincs_fxmss_rom_heap_rel_rt_set h0 h1 rt :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  shrincs_fxmss_rom_heap_rel (h0, set_heap h1 shrincs_fxmss_rt_loc rt).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm].
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption.
apply: heap_ignore_set_r; last exact: hi.
by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
  /shrincs_fxmss_locs !domm_mkfmap !inE /= ?orbT.
Qed.

Local Opaque PRF_msg_sf shrincs_fxmss_rom_pack_secret shrincs_sf_encode fxmss_sign
  shrincs_fxmss_rom_counter.

(* Keep leaf selection folded until its schedule equation is used. *)
#[local] Arguments shrincs_fxmss_select_leaf : simpl never.

Lemma shrincs_fxmss_rom_packed_sign_query st ks kp q cm :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  fxmss_sf_sign_query
    (shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2 q) cm =
  match shrincs_fxmss_select_leaf st.2.1 st.2.2 q with
  | None => None
  | Some a =>
      match shrincs_fxmss_prf_msg_eval shrincs_fxmss_sha256 kp st.1.1.1 a
          (shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message st.1.1.2 cm))
            with
      | None => None
      | Some r => Some (shrincs_fxmss_rom_hash_encode
          (r, ((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message
            (shrincs_fxmss_rom_embed_message st.1.1.2 cm)))))
      end
  end.
Proof.
move=> hl.
have [hks hkp hpp hpartner [hsp hroot]] := shrincs_fxmss_rom_secret_slices st ks kp.
rewrite /fxmss_sf_sign_query.
cbn [fst snd].
rewrite hsp hkp hpp hpartner hroot
  (shrincs_fxmss_rom_leaf_schedule st.2 st.1.1.2 q hl).
case: shrincs_fxmss_select_leaf => [[h i]|] //=.
rewrite -shrincs_fxmss_rom_internal_bound_message.
reflexivity.
Qed.

Local Opaque shrincs_fxmss_sign shrincs_fxmss_derived_keys
  shrincs_sf_sign_with_digest.

Lemma shrincs_fxmss_rom_packed_sign_finish st ks kp q cm a r md :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  fxmss_sf_message_valid cm ->
  shrincs_fxmss_select_leaf st.2.1 st.2.2 q = Some a ->
  shrincs_fxmss_prf_msg_eval shrincs_fxmss_sha256 kp st.1.1.1 a
    (shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message st.1.1.2 cm)) = Some r
      ->
  stateful_rom.sf_sign_finish fxmss_sf_scheme
    (shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2 q) cm md =
  match shrincs_fxmss_sign shrincs_fxmss_sha256 md
      (shrincs_fxmss_derived_keys shrincs_fxmss_sha256 st.1.1.1 ks st.2.1
        (uint U8 st.2.2)) a.2 a.1 st.1.1.1 st.2.1 (uint U8 st.2.2) with
  | Some sg => shrincs_sf_encode a.1 r a.2 sg
  | None => None
  end.
Proof.
move=> hl hm ha hr.
have [hks hkp hpp hpartner [hsp hroot]] := shrincs_fxmss_rom_secret_slices st ks kp.
have hs : shrincs_sf_leaf_select (slice (shrincs_fxmss_rom_pack_secret st ks kp) 64 2)
    (shrincs_fxmss_rom_counter st.2 q) = Some (a.2, a.1).
{ by rewrite hsp (shrincs_fxmss_rom_leaf_schedule st.2 st.1.1.2 q hl) ha. }
have hpr : shrincs_fxmss_prf_msg_eval shrincs_fxmss_sha256
    (slice (shrincs_fxmss_rom_pack_secret st ks kp) 16 16)
    (slice (shrincs_fxmss_rom_pack_secret st ks kp) 32 16) (a.1, a.2)
    (shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message (slice
      (shrincs_fxmss_rom_pack_secret st ks kp) 48 16) cm)) = Some r.
{ by rewrite hkp hpp hpartner -surjective_pairing. }
pose proof (shrincs_fxmss_rom_internal_sign_finish
  (shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2 q)
  cm md a.2 a.1 r hm hs hpr) as hf.
rewrite hf.
cbn [fst snd].
rewrite hks hpp hsp /shrincs_fxmss_rom_structure.
case: st.2.1; reflexivity.
Qed.

Lemma shrincs_fxmss_rom_state_rel_sign_next sk pk st ks kp q cm :
  shrincs_fxmss_rom_state_rel (Some (sk, pk)) (Some st) ks kp q ->
  shrincs_fxmss_rom_state_rel (Some (fxmss_sf_sign_next sk cm, pk)) (Some st) ks kp
    (if q < shrincs_fxmss_leaf_count st.2.1 st.2.2 then q.+1 else q).
Proof.
rewrite /shrincs_fxmss_rom_state_rel.
move=> [kseed [kprf [hks hkp -> hpk [hl hq]]]].
rewrite (shrincs_fxmss_rom_sign_next_schedule st kseed kprf q cm hl).
exists kseed, kprf.
split; try assumption; try reflexivity.
split; first exact: hl.
by case hlt: (q < shrincs_fxmss_leaf_count st.2.1 st.2.2).
Qed.


Lemma shrincs_fxmss_rom_heap_rel_sign_next_set h0 h1 sk pk st q cm :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  get_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme) = Some (sk, pk) ->
  get_heap h1 shrincs_fxmss_st_loc = Some st ->
  get_heap h1 shrincs_fxmss_next_loc = q ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme)
      (Some (fxmss_sf_sign_next sk cm, pk)),
     set_heap h1 shrincs_fxmss_next_loc
      (if q < shrincs_fxmss_leaf_count st.2.1 st.2.2 then q.+1 else q)).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] hp ht hq.
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
- rewrite ht.
  apply: shrincs_fxmss_rom_state_rel_sign_next.
  by move: hs; rewrite /rel_app /get_side /= hp ht hq.
Qed.

Lemma shrincs_fxmss_rom_heap_rel_state_same_set h0 h1 p :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  get_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme) = p ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme) p, h1).
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] hp.
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption.
- apply: heap_ignore_set_l; last exact: hi.
  by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
    /stateful_rom.sf_locations !domm_mkfmap !inE /=.
- by move: hs; rewrite /rel_app /get_side /= hp.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge sign oracle *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque PRF_msg_sf shrincs_fxmss_rom_pack_secret shrincs_fxmss_rom_counter
  shrincs_fxmss_sign shrincs_fxmss_derived_keys
  shrincs_sf_sign_with_digest fxmss_sign shrincs_sf_encode
  stateful_rom.shared_lookup shrincs_fxmss_lookup fxmss_sf_sign_query
    fxmss_sf_sign_next.

Lemma shrincs_fxmss_rom_sign_couple q_s q_h bit cm :
  ⊢ ⦃ fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) ⦄
    stateful_rom.sign_body fxmss_sf_scheme q_s cm ≈
    (partner ← get shrincs_fxmss_rom_partner_loc ;;
     resolve (G_forge_keyed shrincs_fxmss_sha256 (shrincs_fxmss_resources_of q_s q_h)
       bit)
      (mkopsig shrincs_fxmss_op_sign shrincs_fxmss_message ('option
        shrincs_fxmss_bytes))
      (shrincs_fxmss_rom_embed_message partner cm))
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1) ⦄.
Proof.
rewrite /G_forge_keyed /G_forge /resolve /= coerce_kleisliE /stateful_rom.sign_body.
ssprove_code_simpl.
eapply r_get_remember_rhs => partner.
eapply r_get_remember_lhs => p.
eapply r_get_remember_rhs => s.
eapply (r_fact (exists ks kp q, shrincs_fxmss_rom_state_rel p s ks kp q)).
{
  move=> h0 h1 [[[hinv hpartner] hp] ht].
  have hs := proj2 (proj1 (proj1 (proj1 (proj1 (proj1 hinv))))).
  rewrite /rel_app /get_side /= in hs.
  rewrite /rem_inv /get_side /= in hp ht.
  rewrite hp ht in hs.
  do 3 eexists.
  exact: hs.
}
move=> [ks0 [kp0 [q0 hs]]].
case: p hs => [[sk pk]|]; case: s => [st|] => hs.
2,3: by case: hs.
2: exact: r_fail.
clear ks0 kp0 q0 hs.
ssprove_code_simpl.
apply rpre_hypothesis_rule => u0 u1 [[[hinv hpartner] hp] ht].
have hs := proj2 (proj1 (proj1 (proj1 (proj1 (proj1 hinv))))).
rewrite /rel_app /get_side /= in hs.
rewrite /rem_inv /get_side /= in hp ht hpartner.
have hpartner_eq := shrincs_fxmss_rom_heap_rel_partner u0 u1 st hinv ht.
rewrite hpartner in hpartner_eq.
subst partner.
rewrite hp ht in hs.
case: hs => ks [kp [hks hkp hsk hpk [hl hq]]].
set q := get_heap u1 shrincs_fxmss_next_loc in hsk hq.
subst sk.
(* Pin the key and counter reads while the admission guards update budgets. *)
set ready : precond := fun '(h0, h1) =>
  shrincs_fxmss_rom_heap_rel (h0, h1) /\
  [ /\ get_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme) =
        Some ((shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2
          q), pk),
       get_heap h1 shrincs_fxmss_st_loc = Some st, get_heap h1 shrincs_fxmss_next_loc
         = q,
       get_heap h1 shrincs_fxmss_ks_loc = Some ks & get_heap h1 shrincs_fxmss_kp_loc =
         Some kp ].
eapply rpre_weaken_rule with (pre := fun '(h0, h1) => ready (h0, h1)).
2: {
  move=> h0 h1 /= [-> ->].
  split; first exact: hinv.
  by split.
}
ssprove_code_simpl.
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{
  move=> h0 h1 [[hr _] hd].
  have he := proj2 (proj1 hr).
  rewrite /rel_app /get_side /= in he.
  by rewrite -he.
}
case: done => /=; first exact: r_fail.
eapply r_get_remember_lhs => sc.
eapply (r_get_rhs_known shrincs_fxmss_scnt_loc sc).
{
  move=> h0 h1 [[[hr _] hd] hc].
  have he := proj2 (proj1 (proj1 (proj1 hr))).
  rewrite /rel_app /get_side /= in he.
  by rewrite -he.
}
case hb: (sc < q_s) => /=; last exact: r_fail.
eapply r_put_lhs.
eapply r_get_remember_lhs => lg.
eapply (r_get_rhs_known shrincs_fxmss_log_loc
  (map (shrincs_fxmss_rom_embed_message st.1.1.2) lg)).
{
  move=> h0 h1 [[h0a [[[[hr hk] hd] hc] ->]] hlg].
  case: hk => hp0 ht0 hq0 hks0 hkp0.
  have he := shrincs_fxmss_rom_heap_rel_log h0a h1 st hr ht0.
  rewrite /rem_inv /get_side /= in hlg.
  rewrite get_set_heap_neq in hlg; first by [].
  by rewrite he hlg.
}
eapply r_put_rhs.
eapply r_put_lhs.
eapply r_put_rhs.
eapply rpre_weaken_rule with (pre := fun '(h0, h1) => ready (h0, h1)).
2: {
  move=> h0 h1 hpre.
  do 3 (case: hpre => ? [hpre ->]).
  case: hpre => [[h0a [[[[hr hk] hd] hc] ->]] hlg].
  case: hk => hp0 ht0 hq0 hks0 hkp0.
  split.
  - rewrite hpartner_eq.
    apply: (shrincs_fxmss_rom_heap_rel_log_set _ _ st (cm :: lg)).
    + exact: shrincs_fxmss_rom_heap_rel_scnt_set.
    + rewrite get_set_heap_neq; first by [].
      exact: ht0.
  - split;
    repeat first [rewrite get_set_heap_neq; first by []];
    assumption.
}
rewrite hpartner_eq.
rewrite shrincs_fxmss_rom_internal_message_valid.
case hm: (fxmss_sf_message_valid cm).
2: { apply r_ret => h0 h1 [hr _]. by split. }
eapply (r_get_rhs_known shrincs_fxmss_next_loc q).
{ by move=> h0 h1 [_ [_ _ hnext _ _]]. }
rewrite (shrincs_fxmss_rom_packed_sign_query st ks kp q cm hl).
case ha: (shrincs_fxmss_select_leaf st.2.1 st.2.2 q) => [a|].
- have hactive : q < shrincs_fxmss_leaf_count st.2.1 st.2.2.
  {
    move: ha.
    rewrite /shrincs_fxmss_select_leaf hl.
    by case he: (q < shrincs_fxmss_leaf_count st.2.1 st.2.2).
  }
  eapply r_put_lhs.
  eapply r_put_rhs.
  eapply rpre_weaken_rule with
    (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) /\
      get_heap h1 shrincs_fxmss_ks_loc = Some ks /\ get_heap h1 shrincs_fxmss_kp_loc =
        Some kp).
  2: {
    move=> h0 h1 [h1a [[h0a [[hr [hp0 ht0 hq0 hks0 hkp0]] ->]] ->]].
    split.
    - have hh := shrincs_fxmss_rom_heap_rel_sign_next_set h0a h1a
        (shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2 q)
        pk st q cm hr hp0 ht0 hq0.
      by rewrite hactive in hh.
    - split; rewrite get_set_heap_neq; first by [];
      first [assumption | by []].
  }
  cbn [bind].
  eapply (r_get_rhs_known shrincs_fxmss_ks_loc (Some ks)
    (fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) /\
      get_heap h1 shrincs_fxmss_ks_loc = Some ks /\ get_heap h1 shrincs_fxmss_kp_loc =
        Some kp)).
  { by move=> h0 h1 [_ [hk _]]. }
  ssprove_code_simpl.
  eapply (r_get_rhs_known shrincs_fxmss_kp_loc (Some kp)
    (fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) /\
      get_heap h1 shrincs_fxmss_ks_loc = Some ks /\ get_heap h1 shrincs_fxmss_kp_loc =
        Some kp)).
  { by move=> h0 h1 [_ [_ hk]]. }
  ssprove_code_simpl.
  eapply r_get_remember_rhs with
    (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) /\
      get_heap h1 shrincs_fxmss_ks_loc = Some ks /\ get_heap h1 shrincs_fxmss_kp_loc =
        Some kp) => kt.
  eapply r_get_remember_rhs => rt.
  eapply rpre_weaken_rule with
    (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1)).
  2: by move=> h0 h1 [[[hr _] _] _].
  change (shrincs_fxmss_prf_msg_eval shrincs_fxmss_sha256 kp st.1.1.1 a
    (shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message st.1.1.2 cm)))
    with (PRF_msg_sf kp st.1.1.1 a.1 a.2 (shrincs_fxmss_bound_message
      (shrincs_fxmss_rom_embed_message st.1.1.2 cm))).
  case hr: (PRF_msg_sf kp st.1.1.1 a.1 a.2
    (shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message st.1.1.2 cm))) =>
      [r|].
  2: { apply r_ret => h0 h1 hh. by split. }
  eapply r_put_rhs.
  eapply rpre_weaken_rule with
    (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1)).
  2: {
    move=> h0 h1 [h1a [hh ->]].
    exact: shrincs_fxmss_rom_heap_rel_rt_set.
  }
  set x := (r, ((st.1.1.1, st.1.2),
    (a, shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message st.1.1.2 cm)))) :
      shrincs_fxmss_hmsg_input.
  have hx : fxmss_sf_hash_valid (shrincs_fxmss_rom_hash_encode x).
  {
    apply: shrincs_fxmss_rom_hash_encode_valid.
    change (Z.leb (Z.of_nat (size (shrincs_fxmss_bound_message
      (shrincs_fxmss_rom_embed_message st.1.1.2 cm))))
      (Z.sub (Z.pow 2 61) 111)).
    rewrite shrincs_fxmss_rom_internal_bound_message.
    apply: shrincs_fxmss_rom_bound_message_valid.
    exact: hm.
  }
  have hc := shrincs_fxmss_rom_lookup_couple (shrincs_fxmss_rom_hash_encode x) hx.
  rewrite /shrincs_fxmss_rom_internal_query shrincs_fxmss_rom_hash_encodeK in hc.
  eapply r_bind with
    (mid := fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0,
      h1)).
  + exact: hc.
  + (* Equal digests yield matching signatures and next states. *)
    move=> md0 md1.
    eapply (r_fact (md0 = md1)
      (fun '(h0, h1) => md0 = md1 /\ shrincs_fxmss_rom_heap_rel (h0, h1))).
    { by move=> h0 h1 []. }
    move=> <-.
    have hf := shrincs_fxmss_rom_packed_sign_finish st ks kp q cm a r md0 hl hm ha hr.
    change (shrincs_sf_sign_with_digest cm.2 cm.1 (shrincs_fxmss_rom_pack_secret st ks
      kp)
        (shrincs_fxmss_rom_counter st.2 q) md0)
      with (stateful_rom.sf_sign_finish fxmss_sf_scheme
        (shrincs_fxmss_rom_pack_secret st ks kp, shrincs_fxmss_rom_counter st.2 q) cm
          md0).
    rewrite hf.
    case: shrincs_fxmss_sign => [sg|]; apply r_ret => h0 h1 [_ hh]; by split.
- (* Exhaustion writes the same public state and performs no hash lookup. *)
  have hex : (q < shrincs_fxmss_leaf_count st.2.1 st.2.2) = false.
  {
    move: ha.
    rewrite /shrincs_fxmss_select_leaf hl /=.
    case he: (q < shrincs_fxmss_leaf_count st.2.1 st.2.2) => //=.
    by case: st.2.1; [|case: (q == st.2.2)].
  }
  rewrite (shrincs_fxmss_rom_sign_next_schedule st ks kp q cm hl) hex.
  eapply r_put_lhs.
  apply r_ret => h0 h1 [h0a [[hh [hp0 _ _ _ _]] ->]].
  split; first by [].
  exact: shrincs_fxmss_rom_heap_rel_state_same_set.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge equivalence *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque stateful_rom.gen_body stateful_rom.sign_body stateful_rom.hash_body stateful_rom.forge_body.

(* Keep the internal game folded while resolving the public adapter. *)
Local Opaque G_forge_keyed shrincs_fxmss_rom_route_query.

Lemma shrincs_fxmss_rom_public_internal_perfect q_s q_h bit :
  perfect (stateful_rom.I_EUCMA fxmss_sf_scheme)
    (fxmss_eucma_game q_s q_h bit)
    (shrincs_fxmss_rom_adapter ∘ G_forge_keyed shrincs_fxmss_sha256
      (shrincs_fxmss_resources_of
      q_s q_h) bit).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ shrincs_fxmss_rom_heap_rel).
- change (Invariant (stateful_rom.sf_locations fxmss_sf_scheme)
    (unionm shrincs_fxmss_rom_adapter_locs shrincs_fxmss_locs)
      shrincs_fxmss_rom_heap_rel).
  exact: shrincs_fxmss_rom_heap_rel_invariant.
- (* Each exported oracle preserves the public-to-internal heap relation. *)
  move=> id S T arg has.
  fmap_invert has.
  + (* GEN: the public and internal key-generation oracles agree. *)
    rewrite resolve_link.
    rewrite /fxmss_eucma_game /stateful_rom.EUCMA_game
      /shrincs_fxmss_rom_adapter /resolve /= !coerce_kleisliE.
    cbn [code_link].
    exact: shrincs_fxmss_rom_gen_couple.
  + (* SIGN: both signing oracles consume the same leaf. *)
    rewrite resolve_link.
    rewrite /fxmss_eucma_game /stateful_rom.EUCMA_game
      /shrincs_fxmss_rom_adapter /resolve /= !coerce_kleisliE.
    cbn [code_link].
    setoid_rewrite bind_ret.
    exact: shrincs_fxmss_rom_sign_couple.
  + (* HASH: both oracles share the same encoded random-oracle query. *)
    rewrite resolve_link.
    rewrite /fxmss_eucma_game /stateful_rom.EUCMA_game
      /shrincs_fxmss_rom_adapter /resolve /= !coerce_kleisliE.
    cbn [code_link].
    rewrite bind_ret.
    exact: shrincs_fxmss_rom_hash_couple.
  + (* FORGE: both oracles apply the same verification and freshness checks. *)
    rewrite resolve_link.
    rewrite /fxmss_eucma_game /stateful_rom.EUCMA_game
      /shrincs_fxmss_rom_adapter /resolve /= !coerce_kleisliE.
    cbn [code_link].
    setoid_rewrite bind_ret.
    case: arg => cm sg.
    exact: shrincs_fxmss_rom_forge_couple.
Qed.

Lemma shrincs_fxmss_rom_public_internal_adv q_s q_h
    (A : adversary (stateful_rom.I_EUCMA fxmss_sf_scheme)) :
  AdvOf (fxmss_eucma_game q_s q_h) A =
  AdvOf (G_forge_keyed shrincs_fxmss_sha256 (shrincs_fxmss_resources_of q_s q_h))
    (A ∘ shrincs_fxmss_rom_adapter).
Proof.
rewrite (Adv_perfect_l (shrincs_fxmss_rom_public_internal_perfect q_s q_h true)).
rewrite (Adv_perfect_r (shrincs_fxmss_rom_public_internal_perfect q_s q_h false)).
exact: Adv_reduction.
Qed.
