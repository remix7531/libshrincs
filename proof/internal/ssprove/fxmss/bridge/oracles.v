(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bridge.oracles

    The public and internal generation, hash and forgery oracles preserve the
    bridge relation. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance bridge.model bridge.adapter bridge.keygen shape scheme.
From Stdlib Require Import BinInt Lia.
From Shrincs.internal.ssprove Require Import shape.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Bridge oracles *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_rom_refused_payload.

Lemma shrincs_fxmss_rom_lookup_couple x :
  fxmss_sf_hash_valid x ->
  ⊢ ⦃ fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) ⦄
    stateful_rom.shared_lookup fxmss_sf_scheme x ≈
    shrincs_fxmss_lookup shrincs_fxmss_sha256 (shrincs_fxmss_rom_internal_query x)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1) ⦄.
Proof.
move=> hx.
rewrite /stateful_rom.shared_lookup /shrincs_fxmss_lookup.
eapply r_get_remember_lhs => mp.
eapply r_get_remember_rhs => mi.
eapply (r_fact (getm mp x = getm mi (shrincs_fxmss_rom_internal_query x))).
{
  move=> h0 h1 [[hinv hp] hi].
  have hm := (proj2 hinv) x hx.
  rewrite /rel_app /get_side /= in hm.
  rewrite /rem_inv /get_side /= in hp hi.
  by rewrite -hp -hi.
}
move=> hm.
rewrite -hm.
case: (getm mp x) => [md|].
- apply r_ret => h0 h1 [[hinv hp] hi].
  by split.
- (* Uncached query: sample the same digest and extend both tables. *)
  eapply (r_scheme_bind (dBytes 32)); first exact: prog_valid.
  move=> md.
  cbv beta.
  eapply r_put_lhs.
  eapply r_put_rhs.
  apply r_ret => h0 h1 [h1a [[h0a [hpre ->]] ->]].
  case: hpre => [[hinv hp] hi].
  split; first by [].
  rewrite /rem_inv /get_side /= in hp hi.
  rewrite -hp -hi.
  exact: shrincs_fxmss_rom_heap_rel_rom_set.
Qed.

Local Opaque shrincs_fxmss_rom_route_query shrincs_fxmss_lookup
  stateful_rom.shared_lookup.

Lemma shrincs_fxmss_rom_hash_couple q_s q_h bit x :
  ⊢ ⦃ fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) ⦄
    stateful_rom.hash_body fxmss_sf_scheme q_h x ≈
    resolve (G_forge_keyed shrincs_fxmss_sha256 (shrincs_fxmss_resources_of q_s q_h)
      bit)
      (mkopsig shrincs_fxmss_op_hash shrincs_fxmss_hmsg_input ('option (bytes 32)))
      (shrincs_fxmss_rom_route_query x)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1) ⦄.
Proof.
rewrite /G_forge_keyed /G_forge /resolve /= coerce_kleisliE /stateful_rom.hash_body.
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{
  move=> h0 h1 [hinv hr].
  have hd := proj2 (proj1 hinv).
  rewrite /rel_app /get_side /= in hd.
  by rewrite -hd.
}
case: done => /=.
- exact: r_fail.
- eapply r_get_remember_lhs => hc.
  eapply (r_get_rhs_known shrincs_fxmss_hcnt_loc hc).
  {
    move=> h0 h1 [[hinv hd] hr].
    have hh := proj2 (proj1 (proj1 hinv)).
    rewrite /rel_app /get_side /= in hh.
    by rewrite -hh.
  }
  case hbudget: (hc < q_h) => /=.
  + eapply r_put_lhs.
    eapply r_put_rhs.
    eapply rpre_weaken_rule with
      (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1)).
    2: {
      move=> h0 h1 [h1a [[h0a [hpre ->]] ->]].
      case: hpre => [[hinv hd] hc0].
      exact: shrincs_fxmss_rom_heap_rel_hcnt_set.
    }
    rewrite shrincs_fxmss_rom_route_query_domain.
    case hx: (fxmss_sf_hash_valid x).
    * rewrite (shrincs_fxmss_rom_route_query_valid x hx).
      eapply r_bind with
        (mid := fun '(v0, h0) '(v1, h1) =>
          v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1)).
      -- exact: shrincs_fxmss_rom_lookup_couple.
      -- move=> md0 md1.
         apply r_ret => h0 h1 [-> hinv].
         by split.
    * apply r_ret => h0 h1 hinv.
      by split.
  + exact: r_fail.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge forge *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma shrincs_fxmss_rom_public_key_slices (pp partner root : bytes 16) :
  [ /\ slice [tuple of pp ++ partner ++ root] 0 16 = pp,
       slice [tuple of pp ++ partner ++ root] 16 16 = partner &
       slice [tuple of pp ++ partner ++ root] 32 16 = root ].
Proof.
change [ /\ slice (pp ++ partner ++ root) 0 16 = pp,
  slice (pp ++ partner ++ root) (16 + 0) 16 = partner &
  slice (pp ++ partner ++ root) (16 + (16 + 0)) 16 = root ].
by rewrite !slice_cat_tail !slice_cat_head slice_all.
Qed.

Local Opaque shrincs_fxmss_lookup stateful_rom.shared_lookup.

Lemma shrincs_fxmss_rom_check_couple cm sg :
  ⊢ ⦃ fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) ⦄
    stateful_rom.check_body fxmss_sf_scheme (cm, sg) ≈
    (partner ← get shrincs_fxmss_rom_partner_loc ;;
     shrincs_fxmss_forge_body shrincs_fxmss_sha256 false (fun _ _ _ _ _ => true)
       (shrincs_fxmss_rom_embed_message partner cm) sg)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1) ⦄.
Proof.
rewrite /stateful_rom.check_body /shrincs_fxmss_forge_body.
ssprove_code_simpl.
eapply r_get_remember_rhs => partner.
eapply r_get_remember_lhs => p.
eapply r_get_remember_rhs => s.
eapply (r_fact (exists ks kp q, shrincs_fxmss_rom_state_rel p s ks kp q)).
{
  move=> h0 h1 [[[hinv hpartner] hp] hi].
  case: hinv => [[[[[[he hs] hl] hsc] hhc] hd] hm].
  rewrite /rel_app /get_side /= in hs.
  rewrite /rem_inv /get_side /= in hp hi.
  rewrite hp hi in hs.
  do 3 eexists.
  exact: hs.
}
move=> [ks [kp [q hs]]].
case: p hs => [[sk pk]|]; case: s => [st|] => hs.
2,3: by case: hs.
2: exact: r_fail.
have hpk := shrincs_fxmss_rom_state_rel_pubkey sk pk st ks kp q hs.
rewrite hpk.
eapply (r_fact (partner = st.1.1.2)).
{ move=> h0 h1 [[[hinv hpartner] hp] hi].
  rewrite /rem_inv /get_side /= in hpartner hi.
  have he := shrincs_fxmss_rom_heap_rel_partner h0 h1 st hinv hi.
  by rewrite hpartner in he. }
move=> ->.
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{
  move=> h0 h1 [[[[hinv hpartner] hp] hi] hr].
  have hd := proj2 (proj1 hinv).
  rewrite /rel_app /get_side /= in hd.
  by rewrite -hd.
}
case: done => /=.
- exact: r_fail.
- eapply r_put_lhs.
  eapply r_put_rhs.
  eapply rpre_weaken_rule with
    (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) /\
      get_heap h1 shrincs_fxmss_st_loc = Some st).
  2: {
    move=> h0 h1 [h1a [[h0a [hpre ->]] ->]].
    case: hpre => [[[[hinv hpartner] hp] hi] hd].
    split; first exact: shrincs_fxmss_rom_heap_rel_done_set.
    rewrite get_set_heap_neq; first by [].
    exact: hi.
  }
  eapply r_get_remember_lhs with
    (pre := fun '(h0,h1) => shrincs_fxmss_rom_heap_rel (h0,h1) /\
      get_heap h1 shrincs_fxmss_st_loc = Some st) => lg.
  eapply (r_get_rhs_known shrincs_fxmss_log_loc
    (map (shrincs_fxmss_rom_embed_message st.1.1.2) lg)).
  {
    move=> h0 h1 [[hinv ht] hr].
    have hl := shrincs_fxmss_rom_heap_rel_log h0 h1 st hinv ht.
    rewrite /rem_inv /get_side /= in hr.
    by rewrite hl hr.
  }
  eapply r_get_remember_rhs => kt.
  eapply r_get_remember_rhs => sd.
  eapply r_get_remember_rhs => rt.
  eapply rpre_weaken_rule with
    (pre := fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1)).
  2: by move=> h0 h1 [[[[[hinv ht] hl] hk] hd] hr].
  rewrite shrincs_fxmss_rom_internal_message_valid.
  case hm: (fxmss_sf_message_valid cm).
  2: { apply r_ret => h0 h1 hinv. by split. }
  rewrite /fxmss_sf_verify_query.
  case hparse: (shrincs_sf_parse sg) => [[[[ht r] i] fsig]|].
  2: { apply r_ret => h0 h1 hinv. by split. }
  have [hpp hpartner hroot] :=
    shrincs_fxmss_rom_public_key_slices st.1.1.1 st.1.1.2 st.1.2.
  rewrite hpp hpartner hroot -shrincs_fxmss_rom_internal_bound_message.
  set x := (r, ((st.1.1.1, st.1.2),
    ((ht, i), shrincs_fxmss_bound_message (shrincs_fxmss_rom_embed_message st.1.1.2
      cm)))) : shrincs_fxmss_hmsg_input.
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
    (mid := fun '(v0, h0) '(v1, h1) =>
      v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1)).
  + exact: hc.
  + (* Equal digests give the same verification result and preserve the relation. *)
    move=> md0 md1.
    apply r_ret => h0 h1 [<- hinv].
    split; last exact: hinv.
    have hv := shrincs_fxmss_rom_internal_verify
      [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2] cm sg md0.
    rewrite hm hparse hpp hroot in hv.
    cbn [stateful_rom.sf_verify_finish fxmss_sf_scheme] in hv.
    by rewrite hv !andbT (mem_map (shrincs_fxmss_rom_embed_message_inj st.1.1.2)).
Qed.

Lemma shrincs_fxmss_rom_forge_couple q_s q_h bit cm sg :
  ⊢ ⦃ fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) ⦄
    stateful_rom.forge_body fxmss_sf_scheme bit (cm, sg) ≈
    (partner ← get shrincs_fxmss_rom_partner_loc ;;
     resolve (G_forge_keyed shrincs_fxmss_sha256 (shrincs_fxmss_resources_of q_s q_h)
       bit)
      shrincs_fxmss_forge_op (shrincs_fxmss_rom_embed_message partner cm, sg))
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1) ⦄.
Proof.
rewrite /stateful_rom.forge_body /G_forge_keyed.
setoid_rewrite resolve_forge.
eapply r_bind with
  (m₁ := (partner ← get shrincs_fxmss_rom_partner_loc ;;
    shrincs_fxmss_forge_body shrincs_fxmss_sha256 false (fun _ _ _ _ _ => true)
      (shrincs_fxmss_rom_embed_message partner cm) sg))
  (f₁ := fun v => ret (bit && v))
  (mid := fun '(v0, h0) '(v1, h1) =>
    v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1)).
- exact: shrincs_fxmss_rom_check_couple.
- move=> v0 v1.
  apply r_ret => h0 h1 [-> hinv].
  by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Bridge gen *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma shrincs_fxmss_rom_key_material (sp : shrincs_fxmss_setup) (ks kp pp root : bytes
  16) :
  fxmss_node ks (uint U64 0) (uint U8 255) pp sp.1.1 (uint U8 sp.1.2) =
    Some root ->
  shrincs_sf_keygen [tuple of ks ++ kp ++ pp] (shrincs_fxmss_rom_structure sp) sp.2 =
    Some (shrincs_fxmss_rom_pack_secret ((pp, sp.2, root), sp.1) ks kp,
      [tuple of pp ++ sp.2 ++ root]).
Proof.
move=> hroot.
have [hks hkp hpp] := shrincs_fxmss_rom_public_key_slices ks kp pp.
rewrite /shrincs_sf_keygen hks hkp hpp.
rewrite /shrincs_fxmss_rom_pack_secret /shrincs_fxmss_rom_structure.
by case: sp.1.1 hroot => hroot; rewrite /= !eqxx /= hroot.
Qed.

Lemma shrincs_fxmss_rom_state_rel_initial (sp : shrincs_fxmss_setup) (pp ks kp root :
  bytes 16) :
  shrincs_fxmss_structure_legal sp.1.1 sp.1.2 ->
  shrincs_fxmss_rom_state_rel
    (Some ((shrincs_fxmss_rom_pack_secret ((pp, sp.2, root), sp.1) ks kp,
            Some (uint U64 0)), [tuple of pp ++ sp.2 ++ root]))
    (Some ((pp, sp.2, root), sp.1)) (Some ks) (Some kp) 0.
Proof.
move=> hlegal.
exists ks, kp.
rewrite shrincs_fxmss_rom_counter_zero.
by split; try split.
Qed.

Lemma shrincs_fxmss_rom_heap_rel_before_gen h0 h1 :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  get_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme) = None ->
  get_heap h1 shrincs_fxmss_st_loc = None /\ get_heap h1 shrincs_fxmss_next_loc = 0.
Proof.
move=> [[[[[[hi hs] hl] hsc] hhc] hd] hm] hp.
rewrite /rel_app /get_side /= hp in hs.
case he: (get_heap h1 shrincs_fxmss_st_loc) => [st|] in hs *; first by [].
by case: hs => hk hprf hq; split.
Qed.

Local Opaque shrincs_fxmss_rom_state_rel.

Lemma shrincs_fxmss_rom_heap_rel_gen_set h0 h1 sp pp ks kp root :
  shrincs_fxmss_rom_heap_rel (h0, h1) ->
  get_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme) = None ->
  shrincs_fxmss_structure_legal sp.1.1 sp.1.2 ->
  shrincs_fxmss_rom_heap_rel
    (set_heap h0 (stateful_rom.sf_st_loc fxmss_sf_scheme)
      (Some ((shrincs_fxmss_rom_pack_secret ((pp, sp.2, root), sp.1) ks kp,
              Some (uint U64 0)), [tuple of pp ++ sp.2 ++ root])),
     set_heap (set_heap (set_heap (set_heap (set_heap (set_heap h1 shrincs_fxmss_st_loc
       (Some ((pp, sp.2, root), sp.1))) shrincs_fxmss_ks_loc (Some ks))
       shrincs_fxmss_kp_loc (Some kp)) shrincs_fxmss_keys_loc emptym)
         shrincs_fxmss_sd_loc emptym)
       shrincs_fxmss_rom_partner_loc sp.2).
Proof.
move=> hinv hp hlegal.
have [hst hn] := shrincs_fxmss_rom_heap_rel_before_gen h0 h1 hinv hp.
case: hinv => [[[[[[hi hs] hl] hsc] hhc] hd] hm].
rewrite /rel_app /get_side /= hst /shrincs_fxmss_rom_log_rel in hl.
rewrite /shrincs_fxmss_rom_heap_rel /rel_app /get_side /=.
repeat split;
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
try assumption.
- (* Generation changes only the private locations on each side. *)
  do 6 (apply: heap_ignore_set_r;
    first by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
      /shrincs_fxmss_locs !domm_mkfmap !inE /= ?orbT).
  apply: heap_ignore_set_l; last exact: hi.
  by rewrite /shrincs_fxmss_rom_private_locs !domm_union !in_fsetU
      /shrincs_fxmss_rom_adapter_locs
    /stateful_rom.sf_locations !domm_mkfmap !inE /=.
- rewrite hn.
  exact: shrincs_fxmss_rom_state_rel_initial.
- rewrite /shrincs_fxmss_rom_log_rel /=.
  by case: hl => -> ->; split.
Qed.

Lemma fxmss_sf_keygen_unfold (sp : fxmss_sf_setup) :
  prog (fxmss_sf_keygen sp) =
  (sk_seed ← dBytes 16 ;;
   sk_prf ← dBytes 16 ;;
   pk_seed ← dBytes 16 ;;
   let seed := [tuple of sk_seed ++ sk_prf ++ pk_seed] in
   let structure := [tuple (if sp.1.1 then FXMSS_SHAPE_BALANCED
                           else FXMSS_SHAPE_UNBALANCED); uint U8 sp.1.2] in
   match shrincs_sf_keygen seed structure sp.2 with
   | Some (sk, pk) => ret ((sk, Some (uint U64 0)), pk)
   | None => @fail (fxmss_sf_secret × bytes 48)
   end).
Proof. by []. Qed.

Local Opaque fxmss_node shrincs_fxmss_node shrincs_fxmss_rom_pack_secret
  dBytes fxmss_sf_keygen shrincs_sf_keygen.

(* Keep the heap relation folded during oracle simplification. *)
#[local] Arguments shrincs_fxmss_rom_heap_rel : simpl never.

Lemma shrincs_fxmss_rom_gen_couple q_s q_h bit sp :
  ⊢ ⦃ fun '(h0, h1) => shrincs_fxmss_rom_heap_rel (h0, h1) ⦄
    stateful_rom.gen_body fxmss_sf_scheme sp ≈
    (pk ← resolve (G_forge_keyed shrincs_fxmss_sha256 (shrincs_fxmss_resources_of q_s
      q_h) bit)
      (mkopsig shrincs_fxmss_op_gen shrincs_fxmss_setup (bytes 48)) sp ;;
     #put shrincs_fxmss_rom_partner_loc := sp.2 ;; ret pk)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ shrincs_fxmss_rom_heap_rel (h0, h1) ⦄.
Proof.
rewrite /G_forge_keyed /G_forge /resolve /= coerce_kleisliE /stateful_rom.gen_body.
change (stateful_rom.sf_setup_valid fxmss_sf_scheme sp)
  with (shrincs_fxmss_structure_legal sp.1.1 sp.1.2).
case hl: (shrincs_fxmss_structure_legal sp.1.1 sp.1.2).
2: {
  eapply r_get_remember_rhs => sto.
  case: sto => [st|] /=; first exact: r_fail_bind_rhs.
  eapply r_get_remember_rhs => done.
  case: done => /=; exact: r_fail_bind_rhs.
}
eapply r_get_remember_lhs => p.
eapply r_get_remember_rhs => s.
eapply (r_fact (isSome p = isSome s)).
{
  move=> h0 h1 [[hinv hp] hi].
  case: hinv => [[[[[[he hs] hlg] hsc] hhc] hd] hm].
  rewrite /rel_app /get_side /= in hs.
  rewrite /rem_inv /get_side /= in hp hi.
  rewrite hp hi in hs.
  exact: shrincs_fxmss_rom_state_rel_isSome hs.
}
move=> his.
case: p his => [p|]; case: s => [s|] => //= his.
- exact: r_fail_bind_rhs.
- eapply r_get_remember_lhs => done.
  eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
  {
    move=> h0 h1 [[[hinv hp] hi] hr].
    have hd := proj2 (proj1 hinv).
    rewrite /rel_app /get_side /= in hd.
    by rewrite -hd.
  }
  case: done => /=; first exact: r_fail_bind_rhs.
  rewrite fxmss_sf_keygen_unfold.
  ssprove_code_simpl.
  (* Keep the sampler abstract while reassociating and commuting draws. *)
  set d16 := dBytes 16.
  clearbody d16.
  eapply r_transR.
  + (* Commute the internal public and secret seed draws. *)
    lazymatch goal with
    | |- ⊢ ⦃ ?pre ⦄ ?c0 ≈ (?f ?a ?b ?c ?k) ⦃ ?post ⦄ =>
      change (⊢ ⦃ pre ⦄ c0 ≈ (@bind a b c k) ⦃ post ⦄)
    end.
    rewrite ?bind_assoc.
    setoid_rewrite bind_assoc.
    eapply (r_swap_scheme_scheme d16 d16); exact: prog_valid.
  + eapply (r_scheme_bind d16); first exact: prog_valid.
    move=> ks.
    cbv beta.
    eapply r_transL.
    * rewrite ?bind_assoc.
      eapply (r_swap_scheme_scheme d16 d16); exact: prog_valid.
    * (* Couple the public and message seeds, then establish the generated state. *)
      eapply (r_scheme_bind d16); first exact: prog_valid.
      move=> pp.
      cbv beta.
      rewrite bind_assoc.
      eapply (r_scheme_bind d16); first exact: prog_valid.
      move=> kp.
      cbv beta.
      have hd := shrincs_fxmss_rom_setup_legal sp hl.
      have hon :
        Shrincs.internal.ssprove.fxmss.model.nodes.shrincs_fxmss_spec_on_shape sp.1.1
        sp.1.2 255 0.
      {
        rewrite
          /Shrincs.internal.ssprove.fxmss.model.nodes.shrincs_fxmss_spec_on_shape.
        case: sp.1.1 hd => hd; repeat split; try lia; auto.
      }
      have [root hroot] :=
        Shrincs.internal.ssprove.fxmss.model.nodes.shrincs_fxmss_spec_node_total ks pp
        hd hon.
      have hk := shrincs_fxmss_rom_key_material sp ks kp pp root hroot.
      rewrite /shrincs_fxmss_rom_structure in hk.
      rewrite hk shrincs_fxmss_node_adapter hroot.
      ssprove_code_simpl.
      cbn [bind].
      eapply r_put_lhs.
      do 6 eapply r_put_rhs.
      apply r_ret => h0 h1 hpre.
      split; first by [].
      do 6 (case: hpre => ? [hpre ->]).
      case: hpre => h0a [[[[hinv hp] hi] hd0] ->].
      apply: shrincs_fxmss_rom_heap_rel_gen_set; assumption.
Qed.
