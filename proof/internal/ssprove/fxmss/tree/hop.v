(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.hop

    The full FORGE protocol preserves the revealed challenge state before routing
    its final collision test. Perfect simulations of the static tree-class
    reduction, followed by the exact single-leg advantage equality with L-1
    committed targets. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.denotational_rules toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params scheme games tree.forgery tree.classify tree.reduction tree.preservation
  tree.oracles shape model.nodes tree.generation tree.encoding tree.model
    digest.filtered
  instance.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Tree forge simulation *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_tree_inv shrincs_fxmss_tree_rel smtcr.SMTCR_game.

Lemma shrincs_fxmss_tree_ready_put P st kt h (l : Location) (v : l) :
  l.1 \notin [:: 44; 45; 46; 47] ->
  shrincs_fxmss_tree_ready P st kt h -> shrincs_fxmss_tree_ready P st kt (set_heap h l
    v).
Proof.
rewrite !inE !negb_or.
move=> /andP[h44 /andP[h45 /andP[h46 h47]]].
rewrite /shrincs_fxmss_tree_ready.
rewrite get_set_heap_neq; first by change (44 != l.1); rewrite eq_sym.
rewrite get_set_heap_neq; first by change (45 != l.1); rewrite eq_sym.
rewrite get_set_heap_neq; first by change (46 != l.1); rewrite eq_sym.
rewrite get_set_heap_neq; first by change (47 != l.1); rewrite eq_sym.
by [].
Qed.

(* Keep the route and lookup bodies folded while simplifying the forge protocol. *)
Local Opaque shrincs_fxmss_tree_route shrincs_fxmss_lookup.

Lemma shrincs_fxmss_tree_forge_known P Q bit cm sg h :
  shrincs_fxmss_tree_inv P (h,h) ->
  Pr_code (code_link (shrincs_fxmss_tree_forge_body P cm sg)
    (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
      (shrincs_fxmss_leaf_capacity Q - 1) bit)) h =
  Pr_code (shrincs_fxmss_full_forge_body P
    (fun st kt a md fsig => (bit || keep_no_tree_collision P st kt a md fsig)%bool)
    cm sg) h.
Proof.
move=> hi.
rewrite /shrincs_fxmss_tree_forge_body /shrincs_fxmss_full_forge_body.
cbn [code_link bind].
rewrite !Pr_code_get.
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|]; last by [].
cbn [code_link bind].
rewrite !Pr_code_get.
case hd: (get_heap h shrincs_fxmss_done_loc); first by [].
cbn [negb assert bind code_link].
rewrite !Pr_code_put.
set h1 := set_heap h shrincs_fxmss_done_loc true.
have hr : shrincs_fxmss_tree_ready P st (get_heap h shrincs_fxmss_keys_loc) h1.
  apply: shrincs_fxmss_tree_ready_put; first by [].
  exact: shrincs_fxmss_tree_inv_ready hi hs.
rewrite !Pr_code_get.
rewrite get_set_heap_neq; first by [].
case hm: (shrincs_fxmss_message_valid cm); last by [].
case hp: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|]; last by [].
fold (@code_link 'bool).
rewrite code_link_bind.
rewrite (code_link_scheme _ _ _ _ (shrincs_fxmss_lookup_valid P [interface] _)).
rewrite bind_ret.
have hk : get_heap h1 shrincs_fxmss_keys_loc = get_heap h shrincs_fxmss_keys_loc.
  by rewrite /h1 get_set_heap_neq.
rewrite hk.
cbn [getSome].
match goal with
| |- Pr_code (bind _ ?kl) _ = Pr_code (bind _ ?kr) _ =>
  set leftk := kl; set rightk := kr
end.
have hend : forall md h2,
    shrincs_fxmss_tree_ready P st (get_heap h shrincs_fxmss_keys_loc) h2 ->
    Pr_code (leftk md) h2 = Pr_code (rightk md) h2.
  move=> md h2 hr2.
  rewrite /leftk /rightk.
  case hc: (_ && _ && _)%bool; last by [].
  have hv : shrincs_fxmss_verify P st.1.1.1 st.1.2 (a,i) fsig md.
    by move: hc => /andP[/andP[hv _] _].
  have he := shrincs_fxmss_tree_route_known P Q bit st (get_heap h
    shrincs_fxmss_keys_loc)
    (a,i) md fsig h2 'bool (fun b => ret b) hr2 hv.
  by rewrite bind_ret in he.
cbv delta [shrincs_fxmss_lookup].
cbn [bind].
rewrite !Pr_code_get.
case: (getm _ _) => [md|].
- exact: hend md h1 hr.
- (* A fresh digest preserves the revealed challenge state. *)
  rewrite !bind_assoc.
  apply: Pr_code_bind_stateless.
  move=> md.
  cbn [bind].
  rewrite !Pr_code_put.
  apply: hend.
  apply: shrincs_fxmss_tree_ready_put; first by [].
  exact hr.
Qed.

Local Ltac tree_access := first
  [ apply: shrincs_fxmss_tree_inv_get; rewrite /shrincs_fxmss_tree_service_locs;
    fmap_solve
  | apply: shrincs_fxmss_tree_inv_put; done ].

(* Keep lookup folded for the separate stability lemma. *)
Local Opaque shrincs_fxmss_lookup.

Lemma shrincs_fxmss_tree_full_forge_stable P keep cm sg :
  code_stable (shrincs_fxmss_tree_inv P) (shrincs_fxmss_full_forge_body P keep cm sg).
Proof.
rewrite /shrincs_fxmss_full_forge_body.
simpl.
split; first tree_access.
move=> sto.
case: sto => [st|]; last by [].
simpl.
split; first tree_access.
move=> done.
case: done; first by [].
simpl.
split; first tree_access.
split; first tree_access.
move=> lg.
split; first tree_access.
move=> kt.
split; first tree_access.
move=> sd.
split; first tree_access.
move=> rt.
case: (shrincs_fxmss_message_valid cm); last by [].
case: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|]; last by [].
rewrite bind_ret.
apply: code_stable_bind; first exact: shrincs_fxmss_tree_lookup_stable.
by move=> md.
Qed.

Lemma shrincs_fxmss_tree_forge_body_sim P Q bit cm sg :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_tree_inv P (s0,s1) ⦄
    shrincs_fxmss_full_forge_body P
      (fun st kt a md fsig => (bit || keep_no_tree_collision P st kt a md fsig)%bool)
      cm sg
    ≈ code_link (shrincs_fxmss_tree_forge_body P cm sg)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit)
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_tree_inv P (s0,s1) ⦄.
Proof.
eapply r_pr_code_rhs.
- (* The right-hand heap satisfies the revealed-state invariant. *)
  move=> h0 h1 hi.
  apply: shrincs_fxmss_tree_forge_known.
  have [_ hr] := shrincs_fxmss_tree_invE P h0 h1 hi.
  split; last exact hr.
  by move=> l hl.
- apply: r_code_stable.
  exact: shrincs_fxmss_tree_full_forge_stable.
Qed.

(* Keep the forge bodies folded while exposing the package operations. *)
Local Opaque shrincs_fxmss_full_forge_body shrincs_fxmss_tree_forge_body.

Lemma shrincs_fxmss_tree_forge_sim P Q bit cm sg :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_tree_inv P (s0,s1) ⦄
    resolve (G_forge_full_signature P Q
      (fun st kt a md fsig => (bit || keep_no_tree_collision P st kt a md fsig)%bool)
      true) shrincs_fxmss_forge_op (cm, sg)
    ≈ code_link (resolve (R_tree P Q) shrincs_fxmss_forge_op (cm, sg))
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit)
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_tree_inv P (s0,s1) ⦄.
Proof.
rewrite /resolve /G_forge_full_signature /R_tree /= coerce_kleisliE !bind_ret.
rewrite coerce_kleisliE bind_ret.
exact: shrincs_fxmss_tree_forge_body_sim.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree init invariant *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_tree_rel shrincs_fxmss_tree_inv.

Lemma shrincs_fxmss_tree_commit_ignore P h0 h1 targets :
  heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) ->
  heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,shrincs_fxmss_commit_heap P h1
    targets).
Proof.
elim: targets h1 => [|t ts ih] h1 hi; first exact hi.
change (heap_ignore (shrincs_fxmss_tree_service_locs P)
  (h0,shrincs_fxmss_commit_heap P (shrincs_fxmss_commit_step P h1 t) ts)).
apply: ih.
rewrite /shrincs_fxmss_commit_step.
apply: relational_rules.heap_ignore_set_r;
  first by rewrite /shrincs_fxmss_tree_service_locs mem_domm.
apply: relational_rules.heap_ignore_set_r;
  first by rewrite /shrincs_fxmss_tree_service_locs mem_domm.
exact hi.
Qed.

Definition shrincs_fxmss_tree_store (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) (h : heap) : heap
      :=
  set_heap (set_heap (set_heap (set_heap (set_heap h
    shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks)) shrincs_fxmss_kp_loc
      (Some kp))
    shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc sd.

Lemma shrincs_fxmss_tree_store_ignore P st ks kp kt sd h0 h1 :
  heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) ->
  heap_ignore (shrincs_fxmss_tree_service_locs P)
    (shrincs_fxmss_tree_store st ks kp kt sd h0, shrincs_fxmss_tree_store st ks kp kt sd
      h1).
Proof.
move=> hi.
rewrite /shrincs_fxmss_tree_store.
do 5 apply: put_pre_cond_heap_ignore.
exact hi.
Qed.

Lemma shrincs_fxmss_tree_store_ready P st ks kp kt sd h :
  shrincs_fxmss_tree_ready P st kt h ->
  shrincs_fxmss_tree_ready P st kt (shrincs_fxmss_tree_store st ks kp kt sd h).
Proof.
move=> hr.
rewrite /shrincs_fxmss_tree_store.
do 5 (apply: shrincs_fxmss_tree_ready_put; first by []).
exact hr.
Qed.

Lemma shrincs_fxmss_tree_store_state st ks kp kt sd h :
  get_heap (shrincs_fxmss_tree_store st ks kp kt sd h) shrincs_fxmss_st_loc = Some st.
Proof.
rewrite /shrincs_fxmss_tree_store.
do 4 (rewrite get_set_heap_neq; first by []).
exact: get_set_heap_eq.
Qed.

Lemma shrincs_fxmss_tree_store_keys st ks kp kt sd h :
  get_heap (shrincs_fxmss_tree_store st ks kp kt sd h) shrincs_fxmss_keys_loc = kt.
Proof.
rewrite /shrincs_fxmss_tree_store.
rewrite get_set_heap_neq; first by [].
exact: get_set_heap_eq.
Qed.

Lemma shrincs_fxmss_tree_store_inv P st ks kp kt sd h0 h1 :
  heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) ->
  shrincs_fxmss_tree_ready P st kt h1 ->
  shrincs_fxmss_tree_inv P
    (shrincs_fxmss_tree_store st ks kp kt sd h0, shrincs_fxmss_tree_store st ks kp kt sd
      h1).
Proof.
move=> hi hr.
split; first exact: shrincs_fxmss_tree_store_ignore.
change (shrincs_fxmss_tree_rel P
  (get_heap (shrincs_fxmss_tree_store st ks kp kt sd h1) shrincs_fxmss_st_loc)
  (get_heap (shrincs_fxmss_tree_store st ks kp kt sd h1) shrincs_fxmss_keys_loc)
  (get_heap (shrincs_fxmss_tree_store st ks kp kt sd h1) (smtcr.tcr_pp_loc
    (shrincs_fxmss_hash_function P)))
  (get_heap (shrincs_fxmss_tree_store st ks kp kt sd h1) (smtcr.tcr_tgts_loc
    (shrincs_fxmss_hash_function P)))
  (get_heap (shrincs_fxmss_tree_store st ks kp kt sd h1) (smtcr.tcr_tws_loc
    (shrincs_fxmss_hash_function P)))
  (get_heap (shrincs_fxmss_tree_store st ks kp kt sd h1) smtcr.tcr_rev_loc)).
rewrite shrincs_fxmss_tree_store_state shrincs_fxmss_tree_store_keys.
change (shrincs_fxmss_tree_ready P st kt (shrincs_fxmss_tree_store st ks kp kt sd h1)).
exact: shrincs_fxmss_tree_store_ready.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree gen simulation *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_gen_pre P (po : option (bytes 16)) : precond :=
  fun '(h0,h1) =>
    [/\ heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1),
        get_heap h1 (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = po,
        get_heap h1 (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)) = emptym,
        get_heap h1 (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) = [::] &
        get_heap h1 smtcr.tcr_rev_loc = false].

Arguments shrincs_fxmss_tree_gen_pre : simpl never.
Local Opaque shrincs_fxmss_tree_inv shrincs_fxmss_tree_rel smtcr.SMTCR_game.

Lemma shrincs_fxmss_tree_gen_pre_seed P pp h0 h1 :
  shrincs_fxmss_tree_gen_pre P None (h0,h1) ->
  shrincs_fxmss_tree_gen_pre P (Some pp)
    (h0, set_heap h1 (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) (Some pp)).
Proof.
move=> [hi hp ht hw hr].
split.
- apply: heap_ignore_set_r hi.
  by rewrite /shrincs_fxmss_tree_service_locs mem_domm.
- exact: get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

Definition shrincs_fxmss_tree_finish (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) : raw_code (bytes
      48) :=
  #put shrincs_fxmss_st_loc := Some st ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_keys_loc := kt ;;
  #put shrincs_fxmss_sd_loc := sd ;;
  ret [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2].

Lemma shrincs_fxmss_tree_finish_sim P st ks kp kt sd :
  ⊢ ⦃ λ '(h0,h1),
      heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) /\
      shrincs_fxmss_tree_ready P st kt h1 ⦄
    shrincs_fxmss_tree_finish st ks kp kt sd ≈ shrincs_fxmss_tree_finish st ks kp kt sd
  ⦃ λ '(x,h0) '(y,h1), x = y /\ shrincs_fxmss_tree_inv P (h0,h1) ⦄.
Proof.
rewrite /shrincs_fxmss_tree_finish.
eapply r_put_lhs with (pre := fun '(h0,h1) =>
  heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) /\ shrincs_fxmss_tree_ready P
    st kt h1).
do 4 eapply r_put_lhs.
do 5 eapply r_put_rhs.
apply: r_ret => h0 h1 hh.
split; first by [].
case: hh => h1e [hh ->].
case: hh => h1d [hh ->].
case: hh => h1c [hh ->].
case: hh => h1b [hh ->].
case: hh => h1a [hh ->].
case: hh => h0e [hh ->].
case: hh => h0d [hh ->].
case: hh => h0c [hh ->].
case: hh => h0b [hh ->].
case: hh => h0a [[hi hr] ->].
exact: shrincs_fxmss_tree_store_inv hi hr.
Qed.

Lemma shrincs_fxmss_tree_generate_sim P Q bit pp partner ks kp kt sd b d :
  shrincs_fxmss_spec_legal_shape b d ->
  let keys := fun c => odflt [::] (getm kt c) in
  let root := val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d) in
  ⊢ ⦃ λ '(h0,h1), shrincs_fxmss_tree_gen_pre P (Some pp) (h0,h1) ⦄
    shrincs_fxmss_tree_finish ((pp,partner,root),(b,d)) ks kp kt sd
    ≈ (root ← code_link (shrincs_fxmss_tree_generate P keys b d)
          (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
            (shrincs_fxmss_leaf_capacity Q - 1) bit) ;;
        pp ← resolve
          (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
            (shrincs_fxmss_leaf_capacity Q - 1) bit)
          (shrincs_fxmss_tree_reveal_op P) tt ;;
        shrincs_fxmss_tree_finish ((pp,partner,root),(b,d)) ks kp kt sd)
  ⦃ λ '(x,h0) '(y,h1), x = y /\ shrincs_fxmss_tree_inv P (h0,h1) ⦄.
Proof.
move=> hd keys root.
eapply r_pr_code_rhs_state with
  (f := fun h => set_heap (shrincs_fxmss_commit_heap P h
    (shrincs_fxmss_generated_targets P pp keys b d)) smtcr.tcr_rev_loc true)
  (pre' := fun '(h0,h1) => heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) /\
    shrincs_fxmss_tree_ready P ((pp,partner,root),(b,d)) kt h1).
- move=> h0 h1 [hi hp ht hw hr].
  rewrite (shrincs_fxmss_tree_generate_known P Q bit pp keys b d h1 _ _ hd hp hr hw).
  rewrite (shrincs_fxmss_tree_reveal_known P (shrincs_fxmss_leaf_capacity Q - 1) bit _
    pp).
  + by rewrite shrincs_fxmss_commit_heap_seed.
  + reflexivity.
- move=> h0 h1 [hi hp ht hw hr].
  split.
  + apply: heap_ignore_set_r;
      first by rewrite /shrincs_fxmss_tree_service_locs mem_domm.
    exact: shrincs_fxmss_tree_commit_ignore.
  + exact: shrincs_fxmss_tree_ready_generated hd hp ht hw.
- exact: shrincs_fxmss_tree_finish_sim.
Qed.

Local Opaque shrincs_fxmss_node shrincs_fxmss_sample_keys shrincs_fxmss_sample_digests
  shrincs_fxmss_tree_generate shrincs_fxmss_tree_finish shrincs_fxmss_lookup_keys.

Lemma shrincs_fxmss_tree_gen_sim P Q keep b0 bit setup :
  ⊢ ⦃ λ '(h0,h1), shrincs_fxmss_tree_inv P (h0,h1) ⦄
    resolve (G_forge_full_signature P Q keep b0) (shrincs_fxmss_op_gen,
      (shrincs_fxmss_setup, bytes 48))
      setup
    ≈ code_link (resolve (R_tree P Q) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes
      48)) setup)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit)
  ⦃ λ '(x,h0) '(y,h1), x = y /\ shrincs_fxmss_tree_inv P (h0,h1) ⦄.
Proof.
have hsync : ProvenBy (syncs shrincs_fxmss_st_loc) (shrincs_fxmss_tree_inv P).
  move=> [h0 h1] hi.
  apply: (shrincs_fxmss_tree_inv_get P shrincs_fxmss_st_loc _ h0 h1 hi).
  by rewrite /shrincs_fxmss_tree_service_locs; fmap_solve.
rewrite /resolve /G_forge_full_signature /R_tree /= !coerce_kleisliE.
cbn [code_link].
eapply (@r_get_vs_get_remember_rhs _ _ _ _ _ _ _ hsync).
move=> sto.
case: sto => [st|].
- simpl.
  apply: r_fail.
- cbn [isSome negb assert bind code_link].
  have hd_sync : ProvenBy (syncs shrincs_fxmss_done_loc)
      (shrincs_fxmss_tree_inv P ⋊ rem_rhs shrincs_fxmss_st_loc None).
    move=> [h0 h1] [hi _].
    apply: (shrincs_fxmss_tree_inv_get P shrincs_fxmss_done_loc _ h0 h1 hi).
    by rewrite /shrincs_fxmss_tree_service_locs; fmap_solve.
  eapply (@r_get_vs_get_remember_rhs _ _ _ _ _ _ _ hd_sync).
  move=> done.
  case: done.
  + simpl.
    apply: r_fail.
  + cbn [negb assert bind code_link].
    case hlegal: (shrincs_fxmss_structure_legal setup.1.1 setup.1.2).
    * (* A legal setup initializes the committed targets. *)
      cbn [assert bind code_link].
      have hd : shrincs_fxmss_spec_legal_shape setup.1.1 setup.1.2.
        by apply/shrincs_fxmss_legal_shapeP; rewrite hlegal.
      eapply rpre_weaken_rule with
        (pre := fun '(h0,h1) => shrincs_fxmss_tree_gen_pre P None (h0,h1)); last first.
      -- (* Unused setup leaves the challenge seed and target table empty. *)
         move=> h0 h1 [[hi hs] _].
         have [he hr] := shrincs_fxmss_tree_invE P h0 h1 hi.
         change (get_heap h1 shrincs_fxmss_st_loc = None) in hs.
         rewrite hs in hr.
         cbv delta [shrincs_fxmss_tree_rel] in hr.
         case: hr => hp ht hw hv.
         by split.
      -- (* Generate keys and commit the tree targets under a shared seed. *)
         simpl.
         fold (@code_link (bytes 48)).
         have heval : resolve
             (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
               (shrincs_fxmss_leaf_capacity Q - 1) bit)
             (shrincs_fxmss_tree_eval_op P) (shrincs_fxmss_grind_tweak (uint U8 0, uint
               U64 0), [::]) =
             (po ← get (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) ;;
              pp ← (match po with
                | Some pp => ret pp
                | None => pp ← shrincs_fxmss_public_seed_dist P ;;
                    #put (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) := Some pp
                      ;; ret pp
                end) ;;
              ret (th_eval (shrincs_fxmss_hash_function P) pp
                (shrincs_fxmss_grind_tweak (uint U8 0, uint U64 0)) [::])).
           cbv delta [smtcr.SMTCR_game].
           by rewrite /resolve /shrincs_fxmss_tree_eval_op /=
             coerce_kleisliE.
         rewrite heval.
         eapply (r_get_bind_rhs (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P))
           None).
           by move=> h0 h1 [_ hp _ _ _].
         cbn [bind].
         rewrite !bind_assoc.
         eapply (@r_scheme_bind (bytes 16) (bytes 48) (shrincs_fxmss_public_seed_dist
           P));
           first exact: prog_valid.
         move=> pp.
         cbn [bind].
         eapply r_put_rhs_weak with
           (pre' := fun '(h0,h1) => shrincs_fxmss_tree_gen_pre P (Some pp) (h0,h1));
           first exact: shrincs_fxmss_tree_gen_pre_seed.
         cbv delta [shrincs_fxmss_tree_finish].
         match goal with
         | |- @rel_jdg ?A ?B ?pre ?post ?c0 (?f ?T ?c ?g) =>
           change (@rel_jdg A B pre post c0 (@code_link T c g))
         end.
         rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid
           (shrincs_fxmss_secret_dist P))).
         eapply (@r_scheme_bind (bytes 16) (bytes 48) (shrincs_fxmss_secret_dist P));
           first exact: prog_valid.
         move=> ks.
         rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid
           (shrincs_fxmss_secret_dist P))).
         eapply (@r_scheme_bind (bytes 16) (bytes 48) (shrincs_fxmss_secret_dist P));
           first exact: prog_valid.
         move=> kp.
         rewrite code_link_bind (code_link_scheme _ _ _ _
           (shrincs_fxmss_sample_keys_valid P emptym [interface] (shrincs_fxmss_schedule
             setup.1))).
         eapply (@r_scheme_bind shrincs_fxmss_key_table (bytes 48));
           first exact: shrincs_fxmss_sample_keys_valid.
         move=> kt.
         rewrite code_link_bind (code_link_scheme _ _ _ _
           (shrincs_fxmss_sample_digests_valid P emptym [interface]
             (shrincs_fxmss_schedule setup.1))).
         eapply (@r_scheme_bind shrincs_fxmss_digest_table (bytes 48));
           first exact: shrincs_fxmss_sample_digests_valid.
         move=> sd.
         cbv delta [shrincs_fxmss_lookup_keys].
         rewrite (@shrincs_fxmss_root_materialized P _ _ _ _
           hd).
         simpl.
         fold (@code_link (bytes 48)).
         rewrite code_link_bind.
         cbn [code_link].
         have ht := shrincs_fxmss_tree_generate_sim P Q bit pp setup.2 ks kp kt sd
           setup.1.1 setup.1.2 hd.
         cbn zeta in ht.
         rewrite -surjective_pairing in ht.
         exact ht.
    * simpl.
      apply: r_fail.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree hop *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_tree_inv shrincs_fxmss_tree_rel smtcr.SMTCR_game.

Lemma R_tree_perfect P Q bit :
  perfect I_forge
    (G_forge_full_signature P Q
      (fun st kt a md sg => (bit || keep_no_tree_collision P st kt a md sg)%bool)
      true)
    (R_tree P Q ∘
      smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (shrincs_fxmss_tree_inv P)).
- cbv beta delta [shrincs_fxmss_tree_inv].
  ssprove_invariant.
  cbv beta delta [shrincs_fxmss_tree_rel].
  by [].
- simplify_eq_rel arg.
  + (* GEN establishes the committed-tree invariant. *)
    have hgen := shrincs_fxmss_tree_gen_sim P Q
      (fun st kt a md sg => (bit || keep_no_tree_collision P st kt a md sg)%bool)
      true bit arg.
    rewrite /resolve /G_forge_full_signature /R_tree /= !coerce_kleisliE in hgen.
    exact hgen.
  + (* SIGN preserves the committed-tree invariant. *)
    have hsign := shrincs_fxmss_tree_sign_sim P Q
      (fun st kt a md sg => (bit || keep_no_tree_collision P st kt a md sg)%bool)
      true (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit) arg.
    rewrite /resolve /G_forge_full_signature /R_tree /= !coerce_kleisliE in hsign.
    exact hsign.
  + (* HASH preserves the committed-tree invariant. *)
    have hhash := shrincs_fxmss_tree_hash_sim P Q
      (fun st kt a md sg => (bit || keep_no_tree_collision P st kt a md sg)%bool)
      true (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) bit) arg.
    rewrite /resolve /G_forge_full_signature /R_tree /= !coerce_kleisliE in hhash.
    exact hhash.
  + case: arg => cm sg.
    have hforge := shrincs_fxmss_tree_forge_sim P Q bit cm sg.
    rewrite /resolve /G_forge_full_signature /R_tree /= !coerce_kleisliE in hforge.
    exact hforge.
Qed.

Lemma R_tree_real P Q :
  perfect I_forge (G_forge_digest_filtered P Q true)
    (R_tree P Q ∘
      smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) true).
Proof.
rewrite -forge_full_signature_digest_filtered_eq.
exact: (R_tree_perfect P Q true).
Qed.

Lemma R_tree_ideal P Q :
  perfect I_forge (G_tree_free P Q true)
    (R_tree P Q ∘
      smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
        (shrincs_fxmss_leaf_capacity Q - 1) false).
Proof. exact: (R_tree_perfect P Q false). Qed.

Lemma tree_advantage P Q (A : adversary I_forge) :
  Adv (G_forge_digest_filtered P Q true) (G_tree_free P Q true) A =
  AdvOf (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
    (shrincs_fxmss_leaf_capacity Q - 1))
    (A ∘ R_tree P Q).
Proof.
rewrite (Adv_perfect_l (R_tree_real P Q)).
rewrite (Adv_perfect_r (R_tree_ideal P Q)).
exact: Adv_reduction.
Qed.

Lemma tree_sha256_advantage Q (A : adversary I_forge) :
  Adv (G_forge_digest_filtered shrincs_fxmss_sha256 Q true) (G_tree_free
    shrincs_fxmss_sha256 Q true) A =
  AdvOf (fxmss_tree_game (shrincs_fxmss_leaf_capacity Q - 1)) (A ∘ R_tree
    shrincs_fxmss_sha256 Q).
Proof.
have he b : smtcr.SMTCR_game (shrincs_fxmss_hash_function shrincs_fxmss_sha256)
  fxmss_tree_class
    (shrincs_fxmss_leaf_capacity Q - 1) b = fxmss_tree_game (shrincs_fxmss_leaf_capacity
      Q - 1) b.
  apply: package_ext => x.
  reflexivity.
  cbv delta [smtcr.SMTCR_game].
  reflexivity.
rewrite (tree_advantage shrincs_fxmss_sha256 Q A).
by rewrite !he.
Qed.
