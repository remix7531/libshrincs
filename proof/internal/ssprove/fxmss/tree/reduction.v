(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.reduction

    Reduction to the static tree class. The preassigned experiment and reduction share
    all experiment locations. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core toolkit.relational_rules.
From Shrincs.internal.ssprove.lib.math Require Import merkle bin_tree.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape scheme games tree.forgery tree.classify tree.encoding tree.oracles
  tree.generation model.nodes tree.nodes tree.model.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** Tree reduction *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_route P st kt a md sg : raw_code 'bool :=
  match shrincs_fxmss_full_case P st kt a md sg with
  | Some (FColl q x y) =>
      let targets := shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
        st.1.1.1 st.2.1 st.2.2 in
      opr (shrincs_fxmss_tree_check_op P)
        (index (shrincs_fxmss_tree_path_tweak q, shrincs_fxmss_tree_message y) targets,
         shrincs_fxmss_tree_message x) (fun b => ret b)
  | _ => ret true
  end.

Lemma shrincs_fxmss_tree_route_valid P (L : Locations) st kt a md sg :
  ValidCode L (smtcr.I_SMTCR (shrincs_fxmss_hash_function P)) (shrincs_fxmss_tree_route
    P st kt a md sg).
Proof.
rewrite /shrincs_fxmss_tree_route.
case: (shrincs_fxmss_full_case P st kt a md sg) => [[q x y|q x a0|q a0|]|];
  ssprove_valid.
Qed.
#[export] Existing Instance shrincs_fxmss_tree_route_valid.

Definition shrincs_fxmss_tree_forge_body P (cm : shrincs_fxmss_message) (sg :
  shrincs_fxmss_bytes) : raw_code 'bool :=
  st ← getSome shrincs_fxmss_st_loc ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #put shrincs_fxmss_done_loc := true ;;
  lg ← get shrincs_fxmss_log_loc ;;
  kt ← get shrincs_fxmss_keys_loc ;;
  sd ← get shrincs_fxmss_sd_loc ;;
  rt ← get shrincs_fxmss_rt_loc ;;
  if shrincs_fxmss_message_valid cm then
    match shrincs_sf_parse sg with
    | Some (h, r, i, fsig) =>
        let a := (h, i) in
        let pp := st.1.1.1 in
        let bm := shrincs_fxmss_bound_message cm in
        md ← shrincs_fxmss_lookup P (r, ((pp, st.1.2), (a, bm))) ;;
        if shrincs_fxmss_verify P pp st.1.2 a fsig md &&
          (cm \notin lg) &&
          (~~ ((md \in codomm sd) && (getm rt (a, bm) != Some r)))
        then shrincs_fxmss_tree_route P st kt a md fsig
        else ret false
    | None => ret false
    end
  else ret false.

Lemma shrincs_fxmss_tree_forge_body_valid P cm sg :
  ValidCode shrincs_fxmss_locs (smtcr.I_SMTCR (shrincs_fxmss_hash_function P))
    (shrincs_fxmss_tree_forge_body P cm sg).
Proof.
rewrite /shrincs_fxmss_tree_forge_body.
ssprove_valid.
exact: shrincs_fxmss_lookup_valid.
exact: shrincs_fxmss_tree_route_valid.
Qed.
#[export] Existing Instance shrincs_fxmss_tree_forge_body_valid.

Definition R_tree P Q : package (smtcr.I_SMTCR (shrincs_fxmss_hash_function P)) I_forge
  :=
  [package shrincs_fxmss_locs;
    [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
      sto ← get shrincs_fxmss_st_loc ;;
      #assert ~~ isSome sto ;;
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
      _ ← opr (shrincs_fxmss_tree_eval_op P)
        (shrincs_fxmss_grind_tweak (uint U8 0, uint U64 0), [::]) (fun x => ret x) ;;
      ks ← shrincs_fxmss_secret_dist P ;;
      kp ← shrincs_fxmss_secret_dist P ;;
      kt ← shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1) ;;
      sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule setup.1) ;;
      root ← shrincs_fxmss_tree_generate P (fun c => odflt [::] (getm kt c))
        setup.1.1 setup.1.2 ;;
      pp ← opr (shrincs_fxmss_tree_reveal_op P) tt (fun p => ret p) ;;
      #put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
      #put shrincs_fxmss_ks_loc := Some ks ;;
      #put shrincs_fxmss_kp_loc := Some kp ;;
      #put shrincs_fxmss_keys_loc := kt ;;
      #put shrincs_fxmss_sd_loc := sd ;;
      ret [tuple of pp ++ setup.2 ++ root]
    };
    [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
      (cm) {
      st ← getSome shrincs_fxmss_st_loc ;;
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      sc ← get shrincs_fxmss_scnt_loc ;;
      #assert sc < shrincs_fxmss_sign_budget Q ;;
      lg ← get shrincs_fxmss_log_loc ;;
      #put shrincs_fxmss_scnt_loc := sc.+1 ;;
      #put shrincs_fxmss_log_loc := cm :: lg ;;
      if shrincs_fxmss_message_valid cm then
        q ← get shrincs_fxmss_next_loc ;;
        match shrincs_fxmss_select_leaf st.2.1 st.2.2 q with
        | None => ret None
        | Some a =>
            #put shrincs_fxmss_next_loc := q.+1 ;;
            ks ← getSome shrincs_fxmss_ks_loc ;;
            kp ← getSome shrincs_fxmss_kp_loc ;;
            kt ← get shrincs_fxmss_keys_loc ;;
            let pp := st.1.1.1 in
            let bm := shrincs_fxmss_bound_message cm in
            rt ← get shrincs_fxmss_rt_loc ;;
            ro ← (match getm rt (a, bm) with
                  | Some r => ret (Some r)
                  | None => r ← shrincs_fxmss_secret_dist P ;; ret (Some r)
                  end) ;;
            match ro with
            | None => ret None
            | Some r =>
                #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
                let x := (r, ((pp, st.1.2), (a, bm))) in
                md ← (sd ← get shrincs_fxmss_sd_loc ;;
                      md ← (match getm sd a with
                            | Some md => ret md
                            | None => md ← shrincs_fxmss_digest_dist P ;; ret md
                            end) ;;
                      mp ← get shrincs_fxmss_rom_loc ;;
                      #put shrincs_fxmss_rom_loc := setm mp x md ;;
                      ret md) ;;
                let keys := shrincs_fxmss_lookup_keys P true st ks kt in
                match shrincs_fxmss_sign P md keys a.2 a.1 pp
                        st.2.1 (uint U8 st.2.2) with
                | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
                | None => ret None
                end
            end
        end
      else ret None
    };
    [ Shrincs.internal.ssprove.fxmss.games.shrincs_fxmss_op_hash ] : {
      shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      hc ← get shrincs_fxmss_hcnt_loc ;;
      #assert hc < shrincs_fxmss_hash_budget Q ;;
      #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
      if Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111) then
        md ← shrincs_fxmss_lookup P x ;; ret (Some md)
      else ret None
    };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      } '(cm, sg) {
      verdict ← shrincs_fxmss_tree_forge_body P cm sg ;; ret verdict
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Tree protocol *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_ready P (st : shrincs_fxmss_state) (kt :
  shrincs_fxmss_key_table) (h : heap) : Prop :=
  let targets := shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 in
  [/\ shrincs_fxmss_spec_legal_shape st.2.1 st.2.2,
      st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
        st.1.1.1 st.2.1 st.2.2 255 0,
      get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some st.1.1.1,
      get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)) = qmap_from 0
        targets &
      get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) = unzip1 targets /\
      get_heap h smtcr.tcr_rev_loc = true].

Local Opaque smtcr.SMTCR_game.

Lemma shrincs_fxmss_tree_route_known P Q bit st kt a md sg h
    (T : choiceType) (K : bool -> raw_code T) :
  shrincs_fxmss_tree_ready P st kt h ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  Pr_code (bind (code_link (shrincs_fxmss_tree_route P st kt a md sg)
    (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class
      (shrincs_fxmss_leaf_capacity Q - 1) bit)) K) h =
  Pr_code (K ((bit || keep_no_tree_collision P st kt a md sg)%bool)) h.
Proof.
move=> [hd hroot hp ht [hw hr]] hv.
rewrite /shrincs_fxmss_tree_route /keep_no_tree_collision.
case hc: (shrincs_fxmss_full_case P st kt a md sg) => [[q x y|q x a0|q a0|]|] /=;
  try by rewrite orbT.
have [hm hne heq] := shrincs_fxmss_full_case_collision_words P st kt a sg md q x y
  hd hroot hv hc.
rewrite bind_assoc.
rewrite (shrincs_fxmss_tree_check_known P (shrincs_fxmss_leaf_capacity Q - 1) bit T
  st.1.1.1
  _ (shrincs_fxmss_tree_path_tweak q) (shrincs_fxmss_tree_message y)) //.
- (* The committed target is present at its indexed challenge slot. *)
  rewrite ht -[index _ _]add0n qmap_from_get.
  have hi : index (shrincs_fxmss_tree_path_tweak q, shrincs_fxmss_tree_message y)
      (shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
        st.1.1.1 st.2.1 st.2.2) < size
      (shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
        st.1.1.1 st.2.1 st.2.2) by rewrite index_mem.
  have [v hv'] := qnth_some _ _ hi.
  have hn := qnth_nth (shrincs_fxmss_tree_path_tweak q, shrincs_fxmss_tree_message y) _
    _ v hv'.
  rewrite nth_index // in hn.
  by rewrite -hn in hv'.
- by rewrite hne heq eqxx /= andbT orbF.
Qed.

Lemma shrincs_fxmss_tree_ready_generated P pp partner kt b d h :
  shrincs_fxmss_spec_legal_shape b d ->
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)) = emptym ->
  get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  shrincs_fxmss_tree_ready P
    ((pp, partner, val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
      (shrincs_fxmss_value_tree P pp (fun c => odflt [::] (getm kt c)) b d)), (b,d)) kt
    (set_heap (shrincs_fxmss_commit_heap P h
      (shrincs_fxmss_generated_targets P pp (fun c => odflt [::] (getm kt c)) b d))
      smtcr.tcr_rev_loc true).
Proof.
move=> hd hp hg ht.
split=> //=.
- by rewrite /shrincs_fxmss_honest_node (@shrincs_fxmss_root_materialized _ _ _ _ _ hd).
- by rewrite get_set_heap_neq // shrincs_fxmss_commit_heap_seed.
- by rewrite get_set_heap_neq // (shrincs_fxmss_commit_heap_table _ _ _ ht hg)
    (shrincs_fxmss_generated_targets_eq _ _ _ _ _ hd).
- split; last by rewrite get_set_heap_eq.
  by rewrite get_set_heap_neq // shrincs_fxmss_commit_heap_tweaks ht cat0s
    (shrincs_fxmss_generated_targets_eq _ _ _ _ _ hd).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree invariant *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_service_locs P : Locations :=
  [fmap smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P); smtcr.tcr_tgts_loc
    (shrincs_fxmss_hash_function P);
        smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P); smtcr.tcr_rev_loc].

Definition shrincs_fxmss_tree_rel P (sto : option shrincs_fxmss_state) (kt :
  shrincs_fxmss_key_table)
    (po : option (bytes 16)) (tg : {fmap nat -> tweak * seq UInt8})
    (tw : seq tweak) (rv : bool) : Prop :=
  match sto with
  | None => [/\ po = None, tg = emptym, tw = [::] & rv = false]
  | Some st =>
      let targets := shrincs_fxmss_tree_committed P (fun c => odflt [::] (getm kt c))
        st.1.1.1 st.2.1 st.2.2 in
      [/\ shrincs_fxmss_spec_legal_shape st.2.1 st.2.2,
          st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
            st.1.1.1 st.2.1 st.2.2 255 0,
          po = Some st.1.1.1, tg = qmap_from 0 targets &
          tw = unzip1 targets /\ rv = true]
  end.

Definition shrincs_fxmss_tree_inv P : precond :=
  heap_ignore (shrincs_fxmss_tree_service_locs P) ⋊
  rel_app [:: (rhs, shrincs_fxmss_st_loc); (rhs, shrincs_fxmss_keys_loc);
    (rhs, smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)); (rhs, smtcr.tcr_tgts_loc
      (shrincs_fxmss_hash_function P));
    (rhs, smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)); (rhs, smtcr.tcr_rev_loc)]
      (shrincs_fxmss_tree_rel P).

Arguments shrincs_fxmss_tree_inv : simpl never.

Lemma shrincs_fxmss_tree_invE P h0 h1 :
  shrincs_fxmss_tree_inv P (h0,h1) ->
  heap_ignore (shrincs_fxmss_tree_service_locs P) (h0,h1) /\
  shrincs_fxmss_tree_rel P (get_heap h1 shrincs_fxmss_st_loc) (get_heap h1
    shrincs_fxmss_keys_loc)
    (get_heap h1 (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)))
    (get_heap h1 (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)))
    (get_heap h1 (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)))
    (get_heap h1 smtcr.tcr_rev_loc).
Proof. by move=> [h1' h2]; split. Qed.

Lemma shrincs_fxmss_tree_inv_ready P h0 h1 st :
  shrincs_fxmss_tree_inv P (h0,h1) -> get_heap h1 shrincs_fxmss_st_loc = Some st ->
  shrincs_fxmss_tree_ready P st (get_heap h1 shrincs_fxmss_keys_loc) h1.
Proof.
move/shrincs_fxmss_tree_invE=> [_ hr] hs.
by rewrite hs /shrincs_fxmss_tree_rel in hr.
Qed.

Lemma shrincs_fxmss_tree_inv_get P l :
  l.1 \notin domm (shrincs_fxmss_tree_service_locs P) ->
  get_pre_cond l (shrincs_fxmss_tree_inv P).
Proof.
move=> hl h0 h1 /shrincs_fxmss_tree_invE[he _].
exact: he l hl.
Qed.

Local Opaque shrincs_fxmss_tree_rel.

Lemma shrincs_fxmss_tree_inv_put P (l : Location) (v : l) :
  l.1 \notin [:: 44; 45; 46; 47; 1300; 1303] ->
  put_pre_cond l v (shrincs_fxmss_tree_inv P).
Proof.
rewrite !inE !negb_or.
move=> /andP[h44 /andP[h45 /andP[h46 /andP[h47 /andP[hst hkt]]]]].
rewrite /shrincs_fxmss_tree_inv.
apply: put_pre_cond_conj; first exact: put_pre_cond_heap_ignore.
apply: put_pre_cond_rel_app.
change (l.1 \notin [:: 1300; 1303; 44; 45; 46; 47]).
by rewrite !inE !negb_or hst hkt h44 h45 h46 h47.
Qed.

Lemma shrincs_fxmss_tree_inv_initial P : shrincs_fxmss_tree_inv P (empty_heap,
  empty_heap).
Proof.
rewrite /shrincs_fxmss_tree_inv.
split.
- by move=> l hl.
- change (shrincs_fxmss_tree_rel P None emptym None emptym [::] false).
  cbv delta [shrincs_fxmss_tree_rel].
  by split.
Qed.
