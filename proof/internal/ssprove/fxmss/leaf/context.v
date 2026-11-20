(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.context

    Assemble a Merkle tree from signing-order leaf roots and relate its lookups to
    the legal leaf schedule. Concrete prepared-leaf contexts for the forward UD
    bound. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules games.scheduled_batch toolkit.batch_map.
From Shrincs.internal.ssprove.lib.math Require Import
  bin_tree tree_paths tree_leaf_map merkle.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape scheme games instance leaf.opening leaf.paths leaf.known_message
  leaf.prepare tree.encoding tree.model leaf.commitments leaf.known_message_game
    model.nodes
  tree.nodes tree.classify paired.reduction leaf.fixed_batch leaf.batch leaf.uniform.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.wots Require Import params scheme.

(* ------------------------------------------------------------------ *)
(** ** Leaf tree *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope nat_scope.

Lemma leaf_tree_balanced_depth d p :
  p \in leaf_paths (shrincs_fxmss_tree_shape true d) -> size p = d.
Proof.
elim: d p => [|d ih] p /=.
- by rewrite inE => /eqP ->.
- rewrite mem_cat => /orP[/mapP[q hq ->]|/mapP[q hq ->]] /=;
    by rewrite (ih q hq).
Qed.

Lemma leaf_tree_spine_path d p :
  p \in leaf_paths (shrincs_fxmss_tree_shape false d) ->
  p = nseq d false \/ exists k, k < d /\ p = rcons (nseq k false) true.
Proof.
elim: d p => [|d ih] p /=.
- rewrite inE => /eqP ->.
  by left.
- rewrite mem_cat => /orP[/mapP[q hq ->]|].
  + have [->|[k [hk ->]]] := ih q hq.
    * by left.
    * right.
      exists k.+1.
      by split.
  + rewrite inE => /eqP ->.
    right.
    exists 0.
    by split.
Qed.

Lemma leaf_tree_path_scheduled b d p :
  shrincs_fxmss_structure_legal b d ->
  p \in leaf_paths (shrincs_fxmss_tree_shape b d) ->
  shrincs_fxmss_path_coord p \in shrincs_fxmss_schedule (b, d).
Proof.
move=> hsp hp.
rewrite (leaf_schedule_eq (b, d) hsp).
apply/mapP.
case: b in hsp hp *.
- have hlen := leaf_tree_balanced_depth d p hp.
  exists (idx_of_path p).
  + rewrite mem_iota add0n /=.
    by have := idx_of_path_lt p; rewrite hlen.
  + by rewrite /leaf_coord_at /shrincs_fxmss_path_coord /= hlen.
- have [->|[k [hk ->]]] := leaf_tree_spine_path d p hp.
  + exists d.
    * by rewrite mem_iota add0n /= ltnSn.
    * by rewrite /leaf_coord_at /shrincs_fxmss_path_coord /= eqxx size_nseq
        idx_of_path_false.
  + exists k.
    * rewrite mem_iota add0n /=.
      exact: ltnW hk.
    * rewrite /leaf_coord_at /shrincs_fxmss_path_coord /= (ltn_eqF hk)
        size_rcons size_nseq shrincs_fxmss_path_index_rcons idx_of_path_false.
      congr (_, _).
Qed.

Definition leaf_root_lookup (sp : shrincs_fxmss_structure) (roots : seq (bytes 16)) a :=
  nth (zeros 16) roots (leaf_slot sp a).

Definition leaf_value_tree (sp : shrincs_fxmss_structure) roots : bt (bytes 16) :=
  bt_posmap (fun p _ => leaf_root_lookup sp roots (shrincs_fxmss_path_coord p))
    [::] (shrincs_fxmss_tree_shape sp.1 sp.2).

Definition leaf_batch_tree P pp sp roots :=
  val_bt (shrincs_fxmss_tree_node_hash P pp) [::] (leaf_value_tree sp roots).

Lemma leaf_root_lookup_honest P sp pp kt a :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  leaf_root_lookup sp (leaf_opening_roots P sp pp kt) a =
    leaf_pk P sp pp a (odflt [::] (getm kt a)).
Proof.
move=> hsp ha.
have [hj he] := leaf_schedule_slot sp a hsp ha.
rewrite /leaf_root_lookup /leaf_opening_roots (nth_map (uint U8 0, uint U64 0)).
- by rewrite (leaf_schedule_length sp hsp).
- by rewrite (leaf_schedule_nth sp _ hsp hj) he.
Qed.

Lemma leaf_value_tree_honest P sp pp kt :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  leaf_value_tree sp (leaf_opening_roots P sp pp kt) =
  shrincs_fxmss_value_tree P pp (fun a => odflt [::] (getm kt a)) sp.1 sp.2.
Proof.
move=> hsp.
apply: bt_posmap_leaf_congr => p x hp.
rewrite cat0s.
apply: (leaf_root_lookup_honest P sp pp kt _ hsp).
exact: (leaf_tree_path_scheduled sp.1 sp.2 p hsp hp).
Qed.

Lemma leaf_batch_tree_honest P sp pp kt :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  shrincs_fxmss_node P (fun a => odflt [::] (getm kt a))
    (uint U64 0) (uint U8 255) pp sp.1 (uint U8 sp.2) =
  Some (leaf_batch_tree P pp sp (leaf_opening_roots P sp pp kt)).
Proof.
move=> hsp.
rewrite /leaf_batch_tree (leaf_value_tree_honest P sp pp kt hsp).
apply: shrincs_fxmss_root_materialized.
exact: (proj1 (shrincs_fxmss_legal_shapeP sp.1 sp.2) hsp).
Qed.

Fixpoint leaf_tree_eval (pos : seq bool) (t : bt (bytes 16)) :
    raw_code (bytes 16) :=
  match t with
  | BLeaf x => ret x
  | BNode l r =>
      lv ← leaf_tree_eval (rcons pos false) l ;;
      rv ← leaf_tree_eval (rcons pos true) r ;;
      call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 }
        (shrincs_fxmss_tree_tweak (shrincs_fxmss_path_coord pos), lv ++ rv)
  end.

Lemma leaf_tree_eval_pre p b pos t pp
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : bytes 16 -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k (val_bt (shrincs_fxmss_tree_node_hash shrincs_fxmss_sha256 pp) pos t) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (leaf_tree_eval pos t)
      (G_scheduled_pre shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin.
elim: t pos k => [x|l ihl r ihr] pos k hk.
- exact: hk.
- (* An internal node evaluates both subtrees with the pinned seed. *)
  cbn [leaf_tree_eval].
  rewrite code_link_bind bind_assoc.
  apply: ihl.
  rewrite code_link_bind bind_assoc.
  apply: ihr.
  cbn [code_link].
  rewrite resolve_leaf_pre_eval bind_ret.
  eapply r_bind_assertD_rhs; first by [].
  move=> _.
  eapply (r_get_rhs_pin (pre_pp_loc shrincs_thf) (Some pp));
    first exact: hpin.
  cbn [bind].
  exact: hk.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf context *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_ctx_roots_loc := mkloc 1900 ([::] : seq (bytes 16)).
Definition leaf_ctx_locs : Locations :=
  [fmap shrincs_fxmss_st_loc; shrincs_fxmss_ks_loc; shrincs_fxmss_kp_loc;
    shrincs_fxmss_keys_loc; shrincs_fxmss_log_loc;
    shrincs_fxmss_scnt_loc; shrincs_fxmss_hcnt_loc; shrincs_fxmss_next_loc;
      shrincs_fxmss_done_loc;
    shrincs_fxmss_rom_loc; shrincs_fxmss_sd_loc; shrincs_fxmss_rt_loc;
      leaf_ctx_roots_loc].

Definition leaf_ctx_tree (sp : shrincs_fxmss_structure) (roots : seq (bytes 16)) :=
  bt_posmap (fun p _ => nth (zeros 16) roots (leaf_slot sp (shrincs_fxmss_path_coord
    p)))
    [::] (shrincs_fxmss_tree_shape sp.1 sp.2).

Definition leaf_ctx_auth pp sp roots (a : shrincs_fxmss_coord) :=
  cons_ap (shrincs_fxmss_tree_node_hash shrincs_fxmss_sha256 pp) [::] (leaf_ctx_tree sp
    roots)
    (shrincs_fxmss_signature_path (Z.to_nat (wunsigned a.1)) (wunsigned a.2)).

Definition leaf_ctx_case (st : shrincs_fxmss_state) (roots : seq (bytes 16))
    (a : shrincs_fxmss_coord) (md : bytes 32) (sg : shrincs_fxmss_bytes) :=
  omap (fun node => extract (shrincs_fxmss_tree_node_hash shrincs_fxmss_sha256 st.1.1.1)
    [::]
    (leaf_ctx_tree st.2 roots)
    (shrincs_fxmss_signature_path (Z.to_nat (wunsigned a.1)) (wunsigned a.2))
    (shrincs_fxmss_signature_auth (Z.to_nat (wunsigned a.1)) sg) node)
    (shrincs_fxmss_leaf_recover shrincs_fxmss_sha256 a false (uint U8 0) st.1.1.1 md
      (slice sg 0 (2 + WOTS_C_CHAINS_SIZE))).

Definition leaf_ctx_gen (setup : shrincs_fxmss_setup) : raw_code (bytes 48) :=
  sto ← get shrincs_fxmss_st_loc ;;
  #assert ~~ isSome sto ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
  ks ← shrincs_fxmss_secret_dist shrincs_fxmss_sha256 ;;
  kp ← shrincs_fxmss_secret_dist shrincs_fxmss_sha256 ;;
  sd ← shrincs_fxmss_sample_digests shrincs_fxmss_sha256 (shrincs_fxmss_schedule
    setup.1) ;;
  pub ← call [ known_message_gen ] : { shrincs_fxmss_structure ×
    shrincs_fxmss_digest_table ~>
    leaf_opening_public }
    (setup.1, sd) ;;
  let pp := pub.1 in
  let root := val_bt (shrincs_fxmss_tree_node_hash shrincs_fxmss_sha256 pp) [::]
    (leaf_ctx_tree setup.1 pub.2) in
  #put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_sd_loc := sd ;;
  #put leaf_ctx_roots_loc := pub.2 ;;
  ret [tuple of pp ++ setup.2 ++ root].

Definition leaf_ctx_sign Q (cm : shrincs_fxmss_message) : raw_code ('option
  shrincs_fxmss_bytes) :=
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
      _ ← getSome shrincs_fxmss_ks_loc ;;
      _ ← getSome shrincs_fxmss_kp_loc ;;
      rt ← get shrincs_fxmss_rt_loc ;;
      let pp := st.1.1.1 in
      let bm := shrincs_fxmss_bound_message cm in
      r ← (match getm rt (a, bm) with
            | Some r => ret r
            | None => shrincs_fxmss_secret_dist shrincs_fxmss_sha256
            end) ;;
      #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
      sd ← get shrincs_fxmss_sd_loc ;;
      md ← (match getm sd a with
             | Some md => ret md
             | None => shrincs_fxmss_digest_dist shrincs_fxmss_sha256
             end) ;;
      mp ← get shrincs_fxmss_rom_loc ;;
      #put shrincs_fxmss_rom_loc := setm mp (r, ((pp, st.1.2), (a, bm))) md ;;
      ws ← call [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } q ;;
      roots ← get leaf_ctx_roots_loc ;;
      match ws, leaf_ctx_auth pp st.2 roots a with
      | Some ws, Some ap =>
          ret (shrincs_sf_encode a.1 r a.2
            (tval ws ++ flatten [seq tval n | n <- rev ap]))
      | _, _ => ret None
      end
    end
  else ret None.

Definition leaf_ctx_hash Q (x : shrincs_fxmss_hmsg_input) :
    raw_code ('option (bytes 32)) :=
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  hc ← get shrincs_fxmss_hcnt_loc ;;
  #assert hc < shrincs_fxmss_hash_budget Q ;;
  #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
  if Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111) then
    md ← shrincs_fxmss_lookup shrincs_fxmss_sha256 x ;; ret (Some md)
  else ret None.

Definition leaf_ctx_forge_query (cm : shrincs_fxmss_message) (sg : shrincs_fxmss_bytes)
  :
    raw_code ('option leaf_opening_opening) :=
  st ← getSome shrincs_fxmss_st_loc ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #put shrincs_fxmss_done_loc := true ;;
  lg ← get shrincs_fxmss_log_loc ;;
  sd ← get shrincs_fxmss_sd_loc ;;
  rt ← get shrincs_fxmss_rt_loc ;;
  roots ← get leaf_ctx_roots_loc ;;
  if shrincs_fxmss_message_valid cm then
    match shrincs_sf_parse sg with
    | Some (h, r, i, fsig) =>
      let a := (h, i) in
      let pp := st.1.1.1 in
      let bm := shrincs_fxmss_bound_message cm in
      md ← shrincs_fxmss_lookup shrincs_fxmss_sha256 (r, ((pp, st.1.2), (a, bm))) ;;
      if shrincs_fxmss_verify shrincs_fxmss_sha256 pp st.1.2 a fsig md &&
        (cm \notin lg) &&
        ~~ ((md \in codomm sd) && (getm rt (a, bm) != Some r)) then
        match leaf_ctx_case st roots a md fsig with
        | Some FAnchor => ret (Some (leaf_slot st.2 a,
            (md, slice fsig 0 (2 + WOTS_C_CHAINS_SIZE))))
        | _ => ret None
        end
      else ret None
    | None => ret None
    end
  else ret None.

Definition leaf_ctx_forge cm sg : raw_code 'bool :=
  query ← leaf_ctx_forge_query cm sg ;;
  match query with
  | Some q => call [ known_message_check ] : { leaf_opening_opening ~> 'bool } q
  | None => ret false
  end.

Lemma leaf_ctx_lookup_valid I x :
  ValidCode leaf_ctx_locs I (shrincs_fxmss_lookup shrincs_fxmss_sha256 x).
Proof. rewrite /shrincs_fxmss_lookup; ssprove_valid. Qed.

Lemma leaf_ctx_gen_valid setup :
  ValidCode leaf_ctx_locs I_known_message (leaf_ctx_gen setup).
Proof.
rewrite /leaf_ctx_gen; ssprove_valid.
exact: shrincs_fxmss_sample_digests_valid.
Qed.

Lemma leaf_ctx_sign_valid Q cm :
  ValidCode leaf_ctx_locs I_known_message (leaf_ctx_sign Q cm).
Proof. rewrite /leaf_ctx_sign; ssprove_valid. Qed.

Lemma leaf_ctx_hash_valid Q x :
  ValidCode leaf_ctx_locs I_known_message (leaf_ctx_hash Q x).
Proof.
rewrite /leaf_ctx_hash; ssprove_valid.
exact: leaf_ctx_lookup_valid.
Qed.

Lemma leaf_ctx_forge_query_valid cm sg :
  ValidCode leaf_ctx_locs I_known_message (leaf_ctx_forge_query cm sg).
Proof.
rewrite /leaf_ctx_forge_query; ssprove_valid.
exact: leaf_ctx_lookup_valid.
Qed.

Lemma leaf_ctx_forge_valid cm sg :
  ValidCode leaf_ctx_locs I_known_message (leaf_ctx_forge cm sg).
Proof.
rewrite /leaf_ctx_forge.
eapply valid_bind; first exact: leaf_ctx_forge_query_valid.
by move=> [q|]; ssprove_valid.
Qed.

Local Opaque leaf_ctx_gen leaf_ctx_sign leaf_ctx_hash leaf_ctx_forge.

Definition R_known_message (Q : shrincs_fxmss_resources) : package I_known_message
  I_forge.
Proof.
notypeclasses refine [package leaf_ctx_locs;
  [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) { leaf_ctx_gen
    setup };
  [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
    (cm) { leaf_ctx_sign Q cm };
  [ Shrincs.internal.ssprove.fxmss.games.shrincs_fxmss_op_hash ] : {
    shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) { leaf_ctx_hash Q x };
  [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool }
    '(cm, sg) {
    leaf_ctx_forge cm sg
  }
].
ssprove_valid;
  first [exact: leaf_ctx_gen_valid | exact: leaf_ctx_sign_valid |
  exact: leaf_ctx_hash_valid | exact: leaf_ctx_forge_valid].
Defined.

(* ------------------------------------------------------------------ *)
(** ** Leaf context facts *)

#[local] Open Scope nat_scope.
Lemma leaf_ctx_case_honest st kt a md sg :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  leaf_ctx_case st (leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1 kt) a md sg =
    shrincs_fxmss_full_case shrincs_fxmss_sha256 st kt a md sg.
Proof.
move=> hs.
rewrite /leaf_ctx_case /shrincs_fxmss_full_case.
have ht := leaf_value_tree_honest shrincs_fxmss_sha256 st.2 st.1.1.1 kt hs.
change (leaf_ctx_tree st.2 (leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1 kt) =
  shrincs_fxmss_value_tree shrincs_fxmss_sha256 st.1.1.1 (fun a => odflt [::] (getm kt
    a))
    st.2.1 st.2.2) in ht.
by rewrite ht.
Qed.
Lemma leaf_ctx_paired_anchor P st kt a md sg :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  keep_paired_free P st kt a md sg ->
  shrincs_fxmss_full_case P st kt a md sg = Some FAnchor.
Proof.
case: a => z i.
move=> hd hroot hv hk.
have hz : (Z.to_nat (wunsigned z) < 256)%coq_nat.
  have [hz0 hz1] := wunsigned_range z.
  change (wunsigned z < 256)%Z in hz1.
  lia.
have hi : (0 <= wunsigned i < 2^64)%Z := wunsigned_range i.
have hw := shrincs_fxmss_full_case_spec P st kt (Z.to_nat (wunsigned z))
  (wunsigned i) sg md hd hz hi hroot.
rewrite uint_to_nat wrepr_unsigned in hw.
have [node [_ hcase _]] := hw hv.
have hs : isSome (shrincs_fxmss_full_case P st kt (z, i) md sg) by rewrite hcase.
move: hk hs.
rewrite /keep_paired_free /keep_no_tree_collision /keep_no_paired_collision.
by case: (shrincs_fxmss_full_case P st kt (z, i) md sg) => [[q x y|q x v|q v|]|].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf context ud *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_ctx_ud_st := mkloc 1901 (None : option leaf_opening_state).
Definition leaf_ctx_ud_roots := mkloc 1902 ([::] : seq (bytes 16)).
Definition leaf_ctx_ud_sd := mkloc 1903 (emptym : shrincs_fxmss_digest_table).
Definition leaf_ctx_ud_cache := mkloc 1904 ([::] : seq (option leaf_opening_signature)).
Definition leaf_ctx_ud_log := mkloc 1905 ([::] : seq nat).
Definition leaf_ctx_ud_locs :=
  [fmap leaf_ctx_ud_st; leaf_ctx_ud_roots; leaf_ctx_ud_sd;
    leaf_ctx_ud_cache; leaf_ctx_ud_log].

Definition leaf_ctx_ud_one (sp : shrincs_fxmss_structure) (a : shrincs_fxmss_coord) :
    raw_code ('option leaf_opening_signature) :=
  sg ← call [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature } tt ;;
  ret (omap (fun cs => wcp_sig_encode
    (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) (cs.2, cs.1))
      sg).

Definition leaf_ctx_ud_gen (sp : shrincs_fxmss_structure) (sd :
  shrincs_fxmss_digest_table) :
    raw_code leaf_opening_public :=
  sto ← get leaf_ctx_ud_st ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  pub ← call [ leaf_prepared_gen ] :
    { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~> fixed_public } (sp, sd) ;;
  cache ← query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp) ;;
  #put leaf_ctx_ud_st := Some (pub.1, sp) ;;
  #put leaf_ctx_ud_roots := pub.2 ;;
  #put leaf_ctx_ud_sd := sd ;;
  #put leaf_ctx_ud_cache := cache ;;
  ret pub.

Definition leaf_ctx_ud_sign (j : nat) : raw_code ('option leaf_opening_signature) :=
  st ← getSome leaf_ctx_ud_st ;;
  #assert j < size (shrincs_fxmss_schedule st.2) ;;
  log ← get leaf_ctx_ud_log ;;
  #assert j \notin log ;;
  #put leaf_ctx_ud_log := j :: log ;;
  cache ← get leaf_ctx_ud_cache ;;
  ret (nth None cache j).

Definition leaf_ctx_ud_check (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome leaf_ctx_ud_st ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  roots ← get leaf_ctx_ud_roots ;;
  sd ← get leaf_ctx_ud_sd ;;
  let a := leaf_coord_at st.2 q.1 in
  ret ((leaf_recover shrincs_fxmss_sha256 st.2 st.1 a q.2.1 q.2.2 ==
    Some (nth (zeros 16) roots q.1)) &&
    known_message_gate shrincs_fxmss_sha256 st.2 st.1 a (leaf_committed_digest sd a)
      q.2.1).

Lemma leaf_ctx_ud_one_valid sp a :
  ValidCode leaf_ctx_ud_locs I_leaf_prepared_ud (leaf_ctx_ud_one sp a).
Proof. rewrite /leaf_ctx_ud_one; ssprove_valid. Qed.

Lemma leaf_ctx_ud_batch_valid sp ats :
  ValidCode leaf_ctx_ud_locs I_leaf_prepared_ud
    (query_list (leaf_ctx_ud_one sp) ats).
Proof.
elim: ats => [|a ats ih]; cbn [query_list]; first exact: valid_ret.
eapply valid_bind; first exact: leaf_ctx_ud_one_valid.
move=> sg; eapply valid_bind; first exact: ih.
move=> sgs; exact: valid_ret.
Qed.

Lemma leaf_ctx_ud_gen_valid sp sd :
  ValidCode leaf_ctx_ud_locs I_leaf_prepared_ud (leaf_ctx_ud_gen sp sd).
Proof.
rewrite /leaf_ctx_ud_gen; ssprove_valid.
exact: leaf_ctx_ud_batch_valid.
Qed.

Lemma leaf_ctx_ud_sign_valid I j :
  ValidCode leaf_ctx_ud_locs I (leaf_ctx_ud_sign j).
Proof. rewrite /leaf_ctx_ud_sign; ssprove_valid. Qed.

Lemma leaf_ctx_ud_check_valid I q :
  ValidCode leaf_ctx_ud_locs I (leaf_ctx_ud_check q).
Proof. rewrite /leaf_ctx_ud_check; ssprove_valid. Qed.

Local Opaque leaf_ctx_ud_gen leaf_ctx_ud_sign leaf_ctx_ud_check.

Definition C_leaf_roots (bit : bool) : package I_leaf_prepared_ud I_known_message.
Proof.
notypeclasses refine [package leaf_ctx_ud_locs;
  [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
    leaf_opening_public }
    '(sp, sd) {
    leaf_ctx_ud_gen sp sd
  };
  [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
    leaf_ctx_ud_sign j };
  [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
    v ← leaf_ctx_ud_check q ;; ret (bit && v)
  };
  [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
    call [ EVAL ] : { leaf_opening_eval_input ~> bytes 16 } q
  }
].
ssprove_valid;
  first [exact: leaf_ctx_ud_gen_valid | exact: leaf_ctx_ud_sign_valid |
  exact: leaf_ctx_ud_check_valid].
Defined.

Lemma resolve_leaf_ctx_ud_gen bit sp sd :
  resolve (C_leaf_roots bit)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      leaf_opening_public)) (sp, sd) =
    leaf_ctx_ud_gen sp sd.
Proof. by rewrite /C_leaf_roots /resolve /= coerce_kleisliE. Qed.

Lemma resolve_leaf_ctx_ud_sign bit j :
  resolve (C_leaf_roots bit)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    leaf_ctx_ud_sign j.
Proof. by rewrite /C_leaf_roots /resolve /= coerce_kleisliE. Qed.

Lemma resolve_leaf_ctx_ud_check bit q :
  resolve (C_leaf_roots bit)
    (known_message_check, (leaf_opening_opening, 'bool)) q =
    (v ← leaf_ctx_ud_check q ;; ret (bit && v)).
Proof. by rewrite /C_leaf_roots /resolve /= coerce_kleisliE. Qed.

Lemma resolve_leaf_ctx_ud_eval bit q :
  resolve (C_leaf_roots bit)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (call [ EVAL ] : { leaf_opening_eval_input ~> bytes 16 } q).
Proof. by rewrite /C_leaf_roots /resolve /= coerce_kleisliE. Qed.

Definition R_leaf_roots (Q : shrincs_fxmss_resources) (bit : bool) :
    package I_leaf_prepared_ud I_forge.
Proof.
pose C := (R_known_message Q ∘ known_message_coll_filter ∘ C_leaf_roots bit)%sep.
refine (@mkpackage _ _ (loc C) C _).
unfold C.
eapply valid_sep_link_weak.
- exact: (pack_valid (R_known_message Q)).
- eapply valid_sep_link_weak.
  + exact: (pack_valid known_message_coll_filter).
  + exact: (pack_valid (C_leaf_roots bit)).
  + exact: fsubmapxx.
- exact: fsubmapxx.
Defined.

Lemma R_leaf_roots_nom Q bit :
  as_nom (R_leaf_roots Q bit) =
    (R_known_message Q ∘ known_message_coll_filter ∘ C_leaf_roots bit)%sep.
Proof. apply: eq_nom_package; reflexivity. Qed.
