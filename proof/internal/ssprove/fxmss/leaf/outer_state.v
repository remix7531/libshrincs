(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.outer_state

    Paths, cached signatures and committed roots establish the outer leaf-context
    invariant. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs.internal.ssprove.lib.math Require Import
  bin_tree tree_paths full_tree_paths merkle tree_lookup.
From Shrincs Require Import spec schemes games.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games scheme model.nodes model.auth tree.encoding tree.model leaf.paths
  leaf.context paired.routing instance tree.nodes leaf.opening leaf.known_message_game
    tree.forgery
  leaf.commitments tree.classify leaf.known_message paired.targets paired.reduction.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt PeanoNat Lia.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context paths *)

#[local] Open Scope nat_scope.

Lemma leaf_outer_balanced_path d p :
  size p = d -> p \in leaf_paths (shrincs_fxmss_tree_shape true d).
Proof.
elim: d p => [|d ih] [|b p] //= hs.
rewrite mem_cat; apply/orP.
case: b.
- right; apply/mapP; exists p; first by apply: ih; case: hs.
  by [].
- left; apply/mapP; exists p; first by apply: ih; case: hs.
  by [].
Qed.

Lemma leaf_outer_spine_last d : nseq d false \in leaf_paths (shrincs_fxmss_tree_shape
  false d).
Proof.
elim: d => [|d ih]; first by rewrite inE.
rewrite /= mem_cat; apply/orP; left.
by apply/mapP; exists (nseq d false).
Qed.

Lemma leaf_outer_spine_right d q :
  q < d -> rcons (nseq q false) true \in leaf_paths (shrincs_fxmss_tree_shape false d).
Proof.
elim: d q => [|d ih] [|q] //= hq.
- by rewrite mem_cat inE eqxx orbT.
- rewrite mem_cat; apply/orP; left.
  by apply/mapP; exists (rcons (nseq q false) true); first exact: ih.
Qed.

Lemma leaf_outer_schedule_path sp a :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  exists p, p \in leaf_paths (shrincs_fxmss_tree_shape sp.1 sp.2) /\
    shrincs_fxmss_path_coord p = a.
Proof.
move=> hd ha.
have [hq <-] := leaf_schedule_slot sp a hd ha.
set q := leaf_slot sp a in hq *.
move: hq; move: q => q hq.
case: sp hd hq {ha} => [[|] d] hd hq /=.
- exists (path_of_idx d q); split.
  + by apply: leaf_outer_balanced_path; rewrite size_path_of_idx.
  + by rewrite /shrincs_fxmss_path_coord /leaf_coord_at /= size_path_of_idx
    idx_of_path_of_idx.
- rewrite /leaf_coord_at /=.
  case hqd: (q == d).
  + exists (nseq d false); split; first exact: leaf_outer_spine_last.
    by rewrite /shrincs_fxmss_path_coord size_nseq idx_of_path_false.
  + have hlt : q < d by move: hq; rewrite ltnS => hq; rewrite ltn_neqAle hqd hq.
    exists (rcons (nseq q false) true); split; first exact: leaf_outer_spine_right.
    by rewrite /shrincs_fxmss_path_coord size_rcons size_nseq
      shrincs_fxmss_path_index_rcons idx_of_path_false.
Qed.

Lemma leaf_outer_path_shape b d p :
  shrincs_fxmss_structure_legal b d -> p \in leaf_paths (shrincs_fxmss_tree_shape b d)
    ->
  shrincs_fxmss_spec_on_shape b d (255-size p) (Z.of_nat (idx_of_path p)) /\
  shrincs_fxmss_spec_is_leaf b d (255-size p) (Z.of_nat (idx_of_path p)).
Proof.
move=> hd hp.
have hd255 := shrincs_fxmss_legal_depth b d hd.
move/leP: hd255=> hd255.
case: b hd hp => hd hp.
- have hs := leaf_tree_balanced_depth d p hp.
  have hi := idx_of_path_lt p.
  rewrite hs in hi *.
  have hsub : 255-(255-d) = d by rewrite !subnE; lia.
  split.
  + (* A balanced-tree leaf coordinate lies on the specified shape. *)
    rewrite /shrincs_fxmss_spec_on_shape -!subnE hsub.
    split; first (rewrite subnE; split; lia).
    split; first exact: Znat.Nat2Z.is_nonneg.
    move/ltP/Znat.Nat2Z.inj_lt: hi.
    by rewrite shape.Z_of_nat_expn2.
  + by rewrite /shrincs_fxmss_spec_is_leaf ?hsub eqxx.
- have [->|[q [hq ->]]] := leaf_tree_spine_path d p hp.
  + rewrite size_nseq idx_of_path_false.
    have hsub : 255-(255-d) = d by rewrite !subnE; lia.
    split.
    * rewrite /shrincs_fxmss_spec_on_shape -!subnE hsub.
      split; first (rewrite subnE; split; lia).
      split; first lia.
      by left.
    * by rewrite /shrincs_fxmss_spec_is_leaf ?hsub eqxx.
  + rewrite size_rcons size_nseq shrincs_fxmss_path_index_rcons idx_of_path_false /=.
    move/ltP: hq=> hq.
    split.
    * (* A right child of the spine lies on the specified shape. *)
      rewrite /shrincs_fxmss_spec_on_shape.
      split; first (rewrite !subnE; split; lia).
      split; first lia.
      right; split; first by [].
      rewrite subnE; lia.
    * by rewrite /shrincs_fxmss_spec_is_leaf /= orbT.
Qed.

Lemma leaf_outer_signature_path p :
  shrincs_fxmss_path_valid p ->
  shrincs_fxmss_signature_path (Z.to_nat (wunsigned (shrincs_fxmss_path_coord p).1))
    (wunsigned (shrincs_fxmss_path_coord p).2) = p.
Proof.
move=> /andP[hp hi].
rewrite /shrincs_fxmss_signature_path /shrincs_fxmss_path_coord /=
  shrincs_fxmss_spec_uint8_nat;
  first by rewrite subnE; lia.
rewrite (shrincs_fxmss_uint64_nat _ hi) subKn //.
exact: path_of_idx_of_path.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context sign *)

#[local] Open Scope nat_scope.

Lemma leaf_outer_sign_honest sp pp kt a md :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  shrincs_fxmss_sign shrincs_fxmss_sha256 md (fun c => odflt [::] (getm kt c))
    a.2 a.1 pp sp.1 (uint U8 sp.2) =
  match leaf_sign_at shrincs_fxmss_sha256 sp pp a (odflt [::] (getm kt a)) md,
        leaf_ctx_auth pp sp (leaf_opening_roots shrincs_fxmss_sha256 sp pp kt) a with
  | Some ws, Some ap => Some (ws ++ flatten [seq tval n | n <- rev ap])
  | _, _ => None
  end.
Proof.
move=> hsp ha.
have hd := (proj1 (shrincs_fxmss_legal_shapeP sp.1 sp.2)) hsp.
have [p [hp <-]] := leaf_outer_schedule_path sp a hsp ha.
have hvalid : shrincs_fxmss_path_valid p.
  apply: shrincs_fxmss_full_path_valid hsp _.
  by rewrite full_paths_mem hp orbT.
have [hs hl] := leaf_outer_path_shape sp.1 sp.2 p hsp hp.
have /andP[hp255 hi64] := hvalid.
have ht := leaf_value_tree_honest shrincs_fxmss_sha256 sp pp kt hsp.
change (leaf_ctx_tree sp (leaf_opening_roots shrincs_fxmss_sha256 sp pp kt) =
  shrincs_fxmss_value_tree shrincs_fxmss_sha256 pp (fun c => odflt [::] (getm kt c))
    sp.1 sp.2) in ht.
rewrite /leaf_ctx_auth ht (leaf_outer_signature_path p hvalid).
have hleaf : p \in leaf_paths (shrincs_fxmss_value_tree shrincs_fxmss_sha256 pp
    (fun c => odflt [::] (getm kt c)) sp.1 sp.2) by rewrite
      shrincs_fxmss_value_tree_leaf.
have hsub := leaf_paths_correct hleaf.
rewrite /leaf_at in hsub.
case he: (subtree_at (shrincs_fxmss_value_tree shrincs_fxmss_sha256 pp
    (fun c => odflt [::] (getm kt c)) sp.1 sp.2) p) => [u|] in hsub;
  last by [].
have hap := @isSome_cons_ap (bytes 16) (shrincs_fxmss_tree_node_hash
  shrincs_fxmss_sha256 pp) [::]
  (shrincs_fxmss_value_tree shrincs_fxmss_sha256 pp (fun c => odflt [::] (getm kt c))
    sp.1 sp.2) p.
rewrite he in hap.
case ea: (cons_ap _ _ _ _) => [ap|] in hap *; last by [].
have hrev := @shrincs_fxmss_cons_ap_honest shrincs_fxmss_sha256 (fun c => odflt [::]
  (getm kt c))
  pp sp.1 sp.2 p u ap (255-size p) (Z.of_nat (idx_of_path p))
  hd hp255 erefl erefl he ea.
rewrite hrev.
exact: shrincs_fxmss_sign_eq hd hs hl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context sign defs *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition leaf_outer_full_sign P Q (cm : shrincs_fxmss_message) : raw_code ('option
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
      else ret None.

Lemma leaf_outer_full_signE P Q keep bit cm :
  resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
    (shrincs_fxmss_message, 'option
    shrincs_fxmss_bytes)) cm =
  leaf_outer_full_sign P Q cm.
Proof. by rewrite /G_forge_full_signature /resolve /= coerce_kleisliE. Qed.

Definition leaf_outer_sign_left (st : shrincs_fxmss_state) (cm : shrincs_fxmss_message)
  (a : shrincs_fxmss_coord) : raw_code ('option shrincs_fxmss_bytes) :=
            ks ← getSome shrincs_fxmss_ks_loc ;;
            kp ← getSome shrincs_fxmss_kp_loc ;;
            kt ← get shrincs_fxmss_keys_loc ;;
            let pp := st.1.1.1 in
            let bm := shrincs_fxmss_bound_message cm in
            rt ← get shrincs_fxmss_rt_loc ;;
            ro ← (match getm rt (a, bm) with
                  | Some r => ret (Some r)
                  | None => r ← shrincs_fxmss_secret_dist shrincs_fxmss_sha256 ;; ret
                    (Some r)
                  end) ;;
            match ro with
            | None => ret None
            | Some r =>
                #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
                let x := (r, ((pp, st.1.2), (a, bm))) in
                md ← (sd ← get shrincs_fxmss_sd_loc ;;
                      md ← (match getm sd a with
                            | Some md => ret md
                            | None => md ← shrincs_fxmss_digest_dist
                              shrincs_fxmss_sha256 ;; ret md
                            end) ;;
                      mp ← get shrincs_fxmss_rom_loc ;;
                      #put shrincs_fxmss_rom_loc := setm mp x md ;;
                      ret md) ;;
                let keys := shrincs_fxmss_lookup_keys shrincs_fxmss_sha256 true st ks kt
                  in
                match shrincs_fxmss_sign shrincs_fxmss_sha256 md keys a.2 a.1 pp
                        st.2.1 (uint U8 st.2.2) with
                | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
                | None => ret None
                end
            end.

Definition leaf_outer_sign_right (st : shrincs_fxmss_state) q (cm :
  shrincs_fxmss_message) (a : shrincs_fxmss_coord) : raw_code ('option
  shrincs_fxmss_bytes) :=
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
      end.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context gen defs *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition leaf_outer_full_gen P (setup : shrincs_fxmss_setup) : raw_code (bytes 48) :=
sto ← get shrincs_fxmss_st_loc ;;
#assert ~~ isSome sto ;;
done ← get shrincs_fxmss_done_loc ;;
#assert ~~ done ;;
#assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
pp ← shrincs_fxmss_public_seed_dist P ;;
ks ← shrincs_fxmss_secret_dist P ;;
kp ← shrincs_fxmss_secret_dist P ;;
kt ← shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1) ;;
sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule setup.1) ;;
let st0 := ((pp, setup.2, zeros 16), setup.1) in
let keys := shrincs_fxmss_lookup_keys P true st0 ks kt in
let ro := shrincs_fxmss_node P keys (uint U64 0) (uint U8 255)
    pp setup.1.1 (uint U8 setup.1.2) in
#assert isSome ro ;;
let root := odflt (zeros 16) ro in
#put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
#put shrincs_fxmss_ks_loc := Some ks ;;
#put shrincs_fxmss_kp_loc := Some kp ;;
#put shrincs_fxmss_keys_loc := kt ;;
#put shrincs_fxmss_sd_loc := sd ;;
ret [tuple of pp ++ setup.2 ++ root].

Lemma leaf_outer_full_genE P Q keep bit setup :
  resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_gen,
    (shrincs_fxmss_setup, bytes 48))
    setup =
  leaf_outer_full_gen P setup.
Proof. by rewrite /G_forge_full_signature /resolve /= coerce_kleisliE. Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context invariant *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_outer_private : Locations :=
  [fmap shrincs_fxmss_keys_loc; leaf_opening_st_loc; leaf_opening_pp_loc;
    leaf_opening_keys_loc;
    leaf_opening_slog_loc; known_message_sd_loc; known_message_cache_loc;
      leaf_ctx_roots_loc].

Record leaf_outer_ready (st : shrincs_fxmss_state) (kt : shrincs_fxmss_key_table) (sd :
  shrincs_fxmss_digest_table)
    (mst : option leaf_opening_state) (po : option (bytes 16)) (mkt :
      shrincs_fxmss_key_table)
    (msd : shrincs_fxmss_digest_table) (cache : seq (option leaf_opening_signature))
    (roots : seq (bytes 16)) : Prop := {
  lor_legal : shrincs_fxmss_structure_legal st.2.1 st.2.2;
  lor_root : st.1.2 = shrincs_fxmss_honest_node shrincs_fxmss_sha256 (fun a => odflt
    [::] (getm kt a))
    st.1.1.1 st.2.1 st.2.2 255 0%Z;
  lor_total : leaf_digest_total (shrincs_fxmss_schedule st.2) sd;
  lor_state : mst = Some (st.1.1.1, st.2);
  lor_seed : po = Some st.1.1.1;
  lor_keys : mkt = kt;
  lor_digests : msd = sd;
  lor_cache : cache = known_message_cache shrincs_fxmss_sha256 st.2 st.1.1.1 sd kt;
  lor_roots : roots = leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1 kt
}.

Definition leaf_outer_rel (sto : option shrincs_fxmss_state) kt sd rt lg q
    mst po mkt slog msd cache roots : Prop :=
  [/\ known_message_log_consistent rt lg,
      all (fun j => j < q) slog &
      match sto with
      | None => mst = None /\ po = None
      | Some st => leaf_outer_ready st kt sd mst po mkt msd cache roots
      end].

Definition leaf_outer_inv : precond :=
  heap_ignore leaf_outer_private ⋊
  rel_app [:: (rhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_keys_loc); (rhs,
    shrincs_fxmss_sd_loc);
    (rhs, shrincs_fxmss_rt_loc); (rhs, shrincs_fxmss_log_loc); (rhs,
      shrincs_fxmss_next_loc);
    (rhs, leaf_opening_st_loc); (rhs, leaf_opening_pp_loc); (rhs,
      leaf_opening_keys_loc);
    (rhs, leaf_opening_slog_loc); (rhs, known_message_sd_loc); (rhs,
      known_message_cache_loc);
    (rhs, leaf_ctx_roots_loc)] leaf_outer_rel.

Arguments leaf_outer_inv : simpl never.

Lemma leaf_outer_invE h0 h1 : leaf_outer_inv (h0,h1) ->
  heap_ignore leaf_outer_private (h0,h1) /\
  leaf_outer_rel (get_heap h1 shrincs_fxmss_st_loc) (get_heap h0 shrincs_fxmss_keys_loc)
    (get_heap h1 shrincs_fxmss_sd_loc) (get_heap h1 shrincs_fxmss_rt_loc) (get_heap h1
      shrincs_fxmss_log_loc)
    (get_heap h1 shrincs_fxmss_next_loc) (get_heap h1 leaf_opening_st_loc) (get_heap h1
      leaf_opening_pp_loc)
    (get_heap h1 leaf_opening_keys_loc) (get_heap h1 leaf_opening_slog_loc)
    (get_heap h1 known_message_sd_loc) (get_heap h1 known_message_cache_loc) (get_heap
      h1 leaf_ctx_roots_loc).
Proof. by move=> [he hr]; split. Qed.

Lemma leaf_outer_inv_get l :
  l.1 \notin domm leaf_outer_private -> get_pre_cond l leaf_outer_inv.
Proof. move=> hl h0 h1 /leaf_outer_invE[he _]; exact: he l hl. Qed.

Local Opaque leaf_outer_rel.
Lemma leaf_outer_inv_put (l : Location) (v : l) :
  l.1 \notin [:: 1300; 1303; 1310; 1311; 1304; 1307;
    1500; 1501; 1502; 1503; 1510; 1511; 1900] ->
  put_pre_cond l v leaf_outer_inv.
Proof.
move=> hl.
rewrite /leaf_outer_inv.
apply: put_pre_cond_conj; first exact: put_pre_cond_heap_ignore.
apply: put_pre_cond_rel_app.
exact hl.
Qed.

Lemma leaf_outer_inv_initial : leaf_outer_inv (empty_heap, empty_heap).
Proof.
rewrite /leaf_outer_inv; split; first by move=> l hl.
change (leaf_outer_rel None emptym emptym emptym [::] 0 None None emptym [::] emptym [::] [::]).
split; [exact: known_message_log_empty | by [] | by split].
Qed.

Lemma leaf_outer_invI h0 h1 :
  heap_ignore leaf_outer_private (h0,h1) /\
  leaf_outer_rel (get_heap h1 shrincs_fxmss_st_loc) (get_heap h0 shrincs_fxmss_keys_loc)
    (get_heap h1 shrincs_fxmss_sd_loc) (get_heap h1 shrincs_fxmss_rt_loc) (get_heap h1
      shrincs_fxmss_log_loc)
    (get_heap h1 shrincs_fxmss_next_loc) (get_heap h1 leaf_opening_st_loc) (get_heap h1
      leaf_opening_pp_loc)
    (get_heap h1 leaf_opening_keys_loc) (get_heap h1 leaf_opening_slog_loc)
    (get_heap h1 known_message_sd_loc) (get_heap h1 known_message_cache_loc) (get_heap
      h1 leaf_ctx_roots_loc) -> leaf_outer_inv (h0,h1).
Proof. by move=> [he hr]; split. Qed.

Lemma leaf_outer_log_put h0 h1 cm lg :
  leaf_outer_inv (h0,h1) -> get_heap h1 shrincs_fxmss_log_loc = lg ->
  leaf_outer_inv (set_heap h0 shrincs_fxmss_log_loc (cm :: lg), set_heap h1
    shrincs_fxmss_log_loc (cm :: lg)).
Proof.
move/leaf_outer_invE=> [he hr] hlg.
apply: leaf_outer_invI; split; first exact: put_pre_cond_heap_ignore he.
repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
case: hr => hlog hslots hready.
rewrite hlg in hlog.
split=> //; exact: known_message_log_cons hlog.
Qed.

Lemma leaf_outer_next_put h0 h1 q :
  leaf_outer_inv (h0,h1) -> get_heap h1 shrincs_fxmss_next_loc <= q ->
  leaf_outer_inv (set_heap h0 shrincs_fxmss_next_loc q, set_heap h1
    shrincs_fxmss_next_loc q).
Proof.
move/leaf_outer_invE=> [he hr] hq.
apply: leaf_outer_invI; split; first exact: put_pre_cond_heap_ignore he.
repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
case: hr => hlog hslots hready.
split=> //.
apply/allP=> j hj; exact: leq_trans (allP hslots j hj) hq.
Qed.

Lemma leaf_outer_slog_put h0 h1 q slog :
  leaf_outer_inv (h0,h1) -> get_heap h1 leaf_opening_slog_loc = slog ->
  q < get_heap h1 shrincs_fxmss_next_loc ->
  leaf_outer_inv (h0, set_heap h1 leaf_opening_slog_loc (q :: slog)).
Proof.
move/leaf_outer_invE=> [he hr] hsl hq.
apply: leaf_outer_invI; split.
- apply: heap_ignore_set_r he.
  by rewrite /leaf_outer_private mem_domm.
- repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  case: hr => hlog hslots hready.
  rewrite hsl in hslots.
  split=> //; by rewrite /= hq hslots.
Qed.

Lemma leaf_outer_log_set_mem rt lg a cm r :
  shrincs_fxmss_message_valid cm -> cm \in lg -> known_message_log_consistent rt lg ->
  known_message_log_consistent (setm rt (a, shrincs_fxmss_bound_message cm) r) lg.
Proof.
move=> hcm hmem hlog a' cm' r' hcm'.
rewrite setmE; case: ifP => [/eqP he|hne] hr.
- have hecm := shrincs_fxmss_bound_message_inj cm' cm hcm' hcm (congr1 snd he).
  by rewrite hecm.
- exact: hlog a' cm' r' hcm' hr.
Qed.

Lemma leaf_outer_rt_put h0 h1 rt a cm r :
  leaf_outer_inv (h0,h1) -> get_heap h1 shrincs_fxmss_rt_loc = rt ->
  shrincs_fxmss_message_valid cm -> cm \in get_heap h1 shrincs_fxmss_log_loc ->
  leaf_outer_inv (set_heap h0 shrincs_fxmss_rt_loc (setm rt (a,
    shrincs_fxmss_bound_message cm) r),
    set_heap h1 shrincs_fxmss_rt_loc (setm rt (a, shrincs_fxmss_bound_message cm) r)).
Proof.
move/leaf_outer_invE=> [he hr] hrt hcm hmem.
apply: leaf_outer_invI; split; first exact: put_pre_cond_heap_ignore he.
repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
case: hr => hlog hslots hready.
rewrite hrt in hlog.
split=> //; exact: leaf_outer_log_set_mem hcm hmem hlog.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context facts *)

#[local] Open Scope nat_scope.

Lemma leaf_outer_anchor P st kt a md sg :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0%Z ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  shrincs_fxmss_full_case P st kt a md sg = Some FAnchor ->
  a \in shrincs_fxmss_schedule st.2 /\
  leaf_win P st.2 st.1.1.1 a md
    (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) (odflt [::] (getm kt a)).
Proof.
move=> hsp hroot hv hc.
have hd := (proj1 (shrincs_fxmss_legal_shapeP st.2.1 st.2.2)) hsp.
have [node [hleaf hs]] := shrincs_fxmss_full_case_extract P st kt a md sg FAnchor hd
  hroot hv hc.
change (subtree_at (shrincs_fxmss_value_tree P st.1.1.1
  (fun c => odflt [::] (getm kt c)) st.2.1 st.2.2)
  (shrincs_fxmss_signature_path (Z.to_nat (wunsigned a.1)) (wunsigned a.2)) =
  Some (BLeaf node)) in hs.
have hpcoord := shrincs_fxmss_verified_path_coord P st.1.1.1 st.1.2 a sg md hv.
have hp := leaf_pathsP hs.
rewrite shrincs_fxmss_value_tree_leaf in hp.
have ha := leaf_tree_path_scheduled st.2.1 st.2.2 _ hsp hp.
rewrite hpcoord in ha.
split; first exact: ha.
have hn : node = leaf_pk P st.2 st.1.1.1 a (odflt [::] (getm kt a)).
  have he : leaf_at (shrincs_fxmss_value_tree P st.1.1.1
      (fun c => odflt [::] (getm kt c)) st.2.1 st.2.2)
      (shrincs_fxmss_signature_path (Z.to_nat (wunsigned a.1)) (wunsigned a.2)) = Some
        node.
  { by rewrite /leaf_at hs. }
  rewrite /shrincs_fxmss_value_tree leaf_at_posmap cat0s hpcoord in he.
  by case: (leaf_at _ _) he => [[]|] //= [<-].
change (shrincs_fxmss_leaf_recover P a false (uint U8 0) st.1.1.1 md
  (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) ==
  Some (leaf_pk P st.2 st.1.1.1 a (odflt [::] (getm kt a)))).
by rewrite hleaf hn.
Qed.

Lemma leaf_outer_keep P st kt a md sg :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0%Z ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  keep_paired_free P st kt a md sg =
    if shrincs_fxmss_full_case P st kt a md sg is Some FAnchor then true else false.
Proof.
move=> hsp hroot hv.
have hd := (proj1 (shrincs_fxmss_legal_shapeP st.2.1 st.2.2)) hsp.
case hk: (keep_paired_free P st kt a md sg).
- by rewrite (leaf_ctx_paired_anchor P st kt a md sg hd hroot hv hk).
- move: hk.
  rewrite /keep_paired_free /keep_no_tree_collision /keep_no_paired_collision.
  by case: (shrincs_fxmss_full_case P st kt a md sg) => [[q x y|q x v|q v|]|].
Qed.

Lemma leaf_outer_opening P st kt sd rt lg cm r a md sg :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0%Z ->
  leaf_digest_total (shrincs_fxmss_schedule st.2) sd -> known_message_log_consistent rt
    lg ->
  shrincs_fxmss_message_valid cm -> cm \notin lg ->
  ~~ ((md \in codomm sd) && (getm rt (a, shrincs_fxmss_bound_message cm) != Some r)) ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  shrincs_fxmss_full_case P st kt a md sg = Some FAnchor ->
  [/\ leaf_slot st.2 a < size (shrincs_fxmss_schedule st.2),
      leaf_coord_at st.2 (leaf_slot st.2 a) = a &
      leaf_win P st.2 st.1.1.1 a md
        (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) (odflt [::] (getm kt a)) &&
      known_message_gate P st.2 st.1.1.1 a (leaf_committed_digest sd a) md].
Proof.
move=> hsp hroot hsd hlog hm hnot hveto hv hc.
have [ha hw] := leaf_outer_anchor P st kt a md sg hsp hroot hv hc.
have [hj he] := leaf_schedule_slot st.2 a hsp ha.
have hsome : isSome (getm sd a).
{ exact: (allP hsd a ha). }
have hg := known_message_population_gate P st.2 st.1.1.1 a sd rt lg cm r md
  hlog hm hnot hsome hveto.
split=> //.
- by rewrite (leaf_schedule_length st.2 hsp).
- by rewrite hw hg.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context init *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_outer_init (po : option (bytes 16)) : precond :=
  fun '(h0,h1) =>
    [/\ heap_ignore leaf_outer_private (h0,h1),
        known_message_log_consistent (get_heap h1 shrincs_fxmss_rt_loc) (get_heap h1
          shrincs_fxmss_log_loc),
        all (fun j => j < get_heap h1 shrincs_fxmss_next_loc) (get_heap h1
          leaf_opening_slog_loc),
        get_heap h1 leaf_opening_st_loc = None & get_heap h1 leaf_opening_pp_loc = po].

Lemma leaf_outer_init_from_inv h0 h1 :
  leaf_outer_inv (h0,h1) -> get_heap h1 shrincs_fxmss_st_loc = None ->
  leaf_outer_init None (h0,h1).
Proof.
move/leaf_outer_invE=> [he [hlog hslots hr]] hs.
rewrite hs in hr; case: hr=> hm hp.
by split.
Qed.

Lemma leaf_outer_init_seed h0 h1 pp :
  leaf_outer_init None (h0,h1) ->
  leaf_outer_init (Some pp) (h0, set_heap h1 leaf_opening_pp_loc (Some pp)).
Proof.
move=> [he hl hq hm hp]; split.
- apply: heap_ignore_set_r he; by rewrite /leaf_outer_private mem_domm.
- by rewrite get_set_heap_neq // get_set_heap_neq.
- by rewrite get_set_heap_neq // get_set_heap_neq.
- by rewrite get_set_heap_neq.
- exact: get_set_heap_eq.
Qed.

Definition leaf_outer_store_left (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) h :=
  set_heap (set_heap (set_heap (set_heap (set_heap h shrincs_fxmss_st_loc (Some st))
    shrincs_fxmss_ks_loc (Some ks)) shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc sd.

Definition leaf_outer_store_right (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) h :=
  set_heap (set_heap (set_heap (set_heap (set_heap (set_heap (set_heap (set_heap
    (set_heap h leaf_opening_st_loc (Some (st.1.1.1,st.2))) leaf_opening_keys_loc kt)
      known_message_sd_loc sd)
    known_message_cache_loc (known_message_cache shrincs_fxmss_sha256 st.2 st.1.1.1 sd
      kt))
      shrincs_fxmss_st_loc (Some st))
    shrincs_fxmss_ks_loc (Some ks)) shrincs_fxmss_kp_loc (Some kp)) shrincs_fxmss_sd_loc
      sd)
    leaf_ctx_roots_loc (leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1 kt).

Lemma leaf_outer_store_inv st ks kp kt sd h0 h1 :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node shrincs_fxmss_sha256 (fun a => odflt [::] (getm kt
    a))
    st.1.1.1 st.2.1 st.2.2 255 0%Z ->
  leaf_digest_total (shrincs_fxmss_schedule st.2) sd ->
  leaf_outer_init (Some st.1.1.1) (h0,h1) ->
  leaf_outer_inv (leaf_outer_store_left st ks kp kt sd h0,
    leaf_outer_store_right st ks kp kt sd h1).
Proof.
move=> hd hroot hsd [he hlog hslots hm hp].
apply: leaf_outer_invI; split.
- (* Storing the generated state changes only private locations. *)
  rewrite /leaf_outer_store_left /leaf_outer_store_right.
  apply: heap_ignore_set_r; first by rewrite /leaf_outer_private mem_domm.
  apply: put_pre_cond_heap_ignore.
  apply: heap_ignore_set_l; first by rewrite /leaf_outer_private mem_domm.
  do 3 apply: put_pre_cond_heap_ignore.
  do 4 (apply: heap_ignore_set_r; first by rewrite /leaf_outer_private mem_domm).
  exact he.
- rewrite /leaf_outer_store_left /leaf_outer_store_right.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context oracles *)

Import Shrincs.internal.ssprove.fxmss.games.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel
  known_message_gen_body known_message_sign_body known_message_check_body.

Lemma leaf_outer_resolve_gen sp sd :
  resolve (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
    (known_message_gen,
    (shrincs_fxmss_structure × shrincs_fxmss_digest_table, leaf_opening_public)) (sp,sd)
      =
    known_message_gen_body shrincs_fxmss_sha256 sp sd.
Proof.
rewrite resolve_link /known_message_coll_filter /G_known_message /resolve /=
  coerce_kleisliE.
cbn [code_link]; rewrite !bind_ret.
by rewrite /resolve /= coerce_kleisliE ?bind_ret.
Qed.

Lemma leaf_outer_resolve_sign j :
  resolve (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
    (known_message_sign,
    ('nat, 'option leaf_opening_signature)) j =
    known_message_sign_body j.
Proof.
rewrite resolve_link /known_message_coll_filter /G_known_message /resolve /=
  coerce_kleisliE.
cbn [code_link]; rewrite !bind_ret.
by rewrite /resolve /= coerce_kleisliE ?bind_ret.
Qed.

Lemma leaf_outer_resolve_check q :
  resolve (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
    (known_message_check,
    (leaf_opening_opening, 'bool)) q =
    known_message_check_body shrincs_fxmss_sha256 q.
Proof.
rewrite resolve_link /known_message_coll_filter /G_known_message /resolve /=
  coerce_kleisliE.
cbn [code_link]; rewrite !bind_ret.
by rewrite /resolve /= coerce_kleisliE ?bind_ret.
Qed.

Lemma leaf_outer_lookup_stable P x :
  code_stable leaf_outer_inv (shrincs_fxmss_lookup P x).
Proof.
rewrite /shrincs_fxmss_lookup.
split.
- apply: leaf_outer_inv_get.
  by rewrite /leaf_outer_private; fmap_solve.
- move=> mp.
  case: (getm mp x) => [md|]; first by [].
  apply: code_stable_bind.
  + apply: (code_stable_valid emptym).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + move=> md.
    split; last by [].
    apply: leaf_outer_inv_put.
    by [].
Qed.

Lemma leaf_outer_hash_stable P Q keep bit x :
  code_stable leaf_outer_inv (resolve (G_forge_full_signature P Q keep bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x).
Proof.
rewrite /G_forge_full_signature /resolve /= coerce_kleisliE.
cbn [code_stable].
split.
- apply: leaf_outer_inv_get.
  by rewrite /leaf_outer_private; fmap_solve.
- move=> done.
  case: done.
  + by [].
  + cbn [negb assert code_stable].
    split.
    * apply: leaf_outer_inv_get.
      by rewrite /leaf_outer_private; fmap_solve.
    * move=> hc.
      case: (hc < shrincs_fxmss_hash_budget Q).
      -- cbn [assert code_stable].
         split.
         ++ apply: leaf_outer_inv_put.
            by [].
         ++ (* An allowed hash lookup preserves the outer invariant. *)
            case: (Z.leb _ _) => //.
            change (code_stable leaf_outer_inv
              (bind (shrincs_fxmss_lookup P x) (fun md => ret (Some md)))).
            apply: code_stable_bind; first exact: leaf_outer_lookup_stable.
            by move=> md.
      -- by [].
Qed.
