(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.paired.generation

    The static paired game's deterministic target-table updates, under a fixed
    hidden seed. Generate the operational FXMSS root through the static paired
    game. *)

From Shrincs.internal.ssprove.lib Require Import prelude chain.core.
From Shrincs.internal.ssprove.lib.math Require Import
  bin_tree merkle tree_paths full_tree_paths.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params tree.encoding tree.oracles paired.routing scheme shape model.nodes tree.model
  tree.generation.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Paired state *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_paired_step P h (target : tweak * seq UInt8) :=
  set_heap
    (set_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P))
      (setm (get_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P)))
        (size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)))) target))
    (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))
    (rcons (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) target.1).

Definition shrincs_fxmss_paired_heap P h targets := foldl (shrincs_fxmss_paired_step P)
  h targets.

Lemma shrincs_fxmss_paired_heap_cat P h xs ys :
  shrincs_fxmss_paired_heap P h (xs ++ ys) =
    shrincs_fxmss_paired_heap P (shrincs_fxmss_paired_heap P h xs) ys.
Proof. exact: foldl_cat. Qed.

Lemma shrincs_fxmss_paired_heap_seed P h targets :
  get_heap (shrincs_fxmss_paired_heap P h targets) (tcrx.tcrx_pp_loc
    (shrincs_fxmss_hash_function P)) =
    get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)).
Proof.
elim: targets h => [|target targets ih] h //=.
rewrite /shrincs_fxmss_paired_heap /= -/shrincs_fxmss_paired_heap ih
  /shrincs_fxmss_paired_step.
by rewrite !get_set_heap_neq.
Qed.

Lemma shrincs_fxmss_paired_heap_revealed P h targets :
  get_heap (shrincs_fxmss_paired_heap P h targets) tcrx.tcrx_rev_loc =
    get_heap h tcrx.tcrx_rev_loc.
Proof.
elim: targets h => [|target targets ih] h //=.
rewrite /shrincs_fxmss_paired_heap /= -/shrincs_fxmss_paired_heap ih
  /shrincs_fxmss_paired_step.
by rewrite !get_set_heap_neq.
Qed.

Lemma shrincs_fxmss_paired_heap_tweaks P h targets :
  get_heap (shrincs_fxmss_paired_heap P h targets) (tcrx.tcrx_tws_loc
    (shrincs_fxmss_hash_function P)) =
    get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 targets.
Proof.
elim: targets h => [|target targets ih] h; first by rewrite cats0.
rewrite /shrincs_fxmss_paired_heap /= -/shrincs_fxmss_paired_heap ih
  /shrincs_fxmss_paired_step.
by rewrite get_set_heap_eq -cat_rcons.
Qed.

Definition shrincs_fxmss_paired_value P pp (inputs : seq bool -> seq UInt8) pos t :=
  shrincs_fxmss_commit_value P pp
    (fun p => th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak
      (shrincs_fxmss_path_coord p)) (inputs p))
    pos t.

Fixpoint shrincs_fxmss_paired_plan P pp (inputs : seq bool -> seq UInt8)
    (pos : seq bool) (t : bt unit) : seq (tweak * seq UInt8) :=
  match t with
  | BLeaf _ => [:: (shrincs_fxmss_pk_tweak (shrincs_fxmss_path_coord pos), inputs pos)]
  | BNode l r =>
      shrincs_fxmss_paired_plan P pp inputs (rcons pos true) r ++
      shrincs_fxmss_paired_plan P pp inputs (rcons pos false) l ++
      [:: (shrincs_fxmss_tree_path_tweak pos,
           shrincs_fxmss_tree_message
             (shrincs_fxmss_paired_value P pp inputs (rcons pos false) l,
              shrincs_fxmss_paired_value P pp inputs (rcons pos true) r))]
  end.

Lemma shrincs_fxmss_paired_plan_coordinates P pp inputs pos t :
  [seq shrincs_fxmss_paired_coordinate x.1 | x <- shrincs_fxmss_paired_plan P pp inputs
    pos t] =
    [seq shrincs_fxmss_path_coord p | p <- full_postorder pos t].
Proof.
elim: t pos => [u|l ihl r ihr] pos.
- by rewrite full_postorder_leaf.
- by rewrite full_postorder_node /= !map_cat /= ihl ihr.
Qed.

Lemma shrincs_fxmss_paired_plan_size P pp inputs pos t :
  size (shrincs_fxmss_paired_plan P pp inputs pos t) = 2 * bt_nleaves t - 1.
Proof.
rewrite -(size_map (fun x => shrincs_fxmss_paired_coordinate x.1)
  (shrincs_fxmss_paired_plan P pp inputs pos t)).
by rewrite shrincs_fxmss_paired_plan_coordinates size_map full_postorder_size.
Qed.

Lemma shrincs_fxmss_paired_plan_class P pp inputs pos t :
  all (fun x => fxmss_paired_class x.1) (shrincs_fxmss_paired_plan P pp inputs pos t).
Proof.
elim: t pos => [u|l ihl r ihr] pos //=.
by rewrite !all_cat ihl ihr.
Qed.

Lemma shrincs_fxmss_paired_prefix_fresh P h (xs ys : seq (tweak * seq UInt8)) :
  uniq [seq shrincs_fxmss_paired_coordinate t | t <-
    get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 (xs ++ ys)]
      ->
  uniq [seq shrincs_fxmss_paired_coordinate t | t <-
    get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 xs].
Proof.
by rewrite /unzip1 !map_cat catA cat_uniq => /and3P[].
Qed.

Lemma shrincs_fxmss_paired_suffix_fresh P h xs ys :
  uniq [seq shrincs_fxmss_paired_coordinate t | t <-
    get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 (xs ++ ys)]
      ->
  uniq [seq shrincs_fxmss_paired_coordinate t | t <-
    get_heap (shrincs_fxmss_paired_heap P h xs) (tcrx.tcrx_tws_loc
      (shrincs_fxmss_hash_function P)) ++
    unzip1 ys].
Proof.
by rewrite shrincs_fxmss_paired_heap_tweaks /unzip1 !map_cat catA.
Qed.

Lemma shrincs_fxmss_paired_prefix_budget P budget h (xs ys : seq (tweak * seq UInt8)) :
  size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) + size (xs ++
    ys) <= budget ->
  size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) + size xs <=
    budget.
Proof.
rewrite size_cat addnA.
move=> hb.
exact: leq_trans (leq_addr _ _) hb.
Qed.

Lemma shrincs_fxmss_paired_suffix_budget P budget h xs ys :
  size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) + size (xs ++
    ys) <= budget ->
  size (get_heap (shrincs_fxmss_paired_heap P h xs) (tcrx.tcrx_tws_loc
    (shrincs_fxmss_hash_function P))) +
    size ys <= budget.
Proof.
by rewrite shrincs_fxmss_paired_heap_tweaks !size_cat /unzip1 size_map addnA.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired table *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_paired_heap_table P h targets :
  get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  get_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P)) = emptym ->
  get_heap (shrincs_fxmss_paired_heap P h targets) (tcrx.tcrx_tgts_loc
    (shrincs_fxmss_hash_function P)) =
    qmap_from 0 targets.
Proof.
move=> ht hg.
elim/last_ind: targets => [|targets t ih]; first exact: hg.
rewrite -cats1 shrincs_fxmss_paired_heap_cat /shrincs_fxmss_paired_heap /=
  /shrincs_fxmss_paired_step.
rewrite get_set_heap_neq // get_set_heap_eq.
change (setm
  (get_heap (shrincs_fxmss_paired_heap P h targets) (tcrx.tcrx_tgts_loc
    (shrincs_fxmss_hash_function P)))
  (size (get_heap (shrincs_fxmss_paired_heap P h targets) (tcrx.tcrx_tws_loc
    (shrincs_fxmss_hash_function P)))) t =
  qmap_from 0 (targets ++ [:: t])).
by rewrite ih shrincs_fxmss_paired_heap_tweaks ht cat0s /unzip1 size_map cats1
  qmap_from_rcons add0n.
Qed.

Lemma shrincs_fxmss_paired_heap_lookup P h targets target :
  get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  get_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P)) = emptym ->
  target \in targets ->
  getm (get_heap (shrincs_fxmss_paired_heap P h targets) (tcrx.tcrx_tgts_loc
    (shrincs_fxmss_hash_function P)))
    (index target targets) = Some target.
Proof.
move=> ht hg hin.
rewrite (shrincs_fxmss_paired_heap_table P h targets ht hg)
  -[index target targets]add0n qmap_from_get.
have hi : index target targets < size targets by rewrite index_mem.
have [x hx] := qnth_some targets (index target targets) hi.
have he := qnth_nth target targets (index target targets) x hx.
rewrite nth_index // in he.
by rewrite -he in hx.
Qed.

Lemma shrincs_fxmss_paired_index_lookup (targets : seq (tweak * seq UInt8)) t m :
  uniq (unzip1 targets) -> (t,m) \in targets ->
  getm (qmap_from 0 targets) (index t (unzip1 targets)) = Some (t,m).
Proof.
rewrite -[index _ _]add0n qmap_from_get.
elim: targets=> [|[t0 m0] targets ih] //=.
move=> /andP[hn hu].
rewrite inE=> /orP[/eqP[-> ->]|hm].
- by rewrite /unzip1 /= eqxx /qnth.
- (* The target occurs in the tail, with a different tweak. *)
  have ht : t != t0.
    apply/eqP=> he; move: hn; rewrite -he.
    by rewrite (map_f fst hm).
  rewrite eq_sym (negbTE ht) /qnth /=.
  exact: ih hu hm.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired commit *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint shrincs_fxmss_paired_commit (input : seq bool -> raw_code ('list ('word U8)))
    (pos : seq bool) (t : bt unit) : raw_code (bytes 16) :=
  match t with
  | BLeaf _ =>
      m ← input pos ;;
      call [ tcrx.XQUERY ] : { tweak × 'list ('word U8) ~> bytes 16 }
        (shrincs_fxmss_pk_tweak (shrincs_fxmss_path_coord pos), m)
  | BNode l r =>
      rv ← shrincs_fxmss_paired_commit input (rcons pos true) r ;;
      lv ← shrincs_fxmss_paired_commit input (rcons pos false) l ;;
      call [ tcrx.XQUERY ] : { tweak × 'list ('word U8) ~> bytes 16 }
        (shrincs_fxmss_tree_path_tweak pos, shrincs_fxmss_tree_message (lv, rv))
  end.

#[export] Instance shrincs_fxmss_paired_commit_valid P (L : Locations) input pos t :
  (forall p, ValidCode L (tcrx.I_TCRX (shrincs_fxmss_hash_function P)) (input p)) ->
  ValidCode L (tcrx.I_TCRX (shrincs_fxmss_hash_function P)) (shrincs_fxmss_paired_commit
    input pos t).
Proof.
move=> hinput.
elim: t pos => [u|l ihl r ihr] pos /=.
- eapply valid_bind; first exact: hinput.
  move=> m; ssprove_valid.
- eapply valid_bind; first exact: ihr.
  move=> rv.
  eapply valid_bind; first exact: ihl.
  move=> lv; ssprove_valid.
Qed.

Local Opaque tcrx.TCRX_game.

Lemma shrincs_fxmss_paired_commit_one P budget bit pp t m h
    (T : choiceType) (K : bytes 16 -> raw_code T) :
  fxmss_paired_class t ->
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h tcrx.tcrx_rev_loc = false ->
  uniq [seq shrincs_fxmss_paired_coordinate x | x <-
    get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ++ [:: t]] ->
  size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) + 1 <= budget ->
  Pr_code (bind
    (resolve (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
      fxmss_partner budget bit)
      (shrincs_fxmss_paired_query_op P) (t, m)) K) h =
  Pr_code (K (th_eval (shrincs_fxmss_hash_function P) pp t m))
    (shrincs_fxmss_paired_heap P h [:: (t, m)]).
Proof.
move=> ht hp hr.
rewrite cats1 map_rcons rcons_uniq addn1 => /andP[hf _] hb.
have [hf0 hf1] := shrincs_fxmss_paired_coordinate_fresh t _ hf.
exact: shrincs_fxmss_paired_query_known.
Qed.

Lemma shrincs_fxmss_paired_commit_known P budget bit pp input inputs (T : choiceType) :
  (forall pos h (K : seq UInt8 -> raw_code T),
    get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
    Pr_code (bind
      (code_link (input pos)
        (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
          budget bit)) K) h =
    Pr_code (K (inputs pos)) h) ->
  forall t pos h (K : bytes 16 -> raw_code T),
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h tcrx.tcrx_rev_loc = false ->
  uniq [seq shrincs_fxmss_paired_coordinate x | x <-
    get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ++
    unzip1 (shrincs_fxmss_paired_plan P pp inputs pos t)] ->
  size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) +
    size (shrincs_fxmss_paired_plan P pp inputs pos t) <= budget ->
  Pr_code (bind
    (code_link (shrincs_fxmss_paired_commit input pos t)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        budget bit)) K) h =
  Pr_code (K (shrincs_fxmss_paired_value P pp inputs pos t))
    (shrincs_fxmss_paired_heap P h (shrincs_fxmss_paired_plan P pp inputs pos t)).
Proof.
move=> hinput.
elim=> [u|l ihl r ihr] pos h K hp hr hf hb.
- (* A leaf contributes one compression target. *)
  cbn [shrincs_fxmss_paired_commit].
  rewrite code_link_bind bind_assoc (hinput _ h _ hp).
  cbn [code_link].
  rewrite bind_ret.
  exact: shrincs_fxmss_paired_commit_one.
- (* An internal node commits both subtrees before its tree target. *)
  cbn [shrincs_fxmss_paired_commit].
  rewrite code_link_bind bind_assoc.
  have hfr := shrincs_fxmss_paired_prefix_fresh P h _ _ hf.
  have hbr := shrincs_fxmss_paired_prefix_budget P budget h _ _ hb.
  rewrite (ihr _ h _ hp hr hfr hbr).
  rewrite code_link_bind bind_assoc.
  set h1 := shrincs_fxmss_paired_heap P h
    (shrincs_fxmss_paired_plan P pp inputs (rcons pos true) r).
  have hp1 : get_heap h1 (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp.
    by rewrite /h1 shrincs_fxmss_paired_heap_seed.
  have hr1 : get_heap h1 tcrx.tcrx_rev_loc = false.
    by rewrite /h1 shrincs_fxmss_paired_heap_revealed.
  have hf1 := shrincs_fxmss_paired_suffix_fresh P h _ _ hf.
  have hb1 := shrincs_fxmss_paired_suffix_budget P budget h _ _ hb.
  have hfl := shrincs_fxmss_paired_prefix_fresh P h1 _ _ hf1.
  have hbl := shrincs_fxmss_paired_prefix_budget P budget h1 _ _ hb1.
  rewrite (ihl _ h1 _ hp1 hr1 hfl hbl).
  set h2 := shrincs_fxmss_paired_heap P h1
    (shrincs_fxmss_paired_plan P pp inputs (rcons pos false) l).
  have hp2 : get_heap h2 (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp.
    by rewrite /h2 shrincs_fxmss_paired_heap_seed.
  have hr2 : get_heap h2 tcrx.tcrx_rev_loc = false.
    by rewrite /h2 shrincs_fxmss_paired_heap_revealed.
  have hf2 := shrincs_fxmss_paired_suffix_fresh P h1 _ _ hf1.
  have hb2 := shrincs_fxmss_paired_suffix_budget P budget h1 _ _ hb1.
  cbn [code_link].
  rewrite bind_ret.
  rewrite (shrincs_fxmss_paired_commit_one P budget bit pp) //.
  by rewrite [in RHS]/shrincs_fxmss_paired_plan -/shrincs_fxmss_paired_plan
    !shrincs_fxmss_paired_heap_cat.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired generation *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_paired_inputs P pp (keys : shrincs_fxmss_coord -> seq (bytes
  16)) p :=
  shrincs_fxmss_paired_input_value P (shrincs_fxmss_path_coord p) pp (keys
    (shrincs_fxmss_path_coord p)).

Definition shrincs_fxmss_paired_generate P (keys : shrincs_fxmss_coord -> seq (bytes
  16)) b d :=
  shrincs_fxmss_paired_commit
    (fun p => shrincs_fxmss_paired_leaf_input P (shrincs_fxmss_path_coord p) (keys
      (shrincs_fxmss_path_coord p)))
    [::] (shrincs_fxmss_tree_shape b d).

Definition shrincs_fxmss_paired_targets P pp (keys : shrincs_fxmss_coord -> seq (bytes
  16)) b d :=
  shrincs_fxmss_paired_plan P pp (shrincs_fxmss_paired_inputs P pp keys) [::]
    (shrincs_fxmss_tree_shape b d).

Lemma shrincs_fxmss_paired_value_eval P pp keys b d pos t :
  shrincs_fxmss_paired_value P pp (shrincs_fxmss_paired_inputs P pp keys) pos t =
    shrincs_fxmss_commit_value P pp (shrincs_fxmss_tree_leaf_values P pp keys b d) pos
      t.
Proof.
rewrite /shrincs_fxmss_paired_value /shrincs_fxmss_commit_value.
congr (val_bt _ _ (bt_posmap _ _ _)).
apply boolp.funext=> p; apply boolp.funext=> u.
exact: shrincs_fxmss_paired_input_eval.
Qed.

Lemma shrincs_fxmss_paired_targets_fresh P pp keys b d :
  shrincs_fxmss_spec_legal_shape b d ->
  uniq [seq shrincs_fxmss_paired_coordinate t | t <- unzip1
    (shrincs_fxmss_paired_targets P pp keys b d)].
Proof.
move=> /shrincs_fxmss_legal_shapeP hd.
rewrite /shrincs_fxmss_paired_targets /unzip1 -map_comp /=
  shrincs_fxmss_paired_plan_coordinates.
exact: shrincs_fxmss_paired_positions_uniq.
Qed.

Lemma shrincs_fxmss_paired_targets_size P pp keys b d :
  size (shrincs_fxmss_paired_targets P pp keys b d) =
    2 * shrincs_fxmss_leaf_count b d - 1.
Proof. by rewrite /shrincs_fxmss_paired_targets shrincs_fxmss_paired_plan_size
  shrincs_fxmss_tree_shape_count. Qed.

Lemma shrincs_fxmss_paired_targets_budget P pp keys b d (Q : shrincs_fxmss_resources) :
  shrincs_fxmss_spec_legal_shape b d ->
  size (shrincs_fxmss_paired_targets P pp keys b d) <= 2 * shrincs_fxmss_leaf_capacity Q
    - 1.
Proof.
move=> /shrincs_fxmss_legal_shapeP hd.
rewrite shrincs_fxmss_paired_targets_size -shrincs_fxmss_tree_shape_count
  -(full_postorder_size [::]).
exact: shrincs_fxmss_paired_positions_budget.
Qed.

#[export] Instance shrincs_fxmss_paired_generate_valid P (L : Locations) keys b d :
  ValidCode L (tcrx.I_TCRX (shrincs_fxmss_hash_function P))
    (shrincs_fxmss_paired_generate P keys b d).
Proof.
rewrite /shrincs_fxmss_paired_generate.
by apply: shrincs_fxmss_paired_commit_valid=> p.
Qed.

Lemma shrincs_fxmss_paired_generate_known P Q bit pp keys b d h
    (T : choiceType) (K : bytes 16 -> raw_code T) :
  shrincs_fxmss_spec_legal_shape b d ->
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h tcrx.tcrx_rev_loc = false ->
  get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  Pr_code (bind
    (code_link (shrincs_fxmss_paired_generate P keys b d)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        (2 * shrincs_fxmss_leaf_capacity Q - 1) bit)) K) h =
  Pr_code (K (val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d)))
    (shrincs_fxmss_paired_heap P h (shrincs_fxmss_paired_targets P pp keys b d)).
Proof.
move=> hd hp hr ht.
have he := shrincs_fxmss_paired_value_eval P pp keys b d [::] (shrincs_fxmss_tree_shape
  b d).
change (shrincs_fxmss_paired_value P pp (shrincs_fxmss_paired_inputs P pp keys) [::]
  (shrincs_fxmss_tree_shape b d) = val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d)) in he.
rewrite -he.
apply: (shrincs_fxmss_paired_commit_known P (2 * shrincs_fxmss_leaf_capacity Q - 1) bit
  pp _
  (shrincs_fxmss_paired_inputs P pp keys) T) => //.
- move=> p h' K' hp'.
  exact: shrincs_fxmss_paired_input_known.
- rewrite ht /=.
  exact: shrincs_fxmss_paired_targets_fresh.
- rewrite ht add0n.
  exact: shrincs_fxmss_paired_targets_budget.
Qed.
