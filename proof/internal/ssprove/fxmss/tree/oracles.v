(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.oracles

    Tree targets are committed in reverse preorder, so both children are available
    before their parent. The runtime target map stores each committed message at
    its position in the reverse-preorder list. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.batch_map chain.core.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree tree_paths merkle.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape model.nodes tree.encoding tree.model scheme.
From Stdlib Require Import Lia.
From Shrincs.internal.ssprove.wots Require Import params scheme games hop.compress.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Tree commit *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_committed P keys pp b d :=
  rev (shrincs_fxmss_tree_targets P keys pp b d).

Definition shrincs_fxmss_tree_check_index (n i : nat) := n - i.+1.

Lemma shrincs_fxmss_tree_check_index_bound n i :
  i < n -> shrincs_fxmss_tree_check_index n i < n.
Proof.
move/ltP=> hi.
apply/ltP.
rewrite /shrincs_fxmss_tree_check_index subnE.
lia.
Qed.

Lemma shrincs_fxmss_tree_check_indexK n i :
  i < n -> shrincs_fxmss_tree_check_index n (shrincs_fxmss_tree_check_index n i) = i.
Proof.
move/ltP=> hi.
rewrite /shrincs_fxmss_tree_check_index !subnE.
lia.
Qed.

Lemma shrincs_fxmss_tree_committed_nth P keys pp b d x i :
  i < size (shrincs_fxmss_tree_targets P keys pp b d) ->
  nth x (shrincs_fxmss_tree_committed P keys pp b d)
    (shrincs_fxmss_tree_check_index (size (shrincs_fxmss_tree_targets P keys pp b d)) i)
      =
  nth x (shrincs_fxmss_tree_targets P keys pp b d) i.
Proof.
move=> hi.
rewrite /shrincs_fxmss_tree_committed nth_rev; first exact:
  shrincs_fxmss_tree_check_index_bound hi.
by rewrite -/(shrincs_fxmss_tree_check_index _ _) shrincs_fxmss_tree_check_indexK.
Qed.

Lemma shrincs_fxmss_tree_committed_budget P keys pp b d Q :
  shrincs_fxmss_spec_legal_shape b d ->
  size (shrincs_fxmss_tree_committed P keys pp b d) <= shrincs_fxmss_leaf_capacity Q -
    1.
Proof.
by rewrite /shrincs_fxmss_tree_committed size_rev; apply:
  shrincs_fxmss_tree_targets_budget.
Qed.

Lemma shrincs_fxmss_tree_committed_fresh P keys pp b d :
  shrincs_fxmss_spec_legal_shape b d ->
  uniq (unzip1 (shrincs_fxmss_tree_committed P keys pp b d)).
Proof.
by rewrite /shrincs_fxmss_tree_committed /unzip1 map_rev rev_uniq;
  apply: shrincs_fxmss_tree_targets_fresh.
Qed.

Section Traversal.
Context (P : shrincs_fxmss_params).

(** Leaf evaluation uses EVAL outside type 18. No seed is revealed by this
    traversal, and TQUERY commits only after both child values are known. *)
Fixpoint shrincs_fxmss_commit_tree (leaf : seq bool -> raw_code (bytes 16))
    (pos : seq bool) (t : bt unit) : raw_code (bytes 16) :=
  match t with
  | BLeaf _ => leaf pos
  | BNode l r =>
      rv ← shrincs_fxmss_commit_tree leaf (rcons pos true) r ;;
      lv ← shrincs_fxmss_commit_tree leaf (rcons pos false) l ;;
      call [ smtcr.TQUERY ] : { tweak × 'list ('word jasmin_wsize.U8)
        ~> bytes 16 } (shrincs_fxmss_tree_path_tweak pos, shrincs_fxmss_tree_message
          (lv, rv))
  end.

#[export] Instance shrincs_fxmss_commit_tree_valid (L : Locations) leaf pos t :
  (forall p, ValidCode L (smtcr.I_SMTCR (shrincs_fxmss_hash_function P)) (leaf p)) ->
  ValidCode L (smtcr.I_SMTCR (shrincs_fxmss_hash_function P)) (shrincs_fxmss_commit_tree
    leaf pos t).
Proof.
move=> hleaf.
elim: t pos => [u|l ihl r ihr] pos /=; first exact: hleaf.
eapply valid_bind; first exact: ihr.
move=> rv.
eapply valid_bind; first exact: ihl.
move=> lv.
ssprove_valid.
Qed.

End Traversal.

(* ------------------------------------------------------------------ *)
(** ** Tree oracles *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_tree_eval_op (P : shrincs_fxmss_params) : opsig :=
  (EVAL, (th_T (shrincs_fxmss_hash_function P) × th_M (shrincs_fxmss_hash_function P),
    th_N (shrincs_fxmss_hash_function P))).
Definition shrincs_fxmss_tree_query_op (P : shrincs_fxmss_params) : opsig :=
  (smtcr.TQUERY,
    (th_T (shrincs_fxmss_hash_function P) × th_M (shrincs_fxmss_hash_function P), th_N
      (shrincs_fxmss_hash_function P))).

Section Oracles.
Context (P : shrincs_fxmss_params) (budget : nat) (bit : bool).

Lemma shrincs_fxmss_tree_eval_known (T : choiceType) pp t m
    (k : bytes 16 -> raw_code T) h :
  ~~ fxmss_tree_class t ->
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (resolve (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget
      bit)
      (shrincs_fxmss_tree_eval_op P) (t, m)) k) h =
  Pr_code (k (th_eval (shrincs_fxmss_hash_function P) pp t m)) h.
Proof.
move=> ht hp.
rewrite /shrincs_fxmss_tree_eval_op /smtcr.SMTCR_game /resolve /= coerce_kleisliE.
by rewrite ht /= Pr_code_get hp.
Qed.

Lemma shrincs_fxmss_tree_query_known (T : choiceType) pp pos m
    (k : bytes 16 -> raw_code T) h :
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h smtcr.tcr_rev_loc = false ->
  size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))) < budget ->
  shrincs_fxmss_tree_path_tweak pos \notin get_heap h (smtcr.tcr_tws_loc
    (shrincs_fxmss_hash_function P)) ->
  Pr_code (bind
    (resolve (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget
      bit)
      (shrincs_fxmss_tree_query_op P) (shrincs_fxmss_tree_path_tweak pos, m)) k) h =
  Pr_code (k (th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_tree_path_tweak
    pos) m))
    (set_heap
      (set_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P))
        (setm (get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)))
          (size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))))
          (shrincs_fxmss_tree_path_tweak pos, m)))
      (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))
      (rcons (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)))
        (shrincs_fxmss_tree_path_tweak pos))).
Proof.
move=> hp hr hb hf.
rewrite /shrincs_fxmss_tree_query_op /smtcr.SMTCR_game /resolve /= coerce_kleisliE.
rewrite Pr_code_get hr /= Pr_code_get hb /= hf /= Pr_code_get.
rewrite !Pr_code_put Pr_code_get !get_set_heap_neq // hp.
reflexivity.
Qed.

Definition shrincs_fxmss_tree_check_op : opsig :=
  (smtcr.CHECK, ('nat × th_M (shrincs_fxmss_hash_function P), 'bool)).
Definition shrincs_fxmss_tree_reveal_op : opsig :=
  (smtcr.GETPP, ('unit, th_PP (shrincs_fxmss_hash_function P))).

Lemma shrincs_fxmss_tree_check_known (T : choiceType) pp j t m0 m
    (k : bool -> raw_code T) h :
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h smtcr.tcr_rev_loc = true ->
  getm (get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P))) j = Some (t,
    m0) ->
  Pr_code (bind
    (resolve (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget
      bit)
      shrincs_fxmss_tree_check_op (j, m)) k) h =
  Pr_code (k (bit && ((m != m0) &&
    (th_eval (shrincs_fxmss_hash_function P) pp t m == th_eval
      (shrincs_fxmss_hash_function P) pp t m0)))) h.
Proof.
move=> hp hr ht.
rewrite /shrincs_fxmss_tree_check_op /smtcr.SMTCR_game /resolve /= coerce_kleisliE.
rewrite Pr_code_get hr /=.
case: bit => /=; last reflexivity.
by rewrite Pr_code_get ht Pr_code_get hp.
Qed.

Lemma shrincs_fxmss_tree_reveal_known (T : choiceType) pp
    (k : bytes 16 -> raw_code T) h :
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (resolve (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget
      bit)
      shrincs_fxmss_tree_reveal_op tt) k) h =
  Pr_code (k pp) (set_heap h smtcr.tcr_rev_loc true).
Proof.
move=> hp.
rewrite /shrincs_fxmss_tree_reveal_op /smtcr.SMTCR_game /resolve /= coerce_kleisliE.
by rewrite Pr_code_get hp /= Pr_code_put.
Qed.

End Oracles.

(* ------------------------------------------------------------------ *)
(** ** Tree leaves *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_eval_leaf (P : shrincs_fxmss_params) (a : shrincs_fxmss_coord)
    (xs : seq (bytes 16)) : raw_code (bytes 16) :=
  ends ← query_list
    (fun ix : nat * bytes 16 =>
      cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) ix.1 0 15 ix.2)
    (zip (iota 0 wots_c_chain_count) xs) ;;
  call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 }
    (shrincs_fxmss_pk_tweak a, flatten [seq tval x | x <- ends]).

#[local] Arguments cp_walk : simpl never.

Lemma shrincs_fxmss_eval_leaf_valid P (L : Locations) a xs :
  ValidCode L (smtcr.I_SMTCR (shrincs_fxmss_hash_function P)) (shrincs_fxmss_eval_leaf P
    a xs).
Proof.
rewrite /shrincs_fxmss_eval_leaf.
eapply valid_bind.
- elim: (zip (iota 0 wots_c_chain_count) xs) => [|ix rest ih]; cbn [query_list].
  + apply valid_ret.
  + eapply valid_bind.
    * exact (cp_walk_valid (shrincs_fxmss_leaf_params P a false (uint U8 0))
        L ix.1 0 15 ix.2).
    * move=> y.
      eapply valid_bind; first exact: ih.
      move=> ys; apply valid_ret.
- move=> ends; ssprove_valid.
Qed.

#[export] Existing Instance shrincs_fxmss_eval_leaf_valid.

Lemma shrincs_fxmss_eval_leaf_shape P a b d pp xs :
  shrincs_fxmss_leaf_pubkey P a b d pp xs =
    shrincs_fxmss_leaf_pubkey P a false (uint U8 0) pp xs.
Proof. by []. Qed.

Definition shrincs_fxmss_walk_value P a pp i x k n :=
  let W := shrincs_fxmss_leaf_params P a false (uint U8 0) in
  chainc (wcp_PP W) (wcp_N W) (wcp_w W) (Fw W) pp i x k n.

#[local] Arguments smtcr.SMTCR_game : simpl never.
Local Opaque smtcr.SMTCR_game.

Lemma shrincs_fxmss_walk_known P budget bit a pp n i k x h
    (T : choiceType) (K : bytes 16 -> raw_code T) :
  k + n <= 15 ->
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (code_link (cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) i k n x)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget bit)) K)
        h =
  Pr_code (K (shrincs_fxmss_walk_value P a pp i x k n)) h.
Proof.
elim: n k x K => [|n ih] k x K hkn hp.
- by rewrite /cp_walk /shrincs_fxmss_walk_value.
- rewrite /cp_walk -/cp_walk /= bind_assoc.
  rewrite (shrincs_fxmss_tree_eval_known P budget bit T pp) //.
  rewrite ih.
  + by rewrite addSnnS.
  + exact hp.
  + (* The chain step uses an evaluation outside the tree target class. *)
    have hkw : k < wcp_w (shrincs_fxmss_leaf_params P a false (uint U8 0)).
      change (k <= 15).
      exact: leq_trans (leq_addr _ _) hkn.
    by rewrite -(eval_Fc_E (shrincs_fxmss_leaf_params P a false (uint U8 0))
      pp i k x hkw).
Qed.

Local Opaque cp_walk.

Lemma shrincs_fxmss_eval_ends_known P budget bit a pp (xs : seq (nat * bytes 16)) h
    (T : choiceType) (K : seq (bytes 16) -> raw_code T) :
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (code_link
      (query_list (fun ix : nat * bytes 16 =>
        cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) ix.1 0 15 ix.2) xs)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget bit)) K)
        h =
  Pr_code (K [seq shrincs_fxmss_walk_value P a pp ix.1 ix.2 0 15 | ix <- xs]) h.
Proof.
move=> hp.
elim: xs K => [|ix xs ih] K; first by [].
rewrite /= code_link_bind bind_assoc.
rewrite (shrincs_fxmss_walk_known P budget bit a pp) //.
by rewrite code_link_bind bind_assoc ih.
Qed.

Lemma shrincs_fxmss_eval_leaf_known P budget bit a b d pp xs h
    (T : choiceType) (K : bytes 16 -> raw_code T) :
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (code_link (shrincs_fxmss_eval_leaf P a xs)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget bit)) K)
        h =
  Pr_code (K (shrincs_fxmss_leaf_pubkey P a b d pp xs)) h.
Proof.
move=> hp.
rewrite /shrincs_fxmss_eval_leaf code_link_bind bind_assoc.
rewrite (shrincs_fxmss_eval_ends_known P budget bit a pp) //.
cbn [code_link].
rewrite bind_ret.
by rewrite (shrincs_fxmss_tree_eval_known P budget bit T pp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree state *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_commit_step P h (target : tweak * seq UInt8) :=
  set_heap
    (set_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P))
      (setm (get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)))
        (size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)))) target))
    (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))
    (rcons (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))) target.1).

Definition shrincs_fxmss_commit_heap P h targets := foldl (shrincs_fxmss_commit_step P)
  h targets.

Lemma shrincs_fxmss_commit_heap_cat P h xs ys :
  shrincs_fxmss_commit_heap P h (xs ++ ys) =
    shrincs_fxmss_commit_heap P (shrincs_fxmss_commit_heap P h xs) ys.
Proof. exact: foldl_cat. Qed.

Lemma shrincs_fxmss_commit_heap_seed P h targets :
  get_heap (shrincs_fxmss_commit_heap P h targets) (smtcr.tcr_pp_loc
    (shrincs_fxmss_hash_function P)) =
    get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)).
Proof.
elim: targets h => [|target targets ih] h //=.
rewrite /shrincs_fxmss_commit_heap /= -/shrincs_fxmss_commit_heap ih
  /shrincs_fxmss_commit_step.
by rewrite !get_set_heap_neq.
Qed.

Lemma shrincs_fxmss_commit_heap_revealed P h targets :
  get_heap (shrincs_fxmss_commit_heap P h targets) smtcr.tcr_rev_loc =
    get_heap h smtcr.tcr_rev_loc.
Proof.
elim: targets h => [|target targets ih] h //=.
rewrite /shrincs_fxmss_commit_heap /= -/shrincs_fxmss_commit_heap ih
  /shrincs_fxmss_commit_step.
by rewrite !get_set_heap_neq.
Qed.

Lemma shrincs_fxmss_commit_heap_tweaks P h targets :
  get_heap (shrincs_fxmss_commit_heap P h targets) (smtcr.tcr_tws_loc
    (shrincs_fxmss_hash_function P)) =
    get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 targets.
Proof.
elim: targets h => [|target targets ih] h; first by rewrite cats0.
rewrite /shrincs_fxmss_commit_heap /= -/shrincs_fxmss_commit_heap ih
  /shrincs_fxmss_commit_step.
by rewrite get_set_heap_eq -cat_rcons.
Qed.

Definition shrincs_fxmss_commit_value P pp (values : seq bool -> bytes 16) pos (t : bt
  unit) :=
  val_bt (shrincs_fxmss_tree_node_hash P pp) pos
    (bt_posmap (fun p _ => values p) pos t).

Fixpoint shrincs_fxmss_commit_plan P pp (values : seq bool -> bytes 16)
    (pos : seq bool) (t : bt unit) : seq (tweak * seq UInt8) :=
  match t with
  | BLeaf _ => [::]
  | BNode l r =>
      shrincs_fxmss_commit_plan P pp values (rcons pos true) r ++
      shrincs_fxmss_commit_plan P pp values (rcons pos false) l ++
      [:: (shrincs_fxmss_tree_path_tweak pos,
           shrincs_fxmss_tree_message
             (shrincs_fxmss_commit_value P pp values (rcons pos false) l,
              shrincs_fxmss_commit_value P pp values (rcons pos true) r))]
  end.

Lemma shrincs_fxmss_commit_plan_order P pp values pos t :
  unzip1 (shrincs_fxmss_commit_plan P pp values pos t) =
    [seq shrincs_fxmss_tree_path_tweak p | p <- tree_postorder pos t].
Proof.
elim: t pos => [u|l ihl r ihr] pos; first by [].
rewrite tree_postorder_node /unzip1 /= !map_cat /=.
by rewrite -ihl -ihr.
Qed.

Lemma shrincs_fxmss_commit_plan_size P pp values pos t :
  size (shrincs_fxmss_commit_plan P pp values pos t) = (bt_nleaves t).-1.
Proof.
rewrite -(size_map fst (shrincs_fxmss_commit_plan P pp values pos t)).
by rewrite -/(unzip1 _) shrincs_fxmss_commit_plan_order size_map tree_postorder_size.
Qed.

Lemma shrincs_fxmss_commit_prefix_fresh P h (xs ys : seq (tweak * seq UInt8)) :
  uniq (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 (xs ++
    ys)) ->
  uniq (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 xs).
Proof.
by rewrite /unzip1 map_cat catA cat_uniq => /and3P[].
Qed.

Lemma shrincs_fxmss_commit_suffix_fresh P h xs ys :
  uniq (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) ++ unzip1 (xs ++
    ys)) ->
  uniq (get_heap (shrincs_fxmss_commit_heap P h xs) (smtcr.tcr_tws_loc
    (shrincs_fxmss_hash_function P)) ++
    unzip1 ys).
Proof.
by rewrite shrincs_fxmss_commit_heap_tweaks /unzip1 map_cat catA.
Qed.

Lemma shrincs_fxmss_commit_prefix_budget P budget h (xs ys : seq (tweak * seq UInt8)) :
  size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))) + size (xs ++
    ys) <= budget ->
  size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))) + size xs <=
    budget.
Proof.
rewrite size_cat addnA.
move=> hb.
exact: leq_trans (leq_addr _ _) hb.
Qed.

Lemma shrincs_fxmss_commit_suffix_budget P budget h xs ys :
  size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))) + size (xs ++
    ys) <= budget ->
  size (get_heap (shrincs_fxmss_commit_heap P h xs) (smtcr.tcr_tws_loc
    (shrincs_fxmss_hash_function P))) +
    size ys <= budget.
Proof.
by rewrite shrincs_fxmss_commit_heap_tweaks !size_cat /unzip1 size_map addnA.
Qed.

#[local] Arguments smtcr.SMTCR_game : simpl never.
Local Opaque smtcr.SMTCR_game.
#[local] Arguments shrincs_fxmss_commit_value : simpl never.

Lemma shrincs_fxmss_commit_tree_known P budget bit pp leaf values (T : choiceType) :
  (forall pos h (K : bytes 16 -> raw_code T),
    get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
    Pr_code (bind
      (code_link (leaf pos)
        (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget bit))
          K) h =
    Pr_code (K (values pos)) h) ->
  forall t pos h (K : bytes 16 -> raw_code T),
  get_heap h (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h smtcr.tcr_rev_loc = false ->
  uniq (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) ++
    unzip1 (shrincs_fxmss_commit_plan P pp values pos t)) ->
  size (get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))) +
    size (shrincs_fxmss_commit_plan P pp values pos t) <= budget ->
  Pr_code (bind
    (code_link (shrincs_fxmss_commit_tree leaf pos t)
      (smtcr.SMTCR_game (shrincs_fxmss_hash_function P) fxmss_tree_class budget bit)) K)
        h =
  Pr_code (K (shrincs_fxmss_commit_value P pp values pos t))
    (shrincs_fxmss_commit_heap P h (shrincs_fxmss_commit_plan P pp values pos t)).
Proof.
move=> hleaf.
elim=> [u|l ihl r ihr] pos h K hp hr hf hb.
- exact: hleaf.
- (* Commit both subtrees before their parent target. *)
  cbn [shrincs_fxmss_commit_tree].
  rewrite code_link_bind bind_assoc.
  have hfr := shrincs_fxmss_commit_prefix_fresh P h _ _ hf.
  have hbr := shrincs_fxmss_commit_prefix_budget P budget h _ _ hb.
  rewrite (ihr _ h _ hp hr hfr hbr).
  rewrite code_link_bind bind_assoc.
  set h1 := shrincs_fxmss_commit_heap P h
    (shrincs_fxmss_commit_plan P pp values (rcons pos true) r).
  have hp1 : get_heap h1 (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp.
    by rewrite /h1 shrincs_fxmss_commit_heap_seed.
  have hr1 : get_heap h1 smtcr.tcr_rev_loc = false.
    by rewrite /h1 shrincs_fxmss_commit_heap_revealed.
  have hf1 := shrincs_fxmss_commit_suffix_fresh P h _ _ hf.
  have hb1 := shrincs_fxmss_commit_suffix_budget P budget h _ _ hb.
  have hfl := shrincs_fxmss_commit_prefix_fresh P h1 _ _ hf1.
  have hbl := shrincs_fxmss_commit_prefix_budget P budget h1 _ _ hb1.
  rewrite (ihl _ h1 _ hp1 hr1 hfl hbl).
  set h2 := shrincs_fxmss_commit_heap P h1
    (shrincs_fxmss_commit_plan P pp values (rcons pos false) l).
  have hp2 : get_heap h2 (smtcr.tcr_pp_loc (shrincs_fxmss_hash_function P)) = Some pp.
    by rewrite /h2 shrincs_fxmss_commit_heap_seed.
  have hr2 : get_heap h2 smtcr.tcr_rev_loc = false.
    by rewrite /h2 shrincs_fxmss_commit_heap_revealed.
  have hf2 := shrincs_fxmss_commit_suffix_fresh P h1 _ _ hf1.
  have hb2 := shrincs_fxmss_commit_suffix_budget P budget h1 _ _ hb1.
  cbn [code_link].
  rewrite bind_ret.
  change (is_true (uniq (get_heap h2 (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P))
    ++
    [:: shrincs_fxmss_tree_path_tweak pos]))) in hf2.
  move: hf2; rewrite cats1 rcons_uniq => /andP[hfq _].
  change (is_true (size (get_heap h2 (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function
    P))) + 1 <=
    budget)) in hb2.
  rewrite addn1 in hb2.
  rewrite (shrincs_fxmss_tree_query_known P budget bit T pp) //.
  by rewrite [in RHS]/shrincs_fxmss_commit_plan -/shrincs_fxmss_commit_plan
    !shrincs_fxmss_commit_heap_cat.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tree table *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_commit_heap_table P h targets :
  get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)) = emptym ->
  get_heap (shrincs_fxmss_commit_heap P h targets) (smtcr.tcr_tgts_loc
    (shrincs_fxmss_hash_function P)) =
    qmap_from 0 targets.
Proof.
move=> ht hg.
elim/last_ind: targets => [|targets t ih]; first exact: hg.
rewrite -cats1 shrincs_fxmss_commit_heap_cat /shrincs_fxmss_commit_heap /=
  /shrincs_fxmss_commit_step.
rewrite get_set_heap_neq // get_set_heap_eq.
change (setm
  (get_heap (shrincs_fxmss_commit_heap P h targets) (smtcr.tcr_tgts_loc
    (shrincs_fxmss_hash_function P)))
  (size (get_heap (shrincs_fxmss_commit_heap P h targets) (smtcr.tcr_tws_loc
    (shrincs_fxmss_hash_function P)))) t =
  qmap_from 0 (targets ++ [:: t])).
by rewrite ih shrincs_fxmss_commit_heap_tweaks ht cat0s /unzip1 size_map cats1
  qmap_from_rcons add0n.
Qed.

Lemma shrincs_fxmss_commit_heap_lookup P h targets target :
  get_heap h (smtcr.tcr_tws_loc (shrincs_fxmss_hash_function P)) = [::] ->
  get_heap h (smtcr.tcr_tgts_loc (shrincs_fxmss_hash_function P)) = emptym ->
  target \in targets ->
  getm (get_heap (shrincs_fxmss_commit_heap P h targets) (smtcr.tcr_tgts_loc
    (shrincs_fxmss_hash_function P)))
    (index target targets) = Some target.
Proof.
move=> ht hg hin.
rewrite (shrincs_fxmss_commit_heap_table P h targets ht hg)
  -[index target targets]add0n qmap_from_get.
have hi : index target targets < size targets by rewrite index_mem.
have [x hx] := qnth_some targets (index target targets) hi.
have he := qnth_nth target targets (index target targets) x hx.
rewrite nth_index // in he.
by rewrite -he in hx.
Qed.
