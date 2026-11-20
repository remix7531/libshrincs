(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.paired.routing

    Canonical compression/tree targets use one orbit per full coordinate. Evaluate
    WOTS+C chain endpoints through the paired game's EVAL oracle, before revealing
    the seed. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.batch_map chain.core.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  params tree.encoding shape scheme tree.oracles.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree tree_paths full_tree_paths.
From Shrincs.internal.ssprove.wots Require Import params scheme games hop.compress.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Paired routing *)

#[local] Open Scope nat_scope.

Definition shrincs_fxmss_paired_tweak (leaf : bool) (a : shrincs_fxmss_coord) : tweak :=
  if leaf then shrincs_fxmss_pk_tweak a else shrincs_fxmss_tree_tweak a.

Lemma shrincs_fxmss_paired_tweak_class leaf a :
  fxmss_paired_class (shrincs_fxmss_paired_tweak leaf a).
Proof. by case: leaf. Qed.

Lemma shrincs_fxmss_paired_tweak_partner leaf a :
  fxmss_partner (shrincs_fxmss_paired_tweak leaf a) = shrincs_fxmss_paired_tweak (~~
    leaf) a.
Proof. by case: leaf; case: a => h i. Qed.

Lemma shrincs_fxmss_paired_tweak_eq leaf leaf' a a' :
  (shrincs_fxmss_paired_tweak leaf a == shrincs_fxmss_paired_tweak leaf' a') =
    ((leaf == leaf') && (a == a')).
Proof.
case: leaf; case: leaf'; case: a => h i; case: a' => h' i';
  rewrite /shrincs_fxmss_paired_tweak /shrincs_fxmss_pk_tweak /shrincs_fxmss_tree_tweak
    /hash.tweak_of /= ?andbF ?andbT;
  by rewrite !xpair_eqE ?eqxx /= ?andbF ?andbT.
Qed.

Lemma shrincs_fxmss_paired_orbit_eq leaf leaf' a a' :
  ((shrincs_fxmss_paired_tweak leaf a == shrincs_fxmss_paired_tweak leaf' a') ||
   (fxmss_partner (shrincs_fxmss_paired_tweak leaf a) == shrincs_fxmss_paired_tweak
     leaf' a'))%bool =
  (a == a').
Proof.
rewrite shrincs_fxmss_paired_tweak_partner !shrincs_fxmss_paired_tweak_eq.
by case: leaf; case: leaf'; rewrite /= ?orbF.
Qed.

Lemma shrincs_fxmss_paired_orbit_disjoint leaf leaf' a a' :
  a != a' ->
  (shrincs_fxmss_paired_tweak leaf a != shrincs_fxmss_paired_tweak leaf' a') /\
  (fxmss_partner (shrincs_fxmss_paired_tweak leaf a) != shrincs_fxmss_paired_tweak leaf'
    a').
Proof.
rewrite -(shrincs_fxmss_paired_orbit_eq leaf leaf' a a') negb_or.
by move=> /andP[].
Qed.

Lemma shrincs_fxmss_paired_orbit_fresh leaf a (xs : seq (bool * shrincs_fxmss_coord)) :
  a \notin [seq x.2 | x <- xs] ->
  (shrincs_fxmss_paired_tweak leaf a \notin [seq shrincs_fxmss_paired_tweak x.1 x.2 | x
    <- xs]) /\
  (fxmss_partner (shrincs_fxmss_paired_tweak leaf a) \notin
    [seq shrincs_fxmss_paired_tweak x.1 x.2 | x <- xs]).
Proof.
elim: xs => [|[leaf' a'] xs ih] //=.
rewrite in_cons negb_or => /andP[ha hf].
have [hl hr] := shrincs_fxmss_paired_orbit_disjoint leaf leaf' a a' ha.
have [ihl ihr] := ih hf.
split; by rewrite in_cons negb_or ?hl ?hr ?ihl ?ihr.
Qed.

Lemma shrincs_fxmss_paired_compression_size (xs : seq (bytes 16)) :
  size xs = wots_c_chain_count ->
  size (flatten [seq tval x | x <- xs]) = 512.
Proof. move=> hx; by rewrite shape.flatten_rows_size hx. Qed.

Lemma shrincs_fxmss_paired_message_neq (xy : bytes 16 * bytes 16) (xs : seq (bytes 16))
  :
  size xs = wots_c_chain_count ->
  shrincs_fxmss_tree_message xy != flatten [seq tval x | x <- xs].
Proof.
move=> hs; apply/eqP=> he.
have hlen := congr1 size he.
rewrite shrincs_fxmss_tree_message_size (shrincs_fxmss_paired_compression_size xs hs) in
  hlen.
discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired positions *)

#[local] Open Scope nat_scope.

Definition shrincs_fxmss_paired_coordinate (t : tweak) : shrincs_fxmss_coord :=
  t.1.1.1.1.

Lemma shrincs_fxmss_paired_coordinate_tweak leaf a :
  shrincs_fxmss_paired_coordinate (shrincs_fxmss_paired_tweak leaf a) = a.
Proof. by case: leaf; case: a. Qed.

Lemma shrincs_fxmss_paired_coordinate_partner t :
  shrincs_fxmss_paired_coordinate (fxmss_partner t) = shrincs_fxmss_paired_coordinate t.
Proof.
case: t => [[[[[h i] tag] a] b] c].
rewrite /fxmss_partner /shrincs_fxmss_paired_coordinate.
by case: ifP; last case: ifP.
Qed.

Lemma shrincs_fxmss_paired_coordinate_fresh t (ts : seq tweak) :
  shrincs_fxmss_paired_coordinate t \notin [seq shrincs_fxmss_paired_coordinate x | x <-
    ts] ->
  (t \notin ts) /\ (fxmss_partner t \notin ts).
Proof.
move=> hf; split; apply/negP=> ht; move/negP: hf; apply.
- exact: map_f ht.
- rewrite -shrincs_fxmss_paired_coordinate_partner.
  exact: map_f ht.
Qed.

Lemma shrincs_fxmss_full_path_depth b d p :
  p \in full_paths (shrincs_fxmss_tree_shape b d) -> size p <= d.
Proof.
rewrite full_paths_mem => /orP[hp|hp].
- have := internal_path_depth hp.
  by rewrite shrincs_fxmss_tree_shape_depth => /ltnW.
- have hleaf := leaf_paths_correct hp.
  case he: (leaf_at (shrincs_fxmss_tree_shape b d) p) => [u|] in hleaf; last by [].
  by have := leaf_at_size he; rewrite shrincs_fxmss_tree_shape_depth.
Qed.

Lemma shrincs_fxmss_path_false_cons p : idx_of_path (false :: p) = idx_of_path p.
Proof.
have hz s : idx_of_lsb (rcons s false) = idx_of_lsb s.
  by elim: s => [|b s ih] //=; rewrite ih.
by rewrite /idx_of_path rev_cons hz.
Qed.

Lemma shrincs_fxmss_full_path_unbalanced d p :
  p \in full_paths (shrincs_fxmss_tree_shape false d) -> idx_of_path p <= 1.
Proof.
elim: d p => [|d ih] [|b p] //=.
rewrite inE mem_cat cons_path_mem /= !inE.
case: b => /=.
- by move=> /eqP[->].
- rewrite orbF => hp.
  by rewrite shrincs_fxmss_path_false_cons; exact: ih.
Qed.

Lemma shrincs_fxmss_full_path_valid b d p :
  shrincs_fxmss_structure_legal b d ->
  p \in full_paths (shrincs_fxmss_tree_shape b d) -> shrincs_fxmss_path_valid p.
Proof.
move=> hd hp.
have hs := shrincs_fxmss_full_path_depth b d p hp.
apply/andP; split.
- exact: leq_trans hs (shrincs_fxmss_legal_depth b d hd).
- case: b hd hp hs => hd hp hs.
  + apply: leq_trans (idx_of_path_lt p) _.
    rewrite leq_exp2l //.
    exact: leq_trans hs (shrincs_fxmss_balanced_depth d hd).
  + apply: leq_ltn_trans (shrincs_fxmss_full_path_unbalanced d p hp) _.
    change (expn 2 0 < expn 2 64).
    by rewrite ltn_exp2l.
Qed.

Lemma shrincs_fxmss_paired_positions_uniq b d :
  shrincs_fxmss_structure_legal b d ->
  uniq [seq shrincs_fxmss_path_coord p | p <- full_postorder [::]
    (shrincs_fxmss_tree_shape b d)].
Proof.
move=> hd.
rewrite full_postorder_root map_rev rev_uniq map_inj_in_uniq.
- move=> p q hp hq.
  exact: shrincs_fxmss_path_coord_inj p q
    (shrincs_fxmss_full_path_valid b d p hd hp) (shrincs_fxmss_full_path_valid b d q hd
      hq).
- exact: full_paths_uniq.
Qed.

Lemma shrincs_fxmss_paired_positions_budget b d (Q : shrincs_fxmss_resources) :
  shrincs_fxmss_structure_legal b d ->
  size (full_postorder [::] (shrincs_fxmss_tree_shape b d)) <= 2 *
    shrincs_fxmss_leaf_capacity Q - 1.
Proof.
move=> hd.
rewrite full_postorder_size shrincs_fxmss_tree_shape_count.
apply: leq_sub2r.
rewrite leq_mul2l /=.
exact: shrincs_fxmss_leaf_count_bound b d hd.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired oracles *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_paired_eval_op (P : shrincs_fxmss_params) : opsig :=
  (EVAL, (th_T (shrincs_fxmss_hash_function P) × th_M (shrincs_fxmss_hash_function P),
    th_N (shrincs_fxmss_hash_function P))).
Definition shrincs_fxmss_paired_query_op (P : shrincs_fxmss_params) : opsig :=
  (tcrx.XQUERY,
    (th_T (shrincs_fxmss_hash_function P) × th_M (shrincs_fxmss_hash_function P), th_N
      (shrincs_fxmss_hash_function P))).

Section Oracles.
Context (P : shrincs_fxmss_params) (budget : nat) (bit : bool).

Lemma shrincs_fxmss_paired_eval_known (T : choiceType) pp t m
    (k : bytes 16 -> raw_code T) h :
  ~~ fxmss_paired_class t ->
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (resolve (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
      fxmss_partner budget bit)
      (shrincs_fxmss_paired_eval_op P) (t, m)) k) h =
  Pr_code (k (th_eval (shrincs_fxmss_hash_function P) pp t m)) h.
Proof.
move=> ht hp.
rewrite /shrincs_fxmss_paired_eval_op /tcrx.TCRX_game /resolve /= coerce_kleisliE.
by rewrite ht /= Pr_code_get hp.
Qed.

Lemma shrincs_fxmss_paired_query_known (T : choiceType) pp t m
    (k : bytes 16 -> raw_code T) h :
  fxmss_paired_class t ->
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h tcrx.tcrx_rev_loc = false ->
  size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))) < budget ->
  t \notin get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) ->
  fxmss_partner t \notin get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))
    ->
  Pr_code (bind
    (resolve (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
      fxmss_partner budget bit)
      (shrincs_fxmss_paired_query_op P) (t, m)) k) h =
  Pr_code (k (th_eval (shrincs_fxmss_hash_function P) pp (t) m))
    (set_heap
      (set_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P))
        (setm (get_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P)))
          (size (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))))
          (t, m)))
      (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P))
      (rcons (get_heap h (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)))
        (t))).
Proof.
move=> ht hp hr hb hf hpf.
rewrite /shrincs_fxmss_paired_query_op /tcrx.TCRX_game /resolve /= coerce_kleisliE.
rewrite ht /= Pr_code_get hr /= Pr_code_get hb /= hf /= hpf /= Pr_code_get.
rewrite !Pr_code_put Pr_code_get !get_set_heap_neq // hp.
reflexivity.
Qed.

Definition shrincs_fxmss_paired_check_op : opsig :=
  (tcrx.XCHECK, ('nat × (th_T (shrincs_fxmss_hash_function P) × th_M
    (shrincs_fxmss_hash_function P)), 'bool)).
Definition shrincs_fxmss_paired_reveal_op : opsig :=
  (tcrx.XGETPP, ('unit, th_PP (shrincs_fxmss_hash_function P))).

Lemma shrincs_fxmss_paired_check_known (T : choiceType) pp j t0 m0 t m
    (k : bool -> raw_code T) h :
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  get_heap h tcrx.tcrx_rev_loc = true ->
  getm (get_heap h (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P))) j = Some (t0,
    m0) ->
  Pr_code (bind
    (resolve (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
      fxmss_partner budget bit)
      shrincs_fxmss_paired_check_op (j, (t, m))) k) h =
  Pr_code (k (bit && (fxmss_paired_class t &&
    ((t == t0) || (t == fxmss_partner t0)) && (m != m0) &&
    (th_eval (shrincs_fxmss_hash_function P) pp t m == th_eval
      (shrincs_fxmss_hash_function P) pp t0 m0)))) h.
Proof.
move=> hp hr ht.
rewrite /shrincs_fxmss_paired_check_op /tcrx.TCRX_game /resolve /= coerce_kleisliE.
rewrite Pr_code_get hr /= Pr_code_get hp /=.
case: bit => /=; last reflexivity.
by rewrite Pr_code_get ht.
Qed.

Lemma shrincs_fxmss_paired_reveal_known (T : choiceType) pp
    (k : bytes 16 -> raw_code T) h :
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (resolve (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
      fxmss_partner budget bit)
      shrincs_fxmss_paired_reveal_op tt) k) h =
  Pr_code (k pp) (set_heap h tcrx.tcrx_rev_loc true).
Proof.
move=> hp.
rewrite /shrincs_fxmss_paired_reveal_op /tcrx.TCRX_game /resolve /= coerce_kleisliE.
by rewrite Pr_code_get hp /= Pr_code_put.
Qed.

End Oracles.

(* ------------------------------------------------------------------ *)
(** ** Paired leaves *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_paired_leaf_input (P : shrincs_fxmss_params) (a :
  shrincs_fxmss_coord)
    (xs : seq (bytes 16)) : raw_code ('list ('word U8)) :=
  ends ← query_list
    (fun ix : nat * bytes 16 =>
      cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) ix.1 0 15 ix.2)
    (zip (iota 0 wots_c_chain_count) xs) ;;
  ret (flatten [seq tval x | x <- ends]).

Lemma shrincs_fxmss_paired_walk_valid P (L : Locations) a i k n x :
  ValidCode L (tcrx.I_TCRX (shrincs_fxmss_hash_function P))
    (cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) i k n x).
Proof.
elim: n k x => [|n ih] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> y; exact: ih.
Qed.

#[local] Arguments cp_walk : simpl never.

Lemma shrincs_fxmss_paired_leaf_input_valid P (L : Locations) a xs :
  ValidCode L (tcrx.I_TCRX (shrincs_fxmss_hash_function P))
    (shrincs_fxmss_paired_leaf_input P a xs).
Proof.
rewrite /shrincs_fxmss_paired_leaf_input.
eapply valid_bind.
- elim: (zip (iota 0 wots_c_chain_count) xs) => [|ix rest ih]; cbn [query_list].
  + apply valid_ret.
  + eapply valid_bind.
    * exact: shrincs_fxmss_paired_walk_valid.
    * move=> y.
      eapply valid_bind; first exact: ih.
      move=> ys; apply valid_ret.
- move=> ends; ssprove_valid.
Qed.

#[export] Existing Instance shrincs_fxmss_paired_leaf_input_valid.

#[local] Arguments tcrx.TCRX_game : simpl never.
Local Opaque tcrx.TCRX_game.

Lemma shrincs_fxmss_paired_walk_known P budget bit a pp n i k x h
    (T : choiceType) (K : bytes 16 -> raw_code T) :
  k + n <= 15 ->
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (code_link (cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) i k n x)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        budget bit)) K) h =
  Pr_code (K (shrincs_fxmss_walk_value P a pp i x k n)) h.
Proof.
elim: n k x K => [|n ih] k x K hkn hp.
- by rewrite /cp_walk /shrincs_fxmss_walk_value.
- rewrite /cp_walk -/cp_walk /= bind_assoc.
  rewrite (shrincs_fxmss_paired_eval_known P budget bit T pp) //.
  rewrite ih.
  + by rewrite addSnnS.
  + exact hp.
  + (* The chain step uses an evaluation outside the paired target class. *)
    have hkw : k < wcp_w (shrincs_fxmss_leaf_params P a false (uint U8 0)).
      change (k <= 15).
      exact: leq_trans (leq_addr _ _) hkn.
    by rewrite -(eval_Fc_E (shrincs_fxmss_leaf_params P a false (uint U8 0))
      pp i k x hkw).
Qed.

Local Opaque cp_walk.

Lemma shrincs_fxmss_paired_ends_known P budget bit a pp (xs : seq (nat * bytes 16)) h
    (T : choiceType) (K : seq (bytes 16) -> raw_code T) :
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (code_link
      (query_list (fun ix : nat * bytes 16 =>
        cp_walk (shrincs_fxmss_leaf_params P a false (uint U8 0)) ix.1 0 15 ix.2) xs)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        budget bit)) K) h =
  Pr_code (K [seq shrincs_fxmss_walk_value P a pp ix.1 ix.2 0 15 | ix <- xs]) h.
Proof.
move=> hp.
elim: xs K => [|ix xs ih] K; first by [].
rewrite /= code_link_bind bind_assoc.
rewrite (shrincs_fxmss_paired_walk_known P budget bit a pp) //.
by rewrite code_link_bind bind_assoc ih.
Qed.

Definition shrincs_fxmss_paired_input_value P a pp xs : seq UInt8 :=
  flatten [seq tval (shrincs_fxmss_walk_value P a pp ix.1 ix.2 0 15) |
    ix <- zip (iota 0 wots_c_chain_count) xs].

Lemma shrincs_fxmss_paired_input_known P budget bit a pp xs h
    (T : choiceType) (K : seq UInt8 -> raw_code T) :
  get_heap h (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = Some pp ->
  Pr_code (bind
    (code_link (shrincs_fxmss_paired_leaf_input P a xs)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        budget bit)) K) h =
  Pr_code (K (shrincs_fxmss_paired_input_value P a pp xs)) h.
Proof.
move=> hp.
rewrite /shrincs_fxmss_paired_leaf_input code_link_bind bind_assoc.
rewrite (shrincs_fxmss_paired_ends_known P budget bit a pp) //.
by rewrite /= /shrincs_fxmss_paired_input_value -map_comp.
Qed.

Lemma shrincs_fxmss_paired_input_eval P a b d pp xs :
  th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak a)
    (shrincs_fxmss_paired_input_value P a pp xs) =
    shrincs_fxmss_leaf_pubkey P a b d pp xs.
Proof.
rewrite /shrincs_fxmss_paired_input_value
  (map_comp (fun x : bytes 16 => tval x)
    (fun ix : nat * bytes 16 => shrincs_fxmss_walk_value P a pp ix.1 ix.2 0 15)
    (zip (iota 0 wots_c_chain_count) xs)).
reflexivity.
Qed.
