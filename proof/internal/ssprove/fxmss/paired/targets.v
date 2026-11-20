(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.paired.targets

    Candidate compression messages use the verifier's chain completion. Escape and
    short-path forgeries give concrete byte-domain paired collisions. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.ud toolkit.relational_rules.
From Shrincs.internal.ssprove.lib.math Require Import
  bin_tree merkle tree_paths full_tree_paths.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.wots Require Import params scheme.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape model.nodes scheme tree.encoding tree.model tree.nodes games
  tree.classify tree.oracles tree.generation paired.routing paired.generation.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Paired candidates *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Definition shrincs_fxmss_paired_candidate P a pp md (sg : bytes (2 +
  WOTS_C_CHAINS_SIZE)) :=
  let W := shrincs_fxmss_leaf_params P a false (uint U8 0) in
  let parts := wcp_sig_decode W sg in
  flatten [seq tval x |
    x <- complete_ends W pp (digest_of W pp md parts.2) parts.1].

Lemma shrincs_fxmss_paired_candidate_spec P a pp md sg node :
  shrincs_fxmss_leaf_recover P a false (uint U8 0) pp md sg = Some node ->
  size (shrincs_fxmss_paired_candidate P a pp md sg) = 512 /\
  th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak a)
    (shrincs_fxmss_paired_candidate P a pp md sg) = node.
Proof.
rewrite /shrincs_fxmss_leaf_recover /shrincs_fxmss_paired_candidate.
case: ifP=> [/andP[hd /eqP hs]|] // [<-].
split; last by [].
rewrite shape.flatten_rows_size
  (size_complete_ends (shrincs_fxmss_leaf_params P a false (uint U8 0))).
by rewrite size_digest_of hs !minnn.
Qed.

Lemma shrincs_fxmss_full_case_extract P st kt a md sg fc :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  shrincs_fxmss_full_case P st kt a md sg = Some fc ->
  exists node,
    shrincs_fxmss_leaf_recover P a false (uint U8 0) st.1.1.1 md
      (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)) = Some node /\
    extract_ok (shrincs_fxmss_tree_node_hash P st.1.1.1) [::]
      (shrincs_fxmss_value_tree P st.1.1.1 (fun c => odflt [::] (getm kt c)) st.2.1
        st.2.2)
      (shrincs_fxmss_signature_path (Z.to_nat (wunsigned a.1)) (wunsigned a.2)) node fc.
Proof.
case: a=> z i.
move=> hd hroot hv hc.
have hz : (Z.to_nat (wunsigned z) < 256)%coq_nat.
  have [hz0 hz1] := wunsigned_range z.
  change (wunsigned z < 256)%Z in hz1.
  lia.
have hi : (0 <= wunsigned i < 2^64)%Z := wunsigned_range i.
have hh := shrincs_fxmss_full_case_spec P st kt (Z.to_nat (wunsigned z))
  (wunsigned i) sg md hd hz hi hroot.
rewrite uint_to_nat wrepr_unsigned in hh.
have [node [hleaf hclass hex]] := hh hv.
rewrite hc in hclass.
case: hclass=> ->.
by exists node; split.
Qed.

Lemma shrincs_fxmss_verified_path_coord P pp root a sg md :
  shrincs_fxmss_verify P pp root a sg md ->
  shrincs_fxmss_path_coord (shrincs_fxmss_signature_path (Z.to_nat (wunsigned a.1))
    (wunsigned a.2)) = a.
Proof.
case: a=> z i.
rewrite /shrincs_fxmss_verify /shrincs_fxmss_recover.
case: ifP=> [/andP[hsig hindex]|] // _.
have [hi0 hi64] := wunsigned_range i.
have [hz0 hz256] := wunsigned_range z.
change (wunsigned z < 256)%Z in hz256.
have hz : (Z.to_nat (wunsigned z) <= 255)%coq_nat by lia.
have hi : (0 <= wunsigned i < 2 ^ Z.of_nat (255-Z.to_nat (wunsigned z)))%Z.
  split; first exact hi0.
  move/Z.ltb_lt: hindex=> hindex.
  apply: (Z.lt_le_trans _ _ _ hindex).
  apply Z.pow_le_mono_r; first lia.
  apply Znat.Nat2Z.inj_le.
  apply/leP.
  exact: geq_minr.
rewrite /shrincs_fxmss_signature_path (shrincs_fxmss_path_coord_of_idx hz hi).
by rewrite uint_to_nat wrepr_unsigned.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired keys *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_keys_sized (as_ : seq shrincs_fxmss_coord) (kt :
  shrincs_fxmss_key_table) : Prop :=
  forall a, a \in as_ -> size (odflt [::] (getm kt a)) = wots_c_chain_count.

Lemma shrincs_fxmss_keys_sized_cons as_ kt a xs :
  size xs = wots_c_chain_count -> shrincs_fxmss_keys_sized as_ kt ->
  shrincs_fxmss_keys_sized (a :: as_) (setm kt a xs).
Proof.
move=> hx hk a'.
rewrite inE setmE.
case: eqP=> [->|hne] /=; first by [].
by move=> ha; exact: hk.
Qed.

Local Opaque sample_seq.sample_seq.

Lemma shrincs_fxmss_sample_keys_sized P as_ (B : choiceType) (pre : precond)
    (post : postcond B B) (k0 k1 : shrincs_fxmss_key_table -> raw_code B) :
  (forall kt, shrincs_fxmss_keys_sized as_ kt -> ⊢ ⦃ pre ⦄ k0 kt ≈ k1 kt ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    kt ← shrincs_fxmss_sample_keys P as_ ;; k0 kt ≈
    kt ← shrincs_fxmss_sample_keys P as_ ;; k1 kt
  ⦃ post ⦄.
Proof.
elim: as_ k0 k1 => [|a as_ ih] k0 k1 hk.
- cbn [shrincs_fxmss_sample_keys bind].
  apply: hk.
  by move=> a; rewrite in_nil.
- (* Sample this leaf and preserve the length condition for the tail. *)
  cbn [shrincs_fxmss_sample_keys].
  rewrite !(bind_assoc (sample_seq.sample_seq (shrincs_fxmss_secret_dist P)
    wots_c_chain_count)).
  eapply (@r_sample_seq_size (bytes 16) (shrincs_fxmss_secret_dist P) B)=> xs hx.
  rewrite !(bind_assoc (shrincs_fxmss_sample_keys P as_)).
  apply: ih=> kt hkt.
  apply: hk.
  exact: shrincs_fxmss_keys_sized_cons hx hkt.
Qed.

Lemma shrincs_fxmss_balanced_leaf_depth d p :
  p \in leaf_paths (shrincs_fxmss_tree_shape true d) -> size p = d.
Proof.
elim: d p => [|d ih] p /=.
- by rewrite inE => /eqP ->.
- rewrite mem_cat => /orP[] /mapP[q hq ->] /=;
    by rewrite (ih q hq).
Qed.

Lemma shrincs_fxmss_unbalanced_leaf_path d p :
  p \in leaf_paths (shrincs_fxmss_tree_shape false d) ->
  p = nseq d false \/ exists k, k < d /\ p = rcons (nseq k false) true.
Proof.
elim: d p => [|d ih] p /=.
- by rewrite inE => /eqP ->; left.
- rewrite mem_cat => /orP[/mapP[q hq ->]|].
  + case: (ih q hq)=> [->|[k [hk ->]]].
    * by left.
    * right; exists k.+1; by split.
  + rewrite !inE => /eqP ->.
    right; exists 0; by split.
Qed.

Lemma shrincs_fxmss_leaf_path_scheduled b d p :
  shrincs_fxmss_structure_legal b d ->
  p \in leaf_paths (shrincs_fxmss_tree_shape b d) ->
  shrincs_fxmss_path_coord p \in shrincs_fxmss_schedule (b,d).
Proof.
move=> hd hp.
rewrite /shrincs_fxmss_schedule.
rewrite mem_pmap.
apply/mapP.
case: b hd hp => hd hp.
- have hs := shrincs_fxmss_balanced_leaf_depth d p hp.
  have hi : idx_of_path p < 2 ^ d by rewrite -hs; exact: idx_of_path_lt.
  exists (idx_of_path p).
  + by rewrite mem_iota /= add0n.
  + by rewrite shrincs_fxmss_select_balanced // /shrincs_fxmss_path_coord hs.
- case: (shrincs_fxmss_unbalanced_leaf_path d p hp)=> [->|[k [hk ->]]].
  + exists d.
    * by rewrite mem_iota /= add0n.
    * by rewrite shrincs_fxmss_select_unbalanced_last //
        /shrincs_fxmss_path_coord size_nseq idx_of_path_false.
  + exists k.
    * rewrite mem_iota /= add0n.
      exact: ltn_trans hk (ltnSn d).
    * (* The right leaf of the unbalanced spine has the selected coordinate. *)
      rewrite shrincs_fxmss_select_unbalanced_right //
        /shrincs_fxmss_path_coord size_rcons size_nseq shrincs_fxmss_path_index_rcons
          idx_of_path_false /=.
      have he : 255-k.+1 = 254-k by rewrite !subnE; lia.
      by rewrite he.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired targets *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Open Scope nat_scope.

Lemma shrincs_fxmss_paired_plan_leaf P pp inputs pos t q a0 :
  subtree_at (bt_posmap (fun p _ =>
    th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak
      (shrincs_fxmss_path_coord p)) (inputs p)) pos t) q =
      Some (BLeaf a0) ->
  (shrincs_fxmss_pk_tweak (shrincs_fxmss_path_coord (pos ++ q)), inputs (pos ++ q)) \in
    shrincs_fxmss_paired_plan P pp inputs pos t /\
  a0 = th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak
    (shrincs_fxmss_path_coord (pos ++ q)))
    (inputs (pos ++ q)).
Proof.
elim: q pos t a0=> [|c q ih] pos [u|l r] a0 //=.
- move=> [<-]; by rewrite cats0 inE eqxx.
- case: c=> /= hs.
  + have [hm he] := ih (rcons pos true) r a0 hs.
    rewrite -cat_rcons; split=> //.
    by rewrite mem_cat hm.
  + have [hm he] := ih (rcons pos false) l a0 hs.
    rewrite -cat_rcons; split=> //.
    by rewrite !mem_cat hm orbT.
Qed.

Lemma shrincs_fxmss_paired_plan_node P pp inputs pos t q l r :
  subtree_at (bt_posmap (fun p _ =>
    th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak
      (shrincs_fxmss_path_coord p)) (inputs p)) pos t) q =
      Some (BNode l r) ->
  (shrincs_fxmss_tree_path_tweak (pos ++ q), shrincs_fxmss_tree_message
    (val_bt (shrincs_fxmss_tree_node_hash P pp) (rcons (pos ++ q) false) l,
     val_bt (shrincs_fxmss_tree_node_hash P pp) (rcons (pos ++ q) true) r)) \in
    shrincs_fxmss_paired_plan P pp inputs pos t.
Proof.
elim: q pos t l r=> [|c q ih] pos [u|tl tr] l r //=.
- case=> <- <-.
  by rewrite cats0 !mem_cat inE eqxx !orbT.
- case: c=> /= hs.
  + have hm := ih (rcons pos true) tr l r hs.
    by rewrite -cat_rcons mem_cat hm.
  + have hm := ih (rcons pos false) tl l r hs.
    by rewrite -cat_rcons !mem_cat hm orbT.
Qed.

Lemma shrincs_fxmss_paired_value_tree P pp keys b d :
  bt_posmap (fun p _ =>
    th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_pk_tweak
      (shrincs_fxmss_path_coord p))
      (shrincs_fxmss_paired_inputs P pp keys p)) [::] (shrincs_fxmss_tree_shape b d) =
    shrincs_fxmss_value_tree P pp keys b d.
Proof.
rewrite /shrincs_fxmss_value_tree.
congr (bt_posmap _ _ _).
apply boolp.funext=> p; apply boolp.funext=> u.
exact: shrincs_fxmss_paired_input_eval.
Qed.

Lemma shrincs_fxmss_paired_input_size P a pp xs :
  size xs = wots_c_chain_count -> size (shrincs_fxmss_paired_input_value P a pp xs) =
    512.
Proof.
move=> hs.
rewrite /shrincs_fxmss_paired_input_value
  (map_comp (fun x : bytes 16 => tval x)
    (fun ix : nat * bytes 16 => shrincs_fxmss_walk_value P a pp ix.1 ix.2 0 15)
    (zip (iota 0 wots_c_chain_count) xs)).
by rewrite shape.flatten_rows_size size_map size_zip size_iota hs minnn.
Qed.

Lemma shrincs_fxmss_paired_leaf_input_size P pp kt b d p :
  shrincs_fxmss_structure_legal b d ->
  shrincs_fxmss_keys_sized (shrincs_fxmss_schedule (b,d)) kt ->
  p \in leaf_paths (shrincs_fxmss_tree_shape b d) ->
  size (shrincs_fxmss_paired_inputs P pp (fun c => odflt [::] (getm kt c)) p) = 512.
Proof.
move=> hd hk hp.
apply: shrincs_fxmss_paired_input_size.
apply: hk.
exact: shrincs_fxmss_leaf_path_scheduled hd hp.
Qed.

Lemma shrincs_fxmss_paired_targets_uniq P pp keys b d :
  shrincs_fxmss_spec_legal_shape b d -> uniq (unzip1 (shrincs_fxmss_paired_targets P pp
    keys b d)).
Proof.
move=> hd.
apply: map_uniq (shrincs_fxmss_paired_targets_fresh P pp keys b d hd).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired witness *)

Import Shrincs.internal.ssprove.fxmss.scheme.

#[local] Open Scope nat_scope.

Definition shrincs_fxmss_paired_win P pp t0 m0 t m : bool :=
  [&& fxmss_paired_class t,
      ((t == t0) || (t == fxmss_partner t0)), m != m0 &
      th_eval (shrincs_fxmss_hash_function P) pp t m == th_eval
        (shrincs_fxmss_hash_function P) pp t0 m0].

Lemma shrincs_fxmss_paired_cross_win P pp leaf a m0 m :
  m != m0 ->
  th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_paired_tweak (~~ leaf) a) m
    =
    th_eval (shrincs_fxmss_hash_function P) pp (shrincs_fxmss_paired_tweak leaf a) m0 ->
  shrincs_fxmss_paired_win P pp (shrincs_fxmss_paired_tweak leaf a) m0
    (shrincs_fxmss_paired_tweak (~~ leaf) a) m.
Proof.
move=> hn he.
by rewrite /shrincs_fxmss_paired_win shrincs_fxmss_paired_tweak_class
  shrincs_fxmss_paired_tweak_partner
  eqxx orbT hn he eqxx.
Qed.

Lemma shrincs_fxmss_full_case_escape P st kt a sg md q x a0 :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  shrincs_fxmss_keys_sized (shrincs_fxmss_schedule st.2) kt ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  shrincs_fxmss_full_case P st kt a md sg = Some (FEscape q x a0) ->
  exists m0,
    (shrincs_fxmss_pk_tweak (shrincs_fxmss_path_coord q), m0) \in
      shrincs_fxmss_paired_targets P st.1.1.1 (fun c => odflt [::] (getm kt c)) st.2.1
        st.2.2 /\
    shrincs_fxmss_paired_win P st.1.1.1 (shrincs_fxmss_pk_tweak
      (shrincs_fxmss_path_coord q)) m0
      (shrincs_fxmss_tree_path_tweak q) (shrincs_fxmss_tree_message x).
Proof.
move=> hd hk hroot hv hc.
have [node [hleaf hex]] := shrincs_fxmss_full_case_extract P st kt a md sg
  (FEscape q x a0) hd hroot hv hc.
case: hex=> qrel [hq hs he].
rewrite cat0s in hq; subst qrel.
have hp := leaf_pathsP hs.
rewrite shrincs_fxmss_value_tree_leaf in hp.
rewrite -(shrincs_fxmss_paired_value_tree P st.1.1.1
  (fun c => odflt [::] (getm kt c)) st.2.1 st.2.2) in hs.
have [hm ha] := shrincs_fxmss_paired_plan_leaf P st.1.1.1 _ [::]
  (shrincs_fxmss_tree_shape st.2.1 st.2.2) q a0 hs.
rewrite cat0s in hm ha.
eexists; split; first exact hm.
apply: (shrincs_fxmss_paired_cross_win P st.1.1.1 true (shrincs_fxmss_path_coord q)).
- (* Leaf and tree inputs have different lengths. *)
  apply/eqP=> hm0.
  have hlen := congr1 size hm0.
  have hdb : shrincs_fxmss_structure_legal st.2.1 st.2.2.
    by apply/shrincs_fxmss_legal_shapeP.
  have hl := shrincs_fxmss_paired_leaf_input_size P st.1.1.1 kt st.2.1 st.2.2 q hdb.
  rewrite -surjective_pairing in hl.
  rewrite shrincs_fxmss_tree_message_size (hl hk hp) in hlen.
  discriminate.
- rewrite /shrincs_fxmss_tree_node_hash in he.
  by rewrite shrincs_fxmss_tree_hash_eval he ha.
Qed.

Lemma shrincs_fxmss_full_case_short P st kt a sg md q a0 :
  shrincs_fxmss_spec_legal_shape st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node P (fun c => odflt [::] (getm kt c))
    st.1.1.1 st.2.1 st.2.2 255 0 ->
  shrincs_fxmss_verify P st.1.1.1 st.1.2 a sg md ->
  shrincs_fxmss_full_case P st kt a md sg = Some (FShort q a0) ->
  exists m0,
    (shrincs_fxmss_tree_path_tweak q, m0) \in
      shrincs_fxmss_paired_targets P st.1.1.1 (fun c => odflt [::] (getm kt c)) st.2.1
        st.2.2 /\
    shrincs_fxmss_paired_win P st.1.1.1 (shrincs_fxmss_tree_path_tweak q) m0
      (shrincs_fxmss_pk_tweak (shrincs_fxmss_path_coord q))
      (shrincs_fxmss_paired_candidate P a st.1.1.1 md (slice sg 0 (2 +
        WOTS_C_CHAINS_SIZE))).
Proof.
move=> hd hroot hv hc.
have [node [hleaf hex]] := shrincs_fxmss_full_case_extract P st kt a md sg
  (FShort q a0) hd hroot hv hc.
case: hex=> l [r [hq ha hs he]].
have hqa : shrincs_fxmss_path_coord q = a.
  rewrite hq cat0s.
  exact: shrincs_fxmss_verified_path_coord hv.
rewrite -(shrincs_fxmss_paired_value_tree P st.1.1.1
  (fun c => odflt [::] (getm kt c)) st.2.1 st.2.2) in hs.
have hm := shrincs_fxmss_paired_plan_node P st.1.1.1 _ [::]
  (shrincs_fxmss_tree_shape st.2.1 st.2.2) _ l r hs.
rewrite -hq in hm.
have [hlen heval] := shrincs_fxmss_paired_candidate_spec P a st.1.1.1 md _ node hleaf.
eexists; split; first exact hm.
apply: (shrincs_fxmss_paired_cross_win P st.1.1.1 false (shrincs_fxmss_path_coord q)).
- apply/eqP=> hm0.
  have hsizes := congr1 size hm0.
  rewrite hlen shrincs_fxmss_tree_message_size in hsizes.
  discriminate.
- (* The paired hash outputs agree at the forged internal node. *)
  change (th_eval (shrincs_fxmss_hash_function P) st.1.1.1 (shrincs_fxmss_pk_tweak
  (shrincs_fxmss_path_coord q))
    (shrincs_fxmss_paired_candidate P a st.1.1.1 md (slice sg 0 (2 +
      WOTS_C_CHAINS_SIZE))) =
    val_bt (shrincs_fxmss_tree_node_hash P st.1.1.1) q (BNode l r)).
  by rewrite -he hqa heval.
Qed.
