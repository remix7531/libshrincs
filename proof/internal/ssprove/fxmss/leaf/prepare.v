(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.prepare

    Prepare the complete leaf list through outside-class EVAL before issuing any
    chain challenge. Challenge domains for the complete leaf batch. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.scheduled_batch toolkit.batch_map toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import params scheme hop.intermediates.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance leaf.fixed_batch leaf.commitments leaf.known_message shape
  leaf.paths leaf.known_message_game leaf.batch.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Leaf grind *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_grind_pick (sp : shrincs_fxmss_structure) (a : shrincs_fxmss_coord)
    (hs : seq (bytes 16)) : fixed_leaf :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  (a, omap (fun ch => (ch.1, wcp_digits W ch.2)) (cp_pick W hs)).

Definition leaf_grind_one (sp : shrincs_fxmss_structure) (a : shrincs_fxmss_coord)
    (md : bytes 32) : raw_code fixed_leaf :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  hs ← grind_loop W md (iota 0 (wcp_c_max W)) ;;
  ret (leaf_grind_pick sp a hs).

Definition leaf_grind_batch sp (sd : shrincs_fxmss_digest_table) :=
  query_list (fun a => leaf_grind_one sp a (leaf_committed_digest sd a))
    (shrincs_fxmss_schedule sp).

Lemma leaf_grind_pick_map sp pp a md :
  leaf_grind_pick sp a
    [seq wcp_H_grind (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
      sp.2))
       pp (grind_adrs (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
         sp.2)))
       (md, c) | c <- iota 0 wots_c_counter_max] =
  known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a md.
Proof.
rewrite /leaf_grind_pick cp_pick_map /known_message_prepared_leaf
  /leaf.known_message_game.known_message_find.
by case: find_counter.
Qed.

Lemma leaf_grind_one_valid L I sp a md :
  fhas I (EVAL, (tweak × 'list ('word U8), bytes 16)) ->
  ValidCode L I (leaf_grind_one sp a md).
Proof.
move=> heval.
rewrite /leaf_grind_one.
eapply valid_bind.
- apply: grind_loop_valid.
  exact: heval.
- move=> hs; exact: valid_ret.
Qed.

#[local] Arguments leaf_grind_one : simpl never.

Lemma leaf_grind_batch_valid L I sp sd :
  fhas I (EVAL, (tweak × 'list ('word U8), bytes 16)) ->
  ValidCode L I (leaf_grind_batch sp sd).
Proof.
move=> heval.
rewrite /leaf_grind_batch.
elim: (shrincs_fxmss_schedule sp) => [|a ats ih].
- exact: valid_ret.
- cbn [query_list].
  eapply valid_bind.
  + apply: leaf_grind_one_valid.
    exact: heval.
  + move=> leaf.
    eapply valid_bind; first exact: ih.
    move=> leaves; exact: valid_ret.
Qed.

Lemma resolve_leaf_ud_eval p b q :
  resolve (G_scheduled_ud shrincs_thf wots_c_hash_class p known_message_pin b)
    (EVAL, (tweak × 'list ('word U8), bytes 16)) q =
  (#assert ~~ wots_c_hash_class q.1 ;;
   ppo ← get (ud_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← th_dPP shrincs_thf ;;
                  #put (ud_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp q.1 q.2)).
Proof. by rewrite /G_scheduled_ud /resolve /= coerce_kleisliE. Qed.

Lemma leaf_grind_loop_ud p b sp a pp md cs
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : chList (bytes 16) -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k [seq wcp_H_grind W pp (grind_adrs W) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (grind_loop W md cs)
      (G_scheduled_ud shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin /=.
elim: cs k => [|c cs ih] k hk.
- exact: hk.
- cbn [grind_loop code_link].
  rewrite bind_assoc resolve_leaf_ud_eval.
  eapply r_bind_assertD_rhs.
  + by move=> h0 h1 _.
  + (* An allowed UD evaluation uses the pinned seed for the remaining search. *)
    move=> _.
    eapply (r_get_rhs_pin (ud_pp_loc shrincs_thf) (Some pp));
      first exact: hpin.
    cbn [bind].
    rewrite code_link_bind bind_assoc.
    apply: ih.
    exact: hk.
Qed.

Lemma resolve_leaf_pre_eval p b q :
  resolve (G_scheduled_pre shrincs_thf wots_c_hash_class p known_message_pin b)
    (EVAL, (tweak × 'list ('word U8), bytes 16)) q =
  (#assert ~~ wots_c_hash_class q.1 ;;
   ppo ← get (pre_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← th_dPP shrincs_thf ;;
                  #put (pre_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp q.1 q.2)).
Proof. by rewrite /G_scheduled_pre /resolve /= coerce_kleisliE. Qed.

Lemma leaf_grind_loop_pre p b sp a pp md cs
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : chList (bytes 16) -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp) ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k [seq wcp_H_grind W pp (grind_adrs W) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (grind_loop W md cs)
      (G_scheduled_pre shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin /=.
elim: cs k => [|c cs ih] k hk.
- exact: hk.
- cbn [grind_loop code_link].
  rewrite bind_assoc resolve_leaf_pre_eval.
  eapply r_bind_assertD_rhs.
  + by move=> h0 h1 _.
  + (* An allowed PRE evaluation uses the pinned seed for the remaining search. *)
    move=> _.
    eapply (r_get_rhs_pin (pre_pp_loc shrincs_thf) (Some pp));
      first exact: hpin.
    cbn [bind].
    rewrite code_link_bind bind_assoc.
    apply: ih.
    exact: hk.
Qed.

Lemma leaf_grind_one_ud p b sp a pp md
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : fixed_leaf -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k (known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a md) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (leaf_grind_one sp a md)
      (G_scheduled_ud shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin hk.
rewrite /leaf_grind_one code_link_bind bind_assoc.
apply: leaf_grind_loop_ud hpin _.
cbn [code_link bind].
rewrite leaf_grind_pick_map.
exact: hk.
Qed.

Lemma leaf_grind_one_pre p b sp a pp md
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : fixed_leaf -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k (known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a md) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (leaf_grind_one sp a md)
      (G_scheduled_pre shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin hk.
rewrite /leaf_grind_one code_link_bind bind_assoc.
apply: leaf_grind_loop_pre hpin _.
cbn [code_link bind].
rewrite leaf_grind_pick_map.
exact: hk.
Qed.

Lemma leaf_grind_batch_ud p b sp sd pp
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : chList fixed_leaf -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k (known_message_prepared shrincs_fxmss_sha256 sp pp sd) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (leaf_grind_batch sp sd)
      (G_scheduled_ud shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin.
rewrite /leaf_grind_batch /known_message_prepared.
elim: (shrincs_fxmss_schedule sp) k => [|a ats ih] k hk.
- exact: hk.
- (* The head leaf and remaining schedule agree in the UD game. *)
  cbn [query_list].
  rewrite code_link_bind bind_assoc.
  apply: leaf_grind_one_ud hpin _.
  rewrite code_link_bind bind_assoc.
  apply: ih.
  cbn [code_link bind].
  exact: hk.
Qed.

Lemma leaf_grind_batch_pre p b sp sd pp
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : chList fixed_leaf -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k (known_message_prepared shrincs_fxmss_sha256 sp pp sd) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (leaf_grind_batch sp sd)
      (G_scheduled_pre shrincs_thf wots_c_hash_class p known_message_pin b)) k ⦃ post ⦄.
Proof.
move=> hpin.
rewrite /leaf_grind_batch /known_message_prepared.
elim: (shrincs_fxmss_schedule sp) k => [|a ats ih] k hk.
- exact: hk.
- (* The head leaf and remaining schedule agree in the PRE game. *)
  cbn [query_list].
  rewrite code_link_bind bind_assoc.
  apply: leaf_grind_one_pre hpin _.
  rewrite code_link_bind bind_assoc.
  apply: ih.
  cbn [code_link bind].
  exact: hk.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf batch targets *)

#[local] Open Scope nat_scope.

Lemma fixed_rows_member leaves row :
  row \in fixed_rows leaves ->
  exists leaf, [ /\ leaf \in leaves,
    row.1.1 = leaf.1 & row.1.2 < size (fixed_digits leaf) ].
Proof.
rewrite /fixed_rows => /flattenP[rows /mapP[leaf hleaf ->] /mapP[jd hjd ->]].
exists leaf; split=> //.
- by case: leaf hleaf hjd => [[h i] cd].
- have hj := map_f fst hjd.
  move: hj.
  rewrite -/(unzip1 _) unzip1_zip ?size_iota // mem_iota add0n /=.
  by [].
Qed.

Lemma fixed_rows_keys_cons leaf leaves :
  [seq row.1 | row <- fixed_rows (leaf :: leaves)] =
  [seq (leaf.1, j) | j <- iota 0 (size (fixed_digits leaf))] ++
  [seq row.1 | row <- fixed_rows leaves].
Proof.
rewrite /fixed_rows /= map_cat -map_comp.
congr (_ ++ _).
have hz : unzip1 (zip (iota 0 (size (fixed_digits leaf)))
    (fixed_digits leaf)) = iota 0 (size (fixed_digits leaf)).
  by rewrite unzip1_zip ?size_iota.
rewrite -{2}hz /unzip1 -map_comp.
apply: eq_map => [[j d]].
by case: leaf hz => [[h i] cd].
Qed.

Lemma fixed_rows_keys_uniq leaves :
  uniq [seq leaf.1 | leaf <- leaves] ->
  uniq [seq row.1 | row <- fixed_rows leaves].
Proof.
elim: leaves => [|leaf leaves ih] //= /andP[ha hu].
rewrite fixed_rows_keys_cons cat_uniq.
apply/and3P; split.
- rewrite map_inj_uniq ?iota_uniq //.
  by move=> x y [].
- (* The head leaf's row keys are disjoint from all remaining leaves. *)
  apply/hasP => [[key /mapP[row hrow ->] /mapP[j hj he]]].
  have [leaf' [hleaf' hcoord hj']] := fixed_rows_member leaves row hrow.
  move: ha => /negP hnot.
  apply: hnot.
  apply/mapP.
  exists leaf' => //.
  by rewrite -hcoord he.
- exact: ih hu.
Qed.

Lemma fixed_rows_chain_bound leaves row :
  all (fun leaf => size (fixed_digits leaf) == 32) leaves ->
  row \in fixed_rows leaves -> row.1.2 < 32.
Proof.
move=> hsize hrow.
have [leaf [hleaf _ hj]] := fixed_rows_member leaves row hrow.
have /eqP he := allP hsize leaf hleaf.
by rewrite -he.
Qed.

Lemma fixed_rows_digit_bound leaves row :
  all (fun leaf => all (fun d => d < 16) (fixed_digits leaf)) leaves ->
  row \in fixed_rows leaves -> row.2 < 16.
Proof.
move=> hd.
rewrite /fixed_rows => /flattenP[rows /mapP[leaf hleaf ->] /mapP[jd hjd ->]].
have hj := map_f snd hjd.
have hj' : jd.2 \in fixed_digits leaf.
- move: hj.
  by rewrite -/(unzip2 _) unzip2_zip ?size_iota.
- exact: (allP (allP hd leaf hleaf) jd.2 hj').
Qed.

Lemma fixed_tweak_key_inj r r' k k' :
  r.1.2 < 32 -> r'.1.2 < 32 -> k < 15 -> k' < 15 ->
  fixed_tweak r k = fixed_tweak r' k' -> r.1 = r'.1.
Proof.
move=> hr hr' hk hk' he.
have [ha [hj _]] := shrincs_fxmss_chain_tweak_inj _ _ _ _ _ _ hr hr' hk hk' he.
by rewrite (surjective_pairing r.1) (surjective_pairing r'.1) ha hj.
Qed.

Lemma fixed_tweaks_uniq (rows : seq fixed_row) (pos : fixed_row -> nat) :
  uniq [seq row.1 | row <- rows] ->
  all (fun row => row.1.2 < 32) rows ->
  all (fun row => pos row < 15) rows ->
  uniq [seq fixed_tweak row (pos row) | row <- rows].
Proof.
elim: rows => [|r rows ih] //= /andP[hfresh huniq] /andP[hr hrs]
  /andP[hp hps].
apply/andP; split.
- (* A fresh row key gives a fresh encoded tweak. *)
  apply/negP=> /mapP[r' hr' he].
  have hekey := fixed_tweak_key_inj r r' (pos r) (pos r')
    hr (allP hrs r' hr') hp (allP hps r' hr') he.
  move: hfresh; rewrite hekey.
  by rewrite (map_f fst hr').
- exact: ih huniq hrs hps.
Qed.

Lemma fixed_ud_targets s leaves :
  pmap id (fixed_ud_requests s leaves) =
  [seq fixed_tweak row s | row <- fixed_rows leaves & s.+2 <= row.2].
Proof.
rewrite /fixed_ud_requests.
elim: (fixed_rows leaves) => [|row rows ih] //=.
by case: ifP => _ /=; rewrite ih.
Qed.

Lemma fixed_pre_targets leaves :
  pmap id (fixed_pre_requests leaves) =
  [seq fixed_tweak row row.2.-1 | row <- fixed_rows leaves & 0 < row.2].
Proof.
rewrite /fixed_pre_requests.
elim: (fixed_rows leaves) => [|row rows ih] //=.
by case: row => [key [|d]] /=; rewrite ih.
Qed.

Lemma fixed_ud_targets_uniq s leaves :
  s < 15 ->
  uniq [seq leaf.1 | leaf <- leaves] ->
  all (fun leaf => size (fixed_digits leaf) == 32) leaves ->
  uniq (pmap id (fixed_ud_requests s leaves)).
Proof.
move=> hs hu hl.
rewrite fixed_ud_targets.
apply: fixed_tweaks_uniq.
- apply: (subseq_uniq (map_subseq fst (filter_subseq _ _))).
  exact: fixed_rows_keys_uniq hu.
- apply/allP=> row.
  rewrite mem_filter => /andP[_ hr].
  exact: fixed_rows_chain_bound leaves row hl hr.
- by apply/allP=> row _.
Qed.

Lemma fixed_pre_targets_uniq leaves :
  uniq [seq leaf.1 | leaf <- leaves] ->
  all (fun leaf => size (fixed_digits leaf) == 32) leaves ->
  all (fun leaf => all (fun d => d < 16) (fixed_digits leaf)) leaves ->
  uniq (pmap id (fixed_pre_requests leaves)).
Proof.
move=> hu hl hd.
rewrite fixed_pre_targets.
apply: fixed_tweaks_uniq.
- apply: (subseq_uniq (map_subseq fst (filter_subseq _ _))).
  exact: fixed_rows_keys_uniq hu.
- apply/allP=> row.
  rewrite mem_filter => /andP[_ hr].
  exact: fixed_rows_chain_bound leaves row hl hr.
- apply/allP=> row.
  rewrite mem_filter => /andP[hp hr].
  have hb := fixed_rows_digit_bound leaves row hd hr.
  by rewrite -ltnS (prednK hp).
Qed.

Lemma fixed_ud_targets_class s leaves :
  all wots_c_hash_class (pmap id (fixed_ud_requests s leaves)).
Proof.
rewrite fixed_ud_targets.
by apply/allP=> t /mapP[row _ ->]; apply: fixed_tweak_class.
Qed.

Lemma fixed_pre_targets_class leaves :
  all wots_c_hash_class (pmap id (fixed_pre_requests leaves)).
Proof.
rewrite fixed_pre_targets.
by apply/allP=> t /mapP[row _ ->]; apply: fixed_tweak_class.
Qed.

Lemma known_message_prepared_sizes P sp pp sd :
  all (fun leaf => size (fixed_digits leaf) == 32)
    (known_message_prepared P sp pp sd).
Proof.
apply/allP=> leaf /mapP[a ha ->].
by rewrite known_message_prepared_digits known_message_digits_length.
Qed.

Lemma known_message_prepared_digits_bound P sp pp sd :
  all (fun leaf => all (fun d => d < 16) (fixed_digits leaf))
    (known_message_prepared P sp pp sd).
Proof.
apply/allP=> leaf /mapP[a ha ->].
rewrite known_message_prepared_digits /known_message_digits.
case: known_message_find => [c|].
- exact: (wcp_digits_wf (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) _).
- by rewrite all_nseq.
Qed.

Lemma leaf_ud_targets_uniq P sp pp sd s :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 15 ->
  uniq (pmap id (fixed_ud_requests s (known_message_prepared P sp pp sd))).
Proof.
move=> hsp hs.
apply: fixed_ud_targets_uniq hs _ (known_message_prepared_sizes P sp pp sd).
rewrite known_message_prepared_coordinates.
exact: leaf_schedule_uniq hsp.
Qed.

Lemma leaf_pre_targets_uniq P sp pp sd :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  uniq (pmap id (fixed_pre_requests (known_message_prepared P sp pp sd))).
Proof.
move=> hsp.
apply: fixed_pre_targets_uniq _ (known_message_prepared_sizes P sp pp sd)
  (known_message_prepared_digits_bound P sp pp sd).
rewrite known_message_prepared_coordinates.
exact: leaf_schedule_uniq hsp.
Qed.

Lemma leaf_chain_budget_eq : 32 * 2 ^ 64 = 2 ^ 69.
Proof. by rewrite -[32]/(2 ^ 5) -expnD. Qed.

Lemma leaf_ud_domain P sp pp sd s :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  [ /\ all wots_c_hash_class
         (pmap id (fixed_ud_requests s (known_message_prepared P sp pp sd))),
       uniq (pmap id (fixed_ud_requests s (known_message_prepared P sp pp sd))) &
       count isSome (fixed_ud_requests s (known_message_prepared P sp pp sd))
         <= 2 ^ 69 ].
Proof.
move=> hsp hs.
split.
- exact: fixed_ud_targets_class.
- apply: leaf_ud_targets_uniq hsp _.
  exact: ltnW hs.
- apply: leq_trans (leaf_ud_target_budget P sp pp sd s) _.
  rewrite -leaf_chain_budget_eq (leaf_schedule_length sp hsp).
  apply: leq_mul.
  + exact: leqnn.
  + exact: shrincs_fxmss_leaf_count_bound hsp.
Qed.

Lemma leaf_pre_domain P sp pp sd :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  [ /\ all wots_c_hash_class
         (pmap id (fixed_pre_requests (known_message_prepared P sp pp sd))),
       uniq (pmap id (fixed_pre_requests (known_message_prepared P sp pp sd))) &
       count isSome (fixed_pre_requests (known_message_prepared P sp pp sd))
         <= 2 ^ 69 ].
Proof.
move=> hsp.
split.
- exact: fixed_pre_targets_class.
- exact: leaf_pre_targets_uniq hsp.
- apply: leq_trans (leaf_pre_target_budget P sp pp sd) _.
  rewrite -leaf_chain_budget_eq (leaf_schedule_length sp hsp).
  apply: leq_mul.
  + exact: leqnn.
  + exact: shrincs_fxmss_leaf_count_bound hsp.
Qed.
