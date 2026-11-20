(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.sampling

    Pointwise and scheduled sampling couple the chain-start cache with the PRF
    oracle. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.prf_memo games.prf_memo_state games.prf_memo_coupling
  toolkit.relational_rules toolkit.sample_seq games.prf_memo_real_coupling.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance prf.inputs prf.reduction prf.schedule scheme.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF sampling *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma shrincs_fxmss_prf_derive_leaf_queries pp a b d j n :
  shrincs_fxmss_prf_derive_leaf pp a b d j n =
  prf_memo_queries shrincs_khf_prf
    [seq shrincs_fxmss_prf_input pp a b d k | k <- iota j n].
Proof.
elim: n j => [|n ih] j; first reflexivity.
cbn [shrincs_fxmss_prf_derive_leaf iota map prf_memo_queries].
by rewrite ih.
Qed.

Lemma shrincs_fxmss_prf_queries_cons pp b d a as_ :
  shrincs_fxmss_prf_queries pp b d (a :: as_) =
  [seq shrincs_fxmss_prf_input pp a b d j | j <- iota 0 wots_c_chain_count] ++
    shrincs_fxmss_prf_queries pp b d as_.
Proof. reflexivity. Qed.

Lemma r_prf_ideal_leaf (L : Locations) q qs cnt pp a b d :
  (prf_memo_tab_loc shrincs_khf_prf).1 \in domm L ->
  (prf.prf_qs_loc shrincs_khf_prf).1 \in domm L ->
  prf_memo_cnt_loc.1 \in domm L ->
  let ms := [seq shrincs_fxmss_prf_input pp a b d j | j <- iota 0 wots_c_chain_count] in
  uniq (qs ++ ms) -> cnt + wots_c_chain_count <= q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_rel shrincs_khf_prf L qs cnt (s0,s1) ⦄
    sample_seq (shrincs_fxmss_secret_dist shrincs_fxmss_sha256) wots_c_chain_count
    ≈ code_link (code_link (shrincs_fxmss_prf_derive_leaf pp a b d 0 wots_c_chain_count)
        (prf_memo.R_prf_memo shrincs_khf_prf q)) (prf.PRF_game shrincs_khf_prf q false)
    ⦃ fun '(ys0,s0) '(ys1,s1) => ys0 = ys1 /\
      prf_memo_rel shrincs_khf_prf L (qs ++ ms)
        (cnt + wots_c_chain_count) (s0,s1) ⦄.
Proof.
move=> ht hq hc ms hu hb.
rewrite shrincs_fxmss_prf_derive_leaf_queries.
have hs : size ms = wots_c_chain_count by rewrite /ms size_map size_iota.
fold ms.
rewrite -hs.
apply: r_prf_memo_ideal_queries ht hq hc hu _.
by rewrite hs.
Qed.

(* Keep heap operations and per-leaf queries folded in the table induction. *)
Local Opaque prf_memo_rel kh_dN get_heap set_heap shrincs_fxmss_prf_derive_leaf.

Lemma r_prf_ideal_table (L : Locations) q qs cnt pp b d as_ :
  (prf_memo_tab_loc shrincs_khf_prf).1 \in domm L ->
  (prf.prf_qs_loc shrincs_khf_prf).1 \in domm L ->
  prf_memo_cnt_loc.1 \in domm L ->
  uniq (qs ++ shrincs_fxmss_prf_queries pp b d as_) ->
  cnt + size (shrincs_fxmss_prf_queries pp b d as_) <= q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_rel shrincs_khf_prf L qs cnt (s0,s1) ⦄
    shrincs_fxmss_sample_keys shrincs_fxmss_sha256 as_
    ≈ code_link (code_link (shrincs_fxmss_prf_derive_table pp b d as_)
        (prf_memo.R_prf_memo shrincs_khf_prf q)) (prf.PRF_game shrincs_khf_prf q false)
    ⦃ fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
      prf_memo_rel shrincs_khf_prf L (qs ++ shrincs_fxmss_prf_queries pp b d as_)
        (cnt + size (shrincs_fxmss_prf_queries pp b d as_)) (s0,s1) ⦄.
Proof.
move=> ht hq hc.
elim: as_ qs cnt => [|a rest ih] qs cnt hu hb.
-
  rewrite /shrincs_fxmss_prf_queries /= cats0 addn0.
  simplify_linking.
  apply r_ret.
  by move=> s0 s1 hr; split.
-
  rewrite shrincs_fxmss_prf_queries_cons in hu hb *.
  set ms := [seq shrincs_fxmss_prf_input pp a b d j | j <- iota 0 wots_c_chain_count]
    in hu hb *.
  have hs : size ms = wots_c_chain_count by rewrite /ms size_map size_iota.
  cbn [shrincs_fxmss_sample_keys shrincs_fxmss_prf_derive_table].
  rewrite (code_link_bind (shrincs_fxmss_prf_derive_leaf pp a b d 0
    wots_c_chain_count)).
  rewrite (code_link_bind (code_link
    (shrincs_fxmss_prf_derive_leaf pp a b d 0 wots_c_chain_count)
    (prf_memo.R_prf_memo shrincs_khf_prf q))).
  have hu0 : uniq (qs ++ ms).
  {
    move: hu.
    rewrite catA cat_uniq.
    by move/and3P=> [h _ _].
  }
  have hb0 : cnt + wots_c_chain_count <= q.
  {
    apply: leq_trans _ hb.
    by rewrite size_cat hs leq_add2l leq_addr.
  }
  eapply r_bind with (mid := fun '(xs0,s0) '(xs1,s1) => xs0 = xs1 /\
    prf_memo_rel shrincs_khf_prf L (qs ++ ms)
      (cnt + wots_c_chain_count) (s0,s1)).
  + exact: r_prf_ideal_leaf ht hq hc hu0 hb0.
  +
    move=> xs0 xs1.
    eapply (@r_fact shrincs_fxmss_key_table shrincs_fxmss_key_table (xs0 = xs1)
      (fun '(s0,s1) => xs0 = xs1 /\ prf_memo_rel shrincs_khf_prf L
        (qs ++ ms) (cnt + wots_c_chain_count) (s0,s1)));
      first by move=> s0 s1 [he hr].
    move=> ->.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
      prf_memo_rel shrincs_khf_prf L (qs ++ ms)
        (cnt + wots_c_chain_count) (s0,s1));
      last by move=> s0 s1 [_ hr].
    rewrite (code_link_bind (shrincs_fxmss_prf_derive_table pp b d rest)).
    rewrite (code_link_bind (code_link (shrincs_fxmss_prf_derive_table pp b d rest)
      (prf_memo.R_prf_memo shrincs_khf_prf q))).
    have hu1 : uniq ((qs ++ ms) ++ shrincs_fxmss_prf_queries pp b d rest) by rewrite
      -catA.
    have hb1 : cnt + wots_c_chain_count + size (shrincs_fxmss_prf_queries pp b d rest)
      <= q.
    { by rewrite -addnA -hs -size_cat. }
    eapply r_bind with (mid := fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
      prf_memo_rel shrincs_khf_prf L ((qs ++ ms) ++ shrincs_fxmss_prf_queries pp b d
        rest)
        (cnt + wots_c_chain_count + size (shrincs_fxmss_prf_queries pp b d rest))
          (s0,s1)).
    * exact: ih hu1 hb1.
    *
      move=> kt0 kt1.
      simplify_linking.
      apply r_ret.
      move=> s0 s1 [he hr]; split; first by rewrite he.
      by rewrite -catA -addnA -hs -size_cat in hr.
Qed.

Lemma r_prf_ideal_schedule (L : Locations) Q pp b d :
  (prf_memo_tab_loc shrincs_khf_prf).1 \in domm L ->
  (prf.prf_qs_loc shrincs_khf_prf).1 \in domm L ->
  prf_memo_cnt_loc.1 \in domm L ->
  shrincs_fxmss_structure_legal b d ->
  ⊢ ⦃ fun '(s0,s1) =>
      prf_memo_rel shrincs_khf_prf L [:: shrincs_fxmss_prf_pin pp] 1 (s0,s1) ⦄
    shrincs_fxmss_sample_keys shrincs_fxmss_sha256 (shrincs_fxmss_schedule (b,d))
    ≈ code_link (code_link (shrincs_fxmss_prf_derive_table pp b (uint U8 d)
      (shrincs_fxmss_schedule (b,d)))
        (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
        (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false)
    ⦃ fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
      prf_memo_rel shrincs_khf_prf L
        (shrincs_fxmss_prf_pin pp :: shrincs_fxmss_prf_queries pp b (uint U8 d)
          (shrincs_fxmss_schedule (b,d)))
        (size (shrincs_fxmss_schedule (b,d)) * wots_c_chain_count).+1 (s0,s1) ⦄.
Proof.
move=> ht hq hc hl.
have hu : uniq ([:: shrincs_fxmss_prf_pin pp] ++
    shrincs_fxmss_prf_queries pp b (uint U8 d) (shrincs_fxmss_schedule (b,d))).
{
  rewrite /= shrincs_fxmss_prf_queries_no_pin /=.
  exact: shrincs_fxmss_prf_queries_uniq (shrincs_fxmss_prf_schedule_uniq _).
}
have hb : 1 + size (shrincs_fxmss_prf_queries pp b (uint U8 d) (shrincs_fxmss_schedule
  (b,d)))
    <= shrincs_fxmss_prf_budget Q.
{
  rewrite shrincs_fxmss_prf_queries_size add1n.
  exact: shrincs_fxmss_prf_query_budget hl.
}
have h := @r_prf_ideal_table L (shrincs_fxmss_prf_budget Q) [::
  shrincs_fxmss_prf_pin pp] 1 pp b
  (uint U8 d) (shrincs_fxmss_schedule (b,d)) ht hq hc hu hb.
by rewrite /= shrincs_fxmss_prf_queries_size add1n in h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real chain-start PRF sampling *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint shrincs_fxmss_prf_key_table k pp b d (as_ : seq shrincs_fxmss_coord) :
  shrincs_fxmss_key_table :=
  match as_ with
  | [::] => emptym
  | a :: rest => setm (shrincs_fxmss_prf_key_table k pp b d rest) a
      (shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k)
  end.

Lemma shrincs_fxmss_prf_key_table_lookup k pp b d as_ a :
  a \in as_ -> odflt [::] (getm (shrincs_fxmss_prf_key_table k pp b d as_) a) =
    shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k.
Proof.
elim: as_ => [|x xs ih]; first by rewrite in_nil.
rewrite in_cons /shrincs_fxmss_prf_key_table -/shrincs_fxmss_prf_key_table setmE.
case: eqP => [->|hne]; first by [].
exact: ih.
Qed.

Lemma r_prf_real_leaf (L : Locations) q qs cnt k pp a b d :
  (prf_memo_tab_loc shrincs_khf_prf).1 \in domm L ->
  (prf.prf_qs_loc shrincs_khf_prf).1 \in domm L ->
  prf_memo_cnt_loc.1 \in domm L ->
  let ms := [seq shrincs_fxmss_prf_input pp a b d j | j <- iota 0 wots_c_chain_count] in
  uniq (qs ++ ms) -> cnt + wots_c_chain_count <= q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_key_rel shrincs_khf_prf L qs cnt k (s0,s1) ⦄
    ret (shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k)
    ≈ code_link (code_link (shrincs_fxmss_prf_derive_leaf pp a b d 0 wots_c_chain_count)
        (prf_memo.R_prf_memo shrincs_khf_prf q)) (prf.PRF_game shrincs_khf_prf q true)
    ⦃ fun '(ys0,s0) '(ys1,s1) => ys0 = ys1 /\
      prf_memo_key_rel shrincs_khf_prf L (qs ++ ms)
        (cnt + wots_c_chain_count) k (s0,s1) ⦄.
Proof.
move=> ht hq hc ms hu hb.
have hs : size ms = wots_c_chain_count by rewrite /ms size_map size_iota.
have hb' : cnt + size ms <= q by rewrite hs.
have h := @r_prf_memo_real_queries shrincs_khf_prf L q qs cnt ms k
  ht hq hc hu hb'.
rewrite hs in h.
rewrite shrincs_fxmss_prf_derive_leaf_queries shrincs_fxmss_prf_leaf_keys_eq.
move: h.
by rewrite /ms map_comp.
Qed.
(* Keep heap operations and per-leaf queries folded in the table induction. *)
Local Opaque prf_memo_key_rel kh_dN get_heap set_heap shrincs_fxmss_prf_derive_leaf.

Lemma r_prf_real_table (L : Locations) q qs cnt k pp b d as_ :
  (prf_memo_tab_loc shrincs_khf_prf).1 \in domm L ->
  (prf.prf_qs_loc shrincs_khf_prf).1 \in domm L ->
  prf_memo_cnt_loc.1 \in domm L ->
  uniq (qs ++ shrincs_fxmss_prf_queries pp b d as_) ->
  cnt + size (shrincs_fxmss_prf_queries pp b d as_) <= q ->
  ⊢ ⦃ fun '(s0,s1) => prf_memo_key_rel shrincs_khf_prf L qs cnt k (s0,s1) ⦄
    ret (shrincs_fxmss_prf_key_table k pp b d as_)
    ≈ code_link (code_link (shrincs_fxmss_prf_derive_table pp b d as_)
        (prf_memo.R_prf_memo shrincs_khf_prf q)) (prf.PRF_game shrincs_khf_prf q true)
    ⦃ fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
      prf_memo_key_rel shrincs_khf_prf L (qs ++ shrincs_fxmss_prf_queries pp b d as_)
        (cnt + size (shrincs_fxmss_prf_queries pp b d as_)) k (s0,s1) ⦄.
Proof.
move=> ht hq hc.
elim: as_ qs cnt => [|a rest ih] qs cnt hu hb.
-
  rewrite /shrincs_fxmss_prf_queries /= cats0 addn0.
  simplify_linking.
  apply r_ret.
  by move=> s0 s1 hr; split.
-
  rewrite shrincs_fxmss_prf_queries_cons in hu hb *.
  set ms := [seq shrincs_fxmss_prf_input pp a b d j | j <- iota 0 wots_c_chain_count]
    in hu hb *.
  have hs : size ms = wots_c_chain_count by rewrite /ms size_map size_iota.
  cbn [shrincs_fxmss_prf_key_table shrincs_fxmss_prf_derive_table].
  change (ret (setm (shrincs_fxmss_prf_key_table k pp b d rest) a
    (shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k))) with
    (xs ← ret (shrincs_fxmss_leaf_keys shrincs_fxmss_sha256 a b d pp k) ;;
     kt ← ret (shrincs_fxmss_prf_key_table k pp b d rest) ;; ret (setm kt a xs)).
  rewrite (code_link_bind (shrincs_fxmss_prf_derive_leaf pp a b d 0
    wots_c_chain_count)).
  rewrite (code_link_bind (code_link
    (shrincs_fxmss_prf_derive_leaf pp a b d 0 wots_c_chain_count)
    (prf_memo.R_prf_memo shrincs_khf_prf q))).
  have hu0 : uniq (qs ++ ms).
  {
    move: hu.
    rewrite catA cat_uniq.
    by move/and3P=> [h _ _].
  }
  have hb0 : cnt + wots_c_chain_count <= q.
  {
    apply: leq_trans _ hb.
    by rewrite size_cat hs leq_add2l leq_addr.
  }
  eapply r_bind with (mid := fun '(xs0,s0) '(xs1,s1) => xs0 = xs1 /\
    prf_memo_key_rel shrincs_khf_prf L (qs ++ ms)
      (cnt + wots_c_chain_count) k (s0,s1)).
  + exact: r_prf_real_leaf ht hq hc hu0 hb0.
  +
    move=> xs0 xs1.
    eapply (@r_fact shrincs_fxmss_key_table shrincs_fxmss_key_table (xs0 = xs1)
      (fun '(s0,s1) => xs0 = xs1 /\ prf_memo_key_rel shrincs_khf_prf L
        (qs ++ ms) (cnt + wots_c_chain_count) k (s0,s1)));
      first by move=> s0 s1 [he hr].
    move=> ->.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
      prf_memo_key_rel shrincs_khf_prf L (qs ++ ms)
        (cnt + wots_c_chain_count) k (s0,s1));
      last by move=> s0 s1 [_ hr].
    rewrite (code_link_bind (shrincs_fxmss_prf_derive_table pp b d rest)).
    rewrite (code_link_bind (code_link (shrincs_fxmss_prf_derive_table pp b d rest)
      (prf_memo.R_prf_memo shrincs_khf_prf q))).
    have hu1 : uniq ((qs ++ ms) ++ shrincs_fxmss_prf_queries pp b d rest) by rewrite
      -catA.
    have hb1 : cnt + wots_c_chain_count + size (shrincs_fxmss_prf_queries pp b d rest)
      <= q.
    { by rewrite -addnA -hs -size_cat. }
    eapply r_bind with (mid := fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
      prf_memo_key_rel shrincs_khf_prf L ((qs ++ ms) ++ shrincs_fxmss_prf_queries pp b
        d rest)
        (cnt + wots_c_chain_count + size (shrincs_fxmss_prf_queries pp b d rest)) k
          (s0,s1)).
    * exact: ih hu1 hb1.
    *
      move=> kt0 kt1.
      simplify_linking.
      apply r_ret.
      move=> s0 s1 [he hr]; split; first by rewrite he.
      by rewrite -catA -addnA -hs -size_cat in hr.
Qed.

Lemma r_prf_real_schedule (L : Locations) Q k pp b d :
  (prf_memo_tab_loc shrincs_khf_prf).1 \in domm L ->
  (prf.prf_qs_loc shrincs_khf_prf).1 \in domm L ->
  prf_memo_cnt_loc.1 \in domm L ->
  shrincs_fxmss_structure_legal b d ->
  ⊢ ⦃ fun '(s0,s1) =>
      prf_memo_key_rel shrincs_khf_prf L [:: shrincs_fxmss_prf_pin pp] 1 k (s0,s1) ⦄
    ret (shrincs_fxmss_prf_key_table k pp b (uint U8 d) (shrincs_fxmss_schedule (b,d)))
    ≈ code_link (code_link (shrincs_fxmss_prf_derive_table pp b (uint U8 d)
      (shrincs_fxmss_schedule (b,d)))
        (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
        (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true)
    ⦃ fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
      prf_memo_key_rel shrincs_khf_prf L
        (shrincs_fxmss_prf_pin pp :: shrincs_fxmss_prf_queries pp b (uint U8 d)
          (shrincs_fxmss_schedule (b,d)))
        (size (shrincs_fxmss_schedule (b,d)) * wots_c_chain_count).+1 k (s0,s1) ⦄.
Proof.
move=> ht hq hc hl.
have hu : uniq ([:: shrincs_fxmss_prf_pin pp] ++
    shrincs_fxmss_prf_queries pp b (uint U8 d) (shrincs_fxmss_schedule (b,d))).
{
  rewrite /= shrincs_fxmss_prf_queries_no_pin /=.
  exact: shrincs_fxmss_prf_queries_uniq (shrincs_fxmss_prf_schedule_uniq _).
}
have hb : 1 + size (shrincs_fxmss_prf_queries pp b (uint U8 d) (shrincs_fxmss_schedule
  (b,d)))
    <= shrincs_fxmss_prf_budget Q.
{
  rewrite shrincs_fxmss_prf_queries_size add1n.
  exact: shrincs_fxmss_prf_query_budget hl.
}
have h := @r_prf_real_table L (shrincs_fxmss_prf_budget Q) [::
  shrincs_fxmss_prf_pin pp] 1 k pp b
  (uint U8 d) (shrincs_fxmss_schedule (b,d)) ht hq hc hu hb.
by rewrite /= shrincs_fxmss_prf_queries_size add1n in h.
Qed.
