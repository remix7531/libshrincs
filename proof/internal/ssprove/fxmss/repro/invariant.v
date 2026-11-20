(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.repro.invariant

    The separated random-oracle table and sequential leaf schedule determine the
    reprogramming heap invariant. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.ro_plus toolkit.reprogram_sep.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games bound.reprogramming repro.games.
From Shrincs.internal.ssprove Require Import shape.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming invariants *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Lemma repro_uint64_inj (i j : nat) :
  i < 2 ^ 64 -> j < 2 ^ 64 -> uint U64 i = uint U64 j -> i = j.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt hi /ltP /Znat.Nat2Z.inj_lt hj
  /(congr1 (@wunsigned U64)).
rewrite Z_of_nat_expn2 in hi; rewrite Z_of_nat_expn2 in hj.
rewrite /uint !wunsigned_repr_small;
  try by split; [exact: Znat.Nat2Z.is_nonneg|].
exact: Znat.Nat2Z.inj.
Qed.

Lemma repro_uint8_inj (i j : nat) :
  i < 2 ^ 8 -> j < 2 ^ 8 -> uint U8 i = uint U8 j -> i = j.
Proof.
move=> /ltP /Znat.Nat2Z.inj_lt hi /ltP /Znat.Nat2Z.inj_lt hj
  /(congr1 (@wunsigned U8)).
rewrite Z_of_nat_expn2 in hi; rewrite Z_of_nat_expn2 in hj.
rewrite /uint !wunsigned_repr_small;
  try by split; [exact: Znat.Nat2Z.is_nonneg|].
exact: Znat.Nat2Z.inj.
Qed.

Lemma repro_select_leaf_inj b d q q' a :
  shrincs_fxmss_select_leaf b d q = Some a ->
  shrincs_fxmss_select_leaf b d q' = Some a -> q = q'.
Proof.
move=> hq hq'.
have [hl hlt] := shrincs_fxmss_select_leaf_some b d q a hq.
have [_ hlt'] := shrincs_fxmss_select_leaf_some b d q' a hq'.
have he : shrincs_fxmss_select_leaf b d q =
    shrincs_fxmss_select_leaf b d q' by rewrite hq hq'.
clear hq hq' a.
case: b hl hlt hlt' he => hl hlt hlt' he.
- (* Balanced tree: the leaf index determines the counter. *)
  have hb := shrincs_fxmss_leaf_count_bound true d hl.
  have h64 := leq_trans hlt hb.
  have h64' := leq_trans hlt' hb.
  rewrite !shrincs_fxmss_select_balanced // in he.
  have hw : uint U64 q = uint U64 q'.
  { exact: (congr1 (fun x : option shrincs_fxmss_coord =>
      (odflt (uint U8 0, uint U64 0) x).2) he). }
  exact: (repro_uint64_inj q q' h64 h64' hw).
- have hd := shrincs_fxmss_legal_depth false d hl.
  rewrite /shrincs_fxmss_select_leaf hl hlt hlt' /= in he.
  case hqd: (q == d) in he; case hqd': (q' == d) in he.
  + by move/eqP: hqd => ->; move/eqP: hqd' => ->.
  + discriminate he.
  + discriminate he.
  + (* Earlier unbalanced leaves have distinct encoded heights. *)
    have hw : uint U8 (254 - q) = uint U8 (254 - q').
    { exact: (congr1 (fun x : option shrincs_fxmss_coord =>
        (odflt (uint U8 0, uint U64 0) x).1) he). }
    have hb z : 254 - z < 2 ^ 8.
    { exact: leq_ltn_trans (leq_subr _ _) (isT : 254 < 2 ^ 8). }
    have hs := repro_uint8_inj _ _ (hb q) (hb q') hw.
    have hn : q <> d by move=> e; rewrite e eqxx in hqd.
    have hn' : q' <> d by move=> e; rewrite e eqxx in hqd'.
    move/ltP: hlt => hlt; move/ltP: hlt' => hlt'; move/leP: hd => hd.
    change (q < d.+1)%coq_nat in hlt.
    change (q' < d.+1)%coq_nat in hlt'.
    rewrite !subnE in hs.
    lia.
Qed.

Definition repro_past b d q a : Prop :=
  exists j, j < q /\ shrincs_fxmss_select_leaf b d j = Some a.

Lemma repro_select_fresh b d q a :
  shrincs_fxmss_select_leaf b d q = Some a -> ~ repro_past b d q a.
Proof.
move=> hq [j [hj hs]].
have he := repro_select_leaf_inj b d q j a hq hs.
by move: hj; rewrite -he ltnn.
Qed.

Lemma repro_past_mono b d q a :
  repro_past b d q a -> repro_past b d q.+1 a.
Proof.
move=> [j [hj hs]]; exists j; split=> //.
exact: ltn_trans hj (ltnSn q).
Qed.

Definition repro_table_consumed b d q
    (rt : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16)) : Prop :=
  forall k, k \in domm rt -> repro_past b d q k.1.

Lemma repro_table_consumed_empty b d q :
  repro_table_consumed b d q emptym.
Proof. by move=> k; rewrite domm0 in_fset0. Qed.

Lemma repro_randomizer_fresh b d q a m rt :
  repro_table_consumed b d q rt ->
  shrincs_fxmss_select_leaf b d q = Some a -> getm rt (a, m) = None.
Proof.
move=> ht hs.
case he: (getm rt (a, m)) => [r|] //.
have hk : (a, m) \in domm rt by rewrite mem_domm he.
exfalso; exact: (repro_select_fresh b d q a hs (ht _ hk)).
Qed.

Lemma repro_table_consumed_set b d q rt a m r :
  repro_table_consumed b d q rt ->
  shrincs_fxmss_select_leaf b d q = Some a ->
  repro_table_consumed b d q.+1 (setm rt (a, m) r).
Proof.
move=> ht hs k.
rewrite domm_set in_fset1U => /orP[/eqP ->|hk].
- exists q; by split; first exact: ltnSn.
- exact: repro_past_mono (ht _ hk).
Qed.

(** Consumption precedes grinding; neither this update nor the next
    fresh-separator fact requires the signing result to be Some. *)
Definition repro_used_consumed b d q (used : seq shrincs_fxmss_coord) : Prop :=
  forall a, a \in used -> repro_past b d q a.

Lemma repro_used_consumed_empty b d q :
  repro_used_consumed b d q [::].
Proof. by move=> a; rewrite in_nil. Qed.

Lemma repro_used_consumed_set b d q used a :
  repro_used_consumed b d q used ->
  shrincs_fxmss_select_leaf b d q = Some a ->
  repro_used_consumed b d q.+1 (a :: used).
Proof.
move=> hu hs a'.
rewrite in_cons => /orP[/eqP ->|ha].
- exists q; by split; first exact: ltnSn.
- exact: repro_past_mono (hu _ ha).
Qed.

Lemma repro_separator_fresh b d q used a :
  repro_used_consumed b d q used ->
  shrincs_fxmss_select_leaf b d q = Some a -> a \notin used.
Proof.
move=> hu hs; apply/negP=> ha.
exact: (repro_select_fresh b d q a hs (hu _ ha)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming heap *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition repro_private_locs : Locations :=
  [fmap shrincs_fxmss_rom_loc; ro_map_loc (bytes 16) repro_suffix (bytes 32);
        ro_qcnt_loc; ro_used_loc shrincs_fxmss_coord].

Definition repro_consumed (sto : option shrincs_fxmss_state) (q : nat)
    (rt : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16))
    (used : seq shrincs_fxmss_coord) : Prop :=
  match sto with
  | None => [ /\ q = 0, rt = emptym & used = [::] ]
  | Some st =>
      repro_table_consumed st.2.1 st.2.2 q rt /\
      repro_used_consumed st.2.1 st.2.2 q used
  end.

Definition repro_heap_relation (Q : shrincs_fxmss_resources)
    (mp mp' : chMap shrincs_fxmss_hmsg_input (bytes 32)) (sto : option
      shrincs_fxmss_state)
    (q : nat) (rt : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16))
    (used : seq shrincs_fxmss_coord) (hc sc : nat) (done : bool) (qc : nat) : Prop :=
  [ /\ mp = mp', repro_consumed sto q rt used &
       repro_quota Q hc sc done qc ].

Definition repro_inv (Q : shrincs_fxmss_resources) : precond :=
  heap_ignore repro_private_locs
  ⋊ rel_app [:: (lhs, shrincs_fxmss_rom_loc);
                (rhs, ro_map_loc (bytes 16) repro_suffix (bytes 32));
                (lhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_next_loc); (lhs,
                  shrincs_fxmss_rt_loc);
                (rhs, ro_used_loc shrincs_fxmss_coord);
                (lhs, shrincs_fxmss_hcnt_loc); (lhs, shrincs_fxmss_scnt_loc);
                (lhs, shrincs_fxmss_done_loc); (rhs, ro_qcnt_loc)]
      (repro_heap_relation Q).

Lemma repro_inv_invariant P Q bit c :
  Invariant (loc (G_forge_randomized P Q bit))
    (unionm (loc (R_reprogram P Q bit))
      (loc (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) c)))
    (repro_inv Q).
Proof.
rewrite /repro_inv.
ssprove_invariant.
split.
- by [].
- by split.
- exact: repro_quota_empty.
Qed.

Lemma repro_consumed_gen st q rt used :
  repro_consumed None q rt used ->
  repro_consumed (Some st) q rt used.
Proof.
move=> [-> -> ->].
split.
- exact: repro_table_consumed_empty.
- exact: repro_used_consumed_empty.
Qed.

Lemma repro_consumed_fresh st q rt used a m :
  repro_consumed (Some st) q rt used ->
  shrincs_fxmss_select_leaf st.2.1 st.2.2 q = Some a ->
  getm rt (a, m) = None /\ a \notin used.
Proof.
move=> [ht hu] hs.
split.
- exact: repro_randomizer_fresh ht hs.
- exact: repro_separator_fresh hu hs.
Qed.

Lemma repro_consumed_sign st q rt used a m r :
  repro_consumed (Some st) q rt used ->
  shrincs_fxmss_select_leaf st.2.1 st.2.2 q = Some a ->
  repro_consumed (Some st) q.+1 (setm rt (a, m) r) (a :: used).
Proof.
move=> [ht hu] hs.
split.
- exact: repro_table_consumed_set ht hs.
- exact: repro_used_consumed_set hu hs.
Qed.
