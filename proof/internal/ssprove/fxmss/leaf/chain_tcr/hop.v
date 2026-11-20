(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.chain_tcr.hop

    Full GEN simulation for both chain-collision bits. Exact leaf chain-collision
    hybrid against static type-16 SMTCR game, with the paper's L * l_sf * w = 512L
    target budget. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core toolkit.relational_rules toolkit.batch_map toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games leaf.opening leaf.paths leaf.commitments leaf.known_message_game
  leaf.known_message leaf.prepared leaf.compress.reduction leaf.compress.pure
  leaf.compress.sampling leaf.compress.hop leaf.chain_tcr.reduction
  leaf.chain_tcr.sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions gen *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes Th prepared_leaf_roots r_compress_record r_chain_tcr_inv
  r_compress_block.

Lemma r_chain_tcr_store_spec sp sd pp uss :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size uss = size (shrincs_fxmss_schedule sp) -> all (fun us => size us == 32) uss ->
  let entries := r_chain_tcr_entries sp pp sd (shrincs_fxmss_schedule sp) uss in
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true
    (unzip1 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp) uss))
    (qmap_from 0 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp) uss)) (h0,
      h1) ⦄
    r_compress_store sp sd pp entries ≈ r_compress_store sp sd pp entries
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0, h1) ⦄.
Proof.
move=> hsp hlen huss entries.
rewrite /r_compress_store.
do 3 apply r_put_vs_put.
apply r_ret.
move=> h0 h1.
rewrite /set_rhs /set_lhs /=.
move=> [h1e [[h0e [[h1d [[h0d [[h1s [[h0s [hp ->]] ->]] ->]] ->]] ->]] ->]].
split; first by [].
exact: r_chain_tcr_inv_finish hsp hlen huss hp.
Qed.

Definition r_chain_tcr_reveal_store sp sd b (results : seq r_compress_result) : raw_code
  leaf_opening_public :=
  pp ← resolve (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b)
    (GETPP, ('unit, bytes 16)) tt ;;
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := [seq entry.2 | entry <- results] ;;
  ret (pp, [seq entry.1 | entry <- results]).

Lemma r_chain_tcr_gen_finish b sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false [::] emptym (h0, h1) ⦄
    (entries ← prepared_leaf_samples sp pp sd ;; r_compress_store sp sd pp entries) ≈
    (results ← code_link (r_chain_tcr_batch sp sd)
       (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b) ;;
     r_chain_tcr_reveal_store sp sd b results)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0, h1) ⦄.
Proof.
move=> hsp.
rewrite /prepared_leaf_samples /r_chain_tcr_batch.
apply: (r_chain_tcr_batch_spec r_chain_tcr_budget b sp pp sd (shrincs_fxmss_schedule sp)
  [::]).
- exact: leaf_schedule_uniq.
- by apply/allP => a ha.
- rewrite add0n /r_chain_tcr_budget.
  apply: leq_mul; last exact: leqnn.
  by have := r_compress_targets_budget sp hsp; rewrite /r_compress_targets size_map.
- (* Revelation stores the completed entries and establishes the invariant. *)
  move=> uss hlen huss; cbv zeta.
  have he : size (r_chain_tcr_entries sp pp sd (shrincs_fxmss_schedule sp) uss) = size
    (shrincs_fxmss_schedule sp).
  { by rewrite /r_chain_tcr_entries size_map size_zip hlen minnn. }
  rewrite /r_chain_tcr_reveal_store (r_compress_results_entries _ _ _ he).
  apply: (r_compress_reveal_spec_class wots_c_hash_class).
  rewrite r_compress_results_roots.
  exact: r_chain_tcr_store_spec hsp hlen huss.
Qed.

Lemma r_chain_tcr_gen_sim b sp sd :
  ⊢ ⦃ fun '(h0, h1) => r_chain_tcr_inv (h0, h1) ⦄
    prepared_leaf_gen sp sd ≈
    code_link (r_chain_tcr_gen sp sd)
      (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_gen /r_chain_tcr_gen.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := r_chain_tcr_inv) _).
{ move=> [h0 h1] /r_chain_tcr_invE [hi _].
  exact: hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
}
move=> sto.
rewrite code_link_assertD.
ssprove_sync => hsto.
case: sto hsto => [st|] //= _.
rewrite code_link_assertD.
ssprove_sync => hsp.
rewrite code_link_assertD.
ssprove_sync => hsd.
cbn [code_link].
rewrite (r_chain_tcr_resolve_eval r_chain_tcr_budget b known_message_pin).
eapply r_bind_assertD_rhs; first by [].
move=> _.
sync_eq po0 po1.
{ move=> h0 h1 [[hi hp0] hp1].
case: hi => hi hs.
have he := r_chain_tcr_inv_seed_eq h0 h1 hi.
rewrite /rem_inv /= in hp0 hp1.
by rewrite hp0 hp1 in he.
} move=> he; subst po1.
case: po0 => [pp|].
- cbn [bind].
rewrite code_link_bind.
cbn [code_link].
rewrite bind_assoc.
eapply rpre_weaken_rule; first exact: (r_chain_tcr_gen_finish b sp sd pp hsp).
move=> h0 h1 [[[hi hs] hp0] hp1].
have [hignore _] := r_chain_tcr_invE h0 h1 hi.
apply: r_chain_tcr_inv_start hi _ hp0.
rewrite (hignore prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve))).
exact: hs.
- change (th_dPP shrincs_thf) with (dBytes 16).
remember (dBytes 16) as dn eqn:hdn.
rewrite !bind_assoc.
cbn [bind].
fold @bind.
rewrite !bind_assoc.
eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
move=> pp.
apply r_put_vs_put.
rewrite hdn.
rewrite code_link_bind.
cbn [code_link].
rewrite bind_assoc.
eapply rpre_weaken_rule; first exact: (r_chain_tcr_gen_finish b sp sd pp hsp).
move=> h0 h1 [h1' [[h0' [[[[hi hs] hp0] hp1] ->]] ->]].
have [hignore _] := r_chain_tcr_invE h0' h1' hi.
apply: r_chain_tcr_inv_pin hi _.
rewrite (hignore prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve))).
exact: hs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions common *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque Th dBytes r_chain_tcr_inv prepared_leaf_verdict prepared_leaf_forged_ends
  prepared_leaf_chain_decision r_chain_tcr_offset.

Lemma r_chain_tcr_sign_sim b j :
  ⊢ ⦃ fun '(h0, h1) => r_chain_tcr_inv (h0, h1) ⦄
    prepared_leaf_sign j ≈ code_link (prepared_leaf_sign j)
      (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0, h1) ⦄.
Proof.
have hv : ValidCode prepared_leaf_locs emptym (prepared_leaf_sign j) :=
  prepared_leaf_sign_valid _ _.
rewrite (code_link_scheme _ _ _ _ hv) /prepared_leaf_sign.
ssprove_sync.
- move=> h0 h1 /r_chain_tcr_invE [hi _].
exact: hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
- move=> sto.
ssprove_sync=> hsto.
ssprove_sync=> hj.
ssprove_sync.
+ move=> h0 h1 /r_chain_tcr_invE [hi _].
exact: hi prepared_leaf_slog_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
+ move=> slog.
ssprove_sync=> hfresh.
ssprove_sync.
* (* Logging the slot preserves the reduction invariant. *)
  change (put_pre_cond prepared_leaf_slog_loc (j :: slog)
    (heap_ignore r_compress_private ⋊
      rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, tcr_pp_loc shrincs_thf);
        (lhs, prepared_leaf_st_loc); (lhs, prepared_leaf_sd_loc); (lhs,
          prepared_leaf_entries_loc); (rhs, tcr_rev_loc);
        (rhs, tcr_tws_loc shrincs_thf); (rhs, tcr_tgts_loc shrincs_thf)] r_chain_tcr_rel)).
  ssprove_invariant.
* ssprove_sync.
{ move=> h0 h1 /r_chain_tcr_invE [hi _].
exact: hi prepared_leaf_entries_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
} move=> entries.
by apply r_ret.
Qed.

Local Opaque r_chain_tcr_inv.
Lemma r_chain_tcr_eval_sim b (q : leaf_opening_eval_input) :
  ~~ wots_c_hash_class q.1 ->
  ⊢ ⦃ fun '(h0, h1) => r_chain_tcr_inv (h0, h1) ⦄
    (pp ← prepared_leaf_seed ;; ret (Th pp q.1 q.2)) ≈
    resolve (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b)
      (EVAL, (leaf_opening_eval_input, bytes 16)) q
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0, h1) ⦄.
Proof.
move=> hq.
rewrite /prepared_leaf_seed (r_chain_tcr_resolve_eval r_chain_tcr_budget b q).
rewrite hq.
cbn [assertD].
sync_eq po0 po1.
{ move=> h0 h1 [[hi hp0] hp1].
have he := r_chain_tcr_inv_seed_eq h0 h1 hi.
rewrite /rem_inv /= in hp0 hp1.
by rewrite hp0 hp1 in he.
} move=> he; subst po1.
case: po0 => [pp|].
- cbn [bind].
apply r_ret => h0 h1 [[hi _] _].
by split.
- change (th_dPP shrincs_thf) with (dBytes 16).
remember (dBytes 16) as dn eqn:hdn.
fold @bind.
rewrite !bind_assoc.
eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
move=> pp.
apply r_put_vs_put.
apply r_ret => h0 h1 [h1' [[h0' [[[hi hp0] hp1] ->]] ->]].
split; first by [].
have hs := r_chain_tcr_inv_no_seed h0' h1' hi hp0.
have hb := r_chain_tcr_inv_pin pp h0' h1' hi hs.
apply: r_chain_tcr_block_initial_inv hb _.
by rewrite get_set_heap_neq.
Qed.

Lemma r_chain_tcr_inv_ready pp sp sd entries h0 h1 :
  (r_chain_tcr_inv ⋊ rem_rhs prepared_leaf_st_loc (Some (pp, sp)) ⋊
    rem_rhs prepared_leaf_entries_loc entries ⋊ rem_rhs prepared_leaf_sd_loc sd) (h0,
      h1) ->
  exists uss,
    [/\ shrincs_fxmss_structure_legal sp.1 sp.2,
      size uss = size (shrincs_fxmss_schedule sp), all (fun us => size us == 32) uss,
      entries = r_chain_tcr_entries sp pp sd (shrincs_fxmss_schedule sp) uss &
      r_compress_block pp true (unzip1 (r_chain_tcr_queries sp pp sd
        (shrincs_fxmss_schedule sp) uss))
        (qmap_from 0 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp) uss))
          (h0, h1)].
Proof.
move=> [[[ /r_chain_tcr_invE [hi [he hr]] hs] hc] hd].
have hs0 := hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
have hc0 := hi prepared_leaf_entries_loc (ltac:(rewrite /r_compress_private;
  fmap_solve)).
have hd0 := hi prepared_leaf_sd_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
change (get_heap h1 prepared_leaf_st_loc = Some (pp, sp)) in hs.
change (get_heap h1 prepared_leaf_entries_loc = entries) in hc.
change (get_heap h1 prepared_leaf_sd_loc = sd) in hd.
rewrite hs0 hs hc0 hc hd0 hd in hr.
move: hr => [hp [hv [hsp [uss [hlen [huss [hentries [hw ht]]]]]]]].
exists uss; split=> //.
split; first exact: hi.
split; first exact: hp.
split; first by rewrite -he.
by repeat split.
Qed.

Lemma r_chain_tcr_check_verdict b sp pp a md entry mw :
  prepared_leaf_verdict (if b then 2 else 3) sp pp a md entry mw =
  if prepared_leaf_verdict 2 sp pp a md entry mw then
    if prepared_leaf_chain_decision sp pp a md entry mw is Some _ then b else true
  else false.
Proof.
case: b.
- by case: (prepared_leaf_verdict 2 sp pp a md entry mw);
    case: (prepared_leaf_chain_decision sp pp a md entry mw).
- rewrite -prepared_leaf_verdict_chain.
  by case: (prepared_leaf_verdict 2 sp pp a md entry mw);
    case: (prepared_leaf_chain_decision sp pp a md entry mw).
Qed.

Lemma r_chain_tcr_check_sim b q :
  ⊢ ⦃ fun '(h0, h1) => r_chain_tcr_inv (h0, h1) ⦄
    prepared_leaf_check (if b then 2 else 3) q ≈ code_link (r_chain_tcr_check q)
      (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_check /r_chain_tcr_check.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := r_chain_tcr_inv) _).
- move=> [h0 h1] /r_chain_tcr_invE [hi _].
  exact: hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
- move=> sto.
  rewrite code_link_assertD.
  ssprove_sync => hsto.
  case: sto hsto => [st|] //= hsto.
  rewrite code_link_assertD.
  ssprove_sync => hj.
  cbn [code_link].
  refine (r_get_vs_get_remember_rhs
    (pre := r_chain_tcr_inv ⋊ rem_rhs prepared_leaf_st_loc (Some st)) _).
  + move=> [h0 h1] [/r_chain_tcr_invE [hi _] _].
    exact: hi prepared_leaf_entries_loc (ltac:(rewrite /r_compress_private;
      fmap_solve)).
  + move=> entries.
    refine (r_get_vs_get_remember_rhs
      (pre := r_chain_tcr_inv ⋊ rem_rhs prepared_leaf_st_loc (Some st) ⋊
        rem_rhs prepared_leaf_entries_loc entries) _).
    * move=> [h0 h1] [[/r_chain_tcr_invE [hi _] _] _].
      exact: hi prepared_leaf_sd_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
    * move=> sd.
      cbn [code_link].
      case: st hsto hj => pp sp hsto hj.
      cbn [fst snd].
      set a := leaf_coord_at sp q.1.
      set md := leaf_committed_digest sd a.
      set entry := nth prepared_leaf_default entries q.1.
      rewrite r_chain_tcr_check_verdict.
      case hv: (prepared_leaf_verdict 2 sp pp a md entry q.2).
      -- case hd: (prepared_leaf_chain_decision sp pp a md entry q.2) => [[jc u]|].
         ++ cbn [code_link].
            rewrite bind_ret r_compress_resolve_check_class.
            eapply (r_get_rhs_pin tcr_rev_loc true).
            { move=> h0 h1 hp.
              have [uss [_ _ _ _ [_ [_ [_ [hr _]]]]]] :=
                r_chain_tcr_inv_ready pp sp sd entries h0 h1 hp.
              exact: hr. }
            cbv beta iota.
            cbn [assertD].
            case: b; cbn [andb].
            ** (* The real game finds the extracted collision in its target table. *)
               eapply r_get_remember_rhs => tg.
               eapply (r_fact (exists t m0,
                 [/\ getm tg (r_chain_tcr_offset sp pp sd q.1 + jc)%N = Some (t, m0),
                   tval u != m0 & Th pp t (tval u) = Th pp t m0])).
               { move=> h0 h1 [hp htg].
                 have [uss [hsp hlen huss he hb]] :=
                   r_chain_tcr_inv_ready pp sp sd entries h0 h1 hp.
                 have [_ [_ [_ [_ [_ hmap]]]]] := hb.
                 change (get_heap h1 (tcr_tgts_loc shrincs_thf) = tg) in htg.
                 rewrite -htg hmap.
                 have hv' := hv; have hd' := hd.
                 rewrite /entry he in hv' hd'.
                 exact: r_chain_tcr_table_collision hsp hlen huss hj hv' hd'. }
               move=> [t [m0 [ht hne hcol]]].
               rewrite ht.
               eapply (r_get_rhs_pin (tcr_pp_loc shrincs_thf) (Some pp)).
               { move=> h0 h1 [hp htg].
                 have [uss [_ _ _ _ [_ [_ [hr _]]]]] :=
                   r_chain_tcr_inv_ready pp sp sd entries h0 h1 hp.
                 exact: hr. }
               cbn [bind].
               rewrite hne hcol eqxx.
               apply r_ret => h0 h1 [[[[hi _] _] _] _].
               by split.
            ** apply r_ret => h0 h1 [[[hi _] _] _].
               by split.
         ++ cbn [code_link].
            apply r_ret => h0 h1 [[[hi _] _] _].
            by split.
      -- cbn [code_link].
         apply r_ret => h0 h1 [[[hi _] _] _].
         by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions hop *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque G_prepared_leaf R_chain_tcr SMTCR_game known_message_coll_filter
  r_chain_tcr_inv.

Lemma r_chain_tcr_perfect b :
  perfect I_known_message
    (known_message_coll_filter ∘ G_prepared_leaf (if b then 2 else 3))
    ((known_message_coll_filter ∘ R_chain_tcr) ∘
      SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ r_chain_tcr_inv).
- exact: r_chain_tcr_inv_invariant.
- intros id S T arg has; fmap_invert has.
+ case: arg => sp sd.
rewrite !resolve_link resolve_known_message_filter_gen.
cbn [code_link].
rewrite !bind_ret resolve_prepared_leaf_gen resolve_r_chain_tcr_gen.
exact: r_chain_tcr_gen_sim.
+ rewrite !resolve_link resolve_known_message_filter_sign.
cbn [code_link].
rewrite !bind_ret.
rewrite resolve_prepared_leaf_sign.
exact: r_chain_tcr_sign_sim.
+ rewrite !resolve_link resolve_known_message_filter_check.
cbn [code_link].
rewrite !bind_ret resolve_prepared_leaf_check resolve_r_chain_tcr_check.
exact: r_chain_tcr_check_sim.
+ rewrite !resolve_link resolve_known_message_filter_eval /known_message_filter_eval !code_link_bind.
cbn [code_link].
rewrite resolve_prepared_leaf_eval resolve_r_chain_tcr_eval.
rewrite !bind_ret.
cbn [code_link].
rewrite bind_ret.
eapply r_bind with (mid := fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_chain_tcr_inv (h0,
  h1)).
- apply: r_chain_tcr_eval_sim.
by have /and3P[hp _ _] := known_message_filter_request_outside arg.
- move=> x0 x1.
apply r_ret => h0 h1 [-> hi].
by split.
Qed.

Lemma R_chain_tcr_real :
  perfect I_known_message (known_message_coll_filter ∘ G_prepared_leaf 2)
    ((known_message_coll_filter ∘ R_chain_tcr) ∘
      SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget true).
Proof. exact: (r_chain_tcr_perfect true). Qed.

Lemma R_chain_tcr_ideal :
  perfect I_known_message (known_message_coll_filter ∘ G_prepared_leaf 3)
    ((known_message_coll_filter ∘ R_chain_tcr) ∘
      SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget false).
Proof. exact: (r_chain_tcr_perfect false). Qed.

Lemma prepared_leaf_chain_collision_advantage (A : adversary I_known_message) :
  Adv (G_prepared_leaf 2) (G_prepared_leaf 3) (A ∘ known_message_coll_filter) =
    AdvOf (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget)
      ((A ∘ known_message_coll_filter) ∘ R_chain_tcr).
Proof.
rewrite -Adv_reduction.
rewrite (Adv_perfect_l (r_chain_tcr_perfect true)) (Adv_perfect_r (r_chain_tcr_perfect
  false)).
rewrite Adv_reduction.
by rewrite sep_link_assoc.
Qed.
