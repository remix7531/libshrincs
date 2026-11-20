(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.compress.hop

    Full GEN simulation for either compression bit. Exact leaf compression hybrid
    against the static SMTCR at type 17 with 2^64 targets. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules toolkit.batch_map toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games leaf.opening leaf.paths leaf.commitments leaf.known_message_game
  leaf.known_message leaf.prepared leaf.compress.reduction leaf.compress.pure
  leaf.compress.sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Compression gen *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition r_compress_store sp sd pp entries : raw_code leaf_opening_public :=
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := entries ;;
  ret (pp, prepared_leaf_roots sp pp entries).

Local Opaque dBytes Th prepared_leaf_roots r_compress_record r_compress_inv
  r_compress_block.

Lemma r_compress_store_spec sp sd pp entries :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size entries = size (shrincs_fxmss_schedule sp) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true (r_compress_targets sp)
    (r_compress_record 0 emptym (shrincs_fxmss_schedule sp) entries) (h0, h1) ⦄
    r_compress_store sp sd pp entries ≈ r_compress_store sp sd pp entries
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0, h1) ⦄.
Proof.
move=> hsp hlen.
rewrite /r_compress_store.
do 3 apply r_put_vs_put.
apply r_ret.
move=> h0 h1.
rewrite /set_rhs /set_lhs /=.
move=> [h1e [[h0e [[h1d [[h0d [[h1s [[h0s [hp ->]] ->]] ->]] ->]] ->]] ->]].
split; first by [].
exact: r_compress_inv_finish hsp hlen hp.
Qed.

Definition r_compress_reveal_store sp sd b (results : seq r_compress_result) : raw_code
  leaf_opening_public :=
  pp ← resolve (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b)
    (GETPP, ('unit, bytes 16)) tt ;;
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := [seq entry.2 | entry <- results] ;;
  ret (pp, [seq entry.1 | entry <- results]).

Lemma r_compress_gen_finish b sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false [::] emptym (h0, h1) ⦄
    (entries ← prepared_leaf_samples sp pp sd ;; r_compress_store sp sd pp entries) ≈
    (results ← code_link (r_compress_batch sp sd)
       (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b) ;;
     r_compress_reveal_store sp sd b results)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0, h1) ⦄.
Proof.
move=> hsp.
rewrite /prepared_leaf_samples /r_compress_batch.
apply: r_compress_batch_spec.
- exact: r_compress_targets_uniq.
- have := r_compress_targets_budget sp hsp.
  by rewrite /r_compress_targets size_map.
- (* Revelation stores the completed entries and establishes the invariant. *)
  move=> entries hlen.
  rewrite /r_compress_reveal_store (r_compress_results_entries _ _ _ hlen).
  apply: r_compress_reveal_spec.
  rewrite r_compress_results_roots.
  exact: r_compress_store_spec hsp hlen.
Qed.

Lemma r_compress_gen_sim b sp sd :
  ⊢ ⦃ fun '(h0, h1) => r_compress_inv (h0, h1) ⦄
    prepared_leaf_gen sp sd ≈
    code_link (r_compress_gen sp sd)
      (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_gen /r_compress_gen.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := r_compress_inv) _).
{ move=> [h0 h1] /r_compress_invE [hi _].
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
rewrite (Shrincs.internal.ssprove.fxmss.leaf.compress.pure.r_compress_resolve_eval
  (shrincs_fxmss_leaf_params instance.shrincs_fxmss_sha256 (uint U8 0, uint U64 0) false
  (uint U8 0)) (2 ^ 64) b known_message_pin).
eapply r_bind_assertD_rhs; first by [].
move=> _.
sync_eq po0 po1.
{ move=> h0 h1 [[hi hp0] hp1].
case: hi => hi hs.
have he := r_compress_inv_seed_eq h0 h1 hi.
rewrite /rem_inv /= in hp0 hp1.
by rewrite hp0 hp1 in he.
} move=> he; subst po1.
case: po0 => [pp|].
- cbn [bind].
rewrite code_link_bind.
cbn [code_link].
rewrite bind_assoc.
eapply rpre_weaken_rule; first exact: (r_compress_gen_finish b sp sd pp hsp).
move=> h0 h1 [[[hi hs] hp0] hp1].
have [hignore _] := r_compress_invE h0 h1 hi.
apply: r_compress_inv_start hi _ hp0.
rewrite (hignore prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve))).
exact: hs.
- change (Shrincs.internal.ssprove.wots.params.wcp_dPP (shrincs_fxmss_leaf_params
  instance.shrincs_fxmss_sha256 (uint U8 0, uint U64 0) false (uint U8 0))) with (dBytes
  16).
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
eapply rpre_weaken_rule; first exact: (r_compress_gen_finish b sp sd pp hsp).
move=> h0 h1 [h1' [[h0' [[[[hi hs] hp0] hp1] ->]] ->]].
have [hignore _] := r_compress_invE h0' h1' hi.
apply: r_compress_inv_pin hi _.
rewrite (hignore prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve))).
exact: hs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Compression common *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque Th dBytes r_compress_inv prepared_leaf_verdict prepared_leaf_forged_ends.

Lemma r_compress_sign_sim b j :
  ⊢ ⦃ fun '(h0, h1) => r_compress_inv (h0, h1) ⦄
    prepared_leaf_sign j ≈ code_link (prepared_leaf_sign j)
      (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0, h1) ⦄.
Proof.
have hv : ValidCode prepared_leaf_locs emptym (prepared_leaf_sign j) :=
  prepared_leaf_sign_valid _ _.
rewrite (code_link_scheme _ _ _ _ hv) /prepared_leaf_sign.
ssprove_sync.
- move=> h0 h1 /r_compress_invE [hi _].
exact: hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
- move=> sto.
ssprove_sync=> hsto.
ssprove_sync=> hj.
ssprove_sync.
+ move=> h0 h1 /r_compress_invE [hi _].
exact: hi prepared_leaf_slog_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
+ move=> slog.
ssprove_sync=> hfresh.
ssprove_sync.
* (* Logging the slot preserves the reduction invariant. *)
  change (put_pre_cond prepared_leaf_slog_loc (j :: slog)
    (heap_ignore r_compress_private ⋊
      rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, tcr_pp_loc shrincs_thf);
        (lhs, prepared_leaf_st_loc); (lhs, prepared_leaf_entries_loc); (rhs, tcr_rev_loc);
        (rhs, tcr_tws_loc shrincs_thf); (rhs, tcr_tgts_loc shrincs_thf)] r_compress_rel)).
  ssprove_invariant.
* ssprove_sync.
{ move=> h0 h1 /r_compress_invE [hi _].
exact: hi prepared_leaf_entries_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
} move=> entries.
by apply r_ret.
Qed.

Local Opaque r_compress_inv.
Lemma r_compress_check_sim b q :
  ⊢ ⦃ fun '(h0, h1) => r_compress_inv (h0, h1) ⦄
    prepared_leaf_check (if b then 1 else 2) q ≈ code_link (r_compress_check q)
      (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_check /r_compress_check.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := r_compress_inv) _).
- move=> [h0 h1] /r_compress_invE [hi _].
exact: hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
- move=> sto.
rewrite code_link_assertD.
ssprove_sync=> hsto.
case: sto hsto => [st|] //= hsto.
rewrite code_link_assertD.
ssprove_sync=> hj.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := r_compress_inv ⋊ rem_rhs prepared_leaf_st_loc
  (Some st)) _).
+ move=> [h0 h1] [/r_compress_invE [hi _] _].
exact: hi prepared_leaf_entries_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
+ move=> entries.
ssprove_sync.
* move=> h0 h1 /r_compress_invE [hi _].
exact: hi prepared_leaf_sd_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
* move=> sd.
cbn [code_link].
case: st hsto hj => pp sp hsto hj.
have hready h0 h1 : (r_compress_inv ⋊ rem_rhs prepared_leaf_st_loc (Some (pp, sp)) ⋊
  rem_rhs
  prepared_leaf_entries_loc entries) (h0, h1) -> r_compress_block pp true
    (r_compress_targets sp) (r_compress_record
  0 emptym (shrincs_fxmss_schedule sp) entries) (h0, h1) /\
  shrincs_fxmss_structure_legal sp.1 sp.2 /\ size entries = size (shrincs_fxmss_schedule
  sp).
{ move=> [[/r_compress_invE [hi [he hr]] hs] hc].
have hs0 := hi prepared_leaf_st_loc (ltac:(rewrite /r_compress_private; fmap_solve)).
have hc0 := hi prepared_leaf_entries_loc (ltac:(rewrite /r_compress_private;
  fmap_solve)).
change (get_heap h1 prepared_leaf_st_loc = Some (pp, sp)) in hs.
change (get_heap h1 prepared_leaf_entries_loc = entries) in hc.
rewrite hs0 hs hc0 hc in hr.
move: hr => [hp [hv [hw [hlen [ht hlegal]]]]].
split; last by split.
split; first exact: hi.
split; first exact: hp.
split; first by rewrite -he.
by repeat split.
} cbn [fst snd].
have hdecision : (if prepared_leaf_verdict 1 sp pp (leaf_coord_at sp q.1)
  (leaf_committed_digest
  sd (leaf_coord_at sp q.1)) (nth prepared_leaf_default entries q.1) q.2 &&
    (prepared_leaf_forged_ends
  sp pp (leaf_coord_at sp q.1) q.2 != (nth prepared_leaf_default entries q.1).1.2) then
    b &&
  ((r_compress_encode (prepared_leaf_forged_ends sp pp (leaf_coord_at sp q.1) q.2) !=
    r_compress_encode (nth
  prepared_leaf_default entries q.1).1.2) && (Th pp (shrincs_fxmss_pk_tweak
    (leaf_coord_at sp
  q.1)) (r_compress_encode (prepared_leaf_forged_ends sp pp (leaf_coord_at sp q.1) q.2))
    == Th pp
  (shrincs_fxmss_pk_tweak (leaf_coord_at sp q.1)) (r_compress_encode (nth
    prepared_leaf_default entries
  q.1).1.2))) else prepared_leaf_verdict 1 sp pp (leaf_coord_at sp q.1)
    (leaf_committed_digest
  sd (leaf_coord_at sp q.1)) (nth prepared_leaf_default entries q.1) q.2) =
    prepared_leaf_verdict (if b
  then 1 else 2) sp pp (leaf_coord_at sp q.1) (leaf_committed_digest sd (leaf_coord_at
  sp q.1)) (nth prepared_leaf_default entries q.1) q.2.
{ case: b; first exact: r_compress_real_check_decision.
exact: r_compress_ideal_check_decision.
} rewrite -hdecision.
case htest: (prepared_leaf_verdict _ _ _ _ _ _ _ && _) .
-- cbn [code_link].
rewrite bind_ret r_compress_resolve_check.
eapply (r_get_rhs_pin tcr_rev_loc true).
{ move=> h0 h1 hp.
have [[_ [_ [_ [hr _]]]] _] := hready h0 h1 hp.
exact: hr.
} cbv beta iota.
cbn [assertD].
case: b hdecision => hdecision; cbn [andb].
++ eapply (r_get_rhs_pin (tcr_tgts_loc shrincs_thf) (r_compress_record 0 emptym
  (shrincs_fxmss_schedule sp) entries)).
{ move=> h0 h1 hp.
have [[_ [_ [_ [_ [_ ht]]]]] _] := hready h0 h1 hp.
exact: ht.
} cbv beta iota.
eapply (r_fact (getm (r_compress_record 0 emptym (shrincs_fxmss_schedule sp) entries)
  q.1 =
  Some (shrincs_fxmss_pk_tweak (leaf_coord_at sp q.1), r_compress_encode (nth
    prepared_leaf_default
  entries q.1).1.2))).
{ move=> h0 h1 hp.
have [_ [hlegal hlen]] := hready h0 h1 hp.
have hr := r_compress_record_lookup 0 emptym (shrincs_fxmss_schedule sp) entries q.1
  hlen hj.
have hq : q.1 < shrincs_fxmss_leaf_count sp.1 sp.2 by rewrite -(leaf_schedule_length sp hlegal).
rewrite add0n (leaf_schedule_nth sp q.1 hlegal hq) in hr.
exact: hr.
} move=> ht.
rewrite ht.
eapply (r_get_rhs_pin (tcr_pp_loc shrincs_thf) (Some pp)).
{ move=> h0 h1 hp.
have [[_ [_ [hr _]]] _] := hready h0 h1 hp.
exact: hr.
} cbn [bind].
apply r_ret => h0 h1 [[hi _] _].
by split.
++ apply r_ret => h0 h1 [[hi _] _].
by split.
-- cbn [code_link].
apply r_ret => h0 h1 [[hi _] _].
by split.
Qed.

Lemma r_compress_eval_sim b (q : leaf_opening_eval_input) :
  ~~ wots_c_pk_class q.1 ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_inv (h0, h1) ⦄
    (pp ← prepared_leaf_seed ;; ret (Th pp q.1 q.2)) ≈
    resolve (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b)
      (EVAL, (leaf_opening_eval_input, bytes 16)) q
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0, h1) ⦄.
Proof.
move=> hq.
rewrite /prepared_leaf_seed
  (Shrincs.internal.ssprove.fxmss.leaf.compress.pure.r_compress_resolve_eval
  (shrincs_fxmss_leaf_params instance.shrincs_fxmss_sha256 (uint U8 0, uint U64 0) false
  (uint U8 0)) (2 ^ 64) b q).
rewrite hq.
cbn [assertD].
sync_eq po0 po1.
{ move=> h0 h1 [[hi hp0] hp1].
have he := r_compress_inv_seed_eq h0 h1 hi.
rewrite /rem_inv /= in hp0 hp1.
by rewrite hp0 hp1 in he.
} move=> he; subst po1.
case: po0 => [pp|].
- cbn [bind].
apply r_ret => h0 h1 [[hi _] _].
by split.
- change (Shrincs.internal.ssprove.wots.params.wcp_dPP (shrincs_fxmss_leaf_params
  instance.shrincs_fxmss_sha256 (uint U8 0, uint U64 0) false (uint U8 0))) with (dBytes
  16).
remember (dBytes 16) as dn eqn:hdn.
fold @bind.
rewrite !bind_assoc.
eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
move=> pp.
apply r_put_vs_put.
apply r_ret => h0 h1 [h1' [[h0' [[[hi hp0] hp1] ->]] ->]].
split; first by [].
have hs := r_compress_inv_no_seed h0' h1' hi hp0.
have hb := r_compress_inv_pin pp h0' h1' hi hs.
apply: r_compress_block_initial_inv hb _.
by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Compression hop *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque G_prepared_leaf R_compress SMTCR_game known_message_coll_filter
  r_compress_inv.

Lemma r_compress_perfect b :
  perfect I_known_message
    (known_message_coll_filter ∘ G_prepared_leaf (if b then 1 else 2))
    ((known_message_coll_filter ∘ R_compress) ∘
      SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ r_compress_inv).
- exact: r_compress_inv_invariant.
- intros id S T arg has; fmap_invert has.
+ case: arg => sp sd.
rewrite !resolve_link resolve_known_message_filter_gen.
cbn [code_link].
rewrite !bind_ret resolve_prepared_leaf_gen resolve_r_compress_gen.
exact: r_compress_gen_sim.
+ rewrite !resolve_link resolve_known_message_filter_sign.
cbn [code_link].
rewrite !bind_ret.
rewrite resolve_prepared_leaf_sign.
exact: r_compress_sign_sim.
+ rewrite !resolve_link resolve_known_message_filter_check.
cbn [code_link].
rewrite !bind_ret resolve_prepared_leaf_check resolve_r_compress_check.
exact: r_compress_check_sim.
+ rewrite !resolve_link resolve_known_message_filter_eval /known_message_filter_eval !code_link_bind.
cbn [code_link].
rewrite resolve_prepared_leaf_eval resolve_r_compress_eval.
rewrite !bind_ret.
cbn [code_link].
rewrite bind_ret.
eapply r_bind with (mid := fun '(x0, h0) '(x1, h1) => x0 = x1 /\ r_compress_inv (h0,
  h1)).
- apply: r_compress_eval_sim.
by have /and3P[_ hp _] := known_message_filter_request_outside arg.
- move=> x0 x1.
apply r_ret => h0 h1 [-> hi].
by split.
Qed.

Lemma prepared_leaf_compression_advantage (A : adversary I_known_message) :
  Adv (G_prepared_leaf 1) (G_prepared_leaf 2) (A ∘ known_message_coll_filter) =
    AdvOf (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64))
      ((A ∘ known_message_coll_filter) ∘ R_compress).
Proof.
rewrite -Adv_reduction.
rewrite (Adv_perfect_l (r_compress_perfect true)) (Adv_perfect_r (r_compress_perfect
  false)).
rewrite Adv_reduction.
by rewrite sep_link_assoc.
Qed.
