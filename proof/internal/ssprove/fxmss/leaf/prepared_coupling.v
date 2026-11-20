(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.prepared_coupling

    The prepared-root endpoint is perfectly coupled to the re-rooted known-message
    leaf game. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules toolkit.hop_tactics toolkit.batch_map
  toolkit.sample_seq.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.opening leaf.paths leaf.commitments
    leaf.known_message_game
  leaf.known_message leaf.fixed_batch leaf.batch leaf.uniform leaf.context leaf.prepared
  leaf.coupling_sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling invariant *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition prepared_leaf_coupling_private := unionm prepared_leaf_locs (unionm
  leaf_ctx_ud_locs leaf_roots_locs).

Definition prepared_leaf_coupling_counters sp pp sd (entries : seq prepared_leaf_entry)
  : Prop :=
  forall j, j < size (shrincs_fxmss_schedule sp) ->
    (nth prepared_leaf_default entries j).2 =
      known_message_find shrincs_fxmss_sha256 sp pp (leaf_coord_at sp j)
        (leaf_committed_digest sd (leaf_coord_at sp j)).

Definition prepared_leaf_coupling_rel (po0 po1 : option (bytes 16)) (st0 st1 : option
  leaf_opening_state)
    (sd0 sd1 : shrincs_fxmss_digest_table) (lg0 lg1 : seq nat) (entries : seq
      prepared_leaf_entry)
    (roots : seq (bytes 16)) (cache : seq (option leaf_opening_signature))
    (done : bool) (slot : nat) : Prop :=
  po0 = po1 /\ st0 = st1 /\ sd0 = sd1 /\ lg0 = lg1 /\
  match st0 with
  | None => done = false /\ slot = 0
  | Some (pp, sp) =>
      po0 = Some pp /\ shrincs_fxmss_structure_legal sp.1 sp.2 /\
      size entries = size (shrincs_fxmss_schedule sp) /\
      roots = prepared_leaf_roots sp pp entries /\
      cache = leaf_values_last_signatures sp (shrincs_fxmss_schedule sp) entries /\
      prepared_leaf_coupling_counters sp pp sd0 entries
  end.

Definition prepared_leaf_coupling_inv : precond :=
  heap_ignore prepared_leaf_coupling_private ⋊
  rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, ud_pp_loc shrincs_thf);
    (lhs, prepared_leaf_st_loc); (rhs, leaf_ctx_ud_st);
    (lhs, prepared_leaf_sd_loc); (rhs, leaf_ctx_ud_sd);
    (lhs, prepared_leaf_slog_loc); (rhs, leaf_ctx_ud_log);
    (lhs, prepared_leaf_entries_loc); (rhs, leaf_ctx_ud_roots);
    (rhs, leaf_ctx_ud_cache); (rhs, leaf_prepared_done_loc);
    (rhs, leaf_batch_slot_loc)] prepared_leaf_coupling_rel.

Local Opaque wots_c_counter_max known_message_find prepared_leaf_coupling_counters.

Lemma prepared_leaf_coupling_inv_invariant bit :
  Invariant (loc (G_prepared_leaf 0))
    (unionm (loc (C_leaf_roots bit)) (loc (G_leaf_roots 14)))
      prepared_leaf_coupling_inv.
Proof.
rewrite /prepared_leaf_coupling_inv.
ssprove_invariant.
by rewrite /rel_empty /prepared_leaf_coupling_rel /=.
Qed.

Definition prepared_leaf_coupling_reads h0 h1 :=
  prepared_leaf_coupling_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (ud_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h1 leaf_ctx_ud_st)
    (get_heap h0 prepared_leaf_sd_loc) (get_heap h1 leaf_ctx_ud_sd)
    (get_heap h0 prepared_leaf_slog_loc) (get_heap h1 leaf_ctx_ud_log)
    (get_heap h0 prepared_leaf_entries_loc) (get_heap h1 leaf_ctx_ud_roots)
    (get_heap h1 leaf_ctx_ud_cache) (get_heap h1 leaf_prepared_done_loc)
    (get_heap h1 leaf_batch_slot_loc).

Lemma prepared_leaf_coupling_invE h0 h1 :
  prepared_leaf_coupling_inv (h0, h1) -> heap_ignore prepared_leaf_coupling_private (h0,
    h1) /\ prepared_leaf_coupling_reads h0 h1.
Proof. by []. Qed.

Lemma prepared_leaf_coupling_invI h0 h1 :
  heap_ignore prepared_leaf_coupling_private (h0, h1) -> prepared_leaf_coupling_reads h0
    h1 -> prepared_leaf_coupling_inv (h0, h1).
Proof. by split. Qed.

Definition prepared_leaf_coupling_frame (pp : bytes 16) : precond := fun '(h0, h1) =>
  heap_ignore prepared_leaf_coupling_private (h0, h1) /\
  get_heap h0 prepared_leaf_pp_loc = Some pp /\
  get_heap h1 (ud_pp_loc shrincs_thf) = Some pp /\
  get_heap h0 prepared_leaf_slog_loc = get_heap h1 leaf_ctx_ud_log.

Local Opaque get_heap set_heap.

Lemma prepared_leaf_coupling_frame_rhs pp (l : Location) (v : l) h0 h1 :
  fhas prepared_leaf_coupling_private l -> (ud_pp_loc shrincs_thf).1 != l.1 ->
    leaf_ctx_ud_log.1 != l.1 ->
  prepared_leaf_coupling_frame pp (h0, h1) -> prepared_leaf_coupling_frame pp (h0,
    set_heap h1 l v).
Proof.
move=> hl hp hg [hi [h0p [h1p hlog]]].
split.
- apply: heap_ignore_set_r hi.
  exact: fhas_in hl.
- split; first exact: h0p.
  split.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
Qed.

Lemma prepared_leaf_coupling_inv_start pp h0 h1 :
  prepared_leaf_coupling_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  get_heap h0 prepared_leaf_pp_loc = Some pp ->
  prepared_leaf_coupling_frame pp (h0, h1) /\ get_heap h1 leaf_prepared_done_loc = false
    /\
    get_heap h1 leaf_batch_slot_loc = 0.
Proof.
move=> /prepared_leaf_coupling_invE [hi [hp [hst [hsd [hlog hr]]]]] hs hpp.
rewrite hs in hr.
split; last exact: hr.
by split; [exact: hi | split; [exact: hpp | split; [rewrite -hp | exact: hlog]]].
Qed.

Lemma prepared_leaf_coupling_inv_no_seed h0 h1 :
  prepared_leaf_coupling_inv (h0, h1) -> get_heap h0 prepared_leaf_pp_loc = None ->
  get_heap h0 prepared_leaf_st_loc = None.
Proof.
move=> /prepared_leaf_coupling_invE [_ [_ [_ [_ [_ hr]]]]] hp.
case hs: (get_heap h0 prepared_leaf_st_loc) hr => [[pp sp]|] //.
by rewrite hp => -[].
Qed.

Lemma prepared_leaf_coupling_inv_pin pp h0 h1 :
  prepared_leaf_coupling_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  prepared_leaf_coupling_inv (set_heap h0 prepared_leaf_pp_loc (Some pp),
    set_heap h1 (ud_pp_loc shrincs_thf) (Some pp)).
Proof.
move=> /prepared_leaf_coupling_invE [hi [hp [hst [hsd [hlog hr]]]]] hs.
rewrite hs in hr.
apply: prepared_leaf_coupling_invI.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /prepared_leaf_coupling_private /prepared_leaf_locs;
    fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /prepared_leaf_coupling_private /leaf_roots_locs;
      fmap_solve.
- (* Pinning the seed preserves the recorded state and roots. *)
  rewrite /prepared_leaf_coupling_reads /prepared_leaf_coupling_rel !get_set_heap_eq
  !get_set_heap_neq //.
  rewrite -hst hs hsd hlog.
  do 4 (split; first by []).
  exact: hr.
Qed.

Lemma prepared_leaf_coupling_inv_log log h0 h1 :
  prepared_leaf_coupling_inv (h0, h1) ->
  prepared_leaf_coupling_inv (set_heap h0 prepared_leaf_slog_loc log, set_heap h1
    leaf_ctx_ud_log log).
Proof.
move=> /prepared_leaf_coupling_invE [hi [hp [hst [hsd [hlog hr]]]]].
apply: prepared_leaf_coupling_invI.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /prepared_leaf_coupling_private /prepared_leaf_locs;
    fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /prepared_leaf_coupling_private /leaf_ctx_ud_locs;
      fmap_solve.
- by rewrite /prepared_leaf_coupling_reads /prepared_leaf_coupling_rel
  !get_set_heap_eq !get_set_heap_neq //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling eval *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes prepared_leaf_coupling_inv prepared_leaf_verdict
  known_message_find get_heap set_heap
  wots_c_counter_max leaf_recover known_message_gate.

Lemma prepared_leaf_coupling_eval_sim (q : leaf_opening_eval_input) :
  ~~ wots_c_hash_class q.1 ->
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_inv (h0, h1) ⦄
    (pp ← prepared_leaf_seed ;; ret (Th pp q.1 q.2)) ≈
    resolve (G_leaf_roots 14) (EVAL, (leaf_opening_eval_input, bytes 16)) q
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
move=> hq.
rewrite /G_leaf_roots /resolve /= coerce_kleisliE hq.
cbn [assertD].
rewrite /prepared_leaf_seed /leaf_roots_seed.
sync_eq po0 po1.
{ move=> h0 h1 [[/prepared_leaf_coupling_invE [_ [he _]] hp0] hp1].
  by rewrite /rem_inv /= in hp0 hp1; rewrite hp0 hp1 in he.
}
move=> he; subst po1.
case: po0 => [pp|].
- cbn [bind].
  apply r_ret => h0 h1 [[hi _] _].
  by split.
- (* An absent public seed is sampled and stored on both sides. *)
  remember (dBytes 16) as dn eqn:hdn.
  fold @bind.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
  move=> pp.
  apply r_put_vs_put.
  apply r_ret => h0 h1 [h1' [[h0' [[[hi hp0] hp1] ->]] ->]].
  split; first by [].
  have hs := prepared_leaf_coupling_inv_no_seed h0' h1' hi hp0.
  exact: prepared_leaf_coupling_inv_pin hi hs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling sign *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes prepared_leaf_coupling_inv prepared_leaf_verdict
  known_message_find get_heap set_heap
  wots_c_counter_max.

Lemma prepared_leaf_coupling_sign_sim j :
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_inv (h0, h1) ⦄
    prepared_leaf_sign j ≈ leaf_ctx_ud_sign j
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_sign /leaf_ctx_ud_sign.
sync_eq st0 st1.
{ move=> h0 h1 [[/prepared_leaf_coupling_invE [_ [_ [he _]]] hs0] hs1].
  by rewrite /rem_inv /= in hs0 hs1; rewrite hs0 hs1 in he.
}
move=> he; subst st1.
ssprove_sync=> hs.
case: st0 hs => [[pp sp]|] //= hs.
ssprove_sync=> hj.
sync_eq log0 log1.
{ move=> h0 h1 [[[[/prepared_leaf_coupling_invE [_ [_ [_ [_ [he _]]]]] _] _] hl0]
  hl1].
  by rewrite /rem_inv /= in hl0 hl1; rewrite hl0 hl1 in he.
}
move=> he; subst log1.
ssprove_sync=> hfresh.
apply r_put_vs_put.
eapply r_get_remember_lhs => entries.
eapply r_get_remember_rhs => cache.
apply r_ret.
move=> h0 h1 [[[h1' [[h0' [[[[[hi hs0] hs1] hl0] hl1] ->]] ->]] he] hc].
have hi' := prepared_leaf_coupling_inv_log (j :: log0) h0' h1' hi.
split; last exact: hi'.
move: hi => /prepared_leaf_coupling_invE [_ [_ [_ [_ [_ hr]]]]].
change (get_heap h0' prepared_leaf_st_loc = Some (pp, sp)) in hs0.
rewrite hs0 in hr.
move: hr => [hp [hsp [hlen [hroots [hcache hcs]]]]].
change (get_heap (set_heap h0' prepared_leaf_slog_loc (j :: log0))
  prepared_leaf_entries_loc = entries) in he.
change (get_heap (set_heap h1' leaf_ctx_ud_log (j :: log0))
  leaf_ctx_ud_cache = cache) in hc.
rewrite get_set_heap_neq // in he.
rewrite get_set_heap_neq // in hc.
rewrite he in hlen hcache.
rewrite hc in hcache.
rewrite hcache (prepared_leaf_coupling_signatures_nth _ _ _ _ hlen hj).
rewrite (leaf_schedule_nth sp j hsp); first by
  rewrite -(leaf_schedule_length sp hsp).
by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling store *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition prepared_leaf_coupling_store_left pp sp sd entries h :=
  set_heap (set_heap (set_heap h prepared_leaf_st_loc (Some (pp, sp)))
    prepared_leaf_sd_loc sd) prepared_leaf_entries_loc entries.
Definition prepared_leaf_coupling_store_right pp sp sd roots cache h :=
  set_heap (set_heap (set_heap (set_heap h leaf_ctx_ud_st (Some (pp, sp)))
    leaf_ctx_ud_roots roots) leaf_ctx_ud_sd sd) leaf_ctx_ud_cache cache.

Local Opaque get_heap set_heap known_message_find prepared_leaf_coupling_counters
  shrincs_fxmss_schedule.

Lemma prepared_leaf_coupling_inv_finish pp sp sd entries h0 h1 :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size entries = size (shrincs_fxmss_schedule sp) ->
  prepared_leaf_coupling_counters sp pp sd entries ->
  prepared_leaf_coupling_frame pp (h0, h1) ->
  prepared_leaf_coupling_inv (prepared_leaf_coupling_store_left pp sp sd entries h0,
    prepared_leaf_coupling_store_right pp sp sd (prepared_leaf_roots sp pp entries)
      (leaf_values_last_signatures sp (shrincs_fxmss_schedule sp) entries) h1).
Proof.
move=> hsp hlen hc [hi [hp0 [hp1 hlog]]].
apply: prepared_leaf_coupling_invI.
- (* Initialization writes only private locations. *)
  rewrite /prepared_leaf_coupling_store_left /prepared_leaf_coupling_store_right.
  do 3 (apply: heap_ignore_set_l; first by
    apply: fhas_in; rewrite /prepared_leaf_coupling_private /prepared_leaf_locs;
      fmap_solve).
  do 4 (apply: heap_ignore_set_r; first by
    apply: fhas_in; rewrite /prepared_leaf_coupling_private /leaf_ctx_ud_locs;
      fmap_solve).
  exact: hi.
- (* Initialization establishes the state, digest, log and root relation. *)
  rewrite /prepared_leaf_coupling_reads /prepared_leaf_coupling_rel
  /prepared_leaf_coupling_store_left /prepared_leaf_coupling_store_right.
  repeat first [rewrite get_set_heap_eq |
    match goal with
    | |- context [get_heap (set_heap ?h ?l ?v) ?k] =>
      rewrite (get_set_heap_neq h l v k ltac:(reflexivity))
    end].
  rewrite hp0 hp1 hlog.
  by repeat split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling finish *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition prepared_leaf_coupling_left_store sp sd pp entries : raw_code
  leaf_opening_public :=
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := entries ;;
  ret (pp, prepared_leaf_roots sp pp entries).

Definition prepared_leaf_coupling_right_store sp sd pp roots cache : raw_code
  leaf_opening_public :=
  #put leaf_ctx_ud_st := Some (pp, sp) ;;
  #put leaf_ctx_ud_roots := roots ;;
  #put leaf_ctx_ud_sd := sd ;;
  #put leaf_ctx_ud_cache := cache ;;
  ret (pp, roots).

Local Opaque Th dBytes known_message_find wots_c_counter_max prepared_leaf_roots
  leaf_values_last_signatures get_heap set_heap prepared_leaf_coupling_inv
    prepared_leaf_coupling_frame.

Lemma prepared_leaf_coupling_stores_sim sp sd pp entries :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size entries = size (shrincs_fxmss_schedule sp) ->
  prepared_leaf_coupling_counters sp pp sd entries ->
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_frame pp (h0, h1) ⦄
    prepared_leaf_coupling_left_store sp sd pp entries ≈
    prepared_leaf_coupling_right_store sp sd pp (prepared_leaf_roots sp pp entries)
      (leaf_values_last_signatures sp (shrincs_fxmss_schedule sp) entries)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
move=> hsp hlen hc.
rewrite /prepared_leaf_coupling_left_store /prepared_leaf_coupling_right_store.
do 3 apply r_put_lhs.
do 4 apply r_put_rhs.
apply r_ret.
move=> h0 h1.
rewrite /set_rhs /set_lhs /=.
move=> [hr3 [[hr2 [[hr1 [[hr0 [[hl2 [[hl1 [[hl0 [hp ->]] ->]] ->]] ->]] ->]] ->]] ->]].
split; first by [].
exact: prepared_leaf_coupling_inv_finish hsp hlen hc hp.
Qed.

Definition prepared_leaf_coupling_ready pp cache j : precond := fun '(h0, h1) =>
  prepared_leaf_coupling_frame pp (h0, h1) /\
  get_heap h1 leaf_batch_cache_loc = Some cache /\
  get_heap h1 leaf_batch_slot_loc = j.

Lemma prepared_leaf_coupling_ready_step pp cache j h0 h1 :
  prepared_leaf_coupling_ready pp cache j (h0, h1) ->
  prepared_leaf_coupling_ready pp cache j.+1 (h0, set_heap h1 leaf_batch_slot_loc j.+1).
Proof.
move=> [hf [hc hs]].
split.
- apply: prepared_leaf_coupling_frame_rhs hf => //.
- split; last exact: get_set_heap_eq.
  by rewrite get_set_heap_neq.
Qed.

Lemma prepared_leaf_coupling_ready_init pp cache h0 h1 :
  prepared_leaf_coupling_frame pp (h0, h1) -> get_heap h1 leaf_batch_slot_loc = 0 ->
  prepared_leaf_coupling_ready pp cache 0
    (h0, set_heap (set_heap h1 leaf_batch_cache_loc (Some cache))
      leaf_prepared_done_loc true).
Proof.
move=> hf hs.
split.
- apply: prepared_leaf_coupling_frame_rhs => //.
  apply: prepared_leaf_coupling_frame_rhs hf => //.
- split.
  + rewrite (get_set_heap_neq _ leaf_prepared_done_loc _
      leaf_batch_cache_loc ltac:(reflexivity)).
    exact: get_set_heap_eq.
  + by rewrite !get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling drain *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max prepared_leaf_roots
  leaf_values_last_signatures get_heap set_heap prepared_leaf_coupling_inv
    prepared_leaf_coupling_frame.

Lemma prepared_leaf_coupling_drain_sim sp sd pp blocks :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  leaf_blocks_wf (shrincs_fxmss_schedule sp) blocks ->
  let entries := leaf_blocks_last sp pp sd (shrincs_fxmss_schedule sp) blocks in
  let cache := leaf_blocks_cache 14 sp pp sd (shrincs_fxmss_schedule sp) blocks in
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_frame pp (h0, h1) /\
      get_heap h1 leaf_batch_slot_loc = 0 ⦄
    prepared_leaf_coupling_left_store sp sd pp entries ≈
    (#put leaf_batch_cache_loc := Some [seq e.2 | e <- cache] ;;
     #put leaf_prepared_done_loc := true ;;
     ys ← code_link (query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp))
       (G_leaf_roots 14) ;;
     prepared_leaf_coupling_right_store sp sd pp [seq e.1 | e <- cache] ys)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
move=> hsp [hb hwf].
cbv zeta.
cbn [bind].
eapply (r_put_rhs _ _ _ _ (fun '(h0,h1) => prepared_leaf_coupling_frame pp (h0,h1) /\
  get_heap h1 leaf_batch_slot_loc = 0) _).
apply r_put_rhs.
eapply (rpre_weaken_rule (prepared_leaf_coupling_ready pp
  [seq e.2 | e <- leaf_blocks_cache 14 sp pp sd (shrincs_fxmss_schedule sp) blocks]
    0)).
2: { move=> h0 h1 [h1b [[h1a [[hf hs] ->]] ->]].
     exact: prepared_leaf_coupling_ready_init hf hs. }
apply: (@leaf_context_sampling_drain 14 sp (shrincs_fxmss_schedule sp)
  [seq e.2 | e <- leaf_blocks_cache 14 sp pp sd (shrincs_fxmss_schedule sp) blocks] 0
  leaf_opening_public (prepared_leaf_coupling_ready pp
    [seq e.2 | e <- leaf_blocks_cache 14 sp pp sd (shrincs_fxmss_schedule sp) blocks])
  _ (fun _ => prepared_leaf_coupling_left_store sp sd pp
    (leaf_blocks_last sp pp sd (shrincs_fxmss_schedule sp) blocks)) _).
- by move=> j h0 h1 [_ hh].
- exact: prepared_leaf_coupling_ready_step.
- move=> ys ->.
  rewrite leaf_values_drain_full; first exact: leaf_values_cache_size hb.
  rewrite leaf_values_last_encoded leaf_values_last_roots.
  change [seq Th pp (shrincs_fxmss_pk_tweak ae.1)
    (Shrincs.internal.ssprove.fxmss.leaf.compress.pure.r_compress_encode ae.2.1.2)
    | ae <- zip (shrincs_fxmss_schedule sp) (leaf_blocks_last sp pp sd
      (shrincs_fxmss_schedule
      sp) blocks)]
    with (prepared_leaf_roots sp pp (leaf_blocks_last sp pp sd (shrincs_fxmss_schedule
      sp) blocks)).
  eapply rpre_weaken_rule.
  + apply: prepared_leaf_coupling_stores_sim.
    * exact: hsp.
    * exact: leaf_values_last_size hb.
    * move=> j hj.
      rewrite (leaf_values_last_counter _ _ _ _ _ _ hb hj).
      rewrite (leaf_schedule_nth sp j hsp) //.
      by rewrite -(leaf_schedule_length sp hsp).
  + by move=> h0 h1 [hf _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max prepared_leaf_roots
  leaf_values_last_signatures get_heap set_heap prepared_leaf_coupling_inv
    prepared_leaf_coupling_frame.

Definition prepared_leaf_coupling_prepared_tail sp sd pp cache : raw_code
  leaf_opening_public :=
  #put leaf_batch_cache_loc := Some [seq e.2 | e <- cache] ;;
  #put leaf_prepared_done_loc := true ;;
  ys ← code_link (query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp))
    (G_leaf_roots 14) ;;
  prepared_leaf_coupling_right_store sp sd pp [seq e.1 | e <- cache] ys.

Lemma prepared_leaf_coupling_sampling_sim sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_frame pp (h0, h1) /\
      get_heap h1 leaf_batch_slot_loc = 0 ⦄
    (entries ← prepared_leaf_samples sp pp sd ;; prepared_leaf_coupling_left_store sp sd
      pp entries) ≈
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     prepared_leaf_coupling_prepared_tail sp sd pp
       (Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete 14
         (known_message_prepared shrincs_fxmss_sha256 sp pp sd) pp xs))
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
move=> hsp.
rewrite /prepared_leaf_samples leaf_blocks_last_congr /known_message_prepared
  leaf_blocks_flat_congr.
apply: leaf_blocks_blocks_spec => blocks hwf.
exact: prepared_leaf_coupling_drain_sim hsp hwf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling link *)

(* Keep opacity settings local to the linking lemmas. *)
Section PreparedCouplingLink.

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max prepared_leaf_roots
  leaf_values_last_signatures leaf_roots_seed sample_seq
  Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete.

Lemma prepared_leaf_coupling_context_gen_link sp sd :
  code_link (leaf_ctx_ud_gen sp sd) (G_leaf_roots 14) =
  (sto ← get leaf_ctx_ud_st ;;
   #assert ~~ isSome sto ;;
   #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
   #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
   pub ← resolve (G_leaf_roots 14)
     (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
       fixed_public)) (sp, sd) ;;
   ys ← code_link (query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp))
     (G_leaf_roots 14) ;;
   prepared_leaf_coupling_right_store sp sd pub.1 pub.2 ys).
Proof.
rewrite /leaf_ctx_ud_gen.
cbn [code_link].
congr (getr _ _).
apply functional_extensionality => sto.
rewrite !code_link_assertD.
apply f_equal; apply functional_extensionality => hs.
apply f_equal; apply functional_extensionality => hsp.
apply f_equal; apply functional_extensionality => hsd.
rewrite code_link_bind.
cbn [code_link].
rewrite bind_ret.
congr (bind _ _).
apply functional_extensionality => pub.
rewrite code_link_bind.
congr (bind _ _).
apply functional_extensionality => ys.
by case: pub => pp roots; rewrite /prepared_leaf_coupling_right_store.
Qed.

End PreparedCouplingLink.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling gen *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max prepared_leaf_roots
  leaf_values_last_signatures prepared_leaf_samples sample_seq
    prepared_leaf_coupling_inv prepared_leaf_coupling_frame
  get_heap set_heap Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete.

Lemma prepared_leaf_coupling_gen_sim sp sd :
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_inv (h0, h1) ⦄
    prepared_leaf_gen sp sd ≈ code_link (leaf_ctx_ud_gen sp sd) (G_leaf_roots 14)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_gen prepared_leaf_coupling_context_gen_link.
sync_eq st0 st1.
{ move=> h0 h1 [[/prepared_leaf_coupling_invE [_ [_ [he _]]] hs0] hs1].
  by rewrite /rem_inv /= in hs0 hs1; rewrite hs0 hs1 in he.
}
move=> he; subst st1.
ssprove_sync=> hs.
case: st0 hs => [st|] //= hs.
ssprove_sync=> hsp.
ssprove_sync=> hsd.
have hresolve : resolve (G_leaf_roots 14)
  (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
    fixed_public)) (sp, sd) =
  (done ← get leaf_prepared_done_loc ;;
   #assert ~~ done ;;
   #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
   pp ← leaf_roots_seed ;;
   xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
   let cache := Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete 14
     (known_message_prepared shrincs_fxmss_sha256 sp pp sd) pp xs in
   #put leaf_batch_cache_loc := Some [seq e.2 | e <- cache] ;;
   #put leaf_prepared_done_loc := true ;;
   ret (pp, [seq e.1 | e <- cache])).
{ by rewrite /G_leaf_roots /resolve /= coerce_kleisliE. }
rewrite hresolve.
eapply (r_get_bind_rhs leaf_prepared_done_loc false).
{ move=> h0 h1 [[/prepared_leaf_coupling_invE [_ [_ [_ [_ [_ hr]]]]] hs0] hs1].
  change (get_heap h0 prepared_leaf_st_loc = None) in hs0.
  by rewrite hs0 in hr; have [] := hr.
}
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply r_bind_assertD_rhs; first by [].
move=> _.
rewrite bind_assoc /leaf_roots_seed.
cbn [bind].
sync_eq po0 po1.
{ move=> h0 h1 [[[[/prepared_leaf_coupling_invE [_ [he _]] _] _] hp0] hp1].
  by rewrite /rem_inv /= in hp0 hp1; rewrite hp0 hp1 in he.
}
move=> he; subst po1.
case: po0 => [pp|].
- (* An existing public seed starts the prepared-leaf sampling coupling. *)
  cbn [bind].
  rewrite bind_assoc.
  cbn [bind].
  eapply rpre_weaken_rule; first exact: (prepared_leaf_coupling_sampling_sim sp sd pp
    hsp).
  move=> h0 h1 [[[[hi hs0] hs1] hp0] hp1].
  have [hf [_ hslot]] := prepared_leaf_coupling_inv_start pp h0 h1 hi hs0 hp0.
  by split.
- (* An absent public seed is sampled before the prepared-leaf coupling. *)
  remember (dBytes 16) as dn eqn:hdn.
  rewrite !bind_assoc.
  cbn [bind].
  eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
  move=> pp.
  apply r_put_vs_put.
  rewrite hdn.
  rewrite bind_assoc.
  cbn [bind].
  eapply rpre_weaken_rule; first exact: (prepared_leaf_coupling_sampling_sim sp sd pp
    hsp).
  move=> h0 h1 [h1' [[h0' [[[[[hi hs0] hs1] hp0] hp1] ->]] ->]].
  have hi' := prepared_leaf_coupling_inv_pin pp h0' h1' hi hs0.
  have hs' : get_heap (set_heap h0' prepared_leaf_pp_loc (Some pp))
    prepared_leaf_st_loc = None.
  { by rewrite get_set_heap_neq. }
  have [hf [_ hslot]] := prepared_leaf_coupling_inv_start pp _ _ hi' hs'
    (get_set_heap_eq _ _ _).
  by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling check *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes prepared_leaf_coupling_inv prepared_leaf_verdict
  known_message_find get_heap set_heap
  wots_c_counter_max leaf_recover known_message_gate.

Lemma prepared_leaf_coupling_check_sim q :
  ⊢ ⦃ fun '(h0, h1) => prepared_leaf_coupling_inv (h0, h1) ⦄
    prepared_leaf_check 0 q ≈ leaf_ctx_ud_check q
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0, h1) ⦄.
Proof.
rewrite /prepared_leaf_check /leaf_ctx_ud_check.
sync_eq st0 st1.
{ move=> h0 h1 [[/prepared_leaf_coupling_invE [_ [_ [he _]]] hs0] hs1].
  by rewrite /rem_inv /= in hs0 hs1; rewrite hs0 hs1 in he.
}
move=> he; subst st1.
ssprove_sync=> hs.
case: st0 hs => [[pp sp]|] //= hs.
ssprove_sync=> hj.
eapply r_get_remember_lhs => entries.
eapply r_get_remember_rhs => roots.
sync_eq sd0 sd1.
{ move=> h0 h1 [[[[[[/prepared_leaf_coupling_invE [_ [_ [_ [he _]]]] _] _] _] _] hd0]
  hd1].
  by rewrite /rem_inv /= in hd0 hd1; rewrite hd0 hd1 in he.
}
move=> he; subst sd1.
apply r_ret.
move=> h0 h1 [[[[[[hi hs0] hs1] he] hr] hd0] hd1].
split; last exact: hi.
move: hi => /prepared_leaf_coupling_invE [_ [_ [_ [_ [_ hrel]]]]].
change (get_heap h0 prepared_leaf_st_loc = Some (pp, sp)) in hs0.
rewrite hs0 in hrel.
move: hrel => [hp [hsp [hlen [hroots [hcache hcs]]]]].
change (get_heap h0 prepared_leaf_entries_loc = entries) in he.
change (get_heap h1 leaf_ctx_ud_roots = roots) in hr.
change (get_heap h0 prepared_leaf_sd_loc = sd0) in hd0.
rewrite he in hlen hroots hcs.
rewrite hr in hroots.
rewrite hd0 in hcs.
rewrite hroots (prepared_leaf_coupling_roots_nth _ _ _ _ hsp hlen hj).
apply: prepared_leaf_coupling_verdict.
exact: hcs _ hj.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque G_prepared_leaf C_leaf_roots G_leaf_roots known_message_coll_filter
  prepared_leaf_coupling_inv
  leaf_ctx_ud_gen leaf_ctx_ud_sign leaf_ctx_ud_check
  prepared_leaf_gen prepared_leaf_sign prepared_leaf_check.

Lemma prepared_leaf_coupling_perfect :
  perfect I_known_message (known_message_coll_filter ∘ G_prepared_leaf 0)
    (known_message_coll_filter ∘ C_leaf_roots true ∘ G_leaf_roots 14).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ prepared_leaf_coupling_inv).
- exact: prepared_leaf_coupling_inv_invariant.
- intros id S T arg has; fmap_invert has.
  + (* GEN agrees with the prepared-leaf root coupling. *)
    case: arg => sp sd.
    rewrite !resolve_link resolve_known_message_filter_gen.
    cbn [code_link].
    rewrite !bind_ret resolve_prepared_leaf_gen resolve_link resolve_leaf_ctx_ud_gen.
    exact: prepared_leaf_coupling_gen_sim.
  + (* SIGN returns the same cached signature. *)
    rewrite !resolve_link resolve_known_message_filter_sign.
    cbn [code_link].
    rewrite !bind_ret resolve_prepared_leaf_sign resolve_link resolve_leaf_ctx_ud_sign.
    have hv := leaf_ctx_ud_sign_valid emptym arg.
    rewrite (code_link_scheme _ _ _ _ hv).
    exact: prepared_leaf_coupling_sign_sim.
  + (* CHECK agrees with the prepared-leaf verdict. *)
    have hc : resolve (C_leaf_roots true) (known_message_check, (leaf_opening_opening,
      'bool)) arg =
      leaf_ctx_ud_check arg.
    { rewrite resolve_leaf_ctx_ud_check.
      exact: bind_ret. }
    rewrite !resolve_link resolve_known_message_filter_check.
    cbn [code_link].
    rewrite !bind_ret resolve_prepared_leaf_check resolve_link hc.
    have hv := leaf_ctx_ud_check_valid emptym arg.
    rewrite (code_link_scheme _ _ _ _ hv).
    exact: prepared_leaf_coupling_check_sim.
  + rewrite !resolve_link resolve_known_message_filter_eval /known_message_filter_eval !code_link_bind.
    cbn [code_link].
    rewrite resolve_prepared_leaf_eval resolve_link resolve_leaf_ctx_ud_eval !bind_ret.
    cbn [code_link].
    rewrite bind_ret.
    eapply r_bind with
      (mid := fun '(x0,h0) '(x1,h1) => x0 = x1 /\ prepared_leaf_coupling_inv (h0,h1)).
    * apply: prepared_leaf_coupling_eval_sim.
      by have /and3P[hout _] := known_message_filter_request_outside arg.
    * move=> x0 x1.
      apply r_ret => h0 h1 [-> hi].
      by split.
Qed.

Lemma leaf_inner_last_perfect Q :
  perfect I_forge (R_leaf_roots Q true ∘ G_leaf_roots 14)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_prepared_leaf 0).
Proof.
rewrite R_leaf_roots_nom -!sep_link_assoc.
apply static_batch.batch_context_perfect.
apply perfect_sym.
exact: prepared_leaf_coupling_perfect.
Qed.
