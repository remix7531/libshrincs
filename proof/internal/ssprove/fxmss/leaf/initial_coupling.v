(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.initial_coupling

    The initial prepared-root endpoint is perfectly coupled to ordinary known-
    message leaf signing. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules toolkit.batch_map toolkit.sample_seq
  toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.opening leaf.paths leaf.commitments
    leaf.known_message_game
  leaf.known_message leaf.fixed_batch leaf.batch leaf.uniform leaf.context leaf.prepared
  leaf.coupling_sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling invariant *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition known_message_coupling_private := unionm known_message_locs (unionm
  leaf_ctx_ud_locs leaf_roots_locs).

Definition known_message_coupling_rel (po0 po1 : option (bytes 16)) (st0 st1 : option
  leaf_opening_state)
    (sd0 sd1 : shrincs_fxmss_digest_table) (lg0 lg1 : seq nat) (kt :
      shrincs_fxmss_key_table)
    (roots : seq (bytes 16)) (cache0 cache1 : seq (option leaf_opening_signature))
    (done : bool) (slot : nat) : Prop :=
  po0 = po1 /\ st0 = st1 /\ sd0 = sd1 /\ lg0 = lg1 /\
  match st0 with
  | None => done = false /\ slot = 0
  | Some (pp, sp) =>
      po0 = Some pp /\ shrincs_fxmss_structure_legal sp.1 sp.2 /\
      roots = leaf_opening_roots shrincs_fxmss_sha256 sp pp kt /\ cache0 = cache1
  end.

Definition known_message_coupling_inv : precond :=
  heap_ignore known_message_coupling_private ⋊
  rel_app [:: (lhs, leaf_opening_pp_loc); (rhs, ud_pp_loc shrincs_thf);
    (lhs, leaf_opening_st_loc); (rhs, leaf_ctx_ud_st);
    (lhs, known_message_sd_loc); (rhs, leaf_ctx_ud_sd);
    (lhs, leaf_opening_slog_loc); (rhs, leaf_ctx_ud_log);
    (lhs, leaf_opening_keys_loc); (rhs, leaf_ctx_ud_roots);
    (lhs, known_message_cache_loc); (rhs, leaf_ctx_ud_cache); (rhs,
      leaf_prepared_done_loc);
    (rhs, leaf_batch_slot_loc)] known_message_coupling_rel.

Lemma leaf_opening_rootsE P sp pp kt :
  leaf_opening_roots P sp pp kt =
    [seq leaf_pk P sp pp a (odflt [::] (getm kt a))
     | a <- shrincs_fxmss_schedule sp].
Proof. by []. Qed.

Lemma leaf_winE P sp pp a md sg xs :
  leaf_win P sp pp a md sg xs =
    (leaf_recover P sp pp a md sg == Some (leaf_pk P sp pp a xs)).
Proof. by []. Qed.

Local Opaque wots_c_counter_max known_message_find.

Lemma known_message_coupling_inv_invariant bit :
  Invariant (loc (G_known_message shrincs_fxmss_sha256 bit))
    (unionm (loc (C_leaf_roots bit)) (loc (G_leaf_roots 0))) known_message_coupling_inv.
Proof.
rewrite /known_message_coupling_inv.
ssprove_invariant.
by rewrite /rel_empty /known_message_coupling_rel /=.
Qed.

Definition known_message_coupling_reads h0 h1 :=
  known_message_coupling_rel (get_heap h0 leaf_opening_pp_loc) (get_heap h1 (ud_pp_loc
    shrincs_thf))
    (get_heap h0 leaf_opening_st_loc) (get_heap h1 leaf_ctx_ud_st)
    (get_heap h0 known_message_sd_loc) (get_heap h1 leaf_ctx_ud_sd)
    (get_heap h0 leaf_opening_slog_loc) (get_heap h1 leaf_ctx_ud_log)
    (get_heap h0 leaf_opening_keys_loc) (get_heap h1 leaf_ctx_ud_roots)
    (get_heap h0 known_message_cache_loc) (get_heap h1 leaf_ctx_ud_cache)
    (get_heap h1 leaf_prepared_done_loc)
    (get_heap h1 leaf_batch_slot_loc).

Lemma known_message_coupling_invE h0 h1 :
  known_message_coupling_inv (h0, h1) -> heap_ignore known_message_coupling_private (h0,
    h1) /\ known_message_coupling_reads h0 h1.
Proof. by []. Qed.

Lemma known_message_coupling_invI h0 h1 :
  heap_ignore known_message_coupling_private (h0, h1) -> known_message_coupling_reads h0
    h1 -> known_message_coupling_inv (h0, h1).
Proof. by split. Qed.

Definition known_message_coupling_frame (pp : bytes 16) : precond := fun '(h0, h1) =>
  heap_ignore known_message_coupling_private (h0, h1) /\
  get_heap h0 leaf_opening_pp_loc = Some pp /\
  get_heap h1 (ud_pp_loc shrincs_thf) = Some pp /\
  get_heap h0 leaf_opening_slog_loc = get_heap h1 leaf_ctx_ud_log.

Local Opaque get_heap set_heap.

Lemma known_message_coupling_frame_rhs pp (l : Location) (v : l) h0 h1 :
  fhas known_message_coupling_private l -> (ud_pp_loc shrincs_thf).1 != l.1 ->
    leaf_ctx_ud_log.1 != l.1 ->
  known_message_coupling_frame pp (h0, h1) -> known_message_coupling_frame pp (h0,
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

Lemma known_message_coupling_inv_start pp h0 h1 :
  known_message_coupling_inv (h0, h1) -> get_heap h0 leaf_opening_st_loc = None ->
  get_heap h0 leaf_opening_pp_loc = Some pp ->
  known_message_coupling_frame pp (h0, h1) /\ get_heap h1 leaf_prepared_done_loc = false
    /\
    get_heap h1 leaf_batch_slot_loc = 0.
Proof.
move=> /known_message_coupling_invE [hi [hp [hst [hsd [hlog hr]]]]] hs hpp.
rewrite hs in hr.
split; last exact: hr.
by split; [exact: hi | split; [exact: hpp | split; [rewrite -hp | exact: hlog]]].
Qed.

Lemma known_message_coupling_inv_no_seed h0 h1 :
  known_message_coupling_inv (h0, h1) -> get_heap h0 leaf_opening_pp_loc = None ->
  get_heap h0 leaf_opening_st_loc = None.
Proof.
move=> /known_message_coupling_invE [_ [_ [_ [_ [_ hr]]]]] hp.
case hs: (get_heap h0 leaf_opening_st_loc) hr => [[pp sp]|] //.
by rewrite hp => -[].
Qed.

Lemma known_message_coupling_inv_pin pp h0 h1 :
  known_message_coupling_inv (h0, h1) -> get_heap h0 leaf_opening_st_loc = None ->
  known_message_coupling_inv (set_heap h0 leaf_opening_pp_loc (Some pp),
    set_heap h1 (ud_pp_loc shrincs_thf) (Some pp)).
Proof.
move=> /known_message_coupling_invE [hi [hp [hst [hsd [hlog hr]]]]] hs.
rewrite hs in hr.
apply: known_message_coupling_invI.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /known_message_coupling_private /known_message_locs;
    fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /known_message_coupling_private /leaf_roots_locs;
      fmap_solve.
- (* Pinning the seed preserves the recorded state and roots. *)
  rewrite /known_message_coupling_reads /known_message_coupling_rel !get_set_heap_eq
  !get_set_heap_neq //.
  rewrite -hst hs hsd hlog.
  do 4 (split; first by []).
  exact: hr.
Qed.

Lemma known_message_coupling_inv_log log h0 h1 :
  known_message_coupling_inv (h0, h1) ->
  known_message_coupling_inv (set_heap h0 leaf_opening_slog_loc log, set_heap h1
    leaf_ctx_ud_log log).
Proof.
move=> /known_message_coupling_invE [hi [hp [hst [hsd [hlog hr]]]]].
apply: known_message_coupling_invI.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /known_message_coupling_private /known_message_locs;
    fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /known_message_coupling_private /leaf_ctx_ud_locs;
      fmap_solve.
- by rewrite /known_message_coupling_reads /known_message_coupling_rel
  !get_set_heap_eq !get_set_heap_neq //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling store *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition known_message_coupling_store_left pp sp sd kt cache h :=
  set_heap (set_heap (set_heap (set_heap h leaf_opening_st_loc (Some (pp, sp)))
    leaf_opening_keys_loc kt) known_message_sd_loc sd) known_message_cache_loc cache.
Definition known_message_coupling_store_right pp sp sd roots cache h :=
  set_heap (set_heap (set_heap (set_heap h leaf_ctx_ud_st (Some (pp, sp)))
    leaf_ctx_ud_roots roots) leaf_ctx_ud_sd sd) leaf_ctx_ud_cache cache.

Local Opaque get_heap set_heap known_message_find shrincs_fxmss_schedule.

Lemma known_message_coupling_inv_finish pp sp sd kt cache h0 h1 :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  known_message_coupling_frame pp (h0, h1) ->
  known_message_coupling_inv (known_message_coupling_store_left pp sp sd kt cache h0,
    known_message_coupling_store_right pp sp sd (leaf_opening_roots shrincs_fxmss_sha256
      sp pp kt) cache h1).
Proof.
move=> hsp [hi [hp0 [hp1 hlog]]].
apply: known_message_coupling_invI.
- (* Initialization writes only private locations. *)
  rewrite /known_message_coupling_store_left /known_message_coupling_store_right.
  do 4 (apply: heap_ignore_set_l; first by
    apply: fhas_in; rewrite /known_message_coupling_private /known_message_locs;
      fmap_solve).
  do 4 (apply: heap_ignore_set_r; first by
    apply: fhas_in; rewrite /known_message_coupling_private /leaf_ctx_ud_locs;
      fmap_solve).
  exact: hi.
- (* Initialization establishes the state, digest, log and root relation. *)
  rewrite /known_message_coupling_reads /known_message_coupling_rel
  /known_message_coupling_store_left /known_message_coupling_store_right.
  repeat first [rewrite get_set_heap_eq |
    match goal with
    | |- context [get_heap (set_heap ?h ?l ?v) ?k] =>
      rewrite (get_set_heap_neq h l v k ltac:(reflexivity))
    end].
  rewrite hp0 hp1 hlog.
  by repeat split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling finish *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition known_message_coupling_left_store sp sd pp kt : raw_code leaf_opening_public
  :=
  #put leaf_opening_st_loc := Some (pp, sp) ;;
  #put leaf_opening_keys_loc := kt ;;
  #put known_message_sd_loc := sd ;;
  #put known_message_cache_loc := known_message_cache shrincs_fxmss_sha256 sp pp sd kt
    ;;
  ret (pp, leaf_opening_roots shrincs_fxmss_sha256 sp pp kt).

Definition known_message_coupling_right_store sp sd pp roots cache : raw_code
  leaf_opening_public :=
  #put leaf_ctx_ud_st := Some (pp, sp) ;;
  #put leaf_ctx_ud_roots := roots ;;
  #put leaf_ctx_ud_sd := sd ;;
  #put leaf_ctx_ud_cache := cache ;;
  ret (pp, roots).

Local Opaque Th dBytes known_message_find wots_c_counter_max leaf_opening_roots
  known_message_cache get_heap
  set_heap known_message_coupling_inv known_message_coupling_frame.

Lemma known_message_coupling_stores_sim sp sd pp kt :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_frame pp (h0, h1) ⦄
    known_message_coupling_left_store sp sd pp kt ≈
    known_message_coupling_right_store sp sd pp (leaf_opening_roots shrincs_fxmss_sha256
      sp pp kt)
      (known_message_cache shrincs_fxmss_sha256 sp pp sd kt)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
move=> hsp.
rewrite /known_message_coupling_left_store /known_message_coupling_right_store.
do 4 apply r_put_lhs.
do 4 apply r_put_rhs.
apply r_ret.
move=> h0 h1.
rewrite /set_rhs /set_lhs /=.
move=> [hr3 [[hr2 [[hr1 [[hr0 [[hl3 [[hl2 [[hl1 [[hl0 [hp ->]] ->]] ->]] ->]] ->]] ->]] ->]] ->]].
split; first by [].
exact: known_message_coupling_inv_finish hsp hp.
Qed.

Definition known_message_coupling_ready pp cache j : precond := fun '(h0, h1) =>
  known_message_coupling_frame pp (h0, h1) /\
  get_heap h1 leaf_batch_cache_loc = Some cache /\
  get_heap h1 leaf_batch_slot_loc = j.

Lemma known_message_coupling_ready_step pp cache j h0 h1 :
  known_message_coupling_ready pp cache j (h0, h1) ->
  known_message_coupling_ready pp cache j.+1 (h0, set_heap h1 leaf_batch_slot_loc j.+1).
Proof.
move=> [hf [hc hs]].
split.
- apply: known_message_coupling_frame_rhs hf => //.
- split; last exact: get_set_heap_eq.
  by rewrite get_set_heap_neq.
Qed.

Lemma known_message_coupling_ready_init pp cache h0 h1 :
  known_message_coupling_frame pp (h0, h1) -> get_heap h1 leaf_batch_slot_loc = 0 ->
  known_message_coupling_ready pp cache 0
    (h0, set_heap (set_heap h1 leaf_batch_cache_loc (Some cache))
      leaf_prepared_done_loc true).
Proof.
move=> hf hs.
split.
- apply: known_message_coupling_frame_rhs => //.
  apply: known_message_coupling_frame_rhs hf => //.
- split.
  + rewrite (get_set_heap_neq _ leaf_prepared_done_loc _
      leaf_batch_cache_loc ltac:(reflexivity)).
    exact: get_set_heap_eq.
  + by rewrite !get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling drain *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max leaf_opening_roots
  known_message_cache get_heap
  set_heap known_message_coupling_inv known_message_coupling_frame.

Lemma known_message_coupling_drain_sim sp sd pp blocks :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  leaf_blocks_wf (shrincs_fxmss_schedule sp) blocks ->
  let kt := leaf_blocks_keys (shrincs_fxmss_schedule sp) blocks in
  let cache := leaf_blocks_cache 0 sp pp sd (shrincs_fxmss_schedule sp) blocks in
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_frame pp (h0, h1) /\
      get_heap h1 leaf_batch_slot_loc = 0 ⦄
    known_message_coupling_left_store sp sd pp kt ≈
    (#put leaf_batch_cache_loc := Some [seq e.2 | e <- cache] ;;
     #put leaf_prepared_done_loc := true ;;
     ys ← code_link (query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp))
       (G_leaf_roots 0) ;;
     known_message_coupling_right_store sp sd pp [seq e.1 | e <- cache] ys)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
move=> hsp [hb hwf].
cbv zeta.
cbn [bind].
eapply (r_put_rhs _ _ _ _ (fun '(h0,h1) => known_message_coupling_frame pp (h0,h1) /\
  get_heap h1 leaf_batch_slot_loc = 0) _).
apply r_put_rhs.
eapply (rpre_weaken_rule (known_message_coupling_ready pp
  [seq e.2 | e <- leaf_blocks_cache 0 sp pp sd (shrincs_fxmss_schedule sp) blocks]
    0)).
2: { move=> h0 h1 [h1b [[h1a [[hf hs] ->]] ->]].
     exact: known_message_coupling_ready_init hf hs. }
apply: (@leaf_context_sampling_drain 0 sp (shrincs_fxmss_schedule sp)
  [seq e.2 | e <- leaf_blocks_cache 0 sp pp sd (shrincs_fxmss_schedule sp) blocks] 0
  leaf_opening_public (known_message_coupling_ready pp
    [seq e.2 | e <- leaf_blocks_cache 0 sp pp sd (shrincs_fxmss_schedule sp) blocks])
  _ (fun _ => known_message_coupling_left_store sp sd pp
    (leaf_blocks_keys (shrincs_fxmss_schedule sp) blocks)) _).
- by move=> j h0 h1 [_ hh].
- exact: known_message_coupling_ready_step.
- (* Draining the initial cache returns the sampled keys' roots and signatures. *)
  move=> ys ->.
  rewrite leaf_values_drain_full; first exact: leaf_values_cache_size hb.
  have hu := leaf_schedule_uniq sp hsp.
  rewrite (leaf_values_zero_signatures _ _ _ _ _ hu hb)
    (leaf_values_zero_roots _ _ _ _ _ hu hb).
  change [seq leaf_pk shrincs_fxmss_sha256 sp pp a
    (odflt [::] (getm (leaf_blocks_keys (shrincs_fxmss_schedule sp) blocks) a))
    | a <- shrincs_fxmss_schedule sp] with
    (leaf_opening_roots shrincs_fxmss_sha256 sp pp (leaf_blocks_keys
      (shrincs_fxmss_schedule sp)
      blocks)).
  change [seq leaf_sign_at shrincs_fxmss_sha256 sp pp a
    (odflt [::] (getm (leaf_blocks_keys (shrincs_fxmss_schedule sp) blocks) a))
    (leaf_committed_digest sd a) | a <- shrincs_fxmss_schedule sp] with
    (known_message_cache shrincs_fxmss_sha256 sp pp sd (leaf_blocks_keys
      (shrincs_fxmss_schedule sp)
      blocks)).
  eapply rpre_weaken_rule; first exact: known_message_coupling_stores_sim hsp.
  by move=> h0 h1 [hf _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max leaf_opening_roots
  known_message_cache get_heap
  set_heap known_message_coupling_inv known_message_coupling_frame.

Definition known_message_coupling_prepared_tail sp sd pp cache : raw_code
  leaf_opening_public :=
  #put leaf_batch_cache_loc := Some [seq e.2 | e <- cache] ;;
  #put leaf_prepared_done_loc := true ;;
  ys ← code_link (query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp))
    (G_leaf_roots 0) ;;
  known_message_coupling_right_store sp sd pp [seq e.1 | e <- cache] ys.

Lemma known_message_coupling_sampling_sim sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_frame pp (h0, h1) /\
      get_heap h1 leaf_batch_slot_loc = 0 ⦄
    (kt ← shrincs_fxmss_sample_keys shrincs_fxmss_sha256 (shrincs_fxmss_schedule sp) ;;
      known_message_coupling_left_store sp sd pp kt) ≈
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     known_message_coupling_prepared_tail sp sd pp
       (Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete 0
         (known_message_prepared shrincs_fxmss_sha256 sp pp sd) pp xs))
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
move=> hsp.
rewrite leaf_blocks_keys_congr /known_message_prepared leaf_blocks_flat_congr.
apply: leaf_blocks_blocks_spec => blocks hwf.
exact: known_message_coupling_drain_sim hsp hwf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling link *)

(* Keep opacity settings local to the linking lemmas. *)
Section InitialCouplingLink.

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max prepared_leaf_roots
  leaf_values_last_signatures leaf_roots_seed sample_seq
  Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete.

Lemma known_message_coupling_context_gen_link sp sd :
  code_link (leaf_ctx_ud_gen sp sd) (G_leaf_roots 0) =
  (sto ← get leaf_ctx_ud_st ;;
   #assert ~~ isSome sto ;;
   #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
   #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
   pub ← resolve (G_leaf_roots 0)
     (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
       fixed_public)) (sp, sd) ;;
   ys ← code_link (query_list (leaf_ctx_ud_one sp) (shrincs_fxmss_schedule sp))
     (G_leaf_roots 0) ;;
   known_message_coupling_right_store sp sd pub.1 pub.2 ys).
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
by case: pub => pp roots; rewrite /known_message_coupling_right_store.
Qed.

End InitialCouplingLink.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling check *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_coupling_inv leaf_win known_message_find get_heap
  set_heap
  wots_c_counter_max leaf_recover known_message_gate leaf_opening_roots leaf_pk.

Lemma known_message_coupling_check_sim q :
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_inv (h0, h1) ⦄
    known_message_check_body shrincs_fxmss_sha256 q ≈ leaf_ctx_ud_check q
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
rewrite /known_message_check_body /leaf_ctx_ud_check.
sync_eq st0 st1.
{ move=> h0 h1 [[/known_message_coupling_invE [_ [_ [he _]]] hs0] hs1].
  by rewrite /rem_inv /= in hs0 hs1; rewrite hs0 hs1 in he.
}
move=> he; subst st1.
ssprove_sync=> hs.
case: st0 hs => [[pp sp]|] //= hs.
ssprove_sync=> hj.
eapply r_get_remember_lhs => entries.
eapply r_get_remember_rhs => roots.
sync_eq sd0 sd1.
{ move=> h0 h1 [[[[[[/known_message_coupling_invE [_ [_ [_ [he _]]]] _] _] _] _] hd0]
  hd1].
  by rewrite /rem_inv /= in hd0 hd1; rewrite hd0 hd1 in he.
}
move=> he; subst sd1.
apply r_ret.
move=> h0 h1 [[[[[[hi hs0] hs1] he] hr] hd0] hd1].
split; last exact: hi.
move: hi => /known_message_coupling_invE [_ [_ [_ [_ [_ hrel]]]]].
change (get_heap h0 leaf_opening_st_loc = Some (pp, sp)) in hs0.
rewrite hs0 in hrel.
move: hrel => [hp [hsp [hroots hcache]]].
change (get_heap h0 leaf_opening_keys_loc = entries) in he.
change (get_heap h1 leaf_ctx_ud_roots = roots) in hr.
change (get_heap h0 known_message_sd_loc = sd0) in hd0.
rewrite he in hroots.
rewrite hr in hroots.
rewrite hroots leaf_opening_rootsE.
rewrite (nth_map (uint U8 0, uint U64 0)); first exact: hj.
rewrite (leaf_schedule_nth sp q.1 hsp); first by
  rewrite -(leaf_schedule_length sp hsp).
by rewrite leaf_winE.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling eval *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_coupling_inv prepared_leaf_verdict
  known_message_find get_heap set_heap
  wots_c_counter_max leaf_recover known_message_gate.

Lemma known_message_coupling_eval_sim (q : leaf_opening_eval_input) :
  ~~ wots_c_hash_class q.1 ->
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_inv (h0, h1) ⦄
    (pp ← leaf_opening_seed shrincs_fxmss_sha256 ;; ret (Th pp q.1 q.2)) ≈
    resolve (G_leaf_roots 0) (EVAL, (leaf_opening_eval_input, bytes 16)) q
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
move=> hq.
rewrite /G_leaf_roots /resolve /= coerce_kleisliE hq.
cbn [assertD].
rewrite /leaf_opening_seed /leaf_roots_seed.
sync_eq po0 po1.
{ move=> h0 h1 [[/known_message_coupling_invE [_ [he _]] hp0] hp1].
  by rewrite /rem_inv /= in hp0 hp1; rewrite hp0 hp1 in he.
}
move=> he; subst po1.
case: po0 => [pp|].
- cbn [bind].
  apply r_ret => h0 h1 [[hi _] _].
  by split.
- (* An absent public seed is sampled and stored on both sides. *)
  change (shrincs_fxmss_public_seed_dist shrincs_fxmss_sha256) with (dBytes 16).
  remember (dBytes 16) as dn eqn:hdn.
  fold @bind.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
  move=> pp.
  apply r_put_vs_put.
  apply r_ret => h0 h1 [h1' [[h0' [[[hi hp0] hp1] ->]] ->]].
  split; first by [].
  have hs := known_message_coupling_inv_no_seed h0' h1' hi hp0.
  exact: known_message_coupling_inv_pin hi hs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling gen *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_find wots_c_counter_max leaf_opening_roots
  known_message_cache
  shrincs_fxmss_sample_keys
  sample_seq known_message_coupling_inv known_message_coupling_frame
  get_heap set_heap Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete.

Lemma known_message_coupling_gen_sim sp sd :
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_inv (h0, h1) ⦄
    known_message_gen_body shrincs_fxmss_sha256 sp sd ≈ code_link (leaf_ctx_ud_gen sp
      sd)
      (G_leaf_roots 0)
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
rewrite /known_message_gen_body known_message_coupling_context_gen_link.
sync_eq st0 st1.
{ move=> h0 h1 [[/known_message_coupling_invE [_ [_ [he _]]] hs0] hs1].
  by rewrite /rem_inv /= in hs0 hs1; rewrite hs0 hs1 in he.
}
move=> he; subst st1.
ssprove_sync=> hs.
case: st0 hs => [st|] //= hs.
ssprove_sync=> hsp.
ssprove_sync=> hsd.
have hresolve : resolve (G_leaf_roots 0)
  (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
    fixed_public)) (sp, sd) =
  (done ← get leaf_prepared_done_loc ;;
   #assert ~~ done ;;
   #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
   pp ← leaf_roots_seed ;;
   xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
   let cache := Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling.leaf_ud_complete 0
     (known_message_prepared shrincs_fxmss_sha256 sp pp sd) pp xs in
   #put leaf_batch_cache_loc := Some [seq e.2 | e <- cache] ;;
   #put leaf_prepared_done_loc := true ;;
   ret (pp, [seq e.1 | e <- cache])).
{ by rewrite /G_leaf_roots /resolve /= coerce_kleisliE. }
rewrite hresolve.
eapply (r_get_bind_rhs leaf_prepared_done_loc false).
{ move=> h0 h1 [[/known_message_coupling_invE [_ [_ [_ [_ [_ hr]]]]] hs0] hs1].
  change (get_heap h0 leaf_opening_st_loc = None) in hs0.
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
{ move=> h0 h1 [[[[/known_message_coupling_invE [_ [he _]] _] _] hp0] hp1].
  by rewrite /rem_inv /= in hp0 hp1; rewrite hp0 hp1 in he.
}
move=> he; subst po1.
case: po0 => [pp|].
- (* An existing public seed starts the sampling coupling. *)
  cbn [bind].
  rewrite bind_assoc.
  cbn [bind].
  eapply rpre_weaken_rule; first exact: (known_message_coupling_sampling_sim sp sd pp
    hsp).
  move=> h0 h1 [[[[hi hs0] hs1] hp0] hp1].
  have [hf [_ hslot]] := known_message_coupling_inv_start pp h0 h1 hi hs0 hp0.
  by split.
- (* An absent public seed is sampled before the sampling coupling. *)
  change (shrincs_fxmss_public_seed_dist shrincs_fxmss_sha256) with (dBytes 16).
  remember (dBytes 16) as dn eqn:hdn.
  rewrite !bind_assoc.
  cbn [bind].
  eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
  move=> pp.
  apply r_put_vs_put.
  rewrite hdn.
  rewrite bind_assoc.
  cbn [bind].
  eapply rpre_weaken_rule; first exact: (known_message_coupling_sampling_sim sp sd pp
    hsp).
  move=> h0 h1 [h1' [[h0' [[[[[hi hs0] hs1] hp0] hp1] ->]] ->]].
  have hi' := known_message_coupling_inv_pin pp h0' h1' hi hs0.
  have hs' : get_heap (set_heap h0' leaf_opening_pp_loc (Some pp))
    leaf_opening_st_loc = None.
  { by rewrite get_set_heap_neq. }
  have [hf [_ hslot]] := known_message_coupling_inv_start pp _ _ hi' hs'
    (get_set_heap_eq _ _ _).
  by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling sign *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque Th dBytes known_message_coupling_inv leaf_win known_message_find get_heap
  set_heap
  wots_c_counter_max leaf_pk leaf_recover known_message_gate known_message_cache
    leaf_opening_roots.

Lemma known_message_coupling_sign_sim j :
  ⊢ ⦃ fun '(h0, h1) => known_message_coupling_inv (h0, h1) ⦄
    known_message_sign_body j ≈ leaf_ctx_ud_sign j
  ⦃ fun '(x0, h0) '(x1, h1) => x0 = x1 /\ known_message_coupling_inv (h0, h1) ⦄.
Proof.
rewrite /known_message_sign_body /leaf_ctx_ud_sign.
sync_eq st0 st1.
{ move=> h0 h1 [[/known_message_coupling_invE [_ [_ [he _]]] hs0] hs1].
  by rewrite /rem_inv /= in hs0 hs1; rewrite hs0 hs1 in he.
}
move=> he; subst st1.
ssprove_sync=> hs.
case: st0 hs => [[pp sp]|] //= hs.
ssprove_sync=> hj.
sync_eq log0 log1.
{ move=> h0 h1 [[[[/known_message_coupling_invE [_ [_ [_ [_ [he _]]]]] _] _] hl0]
  hl1].
  by rewrite /rem_inv /= in hl0 hl1; rewrite hl0 hl1 in he.
}
move=> he; subst log1.
ssprove_sync=> hfresh.
apply r_put_vs_put.
eapply r_get_remember_lhs => cache0.
eapply r_get_remember_rhs => cache1.
apply r_ret.
move=> h0 h1 [[[h1' [[h0' [[[[[hi hs0] hs1] hl0] hl1] ->]] ->]] he] hc].
have hi' := known_message_coupling_inv_log (j :: log0) h0' h1' hi.
split; last exact: hi'.
move: hi => /known_message_coupling_invE [_ [_ [_ [_ [_ hr]]]]].
change (get_heap h0' leaf_opening_st_loc = Some (pp, sp)) in hs0.
rewrite hs0 in hr.
move: hr => [hp [hsp [hroots hcache]]].
change (get_heap (set_heap h0' leaf_opening_slog_loc (j :: log0))
  known_message_cache_loc = cache0) in he.
change (get_heap (set_heap h1' leaf_ctx_ud_log (j :: log0))
  leaf_ctx_ud_cache = cache1) in hc.
rewrite get_set_heap_neq // in he.
rewrite get_set_heap_neq // in hc.
by rewrite he hc in hcache; rewrite hcache.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial prepared-leaf coupling *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma resolve_known_message_gen P bit sp sd :
  resolve (G_known_message P bit)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      leaf_opening_public)) (sp, sd) =
    known_message_gen_body P sp sd.
Proof. by rewrite /G_known_message /resolve /= coerce_kleisliE. Qed.

Lemma resolve_known_message_sign P bit j :
  resolve (G_known_message P bit)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    known_message_sign_body j.
Proof. by rewrite /G_known_message /resolve /= coerce_kleisliE. Qed.

Lemma resolve_known_message_eval P bit q :
  resolve (G_known_message P bit)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (pp ← leaf_opening_seed P ;; ret (shrincs_fxmss_hash_eval P pp q.1 q.2)).
Proof. by rewrite /G_known_message /resolve /= coerce_kleisliE. Qed.

Local Opaque G_known_message C_leaf_roots G_leaf_roots known_message_coll_filter
  known_message_coupling_inv
  leaf_ctx_ud_gen leaf_ctx_ud_sign leaf_ctx_ud_check
  known_message_gen_body known_message_sign_body known_message_check_body.

Lemma known_message_coupling_perfect bit :
  perfect I_known_message (known_message_coll_filter ∘ G_known_message
    shrincs_fxmss_sha256 bit)
    (known_message_coll_filter ∘ C_leaf_roots bit ∘ G_leaf_roots 0).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ known_message_coupling_inv).
- exact: known_message_coupling_inv_invariant.
- intros id S T arg has; fmap_invert has.
  + (* GEN agrees with the initial leaf-root coupling. *)
    case: arg => sp sd.
    rewrite !resolve_link resolve_known_message_filter_gen.
    cbn [code_link].
    rewrite !bind_ret resolve_known_message_gen resolve_link resolve_leaf_ctx_ud_gen.
    exact: known_message_coupling_gen_sim.
  + (* SIGN returns the same cached signature. *)
    rewrite !resolve_link resolve_known_message_filter_sign.
    cbn [code_link].
    rewrite !bind_ret resolve_known_message_sign resolve_link resolve_leaf_ctx_ud_sign.
    have hv := leaf_ctx_ud_sign_valid emptym arg.
    rewrite (code_link_scheme _ _ _ _ hv).
    exact: known_message_coupling_sign_sim.
  + rewrite !resolve_link resolve_known_message_filter_check.
    cbn [code_link].
    rewrite !bind_ret resolve_known_message_check resolve_link resolve_leaf_ctx_ud_check code_link_bind.
    cbn [code_link].
    have hv := leaf_ctx_ud_check_valid emptym arg.
    rewrite (code_link_scheme _ _ _ _ hv).
    eapply r_bind with
      (mid := fun '(x0,h0) '(x1,h1) => x0 = x1 /\ known_message_coupling_inv (h0,h1)).
    * exact: known_message_coupling_check_sim.
    * move=> x0 x1.
      apply r_ret => h0 h1 [-> hi].
      by split.
  + have hg : resolve (G_known_message shrincs_fxmss_sha256 bit)
      (known_message_eval, (leaf_opening_eval_input, bytes 16))
        (known_message_filter_request arg) =
      (pp ← leaf_opening_seed shrincs_fxmss_sha256 ;;
       ret (Th pp (known_message_filter_request arg).1 (known_message_filter_request
         arg).2)).
    { by rewrite resolve_known_message_eval /shrincs_fxmss_hash_eval. }
    rewrite !resolve_link resolve_known_message_filter_eval /known_message_filter_eval !code_link_bind.
    cbn [code_link].
    rewrite hg resolve_link resolve_leaf_ctx_ud_eval !bind_ret.
    cbn [code_link].
    rewrite bind_ret.
    eapply r_bind with
      (mid := fun '(x0,h0) '(x1,h1) => x0 = x1 /\ known_message_coupling_inv (h0,h1)).
    * apply: known_message_coupling_eval_sim.
      by have /and3P[hout _] := known_message_filter_request_outside arg.
    * move=> x0 x1.
      apply r_ret => h0 h1 [-> hi].
      by split.
Qed.

Lemma leaf_inner_first_perfect Q bit :
  perfect I_forge (R_known_message Q ∘ known_message_coll_filter ∘ G_known_message
    shrincs_fxmss_sha256 bit)
    (R_leaf_roots Q bit ∘ G_leaf_roots 0).
Proof.
rewrite R_leaf_roots_nom -!sep_link_assoc.
apply static_batch.batch_context_perfect.
exact: known_message_coupling_perfect.
Qed.
