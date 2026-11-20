(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.grind.sampling

    Couple one option grinding query with re-rooted chain sampling and the
    outside-class compression evaluation. Package invariant for the grinding hop. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core chain.ud toolkit.relational_rules toolkit.batch_map.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.compress.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.known_message_game
    leaf.known_message leaf.prepared
  leaf.compress.pure leaf.compress.sampling leaf.grind.reduction leaf.grind.state
  leaf.commitments leaf.opening leaf.paths.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Grinding sampling *)

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes Th known_message_find known_message_digits complete_ends wsigs
  r_grind_block.

Lemma r_grind_one_spec p b {B : choiceType} sp pp a md tw tg
    (K0 : prepared_leaf_entry -> raw_code B) (K1 : r_grind_result -> raw_code B)
    (post : postcond B B) :
  size tw < p -> shrincs_fxmss_grind_tweak a \notin tw ->
  (forall us, size us = 32 ->
    let entry := r_compress_sample_entry sp pp a md us in
    ⊢ ⦃ fun '(h0, h1) => r_grind_block pp false (rcons tw (shrincs_fxmss_grind_tweak a))
      (r_grind_update tg (size tw) a md (r_grind_answer sp pp a md)) (h0, h1) ⦄
      K0 entry ≈ K1 (r_compress_result_of pp a entry) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp false tw tg (h0, h1) ⦄
    bind (prepared_leaf_sample sp pp a md) K0 ≈
    bind (code_link (r_grind_one sp a md) (fxmss_grind_game p b)) K1 ⦃ post ⦄.
Proof.
move=> hbudget hfresh hk.
rewrite /r_grind_one code_link_bind bind_assoc.
cbn [code_link].
rewrite bind_ret.
eapply (r_grind_query_spec p b sp); [exact: hbudget | exact: hfresh |].
rewrite r_grind_answer_digits.
rewrite /prepared_leaf_sample code_link_bind !bind_assoc.
eapply (r_grind_chains_spec (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1
  (uint
  U8 sp.2)) p b pp
  (r_grind_block pp false (rcons tw (shrincs_fxmss_grind_tweak a))
    (r_grind_update tg (size tw) a md (r_grind_answer sp pp a md))) post).
- by move=> i k.
- by move=> h0 h1 [_ [_ [hr _]]].
- exact: r_compress_digits_wf.
- move=> us hus.
  rewrite (wendsE (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
    sp.2)) _ _ _
    (known_message_digits_length shrincs_fxmss_sha256 sp pp a md)).
  cbn [code_link bind].
  rewrite bind_assoc.
  eapply (r_grind_eval_known (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1
    (uint
    U8 sp.2)) p b pp).
  + by move=> h0 h1 [_ [_ [hr _]]].
  + by [].
  + cbn [bind].
    rewrite r_grind_answer_counter.
    apply: hk.
    by rewrite known_message_digits_length in hus.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Grinding batch *)

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint r_grind_record (j : nat) (tg : chMap 'nat (tweak × (bytes 32 × 'nat)))
    sp pp sd (ats : seq shrincs_fxmss_coord) :=
  match ats with
  | a :: ats' =>
      let md := leaf_committed_digest sd a in
      r_grind_record j.+1 (r_grind_update tg j a md (r_grind_answer sp pp a md)) sp pp
        sd ats'
  | [::] => tg
  end.
Definition r_grind_counters sp pp sd (ats : seq shrincs_fxmss_coord) (entries : seq
  prepared_leaf_entry) :=
  [seq entry.2 | entry <- entries] =
    [seq known_message_find shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a) |
      a <- ats].

Local Opaque dBytes Th prepared_leaf_sample r_grind_one r_grind_block
  r_compress_result_of.
Local Opaque bind code_link known_message_find known_message_digits wots_c_counter_max.

Lemma r_grind_batch_spec p b {B : choiceType} sp pp sd ats tw tg
    (K0 : seq prepared_leaf_entry -> raw_code B) (K1 : seq r_grind_result -> raw_code B)
    (post : postcond B B) :
  uniq (tw ++ [seq shrincs_fxmss_grind_tweak a | a <- ats]) ->
  size tw + size ats <= p ->
  (forall entries, size entries = size ats ->
    r_grind_counters sp pp sd ats entries ->
    ⊢ ⦃ fun '(h0, h1) =>
      r_grind_block pp false (tw ++ [seq shrincs_fxmss_grind_tweak a | a <- ats])
        (r_grind_record (size tw) tg sp pp sd ats) (h0, h1) ⦄
      K0 entries ≈ K1 (r_compress_results pp ats entries) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp false tw tg (h0, h1) ⦄
    bind (query_list (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd
      a)) ats) K0 ≈
    bind (code_link (query_list (fun a => r_grind_one sp a (leaf_committed_digest sd a))
      ats)
      (fxmss_grind_game p b)) K1 ⦃ post ⦄.
Proof.
remember (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd a)) as qs
  eqn:hqs.
remember (fun a => r_grind_one sp a (leaf_committed_digest sd a)) as qr eqn:hqr.
elim: ats tw tg K0 K1 => [|a ats ih] tw tg K0 K1 hu hb hk.
- have := hk [::] erefl erefl.
  by rewrite cats0.
- have hfresh : shrincs_fxmss_grind_tweak a \notin tw.
  { move: hu; rewrite cat_uniq => /and3P[_ /hasPn hd _].
    exact: hd _ (mem_head _ _).
  }
  have hc : size tw < p.
  { apply: leq_trans hb.
    by rewrite /= addnS ltnS leq_addr.
  }
  cbn [query_list].
  rewrite code_link_bind !bind_assoc.
  rewrite (congr1 (fun f => f a) hqs) (congr1 (fun f => f a) hqr).
  eapply r_grind_one_spec; [exact: hc | exact: hfresh |].
  move=> us hus.
  cbv zeta.
  rewrite code_link_bind !bind_assoc.
  eapply ih.
  + by rewrite -cats1 -catA.
  + by move: hb; rewrite /= size_rcons addSn addnS.
  + (* The head entry extends the length and counter correspondence. *)
    move=> entries hentries hcounters.
    have he := hk (r_compress_sample_entry sp pp a (leaf_committed_digest sd a) us ::
      entries).
    rewrite /= hentries in he.
    specialize (he erefl).
    have hcs : r_grind_counters sp pp sd (a :: ats)
      (r_compress_sample_entry sp pp a (leaf_committed_digest sd a) us :: entries).
    { exact: (congr1 (cons (known_message_find shrincs_fxmss_sha256 sp pp a
        (leaf_committed_digest sd a))) hcounters).
    }
    specialize (he hcs).
    rewrite size_rcons -cats1 -catA.
    exact: he.
Qed.

Lemma r_grind_record_before sp pp sd ats start tg j :
  j < start -> getm (r_grind_record start tg sp pp sd ats) j = getm tg j.
Proof.
elim: ats start tg => [|a ats ih] start tg //= hj.
rewrite (ih _ _ (ltn_trans hj (ltnSn _))) /r_grind_update.
case: r_grind_answer => [[v c]|] //=.
by rewrite setmE (ltn_eqF hj).
Qed.

Lemma r_grind_record_lookup sp pp sd ats start tg i c :
  i < size ats ->
  known_message_find shrincs_fxmss_sha256 sp pp (nth (uint U8 0, uint U64 0) ats i)
    (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i)) = Some c ->
  getm (r_grind_record start tg sp pp sd ats) (start + i)%N =
    Some (shrincs_fxmss_grind_tweak (nth (uint U8 0, uint U64 0) ats i),
      (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i), c)).
Proof.
elim: ats start tg i => [|a ats ih] start tg i //=.
case: i => [|i] hi hfind.
- rewrite addn0 (r_grind_record_before _ _ _ _ _ _ _ (ltnSn _)).
  by rewrite /r_grind_update /r_grind_answer hfind /= setmE eqxx.
- rewrite addnS -addSn.
  exact: ih hi hfind.
Qed.

Lemma r_grind_counters_nth sp pp sd ats entries i :
  r_grind_counters sp pp sd ats entries -> i < size ats ->
  (nth prepared_leaf_default entries i).2 =
    known_message_find shrincs_fxmss_sha256 sp pp (nth (uint U8 0, uint U64 0) ats i)
      (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i)).
Proof.
rewrite /r_grind_counters.
elim: ats entries i => [|a ats ih] [|entry entries] i //=.
move=> [hhead htail] hi.
case: i hi => [|i] hi; first exact: hhead.
exact: ih htail hi.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Grinding invariant *)

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque wots_c_counter_max.

Definition r_grind_rel (po0 po1 : option (bytes 16)) (st : option leaf_opening_state)
  (sd :
  shrincs_fxmss_digest_table)
    (entries : seq prepared_leaf_entry) (rv : bool) (tw : seq tweak)
    (tg : chMap 'nat (tweak × (bytes 32 × 'nat))) : Prop :=
  po0 = po1 /\
  match st with
  | None => rv = false /\ tw = [::] /\ tg = emptym
  | Some (pp, sp) =>
      po0 = Some pp /\ rv = true /\
      tw = r_grind_targets sp /\ size entries = size (shrincs_fxmss_schedule sp) /\
      tg = r_grind_record 0 emptym sp pp sd (shrincs_fxmss_schedule sp) /\
      r_grind_counters sp pp sd (shrincs_fxmss_schedule sp) entries /\
      shrincs_fxmss_structure_legal sp.1 sp.2
  end.

Definition r_grind_inv : precond :=
  heap_ignore r_grind_private ⋊
  rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, stcr_option_pp_loc shrincs_thf);
    (lhs, prepared_leaf_st_loc); (lhs, prepared_leaf_sd_loc); (lhs,
      prepared_leaf_entries_loc); (rhs, stcr_option_rev_loc);
    (rhs, stcr_option_tws_loc shrincs_thf); (rhs, stcr_option_tgts_loc shrincs_thf
      (bytes 32))] r_grind_rel.

Lemma r_grind_inv_invariant r b :
  Invariant (loc (G_prepared_leaf r))
    (unionm (loc R_grind)
      (loc (fxmss_grind_game (2 ^ 64) b))) r_grind_inv.
Proof.
rewrite /r_grind_inv.
ssprove_invariant.
by rewrite /rel_empty /r_grind_rel /=.
Qed.

Lemma r_grind_invE h0 h1 :
  r_grind_inv (h0, h1) ->
  heap_ignore r_grind_private (h0, h1) /\
  r_grind_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (stcr_option_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_sd_loc)
    (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 stcr_option_rev_loc) (get_heap h1 (stcr_option_tws_loc shrincs_thf))
    (get_heap h1 (stcr_option_tgts_loc shrincs_thf (bytes 32))).
Proof.
by [].
Qed.

Lemma r_grind_invI h0 h1 :
  heap_ignore r_grind_private (h0, h1) ->
  r_grind_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (stcr_option_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_sd_loc)
    (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 stcr_option_rev_loc) (get_heap h1 (stcr_option_tws_loc shrincs_thf))
    (get_heap h1 (stcr_option_tgts_loc shrincs_thf (bytes 32))) ->
  r_grind_inv (h0, h1).
Proof.
by move=> hi hr; split.
Qed.

Lemma r_grind_inv_start pp h0 h1 :
  r_grind_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  get_heap h0 prepared_leaf_pp_loc = Some pp ->
  r_grind_block pp false [::] emptym (h0, h1).
Proof.
move=> /r_grind_invE [hi [he hr]] hs hp.
rewrite hs in hr.
move: hr => [hv [hw ht]].
by split; [exact: hi | split; [exact: hp | split; [rewrite -he | repeat split]]].
Qed.

Definition r_grind_stored pp sp sd entries h :=
  set_heap (set_heap (set_heap h prepared_leaf_st_loc (Some (pp, sp)))
    prepared_leaf_sd_loc sd) prepared_leaf_entries_loc entries.

Local Opaque get_heap set_heap known_message_find r_grind_record r_grind_counters
  shrincs_fxmss_schedule.

Lemma r_grind_inv_finish pp sp sd entries h0 h1 :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size entries = size (shrincs_fxmss_schedule sp) ->
  r_grind_counters sp pp sd (shrincs_fxmss_schedule sp) entries ->
  r_grind_block pp true (r_grind_targets sp)
    (r_grind_record 0 emptym sp pp sd (shrincs_fxmss_schedule sp)) (h0, h1) ->
  r_grind_inv (r_grind_stored pp sp sd entries h0, r_grind_stored pp sp sd entries h1).
Proof.
move=> hsp hlen hcounters [hi [hl [hr [hv [hw ht]]]]].
apply: r_grind_invI.
- rewrite /r_grind_stored.
  do 3 apply: put_pre_cond_heap_ignore.
  exact: hi.
- (* Stored entries, digests and targets satisfy the grinding relation. *)
  rewrite /r_grind_stored /r_grind_rel.
  rewrite !get_set_heap_eq.
  rewrite (get_set_heap_neq _ prepared_leaf_entries_loc _ prepared_leaf_st_loc) //
    (get_set_heap_neq _ prepared_leaf_sd_loc _ prepared_leaf_st_loc) //
      get_set_heap_eq.
  have hsd : get_heap (set_heap (set_heap
    (set_heap h0 prepared_leaf_st_loc (Some (pp, sp))) prepared_leaf_sd_loc sd)
    prepared_leaf_entries_loc entries) prepared_leaf_sd_loc = sd.
  { rewrite (get_set_heap_neq _ prepared_leaf_entries_loc _ prepared_leaf_sd_loc
      ltac:(reflexivity)).
    exact: get_set_heap_eq.
  }
  rewrite hsd.
  rewrite !get_set_heap_neq // hl hr hv hw ht.
  by repeat split.
Qed.

Lemma r_grind_inv_seed_eq h0 h1 :
  r_grind_inv (h0, h1) ->
  get_heap h0 prepared_leaf_pp_loc = get_heap h1 (stcr_option_pp_loc shrincs_thf).
Proof.
by move=> /r_grind_invE [_ [he _]].
Qed.

Lemma r_grind_inv_no_seed h0 h1 :
  r_grind_inv (h0, h1) -> get_heap h0 prepared_leaf_pp_loc = None ->
  get_heap h0 prepared_leaf_st_loc = None.
Proof.
move=> /r_grind_invE [hi [he hr]] hp.
case hs: (get_heap h0 prepared_leaf_st_loc) hr => [[pp sp]|] //.
by rewrite /r_grind_rel hp => -[].
Qed.

Lemma r_grind_inv_pin pp h0 h1 :
  r_grind_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  r_grind_block pp false [::] emptym
    (set_heap h0 prepared_leaf_pp_loc (Some pp),
     set_heap h1 (stcr_option_pp_loc shrincs_thf) (Some pp)).
Proof.
move=> /r_grind_invE [hi [he hr]] hs.
rewrite hs in hr.
move: hr => [hv [hw ht]].
split.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /r_grind_private; fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /r_grind_private; fmap_solve.
- split; first exact: get_set_heap_eq.
  split; first exact: get_set_heap_eq.
  by rewrite !get_set_heap_neq //; repeat split.
Qed.

Lemma r_grind_block_initial_inv pp h0 h1 :
  r_grind_block pp false [::] emptym (h0, h1) ->
  get_heap h0 prepared_leaf_st_loc = None -> r_grind_inv (h0, h1).
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]] hs.
apply: r_grind_invI hi _.
by rewrite /r_grind_rel hl hr hs hv hw ht.
Qed.
