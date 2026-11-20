(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.compress.sampling

    One leaf commitment couples grinding, pointwise re-rooted chain sampling and
    the type-17 challenge. Package invariant for the compression hop. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core chain.ud toolkit.relational_rules toolkit.batch_map.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.compress.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.known_message_game
    leaf.known_message leaf.prepare
  leaf.prepared leaf.compress.reduction leaf.compress.pure leaf.commitments
  leaf.opening leaf.paths.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Compression sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma r_compress_digits_wf sp pp a md :
  all (fun d => d < 16) (known_message_digits shrincs_fxmss_sha256 sp pp a md).
Proof.
rewrite /known_message_digits.
case: known_message_find => [c|]; last by [].
exact: (wcp_digits_wf (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
  sp.2)) _).
Qed.

Definition r_compress_sample_entry sp pp a md us : prepared_leaf_entry :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let ds := known_message_digits shrincs_fxmss_sha256 sp pp a md in
  let sg := wsigs W pp 0 ds us in
  ((sg, complete_ends W pp ds sg), known_message_find shrincs_fxmss_sha256 sp pp a md).
Definition r_compress_target_of a (entry : prepared_leaf_entry) :=
  (shrincs_fxmss_pk_tweak a, r_compress_encode entry.1.2).
Definition r_compress_result_of pp a (entry : prepared_leaf_entry) : r_compress_result
  :=
  (Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode entry.1.2), entry).

Local Opaque dBytes Th known_message_find known_message_digits complete_ends wsigs
  r_compress_block.

Lemma r_compress_one_spec p b {B : choiceType} sp pp a md tw tg
    (K0 : prepared_leaf_entry -> raw_code B) (K1 : r_compress_result -> raw_code B)
    (post : postcond B B) :
  size tw < p -> shrincs_fxmss_pk_tweak a \notin tw ->
  (forall us, size us = 32 ->
    let entry := r_compress_sample_entry sp pp a md us in
    ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false (rcons tw (shrincs_fxmss_pk_tweak a))
      (setm tg (size tw) (r_compress_target_of a entry)) (h0, h1) ⦄
      K0 entry ≈ K1 (r_compress_result_of pp a entry) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false tw tg (h0, h1) ⦄
    bind (prepared_leaf_sample sp pp a md) K0 ≈
    bind (code_link (r_compress_one sp a md)
      (SMTCR_game shrincs_thf wots_c_pk_class p b)) K1 ⦃ post ⦄.
Proof.
move=> hbudget hfresh hk.
rewrite /r_compress_one /leaf_grind_one code_link_bind bind_assoc.
rewrite code_link_bind bind_assoc.
eapply (r_compress_grind_spec (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1
  (uint U8
  sp.2)) p b pp (r_compress_block pp false tw tg)).
- by move=> h0 h1 [_ [_ [hr _]]].
- cbn [code_link bind].
rewrite leaf_grind_pick_map known_message_prepared_digits.
rewrite /prepared_leaf_sample code_link_bind !bind_assoc.
eapply (r_compress_chains_spec (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1
  (uint U8
  sp.2)) p b pp (r_compress_block pp false tw tg) post).
+ by move=> h0 h1 [_ [_ [hr _]]].
+ exact: r_compress_digits_wf.
+ move=> us hus.
rewrite (wendsE (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) _
  _ _ (known_message_digits_length shrincs_fxmss_sha256 sp pp a md)).
cbn [code_link bind].
rewrite /known_message_prepared_leaf.
have hc : omap fst (omap (fun c => (c, digest_of (shrincs_fxmss_leaf_params
  shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) pp md c)) (known_message_find
    shrincs_fxmss_sha256 sp
  pp a md)) = known_message_find shrincs_fxmss_sha256 sp pp a md by case:
    known_message_find.
rewrite hc.
rewrite bind_assoc.
eapply r_compress_target_spec.
- exact: shrincs_fxmss_pk_tweak_class.
- exact: hbudget.
- exact: hfresh.
- apply: hk.
by rewrite known_message_digits_length in hus.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Compression batch *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint r_compress_record (j : nat) (tg : chMap 'nat (tweak × 'list ('word U8)))
    (ats : seq shrincs_fxmss_coord) (entries : seq prepared_leaf_entry) :=
  match ats, entries with
  | a :: ats', entry :: entries' =>
      r_compress_record j.+1 (setm tg j (r_compress_target_of a entry)) ats' entries'
  | _, _ => tg
  end.
Definition r_compress_results pp ats entries :=
  [seq r_compress_result_of pp ae.1 ae.2 | ae <- zip ats entries].

Local Opaque dBytes Th prepared_leaf_sample r_compress_one r_compress_block
  r_compress_target_of r_compress_result_of.
Local Opaque bind code_link.

Lemma r_compress_batch_spec p b {B : choiceType} sp pp sd ats tw tg
    (K0 : seq prepared_leaf_entry -> raw_code B) (K1 : seq r_compress_result -> raw_code
      B)
    (post : postcond B B) :
  uniq (tw ++ [seq shrincs_fxmss_pk_tweak a | a <- ats]) ->
  size tw + size ats <= p ->
  (forall entries, size entries = size ats ->
    ⊢ ⦃ fun '(h0, h1) =>
      r_compress_block pp false (tw ++ [seq shrincs_fxmss_pk_tweak a | a <- ats])
        (r_compress_record (size tw) tg ats entries) (h0, h1) ⦄
      K0 entries ≈ K1 (r_compress_results pp ats entries) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false tw tg (h0, h1) ⦄
    bind (query_list (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd
      a)) ats) K0 ≈
    bind (code_link (query_list (fun a => r_compress_one sp a (leaf_committed_digest sd
      a)) ats)
      (SMTCR_game shrincs_thf wots_c_pk_class p b)) K1 ⦃ post ⦄.
Proof.
remember (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd a)) as qs
  eqn:hqs.
remember (fun a => r_compress_one sp a (leaf_committed_digest sd a)) as qr eqn:hqr.
elim: ats tw tg K0 K1 => [|a ats ih] tw tg K0 K1 hu hb hk.
- have := hk [::] erefl.
by rewrite cats0.
- have hfresh : shrincs_fxmss_pk_tweak a \notin tw.
{ move: hu; rewrite cat_uniq => /and3P[_ /hasPn hd _].
exact: hd _ (mem_head _ _).
} have hc : size tw < p.
{ apply: leq_trans hb.
by rewrite /= addnS ltnS leq_addr.
} cbn [query_list].
rewrite code_link_bind !bind_assoc.
rewrite (congr1 (fun f => f a) hqs) (congr1 (fun f => f a) hqr).
eapply r_compress_one_spec; [exact: hc | exact: hfresh |].
move=> us hus.
cbv zeta.
rewrite code_link_bind !bind_assoc.
eapply ih.
+ by rewrite -cats1 -catA.
+ by move: hb; rewrite /= size_rcons addSn addnS.
+ move=> entries hentries.
have he := hk (r_compress_sample_entry sp pp a (leaf_committed_digest sd a) us ::
  entries).
rewrite /= hentries in he.
specialize (he erefl).
rewrite size_rcons -cats1 -catA.
exact: he.
Qed.

Lemma r_compress_record_before start tg ats entries j :
  j < start -> getm (r_compress_record start tg ats entries) j = getm tg j.
Proof.
elim: ats entries start tg => [|a ats ih] [|entry entries] start tg //= hj.
by rewrite (ih _ _ _ (ltn_trans hj (ltnSn _))) setmE (ltn_eqF hj).
Qed.

Lemma r_compress_record_lookup start tg ats entries i :
  size entries = size ats -> i < size ats ->
  getm (r_compress_record start tg ats entries) (start + i)%N =
    Some (r_compress_target_of (nth (uint U8 0, uint U64 0) ats i)
      (nth prepared_leaf_default entries i)).
Proof.
elim: ats entries start tg i => [|a ats ih] [|entry entries] start tg i //=.
move=> [hlen].
case: i => [|i] hi.
- rewrite addn0 (r_compress_record_before _ _ _ _ _ (ltnSn _)).
  by rewrite setmE eqxx.
- rewrite addnS -addSn.
  exact: ih hlen hi.
Qed.

(* Expose result projections after the sampling proofs kept them folded. *)
Local Transparent r_compress_result_of.
Lemma r_compress_results_entries pp ats entries :
  size entries = size ats ->
  [seq result.2 | result <- r_compress_results pp ats entries] = entries.
Proof.
rewrite /r_compress_results /r_compress_result_of.
elim: ats entries => [|a ats ih] [|entry entries] //= [hlen].
by rewrite ih.
Qed.

Lemma r_compress_results_roots pp sp entries :
  [seq result.1 | result <- r_compress_results pp (shrincs_fxmss_schedule sp) entries] =
    prepared_leaf_roots sp pp entries.
Proof.
by rewrite /r_compress_results /r_compress_result_of /prepared_leaf_roots -map_comp.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Compression invariant *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition r_compress_rel (po0 po1 : option (bytes 16)) (st : option leaf_opening_state)
    (entries : seq prepared_leaf_entry) (rv : bool) (tw : seq tweak)
    (tg : chMap 'nat (tweak × 'list ('word U8))) : Prop :=
  po0 = po1 /\
  match st with
  | None => rv = false /\ tw = [::] /\ tg = emptym
  | Some (pp, sp) =>
      po0 = Some pp /\ rv = true /\
      tw = r_compress_targets sp /\ size entries = size (shrincs_fxmss_schedule sp) /\
      tg = r_compress_record 0 emptym (shrincs_fxmss_schedule sp) entries /\
      shrincs_fxmss_structure_legal sp.1 sp.2
  end.

Definition r_compress_inv : precond :=
  heap_ignore r_compress_private ⋊
  rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, tcr_pp_loc shrincs_thf);
    (lhs, prepared_leaf_st_loc); (lhs, prepared_leaf_entries_loc); (rhs, tcr_rev_loc);
    (rhs, tcr_tws_loc shrincs_thf); (rhs, tcr_tgts_loc shrincs_thf)] r_compress_rel.

Lemma r_compress_inv_invariant r b :
  Invariant (loc (G_prepared_leaf r))
    (unionm (loc R_compress)
      (loc (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64) b))) r_compress_inv.
Proof.
rewrite /r_compress_inv.
ssprove_invariant.
by rewrite /rel_empty /r_compress_rel /=.
Qed.

Lemma r_compress_invE h0 h1 :
  r_compress_inv (h0, h1) ->
  heap_ignore r_compress_private (h0, h1) /\
  r_compress_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (tcr_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 tcr_rev_loc) (get_heap h1 (tcr_tws_loc shrincs_thf))
    (get_heap h1 (tcr_tgts_loc shrincs_thf)).
Proof.
by [].
Qed.

Lemma r_compress_invI h0 h1 :
  heap_ignore r_compress_private (h0, h1) ->
  r_compress_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (tcr_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 tcr_rev_loc) (get_heap h1 (tcr_tws_loc shrincs_thf))
    (get_heap h1 (tcr_tgts_loc shrincs_thf)) ->
  r_compress_inv (h0, h1).
Proof.
by move=> hi hr; split.
Qed.

Lemma r_compress_inv_start pp h0 h1 :
  r_compress_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  get_heap h0 prepared_leaf_pp_loc = Some pp ->
  r_compress_block pp false [::] emptym (h0, h1).
Proof.
move=> /r_compress_invE [hi [he hr]] hs hp.
rewrite hs in hr.
move: hr => [hv [hw ht]].
by split; [exact: hi | split; [exact: hp | split; [rewrite -he | repeat split]]].
Qed.

Definition r_compress_stored pp sp sd entries h :=
  set_heap (set_heap (set_heap h prepared_leaf_st_loc (Some (pp, sp)))
    prepared_leaf_sd_loc sd) prepared_leaf_entries_loc entries.

Lemma r_compress_inv_finish pp sp sd entries h0 h1 :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size entries = size (shrincs_fxmss_schedule sp) ->
  r_compress_block pp true (r_compress_targets sp)
    (r_compress_record 0 emptym (shrincs_fxmss_schedule sp) entries) (h0, h1) ->
  r_compress_inv (r_compress_stored pp sp sd entries h0, r_compress_stored pp sp sd
    entries h1).
Proof.
move=> hsp hlen [hi [hl [hr [hv [hw ht]]]]].
apply: r_compress_invI.
- rewrite /r_compress_stored.
  do 3 apply: put_pre_cond_heap_ignore.
  exact: hi.
- (* Stored entries and target records satisfy the compression relation. *)
  rewrite /r_compress_stored /r_compress_rel.
  rewrite !get_set_heap_eq.
  rewrite (get_set_heap_neq _ prepared_leaf_entries_loc _ prepared_leaf_st_loc) //
    (get_set_heap_neq _ prepared_leaf_sd_loc _ prepared_leaf_st_loc) // get_set_heap_eq.
  rewrite !get_set_heap_neq // hl hr hv hw ht.
  by repeat split.
Qed.

Lemma r_compress_inv_seed_eq h0 h1 :
  r_compress_inv (h0, h1) ->
  get_heap h0 prepared_leaf_pp_loc = get_heap h1 (tcr_pp_loc shrincs_thf).
Proof.
by move=> /r_compress_invE [_ [he _]].
Qed.

Lemma r_compress_inv_no_seed h0 h1 :
  r_compress_inv (h0, h1) -> get_heap h0 prepared_leaf_pp_loc = None ->
  get_heap h0 prepared_leaf_st_loc = None.
Proof.
move=> /r_compress_invE [hi [he hr]] hp.
case hs: (get_heap h0 prepared_leaf_st_loc) hr => [[pp sp]|] //.
by rewrite /r_compress_rel hp => -[].
Qed.

Lemma r_compress_inv_pin pp h0 h1 :
  r_compress_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  r_compress_block pp false [::] emptym
    (set_heap h0 prepared_leaf_pp_loc (Some pp),
     set_heap h1 (tcr_pp_loc shrincs_thf) (Some pp)).
Proof.
move=> /r_compress_invE [hi [he hr]] hs.
rewrite hs in hr.
move: hr => [hv [hw ht]].
split.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /r_compress_private; fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /r_compress_private; fmap_solve.
- split; first exact: get_set_heap_eq.
  split; first exact: get_set_heap_eq.
  by rewrite !get_set_heap_neq //; repeat split.
Qed.

Lemma r_compress_block_initial_inv pp h0 h1 :
  r_compress_block pp false [::] emptym (h0, h1) ->
  get_heap h0 prepared_leaf_st_loc = None -> r_compress_inv (h0, h1).
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]] hs.
apply: r_compress_invI hi _.
by rewrite /r_compress_rel hl hr hs hv hw ht.
Qed.
