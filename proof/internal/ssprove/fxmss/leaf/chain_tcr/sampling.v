(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.chain_tcr.sampling

    Instantiate generic target loops with a committed target prefix. Package
    invariant for the batch chain hop. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core chain.target_loops chain.tcr_extra toolkit.relational_rules
  toolkit.batch_map.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.chain_common.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.known_message_game leaf.known_message leaf.prepare
    leaf.prepared
  leaf.compress.reduction leaf.chain_tcr.reduction leaf.fixed_batch
    leaf.compress.sampling
  leaf.commitments leaf.opening leaf.paths leaf.compress.pure.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions loops *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque Th.

Lemma r_chain_tcr_resolve_eval p b q :
  resolve (SMTCR_game shrincs_thf wots_c_hash_class p b)
    (EVAL, (tweak × 'list ('word U8), bytes 16)) q =
  (#assert ~~ wots_c_hash_class q.1 ;;
   ppo ← get (tcr_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← th_dPP shrincs_thf ;;
                  #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp q.1 q.2)).
Proof. by case: q => t m; rewrite /SMTCR_game /resolve /= coerce_kleisliE. Qed.

Lemma r_chain_tcr_grind_spec p b sp a pp md cs
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : chList (bytes 16) -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (tcr_pp_loc shrincs_thf) = Some pp) ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k [seq wcp_H_grind W pp (grind_adrs W) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (grind_loop W md cs)
      (SMTCR_game shrincs_thf wots_c_hash_class p b)) k ⦃ post ⦄.
Proof.
move=> hpin /=.
elim: cs k => [|c cs ih] k hk.
- exact: hk.
- cbn [grind_loop code_link].
  rewrite bind_assoc r_chain_tcr_resolve_eval.
  eapply r_bind_assertD_rhs.
  + by move=> h0 h1 _.
  + (* An allowed evaluation uses the pinned seed before the remaining search. *)
    move=> _.
    eapply (r_get_rhs_pin (tcr_pp_loc shrincs_thf) (Some pp));
      first exact: hpin.
    cbn [bind].
    rewrite code_link_bind bind_assoc.
    apply: ih.
    exact: hk.
Qed.

Definition r_chain_tcr_prefix sp pp a (pre : seq (tweak * seq UInt8))
    (Q : seq ((nat * nat) * bytes 16)) : precond :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let targets := pre ++ [seq wq W q | q <- Q] in
  r_compress_block pp false (unzip1 targets) (qmap_from 0 targets).

Lemma r_chain_tcr_query_prefix_spec p b {B : choiceType} sp pp a pre
    (post : postcond B B) :
  (forall i k, i < 32 -> k < 15 ->
    chain_tweak (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) i
      k
      \notin unzip1 pre) ->
  size pre + (32 * 16) <= p ->
  target_query_spec (bytes 16) (bytes 16) 32 16 (32 * 16)
    (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
    (fun i k x => code_link (r_chain_tcr_query sp a i k x)
      (SMTCR_game shrincs_thf wots_c_hash_class p b))
    pp (r_chain_tcr_prefix sp pp a pre) post.
Proof.
move=> hpre hbudget i k x Q c0 k1 hi hk hQr hQbudget hfresh hcont.
set W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2).
have hclass : wots_c_hash_class (chain_tweak W i k).
{ exact: (wcp_tw_chain_class W i k). }
have hbudget' : size (unzip1 (pre ++ [seq wq W q | q <- Q])) < p.
{ rewrite /unzip1 size_map size_cat size_map.
  apply: leq_trans hbudget.
  by rewrite ltn_add2l. }
have hfresh' : chain_tweak W i k \notin
    unzip1 (pre ++ [seq wq W q | q <- Q]).
{ rewrite unzip1_cat mem_cat negb_or; apply/andP; split.
  - exact: hpre.
  - rewrite unzip1_wq.
    apply: (wtw_notin W (i, k) (unzip1 Q) hi hk _ hfresh).
    move=> t ht; have /andP[ht1 ht2] := allP hQr t ht.
    by split. }
rewrite /r_chain_tcr_query; cbn [code_link].
rewrite bind_ret.
rewrite /r_chain_tcr_prefix.
eapply (r_compress_target_spec_class wots_c_hash_class p b) => //.
have hkw : k < 16 := ltn_trans hk (ltnSn 15).
have hhash : Th pp (chain_tweak W i k) (tval x) =
    Fc (bytes 16) (bytes 16) 16 (Fw W) pp (i, k) x :=
  Fc_wtw W pp (i, k) x hkw.
rewrite hhash.
move: hcont.
rewrite /r_chain_tcr_prefix map_rcons -rcons_cat /unzip1 map_rcons
  qmap_from_rcons add0n size_map.
by [].
Qed.

Lemma r_chain_tcr_chains_spec p b {B : choiceType} sp pp a ds pre
    (K0 : seq (bytes 16) -> raw_code B)
    (K1 : seq (bytes 16) * seq (bytes 16) -> raw_code B)
    (post : postcond B B) :
  size ds = 32 -> all (fun d => d < 16) ds ->
  (forall i k, i < 32 -> k < 15 ->
    chain_tweak (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) i
      k
      \notin unzip1 pre) ->
  size pre + (32 * 16) <= p ->
  (forall us, size us = 32 ->
    let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
    ⊢ ⦃ fun '(h0, h1) =>
        r_chain_tcr_prefix sp pp a pre (wcommitq W pp 0 ds us) (h0, h1) ⦄
      K0 (wsigs W pp 0 ds us) ≈
      K1 (wsigs W pp 0 ds us, wends W pp 0 ds (wsigs W pp 0 ds us))
    ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false
      (unzip1 pre) (qmap_from 0 pre) (h0, h1) ⦄
    bind (sample_sig_roots (bytes 16) (bytes 16) 16
      (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
      (dBytes 16) pp 0 ds) K0 ≈
    bind (code_link (r_chain_tcr_chains sp a ds)
      (SMTCR_game shrincs_thf wots_c_hash_class p b)) K1 ⦃ post ⦄.
Proof.
move=> hlen hds hpre hbudget hcont.
rewrite /r_chain_tcr_chains target_chains_link.
have hnil : r_chain_tcr_prefix sp pp a pre [::] =
    r_compress_block pp false (unzip1 pre) (qmap_from 0 pre).
{ by rewrite /r_chain_tcr_prefix /= cats0. }
rewrite -hnil.
apply: (target_chains_spec (bytes 16) (bytes 16) 32 16
  (32 * 16)
  (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
  (dBytes 16) _ pp (r_chain_tcr_prefix sp pp a pre) post isT).
- exact: r_chain_tcr_query_prefix_spec hpre hbudget.
- by rewrite add0n hlen.
- exact: hds.
- by [].
- by have := total_query_count_le_base 16 ds isT; rewrite hlen.
- by [].
- move=> us hus.
  apply: hcont.
  by rewrite hus.
Qed.

Lemma r_chain_tcr_eval_known p b {B : choiceType} pp (pre : precond)
    (q : tweak * seq UInt8) (c0 : raw_code B)
    (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (tcr_pp_loc shrincs_thf) = Some pp) ->
  ~~ wots_c_hash_class q.1 ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ k1 (Th pp q.1 q.2) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf wots_c_hash_class p b)
      (EVAL, (tweak × 'list ('word U8), bytes 16)) q) k1 ⦃ post ⦄.
Proof.
move=> hpin hclass hcont.
rewrite r_chain_tcr_resolve_eval.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs (tcr_pp_loc shrincs_thf) (Some pp)); first exact: hpin.
cbv beta iota.
exact: hcont.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque Th dBytes r_compress_block.

Lemma r_chain_tcr_one_spec p b {B : choiceType} sp pp a md pre
    (K0 : prepared_leaf_entry -> raw_code B) (K1 : r_compress_result -> raw_code B)
    (post : postcond B B) :
  a \notin [seq t.1.1.1.1 | t <- unzip1 pre] ->
  size pre + (32 * 16) <= p ->
  (forall us, size us = 32 ->
    let entry := r_compress_sample_entry sp pp a md us in
    ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false
      (unzip1 (pre ++ r_chain_tcr_targets sp pp a md us))
      (qmap_from 0 (pre ++ r_chain_tcr_targets sp pp a md us)) (h0, h1) ⦄
      K0 entry ≈ K1 (r_compress_result_of pp a entry) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false (unzip1 pre) (qmap_from 0 pre) (h0, h1)
    ⦄
    bind (prepared_leaf_sample sp pp a md) K0 ≈
    bind (code_link (r_chain_tcr_one sp a md)
      (SMTCR_game shrincs_thf wots_c_hash_class p b)) K1 ⦃ post ⦄.
Proof.
move=> hfresh hbudget hk.
rewrite /r_chain_tcr_one /leaf_grind_one code_link_bind bind_assoc.
rewrite code_link_bind bind_assoc.
eapply (r_chain_tcr_grind_spec p b sp a pp md _ (r_compress_block pp false (unzip1 pre)
  (qmap_from 0 pre))).
- by move=> h0 h1 [_ [_ [hr _]]].
- cbn [code_link bind].
rewrite leaf_grind_pick_map known_message_prepared_digits.
rewrite /prepared_leaf_sample code_link_bind !bind_assoc.
eapply (r_chain_tcr_chains_spec p b sp pp a _ pre).
+ exact: known_message_digits_length.
+ exact: r_compress_digits_wf.
+ (* The head leaf's chain tweaks are absent from the prefix. *)
  move=> i k hi hk'.
  apply/negP => ht.
  have hm := map_f (fun t : tweak => t.1.1.1.1) ht.
  rewrite r_chain_tcr_target_coordinate in hm.
  by move: hfresh; rewrite hm.
+ exact: hbudget.
+ move=> us hus.
cbv zeta.
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
rewrite /r_chain_tcr_prefix.
eapply (r_chain_tcr_eval_known p b pp).
- by move=> h0 h1 [_ [_ [hr _]]].
- by [].
- apply: hk.
  exact: hus.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions batch *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque Th dBytes prepared_leaf_sample r_chain_tcr_one r_compress_block
  r_compress_result_of.
Local Opaque bind code_link.

Lemma r_chain_tcr_batch_spec p b {B : choiceType} sp pp sd ats pre
    (K0 : seq prepared_leaf_entry -> raw_code B)
    (K1 : seq r_chain_tcr_result -> raw_code B) (post : postcond B B) :
  uniq ats -> all (fun a => a \notin [seq t.1.1.1.1 | t <- unzip1 pre]) ats ->
  size pre + size ats * (32 * 16) <= p ->
  (forall uss, size uss = size ats -> all (fun us => size us == 32) uss ->
    let entries := r_chain_tcr_entries sp pp sd ats uss in
    let targets := pre ++ r_chain_tcr_queries sp pp sd ats uss in
    ⊢ ⦃ fun '(h0, h1) =>
      r_compress_block pp false (unzip1 targets) (qmap_from 0 targets) (h0, h1) ⦄
      K0 entries ≈ K1 (r_compress_results pp ats entries) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) =>
    r_compress_block pp false (unzip1 pre) (qmap_from 0 pre) (h0, h1) ⦄
    bind (query_list (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd
      a)) ats) K0 ≈
    bind (code_link (query_list (fun a => r_chain_tcr_one sp a (leaf_committed_digest sd
      a)) ats)
      (SMTCR_game shrincs_thf wots_c_hash_class p b)) K1 ⦃ post ⦄.
Proof.
remember (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd a)) as qs
  eqn:hqs.
remember (fun a => r_chain_tcr_one sp a (leaf_committed_digest sd a)) as qr eqn:hqr.
elim: ats pre K0 K1 => [|a ats ih] pre K0 K1 hu hf hb hc.
- have := hc [::] erefl isT.
  by rewrite /r_chain_tcr_queries /= cats0.
- move: hu => /= /andP[hnot hu].
  move: hf => /= /andP[hfresh hf].
  have hb' : size pre + (32 * 16) <= p.
  { apply: leq_trans hb.
    by rewrite [size (a :: ats)]/= (mulSn (size ats)) addnA leq_addr. }
  cbn [query_list].
  rewrite code_link_bind !bind_assoc.
  rewrite (congr1 (fun f => f a) hqs) (congr1 (fun f => f a) hqr).
  eapply r_chain_tcr_one_spec; [exact: hfresh | exact: hb' |].
  move=> us hus; cbv zeta.
  rewrite code_link_bind !bind_assoc.
  eapply ih; first exact: hu.
  + apply/allP => a' ha'.
    rewrite unzip1_cat map_cat mem_cat negb_or; apply/andP; split.
    * exact: (allP hf a' ha').
    * apply/negP => /mapP[t ht he].
      have /eqP hcoord := allP
        (r_chain_tcr_targets_coordinate sp pp a (leaf_committed_digest sd a) us) t ht.
      by move: ha'; rewrite he hcoord (negbTE hnot).
  + (* The remaining leaves fit within the query budget. *)
    apply: leq_trans hb.
    rewrite size_cat [size (a :: ats)]/= (mulSn (size ats))
      addnA leq_add2r leq_add2l.
    apply: leq_trans (r_chain_tcr_targets_budget sp pp a (leaf_committed_digest sd a)
      us hus) _.
    by [].
  + (* Prepending the sampled head preserves lengths and block sizes. *)
    move=> uss hlen huss.
    have hlen' : size (us :: uss) = size (a :: ats) by rewrite /= hlen.
    have huss' : all (fun us => size us == 32) (us :: uss).
    { by rewrite /= hus eqxx. }
    have := hc (us :: uss) hlen' huss'.
    by rewrite /r_chain_tcr_queries /r_chain_tcr_entries /r_compress_results /= catA.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions invariant *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition r_chain_tcr_rel (po0 po1 : option (bytes 16)) (st : option
  leaf_opening_state)
    (sd : shrincs_fxmss_digest_table) (entries : seq prepared_leaf_entry) (rv : bool)
      (tw : seq
      tweak)
    (tg : chMap 'nat (tweak × 'list ('word U8))) : Prop :=
  po0 = po1 /\
  match st with
  | None => rv = false /\ tw = [::] /\ tg = emptym
  | Some (pp, sp) =>
      po0 = Some pp /\ rv = true /\
      shrincs_fxmss_structure_legal sp.1 sp.2 /\
      exists uss, size uss = size (shrincs_fxmss_schedule sp) /\
        all (fun us => size us == 32) uss /\
        entries = r_chain_tcr_entries sp pp sd (shrincs_fxmss_schedule sp) uss /\
        tw = unzip1 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp) uss) /\
        tg = qmap_from 0 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp) uss)
  end.

Definition r_chain_tcr_inv : precond :=
  heap_ignore r_compress_private ⋊
  rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, tcr_pp_loc shrincs_thf);
    (lhs, prepared_leaf_st_loc); (lhs, prepared_leaf_sd_loc); (lhs,
      prepared_leaf_entries_loc); (rhs, tcr_rev_loc);
    (rhs, tcr_tws_loc shrincs_thf); (rhs, tcr_tgts_loc shrincs_thf)] r_chain_tcr_rel.

Lemma r_chain_tcr_inv_invariant r b :
  Invariant (loc (G_prepared_leaf r))
    (unionm (loc R_chain_tcr)
      (loc (SMTCR_game shrincs_thf wots_c_hash_class r_chain_tcr_budget b)))
        r_chain_tcr_inv.
Proof.
rewrite /r_chain_tcr_inv.
ssprove_invariant.
by rewrite /rel_empty /r_chain_tcr_rel /=.
Qed.

Lemma r_chain_tcr_invE h0 h1 :
  r_chain_tcr_inv (h0, h1) ->
  heap_ignore r_compress_private (h0, h1) /\
  r_chain_tcr_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (tcr_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_sd_loc)
    (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 tcr_rev_loc) (get_heap h1 (tcr_tws_loc shrincs_thf))
    (get_heap h1 (tcr_tgts_loc shrincs_thf)).
Proof.
by [].
Qed.

Lemma r_chain_tcr_invI h0 h1 :
  heap_ignore r_compress_private (h0, h1) ->
  r_chain_tcr_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (tcr_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_sd_loc)
    (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 tcr_rev_loc) (get_heap h1 (tcr_tws_loc shrincs_thf))
    (get_heap h1 (tcr_tgts_loc shrincs_thf)) ->
  r_chain_tcr_inv (h0, h1).
Proof.
by move=> hi hr; split.
Qed.

Lemma r_chain_tcr_inv_start pp h0 h1 :
  r_chain_tcr_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  get_heap h0 prepared_leaf_pp_loc = Some pp ->
  r_compress_block pp false [::] emptym (h0, h1).
Proof.
move=> /r_chain_tcr_invE [hi [he hr]] hs hp.
rewrite hs in hr.
move: hr => [hv [hw ht]].
by split; [exact: hi | split; [exact: hp | split; [rewrite -he | repeat split]]].
Qed.

Lemma r_chain_tcr_inv_finish pp sp sd uss h0 h1 :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size uss = size (shrincs_fxmss_schedule sp) -> all (fun us => size us == 32) uss ->
  r_compress_block pp true (unzip1 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule
    sp) uss))
    (qmap_from 0 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp) uss)) (h0,
      h1) ->
  let entries := r_chain_tcr_entries sp pp sd (shrincs_fxmss_schedule sp) uss in
  r_chain_tcr_inv (r_compress_stored pp sp sd entries h0, r_compress_stored pp sp sd
    entries h1).
Proof.
move=> hsp hlen huss [hi [hl [hr [hv [hw ht]]]]] entries.
apply: r_chain_tcr_invI.
- rewrite /r_compress_stored.
  do 3 apply: put_pre_cond_heap_ignore.
  exact: hi.
- (* Stored entries and target records satisfy the collision relation. *)
  rewrite /r_compress_stored /r_chain_tcr_rel.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite hl hr hv hw ht.
  repeat split => //.
  exists uss; repeat split => //.
Qed.

Lemma r_chain_tcr_inv_seed_eq h0 h1 :
  r_chain_tcr_inv (h0, h1) ->
  get_heap h0 prepared_leaf_pp_loc = get_heap h1 (tcr_pp_loc shrincs_thf).
Proof.
by move=> /r_chain_tcr_invE [_ [he _]].
Qed.

Lemma r_chain_tcr_inv_no_seed h0 h1 :
  r_chain_tcr_inv (h0, h1) -> get_heap h0 prepared_leaf_pp_loc = None ->
  get_heap h0 prepared_leaf_st_loc = None.
Proof.
move=> /r_chain_tcr_invE [hi [he hr]] hp.
case hs: (get_heap h0 prepared_leaf_st_loc) hr => [[pp sp]|] //.
by rewrite /r_chain_tcr_rel hp => -[].
Qed.

Lemma r_chain_tcr_inv_pin pp h0 h1 :
  r_chain_tcr_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  r_compress_block pp false [::] emptym
    (set_heap h0 prepared_leaf_pp_loc (Some pp),
     set_heap h1 (tcr_pp_loc shrincs_thf) (Some pp)).
Proof.
move=> /r_chain_tcr_invE [hi [he hr]] hs.
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

Lemma r_chain_tcr_block_initial_inv pp h0 h1 :
  r_compress_block pp false [::] emptym (h0, h1) ->
  get_heap h0 prepared_leaf_st_loc = None -> r_chain_tcr_inv (h0, h1).
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]] hs.
apply: r_chain_tcr_invI hi _.
by rewrite /r_chain_tcr_rel hl hr hs hv hw ht.
Qed.
