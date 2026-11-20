(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.chain_tcr.reduction

    Batch chain-collision reduction to static type-16 SMTCR game. Locate a
    collision witness in the batch target list. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.batch_map chain.core chain.target_loops chain.tcr_extra.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.chain_common.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.opening leaf.paths leaf.commitments
  leaf.known_message_game leaf.known_message leaf.prepare leaf.compress.pure
    leaf.prepared
  leaf.compress.sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition r_chain_tcr_budget := (2 ^ 64 * (32 * 16))%N.

Definition r_chain_tcr_query (sp : shrincs_fxmss_structure) a i k (x : bytes 16) :
  raw_code
  (bytes 16) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  call [ TQUERY ] : { tweak × 'list ('word U8) ~> bytes 16 }
    (chain_tweak W i k, wcp_encode_node W x).

Definition r_chain_tcr_chains sp a ds :=
  target_chains (bytes 16) 16 (dBytes 16) (r_chain_tcr_query sp a) 0 ds.

Definition r_chain_tcr_offset sp pp (sd : shrincs_fxmss_digest_table) j :=
  sumn [seq total_query_count 16
    (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a))
    | a <- take j (shrincs_fxmss_schedule sp)].

Definition r_chain_tcr_result : choice_type := bytes 16 × prepared_leaf_entry.
Definition r_chain_tcr_one (sp : shrincs_fxmss_structure) a md : raw_code
  r_chain_tcr_result :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  leaf ← leaf_grind_one sp a md ;;
  '(sg, ends) ← r_chain_tcr_chains sp a (fixed_digits leaf) ;;
  root ← call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 }
    (shrincs_fxmss_pk_tweak a, r_compress_encode ends) ;;
  ret (root, ((sg, ends), omap fst leaf.2)).

Definition r_chain_tcr_batch sp (sd : shrincs_fxmss_digest_table) :=
  query_list (fun a => r_chain_tcr_one sp a (leaf_committed_digest sd a))
    (shrincs_fxmss_schedule sp).

Definition r_chain_tcr_gen (sp : shrincs_fxmss_structure) sd : raw_code
  leaf_opening_public :=
  sto ← get prepared_leaf_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  _ ← call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } known_message_pin ;;
  results ← r_chain_tcr_batch sp sd ;;
  pp ← call [ GETPP ] : { 'unit ~> bytes 16 } tt ;;
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := [seq entry.2 | entry <- results] ;;
  ret (pp, [seq entry.1 | entry <- results]).

Definition r_chain_tcr_check (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome prepared_leaf_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  entries ← get prepared_leaf_entries_loc ;;
  sd ← get prepared_leaf_sd_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  let entry := nth prepared_leaf_default entries q.1 in
  let md := leaf_committed_digest sd a in
  let v := prepared_leaf_verdict 2 st.2 st.1 a md entry q.2 in
  if v then
    match prepared_leaf_chain_decision st.2 st.1 a md entry q.2 with
    | Some (j, u) =>
      call [ CHECK ] : { 'nat × 'list ('word U8) ~> 'bool }
        ((r_chain_tcr_offset st.2 st.1 sd q.1 + j)%N, tval u)
    | None => ret v
    end
  else ret v.

Lemma r_chain_tcr_query_valid L sp a i k x :
  ValidCode L (I_SMTCR shrincs_thf) (r_chain_tcr_query sp a i k x).
Proof. rewrite /r_chain_tcr_query; ssprove_valid. Qed.

Lemma r_chain_tcr_chains_valid L sp a ds :
  ValidCode L (I_SMTCR shrincs_thf) (r_chain_tcr_chains sp a ds).
Proof.
rewrite /r_chain_tcr_chains; apply: target_chains_valid.
exact: r_chain_tcr_query_valid.
Qed.

Lemma r_chain_tcr_one_valid L sp a md :
  ValidCode L (I_SMTCR shrincs_thf) (r_chain_tcr_one sp a md).
Proof.
rewrite /r_chain_tcr_one.
eapply valid_bind.
- apply: leaf_grind_one_valid.
by fmap_solve.
- move=> leaf; eapply valid_bind.
  + exact: r_chain_tcr_chains_valid.
  + move=> [sg ends]; ssprove_valid.
Qed.

Lemma r_chain_tcr_batch_valid L sp sd :
  ValidCode L (I_SMTCR shrincs_thf) (r_chain_tcr_batch sp sd).
Proof.
rewrite /r_chain_tcr_batch.
elim: (shrincs_fxmss_schedule sp) => [|a ats ih].
- exact: valid_ret.
- cbn [query_list].
  eapply valid_bind; first exact: r_chain_tcr_one_valid.
  move=> entry; eapply valid_bind; first exact: ih.
  move=> entries; exact: valid_ret.
Qed.

#[export] Instance r_chain_tcr_gen_valid sp sd :
  ValidCode prepared_leaf_locs (I_SMTCR shrincs_thf) (r_chain_tcr_gen sp sd).
Proof.
rewrite /r_chain_tcr_gen.
ssprove_valid.
exact: r_chain_tcr_batch_valid.
Qed.

#[export] Instance r_chain_tcr_check_valid q :
  ValidCode prepared_leaf_locs (I_SMTCR shrincs_thf) (r_chain_tcr_check q).
Proof.
rewrite /r_chain_tcr_check; ssprove_valid.
Qed.

#[local] Arguments r_chain_tcr_gen : simpl never.
#[local] Arguments r_chain_tcr_check : simpl never.

Definition R_chain_tcr : package (I_SMTCR shrincs_thf) I_known_message :=
  [package prepared_leaf_locs;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      '(sp, sd) {
      r_chain_tcr_gen sp sd
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      prepared_leaf_sign j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      r_chain_tcr_check q
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } q
    }
  ].

Lemma resolve_r_chain_tcr_eval q :
  resolve (R_chain_tcr)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (call [ EVAL ] : { leaf_opening_eval_input ~> bytes 16 } q).
Proof. by rewrite /R_chain_tcr /resolve /= coerce_kleisliE. Qed.

Lemma resolve_r_chain_tcr_gen sp sd :
  resolve R_chain_tcr (known_message_gen, (shrincs_fxmss_structure ×
    shrincs_fxmss_digest_table,
    leaf_opening_public)) (sp, sd) =
  r_chain_tcr_gen sp sd.
Proof.
by rewrite /R_chain_tcr /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_r_chain_tcr_check q :
  resolve R_chain_tcr (known_message_check, (leaf_opening_opening, 'bool)) q =
    r_chain_tcr_check q.
Proof.
by rewrite /R_chain_tcr /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_r_chain_tcr_sign j :
  resolve R_chain_tcr (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    prepared_leaf_sign j.
Proof.
by rewrite /R_chain_tcr /resolve /= coerce_kleisliE.
Qed.

Lemma r_chain_tcr_ideal_check_decision sp pp a md entry mw :
  (if prepared_leaf_verdict 2 sp pp a md entry mw then
    if prepared_leaf_chain_decision sp pp a md entry mw is Some _ then false else true
   else false) = prepared_leaf_verdict 3 sp pp a md entry mw.
Proof.
rewrite -prepared_leaf_verdict_chain.
by case: prepared_leaf_verdict; case: prepared_leaf_chain_decision.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions targets *)

#[local] Open Scope nat_scope.

Definition r_chain_tcr_targets sp pp a md (us : seq (bytes 16)) :
    seq (tweak * seq UInt8) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  [seq wq W q | q <- wcommitq W pp 0 (known_message_digits shrincs_fxmss_sha256 sp pp a
    md) us].

Lemma r_chain_tcr_target_coordinate sp a i k :
  (chain_tweak (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) i
    k).1.1.1.1 = a.
Proof. by case: a. Qed.

Lemma r_chain_tcr_targets_coordinate sp pp a md us :
  all (fun t : tweak => t.1.1.1.1 == a) (unzip1 (r_chain_tcr_targets sp pp a md us)).
Proof.
rewrite /r_chain_tcr_targets /unzip1 -map_comp all_map.
apply/allP => t ht.
change (a == a).
exact: eqxx.
Qed.

Lemma r_chain_tcr_targets_size sp pp a md us :
  size us = 32 -> size (r_chain_tcr_targets sp pp a md us) =
    total_query_count 16 (known_message_digits shrincs_fxmss_sha256 sp pp a md).
Proof.
move=> hus.
rewrite /r_chain_tcr_targets size_map /wcommitq size_commit_queries //.
by rewrite known_message_digits_length.
Qed.

Lemma r_chain_tcr_targets_budget sp pp a md us :
  size us = 32 -> size (r_chain_tcr_targets sp pp a md us) <= 512.
Proof.
move=> hus; rewrite r_chain_tcr_targets_size //.
have := total_query_count_le_base 16 (known_message_digits shrincs_fxmss_sha256 sp pp
  a md) isT.
by rewrite known_message_digits_length.
Qed.

Definition r_chain_tcr_queries sp pp sd (ats : seq shrincs_fxmss_coord)
    (uss : seq (seq (bytes 16))) : seq (tweak * seq UInt8) :=
  flatten [seq r_chain_tcr_targets sp pp au.1 (leaf_committed_digest sd au.1) au.2
    | au <- zip ats uss].

Definition r_chain_tcr_entries sp pp sd (ats : seq shrincs_fxmss_coord)
    (uss : seq (seq (bytes 16))) : seq prepared_leaf_entry :=
  [seq r_compress_sample_entry sp pp au.1 (leaf_committed_digest sd au.1) au.2
    | au <- zip ats uss].

Lemma r_chain_tcr_queries_size sp pp sd ats uss :
  size uss = size ats -> all (fun us => size us == 32) uss ->
  size (r_chain_tcr_queries sp pp sd ats uss) =
    sumn [seq total_query_count 16
      (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a)) |
        a <- ats].
Proof.
elim: ats uss => [|a ats ih] [|us uss] //= [hlen] /andP[/eqP hus huss].
rewrite /r_chain_tcr_queries /= size_cat r_chain_tcr_targets_size //.
by rewrite ih.
Qed.

Lemma r_chain_tcr_queries_budget sp pp sd ats uss :
  size uss = size ats -> all (fun us => size us == 32) uss ->
  size (r_chain_tcr_queries sp pp sd ats uss) <= size ats * 512.
Proof.
move=> hlen huss; rewrite (r_chain_tcr_queries_size _ _ _ _ _ hlen huss).
have ha : all (fun n => n <= 512)
  [seq total_query_count 16
    (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a)) |
      a <- ats].
{ apply/allP => n /mapP[a ha ->].
  have := total_query_count_le_base 16
    (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a))
      isT.
  by rewrite known_message_digits_length. }
by have := sumn_all_leq _ _ ha; rewrite size_map.
Qed.

Lemma r_chain_tcr_queries_coordinates sp pp sd ats uss :
  all (fun t : tweak => t.1.1.1.1 \in ats)
    (unzip1 (r_chain_tcr_queries sp pp sd ats uss)).
Proof.
elim: ats uss => [|a ats ih] [|us uss] //=.
rewrite /r_chain_tcr_queries /= unzip1_cat all_cat.
apply/andP; split.
- apply: sub_all (r_chain_tcr_targets_coordinate sp pp a
    (leaf_committed_digest sd a) us).
  by move=> t /= /eqP ->; rewrite in_cons eqxx.
- apply: sub_all (ih uss).
  by move=> t /= ht; rewrite in_cons ht orbT.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions pure *)

Local Opaque Th.

Lemma r_chain_tcr_dec_none sp pp a md entry mw :
  known_message_find shrincs_fxmss_sha256 sp pp a md = None ->
  prepared_leaf_chain_decision sp pp a md entry mw = None.
Proof.
move=> hfind.
rewrite /prepared_leaf_chain_decision /known_message_digits hfind /wtcr_dec.
exact: tcr_allmax_none.
Qed.

Lemma r_chain_tcr_dec_digit sp pp a md entry mw jc u :
  prepared_leaf_chain_decision sp pp a md entry mw = Some (jc, u) ->
  exists c, known_message_find shrincs_fxmss_sha256 sp pp a md = Some c /\
    known_message_digits shrincs_fxmss_sha256 sp pp a md =
      digest_of (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2))
        pp md c.
Proof.
case hfind: (known_message_find shrincs_fxmss_sha256 sp pp a md) => [c|].
- move=> _; exists c; split; first by [].
  by rewrite /known_message_digits hfind.
- by rewrite (r_chain_tcr_dec_none sp pp a md entry mw hfind).
Qed.

Lemma r_chain_tcr_verdict_facts sp pp a md entry mw c :
  known_message_find shrincs_fxmss_sha256 sp pp a md = Some c ->
  entry.2 = Some c -> prepared_leaf_verdict 2 sp pp a md entry mw ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let sg := wcp_sig_decode W mw.2 in
  [/\ valid_digest W (digest_of W pp mw.1 sg.2),
    size sg.1 == 32,
    prepared_leaf_forged_ends sp pp a mw = entry.1.2 &
    digest_of W pp mw.1 sg.2 != known_message_digits shrincs_fxmss_sha256 sp pp a md].
Proof.
move=> hfind hentry.
rewrite /prepared_leaf_verdict /prepared_leaf_verdict_pre_preimage
  /prepared_leaf_verdict_pre_chain /=.
move=> /andP[/andP[/andP[/and3P[hvd hsz _] _] hgr] /eqP hends].
split=> //.
by move: hgr; rewrite hentry /=.
Qed.

Lemma r_chain_tcr_dec_collision sp pp a md mw (us : seq (bytes 16)) jc u :
  size us = 32 ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let entry := r_compress_sample_entry sp pp a md us in
  prepared_leaf_verdict 2 sp pp a md entry mw ->
  prepared_leaf_chain_decision sp pp a md entry mw = Some (jc, u) ->
  exists t v,
    [/\ qnth (wcommitq W pp 0 (known_message_digits shrincs_fxmss_sha256 sp pp a md) us)
      jc =
        Some (t, v),
      u != v &
      Fc (wcp_PP W) (wcp_N W) (wcp_w W) (Fw W) pp t u =
      Fc (wcp_PP W) (wcp_N W) (wcp_w W) (Fw W) pp t v].
Proof.
move=> hus W entry hwin hdec.
have [c [hfind hdig]] := r_chain_tcr_dec_digit sp pp a md entry mw jc u hdec.
have hentry : entry.2 = Some c by rewrite /entry /r_compress_sample_entry hfind.
have [hvd hsz hends hne] :=
  r_chain_tcr_verdict_facts sp pp a md entry mw c hfind hentry hwin.
have hgood := find_counter_good W pp md c hfind.
rewrite /prepared_leaf_forged_ends /entry /r_compress_sample_entry hdig in hends.
rewrite hdig in hne.
have hcol := wtcr_decisionP W pp md mw.1 c (wcp_sig_decode W mw.2).2
  us (wcp_sig_decode W mw.2).1 hgood hus hvd hsz hends hne.
rewrite /prepared_leaf_chain_decision /entry /r_compress_sample_entry hdig in hdec.
rewrite hdec in hcol.
by rewrite hdig.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain collisions lookup *)

#[local] Open Scope nat_scope.
Local Opaque Th r_compress_sample_entry r_chain_tcr_targets.

Lemma r_chain_tcr_entries_nth sp pp sd ats uss i :
  size uss = size ats -> i < size ats ->
  nth prepared_leaf_default (r_chain_tcr_entries sp pp sd ats uss) i =
  r_compress_sample_entry sp pp (nth (uint U8 0, uint U64 0) ats i)
    (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i))
    (nth [::] uss i).
Proof.
elim: ats uss i => [|a ats ih] [|us uss] i //= [hlen].
case: i => [|i] hi; first by [].
exact: ih hlen hi.
Qed.

Lemma r_chain_tcr_queries_lookup sp pp sd ats uss i j q :
  size uss = size ats -> all (fun us => size us == 32) uss ->
  i < size ats ->
  qnth (r_chain_tcr_targets sp pp (nth (uint U8 0, uint U64 0) ats i)
    (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i))
    (nth [::] uss i)) j = Some q ->
  qnth (r_chain_tcr_queries sp pp sd ats uss)
    (sumn [seq total_query_count 16
      (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a))
      | a <- take i ats] + j) = Some q.
Proof.
elim: ats uss i => [|a ats ih] [|us uss] i //= [hlen]
  /andP[/eqP hus huss].
case: i => [|i] hi hq.
- rewrite /r_chain_tcr_queries /= add0n qnth_cat_l //.
  exact: qnth_size hq.
- rewrite /r_chain_tcr_queries /= -addnA
    -(r_chain_tcr_targets_size sp pp a (leaf_committed_digest sd a) us hus)
    qnth_cat_r.
  exact: ih hlen huss hi hq.
Qed.

(* Expose the target encoding for the extracted collision lookup. *)
Local Transparent r_chain_tcr_targets.

Lemma r_chain_tcr_encoded_collision sp pp a md mw us jc u :
  size us = 32 ->
  prepared_leaf_verdict 2 sp pp a md (r_compress_sample_entry sp pp a md us) mw ->
  prepared_leaf_chain_decision sp pp a md (r_compress_sample_entry sp pp a md us) mw =
    Some (jc, u) ->
  exists t m0,
    [/\ qnth (r_chain_tcr_targets sp pp a md us) jc = Some (t, m0),
      tval u != m0 & Th pp t (tval u) = Th pp t m0].
Proof.
move=> hus hwin hdec.
have [t [v [hq hne hcol]]] := r_chain_tcr_dec_collision sp pp a md mw us jc u hus hwin
  hdec.
set W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2).
have hus' : size us = size (known_message_digits shrincs_fxmss_sha256 sp pp a md) by
  rewrite
  known_message_digits_length.
have hpos := commit_queries_pos_all W pp 0
  (known_message_digits shrincs_fxmss_sha256 sp pp a md) us hus' (r_compress_digits_wf
    sp pp a md).
have ht := qnth_mem_unzip1 _ _ _ _ hq.
have hlt : t.2 < 16 := ltn_trans (allP hpos t ht) (ltnSn 15).
have heval x : Th pp (chain_tweak W t.1 t.2) (tval x) =
  Fc (bytes 16) (bytes 16) 16 (Fw W) pp t x := Fc_wtw W pp t x hlt.
exists (chain_tweak W t.1 t.2), (tval v); split.
- rewrite /r_chain_tcr_targets qnth_map hq.
  by [].
- change (wcp_encode_node W u != wcp_encode_node W v).
  by rewrite (inj_eq (wcp_encode_node_inj W)).
- by rewrite !heval.
Qed.

Lemma r_chain_tcr_table_collision sp pp sd uss i mw jc u :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size uss = size (shrincs_fxmss_schedule sp) -> all (fun us => size us == 32) uss ->
  i < size (shrincs_fxmss_schedule sp) ->
  let a := leaf_coord_at sp i in
  let entry := nth prepared_leaf_default (r_chain_tcr_entries sp pp sd
    (shrincs_fxmss_schedule sp) uss)
    i in
  prepared_leaf_verdict 2 sp pp a (leaf_committed_digest sd a) entry mw ->
  prepared_leaf_chain_decision sp pp a (leaf_committed_digest sd a) entry mw = Some (jc,
    u) ->
  exists t m0,
    [/\ getm (qmap_from 0 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp)
      uss))
        (r_chain_tcr_offset sp pp sd i + jc) = Some (t, m0),
      tval u != m0 & Th pp t (tval u) = Th pp t m0].
Proof.
move=> hsp hlen huss hi a entry hwin hdec.
have hi' : i < shrincs_fxmss_leaf_count sp.1 sp.2.
{ by rewrite -(leaf_schedule_length sp hsp). }
have hn := leaf_schedule_nth sp i hsp hi'.
have hus : size (nth [::] uss i) = 32.
{ apply/eqP; apply: (allP huss).
  apply: mem_nth.
  by rewrite hlen. }
have he : entry = r_compress_sample_entry sp pp a
    (leaf_committed_digest sd a) (nth [::] uss i).
{ by rewrite /entry (r_chain_tcr_entries_nth _ _ _ _ _ _ hlen hi) hn. }
rewrite he in hwin hdec.
have [t [m0 [hq hne hcol]]] := r_chain_tcr_encoded_collision sp pp a
  (leaf_committed_digest sd a) mw (nth [::] uss i) jc u hus hwin hdec.
exists t, m0; split=> //.
have hm := qmap_from_get 0 (r_chain_tcr_queries sp pp sd (shrincs_fxmss_schedule sp)
  uss)
  (r_chain_tcr_offset sp pp sd i + jc).
rewrite add0n in hm.
rewrite hm /r_chain_tcr_offset.
apply: (r_chain_tcr_queries_lookup sp pp sd (shrincs_fxmss_schedule sp) uss i jc
  (t, m0) hlen huss hi).
by rewrite hn.
Qed.
