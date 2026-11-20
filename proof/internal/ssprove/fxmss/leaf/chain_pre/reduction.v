(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.chain_pre.reduction

    Batch chain-preimage reduction to static type-16 SMPRE game. Locate a preimage
    witness in the batch target list. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.batch_map chain.core chain.pre_loops chain.pre_terminal.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.chain_common analysis.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.opening leaf.paths leaf.commitments
  leaf.known_message_game leaf.known_message leaf.prepare leaf.compress.pure
    leaf.prepared
  leaf.compress.sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition r_chain_pre_budget := (2 ^ 64 * 32)%N.

Definition r_chain_pre_query (sp : shrincs_fxmss_structure) a i k : raw_code (bytes 16)
  :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  call [ PQUERY ] : { tweak ~> bytes 16 } (chain_tweak W i k).

Definition r_chain_pre_chains sp a ds :=
  pre_chains (bytes 16) (dBytes 16) (r_chain_pre_query sp a) 0 ds.

Definition r_chain_pre_offset sp pp (sd : shrincs_fxmss_digest_table) j :=
  sumn [seq preimage_query_count
    (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a))
    | a <- take j (shrincs_fxmss_schedule sp)].

Definition r_chain_pre_result : choice_type :=
  ('list (bytes 16) × 'list ('nat)) × 'option ('nat).
Definition r_chain_pre_one (sp : shrincs_fxmss_structure) a md : raw_code
  r_chain_pre_result :=
  leaf ← leaf_grind_one sp a md ;;
  sg ← r_chain_pre_chains sp a (fixed_digits leaf) ;;
  ret ((sg, fixed_digits leaf), omap fst leaf.2).

Definition r_chain_pre_complete sp pp a (entry : r_chain_pre_result) :
  prepared_leaf_entry :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  ((entry.1.1, complete_ends W pp entry.1.2 entry.1.1), entry.2).

Definition r_chain_pre_complete_batch sp pp (results : seq r_chain_pre_result) :=
  [seq r_chain_pre_complete sp pp ae.1 ae.2 | ae <- zip (shrincs_fxmss_schedule sp)
    results].

Definition r_chain_pre_batch sp (sd : shrincs_fxmss_digest_table) :=
  query_list (fun a => r_chain_pre_one sp a (leaf_committed_digest sd a))
    (shrincs_fxmss_schedule sp).

Definition r_chain_pre_gen (sp : shrincs_fxmss_structure) sd : raw_code
  leaf_opening_public :=
  sto ← get prepared_leaf_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  _ ← call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } known_message_pin ;;
  results ← r_chain_pre_batch sp sd ;;
  pp ← call [ PGETPP ] : { 'unit ~> bytes 16 } tt ;;
  let entries := r_chain_pre_complete_batch sp pp results in
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := entries ;;
  ret (pp, prepared_leaf_roots sp pp entries).

Definition r_chain_pre_check (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome prepared_leaf_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  entries ← get prepared_leaf_entries_loc ;;
  sd ← get prepared_leaf_sd_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  let entry := nth prepared_leaf_default entries q.1 in
  let md := leaf_committed_digest sd a in
  let v := prepared_leaf_verdict 3 st.2 st.1 a md entry q.2 in
  if v then
    match prepared_leaf_pre_decision st.2 st.1 a md entry q.2 with
    | Some (j, u) =>
      call [ PCHECK ] : { 'nat × 'list ('word U8) ~> 'bool }
        ((r_chain_pre_offset st.2 st.1 sd q.1 + j)%N, tval u)
    | None => ret v
    end
  else ret v.

Lemma r_chain_pre_query_valid L sp a i k :
  ValidCode L (I_SMPRE shrincs_thf) (r_chain_pre_query sp a i k).
Proof. rewrite /r_chain_pre_query; ssprove_valid. Qed.

Lemma r_chain_pre_chains_valid L sp a ds :
  ValidCode L (I_SMPRE shrincs_thf) (r_chain_pre_chains sp a ds).
Proof.
rewrite /r_chain_pre_chains; apply: pre_chains_valid.
exact: r_chain_pre_query_valid.
Qed.

Lemma r_chain_pre_one_valid L sp a md :
  ValidCode L (I_SMPRE shrincs_thf) (r_chain_pre_one sp a md).
Proof.
rewrite /r_chain_pre_one.
eapply valid_bind.
- apply: leaf_grind_one_valid.
by fmap_solve.
- move=> leaf; eapply valid_bind.
  + exact: r_chain_pre_chains_valid.
  + move=> sg; ssprove_valid.
Qed.

Lemma r_chain_pre_batch_valid L sp sd :
  ValidCode L (I_SMPRE shrincs_thf) (r_chain_pre_batch sp sd).
Proof.
rewrite /r_chain_pre_batch.
elim: (shrincs_fxmss_schedule sp) => [|a ats ih].
- exact: valid_ret.
- cbn [query_list].
  eapply valid_bind; first exact: r_chain_pre_one_valid.
  move=> entry; eapply valid_bind; first exact: ih.
  move=> entries; exact: valid_ret.
Qed.

#[export] Instance r_chain_pre_gen_valid sp sd :
  ValidCode prepared_leaf_locs (I_SMPRE shrincs_thf) (r_chain_pre_gen sp sd).
Proof.
rewrite /r_chain_pre_gen.
ssprove_valid.
exact: r_chain_pre_batch_valid.
Qed.

#[export] Instance r_chain_pre_check_valid q :
  ValidCode prepared_leaf_locs (I_SMPRE shrincs_thf) (r_chain_pre_check q).
Proof.
rewrite /r_chain_pre_check; ssprove_valid.
Qed.

#[local] Arguments r_chain_pre_gen : simpl never.
#[local] Arguments r_chain_pre_check : simpl never.

Definition R_chain_pre : package (I_SMPRE shrincs_thf) I_known_message :=
  [package prepared_leaf_locs;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      '(sp, sd) {
      r_chain_pre_gen sp sd
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      prepared_leaf_sign j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      r_chain_pre_check q
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } q
    }
  ].

Lemma resolve_r_chain_pre_eval q :
  resolve (R_chain_pre)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (call [ EVAL ] : { leaf_opening_eval_input ~> bytes 16 } q).
Proof. by rewrite /R_chain_pre /resolve /= coerce_kleisliE. Qed.

Lemma resolve_r_chain_pre_gen sp sd :
  resolve R_chain_pre (known_message_gen, (shrincs_fxmss_structure ×
    shrincs_fxmss_digest_table,
    leaf_opening_public)) (sp, sd) =
  r_chain_pre_gen sp sd.
Proof.
by rewrite /R_chain_pre /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_r_chain_pre_check q :
  resolve R_chain_pre (known_message_check, (leaf_opening_opening, 'bool)) q =
    r_chain_pre_check q.
Proof.
by rewrite /R_chain_pre /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_r_chain_pre_sign j :
  resolve R_chain_pre (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    prepared_leaf_sign j.
Proof.
by rewrite /R_chain_pre /resolve /= coerce_kleisliE.
Qed.

Lemma r_chain_pre_ideal_check_decision sp pp a md entry mw :
  (if prepared_leaf_verdict 3 sp pp a md entry mw then
    if prepared_leaf_pre_decision sp pp a md entry mw is Some _ then false else true
   else false) = prepared_leaf_verdict 4 sp pp a md entry mw.
Proof.
rewrite -prepared_leaf_verdict_preimage.
by case: prepared_leaf_verdict; case: prepared_leaf_pre_decision.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages targets *)

(* Keep opacity settings local to the target-query lemmas. *)
Section ChainPreimageTargets.

#[local] Open Scope nat_scope.
Local Opaque Th known_message_find known_message_digits pre_queries.

Definition r_chain_pre_targets sp pp a md (us : seq (bytes 16)) :
    seq (tweak * seq UInt8) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  [seq wq W q | q <- pre_queries (bytes 16) 0 (known_message_digits shrincs_fxmss_sha256
    sp pp a
    md) us].

Lemma r_chain_pre_target_coordinate sp a i k :
  (chain_tweak (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) i
    k).1.1.1.1 = a.
Proof. by case: a. Qed.

Lemma r_chain_pre_targets_coordinate sp pp a md us :
  all (fun t : tweak => t.1.1.1.1 == a) (unzip1 (r_chain_pre_targets sp pp a md us)).
Proof.
rewrite /r_chain_pre_targets /unzip1 -map_comp all_map.
apply/allP => t ht.
change (a == a).
exact: eqxx.
Qed.

Lemma r_chain_pre_targets_size sp pp a md us :
  size us = 32 -> size (r_chain_pre_targets sp pp a md us) =
    preimage_query_count (known_message_digits shrincs_fxmss_sha256 sp pp a md).
Proof.
move=> hus.
rewrite /r_chain_pre_targets size_map size_pre_queries //.
by rewrite known_message_digits_length.
Qed.

Lemma r_chain_pre_targets_budget sp pp a md us :
  size us = 32 -> size (r_chain_pre_targets sp pp a md us) <= 32.
Proof.
move=> hus; rewrite r_chain_pre_targets_size //.
exact: npq_le (known_message_digits_length shrincs_fxmss_sha256 sp pp a md).
Qed.

Local Opaque r_chain_pre_targets.

Definition r_chain_pre_queries sp pp sd (ats : seq shrincs_fxmss_coord)
    (uss : seq (seq (bytes 16))) : seq (tweak * seq UInt8) :=
  flatten [seq r_chain_pre_targets sp pp au.1 (leaf_committed_digest sd au.1) au.2
    | au <- zip ats uss].

Definition r_chain_pre_entries sp pp sd (ats : seq shrincs_fxmss_coord)
    (uss : seq (seq (bytes 16))) : seq prepared_leaf_entry :=
  [seq r_compress_sample_entry sp pp au.1 (leaf_committed_digest sd au.1) au.2
    | au <- zip ats uss].

Lemma r_chain_pre_queries_size sp pp sd ats uss :
  size uss = size ats -> all (fun us => size us == 32) uss ->
  size (r_chain_pre_queries sp pp sd ats uss) =
    sumn [seq preimage_query_count
      (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a)) |
        a <- ats].
Proof.
elim: ats uss => [|a ats ih] [|us uss] //= [hlen] /andP[/eqP hus huss].
rewrite /r_chain_pre_queries /= size_cat r_chain_pre_targets_size //.
by rewrite ih.
Qed.

Lemma r_chain_pre_queries_budget sp pp sd ats uss :
  size uss = size ats -> all (fun us => size us == 32) uss ->
  size (r_chain_pre_queries sp pp sd ats uss) <= size ats * 32.
Proof.
move=> hlen huss; rewrite (r_chain_pre_queries_size _ _ _ _ _ hlen huss).
have ha : all (fun n => n <= 32)
  [seq preimage_query_count
    (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a)) |
      a <- ats].
{ apply/allP => n /mapP[a ha ->].
  exact: npq_le (known_message_digits_length shrincs_fxmss_sha256 sp pp a
    (leaf_committed_digest
    sd a)). }
by have := sumn_all_leq _ _ ha; rewrite size_map.
Qed.

Lemma r_chain_pre_queries_coordinates sp pp sd ats uss :
  all (fun t : tweak => t.1.1.1.1 \in ats)
    (unzip1 (r_chain_pre_queries sp pp sd ats uss)).
Proof.
elim: ats uss => [|a ats ih] [|us uss] //=.
rewrite /r_chain_pre_queries /= unzip1_cat all_cat.
apply/andP; split.
- apply: sub_all (r_chain_pre_targets_coordinate sp pp a
    (leaf_committed_digest sd a) us).
  by move=> t /= /eqP ->; rewrite in_cons eqxx.
- apply: sub_all (ih uss).
  by move=> t /= ht; rewrite in_cons ht orbT.
Qed.

End ChainPreimageTargets.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages pure *)

Lemma prepared_leaf_chain_decisionE sp pp a md entry mw :
  prepared_leaf_chain_decision sp pp a md entry mw =
    let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
    let sg := wcp_sig_decode W mw.2 in
    wtcr_dec W pp (known_message_digits shrincs_fxmss_sha256 sp pp a md)
      (digest_of W pp mw.1 sg.2) entry.1.1 sg.1.
Proof. by []. Qed.

Lemma prepared_leaf_pre_decisionE sp pp a md entry mw :
  prepared_leaf_pre_decision sp pp a md entry mw =
    let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
    let sg := wcp_sig_decode W mw.2 in
    wpre_dec W pp (known_message_digits shrincs_fxmss_sha256 sp pp a md)
      (digest_of W pp mw.1 sg.2) entry.1.1 sg.1.
Proof. by []. Qed.

Local Opaque Th digest_of prepared_leaf_chain_decision prepared_leaf_pre_decision.
#[local] Arguments digest_of : simpl never.
#[local] Arguments known_message_digits : simpl never.
#[local] Arguments prepared_leaf_chain_decision : simpl never.
#[local] Arguments prepared_leaf_pre_decision : simpl never.
#[local] Arguments prepared_leaf_forged_ends : simpl never.

Lemma r_chain_pre_coord sp pp a md (fdv : seq nat) :
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  valid_msg 32 16 (wcp_constant_sum W) fdv ->
  ~~ (isSome (known_message_find shrincs_fxmss_sha256 sp pp a md) &&
    (fdv == known_message_digits shrincs_fxmss_sha256 sp pp a md)) ->
  has (fun i => nth 0 fdv i < nth 0 (known_message_digits shrincs_fxmss_sha256 sp pp a
    md) i)
    (iota 0 32).
Proof.
move=> W hvm.
have hsz : size fdv = 32 by case/and3P: hvm => /eqP.
case hfind: (known_message_find shrincs_fxmss_sha256 sp pp a md) => [c|].
- (* A successful grinding counter gives a distinct equal-sum digest. *)
  rewrite /known_message_digits hfind.
  change (fdv != digest_of W pp md c ->
    has (fun i => nth 0 fdv i < nth 0 (digest_of W pp md c) i) (iota 0 32)).
  move=> hne.
  have hgood := find_counter_good W pp md c hfind.
  have hsum : sumn fdv = sumn (digest_of W pp md c).
  { by move: hvm hgood => /and3P[_ _ /eqP ->] /andP[_ /eqP ->]. }
  have hszeq : size fdv = size (digest_of W pp md c).
  { by rewrite hsz size_digest_of. }
  have hne' : fdv <> digest_of W pp md c by apply/eqP.
  have [k hk hlt] := eq_sumn_exists_lt hszeq hsum hne'.
  apply/hasP; exists k; first by rewrite mem_iota /= add0n -hsz.
  exact: hlt.
- (* Exhausted grinding leaves a valid digest with a nonmaximal digit. *)
  rewrite /known_message_digits hfind => _.
  have hdeg : wcp_constant_sum W != (32 * 15)%N by [].
  have hh := valid_msg_not_allmax 32 16 (wcp_constant_sum W) fdv hdeg hvm.
  set k := find (fun d => d < 15) fdv.
  have hk : k < size fdv by rewrite -has_find.
  have hlt : nth 0 fdv k < 15 := nth_find 0 hh.
  apply/hasP; exists k; first by rewrite mem_iota /= add0n -hsz.
  by rewrite nth_nseq -hsz hk.
Qed.

Local Opaque pre_decision tcr_decision sigs_of ends_from_sig Fc.

Lemma r_chain_pre_terminal sp pp a md mw (us : seq (bytes 16)) :
  size us = 32 ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let entry := r_compress_sample_entry sp pp a md us in
  prepared_leaf_verdict 3 sp pp a md entry mw ->
  exists jc x t u,
    [/\ prepared_leaf_pre_decision sp pp a md entry mw = Some (jc, x),
        qnth (pre_queries (bytes 16) 0 (known_message_digits shrincs_fxmss_sha256 sp pp
          a md) us)
          jc =
          Some (t, u)
      & Fc (wcp_PP W) (wcp_N W) (wcp_w W) (Fw W) pp t x =
        Fc (wcp_PP W) (wcp_N W) (wcp_w W) (Fw W) pp t u].
Proof.
move=> hus W entry.
rewrite /prepared_leaf_verdict /prepared_leaf_verdict_pre_preimage /=.
move=> /andP[hv ht].
move: hv; rewrite /prepared_leaf_verdict_pre_chain /=.
move=> /andP[/andP[/andP[/and3P[hvd hsz _] _] hgr] /eqP hends].
have hvm := vdigest_valid_msg W pp mw.1 (wcp_sig_decode W mw.2).2 hvd.
have hcoord := r_chain_pre_coord sp pp a md
  (digest_of W pp mw.1 (wcp_sig_decode W mw.2).2) hvm hgr.
have hnone : prepared_leaf_chain_decision sp pp a md entry mw = None.
{ by move: ht; case: (prepared_leaf_chain_decision _ _ _ _ _ _). }
rewrite prepared_leaf_chain_decisionE /entry /r_compress_sample_entry in hnone.
rewrite /prepared_leaf_forged_ends /entry /r_compress_sample_entry !wcendsE in hends.
rewrite prepared_leaf_pre_decisionE /entry /r_compress_sample_entry /wpre_dec.
exact: (pre_terminal (wcp_PP W) (wcp_N W) 32 16 (wcp_constant_sum W)
  (Fw W) pp (known_message_digits shrincs_fxmss_sha256 sp pp a md) us
  (wcp_sig_decode W mw.2).1 (digest_of W pp mw.1 (wcp_sig_decode W mw.2).2)
  (known_message_digits_length shrincs_fxmss_sha256 sp pp a md) (r_compress_digits_wf sp
    pp a md)
  hus hvm hsz hcoord hends hnone).
Qed.

Lemma r_chain_pre_terminal_zero sp pp a md mw (us : seq (bytes 16)) :
  size us = 32 ->
  prepared_leaf_verdict 4 sp pp a md (r_compress_sample_entry sp pp a md us) mw = false.
Proof.
move=> hus.
rewrite -prepared_leaf_verdict_preimage.
case hv: (prepared_leaf_verdict 3 sp pp a md (r_compress_sample_entry sp pp a md us) mw)
  => //.
have [jc [x [t [u [hdec _ _]]]]] := r_chain_pre_terminal sp pp a md mw us hus hv.
by rewrite hdec.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages lookup *)

#[local] Open Scope nat_scope.
Local Opaque Th r_compress_sample_entry r_chain_pre_targets.

Lemma r_chain_pre_entries_nth sp pp sd ats uss i :
  size uss = size ats -> i < size ats ->
  nth prepared_leaf_default (r_chain_pre_entries sp pp sd ats uss) i =
  r_compress_sample_entry sp pp (nth (uint U8 0, uint U64 0) ats i)
    (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i))
    (nth [::] uss i).
Proof.
elim: ats uss i => [|a ats ih] [|us uss] i //= [hlen].
case: i => [|i] hi; first by [].
exact: ih hlen hi.
Qed.

Lemma r_chain_pre_queries_lookup sp pp sd ats uss i j q :
  size uss = size ats -> all (fun us => size us == 32) uss ->
  i < size ats ->
  qnth (r_chain_pre_targets sp pp (nth (uint U8 0, uint U64 0) ats i)
    (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i))
    (nth [::] uss i)) j = Some q ->
  qnth (r_chain_pre_queries sp pp sd ats uss)
    (sumn [seq preimage_query_count
      (known_message_digits shrincs_fxmss_sha256 sp pp a (leaf_committed_digest sd a))
      | a <- take i ats] + j) = Some q.
Proof.
elim: ats uss i => [|a ats ih] [|us uss] i //= [hlen]
  /andP[/eqP hus huss].
case: i => [|i] hi hq.
- rewrite /r_chain_pre_queries /= add0n qnth_cat_l //.
  exact: qnth_size hq.
- rewrite /r_chain_pre_queries /= -addnA
    -(r_chain_pre_targets_size sp pp a (leaf_committed_digest sd a) us hus)
    qnth_cat_r.
  exact: ih hlen huss hi hq.
Qed.

(* Expose the target encoding for the extracted preimage lookup. *)
Local Transparent r_chain_pre_targets.

Lemma r_chain_pre_encoded_preimage sp pp a md mw us jc u :
  size us = 32 ->
  prepared_leaf_verdict 3 sp pp a md (r_compress_sample_entry sp pp a md us) mw ->
  prepared_leaf_pre_decision sp pp a md (r_compress_sample_entry sp pp a md us) mw =
    Some (jc, u) ->
  exists t m0,
    qnth (r_chain_pre_targets sp pp a md us) jc = Some (t, m0) /\
      Th pp t (tval u) = Th pp t m0.
Proof.
move=> hus hwin hdec.
have [jc' [u' [t [v [hdec' hq hcol]]]]] :=
  r_chain_pre_terminal sp pp a md mw us hus hwin.
rewrite hdec in hdec'; case: hdec' => he1 he2.
subst jc' u'.
set W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2).
have hus' : size us = size (known_message_digits shrincs_fxmss_sha256 sp pp a md) by
  rewrite
  known_message_digits_length.
have hpos := pre_queries_pos_all W 0
  (known_message_digits shrincs_fxmss_sha256 sp pp a md) us hus' (r_compress_digits_wf
    sp pp a md).
have ht := qnth_mem_unzip1 _ _ _ _ hq.
have hlt : t.2 < 16 := ltn_trans (allP hpos t ht) (ltnSn 15).
have heval x : Th pp (chain_tweak W t.1 t.2) (tval x) =
  Fc (bytes 16) (bytes 16) 16 (Fw W) pp t x := Fc_wtw W pp t x hlt.
exists (chain_tweak W t.1 t.2), (tval v); split.
- rewrite /r_chain_pre_targets qnth_map hq.
  by [].
- by rewrite !heval.
Qed.

Lemma r_chain_pre_table_preimage sp pp sd uss i mw jc u :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size uss = size (shrincs_fxmss_schedule sp) -> all (fun us => size us == 32) uss ->
  i < size (shrincs_fxmss_schedule sp) ->
  let a := leaf_coord_at sp i in
  let entry := nth prepared_leaf_default (r_chain_pre_entries sp pp sd
    (shrincs_fxmss_schedule sp) uss)
    i in
  prepared_leaf_verdict 3 sp pp a (leaf_committed_digest sd a) entry mw ->
  prepared_leaf_pre_decision sp pp a (leaf_committed_digest sd a) entry mw = Some (jc,
    u) ->
  exists t m0,
    getm (qmap_from 0 (r_chain_pre_queries sp pp sd (shrincs_fxmss_schedule sp) uss))
        (r_chain_pre_offset sp pp sd i + jc) = Some (t, m0) /\
      Th pp t (tval u) = Th pp t m0.
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
{ by rewrite /entry (r_chain_pre_entries_nth _ _ _ _ _ _ hlen hi) hn. }
rewrite he in hwin hdec.
have [t [m0 [hq hcol]]] := r_chain_pre_encoded_preimage sp pp a
  (leaf_committed_digest sd a) mw (nth [::] uss i) jc u hus hwin hdec.
exists t, m0; split=> //.
have hm := qmap_from_get 0 (r_chain_pre_queries sp pp sd (shrincs_fxmss_schedule sp)
  uss)
  (r_chain_pre_offset sp pp sd i + jc).
rewrite add0n in hm.
rewrite hm /r_chain_pre_offset.
apply: (r_chain_pre_queries_lookup sp pp sd (shrincs_fxmss_schedule sp) uss i jc
  (t, m0) hlen huss hi).
by rewrite hn.
Qed.
