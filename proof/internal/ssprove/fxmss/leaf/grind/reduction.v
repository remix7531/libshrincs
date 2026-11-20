(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.grind.reduction

    The option search agrees with the bounded leaf search, including exhaustion.
    Batch reduction to the static type-22 option grinding game. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.batch_map.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import params scheme games hop.compress.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.paths leaf.known_message_game leaf.known_message
    leaf.prepared
  leaf.fixed_batch leaf.opening leaf.commitments leaf.compress.pure.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Grinding pure *)

#[local] Open Scope nat_scope.
Local Opaque Th prepared_leaf_chain_decision.

Definition r_grind_targets (sp : shrincs_fxmss_structure) :=
  [seq shrincs_fxmss_grind_tweak a | a <- shrincs_fxmss_schedule sp].
Lemma r_grind_targets_uniq sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> uniq (r_grind_targets sp).
Proof.
move=> hsp.
rewrite /r_grind_targets (map_inj_uniq shrincs_fxmss_grind_tweak_inj).
exact: leaf_schedule_uniq.
Qed.
Lemma r_grind_targets_budget sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> size (r_grind_targets sp) <= 2 ^ 64.
Proof.
move=> hsp.
rewrite /r_grind_targets size_map (leaf_schedule_length sp hsp).
exact: shrincs_fxmss_leaf_count_bound.
Qed.
Lemma r_grind_eval sp pp a md c :
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  th_eval shrincs_thf pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).1
    (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).2 =
  wcp_H_grind W pp (grind_adrs W) (md, c).
Proof. by []. Qed.
Lemma r_grind_encoded_class a md c :
  wots_c_grind_class (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).1.
Proof. by []. Qed.
Lemma r_grind_search sp pp a md :
  ohead [seq i <- iota 0 wots_c_counter_max |
    let q := wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md i in
    if wots_c_grind_class q.1 then wots_c_grind_prp (th_eval shrincs_thf pp q.1 q.2)
    else false] = known_message_find shrincs_fxmss_sha256 sp pp a md.
Proof.
exact: (grind_search_find_ctr (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1
  (uint U8 sp.2))).
Qed.
Definition r_grind_answer sp pp a md : option (bytes 16 * nat) :=
  omap (fun c => (Th pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).1
    (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).2, c))
    (known_message_find shrincs_fxmss_sha256 sp pp a md).
Definition r_grind_digits (sp : shrincs_fxmss_structure) a (answer : option (bytes 16 *
  nat)) :=
  match answer with
  | Some (g, _) => wcp_digits (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1
    (uint U8 sp.2)) g
  | None => nseq 32 15
  end.
Lemma r_grind_answer_digits sp pp a md :
  r_grind_digits sp a (r_grind_answer sp pp a md) = known_message_digits
    shrincs_fxmss_sha256 sp pp a md.
Proof.
rewrite /r_grind_digits /r_grind_answer /known_message_digits.
by case: known_message_find.
Qed.
Lemma r_grind_answer_counter sp pp a md :
  omap snd (r_grind_answer sp pp a md) = known_message_find shrincs_fxmss_sha256 sp pp a
    md.
Proof. by rewrite /r_grind_answer; case: known_message_find. Qed.
Definition r_grind_hit sp pp a md (entry : prepared_leaf_entry)
    (mw : bytes 32 * leaf.opening.leaf_opening_signature) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  isSome entry.2 && (digest_of W pp mw.1 (wcp_sig_decode W mw.2).2 ==
    known_message_digits shrincs_fxmss_sha256 sp pp a md).
Lemma r_grind_collision sp pp a md entry mw c :
  entry.2 = known_message_find shrincs_fxmss_sha256 sp pp a md -> entry.2 = Some c ->
  prepared_leaf_verdict 0 sp pp a md entry mw -> r_grind_hit sp pp a md entry mw ->
  (mw.1 != md) &&
    (Th pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).1
       (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md c).2 ==
     Th pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) mw.1
       (wcp_sig_decode (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
         sp.2)) mw.2).2).1
       (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) mw.1
       (wcp_sig_decode (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
         sp.2)) mw.2).2).2).
Proof.
move=> he hc.
rewrite (prepared_leaf_verdict_before_chain 0 sp pp a md entry mw isT).
cbv zeta.
rewrite hc eqxx ltn0Sn !andbT.
move=> /andP[_ hf].
rewrite /r_grind_hit hc /known_message_digits -he hc /=.
move=> /eqP hd.
change (is_true (mw.1 != md)) in hf.
rewrite hf /=.
apply/eqP.
symmetry.
apply: (wcp_digits_inj (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8
  sp.2))).
exact: hd.
Qed.
Lemma r_grind_verdict_ideal sp pp a md entry mw :
  (if prepared_leaf_verdict 0 sp pp a md entry mw && r_grind_hit sp pp a md entry mw
   then false else prepared_leaf_verdict 0 sp pp a md entry mw) =
  prepared_leaf_verdict 1 sp pp a md entry mw.
Proof.
rewrite (prepared_leaf_verdict_before_chain 0 sp pp a md entry mw isT)
  (prepared_leaf_verdict_before_chain 1 sp pp a md entry mw isT) /r_grind_hit.
cbv zeta.
set v := shrincs_wots_verify _ _ _ _ _ && _.
set hit := isSome _ && _.
by case: v; case: hit.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Grinding *)

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.

Definition r_grind_result : choice_type := bytes 16 × prepared_leaf_entry.
Definition r_grind_one (sp : shrincs_fxmss_structure) a md : raw_code r_grind_result :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  answer ← call [ SQUERY ] : { tweak × bytes 32 ~> 'option (bytes 16 × 'nat) }
    (shrincs_fxmss_grind_tweak a, md) ;;
  '(sg, ends) ← cp_chains W 0 (r_grind_digits sp a answer) ;;
  root ← call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 }
    (shrincs_fxmss_pk_tweak a, r_compress_encode ends) ;;
  ret (root, ((sg, ends), omap snd answer)).
Definition r_grind_batch sp (sd : shrincs_fxmss_digest_table) :=
  query_list (fun a => r_grind_one sp a (leaf_committed_digest sd a))
    (shrincs_fxmss_schedule sp).
Definition r_grind_gen (sp : shrincs_fxmss_structure) sd : raw_code leaf_opening_public
  :=
  sto ← get prepared_leaf_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  _ ← call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } known_message_pin ;;
  results ← r_grind_batch sp sd ;;
  pp ← call [ SGETPP ] : { 'unit ~> bytes 16 } tt ;;
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := [seq entry.2 | entry <- results] ;;
  ret (pp, [seq entry.1 | entry <- results]).
Definition r_grind_check (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome prepared_leaf_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  entries ← get prepared_leaf_entries_loc ;;
  sd ← get prepared_leaf_sd_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  let entry := nth prepared_leaf_default entries q.1 in
  let md := leaf_committed_digest sd a in
  let v := prepared_leaf_verdict 0 st.2 st.1 a md entry q.2 in
  if v && r_grind_hit st.2 st.1 a md entry q.2 then
    call [ SCHECK ] : { 'nat × (bytes 32 × 'nat) ~> 'bool }
      (q.1, (q.2.1, (wcp_sig_decode
        (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a st.2.1 (uint U8 st.2.2))
          q.2.2).2))
  else ret v.
Lemma r_grind_walk_valid (W : wc_params) L I i k n (x : wcp_N W) :
  fhas I (cp_eval_op W) -> ValidCode L I (cp_walk W i k n x).
Proof.
move=> hi.
elim: n k x => [|n ih] k x /=.
- apply valid_ret.
- eapply valid_opr; first exact: hi.
  move=> r; exact: ih.
Qed.
Lemma r_grind_chains_valid (W : wc_params) L I st ds :
  fhas I (cp_eval_op W) -> ValidCode L I (cp_chains W st ds).
Proof.
move=> hi.
elim: ds st => [|d ds ih] st /=.
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> u; eapply valid_bind.
  + case: d => [|d']; first by apply valid_ret.
    eapply valid_opr; first exact: hi.
    move=> r; apply valid_ret.
  + move=> s; eapply valid_bind; first exact: r_grind_walk_valid.
    move=> e; eapply valid_bind; first exact: ih.
    move=> [ss es]; apply valid_ret.
Qed.
Lemma r_grind_one_valid L sp a md :
  ValidCode L (I_STCRP_option shrincs_thf (bytes 32)) (r_grind_one sp a md).
Proof.
rewrite /r_grind_one.
eapply valid_bind; first by ssprove_valid.
move=> answer.
eapply valid_bind.
- apply: r_grind_chains_valid.
  by fmap_solve.
- move=> [sg ends]; ssprove_valid.
Qed.
Lemma r_grind_batch_valid L sp sd :
  ValidCode L (I_STCRP_option shrincs_thf (bytes 32)) (r_grind_batch sp sd).
Proof.
rewrite /r_grind_batch.
elim: (shrincs_fxmss_schedule sp) => [|a ats ih].
- exact: valid_ret.
- cbn [query_list].
  eapply valid_bind; first exact: r_grind_one_valid.
  move=> entry; eapply valid_bind; first exact: ih.
  move=> entries; exact: valid_ret.
Qed.
#[export] Instance r_grind_gen_valid sp sd :
  ValidCode prepared_leaf_locs (I_STCRP_option shrincs_thf (bytes 32)) (r_grind_gen sp
    sd).
Proof.
rewrite /r_grind_gen.
ssprove_valid.
exact: r_grind_batch_valid.
Qed.
#[export] Instance r_grind_check_valid q :
  ValidCode prepared_leaf_locs (I_STCRP_option shrincs_thf (bytes 32)) (r_grind_check
    q).
Proof. rewrite /r_grind_check; ssprove_valid. Qed.
#[local] Arguments r_grind_gen : simpl never.
#[local] Arguments r_grind_check : simpl never.
Definition R_grind : package (I_STCRP_option shrincs_thf (bytes 32)) I_known_message
  :=
  [package prepared_leaf_locs;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      '(sp, sd) {
      r_grind_gen sp sd
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      prepared_leaf_sign j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      r_grind_check q
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } q
    }
  ].

Lemma resolve_r_grind_eval q :
  resolve (R_grind)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (call [ EVAL ] : { leaf_opening_eval_input ~> bytes 16 } q).
Proof. by rewrite /R_grind /resolve /= coerce_kleisliE. Qed.

Lemma resolve_r_grind_gen sp sd :
  resolve R_grind (known_message_gen, (shrincs_fxmss_structure ×
    shrincs_fxmss_digest_table,
    leaf_opening_public)) (sp, sd) =
  r_grind_gen sp sd.
Proof. by rewrite /R_grind /resolve /= coerce_kleisliE. Qed.
Lemma resolve_r_grind_check q :
  resolve R_grind (known_message_check, (leaf_opening_opening, 'bool)) q =
    r_grind_check q.
Proof. by rewrite /R_grind /resolve /= coerce_kleisliE. Qed.
Lemma resolve_r_grind_sign j :
  resolve R_grind (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    prepared_leaf_sign j.
Proof. by rewrite /R_grind /resolve /= coerce_kleisliE. Qed.
