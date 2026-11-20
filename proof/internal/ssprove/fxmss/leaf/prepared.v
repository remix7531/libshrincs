(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.prepared

    Batch leaf intermediates on I_known_message: hybrid 0 is the re-rooted
    known-message game, hybrid 1 removes grinding collisions, and hybrid 2
    also removes compression collisions. Hybrid 3 additionally excludes chain
    collisions against the honest chain targets; hybrid 4 excludes chain
    preimages. GEN prepares every legal leaf
    before revealing the seed; failed slots remain in the cache. SIGN
    consumes each slot even when its cached signature is None. CHECK
    reads initialized state and checks the index before its hybrid predicate.
    EVAL shares the lazy seed; the compression hop uses known_message_coll_filter.
    Operation identifiers occupy 2000..2004. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core chain.ud toolkit.batch_map.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import params scheme games hop.chain_common.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.opening leaf.paths leaf.commitments
    leaf.known_message_game
  leaf.known_message leaf.compress.pure.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition prepared_leaf_entry : choice_type :=
  ('list (bytes 16) × 'list (bytes 16)) × 'option ('nat).
Definition prepared_leaf_default : prepared_leaf_entry := (([::], [::]), None).
Definition prepared_leaf_st_loc := mkloc 2000 (None : option leaf_opening_state).
Definition prepared_leaf_pp_loc := mkloc 2001 (None : option (bytes 16)).
Definition prepared_leaf_sd_loc := mkloc 2002 (emptym : shrincs_fxmss_digest_table).
Definition prepared_leaf_entries_loc := mkloc 2003 ([::] : seq prepared_leaf_entry).
Definition prepared_leaf_slog_loc := mkloc 2004 ([::] : seq nat).
Definition prepared_leaf_locs :=
  [fmap prepared_leaf_st_loc; prepared_leaf_pp_loc; prepared_leaf_sd_loc;
        prepared_leaf_entries_loc; prepared_leaf_slog_loc].

Definition prepared_leaf_seed : raw_code (bytes 16) :=
  ppo ← get prepared_leaf_pp_loc ;;
  match ppo with
  | Some pp => ret pp
  | None => pp ← dBytes 16 ;; #put prepared_leaf_pp_loc := Some pp ;; ret pp
  end.

Definition prepared_leaf_sample (sp : shrincs_fxmss_structure) pp a md : raw_code
  prepared_leaf_entry :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let ds := known_message_digits shrincs_fxmss_sha256 sp pp a md in
  sg ← sample_sig_roots (wcp_PP W) (wcp_N W) (wcp_w W) (Fw W)
    (wcp_dN W) pp 0 ds ;;
  ret ((sg, complete_ends W pp ds sg), known_message_find shrincs_fxmss_sha256 sp pp a
    md).

Definition prepared_leaf_samples sp pp (sd : shrincs_fxmss_digest_table) :=
  query_list (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd a))
    (shrincs_fxmss_schedule sp).

Definition prepared_leaf_roots sp pp (entries : seq prepared_leaf_entry) :=
  [seq Th pp (shrincs_fxmss_pk_tweak ae.1) (r_compress_encode ae.2.1.2)
    | ae <- zip (shrincs_fxmss_schedule sp) entries].

Definition prepared_leaf_gen (sp : shrincs_fxmss_structure) sd : raw_code
  leaf_opening_public :=
  sto ← get prepared_leaf_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  pp ← prepared_leaf_seed ;;
  entries ← prepared_leaf_samples sp pp sd ;;
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := entries ;;
  ret (pp, prepared_leaf_roots sp pp entries).

Definition prepared_leaf_sign (j : nat) : raw_code ('option leaf_opening_signature) :=
  st ← getSome prepared_leaf_st_loc ;;
  #assert j < size (shrincs_fxmss_schedule st.2) ;;
  slog ← get prepared_leaf_slog_loc ;;
  #assert j \notin slog ;;
  #put prepared_leaf_slog_loc := j :: slog ;;
  entries ← get prepared_leaf_entries_loc ;;
  let entry := nth prepared_leaf_default entries j in
  ret (omap (fun c => wcp_sig_encode
    (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 (leaf_coord_at st.2 j) st.2.1 (uint
      U8 st.2.2))
    (entry.1.1, c)) entry.2).

Definition prepared_leaf_forged_ends sp pp a (mw : bytes 32 * leaf_opening_signature) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let sg := wcp_sig_decode W mw.2 in
  complete_ends W pp (digest_of W pp mw.1 sg.2) sg.1.

Definition prepared_leaf_chain_decision sp pp a md (entry : prepared_leaf_entry)
    (mw : bytes 32 * leaf_opening_signature) : option (nat * bytes 16) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let sg := wcp_sig_decode W mw.2 in
  wtcr_dec W pp (known_message_digits shrincs_fxmss_sha256 sp pp a md)
    (digest_of W pp mw.1 sg.2) entry.1.1 sg.1.

Definition prepared_leaf_pre_decision sp pp a md (entry : prepared_leaf_entry)
    (mw : bytes 32 * leaf_opening_signature) : option (nat * bytes 16) :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let sg := wcp_sig_decode W mw.2 in
  wpre_dec W pp (known_message_digits shrincs_fxmss_sha256 sp pp a md)
    (digest_of W pp mw.1 sg.2) entry.1.1 sg.1.

Definition prepared_leaf_verdict_pre_chain (r : nat) sp pp a md (entry :
  prepared_leaf_entry)
    (mw : bytes 32 * leaf_opening_signature) : bool :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let sg := wcp_sig_decode W mw.2 in
  let v := shrincs_wots_verify W pp
    (Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode entry.1.2)) mw.1 sg &&
    (~~ isSome entry.2 || (mw.1 != md)) in
  let hit := isSome entry.2 &&
    (digest_of W pp mw.1 sg.2 == known_message_digits shrincs_fxmss_sha256 sp pp a md)
      in
  v && (if r == 0 then true else ~~ hit) &&
    (if r < 2 then true else prepared_leaf_forged_ends sp pp a mw == entry.1.2).

Definition prepared_leaf_verdict_pre_preimage (r : nat) sp pp a md entry mw : bool :=
  if r < 3 then prepared_leaf_verdict_pre_chain r sp pp a md entry mw
  else prepared_leaf_verdict_pre_chain r sp pp a md entry mw &&
    ~~ isSome (prepared_leaf_chain_decision sp pp a md entry mw).

Definition prepared_leaf_verdict (r : nat) sp pp a md entry mw : bool :=
  if r < 4 then prepared_leaf_verdict_pre_preimage r sp pp a md entry mw
  else prepared_leaf_verdict_pre_preimage r sp pp a md entry mw &&
    ~~ isSome (prepared_leaf_pre_decision sp pp a md entry mw).

Definition prepared_leaf_check (r : nat) (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome prepared_leaf_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  entries ← get prepared_leaf_entries_loc ;;
  sd ← get prepared_leaf_sd_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  ret (prepared_leaf_verdict r st.2 st.1 a (leaf_committed_digest sd a)
    (nth prepared_leaf_default entries q.1) q.2).

#[export] Instance prepared_leaf_seed_valid I : ValidCode prepared_leaf_locs I
  prepared_leaf_seed.
Proof.
rewrite /prepared_leaf_seed; ssprove_valid.
Qed.

#[export] Instance prepared_leaf_sample_valid L I sp pp a md :
  ValidCode L I (prepared_leaf_sample sp pp a md).
Proof.
rewrite /prepared_leaf_sample.
eapply valid_bind; last by move=> sg; apply valid_ret.
apply: sample_sig_roots_valid.
Qed.

Lemma prepared_leaf_samples_valid L I sp pp sd :
  ValidCode L I (prepared_leaf_samples sp pp sd).
Proof.
rewrite /prepared_leaf_samples.
elim: (shrincs_fxmss_schedule sp) => [|a ats ih].
- exact: valid_ret.
- cbn [query_list].
  eapply valid_bind; first exact: prepared_leaf_sample_valid.
  move=> entry; eapply valid_bind; first exact: ih.
  move=> entries; exact: valid_ret.
Qed.

#[export] Instance prepared_leaf_gen_valid I sp sd :
  ValidCode prepared_leaf_locs I (prepared_leaf_gen sp sd).
Proof.
rewrite /prepared_leaf_gen.
ssprove_valid.
- exact: prepared_leaf_seed_valid.
- exact: prepared_leaf_samples_valid.
Qed.

#[export] Instance prepared_leaf_sign_valid I j : ValidCode prepared_leaf_locs I
  (prepared_leaf_sign j).
Proof.
rewrite /prepared_leaf_sign; ssprove_valid.
Qed.

#[export] Instance prepared_leaf_check_valid I r q : ValidCode prepared_leaf_locs I
  (prepared_leaf_check r q).
Proof.
rewrite /prepared_leaf_check; ssprove_valid.
Qed.

#[local] Arguments prepared_leaf_gen : simpl never.
#[local] Arguments prepared_leaf_sign : simpl never.
#[local] Arguments prepared_leaf_check : simpl never.

Definition G_prepared_leaf (r : nat) : game I_known_message :=
  [package prepared_leaf_locs;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      '(sp, sd) {
      prepared_leaf_gen sp sd
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      prepared_leaf_sign j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      prepared_leaf_check r q
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      pp ← prepared_leaf_seed ;;
      ret (Th pp q.1 q.2)
    }
  ].

Local Opaque Th prepared_leaf_chain_decision prepared_leaf_pre_decision.
#[local] Arguments prepared_leaf_chain_decision : simpl never.

Lemma prepared_leaf_verdict_collision sp pp a md entry mw :
  prepared_leaf_verdict 1 sp pp a md entry mw ->
  Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode (prepared_leaf_forged_ends sp pp a
    mw)) =
    Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode entry.1.2).
Proof.
change (prepared_leaf_verdict_pre_chain 1 sp pp a md entry mw ->
  Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode (prepared_leaf_forged_ends sp pp a
    mw)) =
    Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode entry.1.2)).
rewrite /prepared_leaf_verdict_pre_chain /= !andbT.
move=> /andP[/andP[/and3P[_ _ /eqP he] _] _].
exact: he.
Qed.

#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments prepared_leaf_forged_ends : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments known_message_digits : simpl never.

Lemma prepared_leaf_verdict_ideal sp pp a md entry mw :
  prepared_leaf_verdict 1 sp pp a md entry mw &&
    (prepared_leaf_forged_ends sp pp a mw == entry.1.2) =
  prepared_leaf_verdict 2 sp pp a md entry mw.
Proof.
have h (v hit ends : bool) :
    (v && ~~ hit && true) && ends = v && ~~ hit && ends.
{ by rewrite andbT. }
rewrite /prepared_leaf_verdict /prepared_leaf_verdict_pre_preimage
  /prepared_leaf_verdict_pre_chain.
exact: h.
Qed.

Lemma resolve_prepared_leaf_eval r q :
  resolve (G_prepared_leaf r)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (pp ← prepared_leaf_seed ;; ret (Th pp q.1 q.2)).
Proof. by rewrite /G_prepared_leaf /resolve /= coerce_kleisliE. Qed.

Lemma resolve_prepared_leaf_gen r sp sd :
  resolve (G_prepared_leaf r) (known_message_gen, (shrincs_fxmss_structure ×
    shrincs_fxmss_digest_table,
    leaf_opening_public)) (sp, sd) =
  prepared_leaf_gen sp sd.
Proof.
by rewrite /G_prepared_leaf /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_prepared_leaf_sign r j :
  resolve (G_prepared_leaf r) (known_message_sign, ('nat, 'option
    leaf_opening_signature)) j = prepared_leaf_sign j.
Proof.
by rewrite /G_prepared_leaf /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_prepared_leaf_check r q :
  resolve (G_prepared_leaf r) (known_message_check, (leaf_opening_opening, 'bool)) q =
    prepared_leaf_check r q.
Proof.
by rewrite /G_prepared_leaf /resolve /= coerce_kleisliE.
Qed.


Lemma prepared_leaf_verdict_chain sp pp a md entry mw :
  prepared_leaf_verdict 2 sp pp a md entry mw &&
    ~~ isSome (prepared_leaf_chain_decision sp pp a md entry mw) =
  prepared_leaf_verdict 3 sp pp a md entry mw.
Proof.
have hbase : prepared_leaf_verdict_pre_chain 2 sp pp a md entry mw =
    prepared_leaf_verdict_pre_chain 3 sp pp a md entry mw.
{ by rewrite /prepared_leaf_verdict_pre_chain. }
change (prepared_leaf_verdict_pre_chain 2 sp pp a md entry mw &&
  ~~ isSome (prepared_leaf_chain_decision sp pp a md entry mw) =
  prepared_leaf_verdict_pre_chain 3 sp pp a md entry mw &&
  ~~ isSome (prepared_leaf_chain_decision sp pp a md entry mw)).
by rewrite hbase.
Qed.

Lemma prepared_leaf_verdict_before_chain r sp pp a md entry mw :
  r <= 2 ->
  prepared_leaf_verdict r sp pp a md entry mw =
    let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
    let sg := wcp_sig_decode W mw.2 in
    let v := shrincs_wots_verify W pp
      (Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode entry.1.2)) mw.1 sg &&
      (~~ isSome entry.2 || (mw.1 != md)) in
    let hit := isSome entry.2 &&
      (digest_of W pp mw.1 sg.2 == known_message_digits shrincs_fxmss_sha256 sp pp a md)
        in
    v && (if r == 0 then true else ~~ hit) &&
      (if r < 2 then true else prepared_leaf_forged_ends sp pp a mw == entry.1.2).
Proof.
move=> hr.
have hr' : r < 3 := hr.
have hr4 : r < 4 := leq_trans hr (leqnSn 2).
by rewrite /prepared_leaf_verdict /prepared_leaf_verdict_pre_preimage hr4 hr'
  /prepared_leaf_verdict_pre_chain.
Qed.

Lemma prepared_leaf_verdict_before_preimage r sp pp a md entry mw :
  r < 4 ->
  prepared_leaf_verdict r sp pp a md entry mw =
  prepared_leaf_verdict_pre_preimage r sp pp a md entry mw.
Proof.
by move=> hr; rewrite /prepared_leaf_verdict hr.
Qed.

Lemma prepared_leaf_verdict_preimage sp pp a md entry mw :
  prepared_leaf_verdict 3 sp pp a md entry mw &&
    ~~ isSome (prepared_leaf_pre_decision sp pp a md entry mw) =
  prepared_leaf_verdict 4 sp pp a md entry mw.
Proof.
have hbase : prepared_leaf_verdict_pre_chain 3 sp pp a md entry mw =
    prepared_leaf_verdict_pre_chain 4 sp pp a md entry mw.
{ by rewrite /prepared_leaf_verdict_pre_chain. }
change ((prepared_leaf_verdict_pre_chain 3 sp pp a md entry mw &&
    ~~ isSome (prepared_leaf_chain_decision sp pp a md entry mw)) &&
    ~~ isSome (prepared_leaf_pre_decision sp pp a md entry mw) =
  (prepared_leaf_verdict_pre_chain 4 sp pp a md entry mw &&
    ~~ isSome (prepared_leaf_chain_decision sp pp a md entry mw)) &&
    ~~ isSome (prepared_leaf_pre_decision sp pp a md entry mw)).
by rewrite hbase.
Qed.
