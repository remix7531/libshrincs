(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.compress.reduction

    Batch compression reduction to static type-17 SMTCR game. The compression
    block couples lazy seeds while tracking the hidden SMTCR target table, tweak
    list and reveal flag. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.batch_map toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.compress.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.opening leaf.paths leaf.commitments
  leaf.known_message_game leaf.known_message leaf.prepare leaf.compress.pure
    leaf.prepared.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Compression *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition r_compress_result : choice_type := bytes 16 × prepared_leaf_entry.
Definition r_compress_one (sp : shrincs_fxmss_structure) a md : raw_code
  r_compress_result :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  leaf ← leaf_grind_one sp a md ;;
  '(sg, ends) ← cp_chains W 0 (fixed_digits leaf) ;;
  root ← call [ TQUERY ] : { tweak × 'list ('word U8) ~> bytes 16 }
    (shrincs_fxmss_pk_tweak a, r_compress_encode ends) ;;
  ret (root, ((sg, ends), omap fst leaf.2)).

Definition r_compress_batch sp (sd : shrincs_fxmss_digest_table) :=
  query_list (fun a => r_compress_one sp a (leaf_committed_digest sd a))
    (shrincs_fxmss_schedule sp).

Definition r_compress_gen (sp : shrincs_fxmss_structure) sd : raw_code
  leaf_opening_public :=
  sto ← get prepared_leaf_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  _ ← call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } known_message_pin ;;
  results ← r_compress_batch sp sd ;;
  pp ← call [ GETPP ] : { 'unit ~> bytes 16 } tt ;;
  #put prepared_leaf_st_loc := Some (pp, sp) ;;
  #put prepared_leaf_sd_loc := sd ;;
  #put prepared_leaf_entries_loc := [seq entry.2 | entry <- results] ;;
  ret (pp, [seq entry.1 | entry <- results]).

Definition r_compress_check (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome prepared_leaf_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  entries ← get prepared_leaf_entries_loc ;;
  sd ← get prepared_leaf_sd_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  let entry := nth prepared_leaf_default entries q.1 in
  let ends := prepared_leaf_forged_ends st.2 st.1 a q.2 in
  let v := prepared_leaf_verdict 1 st.2 st.1 a (leaf_committed_digest sd a) entry q.2 in
  if v && (ends != entry.1.2) then
    call [ CHECK ] : { 'nat × 'list ('word U8) ~> 'bool } (q.1, r_compress_encode ends)
  else ret v.

Lemma r_compress_one_valid L sp a md :
  ValidCode L (I_SMTCR shrincs_thf) (r_compress_one sp a md).
Proof.
rewrite /r_compress_one.
eapply valid_bind.
- apply: leaf_grind_one_valid.
by fmap_solve.
- move=> leaf; eapply valid_bind.
  + apply (cp_chains_valid (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint
    U8 sp.2))
      L 0 (fixed_digits leaf)).
  + move=> [sg ends]; ssprove_valid.
Qed.

Lemma r_compress_batch_valid L sp sd :
  ValidCode L (I_SMTCR shrincs_thf) (r_compress_batch sp sd).
Proof.
rewrite /r_compress_batch.
elim: (shrincs_fxmss_schedule sp) => [|a ats ih].
- exact: valid_ret.
- cbn [query_list].
  eapply valid_bind; first exact: r_compress_one_valid.
  move=> entry; eapply valid_bind; first exact: ih.
  move=> entries; exact: valid_ret.
Qed.

#[export] Instance r_compress_gen_valid sp sd :
  ValidCode prepared_leaf_locs (I_SMTCR shrincs_thf) (r_compress_gen sp sd).
Proof.
rewrite /r_compress_gen.
ssprove_valid.
exact: r_compress_batch_valid.
Qed.

#[export] Instance r_compress_check_valid q :
  ValidCode prepared_leaf_locs (I_SMTCR shrincs_thf) (r_compress_check q).
Proof.
rewrite /r_compress_check; ssprove_valid.
Qed.

#[local] Arguments r_compress_gen : simpl never.
#[local] Arguments r_compress_check : simpl never.

Definition R_compress : package (I_SMTCR shrincs_thf) I_known_message :=
  [package prepared_leaf_locs;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      '(sp, sd) {
      r_compress_gen sp sd
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      prepared_leaf_sign j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      r_compress_check q
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      call [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } q
    }
  ].

Lemma resolve_r_compress_eval q :
  resolve (R_compress)
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    (call [ EVAL ] : { leaf_opening_eval_input ~> bytes 16 } q).
Proof. by rewrite /R_compress /resolve /= coerce_kleisliE. Qed.

Lemma resolve_r_compress_gen sp sd :
  resolve R_compress (known_message_gen, (shrincs_fxmss_structure ×
    shrincs_fxmss_digest_table,
    leaf_opening_public)) (sp, sd) =
  r_compress_gen sp sd.
Proof.
by rewrite /R_compress /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_r_compress_check q :
  resolve R_compress (known_message_check, (leaf_opening_opening, 'bool)) q =
    r_compress_check q.
Proof.
by rewrite /R_compress /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_r_compress_sign j :
  resolve R_compress (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    prepared_leaf_sign j.
Proof.
by rewrite /R_compress /resolve /= coerce_kleisliE.
Qed.

Lemma r_compress_real_check_decision sp pp a md entry mw :
  (if prepared_leaf_verdict 1 sp pp a md entry mw &&
       (prepared_leaf_forged_ends sp pp a mw != entry.1.2)
   then (r_compress_encode (prepared_leaf_forged_ends sp pp a mw) != r_compress_encode
     entry.1.2) &&
     (th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a)
       (r_compress_encode (prepared_leaf_forged_ends sp pp a mw)) ==
      th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a) (r_compress_encode entry.1.2))
   else prepared_leaf_verdict 1 sp pp a md entry mw) =
  prepared_leaf_verdict 1 sp pp a md entry mw.
Proof.
apply: r_compress_check_real.
exact: prepared_leaf_verdict_collision.
Qed.

Lemma r_compress_ideal_check_decision sp pp a md entry mw :
  (if prepared_leaf_verdict 1 sp pp a md entry mw &&
       (prepared_leaf_forged_ends sp pp a mw != entry.1.2)
   then false else prepared_leaf_verdict 1 sp pp a md entry mw) =
  prepared_leaf_verdict 2 sp pp a md entry mw.
Proof.
by rewrite r_compress_check_ideal prepared_leaf_verdict_ideal.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Compression state *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition r_compress_private : Locations :=
  [fmap prepared_leaf_pp_loc; tcr_pp_loc shrincs_thf; tcr_tgts_loc shrincs_thf;
    tcr_tws_loc shrincs_thf; tcr_rev_loc].
Definition r_compress_block (pp : bytes 16) (rv : bool) (tw : seq tweak)
    (tg : chMap 'nat (tweak × 'list ('word U8))) : precond :=
  fun '(h0, h1) => heap_ignore r_compress_private (h0, h1) /\
    get_heap h0 prepared_leaf_pp_loc = Some pp /\
    get_heap h1 (tcr_pp_loc shrincs_thf) = Some pp /\
    get_heap h1 tcr_rev_loc = rv /\
    get_heap h1 (tcr_tws_loc shrincs_thf) = tw /\
    get_heap h1 (tcr_tgts_loc shrincs_thf) = tg.

Lemma r_compress_block_targets pp rv tw tg tg' h0 h1 :
  r_compress_block pp rv tw tg (h0, h1) ->
  r_compress_block pp rv tw tg'
    (h0, set_heap h1 (tcr_tgts_loc shrincs_thf) tg').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_compress_private; fmap_solve.
- (* Only the target table changes; seeds, reveal flag and tweaks agree. *)
  split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  exact: get_set_heap_eq.
Qed.

Lemma r_compress_block_tweaks pp rv tw tg tw' h0 h1 :
  r_compress_block pp rv tw tg (h0, h1) ->
  r_compress_block pp rv tw' tg
    (h0, set_heap h1 (tcr_tws_loc shrincs_thf) tw').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_compress_private; fmap_solve.
- (* Only the tweak list changes; the other recorded values agree. *)
  split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  split; first exact: get_set_heap_eq.
  by rewrite get_set_heap_neq.
Qed.

Lemma r_compress_block_reveal pp rv tw tg rv' h0 h1 :
  r_compress_block pp rv tw tg (h0, h1) ->
  r_compress_block pp rv' tw tg (h0, set_heap h1 tcr_rev_loc rv').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_compress_private; fmap_solve.
- split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first exact: get_set_heap_eq.
  split; by rewrite get_set_heap_neq.
Qed.

Lemma r_compress_resolve_target_class (cl : pred tweak) p b t m :
  resolve (SMTCR_game shrincs_thf cl p b)
    (TQUERY, (tweak × 'list ('word U8), bytes 16)) (t, m) =
  (#assert cl t ;;
   revealed ← get tcr_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get (tcr_tws_loc shrincs_thf) ;;
   #assert size tws < p ;;
   #assert t \notin tws ;;
   tgts ← get (tcr_tgts_loc shrincs_thf) ;;
   #put (tcr_tgts_loc shrincs_thf) := setm tgts (size tws) (t, m) ;;
   #put (tcr_tws_loc shrincs_thf) := rcons tws t ;;
   ppo ← get (tcr_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp t m)).
Proof.
by rewrite /SMTCR_game /resolve /= coerce_kleisliE.
Qed.

Lemma r_compress_resolve_target p b t m :
  resolve (SMTCR_game shrincs_thf wots_c_pk_class p b)
    (TQUERY, (tweak × 'list ('word U8), bytes 16)) (t, m) =
  (#assert wots_c_pk_class t ;;
   revealed ← get tcr_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get (tcr_tws_loc shrincs_thf) ;;
   #assert size tws < p ;;
   #assert t \notin tws ;;
   tgts ← get (tcr_tgts_loc shrincs_thf) ;;
   #put (tcr_tgts_loc shrincs_thf) := setm tgts (size tws) (t, m) ;;
   #put (tcr_tws_loc shrincs_thf) := rcons tws t ;;
   ppo ← get (tcr_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp t m)).
Proof. exact: (r_compress_resolve_target_class wots_c_pk_class). Qed.

Lemma r_compress_target_spec_class (cl : pred tweak) p b {B : choiceType} pp tw tg t m
    (c0 : raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  cl t -> size tw < p -> t \notin tw ->
  ⊢ ⦃ fun '(h0, h1) =>
    r_compress_block pp false (rcons tw t) (setm tg (size tw) (t, m)) (h0, h1) ⦄
    c0 ≈ k1 (Th pp t m) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf cl p b)
      (TQUERY, (tweak × 'list ('word U8), bytes 16)) (t, m)) k1 ⦃ post ⦄.
Proof.
move=> hcl hbudget hfresh hk.
rewrite r_compress_resolve_target_class.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs tcr_rev_loc false); first by move=> h0 h1 [_ [_ [_ [hr _]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs (tcr_tws_loc shrincs_thf) tw); first by move=> h0 h1 [_ [_ [_ [_ [ht _]]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs (tcr_tgts_loc shrincs_thf) tg); first by move=> h0 h1 [_ [_ [_ [_ [_ ht]]]]].
cbv beta iota.
eapply (r_put_bind_rhs (tcr_tgts_loc shrincs_thf) (setm tg (size tw) (t, m)) _
  (r_compress_block pp false tw (setm tg (size tw) (t, m)))).
- move=> h0 h1 hp.
exact: r_compress_block_targets hp.
- eapply (r_put_bind_rhs (tcr_tws_loc shrincs_thf) (rcons tw t) _ (r_compress_block pp
  false (rcons tw t) (setm tg (size tw) (t, m)))).
+ move=> h0 h1 hp.
exact: r_compress_block_tweaks hp.
+ eapply (r_get_bind_rhs (tcr_pp_loc shrincs_thf) (Some pp)); first by move=> h0 h1 [_ [_ [hr _]]].
cbv beta iota.
exact: hk.
Qed.

Lemma r_compress_target_spec p b {B : choiceType} pp tw tg t m
    (c0 : raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  wots_c_pk_class t -> size tw < p -> t \notin tw ->
  ⊢ ⦃ fun '(h0, h1) =>
    r_compress_block pp false (rcons tw t) (setm tg (size tw) (t, m)) (h0, h1) ⦄
    c0 ≈ k1 (Th pp t m) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp false tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf wots_c_pk_class p b)
      (TQUERY, (tweak × 'list ('word U8), bytes 16)) (t, m)) k1 ⦃ post ⦄.
Proof. exact: (r_compress_target_spec_class wots_c_pk_class). Qed.

Lemma r_compress_resolve_reveal_class (cl : pred tweak) p b :
  resolve (SMTCR_game shrincs_thf cl p b)
    (GETPP, ('unit, bytes 16)) tt =
  (ppo ← get (tcr_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   #put tcr_rev_loc := true ;;
   ret pp).
Proof.
by rewrite /SMTCR_game /resolve /= coerce_kleisliE.
Qed.

Lemma r_compress_resolve_reveal p b :
  resolve (SMTCR_game shrincs_thf wots_c_pk_class p b)
    (GETPP, ('unit, bytes 16)) tt =
  (ppo ← get (tcr_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   #put tcr_rev_loc := true ;;
   ret pp).
Proof. exact: (r_compress_resolve_reveal_class wots_c_pk_class). Qed.

Lemma r_compress_reveal_spec_class (cl : pred tweak) p b {B : choiceType} pp rv tw tg
    (c0 : raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true tw tg (h0, h1) ⦄
    c0 ≈ k1 pp ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp rv tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf cl p b)
      (GETPP, ('unit, bytes 16)) tt) k1 ⦃ post ⦄.
Proof.
move=> hk.
rewrite r_compress_resolve_reveal_class.
eapply (r_get_bind_rhs (tcr_pp_loc shrincs_thf) (Some pp));
  first by move=> h0 h1 [_ [_ [hr _]]].
cbv beta iota.
eapply (r_put_bind_rhs tcr_rev_loc true _ (r_compress_block pp true tw tg)).
- move=> h0 h1 hp.
exact: r_compress_block_reveal hp.
- exact: hk.
Qed.

Lemma r_compress_reveal_spec p b {B : choiceType} pp rv tw tg
    (c0 : raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true tw tg (h0, h1) ⦄
    c0 ≈ k1 pp ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp rv tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf wots_c_pk_class p b)
      (GETPP, ('unit, bytes 16)) tt) k1 ⦃ post ⦄.
Proof. exact: (r_compress_reveal_spec_class wots_c_pk_class). Qed.

Lemma r_compress_resolve_check_class (cl : pred tweak) p b j m :
  resolve (SMTCR_game shrincs_thf cl p b)
    (CHECK, ('nat × 'list ('word U8), 'bool)) (j, m) =
  (revealed ← get tcr_rev_loc ;;
   #assert revealed ;;
   if b then
     tgts ← get (tcr_tgts_loc shrincs_thf) ;;
     match getm tgts j with
     | Some (t0, m0) =>
       ppo ← get (tcr_pp_loc shrincs_thf) ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dBytes 16 ;;
                      #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
            end ;;
       ret ((m != m0) && (Th pp t0 m == Th pp t0 m0))
     | None => ret false
     end
   else ret false).
Proof.
by rewrite /SMTCR_game /resolve /= coerce_kleisliE.
Qed.

Lemma r_compress_resolve_check p b j m :
  resolve (SMTCR_game shrincs_thf wots_c_pk_class p b)
    (CHECK, ('nat × 'list ('word U8), 'bool)) (j, m) =
  (revealed ← get tcr_rev_loc ;;
   #assert revealed ;;
   if b then
     tgts ← get (tcr_tgts_loc shrincs_thf) ;;
     match getm tgts j with
     | Some (t0, m0) =>
       ppo ← get (tcr_pp_loc shrincs_thf) ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dBytes 16 ;;
                      #put (tcr_pp_loc shrincs_thf) := Some pp ;; ret pp
            end ;;
       ret ((m != m0) && (Th pp t0 m == Th pp t0 m0))
     | None => ret false
     end
   else ret false).
Proof. exact: (r_compress_resolve_check_class wots_c_pk_class). Qed.

Local Opaque dBytes r_compress_block Th.
Lemma r_compress_check_spec_class (cl : pred tweak) p b {B : choiceType} pp tw tg j t m0
  m
    (c0 : raw_code B) (k1 : bool -> raw_code B) (post : postcond B B) :
  getm tg j = Some (t, m0) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true tw tg (h0, h1) ⦄
    c0 ≈ k1 (b && (m != m0) && (Th pp t m == Th pp t m0)) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf cl p b)
      (CHECK, ('nat × 'list ('word U8), 'bool)) (j, m)) k1 ⦃ post ⦄.
Proof.
move=> ht hk.
rewrite r_compress_resolve_check_class.
eapply (r_get_bind_rhs tcr_rev_loc true); first by move=> h0 h1 [_ [_ [_ [hr _]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
case: b hk => hk; cbv beta iota in hk |- *; last exact: hk.
eapply (r_get_bind_rhs (tcr_tgts_loc shrincs_thf) tg); first by move=> h0 h1 [_ [_ [_ [_ [_ ht']]]]].
cbv beta iota.
rewrite ht.
eapply (r_get_bind_rhs (tcr_pp_loc shrincs_thf) (Some pp)); first by move=> h0 h1 [_ [_ [hr _]]].
cbv beta iota.
exact: hk.
Qed.

Lemma r_compress_check_spec p b {B : choiceType} pp tw tg j t m0 m
    (c0 : raw_code B) (k1 : bool -> raw_code B) (post : postcond B B) :
  getm tg j = Some (t, m0) ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true tw tg (h0, h1) ⦄
    c0 ≈ k1 (b && (m != m0) && (Th pp t m == Th pp t m0)) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_compress_block pp true tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMTCR_game shrincs_thf wots_c_pk_class p b)
      (CHECK, ('nat × 'list ('word U8), 'bool)) (j, m)) k1 ⦃ post ⦄.
Proof. exact: (r_compress_check_spec_class wots_c_pk_class). Qed.
