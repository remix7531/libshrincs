(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.known_message_game

    Known-message batch leaf experiment. GEN receives the complete digest
    table, samples every leaf key, and caches optional signatures before
    releasing the public seed and roots. Failed slots remain in the cache.
    The population gate depends on grinding success at commitment, not on
    which signatures the adversary requests. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import params scheme.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games scheme leaf.opening leaf.paths leaf.commitments.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition known_message_find P (sp : shrincs_fxmss_structure) pp a md :=
  find_counter (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) pp md.
Definition known_message_gate P sp pp a md dd :=
  (~~ isSome (known_message_find P sp pp a md) || (dd != md))%bool.

Definition known_message_cache P sp pp (sd : shrincs_fxmss_digest_table) (kt :
  shrincs_fxmss_key_table) :
    seq (option leaf_opening_signature) :=
  [seq leaf_sign_at P sp pp a (odflt [::] (getm kt a))
         (leaf_committed_digest sd a) | a <- shrincs_fxmss_schedule sp].

Definition known_message_gen : nat := 1510.
Definition known_message_sign : nat := 1511.
Definition known_message_check : nat := 1512.
Definition known_message_eval : nat := 1513.
Definition known_message_sd_loc := mkloc 1510 (emptym : shrincs_fxmss_digest_table).
Definition known_message_cache_loc := mkloc 1511 ([::] : seq (option
  leaf_opening_signature)).
Definition known_message_locs : Locations :=
  [fmap leaf_opening_st_loc; leaf_opening_pp_loc; leaf_opening_keys_loc;
    leaf_opening_slog_loc;
        known_message_sd_loc; known_message_cache_loc].

Definition I_known_message :=
  [interface
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 }
  ].

#[export] Instance known_message_seed_valid P I : ValidCode known_message_locs I
  (leaf_opening_seed P).
Proof. rewrite /leaf_opening_seed; ssprove_valid. Qed.

Definition known_message_gen_body P (sp : shrincs_fxmss_structure) (sd :
  shrincs_fxmss_digest_table) :
    raw_code leaf_opening_public :=
  sto ← get leaf_opening_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;;
  pp ← leaf_opening_seed P ;;
  kt ← shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule sp) ;;
  #put leaf_opening_st_loc := Some (pp, sp) ;;
  #put leaf_opening_keys_loc := kt ;;
  #put known_message_sd_loc := sd ;;
  #put known_message_cache_loc := known_message_cache P sp pp sd kt ;;
  ret (pp, leaf_opening_roots P sp pp kt).

Definition known_message_sign_body (j : nat) : raw_code ('option leaf_opening_signature)
  :=
  st ← getSome leaf_opening_st_loc ;;
  #assert j < size (shrincs_fxmss_schedule st.2) ;;
  slog ← get leaf_opening_slog_loc ;;
  #assert j \notin slog ;;
  #put leaf_opening_slog_loc := j :: slog ;;
  cache ← get known_message_cache_loc ;;
  ret (nth None cache j).

Definition known_message_check_body P (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome leaf_opening_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  kt ← get leaf_opening_keys_loc ;;
  sd ← get known_message_sd_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  ret (leaf_win P st.2 st.1 a q.2.1 q.2.2 (odflt [::] (getm kt a)) &&
    known_message_gate P st.2 st.1 a (leaf_committed_digest sd a) q.2.1).

#[export] Instance known_message_gen_valid P I sp sd :
  ValidCode known_message_locs I (known_message_gen_body P sp sd).
Proof.
rewrite /known_message_gen_body.
ssprove_valid;
  typeclasses eauto.
Qed.

#[export] Instance known_message_sign_valid I j : ValidCode known_message_locs I
  (known_message_sign_body j).
Proof. rewrite /known_message_sign_body; ssprove_valid. Qed.

#[export] Instance known_message_check_valid P I q :
  ValidCode known_message_locs I (known_message_check_body P q).
Proof. rewrite /known_message_check_body; ssprove_valid. Qed.

#[local] Arguments known_message_gen_body : simpl never.
#[local] Arguments known_message_sign_body : simpl never.
#[local] Arguments known_message_check_body : simpl never.

Definition G_known_message P (bit : bool) : game I_known_message :=
  [package known_message_locs;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      '(sp, sd) {
      known_message_gen_body P sp sd
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      known_message_sign_body j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      verdict ← known_message_check_body P q ;;
      ret (bit && verdict)
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      pp ← leaf_opening_seed P ;;
      ret (shrincs_fxmss_hash_eval P pp q.1 q.2)
    }
  ].

Lemma resolve_known_message_check P bit q :
  resolve (G_known_message P bit) (known_message_check, (leaf_opening_opening, 'bool)) q
    =
    (verdict ← known_message_check_body P q ;; ret (bit && verdict)).
Proof. by rewrite /G_known_message /resolve /= coerce_kleisliE. Qed.

Lemma known_message_cache_length P sp pp sd kt :
  size (known_message_cache P sp pp sd kt) = size (shrincs_fxmss_schedule sp).
Proof. exact: size_map. Qed.

Lemma known_message_cache_nth P sp pp sd kt j :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  j < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  nth None (known_message_cache P sp pp sd kt) j =
    leaf_sign_at P sp pp (leaf_coord_at sp j)
      (odflt [::] (getm kt (leaf_coord_at sp j)))
      (leaf_committed_digest sd (leaf_coord_at sp j)).
Proof.
move=> hsp hj.
rewrite /known_message_cache (nth_map (uint U8 0, uint U64 0))
  ?leaf_schedule_length //.
by rewrite leaf_schedule_nth.
Qed.

Lemma known_message_cache_failed P sp pp sd kt j :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  j < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  known_message_find P sp pp (leaf_coord_at sp j)
    (leaf_committed_digest sd (leaf_coord_at sp j)) = None ->
  nth None (known_message_cache P sp pp sd kt) j = None.
Proof.
move=> hsp hj hf.
rewrite (known_message_cache_nth P sp pp sd kt j hsp hj).
exact: leaf_sign_failed hf.
Qed.
