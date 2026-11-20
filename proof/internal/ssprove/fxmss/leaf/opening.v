(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.opening

    Batch multi-instance leaf openings over the operational FXMSS model.
    GEN commits every leaf of the chosen legal shape before releasing the
    seed or any root. The evaluator uses the single packed-tweak Th.
    These are internal experiments, not primitive hardness assumptions. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.sample_seq.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import params scheme.
From Shrincs.internal.ssprove.fxmss Require Import params shape games scheme leaf.paths.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_pk (P : shrincs_fxmss_params) (sp : shrincs_fxmss_structure) pp a xs :=
  shrincs_fxmss_leaf_pubkey P a sp.1 (uint U8 sp.2) pp xs.
Definition leaf_sign_at (P : shrincs_fxmss_params) (sp : shrincs_fxmss_structure) pp a
  xs md :=
  shrincs_fxmss_leaf_sign P a sp.1 (uint U8 sp.2) pp xs md.
Definition leaf_recover (P : shrincs_fxmss_params) (sp : shrincs_fxmss_structure) pp a
  md sg :=
  shrincs_fxmss_leaf_recover P a sp.1 (uint U8 sp.2) pp md sg.
Definition leaf_win P sp pp a md sg xs :=
  leaf_recover P sp pp a md sg == Some (leaf_pk P sp pp a xs).

Lemma leaf_win_verify P sp pp a md sg xs :
  leaf_win P sp pp a md sg xs =
  shrincs_wots_verify (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) pp
    (leaf_pk P sp pp a xs) md
    (wcp_sig_decode (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) sg).
Proof. exact: shrincs_fxmss_leaf_recover_verify. Qed.

Lemma leaf_sign_failed P sp pp a xs md :
  find_counter (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) pp md = None ->
  leaf_sign_at P sp pp a xs md = None.
Proof. exact: shrincs_fxmss_leaf_sign_none. Qed.

(* Operation and location identifiers occupy 1500..1599. *)
Definition leaf_opening_gen : nat := 1500.
Definition leaf_opening_sign : nat := 1501.
Definition leaf_opening_check : nat := 1502.
Definition leaf_opening_eval : nat := 1503.

Definition leaf_opening_public : choice_type := bytes 16 × 'list (bytes 16).
Definition leaf_opening_signature : choice_type := bytes (2 + WOTS_C_CHAINS_SIZE).
Definition leaf_opening_eval_input : choice_type := tweak × 'list ('word U8).
Definition leaf_opening_opening : choice_type := 'nat × (bytes 32 ×
  leaf_opening_signature).
Definition leaf_opening_state : choice_type := bytes 16 × shrincs_fxmss_structure.

Definition leaf_opening_st_loc := mkloc 1500 (None : option leaf_opening_state).
Definition leaf_opening_pp_loc := mkloc 1501 (None : option (bytes 16)).
Definition leaf_opening_keys_loc := mkloc 1502 (emptym : shrincs_fxmss_key_table).
Definition leaf_opening_slog_loc := mkloc 1503 ([::] : seq nat).
Definition leaf_opening_locs : Locations :=
  [fmap leaf_opening_st_loc; leaf_opening_pp_loc; leaf_opening_keys_loc;
    leaf_opening_slog_loc].

Definition I_leaf_opening :=
  [interface
    [ leaf_opening_gen ] : { shrincs_fxmss_structure ~> leaf_opening_public };
    [ leaf_opening_sign ] : { 'nat × bytes 32 ~> 'option leaf_opening_signature };
    [ leaf_opening_check ] : { leaf_opening_opening ~> 'bool };
    [ leaf_opening_eval ] : { leaf_opening_eval_input ~> bytes 16 }
  ].

Definition leaf_opening_seed (P : shrincs_fxmss_params) : raw_code (bytes 16) :=
  ppo ← get leaf_opening_pp_loc ;;
  match ppo with
  | Some pp => ret pp
  | None => pp ← shrincs_fxmss_public_seed_dist P ;; #put leaf_opening_pp_loc := Some pp
    ;; ret
    pp
  end.

#[export] Instance leaf_opening_seed_valid P I : ValidCode leaf_opening_locs I
  (leaf_opening_seed P).
Proof.
rewrite /leaf_opening_seed.
ssprove_valid.
Qed.

Definition leaf_opening_roots P sp pp (kt : shrincs_fxmss_key_table) : seq (bytes 16) :=
  [seq leaf_pk P sp pp a (odflt [::] (getm kt a)) | a <- shrincs_fxmss_schedule sp].

Definition leaf_opening_gen_body P (sp : shrincs_fxmss_structure) : raw_code
  leaf_opening_public :=
  sto ← get leaf_opening_st_loc ;;
  #assert ~~ isSome sto ;;
  #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
  pp ← leaf_opening_seed P ;;
  kt ← shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule sp) ;;
  #put leaf_opening_st_loc := Some (pp, sp) ;;
  #put leaf_opening_keys_loc := kt ;;
  ret (pp, leaf_opening_roots P sp pp kt).

Definition leaf_opening_sign_body P (q : nat * bytes 32) :
    raw_code ('option leaf_opening_signature) :=
  st ← getSome leaf_opening_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  slog ← get leaf_opening_slog_loc ;;
  #assert q.1 \notin slog ;;
  #put leaf_opening_slog_loc := q.1 :: slog ;;
  kt ← get leaf_opening_keys_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  ret (leaf_sign_at P st.2 st.1 a (odflt [::] (getm kt a)) q.2).

Definition leaf_opening_check_body P (q : leaf_opening_opening) : raw_code 'bool :=
  st ← getSome leaf_opening_st_loc ;;
  #assert q.1 < size (shrincs_fxmss_schedule st.2) ;;
  kt ← get leaf_opening_keys_loc ;;
  let a := leaf_coord_at st.2 q.1 in
  ret (leaf_win P st.2 st.1 a q.2.1 q.2.2 (odflt [::] (getm kt a))).

#[export] Instance leaf_opening_gen_valid P I sp :
  ValidCode leaf_opening_locs I (leaf_opening_gen_body P sp).
Proof.
rewrite /leaf_opening_gen_body.
ssprove_valid;
  typeclasses eauto.
Qed.

#[export] Instance leaf_opening_sign_valid P I q :
  ValidCode leaf_opening_locs I (leaf_opening_sign_body P q).
Proof. rewrite /leaf_opening_sign_body; ssprove_valid. Qed.

#[export] Instance leaf_opening_check_valid P I q :
  ValidCode leaf_opening_locs I (leaf_opening_check_body P q).
Proof. rewrite /leaf_opening_check_body; ssprove_valid. Qed.

Definition G_leaf_opening P (bit : bool) : game I_leaf_opening :=
  [package leaf_opening_locs;
    [ leaf_opening_gen ] : { shrincs_fxmss_structure ~> leaf_opening_public } (sp) {
      leaf_opening_gen_body P sp
    };
    [ leaf_opening_sign ] : { 'nat × bytes 32 ~> 'option leaf_opening_signature } (q) {
      leaf_opening_sign_body P q
    };
    [ leaf_opening_check ] : { leaf_opening_opening ~> 'bool } (q) {
      verdict ← leaf_opening_check_body P q ;;
      ret (bit && verdict)
    };
    [ leaf_opening_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      pp ← leaf_opening_seed P ;;
      ret (shrincs_fxmss_hash_eval P pp q.1 q.2)
    }
  ].

Lemma resolve_leaf_opening_check P bit q :
  resolve (G_leaf_opening P bit) (leaf_opening_check, (leaf_opening_opening, 'bool)) q =
    (verdict ← leaf_opening_check_body P q ;; ret (bit && verdict)).
Proof. by rewrite /G_leaf_opening /resolve /= coerce_kleisliE. Qed.

Lemma leaf_opening_roots_length P sp pp kt :
  size (leaf_opening_roots P sp pp kt) = size (shrincs_fxmss_schedule sp).
Proof. exact: size_map. Qed.
