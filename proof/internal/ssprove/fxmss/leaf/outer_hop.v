(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.outer_hop

    Generation and the oracle simulations give the exact outer leaf-context hop. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance scheme tree.forgery tree.nodes tree.encoding tree.model
  leaf.opening leaf.commitments leaf.known_message_game leaf.known_message leaf.context
  leaf.outer_state paired.reduction leaf.outer_sign leaf.outer_forge.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context gen *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Lemma leaf_outer_lookup_keys_random P st k kt :
  shrincs_fxmss_lookup_keys P true st k kt =
    (fun a => odflt [::] (getm kt a)).
Proof. by []. Qed.

Lemma leaf_outer_inv_invariant :
  Invariant shrincs_fxmss_locs (unionm leaf_ctx_locs known_message_locs)
    leaf_outer_inv.
Proof.
rewrite /leaf_outer_inv.
ssprove_invariant => //.
Qed.

Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel known_message_cache
  leaf_opening_roots
  shrincs_fxmss_node shrincs_fxmss_lookup_keys shrincs_fxmss_sample_keys
    shrincs_fxmss_sample_digests
  shrincs_fxmss_sign shrincs_fxmss_select_leaf shrincs_fxmss_message_valid
    shrincs_fxmss_full_forge_body
  leaf_ctx_auth leaf_ctx_tree known_message_coll_filter G_known_message.

Definition leaf_outer_finish_left (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) : raw_code (bytes
      48) :=
  #put shrincs_fxmss_st_loc := Some st ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_keys_loc := kt ;;
  #put shrincs_fxmss_sd_loc := sd ;;
  ret [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2].

Definition leaf_outer_finish_right (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) : raw_code (bytes
      48) :=
  #put leaf_opening_st_loc := Some (st.1.1.1,st.2) ;;
  #put leaf_opening_keys_loc := kt ;;
  #put known_message_sd_loc := sd ;;
  #put known_message_cache_loc := known_message_cache shrincs_fxmss_sha256 st.2 st.1.1.1
    sd kt ;;
  #put shrincs_fxmss_st_loc := Some st ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_sd_loc := sd ;;
  #put leaf_ctx_roots_loc := leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1 kt ;;
  ret [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2].

Lemma leaf_outer_finish_sim st ks kp kt sd :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  st.1.2 = shrincs_fxmss_honest_node shrincs_fxmss_sha256 (fun a => odflt [::] (getm kt
    a))
    st.1.1.1 st.2.1 st.2.2 255 0%Z ->
  leaf_digest_total (shrincs_fxmss_schedule st.2) sd ->
  ⊢ ⦃ λ '(h0,h1), leaf_outer_init (Some st.1.1.1) (h0,h1) ⦄
    leaf_outer_finish_left st ks kp kt sd ≈ leaf_outer_finish_right st ks kp kt sd
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
move=> hd hr hsd.
rewrite /leaf_outer_finish_left /leaf_outer_finish_right.
eapply r_put_lhs with (pre := leaf_outer_init (Some st.1.1.1)).
do 4 eapply r_put_lhs.
do 9 eapply r_put_rhs.
apply: r_ret=> h0 h1 hh.
do 14 (case: hh => ? [hh ->]).
split; first by [].
exact: leaf_outer_store_inv hd hr hsd hh.
Qed.

Lemma leaf_outer_sample_digests P as_ (B : choiceType) (pre : precond)
    (post : postcond B B) (k0 k1 : shrincs_fxmss_digest_table -> raw_code B) :
  (forall sd, leaf_digest_total as_ sd -> ⊢ ⦃ pre ⦄ k0 sd ≈ k1 sd ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄ sd ← shrincs_fxmss_sample_digests P as_ ;; k0 sd ≈
    sd ← shrincs_fxmss_sample_digests P as_ ;; k1 sd ⦃ post ⦄.
Proof.
elim: as_ k0 k1 => [|a as_ ih] k0 k1 hk.
- cbn [shrincs_fxmss_sample_digests bind]; exact: hk isT.
- (* The sampled head digest preserves totality of the full table. *)
  cbn [shrincs_fxmss_sample_digests].
  rewrite !bind_assoc.
  eapply (r_scheme_bind (shrincs_fxmss_digest_dist P)); first exact: prog_valid.
  move=> md.
  rewrite !bind_assoc.
  apply: ih=> sd hsd.
  apply: hk; exact: leaf_digest_total_set hsd.
Qed.

Lemma leaf_outer_gen_sim Q keep bit setup :
  ⊢ ⦃ λ '(h0,h1), leaf_outer_inv (h0,h1) ⦄
    resolve (G_forge_full_signature shrincs_fxmss_sha256 Q keep bit)
      (shrincs_fxmss_op_gen,
      (shrincs_fxmss_setup, bytes 48)) setup
    ≈ code_link (leaf_ctx_gen setup)
      (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
have hsync : ProvenBy (syncs shrincs_fxmss_st_loc) leaf_outer_inv.
  move=> [h0 h1] hi.
  apply: (leaf_outer_inv_get shrincs_fxmss_st_loc _ h0 h1 hi).
  by rewrite /leaf_outer_private; fmap_solve.
rewrite leaf_outer_full_genE /leaf_outer_full_gen.
rewrite /leaf_ctx_gen.
cbn [code_link].
eapply (@r_get_vs_get_remember_rhs _ _ _ _ _ _ _ hsync).
move=> sto; case: sto => [st|].
- simpl; exact: r_fail.
- cbn [isSome negb assertD bind code_link].
  have hsync_done : ProvenBy (syncs shrincs_fxmss_done_loc)
      (leaf_outer_inv ⋊ rem_rhs shrincs_fxmss_st_loc None).
    move=> [h0 h1] [hi _].
    apply: (leaf_outer_inv_get shrincs_fxmss_done_loc _ h0 h1 hi).
    by rewrite /leaf_outer_private; fmap_solve.
  eapply (@r_get_vs_get_remember_rhs _ _ _ _ _ _ _ hsync_done).
  move=> done; case: done.
  + simpl; exact: r_fail.
  + cbn [negb assertD bind code_link].
    case hlegal: (shrincs_fxmss_structure_legal setup.1.1 setup.1.2); last first.
    * simpl; exact: r_fail.
    * cbn [assertD bind code_link].
      eapply rpre_weaken_rule with (pre := leaf_outer_init None); last first.
      -- move=> h0 h1 [[hi hs] _]; exact: leaf_outer_init_from_inv hi hs.
      -- match goal with
         | |- @rel_jdg ?A ?B ?pre ?post ?c0 (?f ?T ?c ?g) =>
           change (@rel_jdg A B pre post c0 (@code_link T c g))
         end.
         rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid
           (shrincs_fxmss_secret_dist shrincs_fxmss_sha256))).
         eapply r_transL.
         ++ eapply (r_swap_scheme_scheme (shrincs_fxmss_secret_dist
           shrincs_fxmss_sha256) (shrincs_fxmss_public_seed_dist shrincs_fxmss_sha256));
           exact: prog_valid.
         ++ eapply (r_scheme_bind (shrincs_fxmss_secret_dist shrincs_fxmss_sha256));
           first exact: prog_valid.
            move=> ks.
            rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid
              (shrincs_fxmss_secret_dist shrincs_fxmss_sha256))).
            eapply r_transL.
            ** eapply (r_swap_scheme_scheme (shrincs_fxmss_secret_dist
              shrincs_fxmss_sha256) (shrincs_fxmss_public_seed_dist
              shrincs_fxmss_sha256)); exact: prog_valid.
            ** eapply (r_scheme_bind (shrincs_fxmss_secret_dist shrincs_fxmss_sha256));
              first exact: prog_valid.
               move=> kp.
               rewrite code_link_bind (code_link_scheme _ _ _ _
                 (shrincs_fxmss_sample_digests_valid shrincs_fxmss_sha256 emptym
                   [interface] (shrincs_fxmss_schedule setup.1))).
               eapply r_transL.
               --- (* Digest and key sampling commute after the public seed. *)
                   eapply rsame_head=> pp.
                   eapply (r_swap_scheme_scheme
                     (shrincs_fxmss_sample_digests shrincs_fxmss_sha256
                       (shrincs_fxmss_schedule setup.1))
                     (shrincs_fxmss_sample_keys shrincs_fxmss_sha256
                       (shrincs_fxmss_schedule setup.1)));
                     first exact: shrincs_fxmss_sample_digests_valid.
                   exact: shrincs_fxmss_sample_keys_valid.
               --- eapply r_transL.
                   +++ (* Digest sampling commutes with public-seed sampling. *)
                       eapply (r_swap_scheme_scheme
                         (shrincs_fxmss_sample_digests shrincs_fxmss_sha256
                           (shrincs_fxmss_schedule setup.1))
                         (shrincs_fxmss_public_seed_dist shrincs_fxmss_sha256)); first
                           exact: shrincs_fxmss_sample_digests_valid.
                       exact: prog_valid.
                   +++ eapply leaf_outer_sample_digests=> sd hsd.
                       cbn [code_link].
                       rewrite leaf_outer_resolve_gen /known_message_gen_body.
                       cbn [bind].
                       eapply (r_get_rhs_pin leaf_opening_st_loc None (leaf_outer_init
                         None)).
                       { by move=> h0 h1 [_ _ _ hm _]. }
                       cbn [bind isSome negb assertD].
                       rewrite hlegal hsd.
                       cbn [bind assertD].
                       rewrite (bind_assoc (leaf_opening_seed shrincs_fxmss_sha256))
                         /leaf_opening_seed.
                       cbn [bind].
                       eapply (r_get_rhs_pin leaf_opening_pp_loc None).
                       { by move=> h0 h1 [_ _ _ _ hp]. }
                       cbn [bind].
                       set dPP := shrincs_fxmss_public_seed_dist shrincs_fxmss_sha256.
                       have hdPP : ValidCode emptym [interface] dPP := prog_valid
                         (shrincs_fxmss_public_seed_dist shrincs_fxmss_sha256).
                       clearbody dPP.
                       rewrite !bind_assoc.
                       eapply (r_scheme_bind dPP); first exact hdPP.
                       move=> pp.
                       cbn [bind].
                       eapply r_put_rhs_weak with (pre' := leaf_outer_init (Some pp)).
                       { move=> h0 h1 hi; exact: leaf_outer_init_seed h0 h1 pp hi. }
                       rewrite (bind_assoc (shrincs_fxmss_sample_keys
                         shrincs_fxmss_sha256 (shrincs_fxmss_schedule setup.1))).
                       eapply (r_scheme_bind (shrincs_fxmss_sample_keys
                         shrincs_fxmss_sha256 (shrincs_fxmss_schedule setup.1)));
                         first exact: shrincs_fxmss_sample_keys_valid.
                       move=> kt.
                       rewrite leaf_outer_lookup_keys_random (leaf_batch_tree_honest
                         shrincs_fxmss_sha256 setup.1 pp kt hlegal).
                       cbn [isSome assertD bind odflt].
                       set st := ((pp,setup.2,leaf_batch_tree shrincs_fxmss_sha256 pp
                         setup.1
                         (leaf_opening_roots shrincs_fxmss_sha256 setup.1 pp
                           kt)),setup.1).
                       change (⊢ ⦃ leaf_outer_init (Some pp) ⦄
                         leaf_outer_finish_left st ks kp kt sd ≈
                         leaf_outer_finish_right st ks kp kt sd
                         ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄).
                       apply: (leaf_outer_finish_sim st ks kp kt sd).
                       *** exact hlegal.
                       *** rewrite /st /shrincs_fxmss_honest_node.
                           by rewrite (leaf_batch_tree_honest shrincs_fxmss_sha256
                             setup.1 pp kt hlegal).
                       *** exact hsd.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context hop *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma leaf_outer_resolve_hash Q arg :
  resolve (G_forge_full_signature shrincs_fxmss_sha256 Q
    (keep_paired_free shrincs_fxmss_sha256) true)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg =
      leaf_ctx_hash Q arg.
Proof. by rewrite /G_forge_full_signature /resolve /= coerce_kleisliE. Qed.

Lemma leaf_outer_hash_valid Q arg :
  ValidCode leaf_ctx_locs [interface] (leaf_ctx_hash Q arg).
Proof.
rewrite /leaf_ctx_hash; ssprove_valid.
exact: leaf_ctx_lookup_valid.
Qed.

Local Opaque leaf_outer_inv leaf_outer_rel shrincs_fxmss_sha256
  leaf_ctx_gen leaf_ctx_sign leaf_ctx_hash leaf_ctx_forge
  shrincs_fxmss_full_forge_body known_message_coll_filter G_known_message.

Lemma leaf_outer_perfect Q :
  perfect I_forge (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
    shrincs_fxmss_sha256)
    true)
    (R_known_message Q ∘ known_message_coll_filter ∘ G_known_message
      shrincs_fxmss_sha256 true).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ leaf_outer_inv).
- exact: leaf_outer_inv_invariant.
- move=> id S T arg has.
  fmap_invert has.
  + rewrite !resolve_link /R_known_message /resolve /= !coerce_kleisliE.
    have hgen := leaf_outer_gen_sim Q (keep_paired_free shrincs_fxmss_sha256) true arg.
    rewrite /G_forge_full_signature /resolve /= coerce_kleisliE in hgen.
    exact hgen.
  + (* SIGN agrees with the leaf-context simulation. *)
    have hr : resolve (R_known_message Q) (shrincs_fxmss_op_sign,
    (shrincs_fxmss_message,
    'option shrincs_fxmss_bytes)) arg =
        leaf_ctx_sign Q arg by rewrite /R_known_message /resolve /= coerce_kleisliE.
    rewrite !resolve_link hr.
    exact: (leaf_outer_sign_sim Q (keep_paired_free shrincs_fxmss_sha256) true arg).
  + (* HASH preserves the outer relation and returns the same digest. *)
    have hr : resolve (R_known_message Q) (shrincs_fxmss_op_hash,
    (shrincs_fxmss_hmsg_input,
    'option (bytes 32))) arg =
        leaf_ctx_hash Q arg by rewrite /R_known_message /resolve /= coerce_kleisliE.
    have hl : resolve (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
      shrincs_fxmss_sha256) true)
        (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg =
          leaf_ctx_hash Q arg.
    { exact: leaf_outer_resolve_hash. }
    have hv : ValidCode leaf_ctx_locs [interface] (leaf_ctx_hash Q arg).
    { exact: leaf_outer_hash_valid. }
    rewrite !resolve_link hr (code_link_scheme _ _ _ _ hv) -hl.
    apply: relational_rules.r_code_stable.
    exact: leaf_outer_hash_stable.
  + (* FORGE agrees with the leaf-context simulation. *)
    case: arg=> cm sg.
    have hr : resolve (R_known_message Q) (shrincs_fxmss_op_forge,
      (shrincs_fxmss_message ×
      shrincs_fxmss_bytes, 'bool)) (cm,sg) =
        leaf_ctx_forge cm sg by rewrite /R_known_message /resolve /= coerce_kleisliE.
    have hl : resolve (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
      shrincs_fxmss_sha256) true)
        (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool))
          (cm,sg) =
        shrincs_fxmss_full_forge_body shrincs_fxmss_sha256 (keep_paired_free
          shrincs_fxmss_sha256) cm sg.
    { by rewrite /G_forge_full_signature /resolve /= coerce_kleisliE bind_ret. }
    rewrite !resolve_link hr hl.
    exact: leaf_outer_forge_sim.
Qed.
