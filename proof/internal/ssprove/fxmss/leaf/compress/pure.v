(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.compress.pure

    Compression encodes arbitrary lists of sixteen-byte nodes, including empty
    lists. Compression oracle loops with an arbitrary static target budget and
    caller invariant. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules chain.core chain.ud.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.compress.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.paths leaf.known_message.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Compression pure *)

#[local] Open Scope nat_scope.

Definition r_compress_encode (xs : seq (bytes 16)) : seq UInt8 :=
  flatten [seq tval x | x <- xs].

Lemma r_compress_encode_inj : injective r_compress_encode.
Proof.
exact: (@flatten_rows_inj 16 isT).
Qed.

Lemma r_compress_encode_size xs : size (r_compress_encode xs) = size xs * 16.
Proof.
exact: flatten_rows_size.
Qed.

Lemma r_compress_encode_eq xs ys : (r_compress_encode xs == r_compress_encode ys) = (xs
  == ys).
Proof.
apply/eqP/eqP; first exact: r_compress_encode_inj.
by move=> ->.
Qed.

Definition r_compress_targets (sp : shrincs_fxmss_structure) :=
  [seq shrincs_fxmss_pk_tweak a | a <- shrincs_fxmss_schedule sp].

Lemma r_compress_targets_class sp : all wots_c_pk_class (r_compress_targets sp).
Proof.
apply/allP=> t /mapP[a ha ->].
exact: shrincs_fxmss_pk_tweak_class.
Qed.

Lemma r_compress_targets_uniq sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> uniq (r_compress_targets sp).
Proof.
move=> hsp.
rewrite /r_compress_targets (map_inj_uniq shrincs_fxmss_pk_tweak_inj).
exact: leaf_schedule_uniq.
Qed.

Lemma r_compress_targets_budget sp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> size (r_compress_targets sp) <= 2 ^ 64.
Proof.
move=> hsp.
rewrite /r_compress_targets size_map (leaf_schedule_length sp hsp).
exact: shrincs_fxmss_leaf_count_bound.
Qed.

Lemma r_compress_targets_fresh sp i :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  i < size (shrincs_fxmss_schedule sp) ->
  shrincs_fxmss_pk_tweak (leaf_coord_at sp i) \notin take i (r_compress_targets sp).
Proof.
move=> hsp hi.
have hu := r_compress_targets_uniq sp hsp.
have hn : nth (shrincs_fxmss_pk_tweak (uint U8 0, uint U64 0)) (r_compress_targets sp) i
  =
    shrincs_fxmss_pk_tweak (leaf_coord_at sp i).
{ rewrite /r_compress_targets (nth_map (uint U8 0, uint U64 0)) // leaf_schedule_nth //.
  by rewrite -(leaf_schedule_length sp hsp).
}
rewrite -hn.
have htake := take_uniq i.+1 hu.
rewrite (take_nth (shrincs_fxmss_pk_tweak (uint U8 0, uint U64 0))) in htake.
- by rewrite /r_compress_targets size_map.
- by move: htake; rewrite rcons_uniq => /andP[].
Qed.

Lemma r_compress_target_budget sp i :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  i < size (shrincs_fxmss_schedule sp) -> size (take i (r_compress_targets sp)) < 2 ^
    64.
Proof.
move=> hsp hi.
rewrite size_take /r_compress_targets size_map hi.
apply: leq_trans hi _.
by have := r_compress_targets_budget sp hsp; rewrite /r_compress_targets size_map.
Qed.

Lemma r_compress_target_advance sp i :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  i < size (shrincs_fxmss_schedule sp) ->
  rcons (take i (r_compress_targets sp)) (shrincs_fxmss_pk_tweak (leaf_coord_at sp i)) =
    take i.+1 (r_compress_targets sp).
Proof.
move=> hsp hi.
have ht : i < size (r_compress_targets sp) by rewrite /r_compress_targets size_map.
rewrite (take_nth (shrincs_fxmss_pk_tweak (uint U8 0, uint U64 0)) ht).
rewrite /r_compress_targets (nth_map (uint U8 0, uint U64 0)) // leaf_schedule_nth //.
by rewrite -(leaf_schedule_length sp hsp).
Qed.

Lemma r_compress_eval pp a b d xs :
  th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a) (r_compress_encode xs) =
  wcp_T_sf (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a b d) pp
    (pk_adrs (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a b d)) xs.
Proof.
by [].
Qed.

Lemma r_compress_collision pp a xs ys :
  xs != ys ->
  Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode xs) = Th pp
    (shrincs_fxmss_pk_tweak a)
    (r_compress_encode ys) ->
  (r_compress_encode xs != r_compress_encode ys) &&
  (th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a) (r_compress_encode xs) ==
    th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a) (r_compress_encode ys)).
Proof.
by move=> hne he; rewrite r_compress_encode_eq hne andTb; apply/eqP; exact: he.
Qed.

Lemma r_compress_check_real pp a xs ys (v : bool) :
  (v -> Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode xs) =
    Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode ys)) ->
  (if v && (xs != ys) then
    (r_compress_encode xs != r_compress_encode ys) &&
      (th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a) (r_compress_encode xs) ==
       th_eval shrincs_thf pp (shrincs_fxmss_pk_tweak a) (r_compress_encode ys))
   else v) = v.
Proof.
move=> hv.
case: ifP => [/andP[hv' hn]|] //.
by rewrite (r_compress_collision pp a xs ys hn (hv hv')) hv'.
Qed.

Lemma r_compress_check_ideal (xs ys : seq (bytes 16)) (v : bool) :
  (if v && (xs != ys) then false else v) = v && (xs == ys).
Proof.
by case: v; case: (xs == ys).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Compression loops *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Loops.
Context (P : wc_params) (p : nat) (b : bool).
Local Abbreviation SMB := (SMTCR_game (thf_hash P) (wcp_pk_class P) p b).

Lemma r_compress_resolve_eval (q : th_T (thf_hash P) * th_M (thf_hash P)) :
  resolve SMB (cp_eval_op P) q =
    (#assert ~~ wcp_pk_class P q.1 ;;
     ppo ← get (tcr_pp_loc (thf_hash P)) ;;
     pp ← match ppo with
          | Some pp => ret pp
          | None => pp ← wcp_dPP P ;;
                    #put (tcr_pp_loc (thf_hash P)) := Some pp ;; ret pp
          end ;;
     ret (th_eval (thf_hash P) pp q.1 q.2)).
Proof.
by case: q => [t m]; rewrite /SMTCR_game /resolve /= coerce_kleisliE.
Qed.

#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_counter : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments Shrincs.internal.ssprove.wots.params.decode_tweak : simpl never.
#[local] Arguments intermediates.cp_pick : simpl never.
Local Opaque SMTCR_game.

Lemma r_compress_eval_known {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (q : th_T (thf_hash P) * th_M (thf_hash P))
    (c0 : raw_code B) (k1 : th_N (thf_hash P) -> raw_code B)
    (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (tcr_pp_loc (thf_hash P)) = Some pp) ->
  ~~ wcp_pk_class P q.1 ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈ k1 (th_eval (thf_hash P) pp q.1 q.2) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈ bind (resolve SMB (cp_eval_op P) q) k1 ⦃ post ⦄.
Proof.
move=> hpin ht hk.
rewrite r_compress_resolve_eval.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs (tcr_pp_loc (thf_hash P)) (Some pp)); first exact: hpin.
cbv beta iota.
exact: hk.
Qed.

Lemma r_compress_grind_spec {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (m : wcp_M P) (cs : seq nat)
    (c0 : raw_code B) (k1 : chList (wcp_G P) -> raw_code B)
    (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (tcr_pp_loc (thf_hash P)) = Some pp) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ k1 [seq wcp_H_grind P pp (grind_adrs P) (m, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ bind (code_link (grind_loop P m cs) SMB) k1 ⦃ post ⦄.
Proof.
move=> hpin.
elim: cs k1 => [|c cs ih] k1 hk /=.
- exact: hk.
- rewrite bind_assoc.
  eapply r_compress_eval_known; first exact: hpin.
  + exact: wcp_encode_grind_not_pk.
  + (* An allowed grinding evaluation continues the counter search. *)
    cbv beta.
    rewrite th_evalE_Tgr.
    rewrite code_link_bind bind_assoc.
    apply: ih.
    exact: hk.
Qed.

Lemma r_compress_walk_spec {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (tcr_pp_loc (thf_hash P)) = Some pp) ->
  forall n i k (x : wcp_N P) (c0 : raw_code B) (k1 : wcp_N P -> raw_code B),
  (k + n <= (wcp_w P).-1)%N ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ k1 (chainc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp i x k n) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ bind (code_link (cp_walk P i k n x) SMB) k1 ⦃ post ⦄.
Proof.
move=> hpin.
elim=> [|n ih] i k x c0 k1 hkn hk /=.
- exact: hk.
- rewrite bind_assoc.
  eapply r_compress_eval_known; first exact: hpin.
  + exact: wcp_tw_chain_not_pk.
  + (* An allowed chain evaluation advances the bounded chain walk. *)
    cbv beta.
    have hk' : (k < (wcp_w P).-1)%N by
      apply: leq_trans hkn; rewrite addnS ltnS leq_addr.
    have hkw : (k < wcp_w P)%N by
      apply: (ltn_trans hk'); rewrite ltn_predL; apply: (ltnW (wcp_Hw P)).
    rewrite (eval_Fc_E P pp i k x hkw).
    apply: ih; first by rewrite addSnnS.
    exact: hk.
Qed.

Lemma r_compress_chains_spec {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (tcr_pp_loc (thf_hash P)) = Some pp) ->
  forall ds st (K0 : chList (wcp_N P) -> raw_code B)
    (K1 : chList (wcp_N P) * chList (wcp_N P) -> raw_code B),
  all (fun d : nat => (d < wcp_w P)%N) ds ->
  (forall us, size us = size ds ->
    ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
      K0 (wsigs P pp st ds us) ≈
      K1 (wsigs P pp st ds us, wends P pp st ds (wsigs P pp st ds us)) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    bind (sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P)
      (wcp_dN P) pp st ds) K0 ≈
    bind (code_link (cp_chains P st ds) SMB) K1 ⦃ post ⦄.
Proof.
move=> hpin.
elim=> [|d ds ih] st K0 K1 hds hk.
- exact: (hk [::] erefl).
- move: hds => /= /andP[hd hds'].
rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P))) !bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> u; cbv beta; rewrite !bind_assoc.
case: d hd hk => [|d'] hd hk.
+ rewrite code_link_bind bind_assoc /=.
rewrite code_link_bind bind_assoc.
eapply (r_compress_walk_spec pp pre post hpin ((wcp_w P).-1 - 0) st 0 u); first by
  rewrite add0n subn0.
rewrite (code_link_bind (cp_chains P st.+1 ds)) bind_assoc.
eapply ih; first exact: hds'.
move=> us hus.
move: (hk (u :: us)); rewrite /= hus => /(_ erefl).
exact: id.
+ have hd'w : (d' < wcp_w P)%N := ltn_trans (ltnSn d') hd.
have hd1 : (d'.+1 <= (wcp_w P).-1)%N by rewrite -ltnS (ltn_predK (wcp_Hw P)).
rewrite code_link_bind bind_assoc /=.
rewrite bind_assoc.
eapply r_compress_eval_known; first exact: hpin.
* exact: wcp_tw_chain_not_pk.
* cbv beta.
rewrite (eval_Fc_E P pp st d' u hd'w) /=.
rewrite (code_link_bind (cp_walk P st d'.+1 ((wcp_w P).-1 - d'.+1) (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u))) bind_assoc.
eapply (r_compress_walk_spec pp pre post hpin ((wcp_w P).-1 - d'.+1) st d'.+1 (Fc
  (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u)); first by rewrite (subnKC hd1).
rewrite /= (code_link_bind (cp_chains P st.+1 ds)) bind_assoc.
eapply ih; first exact: hds'.
move=> us hus.
move: (hk (u :: us)); rewrite /= hus => /(_ erefl).
exact: id.
Qed.

End Loops.
