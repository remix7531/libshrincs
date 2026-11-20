(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.outer_forge

    The terminal forgery query preserves the outer leaf-context invariant and
    returns the same verdict. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance tree.nodes leaf.opening leaf.commitments
    leaf.known_message_game
  leaf.paths leaf.context leaf.outer_state leaf.known_message scheme tree.forgery
  tree.classify paired.reduction.
From Stdlib Require Import BinInt.
From Shrincs.internal.ssprove.lib.math Require Import merkle.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context forge state *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_outer_forge_pre st kt sd rt lg roots : precond :=
  leaf_outer_inv ⋊
  rel_app [:: (rhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_keys_loc); (rhs,
    shrincs_fxmss_sd_loc);
    (rhs, shrincs_fxmss_rt_loc); (rhs, shrincs_fxmss_log_loc); (rhs,
      leaf_ctx_roots_loc)]
    (fun sto kt' sd' rt' lg' roots' =>
      sto = Some st /\ kt' = kt /\ sd' = sd /\ rt' = rt /\ lg' = lg /\ roots' = roots).

Lemma leaf_outer_forge_preE st kt sd rt lg roots h0 h1 :
  leaf_outer_forge_pre st kt sd rt lg roots (h0,h1) ->
  leaf_outer_inv (h0,h1) /\
  get_heap h1 shrincs_fxmss_st_loc = Some st /\ get_heap h0 shrincs_fxmss_keys_loc = kt
    /\
  get_heap h1 shrincs_fxmss_sd_loc = sd /\ get_heap h1 shrincs_fxmss_rt_loc = rt /\
  get_heap h1 shrincs_fxmss_log_loc = lg /\ get_heap h1 leaf_ctx_roots_loc = roots.
Proof. by move=> [hi hp]; split. Qed.

Lemma leaf_outer_forge_ready st kt sd rt lg roots h0 h1 :
  leaf_outer_forge_pre st kt sd rt lg roots (h0,h1) ->
  leaf_outer_ready st kt sd (get_heap h1 leaf_opening_st_loc) (get_heap h1
    leaf_opening_pp_loc)
    (get_heap h1 leaf_opening_keys_loc) (get_heap h1 known_message_sd_loc) (get_heap h1
      known_message_cache_loc) roots /\
  known_message_log_consistent rt lg.
Proof.
move/leaf_outer_forge_preE=> [/leaf_outer_invE [he [hl hq hr]] [hs [hk [hsd [hrt [hlg hroots]]]]]].
rewrite hs hk hsd hroots in hr.
by rewrite hrt hlg in hl; split.
Qed.

Lemma leaf_outer_forge_lookup st kt sd rt lg roots x :
  code_stable (leaf_outer_forge_pre st kt sd rt lg roots) (shrincs_fxmss_lookup
    shrincs_fxmss_sha256 x).
Proof.
rewrite /shrincs_fxmss_lookup.
split.
- move=> h0 h1 [/leaf_outer_invE [he _] _].
  apply: he; by rewrite /leaf_outer_private; fmap_solve.
- move=> mp; case: (getm mp x) => [md|]; first by [].
  apply: code_stable_bind.
  + apply: (code_stable_valid emptym).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + move=> md; split; last by [].
    rewrite /leaf_outer_forge_pre.
    apply: put_pre_cond_conj.
    * apply: leaf_outer_inv_put; by [].
    * apply: put_pre_cond_rel_app; by [].
Qed.

Lemma leaf_outer_forge_facts st kt sd rt lg roots h0 h1 :
  leaf_outer_forge_pre st kt sd rt lg roots (h0,h1) ->
  [/\ shrincs_fxmss_structure_legal st.2.1 st.2.2,
      st.1.2 = shrincs_fxmss_honest_node shrincs_fxmss_sha256 (fun a => odflt [::] (getm
        kt a))
        st.1.1.1 st.2.1 st.2.2 255 0%Z,
      leaf_digest_total (shrincs_fxmss_schedule st.2) sd,
      known_message_log_consistent rt lg & roots = leaf_opening_roots
        shrincs_fxmss_sha256 st.2 st.1.1.1
        kt].
Proof.
move/leaf_outer_forge_ready=> [[hd hr ht _ _ _ _ _ hroots] hl].
by split.
Qed.

Lemma leaf_outer_forge_service st kt sd rt lg roots h0 h1 :
  leaf_outer_forge_pre st kt sd rt lg roots (h0,h1) ->
  [/\ get_heap h1 leaf_opening_st_loc = Some (st.1.1.1, st.2),
      get_heap h1 leaf_opening_keys_loc = kt & get_heap h1 known_message_sd_loc = sd].
Proof.
move/leaf_outer_forge_ready=> [[_ _ _ hs _ hk hd _ _] _].
by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context check *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel.

Lemma leaf_outer_check_true st kt sd rt lg roots q :
  q.1 < size (shrincs_fxmss_schedule st.2) ->
  leaf_win shrincs_fxmss_sha256 st.2 st.1.1.1 (leaf_coord_at st.2 q.1) q.2.1 q.2.2
    (odflt [::] (getm kt (leaf_coord_at st.2 q.1))) &&
    known_message_gate shrincs_fxmss_sha256 st.2 st.1.1.1 (leaf_coord_at st.2 q.1)
      (leaf_committed_digest sd (leaf_coord_at st.2 q.1)) q.2.1 ->
  ⊢ ⦃ λ '(h0,h1), leaf_outer_forge_pre st kt sd rt lg roots (h0,h1) ⦄
    ret true ≈ known_message_check_body shrincs_fxmss_sha256 q
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
move=> hq hw.
rewrite /known_message_check_body.
eapply (r_get_rhs_pin leaf_opening_st_loc (Some (st.1.1.1,st.2))).
{ move=> h0 h1 hp; by have [hs _ _] := leaf_outer_forge_service st kt sd rt lg roots h0 h1 hp. }
cbn [bind assertD getSome].
rewrite hq; cbn [bind assertD].
eapply (r_get_rhs_pin leaf_opening_keys_loc kt).
{ move=> h0 h1 hp; by have [_ hk _] := leaf_outer_forge_service st kt sd rt lg roots h0 h1 hp. }
eapply (r_get_rhs_pin known_message_sd_loc sd).
{ move=> h0 h1 hp; by have [_ _ hd] := leaf_outer_forge_service st kt sd rt lg roots h0 h1 hp. }
rewrite hw.
apply: r_ret=> h0 h1 /leaf_outer_forge_preE[hi _]; by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context forge tail *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel shrincs_fxmss_lookup
  known_message_coll_filter G_known_message known_message_check_body leaf_ctx_case
    keep_paired_free
  shrincs_fxmss_verify shrincs_fxmss_full_case.

Definition leaf_outer_forge_left (st : shrincs_fxmss_state) kt (sd :
  shrincs_fxmss_digest_table) rt (lg : seq shrincs_fxmss_message) cm (r : bytes 16) a md
  fsig : raw_code 'bool :=
  ret (shrincs_fxmss_verify shrincs_fxmss_sha256 st.1.1.1 st.1.2 a fsig md &&
    (cm \notin lg) && ~~ ((md \in codomm sd) &&
    (getm rt (a, shrincs_fxmss_bound_message cm) != Some r)) &&
    keep_paired_free shrincs_fxmss_sha256 st kt a md fsig).

Definition leaf_outer_forge_right (st : shrincs_fxmss_state) roots (sd :
  shrincs_fxmss_digest_table) rt (lg : seq shrincs_fxmss_message) cm (r : bytes 16) a md
  fsig : raw_code 'bool :=
  if shrincs_fxmss_verify shrincs_fxmss_sha256 st.1.1.1 st.1.2 a fsig md &&
    (cm \notin lg) && ~~ ((md \in codomm sd) &&
    (getm rt (a, shrincs_fxmss_bound_message cm) != Some r)) then
    match leaf_ctx_case st roots a md fsig with
    | Some FAnchor => known_message_check_body shrincs_fxmss_sha256
        (leaf_slot st.2 a, (md, slice fsig 0 (2 + WOTS_C_CHAINS_SIZE)))
    | _ => ret false
    end
  else ret false.

Lemma leaf_outer_forge_tail st kt sd rt lg roots cm r a md fsig :
  shrincs_fxmss_message_valid cm ->
  ⊢ ⦃ λ '(h0,h1), leaf_outer_forge_pre st kt sd rt lg roots (h0,h1) ⦄
    leaf_outer_forge_left st kt sd rt lg cm r a md fsig
    ≈ leaf_outer_forge_right st roots sd rt lg cm r a md fsig
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
move=> hm.
apply rpre_hypothesis_rule=> u0 u1 hp.
have [hsp hroot hsd hlog hroots] := leaf_outer_forge_facts st kt sd rt lg roots u0 u1 hp.
eapply rpre_weaken_rule with
  (pre := fun '(h0,h1) => leaf_outer_forge_pre st kt sd rt lg roots (h0,h1)); last first.
- by move=> h0 h1 /= [-> ->].
- rewrite /leaf_outer_forge_left /leaf_outer_forge_right hroots
    (leaf_ctx_case_honest st kt a md fsig hsp).
  case hg: (shrincs_fxmss_verify shrincs_fxmss_sha256 st.1.1.1 st.1.2 a fsig md &&
    (cm \notin lg) && ~~ ((md \in codomm sd) &&
    (getm rt (a,shrincs_fxmss_bound_message cm) != Some r))); last first.
  + cbn [andb]; apply: r_ret=> h0 h1 /leaf_outer_forge_preE[hi _]; by split.
  + (* An accepted fresh forgery supplies a winning leaf opening. *)
    have /andP[/andP[hv hf]hveto] := hg.
    rewrite (leaf_outer_keep shrincs_fxmss_sha256 st kt a md fsig hsp hroot hv).
    case hc: (shrincs_fxmss_full_case shrincs_fxmss_sha256 st kt a md fsig) => [[p x y|p
      xy node|p node|]|];
      cbn [andb]; try (by apply: r_ret=> h0 h1 /leaf_outer_forge_preE[hi _]; split).
    have [hq he hw] := leaf_outer_opening shrincs_fxmss_sha256 st kt sd rt lg cm r a md
      fsig
      hsp hroot hsd hlog hm hf hveto hv hc.
    apply: leaf_outer_check_true; first exact hq.
    by rewrite he.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context forge *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel shrincs_fxmss_lookup
  known_message_coll_filter G_known_message known_message_check_body leaf_ctx_case
    keep_paired_free
  shrincs_fxmss_verify shrincs_fxmss_full_case.

Lemma leaf_outer_forge_sim cm sg :
  ⊢ ⦃ λ '(h0,h1), leaf_outer_inv (h0,h1) ⦄
    shrincs_fxmss_full_forge_body shrincs_fxmss_sha256 (keep_paired_free
      shrincs_fxmss_sha256) cm sg
    ≈ code_link (leaf_ctx_forge cm sg)
      (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
rewrite /shrincs_fxmss_full_forge_body /leaf_ctx_forge /leaf_ctx_forge_query.
cbn [bind code_link].
refine (r_get_vs_get_remember_rhs (pre := leaf_outer_inv) _).
- move=> [h0 h1] hi; apply: (leaf_outer_inv_get shrincs_fxmss_st_loc _ h0 h1 hi).
  by rewrite /leaf_outer_private; fmap_solve.
- move=> sto; case: sto => [st|]; last by cbn [isSome assertD fail bind code_link]; apply: r_fail_bind_rhs.
  cbn [isSome assertD bind getSome code_link].
  ssprove_sync.
  + apply: leaf_outer_inv_get.
    by rewrite /leaf_outer_private; fmap_solve.
  + move=> done; case: done; first by cbn [negb assertD fail bind code_link]; apply: r_fail_bind_rhs.
    cbn [negb assertD bind code_link].
    ssprove_sync.
    * apply: leaf_outer_inv_put; by [].
    * refine (r_get_vs_get_remember_rhs
        (pre := leaf_outer_inv ⋊ rem_rhs shrincs_fxmss_st_loc (Some st)) _).
      -- move=> [h0 h1] [hi _]; apply: (leaf_outer_inv_get shrincs_fxmss_log_loc _ h0 h1
        hi).
         by rewrite /leaf_outer_private; fmap_solve.
      -- move=> lg.
         eapply r_get_remember_lhs=> kt.
         refine (r_get_vs_get_remember_rhs _).
         ++ move=> [h0 h1] [[[hi _] _] _]; apply: (leaf_outer_inv_get
           shrincs_fxmss_sd_loc _ h0 h1 hi).
            by rewrite /leaf_outer_private; fmap_solve.
         ++ move=> sd.
            refine (r_get_vs_get_remember_rhs _).
            ** move=> [h0 h1] [[[[hi _] _] _] _]; apply: (leaf_outer_inv_get
              shrincs_fxmss_rt_loc _ h0 h1 hi).
               by rewrite /leaf_outer_private; fmap_solve.
            ** move=> rt.
               eapply r_get_remember_rhs=> roots.
               eapply rpre_weaken_rule with
                 (pre := fun '(h0,h1) => leaf_outer_forge_pre st kt sd rt lg roots (h0,h1)); last first.
               --- (* The remembered heap values establish the forge precondition. *)
                   move=> h0 h1 [[[[[[hi hs] hl] hk] hd] hr] hroots].
                   split; first exact hi.
                   change (get_heap h1 shrincs_fxmss_st_loc = Some st /\ get_heap h0
                     shrincs_fxmss_keys_loc = kt /\
                     get_heap h1 shrincs_fxmss_sd_loc = sd /\ get_heap h1
                       shrincs_fxmss_rt_loc = rt /\
                     get_heap h1 shrincs_fxmss_log_loc = lg /\ get_heap h1
                       leaf_ctx_roots_loc = roots).
                   by repeat split.
               --- case hm: (shrincs_fxmss_message_valid cm); last first.
                   +++ cbn [bind code_link]; apply: r_ret=> h0 h1 /leaf_outer_forge_preE[hi _]; by split.
                   +++ case hs: (shrincs_sf_parse sg) => [[[[z r] i] fsig]|]; last first.
                       *** cbn [bind code_link]; apply: r_ret=> h0 h1 /leaf_outer_forge_preE[hi _]; by split.
                       *** rewrite bind_ret.
                           rewrite !code_link_bind (code_link_scheme _ _ _ _
                             (shrincs_fxmss_lookup_valid shrincs_fxmss_sha256
                               [interface] _)) !bind_assoc.
                           eapply r_bind with (mid := fun '(x,h0) '(y,h1) =>
                             x = y /\ leaf_outer_forge_pre st kt sd rt lg roots (h0,h1)).
                           ---- apply: r_code_stable; exact: leaf_outer_forge_lookup.
                           ---- move=> md md'.
                                apply rpre_hypothesis_rule=> u0 u1 [he hp]; subst md'.
                                eapply rpre_weaken_rule with
                                  (pre := fun '(h0,h1) => leaf_outer_forge_pre st kt sd rt lg roots (h0,h1)); last first.
                                ++++ by move=> h0 h1 /= [-> ->].
                                ++++ (* The parsed forgery agrees with the leaf-context check. *)
                                     cbn [bind code_link].
                                     have ht := leaf_outer_forge_tail st kt sd rt lg roots cm r (z,i) md fsig hm.
                                     rewrite /leaf_outer_forge_left /leaf_outer_forge_right in ht.
                                     case: (shrincs_fxmss_verify shrincs_fxmss_sha256
                                       st.1.1.1 st.1.2 (z,i) fsig md &&
                                       (cm \notin lg) && ~~ ((md \in codomm sd) &&
                                       (getm rt ((z,i),shrincs_fxmss_bound_message cm)
                                         != Some r))) ht;
                                       last by cbn [code_link bind].
                                     case: (leaf_ctx_case st roots (z,i) md fsig) => [[p x y|p xy node|p node|]|];
                                       cbn [code_link bind]; rewrite ?leaf_outer_resolve_check ?bind_ret; by [].
Qed.
