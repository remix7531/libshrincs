(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.outer_sign

    The signing query preserves the outer leaf-context invariant and returns the
    same full signature. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance tree.nodes leaf.opening leaf.commitments
    leaf.known_message_game
  leaf.paths leaf.context leaf.outer_state scheme tree.forgery tree.classify
  leaf.known_message paired.reduction.
From Stdlib Require Import BinInt.
From Shrincs.internal.ssprove.lib.math Require Import merkle.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context sign state *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition leaf_outer_sign_pre st kt sd q cm : precond :=
  leaf_outer_inv ⋊
  rel_app [:: (rhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_keys_loc); (rhs,
    shrincs_fxmss_sd_loc);
    (rhs, shrincs_fxmss_next_loc); (rhs, leaf_opening_slog_loc); (rhs,
      shrincs_fxmss_log_loc)]
    (fun sto kt' sd' nq slog lg => sto = Some st /\ kt' = kt /\ sd' = sd /\
      q < nq /\ all (fun j => j < q) slog /\ cm \in lg).

Lemma leaf_outer_sign_preE st kt sd q cm h0 h1 :
  leaf_outer_sign_pre st kt sd q cm (h0,h1) ->
  leaf_outer_inv (h0,h1) /\
  get_heap h1 shrincs_fxmss_st_loc = Some st /\ get_heap h0 shrincs_fxmss_keys_loc = kt
    /\
  get_heap h1 shrincs_fxmss_sd_loc = sd /\ q < get_heap h1 shrincs_fxmss_next_loc /\
  all (fun j => j < q) (get_heap h1 leaf_opening_slog_loc) /\ cm \in get_heap h1
    shrincs_fxmss_log_loc.
Proof. by move=> [hi hp]; split. Qed.

Lemma leaf_outer_sign_start st q cm h0 h1 :
  leaf_outer_inv (h0,h1) -> get_heap h1 shrincs_fxmss_st_loc = Some st ->
  get_heap h1 shrincs_fxmss_next_loc = q -> cm \in get_heap h1 shrincs_fxmss_log_loc ->
  leaf_outer_sign_pre st (get_heap h0 shrincs_fxmss_keys_loc) (get_heap h1
    shrincs_fxmss_sd_loc) q cm
    (set_heap h0 shrincs_fxmss_next_loc q.+1, set_heap h1 shrincs_fxmss_next_loc q.+1).
Proof.
move=> hi hs hq hm.
split.
- apply: leaf_outer_next_put hi _; by rewrite hq leqnSn.
- (* Advancing the slot establishes the signing precondition. *)
  change (get_heap (set_heap h1 shrincs_fxmss_next_loc q.+1) shrincs_fxmss_st_loc = Some
  st /\
    get_heap (set_heap h0 shrincs_fxmss_next_loc q.+1) shrincs_fxmss_keys_loc = get_heap
      h0 shrincs_fxmss_keys_loc /\
    get_heap (set_heap h1 shrincs_fxmss_next_loc q.+1) shrincs_fxmss_sd_loc = get_heap
      h1 shrincs_fxmss_sd_loc /\
    q < get_heap (set_heap h1 shrincs_fxmss_next_loc q.+1) shrincs_fxmss_next_loc /\
    all (fun j => j < q) (get_heap (set_heap h1 shrincs_fxmss_next_loc q.+1)
      leaf_opening_slog_loc) /\
    cm \in get_heap (set_heap h1 shrincs_fxmss_next_loc q.+1) shrincs_fxmss_log_loc).
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  have [_ [_ hslots _]] := leaf_outer_invE h0 h1 hi.
  rewrite hq in hslots.
  by repeat split.
Qed.

Lemma leaf_outer_sign_ready st kt sd q cm h0 h1 :
  leaf_outer_sign_pre st kt sd q cm (h0,h1) ->
  leaf_outer_ready st kt sd (get_heap h1 leaf_opening_st_loc) (get_heap h1
    leaf_opening_pp_loc)
    (get_heap h1 leaf_opening_keys_loc) (get_heap h1 known_message_sd_loc) (get_heap h1
      known_message_cache_loc)
    (get_heap h1 leaf_ctx_roots_loc).
Proof.
move/leaf_outer_sign_preE=> [/leaf_outer_invE [_ [_ _ hr]] [hs [hk [hd _]]]].
by rewrite hs hk hd in hr.
Qed.

Local Opaque leaf_outer_inv.
Lemma leaf_outer_sign_pre_put st kt sd q cm (l : Location) (v : l) :
  l.1 \notin [:: 1300; 1303; 1310; 1311; 1304; 1307;
    1500; 1501; 1502; 1503; 1510; 1511; 1900] ->
  put_pre_cond l v (leaf_outer_sign_pre st kt sd q cm).
Proof.
move=> hl.
rewrite /leaf_outer_sign_pre.
apply: put_pre_cond_conj; first exact: leaf_outer_inv_put hl.
apply: put_pre_cond_rel_app.
move: hl; rewrite !in_cons !negb_or.
move=> /andP[h0 /andP[h3 /andP[h10 /andP[h11 /andP[h4 /andP[h7 /andP[h500 /andP[h501 /andP[h502 /andP[h503 rest]]]]]]]]]].
by rewrite h0 h3 h10 h4 h7 h503.
Qed.

Lemma leaf_outer_sign_rt_put st kt sd q cm rt a r h0 h1 :
  leaf_outer_sign_pre st kt sd q cm (h0,h1) ->
  get_heap h1 shrincs_fxmss_rt_loc = rt -> shrincs_fxmss_message_valid cm ->
  leaf_outer_sign_pre st kt sd q cm
    (set_heap h0 shrincs_fxmss_rt_loc (setm rt (a, shrincs_fxmss_bound_message cm) r),
     set_heap h1 shrincs_fxmss_rt_loc (setm rt (a, shrincs_fxmss_bound_message cm) r)).
Proof.
move=> hp hr hm.
have [hi [_ [_ [_ [_ [_ hmem]]]]]] := leaf_outer_sign_preE st kt sd q cm h0 h1 hp.
split.
- exact: leaf_outer_rt_put hi hr hm hmem.
- (* Updating the randomness table preserves the other signing state. *)
  have [_ hf] := hp.
  change (rel_app [:: (rhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_keys_loc); (rhs,
    shrincs_fxmss_sd_loc);
    (rhs, shrincs_fxmss_next_loc); (rhs, leaf_opening_slog_loc); (rhs,
      shrincs_fxmss_log_loc)]
    (fun sto kt' sd' nq slog lg => sto = Some st /\ kt' = kt /\ sd' = sd /\
      q < nq /\ all (fun j => j < q) slog /\ cm \in lg)
    (set_heap h0 shrincs_fxmss_rt_loc (setm rt (a, shrincs_fxmss_bound_message cm) r),
     set_heap h1 shrincs_fxmss_rt_loc (setm rt (a, shrincs_fxmss_bound_message cm) r))).
  apply: put_pre_cond_rel_app hf; by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context sign tail *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel shrincs_fxmss_lookup
  known_message_coll_filter G_known_message known_message_check_body leaf_ctx_case
    keep_paired_free
  shrincs_fxmss_verify shrincs_fxmss_full_case.

Lemma leaf_outer_sign_tail st kt sd q cm r a :
  shrincs_fxmss_select_leaf st.2.1 st.2.2 q = Some a ->
  ⊢ ⦃ λ '(h0,h1), leaf_outer_sign_pre st kt sd q cm (h0,h1) ⦄
    (match shrincs_fxmss_sign shrincs_fxmss_sha256 (leaf_committed_digest sd a)
      (fun c => odflt [::] (getm kt c)) a.2 a.1 st.1.1.1 st.2.1 (uint U8 st.2.2) with
     | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
     | None => ret None end)
    ≈ (ws ← known_message_sign_body q ;;
       roots ← get leaf_ctx_roots_loc ;;
       match ws, leaf_ctx_auth st.1.1.1 st.2 roots a with
       | Some ws, Some ap => ret (shrincs_sf_encode a.1 r a.2
           (tval ws ++ flatten [seq tval n | n <- rev ap]))
       | _, _ => ret None end)
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
move=> hs.
have [hsp hq] := shrincs_fxmss_select_leaf_some _ _ _ _ hs.
have ha := leaf_select_in_schedule st.2 q a hs.
have he : leaf_coord_at st.2 q = a.
{ by rewrite (leaf_select_eq st.2 q hsp hq) in hs; case: hs. }
rewrite (leaf_outer_sign_honest st.2 st.1.1.1 kt a _ hsp ha).
rewrite /known_message_sign_body.
cbn [bind].
eapply (r_get_rhs_pin leaf_opening_st_loc (Some (st.1.1.1,st.2))).
- move=> h0 h1 hp.
  by have [_ _ _ hh _ _ _ _ _] := leaf_outer_sign_ready st kt sd q cm h0 h1 hp.
- cbn [isSome assertD getSome bind].
  rewrite (leaf_schedule_length st.2 hsp) hq.
  cbn [assertD bind].
  eapply r_get_remember_rhs=> slog.
  have hfresh : forall h0 h1,
    (leaf_outer_sign_pre st kt sd q cm ⋊ rem_rhs leaf_opening_slog_loc slog) (h0,h1) ->
    q \notin slog.
  { move=> h0 h1 [hp hsl].
    have [_ [_ [_ [_ [_ [hslots _]]]]]] := leaf_outer_sign_preE st kt sd q cm h0 h1 hp.
    change (get_heap h1 leaf_opening_slog_loc = slog) in hsl.
    rewrite hsl in hslots.
    apply/negP=> hmem.
    have := allP hslots q hmem.
    by rewrite ltnn.
  }
  apply rpre_hypothesis_rule=> u0 u1 hp.
  rewrite (hfresh u0 u1 hp).
  cbn [assertD bind].
  eapply rpre_weaken_rule with
    (pre := fun '(h0,h1) => (leaf_outer_sign_pre st kt sd q cm ⋊ rem_rhs
      leaf_opening_slog_loc slog) (h0,h1)); last first.
  + by move=> h0 h1 /= [-> ->].
  + eapply r_put_rhs_pre with (pre' := leaf_outer_inv ⋊
      rem_rhs known_message_cache_loc (known_message_cache shrincs_fxmss_sha256 st.2
        st.1.1.1 sd kt) ⋊
      rem_rhs leaf_ctx_roots_loc (leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1
        kt)).
    * move=> h0 h1 [hp0 hsl].
      have [hi [_ [_ [_ [hn _]]]]] := leaf_outer_sign_preE st kt sd q cm h0 h1 hp0.
      have [_ _ _ _ _ _ _ hc hr] := leaf_outer_sign_ready st kt sd q cm h0 h1 hp0.
      split; first split.
      -- exact: leaf_outer_slog_put hi hsl hn.
      -- (* Logging the slot leaves the cached signatures unchanged. *)
         change (get_heap (set_heap h1 leaf_opening_slog_loc (q::slog))
        known_message_cache_loc = known_message_cache
        shrincs_fxmss_sha256 st.2 st.1.1.1 sd kt).
         rewrite get_set_heap_neq; first by [].
         exact hc.
      -- (* Logging the slot leaves the stored leaf roots unchanged. *)
         change (get_heap (set_heap h1 leaf_opening_slog_loc (q::slog))
        leaf_ctx_roots_loc =
        leaf_opening_roots shrincs_fxmss_sha256 st.2 st.1.1.1 kt).
         rewrite get_set_heap_neq; first by [].
         exact hr.
    * eapply (r_get_rhs_pin known_message_cache_loc (known_message_cache
      shrincs_fxmss_sha256 st.2 st.1.1.1 sd
      kt)).
      -- by move=> h0 h1 [[hi hc] hr].
      -- cbn [bind].
         eapply (r_get_rhs_pin leaf_ctx_roots_loc (leaf_opening_roots
           shrincs_fxmss_sha256 st.2
           st.1.1.1 kt)).
         ++ by move=> h0 h1 [[hi hc] hr].
         ++ cbn [bind].
            rewrite (known_message_cache_nth shrincs_fxmss_sha256 st.2 st.1.1.1 sd kt q
              hsp hq) he.
            case: (leaf_sign_at shrincs_fxmss_sha256 st.2 st.1.1.1 a
              (odflt [::] (getm kt a)) (leaf_committed_digest sd a)) => [ws|].
            ** case: (leaf_ctx_auth st.1.1.1 st.2 (leaf_opening_roots
              shrincs_fxmss_sha256 st.2
              st.1.1.1 kt) a) => [ap|];
                 apply: r_ret=> h0 h1 [[hi _] _]; by split.
            ** apply: r_ret=> h0 h1 [[hi _] _]; by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context sign query *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel shrincs_fxmss_lookup
  known_message_coll_filter G_known_message known_message_check_body leaf_ctx_case
    keep_paired_free
  shrincs_fxmss_verify shrincs_fxmss_full_case.

Local Opaque leaf_outer_sign_pre shrincs_fxmss_sign leaf_ctx_auth
  known_message_sign_body.

Lemma leaf_outer_sign_query st kt sd q cm a :
  shrincs_fxmss_message_valid cm ->
  shrincs_fxmss_select_leaf st.2.1 st.2.2 q = Some a ->
  ⊢ ⦃ λ '(h0,h1), leaf_outer_sign_pre st kt sd q cm (h0,h1) ⦄
    leaf_outer_sign_left st cm a ≈ code_link (leaf_outer_sign_right st q cm a)
      (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
move=> hm hs.
rewrite /leaf_outer_sign_left /leaf_outer_sign_right.
cbn [code_link].
ssprove_sync.
- move=> h0 h1 /leaf_outer_sign_preE[hi _].
  apply: (leaf_outer_inv_get shrincs_fxmss_ks_loc _ h0 h1 hi).
  by rewrite /leaf_outer_private; fmap_solve.
- move=> kso; case: kso => [ks|]; last by cbn [isSome assertD bind code_link]; apply: r_fail.
  cbn [isSome assertD getSome bind code_link].
  ssprove_sync.
  + move=> h0 h1 /leaf_outer_sign_preE[hi _].
    apply: (leaf_outer_inv_get shrincs_fxmss_kp_loc _ h0 h1 hi).
    by rewrite /leaf_outer_private; fmap_solve.
  + move=> kpo; case: kpo => [kp|]; last by cbn [isSome assertD bind code_link]; apply: r_fail.
    cbn [isSome assertD getSome bind code_link].
    eapply r_get_remember_lhs=> kt'.
    apply rpre_hypothesis_rule=> u0 u1 [hp hk].
    have [_ [_ [he _]]] := leaf_outer_sign_preE st kt sd q cm u0 u1 hp.
    change (get_heap u0 shrincs_fxmss_keys_loc = kt') in hk.
    rewrite he in hk; subst kt'.
    eapply rpre_weaken_rule with
      (pre := fun '(h0,h1) => leaf_outer_sign_pre st kt sd q cm (h0,h1)); last first.
    * by move=> h0 h1 /= [-> ->].
    * refine (r_get_vs_get_remember_rhs _).
      -- move=> [h0 h1] /leaf_outer_sign_preE[hi _].
         apply: (leaf_outer_inv_get shrincs_fxmss_rt_loc _ h0 h1 hi).
         by rewrite /leaf_outer_private; fmap_solve.
      -- (* Cached and fresh signing randomness lead to the same leaf query. *)
         move=> rt.
         set dN := shrincs_fxmss_secret_dist shrincs_fxmss_sha256.
         have hdN : ValidCode emptym [interface] dN := prog_valid
           (shrincs_fxmss_secret_dist shrincs_fxmss_sha256).
         clearbody dN.
         case: (getm rt (a,shrincs_fxmss_bound_message cm)) => [r|];
           cbn [bind code_link];
           [ idtac
           | rewrite code_link_bind (code_link_scheme _ _ _ _ hdN) bind_assoc;
             eapply (r_scheme_bind dN); [exact hdN | move=> r] ];
           cbn [bind code_link];
           apply: r_put_vs_put;
           (eapply rpre_weaken_rule with
             (pre := fun '(h0,h1) => leaf_outer_sign_pre st kt sd q cm (h0,h1)); last first);
           try (by move=> h0 h1 [v1 [[v0 [[hp0 hr] ->]] ->]]; exact: leaf_outer_sign_rt_put hp0 hr hm);
           refine (r_get_vs_get_remember_rhs _);
           try (by move=> [h0 h1] /leaf_outer_sign_preE[hi _];
             apply: (leaf_outer_inv_get shrincs_fxmss_sd_loc _ h0 h1 hi); rewrite
               /leaf_outer_private; fmap_solve);
           move=> sd';
           apply rpre_hypothesis_rule=> v0 v1 [hp0 hd];
           have [_ [_ [_ [he' _]]]] := leaf_outer_sign_preE st kt sd q cm v0 v1 hp0;
           change (get_heap v1 shrincs_fxmss_sd_loc = sd') in hd;
           rewrite he' in hd; subst sd';
           have [_ _ ht _ _ _ _ _ _] := leaf_outer_sign_ready st kt sd q cm v0 v1 hp0;
           (have hemd : getm sd a = Some (leaf_committed_digest sd a) by
             (rewrite /leaf_committed_digest;
              have := allP ht a (leaf_select_in_schedule st.2 q a hs); by case: (getm sd a)));
           rewrite hemd;
           cbn [bind code_link];
           (eapply rpre_weaken_rule with
             (pre := fun '(h0,h1) => leaf_outer_sign_pre st kt sd q cm (h0,h1)); last first);
           try (by move=> h0 h1 /= [-> ->]);
           ssprove_sync;
           try (by move=> h0 h1 /leaf_outer_sign_preE[hi _];
             apply: (leaf_outer_inv_get shrincs_fxmss_rom_loc _ h0 h1 hi); rewrite
               /leaf_outer_private; fmap_solve);
           move=> mp;
           ssprove_sync;
           try (by apply: leaf_outer_sign_pre_put);
           rewrite leaf_outer_resolve_sign ?bind_ret /shrincs_fxmss_lookup_keys;
           (have hlink (ws : option leaf_opening_signature) roots :
             code_link (match ws, leaf_ctx_auth st.1.1.1 st.2 roots a with
               | Some ws, Some ap => ret (shrincs_sf_encode a.1 r a.2
                   (tval ws ++ flatten [seq tval n | n <- rev ap]))
               | _, _ => ret None end) (known_message_coll_filter ∘ G_known_message
                 shrincs_fxmss_sha256
                 true)%pack =
             (match ws, leaf_ctx_auth st.1.1.1 st.2 roots a with
               | Some ws, Some ap => ret (shrincs_sf_encode a.1 r a.2
                   (tval ws ++ flatten [seq tval n | n <- rev ap]))
               | _, _ => ret None end) by
             (case: ws => [ws|]; case: (leaf_ctx_auth st.1.1.1 st.2 roots a) => [ap|]; reflexivity));
           setoid_rewrite hlink;
           apply: leaf_outer_sign_tail hs.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Outer leaf context sign sim *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque shrincs_fxmss_sha256 leaf_outer_inv leaf_outer_rel shrincs_fxmss_lookup
  known_message_coll_filter G_known_message known_message_check_body leaf_ctx_case
    keep_paired_free
  shrincs_fxmss_verify shrincs_fxmss_full_case.

Local Opaque leaf_outer_sign_pre shrincs_fxmss_sign leaf_ctx_auth
  known_message_sign_body.

Lemma leaf_outer_sign_sim Q keep bit cm :
  ⊢ ⦃ λ '(h0,h1), leaf_outer_inv (h0,h1) ⦄
    resolve (G_forge_full_signature shrincs_fxmss_sha256 Q keep bit)
      (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm
    ≈ code_link (leaf_ctx_sign Q cm)
      (known_message_coll_filter ∘ G_known_message shrincs_fxmss_sha256 true)%pack
  ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄.
Proof.
rewrite leaf_outer_full_signE /leaf_outer_full_sign /leaf_ctx_sign.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := leaf_outer_inv) _).
- move=> [h0 h1] hi; apply: (leaf_outer_inv_get shrincs_fxmss_st_loc _ h0 h1 hi).
  by rewrite /leaf_outer_private; fmap_solve.
- move=> sto; case: sto => [st|]; last by cbn [isSome assertD code_link bind]; apply: r_fail.
  cbn [isSome assertD getSome bind code_link].
  ssprove_sync.
  + apply: leaf_outer_inv_get.
    by rewrite /leaf_outer_private; fmap_solve.
  + move=> done; case: done; first by cbn [negb assertD bind code_link]; apply: r_fail.
    cbn [negb assertD bind code_link].
    ssprove_sync.
    * apply: leaf_outer_inv_get.
      by rewrite /leaf_outer_private; fmap_solve.
    * move=> sc; case: (sc < shrincs_fxmss_sign_budget Q); last by cbn [assertD bind
      code_link]; apply: r_fail.
      cbn [assertD bind code_link].
      refine (r_get_vs_get_remember_rhs _).
      -- move=> [h0 h1] [hi _]; apply: (leaf_outer_inv_get shrincs_fxmss_log_loc _ h0 h1
        hi).
         by rewrite /leaf_outer_private; fmap_solve.
      -- move=> lg.
         ssprove_sync.
         ++ apply: leaf_outer_inv_put; by [].
         ++ apply: r_put_vs_put.
            eapply rpre_weaken_rule with (pre := fun '(h0,h1) =>
              (leaf_outer_inv ⋊ rem_rhs shrincs_fxmss_st_loc (Some st) ⋊ rem_rhs
                shrincs_fxmss_log_loc (cm::lg)) (h0,h1)); last first.
            ** move=> h0 h1 [u1 [[u0 [[[hi hst] hlg] ->]] ->]].
               split; first split.
               --- exact: leaf_outer_log_put hi hlg.
               --- change (get_heap (set_heap u1 shrincs_fxmss_log_loc (cm::lg))
                 shrincs_fxmss_st_loc = Some st).
                   rewrite get_set_heap_neq; first by [].
                   exact hst.
               --- change (get_heap (set_heap u1 shrincs_fxmss_log_loc (cm::lg))
                 shrincs_fxmss_log_loc = cm::lg).
                   exact: get_set_heap_eq.
            ** case hm: (shrincs_fxmss_message_valid cm); last by cbn [bind code_link];
                 apply: r_ret=> h0 h1 [[hi _] _]; split.
               cbn [code_link].
               refine (r_get_vs_get_remember_rhs _).
               --- move=> [h0 h1] [[hi _] _]; apply: (leaf_outer_inv_get
                 shrincs_fxmss_next_loc _ h0 h1 hi).
                   by rewrite /leaf_outer_private; fmap_solve.
               --- (* An exhausted schedule returns None; a selected slot proceeds to signing. *)
                   move=> q.
                   case hs: (shrincs_fxmss_select_leaf st.2.1 st.2.2 q) => [a|]; last by cbn [code_link];
                     apply: r_ret=> h0 h1 [[[hi _] _] _]; split.
                   cbn [code_link].
                   apply rpre_hypothesis_rule=> u0 u1 [[[hi hst] hlg] hq].
                   eapply rpre_weaken_rule with (pre := fun '(h0,h1) => h0 = u0 /\ h1 = u1); last by [].
                   eapply r_put_vs_put with (pre := fun '(h0,h1) => h0 = u0 /\ h1 = u1).
                   eapply rpre_weaken_rule with (pre := fun '(h0,h1) =>
                     leaf_outer_sign_pre st (get_heap u0 shrincs_fxmss_keys_loc)
                       (get_heap u1 shrincs_fxmss_sd_loc) q cm (h0,h1)); last first.
                   +++ (* Logging the message establishes the signing precondition. *)
                       move=> h0 h1 [v1 [[v0 [[he0 he1] ->]] ->]].
                       cbn in he0, he1; subst v0 v1.
                       apply: leaf_outer_sign_start hi hst hq _.
                       change (get_heap u1 shrincs_fxmss_log_loc = cm::lg) in hlg.
                       by rewrite hlg in_cons eqxx.
                   +++ (* The selected leaf satisfies the signing-query simulation. *)
                       change (⊢ ⦃ λ '(h0,h1),
                         leaf_outer_sign_pre st (get_heap u0 shrincs_fxmss_keys_loc)
                           (get_heap u1 shrincs_fxmss_sd_loc) q cm (h0,h1) ⦄
                         leaf_outer_sign_left st cm a ≈ code_link (leaf_outer_sign_right st q cm a)
                           (known_message_coll_filter ∘ G_known_message
                             shrincs_fxmss_sha256
                             true)%pack
                         ⦃ λ '(x,h0) '(y,h1), x = y /\ leaf_outer_inv (h0,h1) ⦄).
                       exact: leaf_outer_sign_query hm hs.
Qed.
