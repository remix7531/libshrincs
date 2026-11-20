(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.grind.state

    The grinding block tracks the pinned seed, reveal flag, attempted tweaks and
    successful targets. Option-game EVAL and chain sampling couple under any
    pinned seed invariant. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules chain.core chain.ud.
From Shrincs Require Import spec games schemes.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs.internal.ssprove.fxmss Require Import
  params instance leaf.prepared leaf.grind.reduction.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.compress.

(* ------------------------------------------------------------------ *)
(** ** Grinding state *)

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition r_grind_private : Locations :=
  [fmap prepared_leaf_pp_loc; stcr_option_pp_loc shrincs_thf; stcr_option_tgts_loc
    shrincs_thf (bytes 32);
    stcr_option_tws_loc shrincs_thf; stcr_option_rev_loc].
Definition r_grind_block (pp : bytes 16) (rv : bool) (tw : seq tweak)
    (tg : chMap 'nat (tweak × (bytes 32 × 'nat))) : precond :=
  fun '(h0, h1) => heap_ignore r_grind_private (h0, h1) /\
    get_heap h0 prepared_leaf_pp_loc = Some pp /\
    get_heap h1 (stcr_option_pp_loc shrincs_thf) = Some pp /\
    get_heap h1 stcr_option_rev_loc = rv /\
    get_heap h1 (stcr_option_tws_loc shrincs_thf) = tw /\
    get_heap h1 (stcr_option_tgts_loc shrincs_thf (bytes 32)) = tg.

Lemma r_grind_block_targets pp rv tw tg tg' h0 h1 :
  r_grind_block pp rv tw tg (h0, h1) ->
  r_grind_block pp rv tw tg'
    (h0, set_heap h1 (stcr_option_tgts_loc shrincs_thf (bytes 32)) tg').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_grind_private; fmap_solve.
- (* Only the target table changes; seeds, reveal flag and tweaks agree. *)
  split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  exact: get_set_heap_eq.
Qed.

Lemma r_grind_block_tweaks pp rv tw tg tw' h0 h1 :
  r_grind_block pp rv tw tg (h0, h1) ->
  r_grind_block pp rv tw' tg
    (h0, set_heap h1 (stcr_option_tws_loc shrincs_thf) tw').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_grind_private; fmap_solve.
- (* Only the tweak list changes; the other recorded values agree. *)
  split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  split; first exact: get_set_heap_eq.
  by rewrite get_set_heap_neq.
Qed.

Lemma r_grind_block_reveal pp rv tw tg rv' h0 h1 :
  r_grind_block pp rv tw tg (h0, h1) ->
  r_grind_block pp rv' tw tg (h0, set_heap h1 stcr_option_rev_loc rv').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_grind_private; fmap_solve.
- split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first exact: get_set_heap_eq.
  split; by rewrite get_set_heap_neq.
Qed.

Definition r_grind_update (tg : chMap 'nat (tweak × (bytes 32 × 'nat))) j a md
    (answer : option (bytes 16 * nat)) :=
  if answer is Some (_, c) then setm tg j (shrincs_fxmss_grind_tweak a, (md, c)) else
    tg.

Local Opaque wots_c_counter_max.
Lemma r_grind_resolve_query p b a md :
  resolve (fxmss_grind_game p b)
    (SQUERY, (tweak × bytes 32, 'option (bytes 16 × 'nat))) (shrincs_fxmss_grind_tweak
      a, md) =
  (#assert wots_c_grind_class (shrincs_fxmss_grind_tweak a) ;;
   revealed ← get stcr_option_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get (stcr_option_tws_loc shrincs_thf) ;;
   #assert size tws < p ;;
   #assert shrincs_fxmss_grind_tweak a \notin tws ;;
   #put (stcr_option_tws_loc shrincs_thf) := rcons tws (shrincs_fxmss_grind_tweak a) ;;
   ppo ← get (stcr_option_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (stcr_option_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   let found := [seq i <- iota 0 wots_c_counter_max |
     let q := wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md i in
     if wots_c_grind_class q.1 then wots_c_grind_prp (Th pp q.1 q.2) else false] in
   match found with
   | i :: _ =>
     tgts ← get (stcr_option_tgts_loc shrincs_thf (bytes 32)) ;;
     #put (stcr_option_tgts_loc shrincs_thf (bytes 32)) :=
       setm tgts (size tws) (shrincs_fxmss_grind_tweak a, (md, i)) ;;
     ret (Some (Th pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md i).1
       (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md i).2, i))
   | [::] => ret None
   end).
Proof.
by rewrite /fxmss_grind_game /STCRP_option_game /resolve /= coerce_kleisliE.
Qed.

Local Opaque dBytes Th r_grind_block.
Lemma r_grind_query_spec p b {B : choiceType} sp pp tw tg a md
    (c0 : raw_code B) (k1 : option (bytes 16 * nat) -> raw_code B)
    (post : postcond B B) :
  size tw < p -> shrincs_fxmss_grind_tweak a \notin tw ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp false (rcons tw (shrincs_fxmss_grind_tweak a))
      (r_grind_update tg (size tw) a md (r_grind_answer sp pp a md)) (h0, h1) ⦄
    c0 ≈ k1 (r_grind_answer sp pp a md) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp false tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (fxmss_grind_game p b)
      (SQUERY, (tweak × bytes 32, 'option (bytes 16 × 'nat))) (shrincs_fxmss_grind_tweak
        a, md)) k1 ⦃ post ⦄.
Proof.
move=> hbudget hfresh hk.
rewrite r_grind_resolve_query.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs stcr_option_rev_loc false);
  first by move=> h0 h1 [_ [_ [_ [hr _]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs (stcr_option_tws_loc shrincs_thf) tw);
  first by move=> h0 h1 [_ [_ [_ [_ [ht _]]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_put_bind_rhs (stcr_option_tws_loc shrincs_thf)
  (rcons tw (shrincs_fxmss_grind_tweak a)) _
  (r_grind_block pp false (rcons tw (shrincs_fxmss_grind_tweak a)) tg)).
- move=> h0 h1 hp.
  exact: r_grind_block_tweaks hp.
- eapply (r_get_bind_rhs (stcr_option_pp_loc shrincs_thf) (Some pp));
    first by move=> h0 h1 [_ [_ [hr _]]].
  cbv beta iota.
  cbn [bind].
  rewrite /r_grind_answer -(r_grind_search sp pp a md) in hk.
  set found := [seq i <- iota 0 wots_c_counter_max |
    let q := wots_c_grind_enc (shrincs_fxmss_grind_tweak a) md i in
    if wots_c_grind_class q.1 then wots_c_grind_prp (Th pp q.1 q.2)
    else false] in hk |- *.
  case: found hk => [|c cs] hk.
  + exact: hk.
  + eapply (r_get_bind_rhs (stcr_option_tgts_loc shrincs_thf (bytes 32)) tg);
      first by move=> h0 h1 [_ [_ [_ [_ [_ ht]]]]].
    cbv beta iota.
    eapply (r_put_bind_rhs (stcr_option_tgts_loc shrincs_thf (bytes 32))
      (setm tg (size tw) (shrincs_fxmss_grind_tweak a, (md, c))) _
      (r_grind_block pp false (rcons tw (shrincs_fxmss_grind_tweak a))
        (setm tg (size tw) (shrincs_fxmss_grind_tweak a, (md, c))))).
    * move=> h0 h1 hp.
      exact: r_grind_block_targets hp.
    * exact: hk.
Qed.

Lemma r_grind_resolve_reveal p b :
  resolve (fxmss_grind_game p b)
    (SGETPP, ('unit, bytes 16)) tt =
  (ppo ← get (stcr_option_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (stcr_option_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   #put stcr_option_rev_loc := true ;;
   ret pp).
Proof.
by rewrite /fxmss_grind_game /STCRP_option_game /resolve /= coerce_kleisliE.
Qed.

Lemma r_grind_reveal_spec p b {B : choiceType} pp rv tw tg
    (c0 : raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp true tw tg (h0, h1) ⦄
    c0 ≈ k1 pp ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp rv tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (fxmss_grind_game p b)
      (SGETPP, ('unit, bytes 16)) tt) k1 ⦃ post ⦄.
Proof.
move=> hk.
rewrite r_grind_resolve_reveal.
eapply (r_get_bind_rhs (stcr_option_pp_loc shrincs_thf) (Some pp));
  first by move=> h0 h1 [_ [_ [hr _]]].
cbv beta iota.
eapply (r_put_bind_rhs stcr_option_rev_loc true _ (r_grind_block pp true tw tg)).
- move=> h0 h1 hp.
  exact: r_grind_block_reveal hp.
- exact: hk.
Qed.

Lemma r_grind_resolve_check p b j m c :
  resolve (fxmss_grind_game p b)
    (SCHECK, ('nat × (bytes 32 × 'nat), 'bool)) (j, (m, c)) =
  (revealed ← get stcr_option_rev_loc ;;
   #assert revealed ;;
   pp ← getSome (stcr_option_pp_loc shrincs_thf) ;;
   if b then
     tgts ← get (stcr_option_tgts_loc shrincs_thf (bytes 32)) ;;
     match getm tgts j with
     | Some (t0, (m0, c0)) =>
       let target := wots_c_grind_enc t0 m0 c0 in
       let candidate := wots_c_grind_enc t0 m c in
       ret (if wots_c_grind_class target.1 && wots_c_grind_class candidate.1
         then (m != m0) && (Th pp target.1 target.2 ==
           Th pp candidate.1 candidate.2) else false)
     | None => ret false
     end
   else ret false).
Proof.
by rewrite /fxmss_grind_game /STCRP_option_game /resolve /= coerce_kleisliE.
Qed.

Local Opaque dBytes r_grind_block Th.
Lemma r_grind_check_spec p b {B : choiceType} pp tw tg j a m0 c0 m c
    (x0 : raw_code B) (k1 : bool -> raw_code B) (post : postcond B B) :
  getm tg j = Some (shrincs_fxmss_grind_tweak a, (m0, c0)) ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp true tw tg (h0, h1) ⦄
    x0 ≈ k1 (b && (m != m0) &&
      (Th pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) m0 c0).1
        (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) m0 c0).2 ==
       Th pp (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) m c).1
        (wots_c_grind_enc (shrincs_fxmss_grind_tweak a) m c).2)) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_grind_block pp true tw tg (h0, h1) ⦄
    x0 ≈ bind (resolve (fxmss_grind_game p b)
      (SCHECK, ('nat × (bytes 32 × 'nat), 'bool)) (j, (m, c))) k1 ⦃ post ⦄.
Proof.
move=> ht hk.
rewrite r_grind_resolve_check.
eapply (r_get_bind_rhs stcr_option_rev_loc true);
  first by move=> h0 h1 [_ [_ [_ [hr _]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs (stcr_option_pp_loc shrincs_thf) (Some pp));
  first by move=> h0 h1 [_ [_ [hr _]]].
cbv beta iota.
cbn [assertD].
case: b hk => hk; cbv beta iota in hk |- *; last exact: hk.
eapply (r_get_bind_rhs (stcr_option_tgts_loc shrincs_thf (bytes 32)) tg);
  first by move=> h0 h1 [_ [_ [_ [_ [_ ht']]]]].
cbv beta iota.
rewrite ht.
exact: hk.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Grinding loops *)

Import PackageNotation stcrp_option.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Loops.
Context (P : wc_params) (p : nat) (b : bool).
Local Abbreviation SMB := (STCRP_option_game (thf_hash P) (wcp_grind_class P) (wcp_M P)
  (grind_enc P) (grind_prp P) (wcp_c_max P) p b).

Lemma r_grind_resolve_eval (q : th_T (thf_hash P) * th_M (thf_hash P)) :
  resolve SMB (cp_eval_op P) q =
    (#assert ~~ wcp_grind_class P q.1 ;;
     ppo ← get (stcr_option_pp_loc (thf_hash P)) ;;
     pp ← match ppo with
          | Some pp => ret pp
          | None => pp ← wcp_dPP P ;;
                    #put (stcr_option_pp_loc (thf_hash P)) := Some pp ;; ret pp
          end ;;
     ret (th_eval (thf_hash P) pp q.1 q.2)).
Proof.
by case: q => [t m]; rewrite /STCRP_option_game /resolve /= coerce_kleisliE.
Qed.

#[local] Arguments resolve : simpl never.
#[local] Arguments STCRP_option_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_counter : simpl never.
#[local] Arguments complete_ends : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments grind_prp : simpl never.
#[local] Arguments Shrincs.internal.ssprove.wots.params.decode_tweak : simpl never.
#[local] Arguments intermediates.cp_pick : simpl never.
Local Opaque STCRP_option_game.

Lemma r_grind_eval_known {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (q : th_T (thf_hash P) * th_M (thf_hash P))
    (c0 : raw_code B) (k1 : th_N (thf_hash P) -> raw_code B)
    (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (stcr_option_pp_loc (thf_hash P)) = Some pp) ->
  ~~ wcp_grind_class P q.1 ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈ k1 (th_eval (thf_hash P) pp q.1 q.2) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈ bind (resolve SMB (cp_eval_op P) q) k1 ⦃ post ⦄.
Proof.
move=> hpin ht hk.
rewrite r_grind_resolve_eval.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs (stcr_option_pp_loc (thf_hash P)) (Some pp)); first exact: hpin.
cbv beta iota.
exact: hk.
Qed.

Lemma r_grind_walk_spec {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (post : postcond B B) :
  (forall i k, ~~ wcp_grind_class P (chain_tweak P i k)) ->
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (stcr_option_pp_loc (thf_hash P)) = Some pp) ->
  forall n i k (x : wcp_N P) (c0 : raw_code B) (k1 : wcp_N P -> raw_code B),
  (k + n <= (wcp_w P).-1)%N ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ k1 (chainc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp i x k n) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ bind (code_link (cp_walk P i k n x) SMB) k1 ⦃ post ⦄.
Proof.
move=> hsafe hpin.
elim=> [|n ih] i k x c0 k1 hkn hk /=.
- exact: hk.
- rewrite bind_assoc.
  eapply r_grind_eval_known; first exact: hpin.
  + exact: hsafe.
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

Lemma r_grind_chains_spec {B : choiceType} (pp : wcp_PP P)
    (pre : precond) (post : postcond B B) :
  (forall i k, ~~ wcp_grind_class P (chain_tweak P i k)) ->
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (stcr_option_pp_loc (thf_hash P)) = Some pp) ->
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
move=> hsafe hpin.
elim=> [|d ds ih] st K0 K1 hds hk.
- exact: (hk [::] erefl).
- move: hds => /= /andP[hd hds'].
rewrite /= code_link_bind (code_link_scheme _ _ _ _ (prog_valid (wcp_dN P))) !bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> u; cbv beta; rewrite !bind_assoc.
case: d hd hk => [|d'] hd hk.
+ rewrite code_link_bind bind_assoc /=.
rewrite code_link_bind bind_assoc.
eapply (r_grind_walk_spec pp pre post hsafe hpin ((wcp_w P).-1 - 0) st 0 u); first by
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
eapply r_grind_eval_known; first exact: hpin.
* exact: hsafe.
* cbv beta.
rewrite (eval_Fc_E P pp st d' u hd'w) /=.
rewrite (code_link_bind (cp_walk P st d'.+1 ((wcp_w P).-1 - d'.+1) (Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u))) bind_assoc.
eapply (r_grind_walk_spec pp pre post hsafe hpin ((wcp_w P).-1 - d'.+1) st d'.+1 (Fc
  (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp (st, d') u)); first by rewrite (subnKC hd1).
rewrite /= (code_link_bind (cp_chains P st.+1 ds)) bind_assoc.
eapply ih; first exact: hds'.
move=> us hus.
move: (hk (u :: us)); rewrite /= hus => /(_ erefl).
exact: id.
Qed.

End Loops.
