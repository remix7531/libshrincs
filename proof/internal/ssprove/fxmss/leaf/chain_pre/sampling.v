(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.chain_pre.sampling

    Hidden-target sampling and reveal rules for static PRE game. Package invariant
    for the batch chain hop. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.relational_rules chain.core chain.pre_loops toolkit.batch_map.
From Shrincs Require Import games schemes spec.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs.internal.ssprove.fxmss Require Import
  leaf.prepared params shape games instance leaf.known_message_game leaf.known_message
    leaf.prepare
  leaf.chain_pre.reduction leaf.fixed_batch leaf.compress.reduction
    leaf.compress.sampling
  leaf.commitments leaf.opening leaf.paths leaf.compress.pure.
From Shrincs.internal.ssprove.wots Require Import
  params scheme games hop.intermediates hop.chain_common.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages state *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque dBytes Th.

Definition r_chain_pre_private : Locations :=
  [fmap prepared_leaf_pp_loc; pre_pp_loc shrincs_thf; pre_tgts_loc shrincs_thf;
    pre_tws_loc shrincs_thf; pre_rev_loc].
Definition r_chain_pre_block (pp : bytes 16) (rv : bool) (tw : seq tweak)
    (tg : chMap 'nat (tweak × 'list ('word U8))) : precond :=
  fun '(h0, h1) => heap_ignore r_chain_pre_private (h0, h1) /\
    get_heap h0 prepared_leaf_pp_loc = Some pp /\
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp /\
    get_heap h1 pre_rev_loc = rv /\
    get_heap h1 (pre_tws_loc shrincs_thf) = tw /\
    get_heap h1 (pre_tgts_loc shrincs_thf) = tg.

Lemma r_chain_pre_block_targets pp rv tw tg tg' h0 h1 :
  r_chain_pre_block pp rv tw tg (h0, h1) ->
  r_chain_pre_block pp rv tw tg'
    (h0, set_heap h1 (pre_tgts_loc shrincs_thf) tg').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_chain_pre_private; fmap_solve.
- (* Only the target table changes; seeds, reveal flag and tweaks agree. *)
  split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  exact: get_set_heap_eq.
Qed.

Lemma r_chain_pre_block_tweaks pp rv tw tg tw' h0 h1 :
  r_chain_pre_block pp rv tw tg (h0, h1) ->
  r_chain_pre_block pp rv tw' tg
    (h0, set_heap h1 (pre_tws_loc shrincs_thf) tw').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_chain_pre_private; fmap_solve.
- (* Only the tweak list changes; the other recorded values agree. *)
  split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first by rewrite get_set_heap_neq.
  split; first exact: get_set_heap_eq.
  by rewrite get_set_heap_neq.
Qed.

Lemma r_chain_pre_block_reveal pp rv tw tg rv' h0 h1 :
  r_chain_pre_block pp rv tw tg (h0, h1) ->
  r_chain_pre_block pp rv' tw tg (h0, set_heap h1 pre_rev_loc rv').
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; rewrite /r_chain_pre_private; fmap_solve.
- split; first exact: hl.
  split; first by rewrite get_set_heap_neq.
  split; first exact: get_set_heap_eq.
  split; by rewrite get_set_heap_neq.
Qed.

Lemma r_chain_pre_resolve_target p b t :
  resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
    (PQUERY, (tweak, bytes 16)) t =
  (#assert wots_c_hash_class t ;;
   revealed ← get pre_rev_loc ;;
   #assert ~~ revealed ;;
   tws ← get (pre_tws_loc shrincs_thf) ;;
   #assert size tws < p ;;
   #assert t \notin tws ;;
   m ← th_dM shrincs_thf ;;
   tgts ← get (pre_tgts_loc shrincs_thf) ;;
   #put (pre_tgts_loc shrincs_thf) := setm tgts (size tws) (t, m) ;;
   #put (pre_tws_loc shrincs_thf) := rcons tws t ;;
   ppo ← get (pre_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (pre_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp t m)).
Proof.
by rewrite /SMPRE_game /resolve /= coerce_kleisliE.
Qed.

Lemma r_chain_pre_target_spec p b {B : choiceType} pp tw tg t
    (k0 : bytes 16 -> raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  wots_c_hash_class t -> size tw < p -> t \notin tw ->
  (forall x, ⊢ ⦃ fun '(h0, h1) =>
    r_chain_pre_block pp false (rcons tw t) (setm tg (size tw) (t, tval x)) (h0, h1) ⦄
    k0 x ≈ k1 (Th pp t (tval x)) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_chain_pre_block pp false tw tg (h0, h1) ⦄
    bind (dBytes 16) k0 ≈ bind (resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
      (PQUERY, (tweak, bytes 16)) t) k1 ⦃ post ⦄.
Proof.
move=> hcl hbudget hfresh hk.
rewrite r_chain_pre_resolve_target.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs pre_rev_loc false); first by move=> h0 h1 [_ [_ [_ [hr _]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs (pre_tws_loc shrincs_thf) tw); first by move=> h0 h1 [_ [_ [_ [_ [ht _]]]]].
cbv beta iota.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply r_bind_assertD_rhs; first by [].
move=> _.
change (th_dM shrincs_thf) with {code x ← dBytes 16 ;; ret (tval x)}.
remember (dBytes 16) as dn eqn:hdn.
rewrite !bind_assoc.
eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
move=> x; cbv beta.
cbn [bind].
eapply (r_get_rhs_pin (pre_tgts_loc shrincs_thf) tg); first by move=> h0 h1 [_ [_ [_ [_ [_ ht]]]]].
cbv beta iota.
eapply (r_put_rhs_weak (pre_tgts_loc shrincs_thf) (setm tg (size tw) (t, tval x)) _
  (r_chain_pre_block pp false tw (setm tg (size tw) (t, tval x)))).
- move=> h0 h1 hp.
exact: r_chain_pre_block_targets hp.
- eapply (r_put_rhs_weak (pre_tws_loc shrincs_thf) (rcons tw t) _ (r_chain_pre_block pp
  false (rcons tw t) (setm tg (size tw) (t, tval x)))).
+ move=> h0 h1 hp.
exact: r_chain_pre_block_tweaks hp.
+ eapply (r_get_rhs_pin (pre_pp_loc shrincs_thf) (Some pp)); first by move=> h0 h1 [_ [_ [hr _]]].
cbn [bind].
exact: (hk x).
Qed.

Lemma r_chain_pre_resolve_reveal p b :
  resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
    (PGETPP, ('unit, bytes 16)) tt =
  (ppo ← get (pre_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (pre_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   #put pre_rev_loc := true ;;
   ret pp).
Proof.
by rewrite /SMPRE_game /resolve /= coerce_kleisliE.
Qed.

Lemma r_chain_pre_reveal_spec p b {B : choiceType} pp rv tw tg
    (c0 : raw_code B) (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ fun '(h0, h1) => r_chain_pre_block pp true tw tg (h0, h1) ⦄
    c0 ≈ k1 pp ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => r_chain_pre_block pp rv tw tg (h0, h1) ⦄
    c0 ≈ bind (resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
      (PGETPP, ('unit, bytes 16)) tt) k1 ⦃ post ⦄.
Proof.
move=> hk.
rewrite r_chain_pre_resolve_reveal.
eapply (r_get_bind_rhs (pre_pp_loc shrincs_thf) (Some pp));
  first by move=> h0 h1 [_ [_ [hr _]]].
cbv beta iota.
eapply (r_put_bind_rhs pre_rev_loc true _ (r_chain_pre_block pp true tw tg)).
- move=> h0 h1 hp.
exact: r_chain_pre_block_reveal hp.
- exact: hk.
Qed.

Lemma r_chain_pre_resolve_check p b j m :
  resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
    (PCHECK, ('nat × 'list ('word U8), 'bool)) (j, m) =
  (revealed ← get pre_rev_loc ;;
   #assert revealed ;;
   if b then
     tgts ← get (pre_tgts_loc shrincs_thf) ;;
     match getm tgts j with
     | Some (t0, m0) =>
       ppo ← get (pre_pp_loc shrincs_thf) ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dBytes 16 ;;
                      #put (pre_pp_loc shrincs_thf) := Some pp ;; ret pp
            end ;;
       ret (Th pp t0 m == Th pp t0 m0)
     | None => ret false
     end
   else ret false).
Proof.
by rewrite /SMPRE_game /resolve /= coerce_kleisliE.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages loops *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque Th.

Lemma r_chain_pre_resolve_eval p b q :
  resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
    (EVAL, (tweak × 'list ('word U8), bytes 16)) q =
  (#assert ~~ wots_c_hash_class q.1 ;;
   ppo ← get (pre_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← th_dPP shrincs_thf ;;
                  #put (pre_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ret (Th pp q.1 q.2)).
Proof. by case: q => t m; rewrite /SMPRE_game /resolve /= coerce_kleisliE. Qed.

Lemma r_chain_pre_grind_spec p b sp a pp md cs
    {B C : choiceType} (pre : precond) (post : postcond B C)
    (c0 : raw_code B) (k : chList (bytes 16) -> raw_code C) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp) ->
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    k [seq wcp_H_grind W pp (grind_adrs W) (md, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄ c0 ≈
    bind (code_link (grind_loop W md cs)
      (SMPRE_game shrincs_thf wots_c_hash_class p b)) k ⦃ post ⦄.
Proof.
move=> hpin /=.
elim: cs k => [|c cs ih] k hk.
- exact: hk.
- cbn [grind_loop code_link].
  rewrite bind_assoc r_chain_pre_resolve_eval.
  eapply r_bind_assertD_rhs.
  + by move=> h0 h1 _.
  + (* An allowed evaluation uses the pinned seed before the remaining search. *)
    move=> _.
    eapply (r_get_rhs_pin (pre_pp_loc shrincs_thf) (Some pp));
      first exact: hpin.
    cbn [bind].
    rewrite code_link_bind bind_assoc.
    apply: ih.
    exact: hk.
Qed.

Definition r_chain_pre_prefix sp pp a (pre : seq (tweak * seq UInt8))
    (Q : seq ((nat * nat) * bytes 16)) : precond :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let targets := pre ++ [seq wq W q | q <- Q] in
  r_chain_pre_block pp false (unzip1 targets) (qmap_from 0 targets).

Lemma r_chain_pre_query_prefix_spec p b {B : choiceType} sp pp a pre
    (post : postcond B B) :
  (forall i k, i < 32 -> k < 15 ->
    chain_tweak (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) i
      k
      \notin unzip1 pre) ->
  size pre + 32 <= p ->
  pre_query_spec (bytes 16) (bytes 16) 32 16 (32)
    (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
    (dBytes 16) (fun i k => code_link (r_chain_pre_query sp a i k)
      (SMPRE_game shrincs_thf wots_c_hash_class p b))
    pp (r_chain_pre_prefix sp pp a pre) post.
Proof.
move=> hpre hbudget i k Q k0 k1 hi hk hQr hQbudget hfresh hcont.
set W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2).
have hclass : wots_c_hash_class (chain_tweak W i k).
{ exact: (wcp_tw_chain_class W i k). }
have hbudget' : size (unzip1 (pre ++ [seq wq W q | q <- Q])) < p.
{ rewrite /unzip1 size_map size_cat size_map.
  apply: leq_trans hbudget.
  by rewrite ltn_add2l. }
have hfresh' : chain_tweak W i k \notin
    unzip1 (pre ++ [seq wq W q | q <- Q]).
{ rewrite unzip1_cat mem_cat negb_or; apply/andP; split.
  - exact: hpre.
  - rewrite unzip1_wq.
    apply: (wtw_notin W (i, k) (unzip1 Q) hi hk _ hfresh).
    move=> t ht; have /andP[ht1 ht2] := allP hQr t ht.
    by split. }
rewrite /r_chain_pre_query; cbn [code_link].
rewrite bind_ret.
rewrite /r_chain_pre_prefix.
eapply (r_chain_pre_target_spec p b) => //.
move=> x.
have hkw : k < 16 := ltn_trans hk (ltnSn 15).
have hhash : Th pp (chain_tweak W i k) (tval x) =
    Fc (bytes 16) (bytes 16) 16 (Fw W) pp (i, k) x :=
  Fc_wtw W pp (i, k) x hkw.
rewrite hhash.
move: (hcont x).
rewrite /r_chain_pre_prefix map_rcons -rcons_cat /unzip1 map_rcons
  qmap_from_rcons add0n size_map.
by [].
Qed.

Lemma r_chain_pre_chains_spec p b {B : choiceType} sp pp a ds pre
    (K0 : seq (bytes 16) -> raw_code B)
    (K1 : seq (bytes 16) -> raw_code B)
    (post : postcond B B) :
  size ds = 32 -> all (fun d => d < 16) ds ->
  (forall i k, i < 32 -> k < 15 ->
    chain_tweak (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) i
      k
      \notin unzip1 pre) ->
  size pre + 32 <= p ->
  (forall us, size us = 32 ->
    let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
    ⊢ ⦃ fun '(h0, h1) =>
        r_chain_pre_prefix sp pp a pre (pre_queries (bytes 16) 0 ds us) (h0, h1) ⦄
      K0 (wsigs W pp 0 ds us) ≈
      K1 (wsigs W pp 0 ds us)
    ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_chain_pre_block pp false
      (unzip1 pre) (qmap_from 0 pre) (h0, h1) ⦄
    bind (sample_sig_roots (bytes 16) (bytes 16) 16
      (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
      (dBytes 16) pp 0 ds) K0 ≈
    bind (code_link (r_chain_pre_chains sp a ds)
      (SMPRE_game shrincs_thf wots_c_hash_class p b)) K1 ⦃ post ⦄.
Proof.
move=> hlen hds hpre hbudget hcont.
rewrite /r_chain_pre_chains pre_chains_link.
have hnil : r_chain_pre_prefix sp pp a pre [::] =
    r_chain_pre_block pp false (unzip1 pre) (qmap_from 0 pre).
{ by rewrite /r_chain_pre_prefix /= cats0. }
rewrite -hnil.
apply: (pre_chains_spec (bytes 16) (bytes 16) 32 16
  (32)
  (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
  (dBytes 16) _ pp (r_chain_pre_prefix sp pp a pre) post isT).
- exact: r_chain_pre_query_prefix_spec hpre hbudget.
- by rewrite add0n hlen.
- exact: hds.
- by [].
- rewrite add0n.
  exact: npq_le hlen.
- by [].
- move=> us hus.
  apply: hcont.
  by rewrite hus.
Qed.

Lemma r_chain_pre_eval_known p b {B : choiceType} pp (pre : precond)
    (q : tweak * seq UInt8) (c0 : raw_code B)
    (k1 : bytes 16 -> raw_code B) (post : postcond B B) :
  (forall h0 h1, pre (h0, h1) ->
    get_heap h1 (pre_pp_loc shrincs_thf) = Some pp) ->
  ~~ wots_c_hash_class q.1 ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ k1 (Th pp q.1 q.2) ⦃ post ⦄ ->
  ⊢ ⦃ fun '(h0, h1) => pre (h0, h1) ⦄
    c0 ≈ bind (resolve (SMPRE_game shrincs_thf wots_c_hash_class p b)
      (EVAL, (tweak × 'list ('word U8), bytes 16)) q) k1 ⦃ post ⦄.
Proof.
move=> hpin hclass hcont.
rewrite r_chain_pre_resolve_eval.
eapply r_bind_assertD_rhs; first by move=> h0 h1 _.
move=> _.
eapply (r_get_bind_rhs (pre_pp_loc shrincs_thf) (Some pp)); first exact: hpin.
cbv beta iota.
exact: hcont.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque Th dBytes r_chain_pre_block.

Definition r_chain_pre_result_of sp pp a md us : r_chain_pre_result :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let ds := known_message_digits shrincs_fxmss_sha256 sp pp a md in
  ((wsigs W pp 0 ds us, ds), known_message_find shrincs_fxmss_sha256 sp pp a md).

Lemma r_chain_pre_complete_result sp pp a md us :
  r_chain_pre_complete sp pp a (r_chain_pre_result_of sp pp a md us) =
  r_compress_sample_entry sp pp a md us.
Proof. by []. Qed.

Lemma r_chain_pre_one_spec p b {B : choiceType} sp pp a md pre
    (K0 : prepared_leaf_entry -> raw_code B) (K1 : r_chain_pre_result -> raw_code B)
    (post : postcond B B) :
  a \notin [seq t.1.1.1.1 | t <- unzip1 pre] ->
  size pre + 32 <= p ->
  (forall us, size us = 32 ->
    let entry := r_compress_sample_entry sp pp a md us in
    ⊢ ⦃ fun '(h0, h1) => r_chain_pre_block pp false
      (unzip1 (pre ++ r_chain_pre_targets sp pp a md us))
      (qmap_from 0 (pre ++ r_chain_pre_targets sp pp a md us)) (h0, h1) ⦄
      K0 entry ≈ K1 (r_chain_pre_result_of sp pp a md us) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => r_chain_pre_block pp false (unzip1 pre) (qmap_from 0 pre) (h0,
    h1) ⦄
    bind (prepared_leaf_sample sp pp a md) K0 ≈
    bind (code_link (r_chain_pre_one sp a md)
      (SMPRE_game shrincs_thf wots_c_hash_class p b)) K1 ⦃ post ⦄.
Proof.
move=> hfresh hbudget hk.
rewrite /r_chain_pre_one /leaf_grind_one code_link_bind bind_assoc.
rewrite code_link_bind bind_assoc.
eapply (r_chain_pre_grind_spec p b sp a pp md _ (r_chain_pre_block pp false (unzip1 pre)
  (qmap_from 0 pre))).
- by move=> h0 h1 [_ [_ [hr _]]].
- cbn [code_link bind].
rewrite leaf_grind_pick_map known_message_prepared_digits.
rewrite /prepared_leaf_sample code_link_bind !bind_assoc.
eapply (r_chain_pre_chains_spec p b sp pp a _ pre).
+ exact: known_message_digits_length.
+ exact: r_compress_digits_wf.
+ (* The head leaf's chain tweaks are absent from the prefix. *)
  move=> i k hi hk'.
  apply/negP => ht.
  have hm := map_f (fun t : tweak => t.1.1.1.1) ht.
  rewrite r_chain_pre_target_coordinate in hm.
  by move: hfresh; rewrite hm.
+ exact: hbudget.
+ move=> us hus.
cbv zeta.
cbn [code_link bind].
rewrite /known_message_prepared_leaf.
have hc : omap fst (omap (fun c => (c, digest_of (shrincs_fxmss_leaf_params
  shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) pp md c)) (known_message_find
    shrincs_fxmss_sha256 sp
  pp a md)) = known_message_find shrincs_fxmss_sha256 sp pp a md by case:
    known_message_find.
rewrite hc.
rewrite /r_chain_pre_prefix.
apply: hk.
exact: hus.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages batch *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
Local Opaque Th dBytes prepared_leaf_sample r_chain_pre_one r_chain_pre_block
  r_chain_pre_result_of.
Local Opaque bind code_link.

Definition r_chain_pre_results sp pp sd (ats : seq shrincs_fxmss_coord)
    (uss : seq (seq (bytes 16))) : seq r_chain_pre_result :=
  [seq r_chain_pre_result_of sp pp au.1 (leaf_committed_digest sd au.1) au.2
    | au <- zip ats uss].

Lemma r_chain_pre_complete_results sp pp sd uss :
  size uss = size (shrincs_fxmss_schedule sp) ->
  r_chain_pre_complete_batch sp pp (r_chain_pre_results sp pp sd (shrincs_fxmss_schedule
    sp) uss) =
  r_chain_pre_entries sp pp sd (shrincs_fxmss_schedule sp) uss.
Proof.
rewrite /r_chain_pre_complete_batch /r_chain_pre_results /r_chain_pre_entries.
elim: (shrincs_fxmss_schedule sp) uss => [|a ats ih] [|us uss] //= [hlen].
by rewrite r_chain_pre_complete_result ih.
Qed.

Lemma r_chain_pre_batch_spec p b {B : choiceType} sp pp sd ats pre
    (K0 : seq prepared_leaf_entry -> raw_code B)
    (K1 : seq r_chain_pre_result -> raw_code B) (post : postcond B B) :
  uniq ats -> all (fun a => a \notin [seq t.1.1.1.1 | t <- unzip1 pre]) ats ->
  size pre + size ats * 32 <= p ->
  (forall uss, size uss = size ats -> all (fun us => size us == 32) uss ->
    let entries := r_chain_pre_entries sp pp sd ats uss in
    let targets := pre ++ r_chain_pre_queries sp pp sd ats uss in
    ⊢ ⦃ fun '(h0, h1) =>
      r_chain_pre_block pp false (unzip1 targets) (qmap_from 0 targets) (h0, h1) ⦄
      K0 entries ≈ K1 (r_chain_pre_results sp pp sd ats uss) ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) =>
    r_chain_pre_block pp false (unzip1 pre) (qmap_from 0 pre) (h0, h1) ⦄
    bind (query_list (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd
      a)) ats) K0 ≈
    bind (code_link (query_list (fun a => r_chain_pre_one sp a (leaf_committed_digest sd
      a)) ats)
      (SMPRE_game shrincs_thf wots_c_hash_class p b)) K1 ⦃ post ⦄.
Proof.
remember (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd a)) as qs
  eqn:hqs.
remember (fun a => r_chain_pre_one sp a (leaf_committed_digest sd a)) as qr eqn:hqr.
elim: ats pre K0 K1 => [|a ats ih] pre K0 K1 hu hf hb hc.
- have := hc [::] erefl isT.
  by rewrite /r_chain_pre_queries /= cats0.
- move: hu => /= /andP[hnot hu].
  move: hf => /= /andP[hfresh hf].
  have hb' : size pre + 32 <= p.
  { apply: leq_trans hb.
    by rewrite /= mulSn addnA leq_addr. }
  cbn [query_list].
  rewrite code_link_bind !bind_assoc.
  rewrite (congr1 (fun f => f a) hqs) (congr1 (fun f => f a) hqr).
  eapply r_chain_pre_one_spec; [exact: hfresh | exact: hb' |].
  move=> us hus; cbv zeta.
  rewrite code_link_bind !bind_assoc.
  eapply ih; first exact: hu.
  + apply/allP => a' ha'.
    rewrite unzip1_cat map_cat mem_cat negb_or; apply/andP; split.
    * exact: (allP hf a' ha').
    * apply/negP => /mapP[t ht he].
      have /eqP hcoord := allP
        (r_chain_pre_targets_coordinate sp pp a (leaf_committed_digest sd a) us) t ht.
      by move: ha'; rewrite he hcoord (negbTE hnot).
  + (* The remaining leaves fit within the query budget. *)
    apply: leq_trans hb.
    rewrite size_cat /= mulSn addnA leq_add2r leq_add2l.
    apply: leq_trans (r_chain_pre_targets_budget sp pp a (leaf_committed_digest sd a)
      us hus) _.
    by [].
  + (* Prepending the sampled head preserves lengths and block sizes. *)
    move=> uss hlen huss.
    have hlen' : size (us :: uss) = size (a :: ats) by rewrite /= hlen.
    have huss' : all (fun us => size us == 32) (us :: uss).
    { by rewrite /= hus eqxx. }
    have := hc (us :: uss) hlen' huss'.
    by rewrite /r_chain_pre_queries /r_chain_pre_entries /r_chain_pre_results /= catA.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain preimages invariant *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition r_chain_pre_rel (po0 po1 : option (bytes 16)) (st : option
  leaf_opening_state)
    (sd : shrincs_fxmss_digest_table) (entries : seq prepared_leaf_entry) (rv : bool)
      (tw : seq
      tweak)
    (tg : chMap 'nat (tweak × 'list ('word U8))) : Prop :=
  po0 = po1 /\
  match st with
  | None => rv = false /\ tw = [::] /\ tg = emptym
  | Some (pp, sp) =>
      po0 = Some pp /\ rv = true /\
      shrincs_fxmss_structure_legal sp.1 sp.2 /\
      exists uss, size uss = size (shrincs_fxmss_schedule sp) /\
        all (fun us => size us == 32) uss /\
        entries = r_chain_pre_entries sp pp sd (shrincs_fxmss_schedule sp) uss /\
        tw = unzip1 (r_chain_pre_queries sp pp sd (shrincs_fxmss_schedule sp) uss) /\
        tg = qmap_from 0 (r_chain_pre_queries sp pp sd (shrincs_fxmss_schedule sp) uss)
  end.

Definition r_chain_pre_inv : precond :=
  heap_ignore r_chain_pre_private ⋊
  rel_app [:: (lhs, prepared_leaf_pp_loc); (rhs, pre_pp_loc shrincs_thf);
    (lhs, prepared_leaf_st_loc); (lhs, prepared_leaf_sd_loc); (lhs,
      prepared_leaf_entries_loc); (rhs, pre_rev_loc);
    (rhs, pre_tws_loc shrincs_thf); (rhs, pre_tgts_loc shrincs_thf)] r_chain_pre_rel.

Lemma r_chain_pre_inv_invariant r b :
  Invariant (loc (G_prepared_leaf r))
    (unionm (loc R_chain_pre)
      (loc (SMPRE_game shrincs_thf wots_c_hash_class r_chain_pre_budget b)))
        r_chain_pre_inv.
Proof.
rewrite /r_chain_pre_inv.
ssprove_invariant.
by rewrite /rel_empty /r_chain_pre_rel /=.
Qed.

Lemma r_chain_pre_invE h0 h1 :
  r_chain_pre_inv (h0, h1) ->
  heap_ignore r_chain_pre_private (h0, h1) /\
  r_chain_pre_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (pre_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_sd_loc)
    (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 pre_rev_loc) (get_heap h1 (pre_tws_loc shrincs_thf))
    (get_heap h1 (pre_tgts_loc shrincs_thf)).
Proof.
by [].
Qed.

Lemma r_chain_pre_invI h0 h1 :
  heap_ignore r_chain_pre_private (h0, h1) ->
  r_chain_pre_rel (get_heap h0 prepared_leaf_pp_loc) (get_heap h1 (pre_pp_loc
    shrincs_thf))
    (get_heap h0 prepared_leaf_st_loc) (get_heap h0 prepared_leaf_sd_loc)
    (get_heap h0 prepared_leaf_entries_loc)
    (get_heap h1 pre_rev_loc) (get_heap h1 (pre_tws_loc shrincs_thf))
    (get_heap h1 (pre_tgts_loc shrincs_thf)) ->
  r_chain_pre_inv (h0, h1).
Proof.
by move=> hi hr; split.
Qed.

Lemma r_chain_pre_inv_start pp h0 h1 :
  r_chain_pre_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  get_heap h0 prepared_leaf_pp_loc = Some pp ->
  r_chain_pre_block pp false [::] emptym (h0, h1).
Proof.
move=> /r_chain_pre_invE [hi [he hr]] hs hp.
rewrite hs in hr.
move: hr => [hv [hw ht]].
by split; [exact: hi | split; [exact: hp | split; [rewrite -he | repeat split]]].
Qed.

Lemma r_chain_pre_inv_finish pp sp sd uss h0 h1 :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size uss = size (shrincs_fxmss_schedule sp) -> all (fun us => size us == 32) uss ->
  r_chain_pre_block pp true (unzip1 (r_chain_pre_queries sp pp sd
    (shrincs_fxmss_schedule sp) uss))
    (qmap_from 0 (r_chain_pre_queries sp pp sd (shrincs_fxmss_schedule sp) uss)) (h0,
      h1) ->
  let entries := r_chain_pre_entries sp pp sd (shrincs_fxmss_schedule sp) uss in
  r_chain_pre_inv (r_compress_stored pp sp sd entries h0, r_compress_stored pp sp sd
    entries h1).
Proof.
move=> hsp hlen huss [hi [hl [hr [hv [hw ht]]]]] entries.
apply: r_chain_pre_invI.
- rewrite /r_compress_stored.
  do 3 apply: put_pre_cond_heap_ignore.
  exact: hi.
- (* Stored entries and target records satisfy the preimage relation. *)
  rewrite /r_compress_stored /r_chain_pre_rel.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite hl hr hv hw ht.
  repeat split => //.
  exists uss; repeat split => //.
Qed.

Lemma r_chain_pre_inv_seed_eq h0 h1 :
  r_chain_pre_inv (h0, h1) ->
  get_heap h0 prepared_leaf_pp_loc = get_heap h1 (pre_pp_loc shrincs_thf).
Proof.
by move=> /r_chain_pre_invE [_ [he _]].
Qed.

Lemma r_chain_pre_inv_no_seed h0 h1 :
  r_chain_pre_inv (h0, h1) -> get_heap h0 prepared_leaf_pp_loc = None ->
  get_heap h0 prepared_leaf_st_loc = None.
Proof.
move=> /r_chain_pre_invE [hi [he hr]] hp.
case hs: (get_heap h0 prepared_leaf_st_loc) hr => [[pp sp]|] //.
by rewrite /r_chain_pre_rel hp => -[].
Qed.

Lemma r_chain_pre_inv_pin pp h0 h1 :
  r_chain_pre_inv (h0, h1) -> get_heap h0 prepared_leaf_st_loc = None ->
  r_chain_pre_block pp false [::] emptym
    (set_heap h0 prepared_leaf_pp_loc (Some pp),
     set_heap h1 (pre_pp_loc shrincs_thf) (Some pp)).
Proof.
move=> /r_chain_pre_invE [hi [he hr]] hs.
rewrite hs in hr.
move: hr => [hv [hw ht]].
split.
- apply: heap_ignore_set_l.
  + by apply: fhas_in; rewrite /r_chain_pre_private; fmap_solve.
  + apply: heap_ignore_set_r hi.
    by apply: fhas_in; rewrite /r_chain_pre_private; fmap_solve.
- split; first exact: get_set_heap_eq.
  split; first exact: get_set_heap_eq.
  by rewrite !get_set_heap_neq //; repeat split.
Qed.

Lemma r_chain_pre_block_initial_inv pp h0 h1 :
  r_chain_pre_block pp false [::] emptym (h0, h1) ->
  get_heap h0 prepared_leaf_st_loc = None -> r_chain_pre_inv (h0, h1).
Proof.
move=> [hi [hl [hr [hv [hw ht]]]]] hs.
apply: r_chain_pre_invI hi _.
by rewrite /r_chain_pre_rel hl hr hs hv hw ht.
Qed.
