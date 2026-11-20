(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.keys_ideal

    The ideal chain-start PRF simulation couples generation, signing and shared
    oracle calls. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.prf_memo games.prf_memo_state games.prf_memo_coupling
  toolkit.relational_rules toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance prf.inputs prf.reduction prf.sampling.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF coupling *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition prf_ideal_private : Locations :=
  [fmap shrincs_fxmss_ks_loc; prf_memo_tab_loc shrincs_khf_prf; prf_memo_cnt_loc;
    prf.prf_k_loc shrincs_khf_prf; prf.prf_qs_loc shrincs_khf_prf].

Definition prf_ideal_rel (sto : option shrincs_fxmss_state)
    (tab : {fmap kh_M shrincs_khf_prf -> bytes 16})
    (qs : seq (kh_M shrincs_khf_prf)) (cnt : nat)
    (ks0 ks1 : option (bytes 16)) : Prop :=
  (sto = None -> [/\ tab = emptym, qs = [::] & cnt = 0]) /\
  isSome ks0 = isSome ks1.

Definition prf_ideal_inv : precond :=
  heap_ignore prf_ideal_private ⋊ rel_app
    [:: (lhs, shrincs_fxmss_st_loc); (rhs, prf_memo_tab_loc shrincs_khf_prf);
        (rhs, prf.prf_qs_loc shrincs_khf_prf); (rhs, prf_memo_cnt_loc);
        (lhs, shrincs_fxmss_ks_loc); (rhs, shrincs_fxmss_ks_loc)] prf_ideal_rel.

Lemma prf_ideal_inv_invariant Q bit :
  Invariant (loc (G_forge_sampledkey shrincs_fxmss_sha256 Q bit))
    (unionm (loc (R_prf_memo Q bit))
      (unionm (loc (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
        (loc (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false))))
    prf_ideal_inv.
Proof.
cbv beta iota delta [prf_ideal_inv].
ssprove_invariant.
(cbv beta iota delta [prf_ideal_rel]; rewrite /rel_empty /=).
by split; [move=> _; split|].
Qed.

Lemma prf_ideal_inv_put (l : Location) (v : l) :
  l.1 \notin [:: shrincs_fxmss_st_loc.1; (prf_memo_tab_loc shrincs_khf_prf).1;
    (prf.prf_qs_loc shrincs_khf_prf).1; prf_memo_cnt_loc.1; shrincs_fxmss_ks_loc.1] ->
  put_pre_cond l v prf_ideal_inv.
Proof.
move=> hl.
cbv beta iota delta [prf_ideal_inv].
apply: put_pre_cond_conj; first exact: put_pre_cond_heap_ignore.
apply: put_pre_cond_rel_app.
by move: hl; rewrite /= !in_cons !orbF orbb.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_ideal_rel get_heap set_heap.

Lemma prf_ideal_inv_gen st ks kp kt s0 s1 :
  heap_ignore prf_ideal_private (s0,s1) ->
  prf_ideal_inv
    (set_heap (set_heap (set_heap (set_heap (set_heap s0
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks))
        shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc emptym,
     set_heap (set_heap (set_heap (set_heap (set_heap s1
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some (zeros 16)))
        shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc emptym).
Proof.
move=> hi.
cbv beta iota delta [prf_ideal_inv].
split.
-
  do 3 apply: put_pre_cond_heap_ignore.
  apply: heap_ignore_set_l;
    first by rewrite /prf_ideal_private !domm_set !in_fset1U /=.
  apply: heap_ignore_set_r;
    first by rewrite /prf_ideal_private !domm_set !in_fset1U /=.
  apply: put_pre_cond_heap_ignore.
  exact: hi.
- rewrite !rel_app_cons /= rel_app_nil.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_st_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_st_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_st_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ shrincs_fxmss_st_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq s0 shrincs_fxmss_st_loc (Some st)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_ks_loc (Some ks)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_ks_loc (Some (zeros 16))) at 1.

cbv beta iota delta [prf_ideal_rel].
split; [discriminate|reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF common *)

Import Shrincs.internal.ssprove.fxmss.games.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_ideal_inv prf_ideal_rel scheme.shrincs_fxmss_node
  scheme.shrincs_fxmss_verify dBytes shrincs_fxmss_sample_keys kh_eval.

Lemma R_prf_ideal_hash (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_hmsg_input) :
  ⊢ ⦃ fun '(s0, s1) => prf_ideal_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false)%share
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_ideal_inv (s0, s1) ⦄.
Proof.
simplify_linking.
fold @code_link.

ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
}
move=> done.
fold @code_link.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => have hv :
  ValidCode [fmap shrincs_fxmss_done_loc; shrincs_fxmss_hcnt_loc;
    shrincs_fxmss_rom_loc] emptym c by ssprove_valid end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => rewrite
  (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end.
apply: (r_reflexivity_alt prf_ideal_inv _ hv).
-
  move=> l hl s0 s1 [hi hr].
  apply: hi.
  by fmap_invert hl; fmap_solve.
-
  move=> l v hl.
  apply: prf_ideal_inv_put.
  by fmap_invert hl.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_ideal_inv prf_ideal_rel dBytes shrincs_fxmss_sample_keys
  kh_eval scheme.shrincs_fxmss_node scheme.shrincs_fxmss_verify.

Lemma R_prf_ideal_forge (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_message × shrincs_fxmss_bytes) :
  ⊢ ⦃ fun '(s0, s1) => prf_ideal_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) shrincs_fxmss_forge_op arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false)%share
      shrincs_fxmss_forge_op arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_ideal_inv (s0, s1) ⦄.
Proof.
simplify_linking.
case: arg => cm sg.
fold @code_link.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
  have hv : ValidCode shrincs_fxmss_locs emptym c by ssprove_valid end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
  rewrite (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end.

clear hv.
ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
}
move=> sto.
ssprove_code_simpl.
eapply (r_reflexivity_alt
  (L := [fmap shrincs_fxmss_done_loc; shrincs_fxmss_log_loc; shrincs_fxmss_keys_loc;
    shrincs_fxmss_sd_loc; shrincs_fxmss_rt_loc; shrincs_fxmss_rom_loc])
  prf_ideal_inv _ (ltac:(ssprove_valid))).
-
  move=> l hl s0 s1 [hi hr].
  apply: hi.
  by fmap_invert hl; fmap_solve.
-
  move=> l v hl.
  apply: prf_ideal_inv_put.
  by fmap_invert hl.
Unshelve.
ssprove_valid.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF gen *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys shrincs_fxmss_prf_derive_table
  shrincs_fxmss_prf_derive_leaf.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque scheme.shrincs_fxmss_node prf_ideal_inv prf_ideal_rel get_heap
  set_heap prf_memo_rel.

Lemma R_prf_ideal_gen (Q : shrincs_fxmss_resources) (bit : bool) (arg :
  shrincs_fxmss_setup) :
  ⊢ ⦃ fun '(s0, s1) => prf_ideal_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_gen,
      (shrincs_fxmss_setup, bytes 48)) arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false)%share
      (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_ideal_inv (s0, s1) ⦄.
Proof.
simplify_linking.

ssprove_code_simpl.
eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{
  move=> s0 s1 [[hi hr] hs].
  have he := hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hs.
}
ssprove_code_simpl.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hsto _.
case: sto hsto => [st|] hsto; first discriminate.
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{
  move=> s0 s1 [[[hi hr] hs] hd].
  have he := hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hd.
}
fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hdone _.
eapply r_assertD; first by [].
move=> hlegal _.
eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
  prf_memo_rel shrincs_khf_prf prf_ideal_private [::] 0 (s0,s1)); last first.
{
  move=> s0 s1 [[[hi hr] hs] hd].
  rewrite /rem_inv /get_side /= in hs.
  (cbv beta iota delta [prf_ideal_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
  case: hr => hinit hks.
  have [ht hq hc] := hinit erefl.
  split; first exact: hi.
  rewrite /rel_app /get_side /= ht hq hc.
  split; try reflexivity.
  exact: prf_memo_log_empty.
}

rewrite (code_link_bind (dBytes 16))
  (code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
rewrite (code_link_bind (dBytes 16))
  (code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
eapply r_scheme_bind; first exact: prog_valid.
move=> pp; cbv beta.
lazymatch goal with |- context [@opr ?A ?o ?x ?k] =>
  change (@opr A o x k) with (bind (opr o x (fun y => ret y)) k) end.
rewrite (code_link_bind (opr _ _ (fun y => ret y))).
rewrite (code_link_bind (code_link (opr _ _ (fun y => ret y)) _)).
eapply r_bind with (mid := fun '(ks0,s0) '(ks1,s1) => ks0 = ks1 /\
  prf_memo_rel shrincs_khf_prf prf_ideal_private [:: shrincs_fxmss_prf_pin pp] 1
    (s0,s1)).
-
  rewrite !bind_ret.
  change (⊢ ⦃ fun '(s0,s1) =>
      prf_memo_rel shrincs_khf_prf prf_ideal_private [::] 0 (s0,s1) ⦄
    kh_dN shrincs_khf_prf
    ≈ code_link (code_link
        (call [ MQUERY ] : { kh_M shrincs_khf_prf ~> bytes 16 } (shrincs_fxmss_prf_pin
          pp))
        (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
        (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false)
    ⦃ fun '(ks0,s0) '(ks1,s1) => ks0 = ks1 /\
      prf_memo_rel shrincs_khf_prf prf_ideal_private
        [:: shrincs_fxmss_prf_pin pp] 1 (s0,s1) ⦄).
  lazymatch goal with |- context [code_link (@opr ?A ?o ?x ?k) ?p] =>
    change (code_link (@opr A o x k) p)
      with (bind (resolve p o x) (fun y => ret y)) end.
  rewrite bind_ret.
  apply: r_prf_memo_ideal_fresh;
    try by rewrite /prf_ideal_private !domm_set !in_fset1U /=.
  + by [].
  + by rewrite /shrincs_fxmss_prf_budget.
-
  move=> ks0 ks1.
  eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
    prf_memo_rel shrincs_khf_prf prf_ideal_private [:: shrincs_fxmss_prf_pin pp] 1
      (s0,s1));
    last by move=> s0 s1 [_ hr].
  rewrite (code_link_bind (dBytes 16))
    (code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
  rewrite (code_link_bind (dBytes 16))
    (code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> kp; cbv beta.
  rewrite (code_link_bind (shrincs_fxmss_prf_derive_table pp arg.1.1
    (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1))).
  rewrite (code_link_bind (code_link (shrincs_fxmss_prf_derive_table pp arg.1.1
    (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1)) _)).
  eapply r_bind with (mid := fun '(kt0,s0) '(kt1,s1) => kt0 = kt1 /\
    prf_memo_rel shrincs_khf_prf prf_ideal_private
      (shrincs_fxmss_prf_pin pp ::
        Shrincs.internal.ssprove.fxmss.prf.schedule.shrincs_fxmss_prf_queries pp
        arg.1.1
        (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1))
      (size (shrincs_fxmss_schedule arg.1) * wots_c_chain_count).+1 (s0,s1)).
  +
    apply: r_prf_ideal_schedule;
      try by rewrite /prf_ideal_private !domm_set !in_fset1U /=.
    exact: hlegal.
  +
    move=> kt0 kt1.
    eapply (@r_fact (bytes 48) (bytes 48) (kt0 = kt1)
      (fun '(s0,s1) => kt0 = kt1 /\
        prf_memo_rel shrincs_khf_prf prf_ideal_private
          (shrincs_fxmss_prf_pin pp ::
            Shrincs.internal.ssprove.fxmss.prf.schedule.shrincs_fxmss_prf_queries pp
            arg.1.1
            (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1))
          (size (shrincs_fxmss_schedule arg.1) * wots_c_chain_count).+1 (s0,s1)));
      first by move=> s0 s1 [he hr].
    move=> ->.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) =>
      heap_ignore prf_ideal_private (s0,s1));
      last by move=> s0 s1 [_ [hi hr]].
    rewrite !code_link_assertD.
    ssprove_code_simpl.
    eapply (@r_assertD (bytes 48) (bytes 48)); first by [].
    move=> hroot _.
    simplify_linking.
    eapply (r_put_lhs _ _ _ _
      (fun '(s0,s1) => heap_ignore prf_ideal_private (s0,s1))).
    do 4 apply r_put_lhs.
    do 5 apply r_put_rhs.
    apply r_ret.
    move=> s0 s1 h.
    do 10 (let s := fresh "s" in case: h => s [h ->]).
    split; first reflexivity.
    exact: prf_ideal_inv_gen h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF sign *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys shrincs_fxmss_prf_derive_table
  shrincs_fxmss_prf_derive_leaf.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_ideal_inv prf_ideal_rel kh_eval scheme.shrincs_fxmss_node
  scheme.shrincs_fxmss_sign.

Lemma R_prf_ideal_sign (Q : shrincs_fxmss_resources) (bit : bool) (arg :
  shrincs_fxmss_message) :
  ⊢ ⦃ fun '(s0,s1) => prf_ideal_inv (s0,s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) false)%share
      (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) arg
    ⦃ fun '(b0,s0) '(b1,s1) => b0 = b1 /\ prf_ideal_inv (s0,s1) ⦄.
Proof.
simplify_linking.
fold @code_link.

ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
}
move=> sto.
fold @code_link.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
  have hv : ValidCode shrincs_fxmss_locs emptym c by ssprove_valid end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
  rewrite (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end.
clear hv.
ssprove_code_simpl.
ssprove_sync.
move=> hsto.
ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
}
move=> done.
ssprove_sync.
move=> hdone.
ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_scnt_loc (ltac:(fmap_solve)).
}
move=> sc.
ssprove_sync.
move=> hsc.
ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_log_loc (ltac:(fmap_solve)).
}
move=> lg.
ssprove_sync.
{ apply: prf_ideal_inv_put. by []. }
ssprove_sync.
{ apply: prf_ideal_inv_put. by []. }
case: ifP => hmsg; last first.
{ apply r_ret. by move=> s0 s1 hi; split. }
ssprove_sync.
{
  move=> s0 s1 [hi hr].
  exact: hi shrincs_fxmss_next_loc (ltac:(fmap_solve)).
}
move=> q.
case hleaf: (shape.shrincs_fxmss_select_leaf
  (getSome sto hsto).2.1 (getSome sto hsto).2.2 q) => [a|]; last first.
{ apply r_ret. by move=> s0 s1 hi; split. }
ssprove_sync.
{ apply: prf_ideal_inv_put. by []. }
eapply r_get_remember_lhs => ks0.
eapply r_get_remember_rhs => ks1.
eapply (r_fact (isSome ks0 = isSome ks1)).
{
  move=> s0 s1 [[[hi hr] hk0] hk1].
  (cbv beta iota delta [prf_ideal_rel] in hr; rewrite /rel_app /get_side /= in hr).
  case: hr => hinit hks.
  rewrite /rem_inv /get_side /= in hk0 hk1.
  by rewrite -hk0 -hk1.
}
move=> hks.
eapply (@r_assertD ('option shrincs_fxmss_bytes) ('option shrincs_fxmss_bytes)).
- by move=> s _.
-
  move=> hks0 hks1.
  eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_ideal_inv (s0,s1));
    last by move=> s0 s1 [[hi _] _].
  apply: (r_reflexivity_alt
    (L := [fmap shrincs_fxmss_kp_loc; shrincs_fxmss_keys_loc; shrincs_fxmss_rt_loc;
      shrincs_fxmss_rom_loc]) prf_ideal_inv).
  + ssprove_valid.
  +
    move=> l hl s0 s1 [hi hr].
    apply: hi.
    by fmap_invert hl; fmap_solve.
  +
    move=> l v hl.
    apply: prf_ideal_inv_put.
    by fmap_invert hl.
Qed.
