(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.message_real

    The real message-PRF cache invariant couples generation, signing and common
    oracle operations. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.prf_memo games.prf_memo_state games.prf_memo_real
  toolkit.relational_rules toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance prf.inputs prf.reduction prf.message_memo.

(* ------------------------------------------------------------------ *)
(** ** Real message PRF coupling *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition prf_msg_real_keys (sto : option shrincs_fxmss_state)
    (kp kb : option (bytes 16))
    (tab : {fmap kh_M shrincs_khf_prf_msg -> bytes 16}) : Prop :=
  [/\ kp = kb,
    prf_memo_eval shrincs_khf_prf_msg tab (odflt (zeros 16) kp) &
    if isSome sto then True else kp = None].

Definition prf_msg_real_extra : precond :=
  rel_app [:: (lhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_kp_loc);
    (rhs, prf.prf_k_loc shrincs_khf_prf_msg);
    (rhs, prf_memo_tab_loc shrincs_khf_prf_msg)] prf_msg_real_keys.

Definition prf_msg_real_inv : precond := prf_msg_ideal_inv ⋊ prf_msg_real_extra.

Lemma prf_msg_real_inv_invariant Q bit :
  Invariant (loc (G_forge_sampledkey shrincs_fxmss_sha256 Q bit))
    (unionm (loc (R_prf_msg_memo Q bit))
      (unionm (loc (prf_memo.R_prf_memo shrincs_khf_prf_msg
        (shrincs_fxmss_q_prf_msg Q)))
        (loc (prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) true))))
    prf_msg_real_inv.
Proof.
cbv beta iota delta [prf_msg_real_inv].
apply: Invariant_inv_conj.
-
  exact (prf_msg_ideal_inv_invariant Q bit).
-
  rewrite /prf_msg_real_extra.
  ssprove_invariant.
  (cbv beta iota delta [prf_msg_real_keys]; rewrite /rel_empty /=).
  split; try reflexivity.
  exact: prf_memo_eval_empty.
Qed.

Lemma prf_msg_real_extra_put (l : Location) (v : l) :
  l.1 \notin [:: shrincs_fxmss_st_loc.1; shrincs_fxmss_kp_loc.1;
    (prf.prf_k_loc shrincs_khf_prf_msg).1;
    (prf_memo_tab_loc shrincs_khf_prf_msg).1] ->
  put_pre_cond l v prf_msg_real_extra.
Proof.
move=> hl. rewrite /prf_msg_real_extra.
apply: put_pre_cond_rel_app.
by move: hl; rewrite /= !in_cons !orbF.
Qed.

Lemma prf_msg_real_inv_put (l : Location) (v : l) :
  put_pre_cond l v prf_msg_ideal_inv ->
  put_pre_cond l v prf_msg_real_extra ->
  put_pre_cond l v prf_msg_real_inv.
Proof. exact: put_pre_cond_conj. Qed.

Lemma prf_msg_real_inv_scnt sc s0 s1 :
  prf_msg_real_inv (s0, s1) -> get_heap s0 shrincs_fxmss_scnt_loc = sc ->
  prf_msg_real_inv
    (set_heap s0 shrincs_fxmss_scnt_loc sc.+1, set_heap s1 shrincs_fxmss_scnt_loc sc.+1)
      /\
  get_heap (set_heap s1 shrincs_fxmss_scnt_loc sc.+1) prf_memo_cnt_loc <= sc.+1.
Proof.
move=> [hi he] hs.
have [hi' hb] := prf_msg_ideal_inv_scnt sc s0 s1 hi hs.
split; last exact: hb.
split; first exact: hi'.
apply: (prf_msg_real_extra_put shrincs_fxmss_scnt_loc sc.+1 (ltac:(done))).
exact: he.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque get_heap set_heap prf_msg_real_keys.

Lemma prf_msg_real_inv_gen st ks kp kt s0 s1 :
  heap_ignore prf_msg_ideal_private (s0, s1) ->
  get_heap s0 shrincs_fxmss_rt_loc = emptym ->
  get_heap s1 (prf_memo_tab_loc shrincs_khf_prf_msg) =
    setm emptym shrincs_fxmss_prf_msg_pin (kh_eval shrincs_khf_prf_msg kp
      shrincs_fxmss_prf_msg_pin) ->
  get_heap s1 (prf.prf_qs_loc shrincs_khf_prf_msg) = [:: shrincs_fxmss_prf_msg_pin] ->
  get_heap s1 prf_memo_cnt_loc = 1 ->
  get_heap s1 (prf.prf_k_loc shrincs_khf_prf_msg) = Some kp ->
  prf_msg_real_inv
    (set_heap (set_heap (set_heap (set_heap (set_heap s0
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks))
        shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc emptym,
     set_heap (set_heap (set_heap (set_heap (set_heap s1
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks))
        shrincs_fxmss_kp_loc (Some (zeros 16)))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc emptym).
Proof.
move=> hi hr ht hq hc hk.
split; first exact: prf_msg_ideal_inv_gen hi hr ht hq hc.
rewrite /prf_msg_real_extra !rel_app_cons /= rel_app_nil.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_st_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_kp_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite hk ht.

(cbv beta iota delta [prf_msg_real_keys]; rewrite /=).
split; [reflexivity| |exact I].
exact: prf_memo_eval_set (prf_memo_eval_empty shrincs_khf_prf_msg kp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real message PRF memo *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque get_heap set_heap prf_msg_real_keys.

Lemma prf_msg_real_inv_memo_hit rt cnt x y s0 s1 :
  prf_msg_real_inv (s0,s1) -> get_heap s0 shrincs_fxmss_rt_loc = rt ->
  get_heap s1 prf_memo_cnt_loc = cnt ->
  cnt <= get_heap s0 shrincs_fxmss_scnt_loc -> getm rt x = Some y ->
  prf_msg_real_inv
    (set_heap s0 shrincs_fxmss_rt_loc (setm rt x y),
     set_heap (set_heap s1 prf_memo_cnt_loc cnt.+1)
       shrincs_fxmss_rt_loc (setm rt x y)).
Proof.
move=> [hi he] hr hc hb hh.
split; first exact: prf_msg_ideal_inv_memo_hit hi hr hc hb hh.
rewrite /prf_msg_real_extra !rel_app_cons /= rel_app_nil.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_k_loc shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
exact: he.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque get_heap set_heap prf_msg_real_keys kh_eval.

Lemma prf_msg_real_inv_memo_set st rt tab qs cnt (x : shrincs_fxmss_coord ×
  shrincs_fxmss_bytes)
    (k : bytes 16) s0 s1 :
  prf_msg_real_inv (s0,s1) ->
  get_heap s0 shrincs_fxmss_st_loc = Some st ->
  get_heap s0 shrincs_fxmss_rt_loc = rt ->
  get_heap s1 (prf_memo_tab_loc shrincs_khf_prf_msg) = tab ->
  get_heap s1 (prf.prf_qs_loc shrincs_khf_prf_msg) = qs ->
  get_heap s1 prf_memo_cnt_loc = cnt ->
  cnt <= get_heap s0 shrincs_fxmss_scnt_loc ->
  get_heap s0 shrincs_fxmss_kp_loc = Some k ->
  let m := shrincs_fxmss_prf_msg_input st.1.1.1 x.1 x.2 in
  let y := kh_eval shrincs_khf_prf_msg k m in
  prf_msg_real_inv
    (set_heap s0 shrincs_fxmss_rt_loc (setm rt x y),
     set_heap
       (set_heap
         (set_heap (set_heap s1 prf_memo_cnt_loc cnt.+1)
           (prf.prf_qs_loc shrincs_khf_prf_msg) (rcons qs m))
         (prf_memo_tab_loc shrincs_khf_prf_msg) (setm tab m y))
       shrincs_fxmss_rt_loc (setm rt x y)).
Proof.
move=> [hi he] hs hr ht hq hc hb hk m y.
split; first exact: prf_msg_ideal_inv_memo_set hi hs hr ht hq hc hb.
rewrite /prf_msg_real_extra !rel_app_cons /= rel_app_nil.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf.prf_k_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc shrincs_khf_prf_msg) _ (prf.prf_k_loc
  shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc shrincs_khf_prf_msg) _ (prf.prf_k_loc
  shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_k_loc shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ (prf_memo_tab_loc shrincs_khf_prf_msg) _) at 1.
rewrite hs hk.

(cbv beta iota delta [prf_msg_real_keys] in he; rewrite /prf_msg_real_extra /rel_app /get_side /= hs hk ht in he).
case: he => he hv _.
(cbv beta iota delta [prf_msg_real_keys]; rewrite /=).
split; [exact: he | |exact I].
exact: prf_memo_eval_set hv.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real message PRF common *)

Import Shrincs.internal.ssprove.fxmss.games.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_msg_real_inv prf_msg_ideal_inv prf_msg_ideal_rel
  prf_msg_real_keys scheme.shrincs_fxmss_node scheme.shrincs_fxmss_verify
  kh_eval.

Lemma R_prf_msg_real_hash (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_hmsg_input) :
  ⊢ ⦃ fun '(s0, s1) => prf_msg_real_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg
    ≈ resolve
      ((R_prf_msg_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf_msg
        (shrincs_fxmss_q_prf_msg Q))
        ∘ prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) true)%share
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_msg_real_inv (s0, s1) ⦄.
Proof.
simplify_linking.
fold @code_link.

ssprove_sync.
{
  move=> s0 s1 [[hi hr] hx].
  exact: hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
}
move=> done.
fold @code_link.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => have hv :
  ValidCode [fmap shrincs_fxmss_done_loc; shrincs_fxmss_hcnt_loc;
    shrincs_fxmss_rom_loc] emptym c by ssprove_valid end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => rewrite
  (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end.
apply: (r_reflexivity_alt prf_msg_real_inv _ hv).
-
  move=> l hl s0 s1 [[hi hr] hx].
  apply: hi.
  by fmap_invert hl; fmap_solve.
-
  move=> l v hl.
  apply: prf_msg_real_inv_put.
  +
    apply: prf_msg_ideal_inv_put.
    by fmap_invert hl.
  +
    apply: prf_msg_real_extra_put.
    by fmap_invert hl.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_msg_real_inv prf_msg_ideal_inv prf_msg_ideal_rel
  prf_msg_real_keys kh_eval scheme.shrincs_fxmss_node
  scheme.shrincs_fxmss_verify.

Lemma R_prf_msg_real_forge (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_message × shrincs_fxmss_bytes) :
  ⊢ ⦃ fun '(s0, s1) => prf_msg_real_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) shrincs_fxmss_forge_op arg
    ≈ resolve
      ((R_prf_msg_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf_msg
        (shrincs_fxmss_q_prf_msg Q))
        ∘ prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) true)%share
      shrincs_fxmss_forge_op arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_msg_real_inv (s0, s1) ⦄.
Proof.
simplify_linking.
case: arg => cm sg.
fold @code_link.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => have hv :
  ValidCode shrincs_fxmss_locs emptym c by ssprove_valid end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => rewrite
  (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end.

clear hv.
ssprove_sync.
{
  move=> s0 s1 [[hi hr] hx].
  exact: hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
}
move=> sto.
ssprove_code_simpl.
eapply r_bind with (mid := fun '(b0,s0) '(b1,s1) => b0 = b1 /\ prf_msg_real_inv
  (s0,s1)).
-
  ssprove_code_simpl.
  ssprove_sync.
  {
    move=> hsto.
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
    }
    move=> done.
    ssprove_sync.
    move=> hdone.
    ssprove_sync.
    {
      apply: prf_msg_real_inv_put; [apply: prf_msg_ideal_inv_put | apply:
        prf_msg_real_extra_put]; by [].
    }
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_log_loc (ltac:(fmap_solve)).
    }
    move=> lg.
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_keys_loc (ltac:(fmap_solve)).
    }
    move=> kt.
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_sd_loc (ltac:(fmap_solve)).
    }
    move=> sd.
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_rt_loc (ltac:(fmap_solve)).
    }
    move=> rt.
    lazymatch goal with |- ⊢ ⦃ _ ⦄ ?c ≈ _ ⦃ _ ⦄ => have hv : ValidCode [fmap
      shrincs_fxmss_rom_loc] emptym c by ssprove_valid end.
    apply: (r_reflexivity_alt prf_msg_real_inv _ hv).
    -
      move=> l hl s0 s1 [[hi hr] hx].
      apply: hi.
      by fmap_invert hl; fmap_solve.
    -
      move=> l v hl.
      apply: prf_msg_real_inv_put.
      +
        apply: prf_msg_ideal_inv_put.
        by fmap_invert hl.
      +
        apply: prf_msg_real_extra_put.
        by fmap_invert hl.
  }
-
  move=> a0 a1.
  apply r_ret.
  by move=> s0 s1 [-> hi].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real message PRF gen *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque scheme.shrincs_fxmss_node prf_msg_real_inv prf_msg_ideal_inv
  prf_msg_ideal_rel prf_msg_real_keys kh_eval get_heap set_heap.

Lemma R_prf_msg_real_gen (Q : shrincs_fxmss_resources) (bit : bool) (arg :
  shrincs_fxmss_setup) :
  ⊢ ⦃ fun '(s0, s1) => prf_msg_real_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_gen,
      (shrincs_fxmss_setup, bytes 48)) arg
    ≈ resolve
      ((R_prf_msg_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf_msg
        (shrincs_fxmss_q_prf_msg Q))
        ∘ prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) true)%share
      (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_msg_real_inv (s0, s1) ⦄.
Proof.
simplify_linking.

ssprove_code_simpl.
eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{
  move=> s0 s1 [[[hi hr] hx] hs].
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
  move=> s0 s1 [[[[hi hr] hx] hs] hd].
  have he := hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hd.
}
fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hdone _.
eapply r_assertD; first by [].
move=> hlegal _.
set genrel := fun (tab : {fmap kh_M shrincs_khf_prf_msg -> bytes 16}) (qs : seq (kh_M
  shrincs_khf_prf_msg)) (cnt : nat) (ko : option (bytes 16)) => fun '(s0,s1) => [/\
  heap_ignore prf_msg_ideal_private (s0,s1), get_heap s0 shrincs_fxmss_rt_loc =
    emptym,
    get_heap s1
  (prf_memo_tab_loc shrincs_khf_prf_msg) = tab, get_heap s1 (prf.prf_qs_loc
  shrincs_khf_prf_msg) = qs & get_heap s1 prf_memo_cnt_loc = cnt] /\ get_heap s1
  (prf.prf_k_loc shrincs_khf_prf_msg) = ko.
eapply rpre_weaken_rule with (pre := genrel emptym [::] 0 None); last first.
{
  move=> s0 s1 [[[[hi hr] hx] hs] hd].
  rewrite /rem_inv /get_side /= in hs.
  (cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
  case: hr => hlog hbound [hrt htab hqs hcnt] hkp.
  (cbv beta iota delta [prf_msg_real_keys] in hx; rewrite /prf_msg_real_extra /rel_app /get_side /= hs in hx).
  case: hx => hk he hn.
  split; first by split.
  by rewrite -hk hn.
}

rewrite (code_link_bind (dBytes 16)) (code_link_scheme _ _ _ _ (prog_valid (dBytes
  16))).
rewrite (code_link_bind (dBytes 16)) (code_link_scheme _ _ _ _ (prog_valid (dBytes
  16))).
eapply r_scheme_bind; first exact: prog_valid.
move=> pp; cbv beta.
rewrite (code_link_bind (dBytes 16)) (code_link_scheme _ _ _ _ (prog_valid (dBytes
  16))).
rewrite (code_link_bind (dBytes 16)) (code_link_scheme _ _ _ _ (prog_valid (dBytes
  16))).
eapply r_scheme_bind; first exact: prog_valid.
move=> ks; cbv beta.
simplify_linking.
eapply (r_get_rhs_known prf_memo_cnt_loc 0 (genrel emptym [::] 0 None)); first by
  move=> s0 s1 [[_ _ _ _ hc] hk].
fold @code_link.
simplify_linking.
eapply (r_put_rhs_weak prf_memo_cnt_loc 1 (genrel emptym [::] 0 None) (genrel emptym
  [::] 1 None)).
{
  move=> s0 s1 [[hi hr ht hq hc] hk]; split; last by rewrite get_set_heap_neq // hk.
  split.
  -
    apply heap_ignore_set_r; last exact: hi.
    by rewrite /prf_msg_ideal_private !domm_set !in_fset1U /=.
  -
    exact: hr.
  -
    by rewrite get_set_heap_neq // ht.
  -
    by rewrite get_set_heap_neq // hq.
  -
    by rewrite get_set_heap_eq.
}
eapply (r_get_rhs_known (prf_memo_tab_loc shrincs_khf_prf_msg) emptym (genrel emptym
  [::] 1 None)); first by move=> s0 s1 [[_ _ ht _ _] hk].
simplify_linking.
eapply (r_get_rhs_known (prf.prf_qs_loc shrincs_khf_prf_msg) [::] (genrel emptym [::]
  1 None)); first by move=> s0 s1 [[_ _ _ hq _] hk].
eapply (r_bind_assertD_rhs _ (genrel emptym [::] 1 None)); first by [].
move=> _.
eapply (r_bind_assertD_rhs _ (genrel emptym [::] 1 None)); first by [].
move=> _.
eapply (r_put_bind_rhs _ _ (genrel emptym [::] 1 None) (genrel emptym [::
  shrincs_fxmss_prf_msg_pin]
  1 None)).
{
  move=> s0 s1 [[hi hr ht hq hc] hk]; split; last by rewrite get_set_heap_neq // hk.
  split.
  -
    apply heap_ignore_set_r; last exact: hi.
    by rewrite /prf_msg_ideal_private !domm_set !in_fset1U /=.
  -
    exact: hr.
  -
    by rewrite get_set_heap_neq // ht.
  -
    by rewrite get_set_heap_eq.
  -
    by rewrite get_set_heap_neq // hc.
}
ssprove_code_simpl.
eapply (r_get_rhs_known (prf.prf_k_loc shrincs_khf_prf_msg) None (genrel emptym [::
  shrincs_fxmss_prf_msg_pin] 1 None)); first by move=> s0 s1 [hi hk].
ssprove_code_simpl.
fold @bind.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> kp; cbv beta.
ssprove_code_simpl.
eapply (r_put_rhs_weak (prf.prf_k_loc shrincs_khf_prf_msg) (Some kp) (genrel emptym
  [:: shrincs_fxmss_prf_msg_pin] 1 None) (genrel emptym [:: shrincs_fxmss_prf_msg_pin]
    1
    (Some kp))).
{
  move=> s0 s1 [[hi hr ht hq hc] hk]; split; last exact: get_set_heap_eq.
  split.
  -
    apply heap_ignore_set_r; last exact: hi.
    by rewrite /prf_msg_ideal_private !domm_set !in_fset1U /=.
  -
    exact: hr.
  -
    by rewrite get_set_heap_neq // ht.
  -
    by rewrite get_set_heap_neq // hq.
  -
    by rewrite get_set_heap_neq // hc.
}
eapply (r_put_rhs_weak (prf_memo_tab_loc shrincs_khf_prf_msg) (setm emptym
  shrincs_fxmss_prf_msg_pin
  (kh_eval shrincs_khf_prf_msg kp shrincs_fxmss_prf_msg_pin)) (genrel emptym [::
    shrincs_fxmss_prf_msg_pin] 1
  (Some kp)) (genrel (setm emptym shrincs_fxmss_prf_msg_pin (kh_eval
    shrincs_khf_prf_msg
    kp
  shrincs_fxmss_prf_msg_pin)) [:: shrincs_fxmss_prf_msg_pin] 1 (Some kp))).
{
  move=> s0 s1 [[hi hr ht hq hc] hk]; split; last by rewrite get_set_heap_neq // hk.
  split.
  -
    apply heap_ignore_set_r; last exact: hi.
    by rewrite /prf_msg_ideal_private !domm_set !in_fset1U /=.
  -
    exact: hr.
  -
    by rewrite get_set_heap_eq.
  -
    by rewrite get_set_heap_neq // hq.
  -
    by rewrite get_set_heap_neq // hc.
}
rewrite (code_link_bind (shrincs_fxmss_sample_keys shrincs_fxmss_sha256
  (shrincs_fxmss_schedule arg.1)))
  (code_link_scheme _ _ _ _ (shrincs_fxmss_sample_keys_valid shrincs_fxmss_sha256
    emptym emptym _)).
rewrite (code_link_bind (shrincs_fxmss_sample_keys shrincs_fxmss_sha256
  (shrincs_fxmss_schedule arg.1)))
  (code_link_scheme _ _ _ _ (shrincs_fxmss_sample_keys_valid shrincs_fxmss_sha256
    emptym emptym _)).
eapply r_scheme_bind; first exact: shrincs_fxmss_sample_keys_valid.
move=> kt; cbv beta.
rewrite !code_link_assertD.
ssprove_code_simpl.
eapply (@r_assertD (bytes 48) (bytes 48)); first by [].
move=> hroot _.
simplify_linking.
eapply (r_put_lhs _ _ _ _ (genrel (setm emptym shrincs_fxmss_prf_msg_pin (kh_eval
  shrincs_khf_prf_msg kp shrincs_fxmss_prf_msg_pin)) [:: shrincs_fxmss_prf_msg_pin] 1
    (Some
    kp))).
do 4 apply r_put_lhs.
do 5 apply r_put_rhs.
apply r_ret.
move=> s0 s1 h.
do 10 (let s := fresh "s" in case: h => s [h ->]).
case: h => [[hi hr ht hq hc] hk].
split; first reflexivity.
exact: prf_msg_real_inv_gen hi hr ht hq hc hk.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real message PRF sign *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque scheme.shrincs_fxmss_node scheme.shrincs_fxmss_sign
  scheme.shrincs_fxmss_verify prf_msg_real_inv prf_msg_ideal_inv
  prf_msg_ideal_rel prf_msg_real_keys kh_eval PRF_msg_sf get_heap set_heap.

Lemma R_prf_msg_real_sign (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_message) :
  ⊢ ⦃ fun '(s0, s1) => prf_msg_real_inv (s0, s1) ⦄
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)
      (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) arg
    ≈ resolve
      ((R_prf_msg_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf_msg
        (shrincs_fxmss_q_prf_msg Q))
        ∘ prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q) true)%share
      (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_msg_real_inv (s0, s1) ⦄.
Proof.
simplify_linking.

eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{
  move=> s0 s1 [[[hi hr] hx] hs].
  have he := hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hs.
}
fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hsto hsto'.
case: sto hsto hsto' => [st|] hsto hsto'; last discriminate.
ssprove_code_simpl.
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{
  move=> s0 s1 [[[[hi hr] hx] hs] hd].
  have he := hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hd.
}
fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hdone _.
eapply r_get_remember_lhs => sc.
eapply (r_get_rhs_known shrincs_fxmss_scnt_loc sc).
{
  move=> s0 s1 [[[[[hi hr] hx] hs] hd] hc].
  have he := hi shrincs_fxmss_scnt_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hc.
}
fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hsc _.
eapply r_get_remember_lhs => lg.
eapply (r_get_rhs_known shrincs_fxmss_log_loc lg).
{
  move=> s0 s1 [[[[[[hi hr] hx] hs] hd] hc] hl].
  have he := hi shrincs_fxmss_log_loc (ltac:(fmap_solve)).
  by rewrite -he; exact: hl.
}
fold @code_link.
simplify_linking.
set signrel := fun '(s0,s1) => [/\ prf_msg_real_inv (s0,s1), get_heap s0
  shrincs_fxmss_st_loc = Some
  st, get_heap s0 shrincs_fxmss_scnt_loc = sc.+1 & get_heap s1 prf_memo_cnt_loc <=
    sc.+1].
(do 2 apply r_put_lhs).
(do 2 apply r_put_rhs).
(eapply rpre_weaken_rule with (pre := signrel); last first).
{
  move=> s0 s1 h.
  do 4 (let s := fresh "s" in case: h => s [h ->]).
  case: h => [[[[hi hs] hd] hc] hl].
  have [hi' hcnt] := prf_msg_real_inv_scnt sc s4 s2 hi hc.
  rewrite /signrel.
  split.
  (apply: (prf_msg_real_inv_put shrincs_fxmss_log_loc (arg :: lg)); [apply:
    prf_msg_ideal_inv_put; done | apply: prf_msg_real_extra_put; done | exact: hi']).
  (rewrite -> (get_set_heap_neq _ shrincs_fxmss_log_loc _ shrincs_fxmss_st_loc
    ltac:(reflexivity))
    at 1; rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ shrincs_fxmss_st_loc
      ltac:(reflexivity))
    at 1; exact: hs).
  (rewrite -> (get_set_heap_neq _ shrincs_fxmss_log_loc _ shrincs_fxmss_scnt_loc
    ltac:(reflexivity)) at 1; exact: get_set_heap_eq).
  (rewrite -> (get_set_heap_neq _ shrincs_fxmss_log_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at 1; exact: hcnt).
}
case: ifP => hmsg; last first.
{
  apply r_ret.
  by move=> s0 s1 [hi hs hc hb]; split.
}
{
  eapply rpre_weaken_rule with (pre := fun '(s0,s1) => signrel (s0,s1)); last by [].
  simplify_linking.
  (eapply (rsame_head_cmd_alt (cmd_get shrincs_fxmss_next_loc)); first (apply
    (cmd_get_preserve_pre shrincs_fxmss_next_loc signrel))).
  {
    move=> s0 s1 [[[hi hr] hx] hs hc hb].
    exact: hi shrincs_fxmss_next_loc (ltac:(fmap_solve)).
  }
  move=> q.
  case hleaf: (shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 q) => [a|]; last first.
  {
    simplify_linking.
    apply r_ret.
    by move=> s0 s1 [hi hs hc hb]; split.
  }
  simplify_linking.
  (eapply (@rsame_head_cmd_alt _ _ (fun z => _) (fun z => _) (cmd_put
    shrincs_fxmss_next_loc q.+1)); first (apply (cmd_put_preserve_pre
      shrincs_fxmss_next_loc q.+1
    signrel))).
  {
    move=> s0 s1 [hi hs hc hb].
    split.
    -
      apply: (prf_msg_real_inv_put shrincs_fxmss_next_loc q.+1); [apply:
        prf_msg_ideal_inv_put; done |
        apply: prf_msg_real_extra_put; done | ].
      exact: hi.
    -
      rewrite -> (get_set_heap_neq _ shrincs_fxmss_next_loc _ shrincs_fxmss_st_loc
        ltac:(reflexivity)) at 1.
      exact: hs.
    -
      rewrite -> (get_set_heap_neq _ shrincs_fxmss_next_loc _ shrincs_fxmss_scnt_loc
        ltac:(reflexivity)) at
        1.
      exact: hc.
    -
      rewrite -> (get_set_heap_neq _ shrincs_fxmss_next_loc _ prf_memo_cnt_loc
        ltac:(reflexivity)) at 1.
      exact: hb.
  }
  move=> [].
  (eapply (rsame_head_cmd_alt (cmd_get shrincs_fxmss_ks_loc)); first (apply
    (cmd_get_preserve_pre shrincs_fxmss_ks_loc signrel))).
  {
    move=> s0 s1 [[[hi hr] hx] hs hc hb].
    exact: hi shrincs_fxmss_ks_loc (ltac:(fmap_solve)).
  }
  move=> ks.
  fold @code_link.
  rewrite !code_link_assertD.
  eapply (@r_assertD ('option shrincs_fxmss_bytes) ('option shrincs_fxmss_bytes));
    first by [].
  move=> hks _.
  (eapply (@r_get_remember_lhs _ _ shrincs_fxmss_kp_loc _ _ signrel _); move=> kp0).
  (eapply r_get_remember_rhs; move=> kp1).
  eapply (r_fact (isSome kp0 = isSome kp1)).
  {
    move=> s0 s1 [[[[[hi hr] hx] hs hc hb] hk0] hk1].
    (cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= in hr).
    case: hr => hlog hbound htab hkp.
    rewrite /rem_inv /get_side /= in hk0 hk1.
    by rewrite -hk0 -hk1.
  }
  move=> hkp.
  fold @code_link.
  rewrite !code_link_assertD.
  eapply (@r_assertD ('option shrincs_fxmss_bytes) ('option shrincs_fxmss_bytes)).
  -
    by move=> s _.
  -
    move=> hkp0 hkp1.
    case: kp0 hkp0 hkp => [kp|] hkp0 hkp; last discriminate.
    set keyrel := signrel ⋊ rem_lhs shrincs_fxmss_kp_loc (Some kp).
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) => keyrel (s0,s1)); last by
      move=> s0 s1 [hi _].
    simplify_linking.
    rewrite (shrincs_fxmss_prf_msg_eval_bound_message kp st.1.1.1 a arg hmsg).
    eapply (rsame_head_cmd_alt (cmd_get shrincs_fxmss_keys_loc)); first (apply
      (cmd_get_preserve_pre shrincs_fxmss_keys_loc keyrel)).
    {
      move=> s0 s1 [[[[hi hr] hx] hs hc hb] hk].
      exact: hi shrincs_fxmss_keys_loc (ltac:(fmap_solve)).
    }
    move=> kt.
    eapply (@r_get_remember_lhs _ _ shrincs_fxmss_rt_loc _ _ keyrel _); move=> rt.
    eapply (r_get_rhs_known shrincs_fxmss_rt_loc rt).
    {
      move=> s0 s1 [[[[[hi hr] hx] hs hc hb] hk] hrt].
      have he := hi shrincs_fxmss_rt_loc (ltac:(fmap_solve)).
      by rewrite -he; exact: hrt.
    }
    simplify_linking.
    eapply r_get_remember_rhs => cnt.
    rewrite code_link_bind code_link_assertD.
    eapply (r_bind_assertD_rhs _ (keyrel ⋊ rem_lhs shrincs_fxmss_rt_loc rt ⋊ rem_rhs
      prf_memo_cnt_loc cnt)).
    {
      move=> s0 s1 [[[[hi hs hc hb] hk] hrt] hcnt].
      rewrite /rem_inv /get_side /= in hcnt.
      rewrite hcnt in hb.
      apply: leq_ltn_trans hb _.
      by rewrite /shrincs_fxmss_q_prf_msg ltnS.
    }
    move=> _.
    simplify_linking.
    apply r_put_rhs.
    eapply r_get_remember_rhs => tab.
    eapply (r_fact (getm tab (shrincs_fxmss_prf_msg_input st.1.1.1 a
      (shrincs_fxmss_bound_message
      arg)) = getm rt (a, shrincs_fxmss_bound_message arg) /\ prf_memo_eval
      shrincs_khf_prf_msg tab kp)).
    {
      move=> s0 s1 [h ht].
      case: h => s1' [h he].
      subst s1.
      case: h => [[h hrt] hcnt].
      case: h => [h hk].
      case: h => [[[hi hr] hx] hs hc hb].
      rewrite /rem_inv /get_side /= in ht hrt hk.
      rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf_memo_tab_loc
        shrincs_khf_prf_msg) ltac:(reflexivity)) in ht.
      (cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= hs hrt ht in hr).
      case: hr => hlog hbound htab hkp'.
      (cbv beta iota delta [prf_msg_real_keys] in hx; rewrite /prf_msg_real_extra /rel_app /get_side /= hk ht in hx).
      case: hx => hkey hv hn.
      split; last exact: hv.
      exact (htab (a,shrincs_fxmss_bound_message arg)).
    }
    move=> [htab heval].
    case hh: (getm rt (a,shrincs_fxmss_bound_message arg)) => [y|].
  -
    rewrite hh in htab.
    simplify_linking.
    rewrite htab.
    have hy := heval _ _ htab.
    rewrite -hy.
    simplify_linking.
    apply r_put_lhs.
    apply r_put_rhs.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_msg_real_inv (s0,s1));
      last
      first.
    {
      move=> s0 s1 h.
      do 2 (let s := fresh "s" in case: h => s [h ->]).
      case: h => [h ht].
      case: h => s1' [h he].
      subst s.
      case: h => [[h hrt] hcnt].
      case: h => [[hi hs hc hb] hk].
      apply: (prf_msg_real_inv_memo_hit rt cnt (a,shrincs_fxmss_bound_message arg) y
        s2
        s1'
        hi hrt hcnt _ hh).
      rewrite /rem_inv /get_side /= in hcnt.
      by rewrite hc -hcnt.
    }
    simplify_linking.
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_rom_loc (ltac:(fmap_solve)).
    }
    move=> mp.
    fold @code_link.
    (lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
      have hv : ValidCode [fmap shrincs_fxmss_rom_loc] emptym c by ssprove_valid end).
    (lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
      rewrite (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end).
    clear hv.
    ssprove_code_simpl.
    (eapply (@r_reflexivity_alt ('option shrincs_fxmss_bytes) [fmap
      shrincs_fxmss_rom_loc]
      prf_msg_real_inv)).
    ssprove_valid.
    +
      move=> l hl s0 s1 [[hi hr] hx].
      apply: hi.
      by fmap_invert hl; fmap_solve.
    +
      move=> l v hl.
      apply: prf_msg_real_inv_put; [apply: prf_msg_ideal_inv_put | apply:
        prf_msg_real_extra_put]; by fmap_invert hl.
  -
    rewrite hh in htab.
    rewrite htab.
    simplify_linking.
    eapply r_get_remember_rhs => qs.
    eapply (r_fact (size qs < shrincs_fxmss_q_prf_msg Q /\
      shrincs_fxmss_prf_msg_input st.1.1.1 a
      (shrincs_fxmss_bound_message arg) \notin qs)).
    {
      move=> s0 s1 [[h ht] hq].
      case: h => s1' [h he].
      subst s1.
      case: h => [[h hrt] hcnt].
      case: h => [h hk].
      case: h => [[[hi hr] hx] hs hc hb].
      rewrite /rem_inv /get_side /= in ht hq hcnt.
      rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf_memo_tab_loc
        shrincs_khf_prf_msg) ltac:(reflexivity)) in ht.
      rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_qs_loc
        shrincs_khf_prf_msg) ltac:(reflexivity)) in hq.
      (cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= ht hq hcnt in hr).
      case: hr => hlog hbound henc hkp'.
      have hbudget : cnt < shrincs_fxmss_q_prf_msg Q.
      {
        rewrite hcnt in hb.
        apply: leq_ltn_trans hb _.
        by rewrite /shrincs_fxmss_q_prf_msg ltnS.
      }
      exact: (prf_memo_log_miss shrincs_khf_prf_msg tab qs cnt
        (shrincs_fxmss_q_prf_msg Q) _ hlog
        hbudget htab).
    }
    move=> [hsize hfresh].
    fold @code_link.
    simplify_linking.
    rewrite bind_assoc.
    eapply r_bind_assertD_rhs; first by move=> s0 s1 _.
    move=> _.
    eapply r_bind_assertD_rhs; first by move=> s0 s1 _.
    move=> _.
    simplify_linking.
    apply r_put_rhs.
    ssprove_code_simpl.
    eapply (r_get_rhs_known (prf.prf_k_loc shrincs_khf_prf_msg) (Some kp)).
    {
      move=> s0 s1 h.
      case: h => s1' [h he].
      subst s1.
      case: h => [[h ht] hq].
      case: h => s1'' [h he].
      subst s1'.
      case: h => [[h hrt] hcnt].
      case: h => [h hk].
      case: h => [[[hi hr] hx] hs hc hb].
      rewrite /rem_inv /get_side /= in hk.
      rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc shrincs_khf_prf_msg) _
        (prf.prf_k_loc shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
      rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_k_loc
        shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
      (cbv beta iota delta [prf_msg_real_keys] in hx; rewrite /prf_msg_real_extra /rel_app /get_side /= hk in hx).
      by case: hx => <- _ _.
    }
    ssprove_code_simpl.
    apply r_put_lhs.
    do 2 apply r_put_rhs.
    eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_msg_real_inv (s0,s1));
      last
      first.
    {
      move=> s0 s1 h.
      do 4 (let s := fresh "s" in case: h => s [h ->]).
      case: h => [[h ht] hq].
      case: h => s1' [h he].
      subst s4.
      case: h => [[h hrt] hcnt].
      case: h => [[hi hs hc hb] hk].
      rewrite /rem_inv /get_side /= in ht hq hcnt hk.
      rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf_memo_tab_loc
        shrincs_khf_prf_msg) ltac:(reflexivity)) in ht.
      rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_qs_loc
        shrincs_khf_prf_msg) ltac:(reflexivity)) in hq.
      apply: (prf_msg_real_inv_memo_set st rt tab qs cnt
        (a,shrincs_fxmss_bound_message
        arg) kp s3 s1' hi hs hrt ht hq hcnt _ hk).
      by rewrite hc -hcnt.
    }
    simplify_linking.
    ssprove_sync.
    {
      move=> s0 s1 [[hi hr] hx].
      exact: hi shrincs_fxmss_rom_loc (ltac:(fmap_solve)).
    }
    move=> mp.
    fold @code_link.
    (lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
      have hv : ValidCode [fmap shrincs_fxmss_rom_loc] emptym c by ssprove_valid end).
    (lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] =>
      rewrite (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv) end).
    clear hv.
    ssprove_code_simpl.
    (eapply (@r_reflexivity_alt ('option shrincs_fxmss_bytes) [fmap
      shrincs_fxmss_rom_loc]
      prf_msg_real_inv)).
    ssprove_valid.
    +
      move=> l hl s0 s1 [[hi hr] hx].
      apply: hi.
      by fmap_invert hl; fmap_solve.
    +
      move=> l v hl.
      apply: prf_msg_real_inv_put; [apply: prf_msg_ideal_inv_put | apply:
        prf_msg_real_extra_put]; by fmap_invert hl.
}
Qed.
