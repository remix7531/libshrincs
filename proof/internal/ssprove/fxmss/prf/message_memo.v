(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.message_memo

    The ideal message-PRF cache invariant supports memoized randomizer queries. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.prf_memo games.prf_memo_state toolkit.relational_rules
  toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance prf.inputs prf.reduction.

(* ------------------------------------------------------------------ *)
(** ** Message PRF coupling *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition prf_msg_ideal_private : Locations :=
  [fmap shrincs_fxmss_kp_loc; prf_memo_tab_loc shrincs_khf_prf_msg; prf_memo_cnt_loc;
    prf.prf_k_loc shrincs_khf_prf_msg; prf.prf_qs_loc shrincs_khf_prf_msg].

Definition prf_msg_ideal_rel (sto : option shrincs_fxmss_state)
    (rt : {fmap shrincs_fxmss_coord × shrincs_fxmss_bytes -> bytes 16})
    (tab : {fmap kh_M shrincs_khf_prf_msg -> bytes 16})
    (qs : seq (kh_M shrincs_khf_prf_msg)) (cnt sc : nat)
    (kp0 kp1 : option (bytes 16)) : Prop :=
  [/\ prf_memo_log shrincs_khf_prf_msg tab qs cnt,
      cnt <= sc.+1,
      match sto with
      | None => [/\ rt = emptym, tab = emptym, qs = [::] & cnt = 0]
      | Some st => prf_memo_encoded shrincs_khf_prf_msg (shrincs_fxmss_coord ×
        shrincs_fxmss_bytes)
          (fun x => shrincs_fxmss_prf_msg_input st.1.1.1 x.1 x.2) rt tab
      end & isSome kp0 = isSome kp1].

Definition prf_msg_ideal_inv : precond :=
  heap_ignore prf_msg_ideal_private
  ⋊ rel_app [:: (lhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_rt_loc);
    (rhs, prf_memo_tab_loc shrincs_khf_prf_msg);
    (rhs, prf.prf_qs_loc shrincs_khf_prf_msg);
    (rhs, prf_memo_cnt_loc); (lhs, shrincs_fxmss_scnt_loc);
    (lhs, shrincs_fxmss_kp_loc); (rhs, shrincs_fxmss_kp_loc)] prf_msg_ideal_rel.

Lemma prf_msg_ideal_inv_invariant Q bit :
  Invariant (loc (G_forge_randomized shrincs_fxmss_sha256 Q bit))
    (unionm (loc (R_prf_msg_memo Q bit))
      (unionm (loc (prf_memo.R_prf_memo shrincs_khf_prf_msg
        (shrincs_fxmss_q_prf_msg Q)))
        (loc (prf.PRF_game shrincs_khf_prf_msg (shrincs_fxmss_q_prf_msg Q)
          false))))
    prf_msg_ideal_inv.
Proof.
rewrite /prf_msg_ideal_inv.
ssprove_invariant.
(cbv beta iota delta [prf_msg_ideal_rel]; rewrite /rel_empty /=).
split.
-
  exact: prf_memo_log_empty.
-
  by [].
-
  by split.
-
  by [].
Qed.

(** GEN preserves the table relation without evaluating the computed root. *)
(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_msg_ideal_rel get_heap set_heap.

Lemma prf_msg_ideal_inv_gen st ks kp kt pinval s0 s1 :
  heap_ignore prf_msg_ideal_private (s0, s1) ->
  get_heap s0 shrincs_fxmss_rt_loc = emptym ->
  get_heap s1 (prf_memo_tab_loc shrincs_khf_prf_msg) =
    setm emptym shrincs_fxmss_prf_msg_pin pinval ->
  get_heap s1 (prf.prf_qs_loc shrincs_khf_prf_msg) = [:: shrincs_fxmss_prf_msg_pin] ->
  get_heap s1 prf_memo_cnt_loc = 1 ->
  prf_msg_ideal_inv
    (set_heap (set_heap (set_heap (set_heap (set_heap s0
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks))
        shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc emptym,
     set_heap (set_heap (set_heap (set_heap (set_heap s1
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks))
        shrincs_fxmss_kp_loc (Some (zeros 16)))
      shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc emptym).
Proof.
move=> hi hr ht hq hc.
rewrite /prf_msg_ideal_inv.
split.
-
  do 2 apply: put_pre_cond_heap_ignore.
  apply: heap_ignore_set_l; first by rewrite /prf_msg_ideal_private !domm_set
    !in_fset1U
   /=.
  apply: heap_ignore_set_r; first by rewrite /prf_msg_ideal_private !domm_set
    !in_fset1U
   /=.
  do 2 apply: put_pre_cond_heap_ignore.
  exact: hi.
-
  rewrite !rel_app_cons /=.
  rewrite rel_app_nil.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_st_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_st_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_st_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ shrincs_fxmss_st_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_eq s0 shrincs_fxmss_st_loc (Some st)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_rt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_rt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_rt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ shrincs_fxmss_rt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ shrincs_fxmss_rt_loc
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
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ (prf.prf_qs_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ (prf.prf_qs_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ (prf.prf_qs_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ (prf.prf_qs_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ (prf.prf_qs_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at
    1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at
    1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at
    1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at
    1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at
    1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_scnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_scnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_scnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ shrincs_fxmss_scnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ shrincs_fxmss_scnt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_kp_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_kp_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_eq _ shrincs_fxmss_kp_loc (Some kp)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_kp_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_kp_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_eq _ shrincs_fxmss_kp_loc (Some (zeros 16))) at 1.
  rewrite -> hr at 1.
  rewrite -> ht at 1.
  rewrite -> hq at 1.
  rewrite -> hc at 1.
  cbv beta iota delta [prf_msg_ideal_rel].
  split.
  +
    exact: prf_memo_log_set (prf_memo_log_empty shrincs_khf_prf_msg).
  +
    by [].
  +
    apply: prf_memo_encoded_pin.
    *
      by move=> x; apply: shrincs_fxmss_prf_msg_pin_neq.
    *
      exact: prf_memo_encoded_empty.
  +
    by [].
Qed.
Transparent get_heap set_heap.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque get_heap set_heap prf_msg_ideal_rel.

Lemma prf_msg_ideal_inv_scnt sc s0 s1 :
  prf_msg_ideal_inv (s0, s1) -> get_heap s0 shrincs_fxmss_scnt_loc = sc ->
  prf_msg_ideal_inv
    (set_heap s0 shrincs_fxmss_scnt_loc sc.+1, set_heap s1 shrincs_fxmss_scnt_loc sc.+1)
      /\
  get_heap (set_heap s1 shrincs_fxmss_scnt_loc sc.+1) prf_memo_cnt_loc <= sc.+1.
Proof.
move=> [hi hr] hs.
rewrite /prf_msg_ideal_inv.
split.
split; first (apply: put_pre_cond_heap_ignore; exact: hi).
-
  rewrite !rel_app_cons /= rel_app_nil.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ shrincs_fxmss_st_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ shrincs_fxmss_rt_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ (prf_memo_tab_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ (prf.prf_qs_loc
    shrincs_khf_prf_msg)
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ prf_memo_cnt_loc
    ltac:(reflexivity)) at
    1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ shrincs_fxmss_kp_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_neq _ shrincs_fxmss_scnt_loc _ shrincs_fxmss_kp_loc
    ltac:(reflexivity)) at 1.
  rewrite -> (get_set_heap_eq s0 shrincs_fxmss_scnt_loc sc.+1) at 1.
  (cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
  case: hr => hlog hbound htab hkp; split; [exact: hlog | exact: leq_trans hbound
    (leqnSn _) | exact: htab | exact: hkp].
-
  rewrite -> (get_set_heap_neq s1 shrincs_fxmss_scnt_loc sc.+1 prf_memo_cnt_loc
    ltac:(reflexivity)) at 1.
  (cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
  by case: hr.
Qed.

Transparent get_heap set_heap.

Lemma prf_msg_ideal_inv_put (l : Location) (v : l) :
  l.1 \notin [:: shrincs_fxmss_st_loc.1; shrincs_fxmss_rt_loc.1;
    (prf_memo_tab_loc shrincs_khf_prf_msg).1;
    (prf.prf_qs_loc shrincs_khf_prf_msg).1; prf_memo_cnt_loc.1;
    shrincs_fxmss_scnt_loc.1; shrincs_fxmss_kp_loc.1] ->
  put_pre_cond l v prf_msg_ideal_inv.
Proof.
move=> hl.
rewrite /prf_msg_ideal_inv.
apply: put_pre_cond_conj; first exact: put_pre_cond_heap_ignore.
apply: put_pre_cond_rel_app.
by move: hl; rewrite /= !in_cons !orbF orbb.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Message PRF memo *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque get_heap set_heap prf_msg_ideal_rel.

Lemma prf_msg_ideal_inv_memo_set st rt tab qs cnt (x : shrincs_fxmss_coord ×
  shrincs_fxmss_bytes)
    (y : bytes 16) s0 s1 :
  prf_msg_ideal_inv (s0, s1) ->
  get_heap s0 shrincs_fxmss_st_loc = Some st ->
  get_heap s0 shrincs_fxmss_rt_loc = rt ->
  get_heap s1 (prf_memo_tab_loc shrincs_khf_prf_msg) = tab ->
  get_heap s1 (prf.prf_qs_loc shrincs_khf_prf_msg) = qs ->
  get_heap s1 prf_memo_cnt_loc = cnt ->
  cnt <= get_heap s0 shrincs_fxmss_scnt_loc ->
  prf_msg_ideal_inv
    (set_heap s0 shrincs_fxmss_rt_loc (setm rt x y),
     set_heap
       (set_heap
         (set_heap (set_heap s1 prf_memo_cnt_loc cnt.+1)
           (prf.prf_qs_loc shrincs_khf_prf_msg)
           (rcons qs (shrincs_fxmss_prf_msg_input st.1.1.1 x.1 x.2)))
         (prf_memo_tab_loc shrincs_khf_prf_msg)
         (setm tab (shrincs_fxmss_prf_msg_input st.1.1.1 x.1 x.2) y))
       shrincs_fxmss_rt_loc (setm rt x y)).
Proof.
move=> [hi hr] hs hrt ht hq hc hb.
rewrite /prf_msg_ideal_inv.
split.
apply: put_pre_cond_heap_ignore; do 3 (apply: heap_ignore_set_r; first by rewrite
  /prf_msg_ideal_private !domm_set !in_fset1U /=); exact: hi.
rewrite !rel_app_cons /= rel_app_nil.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_rt_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ (prf_memo_tab_loc shrincs_khf_prf_msg) _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf.prf_qs_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc shrincs_khf_prf_msg) _
  (prf.prf_qs_loc shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ (prf.prf_qs_loc shrincs_khf_prf_msg) _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ prf_memo_cnt_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc shrincs_khf_prf_msg) _
  prf_memo_cnt_loc ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc shrincs_khf_prf_msg) _ prf_memo_cnt_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ prf_memo_cnt_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_scnt_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf_memo_tab_loc shrincs_khf_prf_msg) _
  shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ (prf.prf_qs_loc shrincs_khf_prf_msg) _
  shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> hs at 1.

(cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= hs hrt ht hq hc in hr).
case: hr => hlog hbound htab hkp.
cbv beta iota delta [prf_msg_ideal_rel].
split.
exact: prf_memo_log_set hlog.
-
  by rewrite ltnS.
-
  apply: prf_memo_encoded_set.
  move=> [a0 m0] [a1 m1] /= he; exact: (congr1 snd (shrincs_fxmss_prf_msg_input_inj _
    _ _
    _ _ _
    he)).
-
  exact: htab.
-
  exact: hkp.
Qed.
Transparent get_heap set_heap.
(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque get_heap set_heap prf_msg_ideal_rel.

Lemma prf_msg_ideal_inv_memo_hit rt cnt (x : shrincs_fxmss_coord × shrincs_fxmss_bytes)
    (y : bytes 16) s0 s1 :
  prf_msg_ideal_inv (s0, s1) ->
  get_heap s0 shrincs_fxmss_rt_loc = rt ->
  get_heap s1 prf_memo_cnt_loc = cnt ->
  cnt <= get_heap s0 shrincs_fxmss_scnt_loc ->
  getm rt x = Some y ->
  prf_msg_ideal_inv
    (set_heap s0 shrincs_fxmss_rt_loc (setm rt x y),
     set_heap (set_heap s1 prf_memo_cnt_loc cnt.+1)
       shrincs_fxmss_rt_loc (setm rt x y)).
Proof.
move=> [hi hr] hrt hc hb hh.
rewrite (setmI hh) /prf_msg_ideal_inv.
split.
apply: put_pre_cond_heap_ignore; apply: heap_ignore_set_r; [by rewrite
  /prf_msg_ideal_private !domm_set !in_fset1U /= | exact: hi].
rewrite !rel_app_cons /= rel_app_nil.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_st_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_rt_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf_memo_tab_loc
  shrincs_khf_prf_msg) ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ (prf.prf_qs_loc
  shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ (prf.prf_qs_loc shrincs_khf_prf_msg)
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ prf_memo_cnt_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ prf_memo_cnt_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_scnt_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_rt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ prf_memo_cnt_loc _ shrincs_fxmss_kp_loc
  ltac:(reflexivity)) at 1.

(cbv beta iota delta [prf_msg_ideal_rel] in hr; rewrite /rel_app /get_side /= hrt hc in hr).
case: hr => hlog hbound htab hkp.
cbv beta iota delta [prf_msg_ideal_rel].
split.
-
  exact: prf_memo_log_hit hlog.
-
  by rewrite ltnS.
-
  case: (get_heap s0 shrincs_fxmss_st_loc) htab => [st|] htab; first exact: htab;
    case: htab =>
    he _ _ _; rewrite he emptymE in hh; discriminate.
-
  exact: hkp.
Qed.
