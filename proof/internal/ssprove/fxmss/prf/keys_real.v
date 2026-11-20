(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.keys_real

    The real chain-start PRF simulation couples generation and signing with the
    memoizing oracle. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude games.prf_memo games.prf_memo_state games.prf_memo_coupling
  games.prf_memo_real_coupling toolkit.relational_rules toolkit.hop_tactics.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance prf.inputs prf.reduction prf.sampling prf.schedule.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Real chain-start PRF coupling *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition prf_real_private : Locations :=
  [fmap shrincs_fxmss_ks_loc; shrincs_fxmss_keys_loc; prf_memo_tab_loc shrincs_khf_prf;
    prf_memo_cnt_loc;
    prf.prf_k_loc shrincs_khf_prf; prf.prf_qs_loc shrincs_khf_prf].

Definition prf_real_rel (sto : option shrincs_fxmss_state) (ks0 ks1 : option (bytes 16))
    (kt : shrincs_fxmss_key_table) (tab : {fmap kh_M shrincs_khf_prf -> bytes 16})
    (qs : seq (kh_M shrincs_khf_prf)) (cnt : nat) (ko : option (bytes 16)) : Prop :=
  match sto with
  | None => [/\ tab = emptym, qs = [::], cnt = 0, ko = None &
      ks0 = None /\ ks1 = None]
  | Some st => exists k, [/\ ks0 = Some k, ks1 = Some (zeros 16), ko = Some k,
      shrincs_fxmss_structure_legal st.2.1 st.2.2 &
      kt = shrincs_fxmss_prf_key_table k st.1.1.1 st.2.1 (uint U8 st.2.2)
        (shrincs_fxmss_schedule st.2)]
  end.

Definition prf_real_inv : precond :=
  heap_ignore prf_real_private ⋊ rel_app
    [:: (lhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_ks_loc); (rhs,
      shrincs_fxmss_ks_loc); (rhs, shrincs_fxmss_keys_loc);
        (rhs, prf_memo_tab_loc shrincs_khf_prf);
        (rhs, prf.prf_qs_loc shrincs_khf_prf); (rhs, prf_memo_cnt_loc);
        (rhs, prf.prf_k_loc shrincs_khf_prf)] prf_real_rel.

Lemma prf_real_inv_invariant Q bit :
  Invariant (loc (G_forge_keyed shrincs_fxmss_sha256 Q bit))
    (unionm (loc (R_prf_memo Q bit))
      (unionm (loc (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
        (loc (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true))))
    prf_real_inv.
Proof.
rewrite /prf_real_inv.
ssprove_invariant.
rewrite /rel_empty /prf_real_rel /=.
by split; try reflexivity; split.
Qed.

Lemma prf_real_inv_put (l : Location) (v : l) :
  l.1 \notin [:: shrincs_fxmss_st_loc.1; shrincs_fxmss_ks_loc.1;
    shrincs_fxmss_keys_loc.1;
    (prf_memo_tab_loc shrincs_khf_prf).1; (prf.prf_qs_loc shrincs_khf_prf).1;
    prf_memo_cnt_loc.1; (prf.prf_k_loc shrincs_khf_prf).1] ->
  put_pre_cond l v prf_real_inv.
Proof.
move=> hl.
cbv beta iota delta [prf_real_inv].
apply: put_pre_cond_conj; first exact: put_pre_cond_heap_ignore.
apply: put_pre_cond_rel_app.
move: hl.
rewrite /= !in_cons !orbF.
by rewrite (orbA (l.1 == shrincs_fxmss_ks_loc.1) (l.1 == shrincs_fxmss_ks_loc.1))
  orbb.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_real_rel get_heap set_heap.

Lemma prf_real_inv_gen st k kp s0 s1 :
  shrincs_fxmss_structure_legal st.2.1 st.2.2 ->
  heap_ignore prf_real_private (s0,s1) ->
  get_heap s1 (prf.prf_k_loc shrincs_khf_prf) = Some k ->
  prf_real_inv
    (set_heap (set_heap (set_heap (set_heap (set_heap s0
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some k))
        shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc emptym) shrincs_fxmss_sd_loc emptym,
     set_heap (set_heap (set_heap (set_heap (set_heap s1
      shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some (zeros 16)))
        shrincs_fxmss_kp_loc (Some kp))
      shrincs_fxmss_keys_loc (shrincs_fxmss_prf_key_table k st.1.1.1 st.2.1
        (uint U8 st.2.2) (shrincs_fxmss_schedule st.2))) shrincs_fxmss_sd_loc emptym).
Proof.
move=> hl hi hk.
cbv beta iota delta [prf_real_inv].
split.
-
  apply: put_pre_cond_heap_ignore.
  apply: heap_ignore_set_l;
    first by rewrite /prf_real_private !domm_set !in_fset1U /=.
  apply: heap_ignore_set_r;
    first by rewrite /prf_real_private !domm_set !in_fset1U /=.
  apply: put_pre_cond_heap_ignore.
  apply: heap_ignore_set_l;
    first by rewrite /prf_real_private !domm_set !in_fset1U /=.
  apply: heap_ignore_set_r;
    first by rewrite /prf_real_private !domm_set !in_fset1U /=.
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
rewrite -> (get_set_heap_eq _ shrincs_fxmss_ks_loc (Some k)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ shrincs_fxmss_ks_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_ks_loc (Some (zeros 16))) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ shrincs_fxmss_keys_loc
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_eq _ shrincs_fxmss_keys_loc _) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_sd_loc _ (prf.prf_k_loc shrincs_khf_prf)
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_keys_loc _ (prf.prf_k_loc shrincs_khf_prf)
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_kp_loc _ (prf.prf_k_loc shrincs_khf_prf)
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_ks_loc _ (prf.prf_k_loc shrincs_khf_prf)
ltac:(reflexivity)) at 1.
rewrite -> (get_set_heap_neq _ shrincs_fxmss_st_loc _ (prf.prf_k_loc shrincs_khf_prf)
ltac:(reflexivity)) at 1.

cbv beta iota delta [prf_real_rel].
exists k; split; try reflexivity; assumption.
Qed.

Transparent get_heap set_heap.

(* ------------------------------------------------------------------ *)
(** ** Real chain-start PRF common *)

Import Shrincs.internal.ssprove.fxmss.games.
Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_real_inv prf_real_rel dBytes kh_eval.

Lemma R_prf_real_hash (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_hmsg_input) :
  ⊢ ⦃ fun '(s0, s1) => prf_real_inv (s0, s1) ⦄
    resolve (G_forge_keyed shrincs_fxmss_sha256 Q bit)
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true)%share
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_real_inv (s0, s1) ⦄.
Proof.
rewrite !resolve_link.
have hh := resolve_forge_hash shrincs_fxmss_sha256 Q false false false (fun _ _ _ _ _
  =>
  true) bit arg.
lazymatch type of hh with _ = ?body => eapply rel_jdg_replace with (l := body) (r := code_link
  (code_link body (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
    (prf.PRF_game shrincs_khf_prf
  (shrincs_fxmss_prf_budget Q) true)) end.
2: by (cbv beta iota delta [G_forge_keyed]; rewrite hh).
2: by rewrite resolve_R_prf_hash /G_forge_sampledkey resolve_forge_hash.
clear hh.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => have hv : ValidCode [fmap
  shrincs_fxmss_done_loc; shrincs_fxmss_hcnt_loc; shrincs_fxmss_rom_loc] emptym c by
    rewrite /shrincs_fxmss_lookup; ssprove_valid end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => rewrite (code_link_scheme
  _ _ c p hv) (code_link_scheme _ _ c p' hv) end.

apply: (r_reflexivity_alt prf_real_inv _ hv).
- move=> l hl s0 s1 [hi hr].
apply: hi.
by fmap_invert hl; fmap_solve.
- move=> l v hl.
apply: prf_real_inv_put.
by fmap_invert hl.
Qed.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_real_inv prf_real_rel dBytes kh_eval
  scheme.shrincs_fxmss_verify.

Lemma R_prf_real_forge (Q : shrincs_fxmss_resources) (bit : bool)
    (arg : shrincs_fxmss_message × shrincs_fxmss_bytes) :
  ⊢ ⦃ fun '(s0, s1) => prf_real_inv (s0, s1) ⦄
    resolve (G_forge_keyed shrincs_fxmss_sha256 Q bit) shrincs_fxmss_forge_op arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true)%share
      shrincs_fxmss_forge_op arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_real_inv (s0, s1) ⦄.
Proof.
case: arg => cm sg.
rewrite !resolve_link.
have hh := resolve_forge shrincs_fxmss_sha256 Q false false false (fun _ _ _ _ _ =>
  true) bit cm sg.
lazymatch type of hh with _ = ?body => eapply rel_jdg_replace with (l := body) (r := code_link
  (code_link body (prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q)))
    (prf.PRF_game shrincs_khf_prf
  (shrincs_fxmss_prf_budget Q) true)) end.
2: by (cbv beta iota delta [G_forge_keyed]; rewrite hh).
2: by rewrite resolve_R_prf_forge /G_forge_sampledkey resolve_forge.
clear hh.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => have hv : ValidCode
  shrincs_fxmss_locs emptym c by ssprove_valid; apply: shrincs_fxmss_forge_body_valid
    end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => rewrite (code_link_scheme
  _ _ c p hv) (code_link_scheme _ _ c p' hv) end.
eapply r_bind with (mid := fun '(v0,s0) '(v1,s1) => v0 = v1 /\ prf_real_inv (s0,s1)).
2: { move=> v0 v1.
apply r_ret.
by move=> s0 s1 [-> hi]; split.
} clear hv.
rewrite /shrincs_fxmss_forge_body.
ssprove_code_simpl.

ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
} move=> sto.
ssprove_code_simpl.
ssprove_sync.
move=> hsto.
ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
} move=> done.
ssprove_sync.
move=> hdone.
ssprove_sync.
{ apply: prf_real_inv_put.
by [].
} ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_log_loc (ltac:(fmap_solve)).
} move=> lg.
eapply r_get_remember_lhs => kt0.
eapply r_get_remember_rhs => kt1.
eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_real_inv (s0,s1)); last by move=> s0
  s1 [[h _] _].
apply: (r_reflexivity_alt (L := [fmap shrincs_fxmss_sd_loc; shrincs_fxmss_rt_loc;
  shrincs_fxmss_rom_loc]) prf_real_inv).
- rewrite /shrincs_fxmss_lookup.
ssprove_valid.
- move=> l hl s0 s1 [hi hr].
apply: hi.
by fmap_invert hl; fmap_solve.
- move=> l v hl.
apply: prf_real_inv_put.
by fmap_invert hl.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real chain-start PRF gen *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys shrincs_fxmss_prf_derive_table
  shrincs_fxmss_prf_derive_leaf.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque scheme.shrincs_fxmss_node prf_real_inv prf_real_rel kh_eval
  get_heap set_heap G_forge_keyed G_forge R_prf_memo prf_memo.R_prf_memo
  prf.PRF_game prf_memo_key_rel.

Lemma R_prf_real_gen (Q : shrincs_fxmss_resources) (bit : bool) (arg :
  shrincs_fxmss_setup) :
  ⊢ ⦃ fun '(s0, s1) => prf_real_inv (s0, s1) ⦄
    resolve (G_forge_keyed shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_gen,
      (shrincs_fxmss_setup, bytes 48)) arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true)%share
      (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) arg
    ⦃ fun '(b0, s0) '(b1, s1) => b0 = b1 /\ prf_real_inv (s0, s1) ⦄.
Proof.
(rewrite !resolve_link).

(have hr := resolve_R_prf_gen Q bit arg).
(eapply rel_jdg_replace with (l := resolve (G_forge_keyed shrincs_fxmss_sha256 Q bit)
  (shrincs_fxmss_op_gen,(shrincs_fxmss_setup,bytes 48)) arg) (r := code_link
    (code_link (shrincs_fxmss_prf_gen arg) (prf_memo.R_prf_memo
  shrincs_khf_prf (shrincs_fxmss_prf_budget Q))) (prf.PRF_game shrincs_khf_prf
    (shrincs_fxmss_prf_budget Q) true))).
2: reflexivity.
2: by rewrite hr.
have hl := resolve_forge_gen shrincs_fxmss_sha256 Q false false false (fun _ _ _ _ _
  =>
  true) bit arg.
lazymatch type of hl with _ = ?body => eapply rel_jdg_replace with (l := body) end.

2: (by (cbv beta iota delta [G_forge_keyed]; rewrite -hl)).
2: reflexivity.
clear hl hr.
(cbn [shrincs_fxmss_prf_gen]).

ssprove_code_simpl.
eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{ move=> s0 s1 [[hi hr] hs].
have he := hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
by rewrite -he; exact: hs.
} ssprove_code_simpl.
fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hsto _.
case: sto hsto => [st|] hsto; first discriminate.
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{ move=> s0 s1 [[[hi hr] hs] hd].
have he := hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
by rewrite -he; exact: hd.
} fold @code_link.
rewrite !code_link_assertD.
eapply r_assertD; first by [].
move=> hdone _.
eapply r_assertD; first by [].
move=> hlegal _.
set genrel := fun (tab : {fmap kh_M shrincs_khf_prf -> bytes 16})
(qs : seq (kh_M shrincs_khf_prf)) (cnt : nat) (ko : option (bytes 16)) =>
fun '(s0,s1) => [/\ heap_ignore prf_real_private (s0,s1),
get_heap s1 (prf_memo_tab_loc shrincs_khf_prf) = tab,
get_heap s1 (prf.prf_qs_loc shrincs_khf_prf) = qs &
get_heap s1 prf_memo_cnt_loc = cnt] /\
get_heap s1 (prf.prf_k_loc shrincs_khf_prf) = ko.
eapply rpre_weaken_rule with (pre := genrel emptym [::] 0 None); last first.
{ move=> s0 s1 [[[hi hr] hs] hd].
rewrite /rem_inv /get_side /= in hs.

(cbv beta iota delta [prf_real_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
case: hr => ht hq hc hk hks.
split; first by split.
exact: hk.
}
rewrite (code_link_bind (dBytes 16))
(code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
rewrite (code_link_bind (dBytes 16))
(code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
eapply r_scheme_bind; first exact: prog_valid.
move=> pp; cbv beta.
cbv beta delta [prf_memo.R_prf_memo prf.PRF_game].
simplify_linking.
eapply (r_get_rhs_known prf_memo_cnt_loc 0 (genrel emptym [::] 0 None)); first by
move=> s0 s1 [[_ _ _ hc] hk].
fold @code_link.
simplify_linking.
eapply (r_put_rhs_weak prf_memo_cnt_loc 1 (genrel emptym [::] 0 None) (genrel emptym
[::] 1 None)).
{ move=> s0 s1 [[hi ht hq hc] hk]; split; last by rewrite get_set_heap_neq // hk.
split.
- apply heap_ignore_set_r; last exact: hi.
by rewrite /prf_real_private !domm_set !in_fset1U /=.
- by rewrite get_set_heap_neq // ht.
- by rewrite get_set_heap_neq // hq.
- by rewrite get_set_heap_eq.
} eapply (r_get_rhs_known (prf_memo_tab_loc shrincs_khf_prf) emptym (genrel emptym
[::] 1 None)); first by move=> s0 s1 [[_ ht _ _] hk].
simplify_linking.
eapply (r_get_rhs_known (prf.prf_qs_loc shrincs_khf_prf) [::] (genrel emptym [::]
1 None)); first by move=> s0 s1 [[_ _ hq _] hk].
eapply (r_bind_assertD_rhs _ (genrel emptym [::] 1 None)); first by [].
move=> _.
eapply (r_bind_assertD_rhs _ (genrel emptym [::] 1 None)); first by [].
move=> _.
eapply (r_put_bind_rhs _ _ (genrel emptym [::] 1 None) (genrel emptym [::
  (shrincs_fxmss_prf_pin pp)]
1 None)).
{ move=> s0 s1 [[hi ht hq hc] hk]; split; last by rewrite get_set_heap_neq // hk.
split.
- apply heap_ignore_set_r; last exact: hi.
by rewrite /prf_real_private !domm_set !in_fset1U /=.
- by rewrite get_set_heap_neq // ht.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // hc.
} ssprove_code_simpl.
eapply (r_get_rhs_known (prf.prf_k_loc shrincs_khf_prf) None (genrel emptym [::
(shrincs_fxmss_prf_pin pp)] 1 None)); first by move=> s0 s1 [hi hk].
ssprove_code_simpl.
fold @bind.
rewrite bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> ks; cbv beta.
ssprove_code_simpl.
eapply (r_put_rhs_weak (prf.prf_k_loc shrincs_khf_prf) (Some ks) (genrel emptym
[:: (shrincs_fxmss_prf_pin pp)] 1 None) (genrel emptym [:: (shrincs_fxmss_prf_pin pp)]
  1 (Some ks))).
{ move=> s0 s1 [[hi ht hq hc] hk]; split; last exact: get_set_heap_eq.
split.
- apply heap_ignore_set_r; last exact: hi.
by rewrite /prf_real_private !domm_set !in_fset1U /=.
- by rewrite get_set_heap_neq // ht.
- by rewrite get_set_heap_neq // hq.
- by rewrite get_set_heap_neq // hc.
} eapply (r_put_rhs_weak (prf_memo_tab_loc shrincs_khf_prf) (setm emptym
  (shrincs_fxmss_prf_pin pp)
(kh_eval shrincs_khf_prf ks (shrincs_fxmss_prf_pin pp))) (genrel emptym [::
  (shrincs_fxmss_prf_pin pp)] 1
(Some ks)) (genrel (setm emptym (shrincs_fxmss_prf_pin pp) (kh_eval shrincs_khf_prf ks
(shrincs_fxmss_prf_pin pp))) [:: (shrincs_fxmss_prf_pin pp)] 1 (Some ks))).
{ move=> s0 s1 [[hi ht hq hc] hk]; split; last by rewrite get_set_heap_neq // hk.
split.
- apply heap_ignore_set_r; last exact: hi.
by rewrite /prf_real_private !domm_set !in_fset1U /=.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // hq.
- by rewrite get_set_heap_neq // hc.
} ssprove_code_simpl.
fold @code_link.
rewrite (code_link_bind (dBytes 16)) (code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
rewrite (code_link_bind (dBytes 16)) (code_link_scheme _ _ _ _ (prog_valid (dBytes 16))).
eapply r_scheme_bind; first exact: prog_valid.
move=> kp; cbv beta.
eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_memo_key_rel shrincs_khf_prf
  prf_real_private [:: shrincs_fxmss_prf_pin pp] 1 ks (s0,s1)); last first.
{ move=> s0 s1 [[hi ht hq hc] hk].
split; last by rewrite /rel_app /get_side /= hk.
split; first exact: hi.
rewrite /rel_app /get_side /= ht hq hc.
split; try reflexivity.
exact (@prf_memo_log_set shrincs_khf_prf emptym [::] 0 (shrincs_fxmss_prf_pin pp)
  (kh_eval
  shrincs_khf_prf ks (shrincs_fxmss_prf_pin pp)) (prf_memo_log_empty
    shrincs_khf_prf)).
}
rewrite (code_link_bind (shrincs_fxmss_prf_derive_table pp arg.1.1 (uint
  jasmin_wsize.U8 arg.1.2)
  (shrincs_fxmss_schedule arg.1))).
rewrite (code_link_bind (code_link (shrincs_fxmss_prf_derive_table pp arg.1.1 (uint
  jasmin_wsize.U8
  arg.1.2) (shrincs_fxmss_schedule arg.1)) _)).
lazymatch goal with |- ⊢ ⦃ ?pre ⦄ ?l ≈ ?r ⦃ ?post ⦄ => eapply r_bind with (m₀ := ret
  (shrincs_fxmss_prf_key_table ks pp arg.1.1 (uint jasmin_wsize.U8 arg.1.2)
    (shrincs_fxmss_schedule arg.1))) (f₀ :=
  fun _ => l) (mid := fun '(kt0,s0) '(kt1,s1) => kt0 = shrincs_fxmss_prf_key_table ks
    pp arg.1.1 (uint
  jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1) /\ kt0 = kt1 /\
    prf_memo_key_rel
  shrincs_khf_prf prf_real_private (shrincs_fxmss_prf_pin pp ::
    Shrincs.internal.ssprove.fxmss.prf.schedule.shrincs_fxmss_prf_queries pp arg.1.1
  (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1)) (size
    (shrincs_fxmss_schedule arg.1) *
  wots_c_chain_count).+1 ks (s0,s1)) end.
- (* The scheduled real PRF queries return the deterministic key table. *)
  apply: (@r_ret_lhs_fact shrincs_fxmss_key_table shrincs_fxmss_key_table _ _ _ (fun
  '(kt0,s0) '(kt1,s1) => kt0 =
  kt1 /\ prf_memo_key_rel shrincs_khf_prf prf_real_private (shrincs_fxmss_prf_pin pp
    ::
  Shrincs.internal.ssprove.fxmss.prf.schedule.shrincs_fxmss_prf_queries pp arg.1.1
    (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1))
  (size (shrincs_fxmss_schedule arg.1) * wots_c_chain_count).+1 ks (s0,s1))).
apply: r_prf_real_schedule; try by rewrite /prf_real_private !domm_set !in_fset1U /=.
exact: hlegal.
- move=> kt0 kt1.
eapply rpre_hypothesis_rule => s0 s1 [he [he' hr]].
subst kt0 kt1.
have hroot := @shrincs_fxmss_prf_root_congr shrincs_fxmss_sha256
  (scheme.shrincs_fxmss_derived_keys shrincs_fxmss_sha256 pp ks
  arg.1.1 (uint jasmin_wsize.U8 arg.1.2)) (fun a => odflt [::] (getm
    (shrincs_fxmss_prf_key_table ks pp
  arg.1.1 (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1)) a)) pp
    arg.1.1 arg.1.2 hlegal.
have hk : forall a, a \in shrincs_fxmss_schedule arg.1 ->
  scheme.shrincs_fxmss_derived_keys shrincs_fxmss_sha256 pp
  ks arg.1.1 (uint jasmin_wsize.U8 arg.1.2) a = odflt [::] (getm
    (shrincs_fxmss_prf_key_table ks pp
  arg.1.1 (uint jasmin_wsize.U8 arg.1.2) (shrincs_fxmss_schedule arg.1)) a).
{ move=> a ha.
rewrite shrincs_fxmss_prf_key_table_lookup //.
} have he := hroot hk.
rewrite he !code_link_assertD.
ssprove_code_simpl.
eapply (@r_assertD (bytes 48) (bytes 48)); first by [].
move=> hro _.
eapply rpre_weaken_rule with (pre := fun '(t0,t1) => heap_ignore prf_real_private (t0,t1) /\
  get_heap t1 (prf.prf_k_loc shrincs_khf_prf) = Some ks); last first.
{ move=> t0 t1 /= [-> ->].

have [[hi hm] hk'] := hr.
by split.
} eapply (r_put_lhs _ _ _ _ (fun '(t0,t1) => heap_ignore prf_real_private (t0,t1) /\ get_heap
  t1 (prf.prf_k_loc shrincs_khf_prf) = Some ks)).
do 4 apply r_put_lhs.
do 5 apply r_put_rhs.
apply r_ret.
move=> t0 t1 h.
do 10 (let s := fresh "s" in case: h => s [h ->]).
case: h => hi hk'.
split; first reflexivity.
apply: prf_real_inv_gen; [exact: hlegal | exact: hi | exact: hk'].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Real chain-start PRF sign *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque dBytes shrincs_fxmss_sample_keys shrincs_fxmss_prf_derive_table
  shrincs_fxmss_prf_derive_leaf.

(* Keep heap operations and oracle bodies folded during coupling simplification. *)
Local Opaque prf_real_inv prf_real_rel kh_eval scheme.shrincs_fxmss_node
  scheme.shrincs_fxmss_sign PRF_msg_sf shrincs_sf_encode
  scheme.shrincs_fxmss_derived_keys get_heap set_heap.

Lemma R_prf_real_sign (Q : shrincs_fxmss_resources) (bit : bool) (arg :
  shrincs_fxmss_message) :
  ⊢ ⦃ fun '(s0,s1) => prf_real_inv (s0,s1) ⦄
    resolve (G_forge_keyed shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) arg
    ≈ resolve
      ((R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget
        Q))
        ∘ prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true)%share
      (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) arg
    ⦃ fun '(b0,s0) '(b1,s1) => b0 = b1 /\ prf_real_inv (s0,s1) ⦄.
Proof.
rewrite !resolve_link.
have hl := resolve_forge_sign shrincs_fxmss_sha256 Q false false false (fun _ _ _ _ _
  =>
  true) bit arg.
have hr := resolve_forge_sign shrincs_fxmss_sha256 Q true false false (fun _ _ _ _ _
  =>
  true) bit arg.
lazymatch type of hl with _ = ?body0 => lazymatch type of hr with _ = ?body1 => eapply
  rel_jdg_replace with (l := body0) (r := code_link (code_link body1 (prf_memo.R_prf_memo shrincs_khf_prf
  (shrincs_fxmss_prf_budget Q))) (prf.PRF_game shrincs_khf_prf
    (shrincs_fxmss_prf_budget Q) true)) end end.
2: (exact (esym hl)).
2: { (rewrite resolve_R_prf_sign).
exact: (congr1 (fun c => code_link (code_link c (prf_memo.R_prf_memo shrincs_khf_prf
  (shrincs_fxmss_prf_budget Q)))
  (prf.PRF_game shrincs_khf_prf (shrincs_fxmss_prf_budget Q) true)) (esym hr)).
} clear hl hr.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => have hv : ValidCode
  shrincs_fxmss_locs emptym c by (ssprove_valid; apply: shrincs_fxmss_lookup_valid)
    end.
lazymatch goal with |- context [code_link (code_link ?c ?p) ?p'] => (rewrite
  (code_link_scheme _ _ c p hv) (code_link_scheme _ _ c p' hv)) end.
clear hv.
ssprove_code_simpl.

eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{ move=> s0 s1 [[hi hr] hs].
have he := hi shrincs_fxmss_st_loc (ltac:(fmap_solve)).
by rewrite -he; exact: hs.
} ssprove_code_simpl.
ssprove_sync.
move=> hsto.
case: sto hsto => [st|] hsto; last discriminate.
have hput : forall (l : Location) (v : l), l.1 \notin [:: shrincs_fxmss_st_loc.1;
  shrincs_fxmss_ks_loc.1;
  shrincs_fxmss_keys_loc.1; (prf_memo_tab_loc shrincs_khf_prf).1; (prf.prf_qs_loc
    shrincs_khf_prf).1;
  prf_memo_cnt_loc.1; (prf.prf_k_loc shrincs_khf_prf).1] -> put_pre_cond l v (prf_real_inv ⋊
  rem_lhs shrincs_fxmss_st_loc (Some st)).
{ move=> l v hl.
apply: put_pre_cond_conj; first exact: prf_real_inv_put hl.
apply: put_pre_cond_rem.
move: hl.
rewrite in_cons => /norP [hs _].
by rewrite eq_sym.
} ssprove_code_simpl.
ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_done_loc (ltac:(fmap_solve)).
} move=> done.
ssprove_sync.
move=> hdone.
ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_scnt_loc (ltac:(fmap_solve)).
} move=> sc.
ssprove_sync.
move=> hsc.
ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_log_loc (ltac:(fmap_solve)).
} move=> lg.
(apply r_put_vs_put).
eapply rpre_weaken_rule with (pre := fun '(s0,s1) => (prf_real_inv ⋊ rem_lhs
  shrincs_fxmss_st_loc (Some
  st)) (s0,s1)); last first.
{ move=> s0 s1 [s1' [[s0' [h ->]] ->]].
exact (hput shrincs_fxmss_scnt_loc sc.+1 (ltac:(by [])) s0' s1' h).
} (apply r_put_vs_put).
eapply rpre_weaken_rule with (pre := fun '(s0,s1) => (prf_real_inv ⋊ rem_lhs
  shrincs_fxmss_st_loc (Some
  st)) (s0,s1)); last first.
{ move=> s0 s1 [s1' [[s0' [h ->]] ->]].
exact (hput shrincs_fxmss_log_loc (arg :: lg) (ltac:(by [])) s0' s1' h).
} cbv zeta.
case: ifP => hmsg; last first.
{ apply r_ret.
by move=> s0 s1 [hi hs]; split.
} ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_next_loc (ltac:(fmap_solve)).
} move=> q.
case hleaf: (shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 q) => [a|]; last first.
{ apply r_ret.
by move=> s0 s1 [hi hs]; split.
} (apply r_put_vs_put).
eapply rpre_weaken_rule with (pre := fun '(s0,s1) => (prf_real_inv ⋊ rem_lhs
  shrincs_fxmss_st_loc (Some
  st)) (s0,s1)); last first.
{ move=> s0 s1 [s1' [[s0' [h ->]] ->]].
exact (hput shrincs_fxmss_next_loc q.+1 (ltac:(by [])) s0' s1' h).
} eapply r_get_remember_lhs => ks0.
eapply r_get_remember_rhs => ks1.

(eapply (r_fact (isSome ks0 = isSome ks1))).
{ move=> s0 s1 [[[[hi hr] hs] hk0] hk1].

rewrite /rem_inv /get_side /= in hs hk0 hk1.
(cbv beta iota delta [prf_real_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
case: hr => k [he0 he1 hkey hlegal ht].
by rewrite -hk0 -hk1 he0 he1.
} move=> hks.
(eapply (@r_assertD ('option shrincs_fxmss_bytes) ('option shrincs_fxmss_bytes)));
  first by move=> s _.
move=> hks0 hks1.
ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_kp_loc (ltac:(fmap_solve)).
} move=> kp.
ssprove_sync.
move=> hkp.
(eapply r_get_remember_lhs => kt0).
(eapply r_get_remember_rhs => kt1).
(eapply (r_fact (forall md : bytes 32, scheme.shrincs_fxmss_sign shrincs_fxmss_sha256
  md
  (scheme.shrincs_fxmss_derived_keys shrincs_fxmss_sha256 st.1.1.1 (getSome ks0 hks0)
    st.2.1 (uint
  jasmin_wsize.U8 st.2.2)) a.2 a.1 st.1.1.1 st.2.1 (uint jasmin_wsize.U8 st.2.2) =
  scheme.shrincs_fxmss_sign shrincs_fxmss_sha256 md (fun x => odflt [::] (getm kt1 x))
    a.2 a.1 st.1.1.1
  st.2.1 (uint jasmin_wsize.U8 st.2.2)))).
{ move=> s0 s1 [[[[[[hi hr] hs] hk0] hk1] ht0] ht1] md.
rewrite /rem_inv /get_side /= in hs hk0 ht1.
(cbv beta iota delta [prf_real_rel] in hr; rewrite /rel_app /get_side /= hs in hr).
case: hr => k [he0 he1 hkey hlegal ht].
have he : ks0 = Some k by rewrite -hk0 he0.
have hget : getSome ks0 hks0 = k by move: hks0; rewrite he.
rewrite hget -ht1 ht.
apply: shrincs_fxmss_prf_sign_selected_congr hleaf _.
move=> x hx.
rewrite shrincs_fxmss_prf_key_table_lookup //.
} move=> hsign.
eapply rpre_weaken_rule with (pre := fun '(s0,s1) => prf_real_inv (s0,s1)); last by move=> s0
  s1 [[[[[hi _] _] _] _] _].
ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_rt_loc (ltac:(fmap_solve)).
} move=> rt.
(case hro: (PRF_msg_sf (getSome kp hkp) st.1.1.1 a.1 a.2 (shrincs_fxmss_bound_message
  arg)) => [r|]); last first.
{ apply r_ret.
by move=> s0 s1 hi; split.
} ssprove_sync.
{ apply: prf_real_inv_put.
by [].
} ssprove_sync.
{ move=> s0 s1 [hi hr].
exact: hi shrincs_fxmss_rom_loc (ltac:(fmap_solve)).
} move=> mp.
(case hmd: (getm mp (r, ((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message arg))))
  => [md|]).
- (rewrite hsign).
(case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|]); apply r_ret; by move=>
  s0 s1 hi; split.
- (eapply r_scheme_bind); first exact: prog_valid.
move=> md; cbv beta.
ssprove_sync.
{ apply: prf_real_inv_put.
by [].
} (rewrite hsign).
(case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|]); apply r_ret; by move=>
  s0 s1 hi; split.
Qed.
