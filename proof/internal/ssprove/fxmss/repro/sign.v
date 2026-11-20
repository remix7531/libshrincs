(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.repro.sign

    Real and reprogrammed signing simulations preserve the leaf schedule, attempt
    log and random-oracle cache. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.ro_plus toolkit.reprogram_sep toolkit.relational_rules.
From Shrincs Require Import schemes spec.
From Shrincs.internal.ssprove.fxmss Require Import
  params games bound.reprogramming repro.games repro.invariant shape.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming sample *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition repro_at (Q : shrincs_fxmss_resources) (st : shrincs_fxmss_state) (q : nat) :
  precond :=
  repro_inv Q ⋊ rel_app [:: (lhs, shrincs_fxmss_st_loc); (lhs, shrincs_fxmss_next_loc)]
    (fun sto q' => sto = Some st /\ q' = q).

Definition repro_sample_pre Q st q (x : repro_suffix) : precond :=
  repro_at Q st q ⋊ rel_app [:: (rhs, ro_used_loc shrincs_fxmss_coord)]
    (fun used => repro_separator x \notin used).

Lemma repro_sample_ideal P Q st q x
    (hp : repro_past st.2.1 st.2.2 q (repro_separator x)) :
  ⊢ ⦃ fun '(h0, h1) => repro_sample_pre Q st q x (h0, h1) ⦄
    repro_sample P x ≈
    code_link (repro_sample_call x)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) true)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_at Q st q (h0, h1) ⦄.
Proof.
rewrite /repro_sample /repro_sample_call.
simplify_linking.
eapply r_get_remember_rhs => used.
eapply (r_fact (repro_separator x \notin used)).
{
  move=> h0 h1 [[ha hf] hu].
  rewrite /rel_app /get_side /= in hf.
  rewrite /rem_inv /get_side /= in hu.
  by rewrite hu in hf.
}
move=> hf.
rewrite hf.
ssprove_code_simpl.
simpl.
eapply r_put_rhs.
rewrite !bind_assoc.
eapply (r_scheme_bind (shrincs_fxmss_secret_dist P)); first exact: prog_valid.
move=> r.
cbv beta.
eapply r_get_remember_rhs => mp.
fold @bind.
rewrite !bind_assoc.
eapply (r_scheme_bind (shrincs_fxmss_digest_dist P)); first exact: prog_valid.
move=> md.
cbv beta.
eapply r_get_remember_lhs => mp0.
eapply (r_fact (mp0 = mp)).
{
  move=> s0 s1 [[[s1a [hpre ->]] hm] hm0].
  case: hpre => [[[[hi hr] hat] hf0] hu].
  rewrite /rem_inv /get_side /= in hm hm0.
  rewrite get_set_heap_neq in hm; first by [].
  case: hr => he hc hq.
  rewrite /get_side /= in he.
  by rewrite -hm0 -hm.
}
move=> ->.
eapply r_put_lhs.
eapply r_put_rhs.
ssprove_code_simpl.
simpl.
eapply (r_get_rhs_known (ro_used_loc shrincs_fxmss_coord) (repro_separator x ::
  used)).
{
  move=> s0 s1 [s1b [hpre ->]].
  case: hpre => s0a [hpre he0].
  subst s0.
  case: hpre => [[[s1a [hpre ->]] hm] hm0].
  rewrite get_set_heap_neq; first by [].
  by rewrite get_set_heap_eq.
}
eapply r_get_remember_rhs => qc.
rewrite in_cons eqxx /= addn0.
ssprove_code_simpl.
simpl.
eapply r_put_rhs.
eapply (r_get_rhs_known (ro_map_loc (bytes 16) repro_suffix (bytes 32)) (setm mp (r, x) md)).
{
  move=> s0 s1 [s1c [hpre ->]].
  case: hpre => [[s1b [hpre ->]] hqc].
  rewrite get_set_heap_neq; first by [].
  by rewrite get_set_heap_eq.
}
rewrite setmE eqxx.
ssprove_code_simpl.
simpl.
apply r_ret => s0 s1 hpre.
split; first by [].
case: hpre => s1c [hpre he1].
subst s1.
case: hpre => [[s1b [hpre he1]] hqc].
subst s1c.
case: hpre => s0a [hpre he0].
subst s0.
case: hpre => [[[s1a [hpre he1]] hm] hm0].
subst s1b.
case: hpre => [[[[hi hr] hat] hf0] hu].
rewrite /rel_app /get_side /= in hat.
case: hat => hst hnext.
split.
- split.
  + do 3 (apply: heap_ignore_set_r;
    first by rewrite /repro_private_locs domm_mkfmap !inE /=).
    apply: heap_ignore_set_l.
    * by rewrite /repro_private_locs domm_mkfmap !inE /=.
    * exact: hi.
  + rewrite /rel_app /get_side /=.
    rewrite /rel_app /get_side /= in hr.
    case: hr => hmap hcons hq.
    split;
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    * by [].
    * rewrite hst hnext in hcons *.
      rewrite /rem_inv /get_side /= in hu.
      rewrite hu in hcons.
      case: hcons => ht hu0.
      split; first exact: ht.
      move=> a.
      rewrite in_cons => /orP[/eqP ->|ha].
      -- exact: hp.
      -- exact: hu0 ha.
    * rewrite /rem_inv /get_side /= in hqc.
      rewrite get_set_heap_neq in hqc; first by [].
      rewrite get_set_heap_neq in hqc; first by [].
      by rewrite -hqc.
- split.
  + rewrite /get_side /=.
    rewrite get_set_heap_neq; first by [].
    exact: hst.
  + rewrite /get_side /=.
    rewrite get_set_heap_neq; first by [].
    exact: hnext.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming sign *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma repro_sample_call_unfold (x : repro_suffix) :
  repro_sample_call x =
  (r ← call [ REPRO ] : { repro_suffix ~> bytes 16 } x ;;
   md ← call [ QUERY ] : { shrincs_fxmss_hmsg_input ~> bytes 32 } (r, x) ;;
   ret (r, md)).
Proof. by []. Qed.

(* Keep sampling calls folded while simplifying the signing oracle. *)
Local Opaque repro_sample_call.

Lemma repro_sign_ideal P Q cm :
  ⊢ ⦃ fun '(h0, h1) => repro_inv Q (h0, h1) ⦄
    repro_sign_body P Q (repro_sample P) cm ≈
    code_link (repro_sign_body P Q repro_sample_call cm)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) true)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1) ⦄.
Proof.
rewrite /repro_sign_body.
ssprove_code_simpl.
simpl.
rewrite /repro_inv.
eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{
  move=> s0 s1 [[hi hr] hst].
  by rewrite -(hi shrincs_fxmss_st_loc (ltac:(fmap_solve))); exact: hst.
}
case: sto => [st|] /=.
2: {
  exact: r_fail.
}
ssprove_sync => done.
ssprove_code_simpl.
simpl.
ssprove_sync => hdone.
eapply r_get_remember_lhs => sc.
eapply (r_get_rhs_known shrincs_fxmss_scnt_loc sc).
{
  move=> s0 s1 [[[hi hr] hst] hsc].
  by rewrite -(hi shrincs_fxmss_scnt_loc (ltac:(fmap_solve))); exact: hsc.
}
ssprove_code_simpl.
simpl.
ssprove_sync => hsc.
ssprove_sync => lg.
eapply r_put_lhs.
eapply r_put_rhs.
eapply r_put_lhs.
eapply r_put_rhs.
eapply rpre_weaken_rule with
(pre := fun '(h0, h1) =>
(repro_inv Q ⋊ rem_lhs shrincs_fxmss_st_loc (Some st)) (h0, h1)).
2: {
  move=> s0 s1 hpre.
  do 2 (case: hpre => ? [[? [hpre ->]] ->]).
  case: hpre => [[[hi hr] hst] hsc0].
  split.
  - split.
    + do 2 apply: put_pre_cond_heap_ignore.
      exact: hi.
    + rewrite /rel_app /get_side /=.
      rewrite /rel_app /get_side /= in hr.
      case: hr => hmap hcons hquota.
      split;
      repeat first
        [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
      * exact: hmap.
      * exact: hcons.
      * rewrite /rem_inv /get_side /= in hsc0.
        rewrite hsc0 in hquota.
        have h := repro_quota_sign Q _ _ _ _ false hquota hsc.
        by rewrite addn0 in h.
  - rewrite /rem_inv /get_side /= in hst *.
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    exact: hst.
}
case hvalid: (shrincs_fxmss_message_valid cm).
2: {
  apply r_ret => s0 s1 [hinv hst].
  by split.
}
eapply r_get_remember_lhs => q.
eapply (r_get_rhs_known shrincs_fxmss_next_loc q).
{
  move=> s0 s1 [[[hi hr] hst] hq].
  by rewrite -(hi shrincs_fxmss_next_loc (ltac:(fmap_solve))); exact: hq.
}
case hsel: (shrincs_fxmss_select_leaf st.2.1 st.2.2 q) => [a|].
2: {
  apply r_ret => s0 s1 [[hinv hst] hq].
  by split.
}
eapply r_put_lhs.
eapply r_put_rhs.
rewrite /repro_inv.
ssprove_sync => kso.
move=> s1 [s1a [[s0a [hpre ->]] ->]].
case: hpre => [[[hi hr] hst] hq].
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
exact: hi shrincs_fxmss_ks_loc (ltac:(fmap_solve)).
ssprove_sync => hkso.
ssprove_sync => kpo.
{
  move=> s1 [s1a [[s0a [hpre ->]] ->]].
  case: hpre => [[[hi hr] hst] hq].
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  exact: hi shrincs_fxmss_kp_loc (ltac:(fmap_solve)).
}
ssprove_sync => hkpo.
ssprove_sync => kt.
{
  move=> s1 [s1a [[s0a [hpre ->]] ->]].
  case: hpre => [[[hi hr] hst] hq].
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  exact: hi shrincs_fxmss_keys_loc (ltac:(fmap_solve)).
}
eapply r_get_remember_lhs => rt.
eapply (r_get_rhs_known shrincs_fxmss_rt_loc rt).
{
  move=> s0 s1 [[s1a [[s0a [hpre ->]] ->]] hrt].
  case: hpre => [[[hi hr] hst] hq].
  rewrite /rem_inv /get_side /= in hrt.
  rewrite get_set_heap_neq in hrt; first by [].
  rewrite get_set_heap_neq; first by [].
  by rewrite -(hi shrincs_fxmss_rt_loc (ltac:(fmap_solve))).
}
eapply (r_fact (repro_table_consumed st.2.1 st.2.2 q rt)).
{
  move=> s0 s1 [[s1a [[s0a [hpre ->]] ->]] hrt].
  case: hpre => [[[hi [hmap hcons hquota]] hst] hq].
  rewrite /rem_inv /get_side /= in hrt hst hq.
  rewrite get_set_heap_neq in hrt; first by [].
  rewrite /get_side /= hst hq hrt in hcons.
  exact: hcons.1.
}
move=> htable.
eapply rpre_weaken_rule with
(pre := fun '(h0, h1) => repro_sample_pre Q st q.+1
((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message cm)) (h0, h1)).
2: {
  move=> s0 s1 [[s1a [[s0a [hpre ->]] ->]] hrt].
  case: hpre => [[[hi [hmap hcons hquota]] hst] hq].
  rewrite /rem_inv /get_side /= in hst hq.
  rewrite /get_side /= in hmap hcons hquota.
  rewrite hst hq in hcons.
  case: hcons => ht hu.
  split.
  - split.
    + split.
      * apply: put_pre_cond_heap_ignore.
        exact: hi.
      * rewrite /rel_app /get_side /=.
        split;
        repeat first
          [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
        -- exact: hmap.
        -- rewrite hst.
          split.
          ++ move=> k hk.
            exact: repro_past_mono (ht k hk).
          ++ move=> k hk.
            exact: repro_past_mono (hu k hk).
        -- exact: hquota.
    + split.
      * rewrite /get_side /= get_set_heap_neq; first by [].
        exact: hst.
      * by rewrite /get_side /= get_set_heap_eq.
  - rewrite /rel_app /get_side /= get_set_heap_neq; first by [].
    exact: repro_separator_fresh hu hsel.
}
rewrite code_link_bind.
eapply r_bind with
(mid := fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_at Q st q.+1 (h0, h1)).
- (* The selected leaf is past after advancing the signing counter. *)
  have hp : repro_past st.2.1 st.2.2 q.+1 a.
  {
    exists q; by split; first exact: ltnSn.
  }
  have hd := repro_sample_ideal P Q st q.+1
  ((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message cm)) hp.
  rewrite repro_sample_call_unfold code_link_bind in hd.
  exact: hd.
- (* The ideal signing result preserves the advanced reprogramming invariant. *)
  move=> rm0 rm1.
  eapply rpre_hypothesis_rule => h0 h1 [-> hat].
  ssprove_code_simpl.
  simpl.
  set fixed : precond := fun s => s.1 = h0 /\ s.2 = h1.
  eapply rpre_weaken_rule with (pre := fun '(s0, s1) => fixed (s0, s1)).
  2: by [].
  eapply r_put_lhs.
  eapply r_put_rhs.
  case: (scheme.shrincs_fxmss_sign P rm1.2 (fun a => odflt [::] (getm kt a))
  a.2 a.1 st.1.1.1 st.2.1 (uint jasmin_wsize.U8 st.2.2)) => [sg|];
  apply r_ret => s0 s1 hpre;
  (split; first by []);
  case: hpre => s1a [[s0a [hfix ->]] ->];
  (move: hfix; rewrite /fixed /= => [[-> ->]]);
  case: hat => [[hi hr] [hst hnext]];
  split;
  try exact: put_pre_cond_heap_ignore hi;
  rewrite /rel_app /get_side /=;
  rewrite /rel_app /get_side /= in hr;
  case: hr => hmap hcons hquota;
  split;
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
  try assumption;
  rewrite /get_side /= in hst hnext;
  rewrite hst hnext in hcons *;
  (split; last exact: hcons.2);
  exact: repro_table_consumed_set htable hsel.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming real *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition repro_real_sample P (x : repro_suffix) : raw_code (bytes 16 × bytes 32) :=
  r ← shrincs_fxmss_secret_dist P ;;
  md ← shrincs_fxmss_lookup P (r, x) ;;
  ret (r, md).

Lemma repro_sample_real P Q st q x
    (hp : repro_past st.2.1 st.2.2 q (repro_separator x)) :
  ⊢ ⦃ fun '(h0, h1) => repro_sample_pre Q st q x (h0, h1) ⦄
    repro_real_sample P x ≈
    code_link (repro_sample_call x)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) false)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_at Q st q (h0, h1) ⦄.
Proof.
(* Consume the full separator before either potentially aborting draw. *)
rewrite /repro_real_sample repro_sample_call_unfold.
simplify_linking.
eapply r_get_remember_rhs => used.
eapply (r_fact (repro_separator x \notin used)).
{
  move=> h0 h1 [[ha hf] hu].
  rewrite /rel_app /get_side /= in hf.
  rewrite /rem_inv /get_side /= in hu.
  by rewrite hu in hf.
}
move=> hf.
rewrite hf.
ssprove_code_simpl.
simpl.
eapply r_put_rhs.
rewrite !bind_assoc.
eapply (r_scheme_bind (shrincs_fxmss_secret_dist P)); first exact: prog_valid.
move=> r.
cbv beta.
ssprove_code_simpl.
simpl.
eapply rpre_weaken_rule with
  (pre := fun '(h0, h1) => (repro_at Q st q ⋊
    rem_rhs (ro_used_loc shrincs_fxmss_coord) (repro_separator x :: used)) (h0, h1)).
2: {
  move=> s0 s1 [s1a [hpre ->]].
  case: hpre => [[[[hi hr] [hst hn]] hf0] hu].
  rewrite /rel_app /get_side /= in hr hst hn.
  case: hr => hm hc hq.
  split.
  - split.
    + split.
      * apply: heap_ignore_set_r; last exact: hi.
        by rewrite /repro_private_locs domm_mkfmap !inE /=.
      * rewrite /rel_app /get_side /=.
        split;
        repeat first
          [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
        -- exact: hm.
        -- rewrite hst hn in hc *.
          rewrite /rem_inv /get_side /= in hu.
          rewrite hu in hc.
          split; first exact: hc.1.
          move=> a.
          rewrite in_cons => /orP[/eqP ->|ha].
          ++ exact: hp.
          ++ exact: hc.2 ha.
        -- exact: hq.
    + by split.
  - by rewrite /rem_inv /get_side /= get_set_heap_eq.
}
eapply (r_get_rhs_known (ro_used_loc shrincs_fxmss_coord) (repro_separator x ::
  used)).
{
  by move=> s0 s1 [ha hu].
}
eapply r_get_remember_rhs => qc.
rewrite in_cons eqxx /= addn0.
ssprove_code_simpl.
simpl.
eapply r_put_rhs.
eapply rpre_weaken_rule with (pre := fun '(h0,h1) => repro_at Q st q (h0,h1)).
2: {
  move=> s0 s1 [s1a [[[ha hu] hqc] ->]].
  rewrite /rem_inv /get_side /= in hqc.
  case: ha => [[hi hr] hat].
  split; last exact: hat.
  split.
  - apply: heap_ignore_set_r; last exact: hi.
    by rewrite /repro_private_locs domm_mkfmap !inE /=.
  - rewrite /rel_app /get_side /=.
    rewrite /rel_app /get_side /= in hr.
    case: hr => hm hc hq.
    split;
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    + exact: hm.
    + exact: hc.
    + by rewrite -hqc.
}
eapply r_get_remember_lhs => mp.
eapply (r_get_rhs_known (ro_map_loc (bytes 16) repro_suffix (bytes 32)) mp).
{
  move=> s0 s1 [[[hi [hm hc hq]] hat] hmp].
  rewrite /get_side /= in hm.
  rewrite -hm.
  exact: hmp.
}
case: (getm mp (r,x)) => [md|].
- apply r_ret => s0 s1 [ha hm].
  by split.
- eapply (r_scheme_bind (shrincs_fxmss_digest_dist P)); first exact: prog_valid.
  move=> md.
  cbv beta.
  eapply r_put_lhs.
  eapply r_put_rhs.
  apply r_ret => s0 s1 [s1a [[s0a [hpre ->]] ->]].
  split; first by [].
  case: hpre => [[[hi hr] hat] hm].
  split.
  + split.
    * apply: heap_ignore_set_r.
      -- by rewrite /repro_private_locs domm_mkfmap !inE /=.
      -- apply: heap_ignore_set_l; last exact: hi.
        by rewrite /repro_private_locs domm_mkfmap !inE /=.
    * rewrite /rel_app /get_side /=.
      rewrite /rel_app /get_side /= in hr.
      case: hr => hmap hc hq.
      split;
      repeat first
        [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
      -- by [].
      -- exact: hc.
      -- exact: hq.
  + (* Updating the reprogramming table preserves the state and counter. *)
    case: hat => hst hn.
    rewrite /rel_app /get_side /=.
    rewrite /get_side /= in hst hn.
    split;
    (rewrite get_set_heap_neq; first by []);
    assumption.
Qed.

Lemma repro_lookup_rt_swap P rt x (A : choiceType) (k : bytes 32 -> raw_code A) :
  ⊢ ⦃ fun '(h0,h1) => h0 = h1 ⦄
    (md ← shrincs_fxmss_lookup P x ;; #put shrincs_fxmss_rt_loc := rt ;; k md) ≈
    (#put shrincs_fxmss_rt_loc := rt ;; md ← shrincs_fxmss_lookup P x ;; k md)
  ⦃ eq ⦄.
Proof.
rewrite /shrincs_fxmss_lookup.
simpl.
ssprove_swap_rhs 0.
eapply (rsame_head_cmd (cmd_get shrincs_fxmss_rom_loc)) => mp.
case: (getm mp x) => [md|] /=.
- exact: rreflexivity_rule.
- rewrite !bind_assoc.
  cbn [bind].
  eapply r_transR.
  + eapply (rswap_bind_cmd_eq (shrincs_fxmss_digest_dist P) (cmd_put
    shrincs_fxmss_rt_loc rt)
    (fun md _ => #put shrincs_fxmss_rom_loc := setm mp x md ;; k md)).
    exact: r_swap_scheme_cmd (prog_valid _).
  + eapply (rsame_head (shrincs_fxmss_digest_dist P)) => md.
    simpl.
    ssprove_swap_rhs 0.
    exact: rreflexivity_rule.
Qed.

Local Opaque repro_sample_call shrincs_fxmss_lookup.

Lemma repro_sign_real P Q bit cm :
  ⊢ ⦃ fun '(h0, h1) => repro_inv Q (h0, h1) ⦄
    resolve (G_forge_randomized P Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message,
      'option
      shrincs_fxmss_bytes)) cm ≈
    code_link (repro_sign_body P Q repro_sample_call cm)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) false)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1) ⦄.
Proof.
rewrite /G_forge_randomized /G_forge /resolve /= coerce_kleisliE /repro_sign_body.
ssprove_code_simpl.
simpl.
rewrite /repro_inv.
eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{
  move=> s0 s1 [[hi hr] hst].
  by rewrite -(hi shrincs_fxmss_st_loc (ltac:(fmap_solve))); exact: hst.
}
case: sto => [st|] /=.
2: {
  exact: r_fail.
}
ssprove_sync => done.
ssprove_code_simpl.
simpl.
ssprove_sync => hdone.
eapply r_get_remember_lhs => sc.
eapply (r_get_rhs_known shrincs_fxmss_scnt_loc sc).
{
  move=> s0 s1 [[[hi hr] hst] hsc].
  by rewrite -(hi shrincs_fxmss_scnt_loc (ltac:(fmap_solve))); exact: hsc.
}
ssprove_code_simpl.
simpl.
ssprove_sync => hsc.
ssprove_sync => lg.
eapply r_put_lhs.
eapply r_put_rhs.
eapply r_put_lhs.
eapply r_put_rhs.
eapply rpre_weaken_rule with
(pre := fun '(h0, h1) =>
(repro_inv Q ⋊ rem_lhs shrincs_fxmss_st_loc (Some st)) (h0, h1)).
2: {
  move=> s0 s1 hpre.
  do 2 (case: hpre => ? [[? [hpre ->]] ->]).
  case: hpre => [[[hi hr] hst] hsc0].
  split.
  - split.
    + do 2 apply: put_pre_cond_heap_ignore.
      exact: hi.
    + rewrite /rel_app /get_side /=.
      rewrite /rel_app /get_side /= in hr.
      case: hr => hmap hcons hquota.
      split;
      repeat first
        [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
      * exact: hmap.
      * exact: hcons.
      * rewrite /rem_inv /get_side /= in hsc0.
        rewrite hsc0 in hquota.
        have h := repro_quota_sign Q _ _ _ _ false hquota hsc.
        by rewrite addn0 in h.
  - rewrite /rem_inv /get_side /= in hst *.
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    exact: hst.
}
case hvalid: (shrincs_fxmss_message_valid cm).
2: {
  apply r_ret => s0 s1 [hinv hst].
  by split.
}
eapply r_get_remember_lhs => q.
eapply (r_get_rhs_known shrincs_fxmss_next_loc q).
{
  move=> s0 s1 [[[hi hr] hst] hq].
  by rewrite -(hi shrincs_fxmss_next_loc (ltac:(fmap_solve))); exact: hq.
}
case hsel: (shrincs_fxmss_select_leaf st.2.1 st.2.2 q) => [a|].
2: {
  apply r_ret => s0 s1 [[hinv hst] hq].
  by split.
}
eapply r_put_lhs.
eapply r_put_rhs.
rewrite /repro_inv.
ssprove_sync => kso.
move=> s1 [s1a [[s0a [hpre ->]] ->]].
case: hpre => [[[hi hr] hst] hq].
repeat first
  [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
exact: hi shrincs_fxmss_ks_loc (ltac:(fmap_solve)).
ssprove_sync => hkso.
ssprove_sync => kpo.
{
  move=> s1 [s1a [[s0a [hpre ->]] ->]].
  case: hpre => [[[hi hr] hst] hq].
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  exact: hi shrincs_fxmss_kp_loc (ltac:(fmap_solve)).
}
ssprove_sync => hkpo.
ssprove_sync => kt.
{
  move=> s1 [s1a [[s0a [hpre ->]] ->]].
  case: hpre => [[[hi hr] hst] hq].
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  exact: hi shrincs_fxmss_keys_loc (ltac:(fmap_solve)).
}
eapply r_get_remember_lhs => rt.
eapply (r_get_rhs_known shrincs_fxmss_rt_loc rt).
{
  move=> s0 s1 [[s1a [[s0a [hpre ->]] ->]] hrt].
  case: hpre => [[[hi hr] hst] hq].
  rewrite /rem_inv /get_side /= in hrt.
  rewrite get_set_heap_neq in hrt; first by [].
  rewrite get_set_heap_neq; first by [].
  by rewrite -(hi shrincs_fxmss_rt_loc (ltac:(fmap_solve))).
}
eapply (r_fact (repro_table_consumed st.2.1 st.2.2 q rt)).
{
  move=> s0 s1 [[s1a [[s0a [hpre ->]] ->]] hrt].
  case: hpre => [[[hi [hmap hcons hquota]] hst] hq].
  rewrite /rem_inv /get_side /= in hrt hst hq.
  rewrite get_set_heap_neq in hrt; first by [].
  rewrite /get_side /= hst hq hrt in hcons.
  exact: hcons.1.
}
move=> htable.
eapply rpre_weaken_rule with
(pre := fun '(h0, h1) => repro_sample_pre Q st q.+1
((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message cm)) (h0, h1)).
2: {
  move=> s0 s1 [[s1a [[s0a [hpre ->]] ->]] hrt].
  case: hpre => [[[hi [hmap hcons hquota]] hst] hq].
  rewrite /rem_inv /get_side /= in hst hq.
  rewrite /get_side /= in hmap hcons hquota.
  rewrite hst hq in hcons.
  case: hcons => ht hu.
  split.
  - split.
    + split.
      * apply: put_pre_cond_heap_ignore.
        exact: hi.
      * rewrite /rel_app /get_side /=.
        split;
        repeat first
          [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
        -- exact: hmap.
        -- rewrite hst.
          split.
          ++ move=> k hk.
            exact: repro_past_mono (ht k hk).
          ++ move=> k hk.
            exact: repro_past_mono (hu k hk).
        -- exact: hquota.
    + split.
      * rewrite /get_side /= get_set_heap_neq; first by [].
        exact: hst.
      * by rewrite /get_side /= get_set_heap_eq.
  - rewrite /rel_app /get_side /= get_set_heap_neq; first by [].
    exact: repro_separator_fresh hu hsel.
}
(* The current leaf has no cached randomizer; then commute its table write. *)
have hfresh : getm rt (a, shrincs_fxmss_bound_message cm) = None
  by exact: repro_randomizer_fresh htable hsel.
rewrite hfresh.
eapply r_transL with (c₀ :=
  rm ← repro_real_sample P
    ((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message cm)) ;;
  #put shrincs_fxmss_rt_loc := setm rt (a, shrincs_fxmss_bound_message cm) rm.1 ;;
  match scheme.shrincs_fxmss_sign P rm.2 (fun a => odflt [::] (getm kt a))
      a.2 a.1 st.1.1.1 st.2.1 (uint jasmin_wsize.U8 st.2.2) with
  | Some sg => ret (shrincs_sf_encode a.1 rm.1 a.2 sg)
  | None => ret None
  end).
{
  rewrite /repro_real_sample !bind_assoc.
  eapply (rsame_head (shrincs_fxmss_secret_dist P)) => r.
  cbn [bind].
  rewrite !bind_assoc.
  cbn [bind].
  simpl.
  exact: repro_lookup_rt_swap.
}
eapply r_bind with (mid := fun '(v0,h0) '(v1,h1) => v0 = v1 /\ repro_at Q st q.+1 (h0,h1)).
- (* The real sample uses the leaf just consumed by signing. *)
  have hp : repro_past st.2.1 st.2.2 q.+1 a.
  {
    exists q; by split; first exact: ltnSn.
  }
  exact (repro_sample_real P Q st q.+1
    ((st.1.1.1, st.1.2), (a, shrincs_fxmss_bound_message cm)) hp).
- (* The real signing result preserves the advanced reprogramming invariant. *)
  move=> rm0 rm1.
  eapply rpre_hypothesis_rule => h0 h1 [-> hat].
  ssprove_code_simpl.
  simpl.
  set fixed : precond := fun s => s.1 = h0 /\ s.2 = h1.
  eapply rpre_weaken_rule with (pre := fun '(s0, s1) => fixed (s0, s1)).
  2: by [].
  eapply r_put_lhs.
  eapply r_put_rhs.
  case: (scheme.shrincs_fxmss_sign P rm1.2 (fun a => odflt [::] (getm kt a))
  a.2 a.1 st.1.1.1 st.2.1 (uint jasmin_wsize.U8 st.2.2)) => [sg|];
  apply r_ret => s0 s1 hpre;
  (split; first by []);
  case: hpre => s1a [[s0a [hfix ->]] ->];
  (move: hfix; rewrite /fixed /= => [[-> ->]]);
  case: hat => [[hi hr] [hst hnext]];
  split;
  try exact: put_pre_cond_heap_ignore hi;
  rewrite /rel_app /get_side /=;
  rewrite /rel_app /get_side /= in hr;
  case: hr => hmap hcons hquota;
  split;
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
  try assumption;
  rewrite /get_side /= in hst hnext;
  rewrite hst hnext in hcons *;
  (split; last exact: hcons.2);
  exact: repro_table_consumed_set htable hsel.
Qed.
