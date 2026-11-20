(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.repro.hop

    Hash and terminal-forgery simulations complete the sequential reprogramming
    reduction. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.ro_plus toolkit.reprogram_sep toolkit.relational_rules.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games bound.reprogramming repro.games repro.invariant repro.sign
  instance.
From Stdlib Require Import BinInt.
From mathcomp Require Import reals.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming sim *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Lemma repro_gen_couple P Q setup :
  ⊢ ⦃ fun '(h0, h1) => repro_inv Q (h0, h1) ⦄
    repro_gen_body P setup ≈ repro_gen_body P setup
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1) ⦄.
Proof.
rewrite /repro_gen_body.
ssprove_code_simpl.
simpl.
rewrite /repro_inv.
eapply r_get_remember_lhs => sto.
eapply (r_get_rhs_known shrincs_fxmss_st_loc sto).
{
  move=> s0 s1 [[hi hr] hst].
  by rewrite -(hi shrincs_fxmss_st_loc (ltac:(fmap_solve))); exact: hst.
}
ssprove_sync => hsto.
ssprove_sync => done.
ssprove_sync => hdone.
ssprove_sync => hlegal.
eapply (r_scheme_bind (shrincs_fxmss_public_seed_dist P)); first exact: prog_valid.
move=> pp.
cbv beta.
eapply (r_scheme_bind (shrincs_fxmss_secret_dist P)); first exact: prog_valid.
move=> ks.
cbv beta.
eapply (r_scheme_bind (shrincs_fxmss_secret_dist P)); first exact: prog_valid.
move=> kp.
cbv beta.
eapply (r_scheme_bind (shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1)));
  first exact: shrincs_fxmss_sample_keys_valid.
move=> kt.
cbv beta.
ssprove_sync => hroot.
do 5 (eapply r_put_lhs; eapply r_put_rhs).
apply r_ret => s0 s1 hpre.
split; first by [].
do 5 (case: hpre => ? [[? [hpre ->]] ->]).
case: hpre => [[hi hr] hst].
split.
- do 5 apply: put_pre_cond_heap_ignore.
  exact: hi.
- rewrite /rel_app /get_side /=.
  rewrite /rel_app /get_side /= in hr.
  case: hr => hm hc hq.
  split;
  repeat first
    [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  + exact: hm.
  + (* Generation preserves the consumed-leaf table. *)
    apply: repro_consumed_gen.
    rewrite /rem_inv /get_side /= in hst.
    rewrite hst in hc.
    clear hst.
    by case: sto hsto hc => [st|] //=.
  + exact: hq.
Qed.

Definition repro_query_ready (Q : shrincs_fxmss_resources) (h0 h1 : heap) : Prop :=
  (get_heap h1 ro_qcnt_loc < repro_query_budget Q) /\
  (get_heap h1 ro_qcnt_loc).+1 <=
    get_heap h0 shrincs_fxmss_hcnt_loc + get_heap h0 shrincs_fxmss_scnt_loc +
      get_heap h0 shrincs_fxmss_done_loc.

Definition repro_query_inv (Q : shrincs_fxmss_resources) : precond :=
  repro_inv Q ⋊ (fun '(h0, h1) => repro_query_ready Q h0 h1).

Lemma repro_lookup_couple P Q c x :
  ⊢ ⦃ fun '(h0, h1) => repro_query_inv Q (h0, h1) ⦄
    shrincs_fxmss_lookup P x ≈
    code_link (repro_query x)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) c)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1) ⦄.
Proof.
rewrite /shrincs_fxmss_lookup /repro_query.
simplify_linking.
eapply r_get_remember_lhs => mp.
eapply r_get_remember_rhs => used.
eapply r_get_remember_rhs => qc.
rewrite bind_ret.
eapply (r_fact (qc < repro_query_budget Q)).
{
  move=> s0 s1 [[[[[hi hr] [hb hs]] hm] hu] hqc].
  rewrite /rem_inv /get_side /= in hqc.
  by rewrite hqc in hb.
}
move=> hqc.
rewrite hqc orbT.
ssprove_code_simpl.
simpl.
eapply r_put_rhs.
eapply (r_get_rhs_known (ro_map_loc (bytes 16) repro_suffix (bytes 32)) mp).
{
  move=> s0 s1 [s1a [hpre ->]].
  case: hpre => [[[[[hi [he hc hq]] hr] hm] hu] hqc0].
  rewrite get_set_heap_neq; first by [].
  rewrite /get_side /= in he.
  rewrite -he.
  exact: hm.
}
case he: (getm mp x) => [md|].
- apply r_ret => s0 s1 hpre.
  split; first by [].
  case: hpre => s1a [hpre ->].
  case: hpre => [[[[[hi hr] [hb hs]] hm] hu] hqc0].
  split.
  + apply: heap_ignore_set_r.
    * by rewrite /repro_private_locs domm_mkfmap !inE /=.
    * exact: hi.
  + rewrite /rel_app /get_side /=.
    rewrite /rel_app /get_side /= in hr.
    case: hr => hmap hcons [hh hsc hf hq].
    split;
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    * exact: hmap.
    * exact: hcons.
    * (* A cached query preserves the query-count bound. *)
      split=> //.
      rewrite /rem_inv /get_side /= in hqc0.
      rewrite hqc0 in hs.
      apply: leq_trans _ hs.
      rewrite -(addn1 qc).
      exact: leq_add (leqnn qc) (leq_b1 _).
- eapply (r_scheme_bind (shrincs_fxmss_digest_dist P)); first exact: prog_valid.
  move=> md.
  cbv beta.
  eapply r_put_lhs.
  eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  split; first by [].
  case: hpre => s1b [[s0a [[s1a [hpre ->]] ->]] ->].
  case: hpre => [[[[[hi hr] [hb hs]] hm] hu] hqc0].
  split.
  + apply: heap_ignore_set_r.
    * by rewrite /repro_private_locs domm_mkfmap !inE /=.
    * apply: heap_ignore_set_l.
      -- by rewrite /repro_private_locs domm_mkfmap !inE /=.
      -- apply: heap_ignore_set_r.
         ++ by rewrite /repro_private_locs domm_mkfmap !inE /=.
         ++ exact: hi.
  + rewrite /rel_app /get_side /=.
    rewrite /rel_app /get_side /= in hr.
    case: hr => hmap hcons [hh hsc hf hq].
    split;
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    * by [].
    * exact: hcons.
    * (* A fresh query preserves the query-count bound. *)
      split=> //.
      rewrite /rem_inv /get_side /= in hqc0.
      rewrite hqc0 in hs.
      apply: leq_trans _ hs.
      rewrite -(addn1 qc).
      exact: leq_add (leqnn qc) (leq_b1 _).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming queries *)

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque repro_query shrincs_fxmss_lookup.

Lemma repro_hash_couple P Q c x :
  ⊢ ⦃ fun '(h0, h1) => repro_inv Q (h0, h1) ⦄
    repro_hash_body Q (shrincs_fxmss_lookup P) x ≈
    code_link (repro_hash_body Q repro_query x)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) c)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1) ⦄.
Proof.
rewrite /repro_hash_body.
ssprove_code_simpl.
simpl.
rewrite /repro_inv.
ssprove_sync => done.
ssprove_code_simpl.
simpl.
ssprove_sync => hdone.
eapply r_get_remember_lhs => hc.
eapply (r_get_rhs_known shrincs_fxmss_hcnt_loc hc).
{
  move=> s0 s1 [[hi hr] hhc].
  by rewrite -(hi shrincs_fxmss_hcnt_loc (ltac:(fmap_solve))); exact: hhc.
}
ssprove_code_simpl.
simpl.
ssprove_sync => hhc.
eapply r_put_lhs.
eapply r_put_rhs.
eapply rpre_weaken_rule with
(pre := fun '(h0, h1) => repro_query_inv Q (h0, h1)).
2: {
  move=> s0 s1 [s1a [[s0a [hpre ->]] ->]].
  case: hpre => [[hi [hmap hcons hquota]] hhc0].
  rewrite /rem_inv /get_side /= in hhc0.
  rewrite /get_side /= in hmap hcons hquota.
  rewrite hhc0 in hquota.
  split.
  - split.
    + apply: put_pre_cond_heap_ignore.
      exact: hi.
    + rewrite /rel_app /get_side /=.
      split;
      repeat first
        [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
      * exact: hmap.
      * exact: hcons.
      * have h := repro_quota_hash Q _ _ _ _ false hquota hhc.
        by rewrite addn0 in h.
  - rewrite /repro_query_ready.
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    split.
    + exact: repro_query_capacity_hash hquota hhc.
    + rewrite !addSn ltnS.
      by case: hquota => _ _ _ hq.
}
case: (Z.leb (Z.of_nat (size x.2.2.2)) 2305843009213693841).
- eapply r_bind with
  (mid := fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1)).
  + exact: repro_lookup_couple.
  + move=> md0 md1.
    apply r_ret => h0 h1 [-> hinv].
    by split.
- apply r_ret => h0 h1 [hinv hr].
  by split.
Qed.

Lemma repro_forge_couple P Q c cm sg :
  ⊢ ⦃ fun '(h0, h1) => repro_inv Q (h0, h1) ⦄
    repro_forge_body P (shrincs_fxmss_lookup P) cm sg ≈
    code_link (repro_forge_body P repro_query cm sg)
      (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) c)
  ⦃ fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1) ⦄.
Proof.
rewrite /repro_forge_body.
ssprove_code_simpl.
simpl.
rewrite /repro_inv.
ssprove_sync => sto.
case: sto => [st|] /=.
2: {
  exact: r_fail.
}
eapply r_get_remember_lhs => done.
eapply (r_get_rhs_known shrincs_fxmss_done_loc done).
{
  move=> s0 s1 [[hi hr] hd].
  by rewrite -(hi shrincs_fxmss_done_loc (ltac:(fmap_solve))); exact: hd.
}
ssprove_code_simpl.
simpl.
ssprove_sync => hdone.
have hd : done = false by case: done hdone.
eapply r_put_lhs.
eapply r_put_rhs.
eapply rpre_weaken_rule with
(pre := fun '(h0, h1) => repro_query_inv Q (h0, h1)).
2: {
  move=> s0 s1 [s1a [[s0a [hpre ->]] ->]].
  case: hpre => [[hi [hmap hcons hquota]] hdone0].
  rewrite /rem_inv /get_side /= in hdone0.
  rewrite /get_side /= in hmap hcons hquota.
  rewrite hdone0 hd /= in hquota.
  split.
  - split.
    + apply: put_pre_cond_heap_ignore.
      exact: hi.
    + rewrite /rel_app /get_side /=.
      split;
      repeat first
        [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
      * exact: hmap.
      * exact: hcons.
      * have h := repro_quota_forge Q _ _ _ _ false hquota (erefl : (0 < 1) = true).
        by rewrite addn0 in h.
  - rewrite /repro_query_ready.
    repeat first
      [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    split.
    + exact: repro_query_capacity_forge hquota (erefl : (0 < 1) = true).
    + rewrite addn1 ltnS.
      case: hquota => _ _ _ hq.
      by rewrite addn0 in hq.
}
rewrite /repro_query_inv /repro_inv.
ssprove_sync => lg.
ssprove_sync => kt.
ssprove_sync => sd.
ssprove_sync => rt.
ssprove_code_simpl.
simpl.
case: (shrincs_fxmss_message_valid cm).
2: {
  apply r_ret => h0 h1 [hinv hr].
  by split.
}
case: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|].
2: {
  apply r_ret => h0 h1 [hinv hr].
  by split.
}
eapply r_bind with (mid := fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1)).
- exact: repro_lookup_couple.
- move=> md0 md1.
  apply r_ret => h0 h1 [-> hinv].
  by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming hop *)

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Keep oracle bodies folded while resolving the linked packages. *)
Local Opaque repro_gen_body repro_sign_body repro_hash_body repro_forge_body.

Lemma repro_ideal_eq P Q bit :
  perfect I_forge (G_forge_reprogrammed P Q bit)
    (R_reprogram P Q bit ∘
      RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) true).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (repro_inv Q)).
{ exact (repro_inv_invariant P Q bit true). }
simplify_eq_rel arg.
- rewrite (code_link_scheme shrincs_fxmss_locs _ _ _ (repro_gen_valid P _ arg)).
  exact: repro_gen_couple.
- exact: repro_sign_ideal.
- exact (repro_hash_couple P Q true arg).
- case: arg => cm sg.
  rewrite code_link_bind.
  eapply r_bind with
    (mid := fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1)).
  + exact (repro_forge_couple P Q true cm sg).
  + move=> v0 v1.
    ssprove_code_simpl.
    apply r_ret => h0 h1 [-> hinv].
    by split.
Qed.

(* Keep oracle bodies folded while resolving the linked packages. *)
Local Opaque shrincs_fxmss_forge_body shrincs_fxmss_lookup.

Lemma repro_real_eq P Q bit :
  perfect I_forge (G_forge_randomized P Q bit)
    (R_reprogram P Q bit ∘
      RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
          (repro_query_budget Q) false).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (repro_inv Q)).
{ exact (repro_inv_invariant P Q bit false). }
simplify_eq_rel arg.
- rewrite (code_link_scheme shrincs_fxmss_locs _ _ _ (repro_gen_valid P _ arg)).
  cbv beta delta [repro_gen_body].
  exact (repro_gen_couple P Q arg).
- (* SIGN: the real sampler matches the randomized signing oracle. *)
  cbv beta delta [repro_sign_body shrincs_fxmss_lookup].
  have h := repro_sign_real P Q bit arg.
  cbv beta delta [repro_sign_body shrincs_fxmss_lookup] in h.
  rewrite /G_forge_randomized /G_forge /resolve /= coerce_kleisliE in h.
  exact: h.
- cbv beta delta [repro_hash_body].
  exact (repro_hash_couple P Q false arg).
- case: arg => cm sg.
  rewrite code_link_bind.
  eapply r_bind with
    (mid := fun '(v0, h0) '(v1, h1) => v0 = v1 /\ repro_inv Q (h0, h1)).
  + rewrite -(repro_forge_eq P cm sg).
    exact (repro_forge_couple P Q false cm sg).
  + move=> v0 v1.
    ssprove_code_simpl.
    apply r_ret => h0 h1 [-> hinv].
    by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Reprogramming reduction *)

Import PackageNotation GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section Reduction.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).
Lemma repro_simulator_adv (bit : bool) (A : adversary I_forge) :
  Adv
    (R_reprogram P Q bit ∘ RO_repro_sep (bytes 16) repro_suffix (bytes 32)
      shrincs_fxmss_coord
      repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
        (repro_query_budget Q) false)
    (R_reprogram P Q bit ∘ RO_repro_sep (bytes 16) repro_suffix (bytes 32)
      shrincs_fxmss_coord
      repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
        (repro_query_budget Q) true) A =
  AdvOf (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
    repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
      (repro_query_budget Q))
    (A ∘ R_reprogram P Q bit).
Proof.
rewrite Adv_reduction.
exact: Adv_sym.
Qed.

Lemma repro_hop_adv (bit : bool) (A : adversary I_forge) :
  Adv (G_forge_randomized P Q bit) (G_forge_reprogrammed P Q bit) A =
  AdvOf (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
    repro_separator (shrincs_fxmss_secret_dist P) (shrincs_fxmss_digest_dist P)
      (repro_query_budget Q))
    (A ∘ R_reprogram P Q bit).
Proof.
rewrite (Adv_perfect_l (repro_real_eq P Q bit)).
rewrite (Adv_perfect_r (repro_ideal_eq P Q bit)).
exact: repro_simulator_adv.
Qed.

End Reduction.

Lemma repro_simulator_sha256_bound (Q : shrincs_fxmss_resources) (bit : bool)
    (A : adversary I_forge) :
  Adv
    (R_reprogram shrincs_fxmss_sha256 Q bit ∘
      RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (dBytes 16) (dBytes 32) (repro_query_budget Q) false)
    (R_reprogram shrincs_fxmss_sha256 Q bit ∘
      RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
        repro_separator (dBytes 16) (dBytes 32) (repro_query_budget Q) true) A
  <= (shrincs_fxmss_hash_budget Q + shrincs_fxmss_sign_budget Q + 1)%:R / ((2 ^
    128)%nat)%:R.
Proof.
rewrite (repro_simulator_adv shrincs_fxmss_sha256 Q bit A).
apply: repro_sep_sha256_bound.
Qed.

Lemma repro_hop_sha256_bound (Q : shrincs_fxmss_resources) (bit : bool)
    (A : adversary I_forge) :
  Adv (G_forge_randomized shrincs_fxmss_sha256 Q bit) (G_forge_reprogrammed
    shrincs_fxmss_sha256 Q bit) A
  <= (shrincs_fxmss_hash_budget Q + shrincs_fxmss_sign_budget Q + 1)%:R / ((2 ^
    128)%nat)%:R.
Proof.
rewrite (repro_hop_adv shrincs_fxmss_sha256 Q bit A).
apply: repro_sep_sha256_bound.
Qed.
