(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bound.digest

    Generation, signing, hash and terminal-forgery charges yield the digest-
    collision bound. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import reprogram probability.
From Shrincs.internal.ssprove.lib.math Require Import fmap_size.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games digest.games digest.sampling digest.invariant prf.schedule instance.
From mathcomp Require Import reals distr realsum.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** Digest gen bound *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque shrincs_fxmss_leaf_capacity scheme.shrincs_fxmss_node
  shrincs_fxmss_lookup_keys.

Lemma digest_gen_bound Q setup {T : choiceType}
    (k0 k1 : bytes 48 -> raw_code T)
    (ih : forall v h, digest_safe Q h -> forall z,
      `|dfst (Pr_code (k0 v) h) z - dfst (Pr_code (k1 v) h) z|
        <= digest_heap_error Q h)
    h (hsafe : digest_safe Q h) z :
  `|dfst (Pr_code (v ← digest_gen_body shrincs_fxmss_sha256 Q setup ;; k0 v) h) z -
    dfst (Pr_code (v ← digest_gen_body shrincs_fxmss_sha256 Q setup ;; k1 v) h) z|
  <= digest_heap_error Q h.
Proof.
rewrite /digest_gen_body /digest.filtered.G_forge_digest_filtered
  /digest.filtered.G_forge_filtered.
rewrite !digest_gen_step.
case hg: (~~ isSome (get_heap h shrincs_fxmss_st_loc) &&
  ~~ get_heap h shrincs_fxmss_done_loc &&
  shape.shrincs_fxmss_structure_legal setup.1.1 setup.1.2); last first.
{ rewrite subrr normr0. exact: digest_error_ge0. }
case/andP: hg => /andP[hs hd] hl.
have hst : get_heap h shrincs_fxmss_st_loc = None.
{ by case: (get_heap h shrincs_fxmss_st_loc) hs. }
have hdone : get_heap h shrincs_fxmss_done_loc = false.
{ by case: (get_heap h shrincs_fxmss_done_loc) hd. }
have [hi hz hc hp] := hsafe.
have [hsd hsz] := hp hst.
rewrite !dfst_dlet_commut.
apply: dlet_diff_le; first exact: digest_error_ge0.
move=> pp.
rewrite !dfst_dlet_commut.
apply: dlet_diff_le; first exact: digest_error_ge0.
move=> ks.
rewrite !dfst_dlet_commut.
apply: dlet_diff_le; first exact: digest_error_ge0.
move=> kp.
rewrite !dfst_dlet_commut.
apply: dlet_diff_le; first exact: digest_error_ge0.
move=> kt.
case hr: (scheme.shrincs_fxmss_node shrincs_fxmss_sha256
  (shrincs_fxmss_lookup_keys shrincs_fxmss_sha256 true ((pp,setup.2,zeros 16),setup.1)
    ks kt)
  (uint jasmin_wsize.U64 0) (uint jasmin_wsize.U8 255) pp
  setup.1.1 (uint jasmin_wsize.U8 setup.1.2)) => [root|] /=;
  last by rewrite subrr normr0; exact: digest_error_ge0.
rewrite !dfst_dlet_commut.
apply: le_trans (digest_preassignment_split_le (shrincs_fxmss_schedule setup.1)
  (codomm (get_heap h shrincs_fxmss_rom_loc))
  (digest_error Q true (get_heap h shrincs_fxmss_hcnt_loc) false) z _ _
  (shrincs_fxmss_prf_schedule_uniq _) (digest_error_ge0 _ _ _ _) _) _.
- move=> sd ha hsize.
  set h1 := digest_gen_heap h setup pp ks kp kt sd root.
  have he : digest_heap_error Q h1 =
      digest_error Q true (get_heap h shrincs_fxmss_hcnt_loc) false.
  { rewrite /digest_heap_error /h1 /digest_gen_heap.
    repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    by rewrite hdone. }
  rewrite -he.
  apply: ih.
  apply: (@digest_safe_generated Q h h1 ((pp,setup.2,root),setup.1) sd hc).
  + apply: leq_trans (size_codomm_le sd) _.
    exact: leq_trans hsize (digest_schedule_bound Q setup.1 hl).
  + exact ha.
  + rewrite /h1 /digest_gen_heap.
    repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    by [].
  + by rewrite /h1 /digest_gen_heap !get_set_heap_neq.
  + by rewrite /h1 /digest_gen_heap get_set_heap_eq.
  + by rewrite /h1 /digest_gen_heap !get_set_heap_neq.
- (* Generation pays for every scheduled leaf and prior hash output. *)
  rewrite /digest_heap_error hst hdone /=.
  rewrite -(digest_gen_charge Q _ hc).
  apply: lerD; last exact: lexx.
  apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
  rewrite -!natrM ler_nat.
  apply: leq_mul; first exact: digest_schedule_bound hl.
  exact: leq_trans (size_codomm_le _) hsz.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest hash bound *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque shrincs_fxmss_leaf_capacity shrincs_fxmss_lookup.

Lemma digest_hash_bound Q x {T : choiceType}
    (k0 k1 : option (bytes 32) -> raw_code T)
    (ih : forall v h, digest_safe Q h -> forall z,
      `|dfst (Pr_code (k0 v) h) z - dfst (Pr_code (k1 v) h) z|
        <= digest_heap_error Q h)
    h (hsafe : digest_safe Q h) z :
  `|dfst (Pr_code (v ← digest_hash_body shrincs_fxmss_sha256 Q x ;; k0 v) h) z -
    dfst (Pr_code (v ← digest_hash_body shrincs_fxmss_sha256 Q x ;; k1 v) h) z|
  <= digest_heap_error Q h.
Proof.
rewrite !digest_hash_step.
case hg: (~~ get_heap h shrincs_fxmss_done_loc &&
    (get_heap h shrincs_fxmss_hcnt_loc < shrincs_fxmss_hash_budget Q)%nat); last first.
{ rewrite subrr normr0. exact: digest_error_ge0. }
case/andP: hg => hd hlt.
set h1 := set_heap h shrincs_fxmss_hcnt_loc (get_heap h shrincs_fxmss_hcnt_loc).+1.
have [hi hz hc hp] := hsafe.
have hsafe1 : digest_safe Q h1.
{ split.
  - by rewrite /digest_avoid /h1 !get_set_heap_neq.
  - by rewrite /h1 get_set_heap_neq.
  - by rewrite /h1 get_set_heap_eq.
  - (* Before generation, the hash table stays within the incremented budget. *)
    rewrite /h1 get_set_heap_neq // => hn.
    have [he hb] := hp hn.
    split; first by rewrite get_set_heap_neq.
    rewrite get_set_heap_neq // get_set_heap_eq.
    exact: leq_trans hb (leqnSn _). }
have he1 : digest_heap_error Q h1 <= digest_heap_error Q h.
{ rewrite /digest_heap_error /h1 get_set_heap_eq !get_set_heap_neq //.
  case: (isSome (get_heap h shrincs_fxmss_st_loc)); last exact: lexx.
  have hb := digest_query_charge Q (get_heap h shrincs_fxmss_hcnt_loc)
    (get_heap h shrincs_fxmss_done_loc) 0 hlt (leq0n _).
  by rewrite mul0r add0r in hb. }
case: (Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111)); last first.
{ exact: le_trans (ih None h1 hsafe1 z) he1. }
cbn zeta.
rewrite !digest_lookup_step.
rewrite /h1 !get_set_heap_neq //.
case hx: (getm (get_heap h shrincs_fxmss_rom_loc) x) => [md|];
  first exact: le_trans (ih (Some md) h1 hsafe1 z) he1.
rewrite !dfst_dlet_commut.
set hf := fun md => set_heap h1 shrincs_fxmss_rom_loc (setm (get_heap h
  shrincs_fxmss_rom_loc) x md).
have hf_safe : forall md, md \notin codomm (get_heap h shrincs_fxmss_sd_loc) ->
    digest_safe Q (hf md).
{ move=> md hm.
  apply: (@digest_safe_read Q h (hf md) x md hsafe hlt (or_introl hm));
  rewrite /hf /h1;
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
  reflexivity. }
have hf_error : forall md, digest_heap_error Q (hf md) = digest_heap_error Q h1.
{ move=> md. rewrite /digest_heap_error /hf /h1.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  reflexivity. }
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|].
- apply: le_trans (digest_sample_split_le (codomm (get_heap h shrincs_fxmss_sd_loc))
    (digest_heap_error Q h1) z _ _ (digest_error_ge0 _ _ _ _) _) _.
  + move=> md hm.
    rewrite -(hf_error md).
    exact: ih (Some md) (hf md) (hf_safe md hm) z.
  + rewrite /digest_heap_error /h1 get_set_heap_eq !get_set_heap_neq // hs /=.
    exact: digest_query_charge hlt hz.
- (* Before generation, no digest has been assigned to a leaf. *)
  apply: dlet_diff_le; first exact: digest_error_ge0.
  move=> md.
  have hm : md \notin codomm (get_heap h shrincs_fxmss_sd_loc).
  { have [he _] := hp hs. by rewrite he codomm0 in_fset0. }
  apply: le_trans (ih (Some md) (hf md) (hf_safe md hm) z) _.
  by rewrite hf_error.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest sign bound *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque shrincs_fxmss_leaf_capacity digest_sign_result.

Lemma digest_sign_bound Q cm {T : choiceType}
    (k0 k1 : option shrincs_fxmss_bytes -> raw_code T)
    (ih : forall v h, digest_safe Q h -> forall z,
      `|dfst (Pr_code (k0 v) h) z - dfst (Pr_code (k1 v) h) z|
        <= digest_heap_error Q h)
    h (hsafe : digest_safe Q h) z :
  `|dfst (Pr_code (v ← digest_sign_body shrincs_fxmss_sha256 Q cm ;; k0 v) h) z -
    dfst (Pr_code (v ← digest_sign_body shrincs_fxmss_sha256 Q cm ;; k1 v) h) z|
  <= digest_heap_error Q h.
Proof.
rewrite !digest_sign_step.
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|];
  last by rewrite subrr normr0; exact: digest_error_ge0.
case: (get_heap h shrincs_fxmss_done_loc);
  first by rewrite subrr normr0; exact: digest_error_ge0.
case: (get_heap h shrincs_fxmss_scnt_loc < shrincs_fxmss_sign_budget Q)%nat;
  last by rewrite subrr normr0; exact: digest_error_ge0.
set h1 := set_heap (set_heap h shrincs_fxmss_scnt_loc (get_heap h
  shrincs_fxmss_scnt_loc).+1)
  shrincs_fxmss_log_loc (cm :: get_heap h shrincs_fxmss_log_loc).
have hsafe1 : digest_safe Q h1.
{ apply: (digest_safe_frame Q h) => //;
    by rewrite /h1 !get_set_heap_neq. }
have he1 : digest_heap_error Q h1 = digest_heap_error Q h.
{ by rewrite /digest_heap_error /h1 !get_set_heap_neq. }
have hnone : `|dfst (Pr_code (k0 None) h1) z - dfst (Pr_code (k1 None) h1) z|
    <= digest_heap_error Q h.
{ rewrite -he1. exact: ih None h1 hsafe1 z. }
case: (shrincs_fxmss_message_valid cm); last exact hnone.
case: (shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h
  shrincs_fxmss_next_loc))
  => [a|]; last exact hnone.
set h2 := set_heap h1 shrincs_fxmss_next_loc (get_heap h shrincs_fxmss_next_loc).+1.
case: (get_heap h shrincs_fxmss_ks_loc) => [ks|];
  last by rewrite subrr normr0; exact: digest_error_ge0.
case: (get_heap h shrincs_fxmss_kp_loc) => [kp|];
  last by rewrite subrr normr0; exact: digest_error_ge0.
set bm := shrincs_fxmss_bound_message cm.
have hsafe2 : digest_safe Q h2.
{ apply: (digest_safe_frame Q h) => //;
    by rewrite /h2 /h1 !get_set_heap_neq. }
have hf : forall r md,
  (getm (get_heap h shrincs_fxmss_rt_loc) (a,bm) = None \/
   getm (get_heap h shrincs_fxmss_rt_loc) (a,bm) = Some r) ->
  `|dfst (Pr_code (k0 (digest_sign_result shrincs_fxmss_sha256 st ks
      (get_heap h shrincs_fxmss_keys_loc) a r md)) (digest_sign_heap h2 st a bm r md)) z
        -
    dfst (Pr_code (k1 (digest_sign_result shrincs_fxmss_sha256 st ks
      (get_heap h shrincs_fxmss_keys_loc) a r md)) (digest_sign_heap h2 st a bm r md))
        z|
  <= digest_heap_error Q h.
{ move=> r md ht.
  have he : digest_heap_error Q (digest_sign_heap h2 st a bm r md) =
      digest_heap_error Q h.
  { by rewrite /digest_heap_error /digest_sign_heap /h2 /h1 !get_set_heap_neq. }
  rewrite -he.
  apply: ih.
  apply: (@digest_safe_sign Q h2 (digest_sign_heap h2 st a bm r md) st
    (r,((st.1.1.1,st.1.2),(a,bm))) md hsafe2).
  - by rewrite /h2 /h1 !get_set_heap_neq.
  - by rewrite /h2 /h1 !get_set_heap_neq.
  - by rewrite /digest_sign_heap !get_set_heap_neq.
  - by rewrite /digest_sign_heap get_set_heap_eq get_set_heap_neq.
  - by rewrite /digest_sign_heap get_set_heap_neq // get_set_heap_eq.
  - by rewrite /digest_sign_heap !get_set_heap_neq.
  - by rewrite /digest_sign_heap !get_set_heap_neq.
}
rewrite !dfst_dlet_commut.
case ht: (getm (get_heap h shrincs_fxmss_rt_loc) (a,bm)) => [r|].
- rewrite !dlet_unit_ext !dfst_dlet_commut.
  case: (getm (get_heap h shrincs_fxmss_sd_loc) a) => [md|].
  + rewrite !dlet_unit_ext. exact: hf _ _ (or_intror ht).
  + apply: dlet_diff_le; first exact: digest_error_ge0.
    move=> md. exact: hf _ _ (or_intror ht).
- apply: dlet_diff_le; first exact: digest_error_ge0.
  move=> r.
  rewrite !dfst_dlet_commut.
  case: (getm (get_heap h shrincs_fxmss_sd_loc) a) => [md|].
  + rewrite !dlet_unit_ext. exact: hf _ _ (or_introl ht).
  + apply: dlet_diff_le; first exact: digest_error_ge0.
    move=> md. exact: hf _ _ (or_introl ht).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest forge bound *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque shrincs_fxmss_leaf_capacity shrincs_fxmss_lookup
  scheme.shrincs_fxmss_verify.

Lemma digest_forge_bound Q cm sg {T : choiceType}
    (k0 k1 : bool -> raw_code T)
    (ih : forall v h, digest_safe Q h -> forall z,
      `|dfst (Pr_code (k0 v) h) z - dfst (Pr_code (k1 v) h) z|
        <= digest_heap_error Q h)
    h (hsafe : digest_safe Q h) z :
  `|dfst (Pr_code (v ← shrincs_fxmss_forge_body shrincs_fxmss_sha256 false
      (fun _ _ _ _ _ => true) cm sg ;; k0 v) h) z -
    dfst (Pr_code (v ← shrincs_fxmss_forge_body shrincs_fxmss_sha256 true
      (fun _ _ _ _ _ => true) cm sg ;; k1 v) h) z|
  <= digest_heap_error Q h.
Proof.
rewrite !digest_forge_step.
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|];
  last by rewrite subrr normr0; exact: digest_error_ge0.
case hd: (get_heap h shrincs_fxmss_done_loc);
  first by rewrite subrr normr0; exact: digest_error_ge0.
set h1 := set_heap h shrincs_fxmss_done_loc true.
have [hi hz hc hp] := hsafe.
have hsafe1 : digest_safe Q h1.
{ apply: (digest_safe_frame Q h) => //; by rewrite /h1 get_set_heap_neq. }
have he1 : digest_heap_error Q h1 <= digest_heap_error Q h.
{ rewrite /digest_heap_error /h1 get_set_heap_eq !get_set_heap_neq // hs hd /=.
  have hb := digest_forge_charge Q (get_heap h shrincs_fxmss_hcnt_loc) 0 (leq0n _).
  by rewrite mul0r add0r in hb. }
have hfalse : `|dfst (Pr_code (k0 false) h1) z - dfst (Pr_code (k1 false) h1) z|
    <= digest_heap_error Q h.
{ exact: le_trans (ih false h1 hsafe1 z) he1. }
case: (shrincs_fxmss_message_valid cm); last exact hfalse.
case: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|]; last exact hfalse.
cbn zeta.
set x := (r, ((st.1.1.1,st.1.2), ((a,i),shrincs_fxmss_bound_message cm))).
have hcoll md :
  (md \notin codomm (get_heap h shrincs_fxmss_sd_loc) \/ getm (get_heap h
    shrincs_fxmss_rom_loc) x = Some md) ->
  ~~ ((md \in codomm (get_heap h shrincs_fxmss_sd_loc)) &&
    (getm (get_heap h shrincs_fxmss_rt_loc) x.2.2 != Some r)).
{ case=> hm.
  - by rewrite (negbTE hm).
  - exact: digest_filter_safe hi hm. }
rewrite !digest_lookup_step.
rewrite /h1 !get_set_heap_neq //.
case hx: (getm (get_heap h shrincs_fxmss_rom_loc) x) => [md|].
- rewrite (hcoll md (or_intror hx)).
  exact: le_trans (ih _ h1 hsafe1 z) he1.
- rewrite !dfst_dlet_commut.
  set hf := fun md => set_heap h1 shrincs_fxmss_rom_loc (setm (get_heap h
    shrincs_fxmss_rom_loc) x md).
  have hf_safe : forall md, md \notin codomm (get_heap h shrincs_fxmss_sd_loc) ->
    digest_safe Q (hf md).
  { move=> md hm.
    apply: (@digest_safe_lookup Q h (hf md) st x md hsafe hs (or_introl hm));
    rewrite /hf /h1;
    repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []];
    reflexivity. }
  have hf_error : forall md, digest_heap_error Q (hf md) = digest_heap_error Q h1.
  { move=> md. rewrite /digest_heap_error /hf /h1.
    repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    reflexivity. }
  apply: le_trans (digest_sample_split_le (codomm (get_heap h shrincs_fxmss_sd_loc))
    (digest_heap_error Q h1) z _ _ (digest_error_ge0 _ _ _ _) _) _.
  + move=> md hm.
    rewrite (hcoll md (or_introl hm)) -(hf_error md).
    exact: ih _ (hf md) (hf_safe md hm) z.
  + rewrite /digest_heap_error /h1 get_set_heap_eq !get_set_heap_neq // hs hd /=.
    exact: digest_forge_charge hz.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest bound *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Lemma resolve_digest_gen P Q filter bit setup :
  resolve (G_digest P Q filter bit) (shrincs_fxmss_op_gen,(shrincs_fxmss_setup,bytes
    48)) setup =
    digest_gen_body P Q setup.
Proof. by rewrite /G_digest /resolve /= coerce_kleisliE. Qed.

Lemma resolve_digest_sign P Q filter bit cm :
  resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_sign,(shrincs_fxmss_message,'option shrincs_fxmss_bytes)) cm =
    digest_sign_body P Q cm.
Proof. by rewrite /G_digest /resolve /= coerce_kleisliE. Qed.

Lemma resolve_digest_hash P Q filter bit x :
  resolve (G_digest P Q filter bit)
    (shrincs_fxmss_op_hash,(shrincs_fxmss_hmsg_input,'option (bytes 32))) x =
      digest_hash_body P Q x.
Proof. by rewrite /G_digest /resolve /= coerce_kleisliE. Qed.

Lemma resolve_digest_forge P Q filter bit cm sg :
  resolve (G_digest P Q filter bit) (shrincs_fxmss_op_forge,(shrincs_fxmss_message ×
    shrincs_fxmss_bytes,'bool)) (cm,sg) =
    (v ← shrincs_fxmss_forge_body P filter (fun _ _ _ _ _ => true) cm sg ;; ret (bit &&
      v)).
Proof. by rewrite /G_digest /resolve /= coerce_kleisliE. Qed.

Local Opaque G_digest shrincs_fxmss_leaf_capacity Pr_code code_link resolve.

Lemma digest_collision_core Q (LA : Locations) (hsep : fseparate LA shrincs_fxmss_locs)
    bit {T : choiceType} {c : raw_code T} (vc : ValidCode LA I_forge c) :
  forall h, digest_safe Q h -> forall z,
  `|dfst (Pr_code (code_link c (G_digest_preassigned shrincs_fxmss_sha256 Q bit)) h) z -
    dfst (Pr_code (code_link c (G_digest_filtered shrincs_fxmss_sha256 Q bit)) h) z|
  <= digest_heap_error Q h.
Proof.
induction vc as [a | o x k ho hk ih | lo k hl hk ih |
  lo v k hl hk ih | op k hk ih].
- move=> h hs z. cbn [code_link].
  rewrite subrr normr0. exact: digest_error_ge0.
- move=> h hs z. cbn [code_link].
  fmap_invert ho.
  + rewrite /G_digest_preassigned /G_digest_filtered !resolve_digest_gen.
    apply: (@digest_gen_bound Q _ T _ _ _ h hs z).
    by move=> v h' hs' z'; apply: ih.
  + rewrite /G_digest_preassigned /G_digest_filtered !resolve_digest_sign.
    apply: (@digest_sign_bound Q _ T _ _ _ h hs z).
    by move=> v h' hs' z'; apply: ih.
  + rewrite /G_digest_preassigned /G_digest_filtered !resolve_digest_hash.
    apply: (@digest_hash_bound Q _ T _ _ _ h hs z).
    by move=> v h' hs' z'; apply: ih.
  + case: x => cm sg.
    rewrite /G_digest_preassigned /G_digest_filtered !resolve_digest_forge !bind_assoc.
    apply: (@digest_forge_bound Q _ _ T _ _ _ h hs z).
    by move=> v h' hs' z'; apply: ih.
- move=> h hs z. cbn [code_link].
  rewrite !Pr_code_get. exact: ih _ h hs z.
- (* Adversary writes preserve the private state and its error bound. *)
  move=> h hs z. cbn [code_link].
  rewrite !Pr_code_put.
  have hout := notin_has_separate _ _ _ hl hsep.
  have hn (l : Location) (hm : fhas shrincs_fxmss_locs l) : l.1 != lo.1.
  { apply/eqP => he.
    have hin := fhas_in _ _ hm.
    by rewrite -he hin in hout. }
  have hst := hn shrincs_fxmss_st_loc (ltac:(fmap_solve)).
  have hmp := hn shrincs_fxmss_rom_loc (ltac:(fmap_solve)).
  have hrt := hn shrincs_fxmss_rt_loc (ltac:(fmap_solve)).
  have hsd := hn shrincs_fxmss_sd_loc (ltac:(fmap_solve)).
  have hhc := hn shrincs_fxmss_hcnt_loc (ltac:(fmap_solve)).
  have hdone := hn shrincs_fxmss_done_loc (ltac:(fmap_solve)).
  have hs' : digest_safe Q (set_heap h lo v).
  { apply: (digest_safe_frame Q h) => //; by rewrite get_set_heap_neq. }
  have he : digest_heap_error Q (set_heap h lo v) = digest_heap_error Q h.
  { by rewrite /digest_heap_error !get_set_heap_neq. }
  rewrite -he. exact: ih _ hs' z.
- move=> h hs z. cbn [code_link].
  rewrite !dPr_sample.
  apply: dlet_diff_le; first exact: digest_error_ge0.
  move=> a. exact: ih a h hs z.
Qed.

Lemma digest_filter_sha256_bound Q bit (A : adversary I_forge) :
  Adv (G_digest_preassigned shrincs_fxmss_sha256 Q bit) (G_digest_filtered
    shrincs_fxmss_sha256 Q bit) A <=
    (shrincs_fxmss_leaf_capacity Q)%:R * ((shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^
      256)%nat)%:R).
Proof.
apply: (Adv_nom_ind _ _ _ I_forge
  (fun x : Axioms.R => x <= (shrincs_fxmss_leaf_capacity Q)%:R *
    ((shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^ 256)%nat)%:R))) => //.
move=> A' LA' VA' _ sep1 sep2.
rewrite /AdvantageE.
have hrun : fhas A_export RUN by fmap_solve.
have vc := valid_resolve _ _ _ _ RUN tt VA' hrun.
have hsep : fseparate LA' shrincs_fxmss_locs by exact: sep1.
rewrite !Pr_Pr_code !resolve_link.
have hb := digest_collision_core Q LA' hsep bit vc empty_heap
  (digest_safe_empty Q) true.
by rewrite /digest_heap_error /digest_error /digest_remaining /= -mulrA in hb.
Qed.

Corollary digest_filter_sha256_bound_192 Q bit (A : adversary I_forge) :
  Adv (G_digest_preassigned shrincs_fxmss_sha256 Q bit) (G_digest_filtered
    shrincs_fxmss_sha256 Q bit) A <=
    (shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^ 192)%nat)%:R.
Proof.
have hb := digest_filter_sha256_bound Q bit A.
by rewrite digest_budget_normalize in hb.
Qed.
