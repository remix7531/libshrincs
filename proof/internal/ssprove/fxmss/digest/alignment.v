(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.digest.alignment

    The heap invariant couples eager and lazy digest sampling across generation,
    signing and read operations. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games repro.invariant prf.schedule digest.sampling repro.games digest.games
  bound.digest instance.
From Shrincs.internal.ssprove.lib.toolkit Require Import
  reprogram fill_avoid fill_exchange heap_observe probability.
From mathcomp Require Import reals distr realsum.
From Shrincs.internal.ssprove.wots Require Import instance.

(* ------------------------------------------------------------------ *)
(** ** Digest align inv *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope nat_scope.

Record digest_align_inv (h : heap) (sd : shrincs_fxmss_digest_table) (js : seq
  shrincs_fxmss_coord) : Prop := {
  dai_uniq : uniq js;
  dai_disjoint : forall a, a \in js -> a \notin domm sd;
  dai_setup : forall st, get_heap h shrincs_fxmss_st_loc = Some st ->
    (forall a, a \in domm sd ->
      repro_past st.2.1 st.2.2 (get_heap h shrincs_fxmss_next_loc) a) /\
    (forall a, a \in shrincs_fxmss_schedule st.2 ->
      ~ repro_past st.2.1 st.2.2 (get_heap h shrincs_fxmss_next_loc) a -> a \in js) /\
    repro_table_consumed st.2.1 st.2.2 (get_heap h shrincs_fxmss_next_loc)
      (get_heap h shrincs_fxmss_rt_loc);
  dai_before : get_heap h shrincs_fxmss_st_loc = None ->
    sd = emptym /\ js = [::] /\ get_heap h shrincs_fxmss_next_loc = 0 /\
      get_heap h shrincs_fxmss_rt_loc = emptym
}.

Lemma digest_align_empty : digest_align_inv empty_heap emptym [::].
Proof.
constructor.
- by [].
- by move=> a; rewrite in_nil.
- by move=> st.
- by [].
Qed.

Lemma digest_align_frame h h' sd js :
  get_heap h' shrincs_fxmss_st_loc = get_heap h shrincs_fxmss_st_loc ->
  get_heap h' shrincs_fxmss_next_loc = get_heap h shrincs_fxmss_next_loc ->
  get_heap h' shrincs_fxmss_rt_loc = get_heap h shrincs_fxmss_rt_loc ->
  digest_align_inv h sd js -> digest_align_inv h' sd js.
Proof.
move=> hs hn hr [hu hd hst hb].
constructor => //.
- by rewrite hs hn hr.
- by rewrite hs hn hr.
Qed.

Lemma digest_align_slot h sd js st a :
  digest_align_inv h sd js -> get_heap h shrincs_fxmss_st_loc = Some st ->
  shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h shrincs_fxmss_next_loc) =
    Some a ->
  a \in js /\ a \notin domm sd /\
    forall bm, getm (get_heap h shrincs_fxmss_rt_loc) (a,bm) = None.
Proof.
move=> hi hs ha.
have [hp [hc ht]] := dai_setup _ _ _ hi st hs.
have hf := repro_select_fresh _ _ _ _ ha.
have hj : a \in js.
{ apply: hc; last exact: hf. exact: shrincs_fxmss_prf_schedule_mem ha. }
split; first exact: hj.
split; first exact: dai_disjoint _ _ _ hi a hj.
move=> bm. exact: repro_randomizer_fresh ht ha.
Qed.

Lemma digest_align_generated h sd js setup pp ks kp kt root :
  digest_align_inv h sd js -> get_heap h shrincs_fxmss_st_loc = None ->
  digest_align_inv (digest_gen_heap h setup pp ks kp kt emptym root)
    emptym (shrincs_fxmss_schedule setup.1).
Proof.
move=> hi hs.
have [_ [_ [hn hr]]] := dai_before _ _ _ hi hs.
constructor.
- exact: shrincs_fxmss_prf_schedule_uniq.
- by move=> a _; rewrite domm0 in_fset0.
- (* Fresh generation has no assigned or consumed leaf digests. *)
  move=> st. rewrite /digest_gen_heap.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  move=> [<-] /=. rewrite hn hr.
  split; first by move=> a; rewrite domm0.
  split; first by move=> a ha _.
  exact: repro_table_consumed_empty.
- rewrite /digest_gen_heap.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  by [].
Qed.

Lemma digest_align_consumed h h' sd js st a bm r md :
  digest_align_inv h sd js -> get_heap h shrincs_fxmss_st_loc = Some st ->
  shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h shrincs_fxmss_next_loc) =
    Some a ->
  get_heap h' shrincs_fxmss_st_loc = Some st ->
  get_heap h' shrincs_fxmss_next_loc = (get_heap h shrincs_fxmss_next_loc).+1 ->
  get_heap h' shrincs_fxmss_rt_loc = setm (get_heap h shrincs_fxmss_rt_loc) (a,bm) r ->
  digest_align_inv h' (setm sd a md) (rem a js).
Proof.
move=> hi hs ha hs' hn hr.
have [hp [hc ht]] := dai_setup _ _ _ hi st hs.
have hu := dai_uniq _ _ _ hi.
constructor.
- exact: rem_uniq.
- move=> a'. rewrite (mem_rem_uniq _ hu) inE => /andP[hne hj].
  rewrite domm_set in_fset1U negb_or hne /=.
  exact: dai_disjoint _ _ _ hi a' hj.
- move=> st'. rewrite hs' => -[<-]. rewrite hn hr.
  split.
  + move=> a'. rewrite domm_set in_fset1U => /orP[/eqP ->|hd].
    * exists (get_heap h shrincs_fxmss_next_loc); split=> //; exact: ltnSn.
    * exact: repro_past_mono (hp _ hd).
  + split; last exact: repro_table_consumed_set ht ha.
    move=> a' hsch hf.
    rewrite (mem_rem_uniq _ hu) inE.
    apply/andP; split.
    * apply/eqP=> he. subst a'. apply: hf.
      exists (get_heap h shrincs_fxmss_next_loc); split=> //; exact: ltnSn.
    * apply: hc hsch _. move=> hpast. apply: hf. exact: repro_past_mono hpast.
- by rewrite hs'.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest align rel *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Definition digest_align_rel P {T : choiceType} (c0 c1 : raw_code T) : Prop :=
  forall h sd js z, digest_align_inv h sd js ->
    dfst (Pr_code c0 h) z =
    (\dlet_(rest <- Pr_fst (fill_code (shrincs_fxmss_digest_dist P) js emptym))
      dfst (Pr_code c1 (set_heap h shrincs_fxmss_sd_loc (unionm sd rest)))) z.

Lemma digest_align_ret P (hl : LosslessCode (shrincs_fxmss_digest_dist P)) {T :
  choiceType} (v : T) :
  digest_align_rel P (ret v) (ret v).
Proof.
move=> h sd js z hi. rewrite dPr_ret.
symmetry. transitivity ((\dlet_(_ <- Pr_fst (fill_code (shrincs_fxmss_digest_dist P) js
  emptym)) dunit v) z).
- by apply: eq_dlet_at => rest; rewrite dPr_ret.
- by rewrite (fill_const _ hl).
Qed.

Lemma digest_align_sample P {T : choiceType} (op : Op) (k0 k1 : op.π1 -> raw_code T) :
  (forall v, digest_align_rel P (k0 v) (k1 v)) ->
  digest_align_rel P (sampler op k0) (sampler op k1).
Proof.
move=> ih h sd js z hi. rewrite dPr_sample.
transitivity ((\dlet_(v <- op.π2)
  \dlet_(rest <- Pr_fst (fill_code (shrincs_fxmss_digest_dist P) js emptym))
    dfst (Pr_code (k1 v) (set_heap h shrincs_fxmss_sd_loc (unionm sd rest)))) z).
- apply: eq_dlet_at => v. exact: ih.
- rewrite dlet_commut. by apply: eq_dlet_at => rest; rewrite dPr_sample.
Qed.

Lemma digest_align_get P {T : choiceType} (lo : Location)
    (k0 k1 : lo -> raw_code T) : lo.1 != shrincs_fxmss_sd_loc.1 ->
  (forall v, digest_align_rel P (k0 v) (k1 v)) ->
  digest_align_rel P (getr lo k0) (getr lo k1).
Proof.
move=> hn ih h sd js z hi. rewrite Pr_code_get (ih _ _ _ _ z hi).
by apply: eq_dlet_at => rest; rewrite Pr_code_get get_set_heap_neq.
Qed.

Lemma digest_align_put P {T : choiceType} (lo : Location) (v : lo)
    (c0 c1 : raw_code T) :
  shrincs_fxmss_st_loc.1 != lo.1 -> shrincs_fxmss_next_loc.1 != lo.1 ->
  shrincs_fxmss_rt_loc.1 != lo.1 -> shrincs_fxmss_sd_loc.1 != lo.1 ->
  digest_align_rel P c0 c1 ->
  digest_align_rel P (putr lo v c0) (putr lo v c1).
Proof.
move=> hs hn hr hd ih h sd js z hi.
have hi' : digest_align_inv (set_heap h lo v) sd js.
{ apply: (digest_align_frame h) => //; by rewrite get_set_heap_neq. }
rewrite Pr_code_put (ih _ _ _ z hi').
by apply: eq_dlet_at => rest; rewrite Pr_code_put (set_heap_commut _
  shrincs_fxmss_sd_loc).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest align reads *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque Pr_code shrincs_fxmss_lookup scheme.shrincs_fxmss_verify
  shrincs_fxmss_bound_message.

Lemma digest_align_abort P {T : choiceType} {U : choice_type}
    (k0 k1 : U -> raw_code T) :
  digest_align_rel P (v ← fail ;; k0 v) (v ← fail ;; k1 v).
Proof.
move=> h sd js z hi.
rewrite /fail !Pr_code_sample dlet_null_ext dmarginE dlet_null_ext dnullE.
symmetry. apply: dlet_at0 => rest.
by rewrite Pr_code_sample dlet_null_ext dmarginE dlet_null_ext dnullE.
Qed.

Lemma digest_align_lookup P x {T : choiceType}
    (k0 k1 : bytes 32 -> raw_code T)
    (ih : forall v, digest_align_rel P (k0 v) (k1 v)) :
  digest_align_rel P (md ← shrincs_fxmss_lookup P x ;; k0 md)
    (md ← shrincs_fxmss_lookup P x ;; k1 md).
Proof.
move=> h sd js z hi.
rewrite digest_lookup_step.
case hm: (getm (get_heap h shrincs_fxmss_rom_loc) x) => [md|].
- rewrite (ih _ _ _ _ z hi). apply: eq_dlet_at => rest.
  by rewrite digest_lookup_step get_set_heap_neq // hm.
- rewrite dfst_dlet_commut.
  transitivity ((\dlet_(md <- Pr_fst (shrincs_fxmss_digest_dist P))
    \dlet_(rest <- Pr_fst (fill_code (shrincs_fxmss_digest_dist P) js emptym))
      dfst (Pr_code (k1 md) (set_heap
        (set_heap h shrincs_fxmss_rom_loc (setm (get_heap h shrincs_fxmss_rom_loc) x
          md))
        shrincs_fxmss_sd_loc (unionm sd rest)))) z).
  + apply: eq_dlet_at => md. apply: ih.
    apply: (digest_align_frame h) => //; by rewrite get_set_heap_neq.
  + rewrite dlet_commut. apply: eq_dlet_at => rest.
    rewrite digest_lookup_step get_set_heap_neq // hm dfst_dlet_commut.
    apply: eq_dlet_at => md.
    by rewrite (set_heap_commut _ shrincs_fxmss_sd_loc).
Qed.

Lemma digest_align_hash P Q x {T : choiceType}
    (k0 k1 : option (bytes 32) -> raw_code T)
    (ih : forall v, digest_align_rel P (k0 v) (k1 v)) :
  digest_align_rel P (v ← repro_hash_body Q (shrincs_fxmss_lookup P) x ;; k0 v)
    (v ← digest_hash_body P Q x ;; k1 v).
Proof.
move=> h sd js z hi.
rewrite -digest_hash_resolve digest_hash_step.
case hg: (~~ get_heap h shrincs_fxmss_done_loc && (get_heap h shrincs_fxmss_hcnt_loc <
  shrincs_fxmss_hash_budget Q)%nat); last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_hash_step !get_set_heap_neq // hg.
  by rewrite dmarginE dlet_null_ext dnullE. }
set h1 := set_heap h shrincs_fxmss_hcnt_loc (get_heap h shrincs_fxmss_hcnt_loc).+1.
have hi1 : digest_align_inv h1 sd js.
{ apply: (digest_align_frame h) => //; by rewrite /h1 get_set_heap_neq. }
case hm: (BinInt.Z.leb _ _); cbn zeta.
- rewrite (digest_align_lookup P x _ _ (fun md => ih (Some md)) h1 sd js z hi1).
  apply: eq_dlet_at => rest.
  rewrite digest_hash_step !get_set_heap_neq // hg hm.
  by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc).
- rewrite (ih None h1 sd js z hi1).
  apply: eq_dlet_at => rest.
  rewrite digest_hash_step !get_set_heap_neq // hg hm.
  by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc).
Qed.

Lemma digest_align_get_unused P {T : choiceType} (lo : Location)
    (c0 c1 : raw_code T) : digest_align_rel P c0 c1 ->
  digest_align_rel P (_ ← get lo ;; c0) (_ ← get lo ;; c1).
Proof.
move=> ih h sd js z hi. rewrite Pr_code_get (ih _ _ _ z hi).
by apply: eq_dlet_at => rest; rewrite Pr_code_get.
Qed.

Lemma digest_align_forge P cm sg {T : choiceType}
    (k0 k1 : bool -> raw_code T)
    (ih : forall v, digest_align_rel P (k0 v) (k1 v)) :
  digest_align_rel P (v ← repro_forge_body P (shrincs_fxmss_lookup P) cm sg ;; k0 v)
    (v ← shrincs_fxmss_forge_body P false (fun _ _ _ _ _ => true) cm sg ;; k1 v).
Proof.
move=> h sd js z hi.
rewrite repro_forge_eq digest_forge_step.
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|]; last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_forge_step get_set_heap_neq // hs.
  by rewrite dmarginE dlet_null_ext dnullE. }
case hd: (get_heap h shrincs_fxmss_done_loc).
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_forge_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite hs hd. by rewrite dmarginE dlet_null_ext dnullE. }
set h1 := set_heap h shrincs_fxmss_done_loc true.
have hi1 : digest_align_inv h1 sd js.
{ apply: (digest_align_frame h) => //; by rewrite /h1 get_set_heap_neq. }
case hm: (shrincs_fxmss_message_valid cm); last first.
{ rewrite (ih false h1 sd js z hi1).
  apply: eq_dlet_at => rest. rewrite digest_forge_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite hs hd hm.
  by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc). }
case hp: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|]; last first.
{ rewrite (ih false h1 sd js z hi1).
  apply: eq_dlet_at => rest. rewrite digest_forge_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite hs hd hm hp.
  by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc). }
cbn zeta.
rewrite (digest_align_lookup P _ _ _ (fun md => ih _) h1 sd js z hi1).
apply: eq_dlet_at => rest. rewrite digest_forge_step.
repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
rewrite hs hd hm hp.
by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest align gen *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque Pr_code shrincs_fxmss_sample_keys shrincs_fxmss_sample_digests
  scheme.shrincs_fxmss_node shrincs_fxmss_lookup_keys.

Lemma digest_align_gen P Q (hl : LosslessCode (shrincs_fxmss_digest_dist P)) setup {T :
  choiceType}
    (k0 k1 : bytes 48 -> raw_code T)
    (ih : forall v, digest_align_rel P (k0 v) (k1 v)) :
  digest_align_rel P (v ← repro_gen_body P setup ;; k0 v)
    (v ← digest_gen_body P Q setup ;; k1 v).
Proof.
move=> h sd js z hi.
rewrite digest_lazy_gen_step.
case hg: (~~ isSome (get_heap h shrincs_fxmss_st_loc) && ~~ get_heap h
  shrincs_fxmss_done_loc &&
  shape.shrincs_fxmss_structure_legal setup.1.1 setup.1.2); last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite /digest_gen_body /digest.filtered.G_forge_digest_filtered
    /digest.filtered.G_forge_filtered digest_gen_step.
  rewrite !get_set_heap_neq // hg.
  by rewrite ?dmarginE ?dlet_null_ext dnullE. }
have hs : get_heap h shrincs_fxmss_st_loc = None.
{ move: hg => /andP[/andP[hs _] _].
  by case: (get_heap h shrincs_fxmss_st_loc) hs. }
have [-> [-> _]] := dai_before _ _ _ hi hs.
rewrite fill_code_nil Pr_fst_ret dlet_unit_ext union0m.
rewrite /digest_gen_body /digest.filtered.G_forge_digest_filtered
  /digest.filtered.G_forge_filtered digest_gen_step.
rewrite !get_set_heap_neq // hg.
rewrite !dfst_dlet_commut.
apply: eq_dlet_at => pp.
rewrite !dfst_dlet_commut. apply: eq_dlet_at => ks.
rewrite !dfst_dlet_commut. apply: eq_dlet_at => kp.
rewrite !dfst_dlet_commut. apply: eq_dlet_at => kt.
rewrite dfst_dlet_commut.
cbn zeta.
case hr: (scheme.shrincs_fxmss_node P
  (shrincs_fxmss_lookup_keys P true ((pp, setup.2, zeros 16), setup.1) ks kt)
  (uint jasmin_wsize.U64 0) (uint jasmin_wsize.U8 255) pp
  setup.1.1 (uint jasmin_wsize.U8 setup.1.2)) => [root|] /=; last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => table.
  by rewrite ?dmarginE ?dlet_null_ext dnullE. }
have hinv := digest_align_generated h sd js setup pp ks kp kt root hi hs.
rewrite (ih _ _ _ _ z hinv).
rewrite (digest_sample_fill P _ (shrincs_fxmss_prf_schedule_uniq _)).
apply: eq_dlet_at => table.
rewrite union0m /digest_gen_heap set_heap_contract.
rewrite (set_heap_commut _ shrincs_fxmss_sd_loc _ shrincs_fxmss_st_loc) //
  (set_heap_commut _ shrincs_fxmss_sd_loc _ shrincs_fxmss_ks_loc) //
  (set_heap_commut _ shrincs_fxmss_sd_loc _ shrincs_fxmss_kp_loc) //
  (set_heap_commut _ shrincs_fxmss_sd_loc _ shrincs_fxmss_keys_loc) //.
by rewrite set_heap_contract.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest align sign *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
Local Opaque Pr_code digest_sign_result.

Lemma digest_sign_heap_sd h st a bm r md sd :
  digest_sign_heap (set_heap h shrincs_fxmss_sd_loc sd) st a bm r md =
  set_heap (digest_sign_heap h st a bm r md) shrincs_fxmss_sd_loc sd.
Proof.
rewrite /digest_sign_heap !get_set_heap_neq //.
by rewrite (set_heap_commut _ shrincs_fxmss_sd_loc) // (set_heap_commut _
  shrincs_fxmss_sd_loc).
Qed.

Lemma digest_align_sign P Q cm {T : choiceType}
    (k0 k1 : option shrincs_fxmss_bytes -> raw_code T)
    (ih : forall v, digest_align_rel P (k0 v) (k1 v)) :
  digest_align_rel P (v ← repro_sign_body P Q (repro_sample P) cm ;; k0 v)
    (v ← digest_sign_body P Q cm ;; k1 v).
Proof.
move=> h sd js z hi.
rewrite digest_lazy_sign_step.
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|]; last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_sign_step get_set_heap_neq // ?hs.
  by rewrite dmarginE dlet_null_ext dnullE. }
case hd: (get_heap h shrincs_fxmss_done_loc).
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd.
  by rewrite dmarginE dlet_null_ext dnullE. }
case hc: (get_heap h shrincs_fxmss_scnt_loc < shrincs_fxmss_sign_budget Q)%nat; last
  first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd ?hc.
  by rewrite dmarginE dlet_null_ext dnullE. }
set h1 := set_heap (set_heap h shrincs_fxmss_scnt_loc (get_heap h
  shrincs_fxmss_scnt_loc).+1)
  shrincs_fxmss_log_loc (cm :: get_heap h shrincs_fxmss_log_loc).
have hi1 : digest_align_inv h1 sd js.
{ apply: (digest_align_frame h) => //; by rewrite /h1 !get_set_heap_neq. }
have hret : dfst (Pr_code (k0 None) h1) z =
  (\dlet_(rest <- Pr_fst (fill_code (shrincs_fxmss_digest_dist P) js emptym))
    dfst (Pr_code (k1 None) (set_heap h1 shrincs_fxmss_sd_loc (unionm sd rest)))) z.
{ exact: ih _ _ _ _ _ hi1. }
case hm: (shrincs_fxmss_message_valid cm); last first.
{ rewrite hret. apply: eq_dlet_at => rest.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd ?hc ?hm.
  by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc) // (set_heap_commut _
    shrincs_fxmss_sd_loc). }
case ha: (shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h
  shrincs_fxmss_next_loc)) => [a|]; last first.
{ rewrite hret. apply: eq_dlet_at => rest.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd ?hc ?hm ?ha.
  by rewrite /h1 (set_heap_commut _ shrincs_fxmss_sd_loc) // (set_heap_commut _
    shrincs_fxmss_sd_loc). }
set h2 := set_heap h1 shrincs_fxmss_next_loc (get_heap h shrincs_fxmss_next_loc).+1.
case hk: (get_heap h shrincs_fxmss_ks_loc) => [ks|]; last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd ?hc ?hm ?ha ?hk.
  by rewrite dmarginE dlet_null_ext dnullE. }
case hp: (get_heap h shrincs_fxmss_kp_loc) => [kp|]; last first.
{ rewrite [dfst dnull]dmarginE dlet_null_ext dnullE.
  symmetry. apply: dlet_at0 => rest.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd ?hc ?hm ?ha ?hk ?hp.
  by rewrite dmarginE dlet_null_ext dnullE. }
have [hj [hnd hrt]] := digest_align_slot h sd js st a hi hs ha.
set bm := shrincs_fxmss_bound_message cm.
have hstep (md : bytes 32) (rest : shrincs_fxmss_digest_table) :
  dfst (Pr_code (v ← digest_sign_body P Q cm ;; k1 v)
    (set_heap h shrincs_fxmss_sd_loc (unionm (setm sd a md) rest))) =
  \dlet_(r <- Pr_fst (shrincs_fxmss_secret_dist P))
    dfst (Pr_code (k1 (digest_sign_result P st ks (get_heap h shrincs_fxmss_keys_loc) a
      r md))
      (set_heap (digest_sign_heap h2 st a bm r md) shrincs_fxmss_sd_loc
        (unionm (setm sd a md) rest))).
{ apply/distr_ext => zz.
  rewrite digest_sign_step.
  repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
  rewrite ?hs ?hd ?hc ?hm ?ha ?hk ?hp.
  cbn zeta.
  rewrite hrt unionmE setmE eqxx.
  rewrite dfst_dlet_commut.
  apply: eq_dlet_at => r.
  rewrite dlet_unit_ext.
  rewrite (set_heap_commut _ shrincs_fxmss_sd_loc) // (set_heap_commut _
    shrincs_fxmss_sd_loc) //
    (set_heap_commut _ shrincs_fxmss_sd_loc) // digest_sign_heap_sd.
  by []. }
rewrite (fill_peel_at (shrincs_fxmss_digest_dist P) a js sd
  (fun m => dfst (Pr_code (v ← digest_sign_body P Q cm ;; k1 v)
    (set_heap h shrincs_fxmss_sd_loc m))) z hj
  (dai_uniq _ _ _ hi) (dai_disjoint _ _ _ hi)).
cbn beta zeta.
rewrite dfst_dlet_commut.
under [in LHS]eq_dlet => r. { rewrite dfst_dlet_commut. over. }
rewrite [in LHS]dlet_commut.
apply: eq_dlet_at => md.
transitivity ((\dlet_(r <- Pr_fst (shrincs_fxmss_secret_dist P))
  \dlet_(rest <- Pr_fst (fill_code (shrincs_fxmss_digest_dist P) (rem a js) emptym))
    dfst (Pr_code (k1 (digest_sign_result P st ks (get_heap h shrincs_fxmss_keys_loc) a
      r md))
      (set_heap (digest_sign_heap h2 st a bm r md) shrincs_fxmss_sd_loc
        (unionm (setm sd a md) rest)))) z).
- apply: eq_dlet_at => r. apply: ih.
  apply: (digest_align_consumed h _ sd js st a bm r md hi hs ha).
  + by rewrite /digest_sign_heap /h2 /h1 !get_set_heap_neq.
  + rewrite /digest_sign_heap /h2 /h1.
    repeat first [rewrite get_set_heap_eq | rewrite get_set_heap_neq; first by []].
    by [].
  + rewrite /digest_sign_heap get_set_heap_neq // get_set_heap_eq.
    by rewrite /h2 /h1 !get_set_heap_neq.
- rewrite dlet_commut. apply: eq_dlet_at => rest.
  by rewrite hstep.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest align *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Lemma resolve_lazy_gen P Q bit setup :
  resolve (G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_gen,(shrincs_fxmss_setup,bytes 48)) setup =
    repro_gen_body P setup.
Proof. by rewrite /G_forge_reprogrammed /resolve /= coerce_kleisliE. Qed.

Lemma resolve_lazy_sign P Q bit cm :
  resolve (G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_sign,(shrincs_fxmss_message,'option
    shrincs_fxmss_bytes)) cm =
    repro_sign_body P Q (repro_sample P) cm.
Proof. by rewrite /G_forge_reprogrammed /resolve /= coerce_kleisliE. Qed.

Lemma resolve_lazy_hash P Q bit x :
  resolve (G_forge_reprogrammed P Q bit)
    (shrincs_fxmss_op_hash,(shrincs_fxmss_hmsg_input,'option (bytes
    32))) x =
    repro_hash_body Q (shrincs_fxmss_lookup P) x.
Proof. by rewrite /G_forge_reprogrammed /resolve /= coerce_kleisliE. Qed.

Lemma resolve_lazy_forge P Q bit cm sg :
  resolve (G_forge_reprogrammed P Q bit) (shrincs_fxmss_op_forge,(shrincs_fxmss_message
    ×
    shrincs_fxmss_bytes,'bool)) (cm,sg) =
    (v ← repro_forge_body P (shrincs_fxmss_lookup P) cm sg ;; ret (bit && v)).
Proof. by rewrite /G_forge_reprogrammed /resolve /= coerce_kleisliE. Qed.

Local Opaque G_forge_reprogrammed G_digest Pr_code code_link resolve.

Lemma digest_align_core P Q (hl : LosslessCode (shrincs_fxmss_digest_dist P))
    (LA : Locations) (hsep : fseparate LA shrincs_fxmss_locs)
    bit {T : choiceType} {c : raw_code T} (vc : ValidCode LA I_forge c) :
  digest_align_rel P (code_link c (G_forge_reprogrammed P Q bit)) (code_link c
    (G_digest_preassigned P Q bit)).
Proof.
induction vc as [a | o x k ho hk ih | lo k hloc hk ih |
  lo v k hloc hk ih | op k hk ih].
- cbn [code_link]. exact: (digest_align_ret P hl a).
- cbn [code_link]. fmap_invert ho.
  + rewrite resolve_lazy_gen /G_digest_preassigned resolve_digest_gen.
    apply: (digest_align_gen P Q hl). by move=> v; apply: ih.
  + rewrite resolve_lazy_sign /G_digest_preassigned resolve_digest_sign.
    apply: digest_align_sign. by move=> v; apply: ih.
  + rewrite resolve_lazy_hash /G_digest_preassigned resolve_digest_hash.
    apply: digest_align_hash. by move=> v; apply: ih.
  + case: x => cm sg.
    rewrite resolve_lazy_forge /G_digest_preassigned resolve_digest_forge !bind_assoc.
    apply: digest_align_forge. by move=> v; apply: ih.
- (* Adversary reads cannot access the private digest table. *)
  cbn [code_link]. apply: digest_align_get; last exact: ih.
  have hout := notin_has_separate _ _ _ hloc hsep.
  apply/eqP => he.
  have hsd : fhas shrincs_fxmss_locs shrincs_fxmss_sd_loc by fmap_solve.
  have hin := fhas_in _ _ hsd.
  by rewrite he hin in hout.
- (* Adversary writes preserve every private game location. *)
  cbn [code_link].
  have hn (l : Location) (hm : fhas shrincs_fxmss_locs l) : l.1 != lo.1.
  { have hout := notin_has_separate _ _ _ hloc hsep.
    apply/eqP => he. have hin := fhas_in _ _ hm.
    by rewrite -he hin in hout. }
  apply: digest_align_put; try exact: ih;
    apply: hn; fmap_solve.
- cbn [code_link]. apply: digest_align_sample. exact: ih.
Qed.

Lemma digest_alignment P Q (hl : LosslessCode (shrincs_fxmss_digest_dist P))
    bit (A : adversary I_forge) :
  Adv (G_forge_reprogrammed P Q bit) (G_digest_preassigned P Q bit) A = 0.
Proof.
apply: (Adv_nom_ind _ _ _ I_forge (eq^~ (0 : Axioms.R))) => //.
move=> A' LA' VA' _ sep1 sep2.
rewrite /AdvantageE.
have hrun : fhas A_export RUN by fmap_solve.
have vc := valid_resolve _ _ _ _ RUN tt VA' hrun.
have hsep : fseparate LA' shrincs_fxmss_locs by exact: sep1.
rewrite !Pr_Pr_code !resolve_link.
have he := digest_align_core P Q hl LA' hsep bit vc empty_heap
  emptym [::] true digest_align_empty.
rewrite fill_code_nil Pr_fst_ret dlet_unit_ext union0m in he.
have vc0 : ValidCode (unionm LA' shrincs_fxmss_locs) I_forge (resolve A' RUN tt).
{ apply: valid_injectLocations _ vc. exact: fsubmapUl. }
have vg : ValidPackage (unionm LA' shrincs_fxmss_locs) [interface] I_forge
  (G_digest_preassigned P Q bit).
{ apply: valid_package_inject_locations _ (pack_valid (G_digest_preassigned P Q bit)).
  apply: fsubmapUr. exact: fseparate_compat hsep. }
have vcl := valid_code_link _ _ _ _ _ _ vc0 vg.
have hsd : fhas (unionm LA' shrincs_fxmss_locs) shrincs_fxmss_sd_loc.
{ apply: (fsubmap_fhas shrincs_fxmss_locs _ _); last by fmap_solve.
  apply: fsubmapUr. exact: fseparate_compat hsep. }
have ho := Pr_code_heap_observe _ _ _ vcl _ _ (heap_observe_initial _ _ hsd).
change (dfst (Pr_code (code_link (resolve A' RUN tt) (G_digest_preassigned P Q bit))
  (set_heap empty_heap shrincs_fxmss_sd_loc emptym)) =
  dfst (Pr_code (code_link (resolve A' RUN tt) (G_digest_preassigned P Q bit))
    empty_heap)) in ho.
rewrite ho in he.
by rewrite he subrr normr0.
Qed.

Corollary digest_alignment_sha256 Q bit (A : adversary I_forge) :
  Adv (G_forge_reprogrammed shrincs_fxmss_sha256 Q bit) (G_digest_preassigned
    shrincs_fxmss_sha256 Q bit) A = 0.
Proof.
apply: digest_alignment. exact: byte_tuple_lossless.
Qed.
