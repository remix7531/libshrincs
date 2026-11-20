(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.digest.sampling

    Digest sampling and oracle-step specifications support eager/lazy alignment
    and collision accounting. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import
  reprogram fill_avoid fill_exchange byte_sampling reprogram_bytes.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games instance prf.schedule repro.games digest.games.
From mathcomp Require Import reals distr realsum.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** Digest sampling *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Lemma digest_sample_fill P as_ : uniq as_ ->
  Pr_fst (shrincs_fxmss_sample_digests P as_) =
  Pr_fst (fill_code (shrincs_fxmss_digest_dist P) as_ emptym).
Proof.
elim: as_ => [|a rest ih] //= /andP[ha hu].
rewrite (fill_fresh_cons _ _ _ ha) !Pr_fst_bind.
apply: eq_dlet => md.
rewrite Pr_fst_bind (ih hu).
apply: eq_dlet => sd.
exact: Pr_fst_ret.
Qed.

Lemma digest_sha256_uniform :
  Pr_fst (shrincs_fxmss_digest_dist shrincs_fxmss_sha256) =
    dmargin (bytes_unrank 32) (uniform (256 ^ 32)%nat).π2.
Proof.
exact: (bytes_sampler_transport dByte byte_sampler_uniform dBytes
  erefl (fun _ => erefl) 32).
Qed.

Lemma digest_sample_split_le {T : choiceType}
    (S : {fset bytes 32}) (c : Axioms.R) (z : T)
    (G0 G1 : bytes 32 -> {distr T / Axioms.R}) :
  0 <= c ->
  (forall md, md \notin S -> `|G0 md z - G1 md z| <= c) ->
  `|(\dlet_(md <- Pr_fst (shrincs_fxmss_digest_dist shrincs_fxmss_sha256)) G0 md) z -
    (\dlet_(md <- Pr_fst (shrincs_fxmss_digest_dist shrincs_fxmss_sha256)) G1 md) z|
  <= (size S)%:R / ((2 ^ 256)%nat)%:R + c.
Proof.
move=> hc hg.
have hb := finite_sample_split_le (256 ^ 32)%nat (byte_card_positive 32)
  (bytes 32) (shrincs_fxmss_digest_dist shrincs_fxmss_sha256) (bytes_unrank 32)
  (can_inj (bytes_unrankK 32)) digest_sha256_uniform S c z G0 G1 hc hg.
by rewrite byte_card_bits in hb.
Qed.

Lemma digest_preassignment_split_le {T : choiceType}
    (as_ : seq shrincs_fxmss_coord) (S : {fset bytes 32}) (c : Axioms.R) (z : T)
    (G0 G1 : shrincs_fxmss_digest_table -> {distr T / Axioms.R}) :
  uniq as_ -> 0 <= c ->
  (forall sd, (forall md, md \in codomm sd -> md \notin S) ->
    (size (domm sd) <= size as_)%nat -> `|G0 sd z - G1 sd z| <= c) ->
  `|(\dlet_(sd <- Pr_fst (shrincs_fxmss_sample_digests shrincs_fxmss_sha256 as_)) G0 sd)
    z -
    (\dlet_(sd <- Pr_fst (shrincs_fxmss_sample_digests shrincs_fxmss_sha256 as_)) G1 sd)
      z|
  <= (size as_)%:R * (size S)%:R / ((2 ^ 256)%nat)%:R + c.
Proof.
move=> hu hc hg.
rewrite (digest_sample_fill _ _ hu).
have hb := fill_split_finite_le (256 ^ 32)%nat (byte_card_positive 32)
  (bytes 32) (shrincs_fxmss_digest_dist shrincs_fxmss_sha256) (bytes_unrank 32)
  (can_inj (bytes_unrankK 32)) digest_sha256_uniform as_ S c z hc
  emptym G0 G1.
rewrite domm0 sizes0 add0n byte_card_bits in hb.
apply: hb => //.
by move=> md; rewrite codomm0 in_fset0.
Qed.

Lemma digest_schedule_bound Q sp :
  shape.shrincs_fxmss_structure_legal sp.1 sp.2 ->
  (size (shrincs_fxmss_schedule sp) <= shrincs_fxmss_leaf_capacity Q)%nat.
Proof.
move=> hlegal.
apply: leq_trans (shape.shrincs_fxmss_leaf_count_bound sp.1 sp.2 hlegal).
rewrite /shrincs_fxmss_schedule size_pmap.
have hcount := count_size
  (fun q => isSome (shape.shrincs_fxmss_select_leaf sp.1 sp.2 q))
  (iota 0 (shape.shrincs_fxmss_leaf_count sp.1 sp.2)).
by rewrite size_iota in hcount.
Qed.

Lemma digest_preassignment_bad_le Q sp (S : {fset bytes 32}) :
  shape.shrincs_fxmss_structure_legal sp.1 sp.2 ->
  Pr_fst (sd ← shrincs_fxmss_sample_digests shrincs_fxmss_sha256 (shrincs_fxmss_schedule
    sp) ;;
    ret (has (mem S) (codomm sd))) true
  <= (shrincs_fxmss_leaf_capacity Q)%:R * (size S)%:R / ((2 ^ 256)%nat)%:R.
Proof.
move=> hsp.
have he : forall md, md \in codomm (emptym : shrincs_fxmss_digest_table) -> md \notin S.
{ by move=> md; rewrite codomm0 in_fset0. }
have hb := fill_bad_finite_le (256 ^ 32)%nat (byte_card_positive 32)
  (bytes 32) (shrincs_fxmss_digest_dist shrincs_fxmss_sha256) (bytes_unrank 32)
  (can_inj (bytes_unrankK 32)) digest_sha256_uniform (shrincs_fxmss_schedule sp) S
    emptym he.
rewrite !Pr_fst_bind byte_card_bits in hb *.
rewrite (digest_sample_fill _ _ (shrincs_fxmss_prf_schedule_uniq sp)).
apply: le_trans hb _.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
apply: ler_wpM2r; first by rewrite ler0n.
by rewrite ler_nat; exact: digest_schedule_bound hsp.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest steps *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Lemma digest_lookup_step P x {T : choiceType}
    (k : bytes 32 -> raw_code T) h :
  Pr_code (md ← shrincs_fxmss_lookup P x ;; k md) h =
  match getm (get_heap h shrincs_fxmss_rom_loc) x with
  | Some md => Pr_code (k md) h
  | None => \dlet_(md <- Pr_fst (shrincs_fxmss_digest_dist P))
      Pr_code (k md) (set_heap h shrincs_fxmss_rom_loc
        (setm (get_heap h shrincs_fxmss_rom_loc) x md))
  end.
Proof.
rewrite /shrincs_fxmss_lookup Pr_code_get.
case: (getm (get_heap h shrincs_fxmss_rom_loc) x) => [md|]; first by [].
fold @bind.
rewrite bind_assoc Pr_code_fst.
apply: eq_dlet => md.
by rewrite Pr_code_put.
Qed.

Definition digest_gen_heap h (setup : shrincs_fxmss_setup) pp ks kp kt sd root : heap :=
  set_heap
    (set_heap
      (set_heap
        (set_heap
          (set_heap h shrincs_fxmss_st_loc (Some ((pp, setup.2, root), setup.1)))
          shrincs_fxmss_ks_loc (Some ks)) shrincs_fxmss_kp_loc (Some kp))
            shrincs_fxmss_keys_loc kt)
    shrincs_fxmss_sd_loc sd.

Local Opaque scheme.shrincs_fxmss_node shrincs_fxmss_sample_keys
  shrincs_fxmss_sample_digests
  shrincs_fxmss_lookup_keys.

Lemma digest_gen_step P Q bit setup {T : choiceType}
    (k : bytes 48 -> raw_code T) h :
  Pr_code (v ← resolve (G_forge P Q true true true (fun _ _ _ _ _ => true) bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) setup ;; k v) h =
  if ~~ isSome (get_heap h shrincs_fxmss_st_loc) &&
     ~~ get_heap h shrincs_fxmss_done_loc &&
     shape.shrincs_fxmss_structure_legal setup.1.1 setup.1.2 then
    \dlet_(pp <- Pr_fst (shrincs_fxmss_public_seed_dist P))
    \dlet_(ks <- Pr_fst (shrincs_fxmss_secret_dist P))
    \dlet_(kp <- Pr_fst (shrincs_fxmss_secret_dist P))
    \dlet_(kt <- Pr_fst (shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1)))
    \dlet_(sd <- Pr_fst (shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule
      setup.1)))
    let ro := scheme.shrincs_fxmss_node P
      (shrincs_fxmss_lookup_keys P true ((pp, setup.2, zeros 16), setup.1) ks kt)
      (uint jasmin_wsize.U64 0) (uint jasmin_wsize.U8 255) pp
      setup.1.1 (uint jasmin_wsize.U8 setup.1.2) in
    if isSome ro then
      Pr_code (k [tuple of pp ++ setup.2 ++ odflt (zeros 16) ro])
        (digest_gen_heap h setup pp ks kp kt sd (odflt (zeros 16) ro))
    else dnull
  else dnull.
Proof.
rewrite /G_forge /resolve /= coerce_kleisliE.
rewrite Pr_code_get.
case: (isSome (get_heap h shrincs_fxmss_st_loc)) => /=;
  first by rewrite !Pr_code_sample !dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=;
  first by rewrite !Pr_code_sample !dlet_null_ext.
case: (shape.shrincs_fxmss_structure_legal setup.1.1 setup.1.2) => /=;
  last by rewrite !Pr_code_sample !dlet_null_ext.
fold @bind.
cbn [tgt].
fold @bind.
match goal with
| |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
  change (Pr_code (@bind A B c k0) h0 = rhs)
end.
rewrite bind_assoc.
rewrite (Pr_code_fst (c := prog (shrincs_fxmss_public_seed_dist P))).
apply: eq_dlet => pp.
rewrite bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_secret_dist P))).
apply: eq_dlet => ks.
rewrite bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_secret_dist P))).
apply: eq_dlet => kp.
rewrite bind_assoc (Pr_code_fst (c := shrincs_fxmss_sample_keys P
  (shrincs_fxmss_schedule setup.1))).
apply: eq_dlet => kt.
rewrite bind_assoc (Pr_code_fst (c := shrincs_fxmss_sample_digests P
  (shrincs_fxmss_schedule setup.1))).
apply: eq_dlet => sd.
case: (isSome _) => /=.
- by rewrite !Pr_code_put.
- by rewrite !Pr_code_sample !dlet_null_ext.
Qed.

Local Opaque shrincs_fxmss_lookup.

Lemma digest_hash_resolve P Q x :
  digest_hash_body P Q x = repro_hash_body Q (shrincs_fxmss_lookup P) x.
Proof. by rewrite /digest_hash_body /digest.filtered.G_forge_digest_filtered
  /digest.filtered.G_forge_filtered /G_forge /resolve /= coerce_kleisliE. Qed.

Lemma digest_hash_step P Q x {T : choiceType}
    (k : option (bytes 32) -> raw_code T) h :
  Pr_code (v ← digest_hash_body P Q x ;; k v) h =
  if ~~ get_heap h shrincs_fxmss_done_loc && (get_heap h shrincs_fxmss_hcnt_loc <
    shrincs_fxmss_hash_budget Q)%nat then
    let h1 := set_heap h shrincs_fxmss_hcnt_loc (get_heap h shrincs_fxmss_hcnt_loc).+1
      in
    if Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111) then
      Pr_code (md ← shrincs_fxmss_lookup P x ;; k (Some md)) h1
    else Pr_code (k None) h1
  else dnull.
Proof.
rewrite digest_hash_resolve /repro_hash_body Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=;
  first by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_hcnt_loc < shrincs_fxmss_hash_budget Q)%nat => /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_put.
case: (Z.leb _ _) => //.
match goal with
| |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
  change (Pr_code (@bind A B c k0) h0 = rhs)
end.
by rewrite !bind_assoc.
Qed.

Lemma digest_forge_step P filter cm sg {T : choiceType}
    (k : bool -> raw_code T) h :
  Pr_code (v ← shrincs_fxmss_forge_body P filter (fun _ _ _ _ _ => true) cm sg ;; k v) h
    =
  match get_heap h shrincs_fxmss_st_loc with
  | None => dnull
  | Some st =>
      if get_heap h shrincs_fxmss_done_loc then dnull else
      let h1 := set_heap h shrincs_fxmss_done_loc true in
      if shrincs_fxmss_message_valid cm then
        match shrincs_sf_parse sg with
        | None => Pr_code (k false) h1
        | Some (a, r, i, fsig) =>
            let x := (r, ((st.1.1.1, st.1.2),
              ((a, i), shrincs_fxmss_bound_message cm))) in
            Pr_code (md ← shrincs_fxmss_lookup P x ;;
              k (scheme.shrincs_fxmss_verify P st.1.1.1 st.1.2 (a, i) fsig md &&
                (cm \notin get_heap h shrincs_fxmss_log_loc) &&
                (if filter then ~~ ((md \in codomm (get_heap h shrincs_fxmss_sd_loc)) &&
                  (getm (get_heap h shrincs_fxmss_rt_loc) x.2.2 != Some r)) else true)
                    && true)) h1
        end
      else Pr_code (k false) h1
  end.
Proof.
rewrite /shrincs_fxmss_forge_body Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=;
  first by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_put !Pr_code_get.
rewrite !get_set_heap_neq //.
case: (shrincs_fxmss_message_valid cm) => //.
case: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|] //.
match goal with
| |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
  change (Pr_code (@bind A B c k0) h0 = rhs)
end.
by rewrite !bind_assoc.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest sign steps *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Definition digest_sign_result P (st : shrincs_fxmss_state) ks kt a r md : option
  shrincs_fxmss_bytes :=
  match scheme.shrincs_fxmss_sign P md (shrincs_fxmss_lookup_keys P true st ks kt)
    a.2 a.1 st.1.1.1 st.2.1 (uint jasmin_wsize.U8 st.2.2) with
  | Some sg => shrincs_sf_encode a.1 r a.2 sg
  | None => None
  end.

Definition digest_sign_heap h (st : shrincs_fxmss_state) a bm r md : heap :=
  set_heap
    (set_heap h shrincs_fxmss_rt_loc (setm (get_heap h shrincs_fxmss_rt_loc) (a,bm) r))
    shrincs_fxmss_rom_loc (setm (get_heap h shrincs_fxmss_rom_loc)
      (r, ((st.1.1.1, st.1.2), (a,bm))) md).

Local Opaque scheme.shrincs_fxmss_sign shrincs_fxmss_lookup_keys shrincs_fxmss_lookup.

Lemma digest_sign_step P Q cm {T : choiceType}
    (k : option shrincs_fxmss_bytes -> raw_code T) h :
  Pr_code (v ← digest_sign_body P Q cm ;; k v) h =
  match get_heap h shrincs_fxmss_st_loc with
  | None => dnull
  | Some st =>
    if get_heap h shrincs_fxmss_done_loc then dnull else
    if (get_heap h shrincs_fxmss_scnt_loc < shrincs_fxmss_sign_budget Q)%nat then
      let h1 := set_heap (set_heap h shrincs_fxmss_scnt_loc (get_heap h
        shrincs_fxmss_scnt_loc).+1)
        shrincs_fxmss_log_loc (cm :: get_heap h shrincs_fxmss_log_loc) in
      if shrincs_fxmss_message_valid cm then
        match shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h
          shrincs_fxmss_next_loc) with
        | None => Pr_code (k None) h1
        | Some a =>
          let h2 := set_heap h1 shrincs_fxmss_next_loc (get_heap h
            shrincs_fxmss_next_loc).+1 in
          match get_heap h shrincs_fxmss_ks_loc, get_heap h shrincs_fxmss_kp_loc with
          | Some ks, Some kp =>
            let bm := shrincs_fxmss_bound_message cm in
            \dlet_(r <- match getm (get_heap h shrincs_fxmss_rt_loc) (a,bm) with
              | Some r => dunit r | None => Pr_fst (shrincs_fxmss_secret_dist P) end)
            \dlet_(md <- match getm (get_heap h shrincs_fxmss_sd_loc) a with
              | Some md => dunit md | None => Pr_fst (shrincs_fxmss_digest_dist P) end)
            Pr_code (k (digest_sign_result P st ks (get_heap h shrincs_fxmss_keys_loc) a
              r md))
              (digest_sign_heap h2 st a bm r md)
          | _, _ => dnull
          end
        end
      else Pr_code (k None) h1
    else dnull
  end.
Proof.
rewrite /digest_sign_body /digest.filtered.G_forge_digest_filtered
  /digest.filtered.G_forge_filtered /G_forge /resolve /= coerce_kleisliE.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=;
  first by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_scnt_loc < shrincs_fxmss_sign_budget Q)%nat => /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get !Pr_code_put.
case: (shrincs_fxmss_message_valid cm) => //.
rewrite Pr_code_get.
get_heap_simpl.
rewrite !get_set_heap_neq //.
case: (shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h
  shrincs_fxmss_next_loc)) => [a|] /=;
  last by [].
rewrite Pr_code_put Pr_code_get !get_set_heap_neq //.
case: (get_heap h shrincs_fxmss_ks_loc) => [ks|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get !get_set_heap_neq //.
case: (get_heap h shrincs_fxmss_kp_loc) => [kp|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite !Pr_code_get !get_set_heap_neq //.
case: (getm (get_heap h shrincs_fxmss_rt_loc) (a,shrincs_fxmss_bound_message cm)) =>
  [r|].
- rewrite dlet_unit_ext Pr_code_put Pr_code_get !get_set_heap_neq //.
  case: (getm (get_heap h shrincs_fxmss_sd_loc) a) => [md|].
  + rewrite dlet_unit_ext !Pr_code_get !Pr_code_put !get_set_heap_neq //.
    rewrite /digest_sign_result /digest_sign_heap !get_set_heap_neq //.
    case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|] //.
  + (* The message randomness is cached, but the leaf digest needs sampling. *)
    match goal with
    | |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
      change (Pr_code (@bind A B c k0) h0 = rhs)
    end.
    rewrite !bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_digest_dist P))).
    apply: eq_dlet => md.
    rewrite !Pr_code_get !Pr_code_put !get_set_heap_neq //.
    rewrite /digest_sign_result /digest_sign_heap !get_set_heap_neq //.
    case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|] //.
- match goal with
  | |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
    change (Pr_code (@bind A B c k0) h0 = rhs)
  end.
  rewrite !bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_secret_dist P))).
  apply: eq_dlet => r.
  rewrite Pr_code_put Pr_code_get !get_set_heap_neq //.
  case: (getm (get_heap h shrincs_fxmss_sd_loc) a) => [md|].
  + rewrite dlet_unit_ext !Pr_code_get !Pr_code_put !get_set_heap_neq //.
    rewrite /digest_sign_result /digest_sign_heap !get_set_heap_neq //.
    case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|] //.
  + (* Both the message randomness and the leaf digest need sampling. *)
    match goal with
    | |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
      change (Pr_code (@bind A B c k0) h0 = rhs)
    end.
    rewrite !bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_digest_dist P))).
    apply: eq_dlet => md.
    rewrite !Pr_code_get !Pr_code_put !get_set_heap_neq //.
    rewrite /digest_sign_result /digest_sign_heap !get_set_heap_neq //.
    case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|] //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Digest lazy steps *)

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Local Opaque scheme.shrincs_fxmss_sign shrincs_fxmss_lookup_keys.

Lemma digest_lazy_sign_step P Q cm {T : choiceType}
    (k : option shrincs_fxmss_bytes -> raw_code T) h :
  Pr_code (v ← repro_sign_body P Q (repro_sample P) cm ;; k v) h =
  match get_heap h shrincs_fxmss_st_loc with
  | None => dnull
  | Some st =>
    if get_heap h shrincs_fxmss_done_loc then dnull else
    if (get_heap h shrincs_fxmss_scnt_loc < shrincs_fxmss_sign_budget Q)%nat then
      let h1 := set_heap (set_heap h shrincs_fxmss_scnt_loc (get_heap h
        shrincs_fxmss_scnt_loc).+1)
        shrincs_fxmss_log_loc (cm :: get_heap h shrincs_fxmss_log_loc) in
      if shrincs_fxmss_message_valid cm then
        match shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h
          shrincs_fxmss_next_loc) with
        | None => Pr_code (k None) h1
        | Some a =>
          let h2 := set_heap h1 shrincs_fxmss_next_loc (get_heap h
            shrincs_fxmss_next_loc).+1 in
          match get_heap h shrincs_fxmss_ks_loc, get_heap h shrincs_fxmss_kp_loc with
          | Some ks, Some kp =>
            let bm := shrincs_fxmss_bound_message cm in
            \dlet_(r <- Pr_fst (shrincs_fxmss_secret_dist P))
            \dlet_(md <- Pr_fst (shrincs_fxmss_digest_dist P))
            Pr_code (k (digest_sign_result P st ks (get_heap h shrincs_fxmss_keys_loc) a
              r md))
              (digest_sign_heap h2 st a bm r md)
          | _, _ => dnull
          end
        end
      else Pr_code (k None) h1
    else dnull
  end.
Proof.
rewrite /repro_sign_body /repro_sample.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=;
  first by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_scnt_loc < shrincs_fxmss_sign_budget Q)%nat => /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get !Pr_code_put.
case: (shrincs_fxmss_message_valid cm) => //.
rewrite Pr_code_get.
get_heap_simpl.
rewrite !get_set_heap_neq //.
case: (shape.shrincs_fxmss_select_leaf st.2.1 st.2.2 (get_heap h
  shrincs_fxmss_next_loc)) => [a|] /=;
  last by [].
rewrite Pr_code_put Pr_code_get !get_set_heap_neq //.
case: (get_heap h shrincs_fxmss_ks_loc) => [ks|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite Pr_code_get !get_set_heap_neq //.
case: (get_heap h shrincs_fxmss_kp_loc) => [kp|] /=;
  last by rewrite Pr_code_sample dlet_null_ext.
rewrite !Pr_code_get !get_set_heap_neq //.
match goal with
| |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
  change (Pr_code (@bind A B c k0) h0 = rhs)
end.
rewrite !bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_secret_dist P))).
apply: eq_dlet => r.
rewrite !bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_digest_dist P))).
apply: eq_dlet => md.
rewrite !Pr_code_get !Pr_code_put !get_set_heap_neq //.
rewrite /digest_sign_result /digest_sign_heap !get_set_heap_neq //.
case: (scheme.shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|] //;
by rewrite (set_heap_commut _ shrincs_fxmss_rom_loc _ shrincs_fxmss_rt_loc).
Qed.

Local Opaque scheme.shrincs_fxmss_node shrincs_fxmss_sample_keys.

Lemma digest_lazy_gen_step P setup {T : choiceType}
    (k : bytes 48 -> raw_code T) h :
  Pr_code (v ← repro_gen_body P setup ;; k v) h =
  if ~~ isSome (get_heap h shrincs_fxmss_st_loc) &&
     ~~ get_heap h shrincs_fxmss_done_loc &&
     shape.shrincs_fxmss_structure_legal setup.1.1 setup.1.2 then
    \dlet_(pp <- Pr_fst (shrincs_fxmss_public_seed_dist P))
    \dlet_(ks <- Pr_fst (shrincs_fxmss_secret_dist P))
    \dlet_(kp <- Pr_fst (shrincs_fxmss_secret_dist P))
    \dlet_(kt <- Pr_fst (shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1)))
    let ro := scheme.shrincs_fxmss_node P
      (shrincs_fxmss_lookup_keys P true ((pp, setup.2, zeros 16), setup.1) ks kt)
      (uint jasmin_wsize.U64 0) (uint jasmin_wsize.U8 255) pp
      setup.1.1 (uint jasmin_wsize.U8 setup.1.2) in
    if isSome ro then
      Pr_code (k [tuple of pp ++ setup.2 ++ odflt (zeros 16) ro])
        (digest_gen_heap h setup pp ks kp kt emptym (odflt (zeros 16) ro))
    else dnull
  else dnull.
Proof.
rewrite /repro_gen_body.
rewrite Pr_code_get.
case: (isSome (get_heap h shrincs_fxmss_st_loc)) => /=;
  first by rewrite !Pr_code_sample !dlet_null_ext.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=;
  first by rewrite !Pr_code_sample !dlet_null_ext.
case: (shape.shrincs_fxmss_structure_legal setup.1.1 setup.1.2) => /=;
  last by rewrite !Pr_code_sample !dlet_null_ext.
fold @bind.
cbn [tgt].
fold @bind.
match goal with
| |- Pr_code (?f ?A ?B ?c ?k0) ?h0 = ?rhs =>
  change (Pr_code (@bind A B c k0) h0 = rhs)
end.
rewrite bind_assoc.
rewrite (Pr_code_fst (c := prog (shrincs_fxmss_public_seed_dist P))).
apply: eq_dlet => pp.
rewrite bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_secret_dist P))).
apply: eq_dlet => ks.
rewrite bind_assoc (Pr_code_fst (c := prog (shrincs_fxmss_secret_dist P))).
apply: eq_dlet => kp.
rewrite bind_assoc (Pr_code_fst (c := shrincs_fxmss_sample_keys P
  (shrincs_fxmss_schedule setup.1))).
apply: eq_dlet => kt.
case: (isSome _) => /=.
- by rewrite !Pr_code_put.
- by rewrite !Pr_code_sample !dlet_null_ext.
Qed.
