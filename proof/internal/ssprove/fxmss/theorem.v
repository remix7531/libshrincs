(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.theorem

    Total key generation, honest-signature correctness, and the concrete
    EU-CMA reduction bound. The reduction packages include the public
    experiment adapter and expose the signing and hash-query budgets. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From mathcomp Require Import reals word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import shape.
From Shrincs.internal.ssprove.fxmss Require Import
  params instance bridge.adapter bridge.keygen correct prf.reduction tree.reduction
  paired.reduction leaf.known_message_game leaf.known_message leaf.context leaf.uniform
  leaf.grind.reduction leaf.compress.reduction leaf.chain_tcr.reduction
  leaf.chain_pre.reduction security.

Import PackageNotation Order.POrderTheory Num.Theory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Definition fxmss_R_prf q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ prf.reduction.R_prf Q true).

Definition fxmss_R_prf_msg q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ prf.reduction.R_prf_msg Q true).

Definition fxmss_R_grind q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.grind.reduction.R_grind).

Definition fxmss_R_ud q_s q_h s : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ R_leaf_roots Q true ∘ R_leaf_prepared_ud s).

Definition fxmss_R_chain_tcr q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.chain_tcr.reduction.R_chain_tcr).

Definition fxmss_R_chain_pre q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.chain_pre.reduction.R_chain_pre).

Definition fxmss_R_compress q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ R_known_message Q ∘ known_message_coll_filter ∘
    leaf.compress.reduction.R_compress).

Definition fxmss_R_tree q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ tree.reduction.R_tree shrincs_fxmss_sha256 Q).

Definition fxmss_R_paired q_s q_h : nom_package :=
  let Q := shrincs_fxmss_resources_of q_s q_h in
  (shrincs_fxmss_rom_adapter ∘ paired.reduction.R_paired shrincs_fxmss_sha256 Q).

Lemma fxmss_keygen_total
    (seed : Bytes 48) (sf_structure : Bytes 2) (partner : Bytes 16) :
  let tree_shape := nth (uint U8 0) sf_structure 0 in
  let tree_depth := Z.to_nat (wunsigned (nth (uint U8 0) sf_structure 1)) in
  ((tree_shape == FXMSS_SHAPE_BALANCED) && (1 <= tree_depth <= 64)%nat
  || (tree_shape == FXMSS_SHAPE_UNBALANCED) && (1 <= tree_depth)%nat)%bool ->
  exists seckey pubkey,
    shrincs_sf_keygen seed sf_structure partner = Some (seckey, pubkey).
Proof.
case/tupleP: sf_structure => tag st.
case/tupleP: st => depth st.
rewrite (tuple0 st).
cbn zeta.
change (((tag == FXMSS_SHAPE_BALANCED)
    && (1 <= Z.to_nat (wunsigned depth) <= 64)%nat
  || (tag == FXMSS_SHAPE_UNBALANCED)
    && (1 <= Z.to_nat (wunsigned depth))%nat)%bool ->
  exists sk pk, shrincs_sf_keygen seed [tuple tag; depth] partner = Some (sk, pk)).
move/orP => [/andP [/eqP ht hd]|/andP [/eqP ht hd]].
- (* balanced *)
  subst tag.
  have hv : fxmss_sf_setup_valid ((true, Z.to_nat (wunsigned depth)), partner).
  { exact hd. }
  have hh := shrincs_fxmss_spec_keygen_total _ seed hv.
  by rewrite /shrincs_fxmss_rom_structure /= uint_to_nat in hh.
- (* unbalanced *)
  subst tag.
  have hb := wunsigned_range depth.
  change (Z.le 0 (wunsigned depth) /\ Z.lt (wunsigned depth) 256) in hb.
  have hv : fxmss_sf_setup_valid ((false, Z.to_nat (wunsigned depth)), partner).
  { apply/andP; split; first exact hd.
    apply/leP.
    change (le (Z.to_nat (wunsigned depth)) 255).
    lia. }
  have hh := shrincs_fxmss_spec_keygen_total _ seed hv.
  by rewrite /shrincs_fxmss_rom_structure /= uint_to_nat in hh.
Qed.

Lemma fxmss_sign_correct
    seed sf_structure partner seckey pubkey message ctx state signature :
  shrincs_sf_keygen seed sf_structure partner = Some (seckey, pubkey) ->
  shrincs_sf_sign message ctx seckey state = Some signature ->
  shrincs_sf_verify message signature ctx pubkey = true.
Proof. exact: shrincs_fxmss_spec_public_correct. Qed.

Lemma shrincs_fxmss_ud_budget :
  (2 ^ 64 * wots_c_chain_count = 2 ^ 69)%nat.
Proof.
change (2 ^ 64 * 2 ^ 5 = 2 ^ (64 + 5))%nat.
by rewrite expnD.
Qed.

Lemma shrincs_fxmss_paired_budget : (2 * 2 ^ 64 = 2 ^ 65)%nat.
Proof.
change (2 ^ 1 * 2 ^ 64 = 2 ^ (1 + 64))%nat.
by rewrite expnD.
Qed.

(* Transparent conversion of the concrete advantage sum takes minutes.
   Keep advantage semantics and exponential budgets symbolic here. *)
Local Opaque Adv expn.

(** Bound a canonical forger, which makes one final forgery query. *)
Lemma fxmss_secure (q_s q_h : nat) (LA : Locations)
    (c : raw_code (fxmss_sf_message × fxmss_sf_signature))
    (vc : ValidCode LA (stateful_rom.I_EUCMA_prefix fxmss_sf_scheme) c) :
  let A := fxmss_forger LA c vc in
  AdvOf (fxmss_eucma_game q_s q_h) A
  <= AdvOf (PRF_game shrincs_khf_prf (2 ^ 64 * wots_c_chain_count).+1)
       (A ∘ fxmss_R_prf q_s q_h)
   + AdvOf (PRF_game shrincs_khf_prf_msg q_s.+1)
       (A ∘ fxmss_R_prf_msg q_s q_h)
   + ((2 ^ 64)%nat)%:R * ((q_h + 1)%:R / ((2 ^ 256)%nat)%:R)
   + (q_h + q_s + 1)%:R / ((2 ^ 128)%nat)%:R
   + AdvOf (fxmss_grind_game (2 ^ 64))
       (A ∘ fxmss_R_grind q_s q_h)
   + \sum_(0 <= s < wots_c_w.-2)
       AdvOf (SMUD_game shrincs_thf wots_c_hash_class
                (2 ^ 64 * wots_c_chain_count))
         (A ∘ fxmss_R_ud q_s q_h s)
   + AdvOf (SMTCR_game shrincs_thf wots_c_hash_class
              (2 ^ 64 * (wots_c_chain_count * wots_c_w)))
       (A ∘ fxmss_R_chain_tcr q_s q_h)
   + AdvOf (SMPRE_game shrincs_thf wots_c_hash_class
              (2 ^ 64 * wots_c_chain_count))
       (A ∘ fxmss_R_chain_pre q_s q_h)
   + AdvOf (SMTCR_game shrincs_thf wots_c_pk_class (2 ^ 64))
       (A ∘ fxmss_R_compress q_s q_h)
   + AdvOf (fxmss_tree_game (2 ^ 64 - 1))
       (A ∘ fxmss_R_tree q_s q_h)
   + AdvOf (fxmss_tcrx_game (2 ^ 65 - 1))
       (A ∘ fxmss_R_paired q_s q_h).
Proof.
have sum_assoc n (G : nat -> bool -> nom_package)
    (A D : nom_package) (R : nat -> nom_package) :
    \sum_(0 <= s < n) AdvOf (G s) (A ∘ D ∘ R s) =
    \sum_(0 <= s < n) AdvOf (G s) ((A ∘ D) ∘ R s).
{ apply: eq_big_nat => s _.
  by rewrite sep_link_assoc. }
have adv_le (G0 G1 C E R : nom_package) :
    Adv G0 G1 ((C ∘ E) ∘ R) <= Adv G0 G1 (C ∘ E ∘ R).
{ have he : Adv G0 G1 (C ∘ E ∘ R) = Adv G0 G1 ((C ∘ E) ∘ R)
    by rewrite sep_link_assoc.
  rewrite -{1}he.
  exact: lexx. }

cbn zeta.
have htcr : r_chain_tcr_budget =
    (2 ^ 64 * (wots_c_chain_count * wots_c_w))%nat by reflexivity.
have h := shrincs_fxmss_eucma_bound q_s q_h LA c vc.
cbn zeta in h.
rewrite /shrincs_fxmss_leaf_capacity -shrincs_fxmss_ud_budget
  shrincs_fxmss_paired_budget htcr in h.
rewrite /security.R_prf /security.R_prf_msg /security.R_grind
  /security.R_ud /security.R_chain_tcr /security.R_chain_pre
  /security.R_compress /security.R_tree /security.R_paired in h.
change (shrincs_fxmss_sign_budget (shrincs_fxmss_resources_of q_s q_h)) with q_s in h.
rewrite /fxmss_R_prf /fxmss_R_prf_msg /fxmss_R_grind /fxmss_R_ud
  /fxmss_R_chain_tcr /fxmss_R_chain_pre /fxmss_R_compress
  /fxmss_R_tree /fxmss_R_paired.
rewrite (sum_assoc wots_c_w.-2
  (fun _ => SMUD_game shrincs_thf wots_c_hash_class
    (2 ^ 64 * wots_c_chain_count))
  (fxmss_forger LA c vc) shrincs_fxmss_rom_adapter
  (fun s => R_leaf_roots (shrincs_fxmss_resources_of q_s q_h) true ∘ R_leaf_prepared_ud
    s)).

(* Match reduction terms without unfolding the forger or the adapter. *)
set A := fxmss_forger LA c vc in h *.
set D := shrincs_fxmss_rom_adapter in h *.
clearbody A D.
eapply le_trans; first exact h.
apply: lerD; last exact: adv_le.
apply: lerD; last exact: adv_le.
apply: lerD; last exact: adv_le.
apply: lerD; last exact: adv_le.
apply: lerD; last exact: adv_le.
apply: lerD; last exact: lexx.
apply: lerD; last exact: adv_le.
apply: lerD; last exact: lexx.
apply: lerD; last exact: lexx.
apply: lerD; last exact: adv_le.
exact: adv_le.
Qed.
