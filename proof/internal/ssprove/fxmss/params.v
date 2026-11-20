(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.params

    Coordinates, static address classes and lossless byte sampling support the
    FXMSS parameter and resource records. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import hash.
From Shrincs.internal.ssprove.wots Require Import instance params.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From mathcomp.experimental_reals Require Import distr.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** Addresses and coordinates *)

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.

Definition shrincs_fxmss_coord : choice_type := 'word U8 × 'word U64.

Definition shrincs_fxmss_type_class (tag : UInt8) (t : tweak) : bool :=
  t.1.1.1.2 == tag.

Definition shrincs_fxmss_tree_class := shrincs_fxmss_type_class SF_FXMSS_TREE.
Definition shrincs_fxmss_prf_class := shrincs_fxmss_type_class SF_WOTS_C_PRF.

Definition shrincs_fxmss_tree_tweak (a : shrincs_fxmss_coord) : tweak :=
  tweak_of (FxmssTree a.1 a.2).
Definition shrincs_fxmss_pk_tweak (a : shrincs_fxmss_coord) : tweak :=
  tweak_of (WotsCPk a.1 a.2).
Definition shrincs_fxmss_grind_tweak (a : shrincs_fxmss_coord) : tweak :=
  tweak_of (WotsCGrind a.1 a.2).
Definition shrincs_fxmss_chain_tweak (a : shrincs_fxmss_coord) (j k : nat) : tweak :=
  tweak_of (WotsCHash a.1 a.2 (uint U32 j) (uint U32 k)).
Definition shrincs_fxmss_prf_tweak (a : shrincs_fxmss_coord) (b : bool) (d : UInt8)
    (j : nat) : tweak :=
  tweak_of (WotsCPrf a.1 a.2 b d (uint U32 j)).

Lemma shrincs_fxmss_tree_tweak_inj : injective shrincs_fxmss_tree_tweak.
Proof. by move=> [h i] [h' i'] /= [-> ->]. Qed.

Lemma shrincs_fxmss_pk_tweak_inj : injective shrincs_fxmss_pk_tweak.
Proof. by move=> [h i] [h' i'] /= [-> ->]. Qed.

Lemma shrincs_fxmss_grind_tweak_inj : injective shrincs_fxmss_grind_tweak.
Proof. by move=> [h i] [h' i'] /= [-> ->]. Qed.

Lemma shrincs_fxmss_chain_tweak_inj a a' j j' k k' :
  j < wots_c_chain_count -> j' < wots_c_chain_count ->
  k < wots_c_w.-1 -> k' < wots_c_w.-1 ->
  shrincs_fxmss_chain_tweak a j k = shrincs_fxmss_chain_tweak a' j' k' ->
  a = a' /\ j = j' /\ k = k'.
Proof.
case: a => [h i]; case: a' => [h' i'].
move=> hj hj' hk hk' he.
split.
- exact: (congr1 (fun t : tweak => t.1.1.1.1) he).
- split.
  + apply: (@shape.uint32_inj j j' (chain_index_lt j hj)
      (chain_index_lt j' hj')).
    exact: (congr1 (fun t : tweak => t.1.2) he).
  + apply: (@shape.uint32_inj k k' (chain_position_lt k hk)
      (chain_position_lt k' hk')).
    exact: (congr1 (fun t : tweak => t.2) he).
Qed.

Lemma shrincs_fxmss_prf_tweak_inj a a' b d j j' :
  j < wots_c_chain_count -> j' < wots_c_chain_count ->
  shrincs_fxmss_prf_tweak a b d j = shrincs_fxmss_prf_tweak a' b d j' ->
  a = a' /\ j = j'.
Proof.
case: a => [h i]; case: a' => [h' i'].
move=> hj hj' he.
split.
- exact: (congr1 (fun t : tweak => t.1.1.1.1) he).
- apply: (@shape.uint32_inj j j' (chain_index_lt j hj)
    (chain_index_lt j' hj')).
  exact: (congr1 (fun t : tweak => t.1.2) he).
Qed.

Lemma shrincs_fxmss_tree_tweak_class a : shrincs_fxmss_tree_class
  (shrincs_fxmss_tree_tweak a).
Proof. by []. Qed.
Lemma shrincs_fxmss_pk_tweak_class a : wots_c_pk_class (shrincs_fxmss_pk_tweak a).
Proof. by []. Qed.
Lemma shrincs_fxmss_chain_tweak_class a j k :
  wots_c_hash_class (shrincs_fxmss_chain_tweak a j k).
Proof. by []. Qed.
Lemma shrincs_fxmss_grind_tweak_class a : wots_c_grind_class (shrincs_fxmss_grind_tweak
  a).
Proof. by []. Qed.
Lemma shrincs_fxmss_prf_tweak_class a b d j : shrincs_fxmss_prf_class
  (shrincs_fxmss_prf_tweak a b d j).
Proof. by []. Qed.

Lemma shrincs_fxmss_type_class_disjoint x y t :
  x != y -> shrincs_fxmss_type_class x t -> ~~ shrincs_fxmss_type_class y t.
Proof.
move=> hxy /eqP hx.
by rewrite /shrincs_fxmss_type_class hx.
Qed.

Lemma shrincs_fxmss_tree_tweak_separation a :
  [&& ~~ wots_c_hash_class (shrincs_fxmss_tree_tweak a),
      ~~ wots_c_pk_class (shrincs_fxmss_tree_tweak a),
      ~~ wots_c_grind_class (shrincs_fxmss_tree_tweak a)
    & ~~ shrincs_fxmss_prf_class (shrincs_fxmss_tree_tweak a)].
Proof. by []. Qed.

Lemma shrincs_fxmss_leaf_tweak_not_tree a b d j k m :
  [&& ~~ shrincs_fxmss_tree_class (shrincs_fxmss_chain_tweak a j k),
      ~~ shrincs_fxmss_tree_class (shrincs_fxmss_pk_tweak a),
      ~~ shrincs_fxmss_tree_class (shrincs_fxmss_prf_tweak a b d j)
    & ~~ shrincs_fxmss_tree_class (grinding_tweak (shrincs_fxmss_grind_tweak a) m)].
Proof. by []. Qed.

Lemma shrincs_fxmss_tree_tweak_pack a :
  to_bytes (FxmssTree a.1 a.2) =
  Shrincs.spec.pack a.1 a.2 SF_FXMSS_TREE
    (uint U32 0) (uint U32 0) (uint U32 0).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Static hash classes *)

Lemma shrincs_fxmss_partner_involutive : involutive fxmss_partner.
Proof.
case=> [[[[[h i] tag] a] b] c].
rewrite /fxmss_partner.
case h17: (tag == spec.SF_WOTS_C_PK).
- move/eqP: h17 => ->.
  by vm_compute.
- case h18: (tag == spec.SF_FXMSS_TREE).
  + move/eqP: h18 => ->.
    by vm_compute.
  + by rewrite /= h17 h18.
Qed.

Lemma shrincs_fxmss_partner_class (t : tweak) :
  fxmss_paired_class (fxmss_partner t) = fxmss_paired_class t.
Proof.
case: t => [[[[[h i] tag] a] b] c].
rewrite /fxmss_partner.
case h17: (tag == spec.SF_WOTS_C_PK).
- move/eqP: h17 => ->.
  by vm_compute.
- case h18: (tag == spec.SF_FXMSS_TREE).
  + move/eqP: h18 => ->.
    by vm_compute.
  + by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Byte samplers *)

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma byte_tuple_lossless n : LosslessCode (dBytes n).
Proof.
rewrite /dBytes /=.
elim: n => [|n ih].
- apply Lossless_ret.
- rewrite /= /dByte /=.
  apply Lossless_sample.
  + exact: LosslessOp_uniform.
  + (* Each sampled byte leaves a lossless draw of the remaining bytes. *)
    move=> x.
    rewrite /LosslessCode (Pr_fst_bind (sample_bytes_valid n)).
    under eq_dlet do rewrite Pr_fst_ret.
    rewrite -pr_predT pr_dlet.
    under eq_exp do rewrite pr_dunit /=.
    by rewrite exp_cst pr_predT ih GRing.mulr1.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Parameters and resources *)

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.

Definition shrincs_fxmss_bytes : choice_type := 'list ('word U8).
Definition shrincs_fxmss_message : choice_type := shrincs_fxmss_bytes ×
  shrincs_fxmss_bytes.
Definition shrincs_fxmss_structure : choice_type := 'bool × 'nat.
Definition shrincs_fxmss_setup : choice_type := shrincs_fxmss_structure × bytes 16.
Definition shrincs_fxmss_hmsg_input : choice_type :=
  bytes 16 × ((bytes 16 × bytes 16) × (shrincs_fxmss_coord × shrincs_fxmss_bytes)).

Definition shrincs_fxmss_hmsg_separator (x : shrincs_fxmss_hmsg_input) :
  shrincs_fxmss_coord := x.2.2.1.

Record shrincs_fxmss_params := {
  shrincs_fxmss_hash_eval : bytes 16 -> tweak -> seq UInt8 -> bytes 16 ;
  shrincs_fxmss_prf_msg_eval : bytes 16 -> bytes 16 -> shrincs_fxmss_coord ->
    shrincs_fxmss_bytes -> option (bytes 16) ;
  shrincs_fxmss_public_seed_dist : dist (bytes 16) ;
  shrincs_fxmss_secret_dist : dist (bytes 16) ;
  shrincs_fxmss_digest_dist : dist (bytes 32) ;
  shrincs_fxmss_public_seed_lossless : LosslessCode shrincs_fxmss_public_seed_dist ;
  shrincs_fxmss_secret_lossless : LosslessCode shrincs_fxmss_secret_dist
}.

Definition shrincs_fxmss_leaf_params (P : shrincs_fxmss_params) (a :
  shrincs_fxmss_coord)
    (b : bool) (d : UInt8) : wc_params.
Proof.
pose W := wc_sha256 a.1 a.2 b d.
refine {|
wcp_PP := wcp_PP W ;
wcp_N := wcp_N W ;
wcp_M := wcp_M W ;
wcp_Tw := wcp_Tw W ;
wcp_HM := wcp_HM W ;
wcp_w := wcp_w W ;
wcp_chain_count := wcp_chain_count W ;
wcp_Hcc := wcp_Hcc W ;
wcp_Hw := wcp_Hw W ;
wcp_tw_chain := wcp_tw_chain W ;
wcp_tw_prf := wcp_tw_prf W ;
wcp_tw_pk := wcp_tw_pk W ;
wcp_tw_grind := wcp_tw_grind W ;
wcp_tw_chain_inj := wcp_tw_chain_inj W ;
wcp_tw_prf_inj := wcp_tw_prf_inj W ;
wcp_Th := shrincs_fxmss_hash_eval P ;
wcp_encode_node := wcp_encode_node W ;
wcp_encode_node_inj := wcp_encode_node_inj W ;
wcp_encode_ends := wcp_encode_ends W ;
wcp_encode_ends_inj := wcp_encode_ends_inj W ;
wcp_encode_grind := wcp_encode_grind W ;
wcp_chain_class := wcp_chain_class W ;
wcp_pk_class := wcp_pk_class W ;
wcp_grind_class := wcp_grind_class W ;
wcp_tw_chain_class := wcp_tw_chain_class W ;
wcp_tw_pk_class := wcp_tw_pk_class W ;
wcp_tw_grind_class := wcp_tw_grind_class W ;
wcp_tw_chain_not_pk := wcp_tw_chain_not_pk W ;
wcp_encode_grind_class := wcp_encode_grind_class W ;
wcp_encode_grind_not_chain := wcp_encode_grind_not_chain W ;
wcp_encode_grind_not_pk := wcp_encode_grind_not_pk W ;
wcp_digits := wcp_digits W ;
wcp_digits_size := wcp_digits_size W ;
wcp_digits_wf := wcp_digits_wf W ;
wcp_digits_inj := wcp_digits_inj W ;
wcp_G0 := wcp_G0 W ;
wcp_Sig := wcp_Sig W ;
wcp_sig_encode := wcp_sig_encode W ;
wcp_sig_decode := wcp_sig_decode W ;
wcp_dPP := shrincs_fxmss_public_seed_dist P ;
wcp_dN := shrincs_fxmss_secret_dist P ;
wcp_constant_sum := wcp_constant_sum W ;
wcp_c_max := wcp_c_max W ;
|}.
Defined.

Definition shrincs_fxmss_hash_node (P : shrincs_fxmss_params) (pp : bytes 16) (a :
  shrincs_fxmss_coord)
    (l r : bytes 16) : bytes 16 :=
  shrincs_fxmss_hash_eval P pp (shrincs_fxmss_tree_tweak a) (l ++ r).

Definition shrincs_fxmss_prf_key (P : shrincs_fxmss_params) (pp : bytes 16)
    (t : tweak) (k : bytes 16) : bytes 16 := shrincs_fxmss_hash_eval P pp t k.

Lemma shrincs_fxmss_leaf_hash_eval P a b d : wcp_Th (shrincs_fxmss_leaf_params P a b d)
  = shrincs_fxmss_hash_eval P.
Proof. by []. Qed.

Lemma shrincs_fxmss_leaf_carriers P a b d :
  (wcp_PP (shrincs_fxmss_leaf_params P a b d), wcp_N (shrincs_fxmss_leaf_params P a b
    d),
   wcp_M (shrincs_fxmss_leaf_params P a b d), wcp_Tw (shrincs_fxmss_leaf_params P a b
     d)) =
  (bytes 16, bytes 16, bytes 32, tweak).
Proof. by []. Qed.

Record shrincs_fxmss_resources := {
  shrincs_fxmss_sign_budget : nat ;
  shrincs_fxmss_hash_budget : nat
}.
Definition shrincs_fxmss_resources_of q_s q_h := {| shrincs_fxmss_sign_budget := q_s;
  shrincs_fxmss_hash_budget := q_h |}.
Definition shrincs_fxmss_forge_budget (_ : shrincs_fxmss_resources) : nat := 1.
Definition shrincs_fxmss_leaf_capacity (_ : shrincs_fxmss_resources) : nat := 2 ^ 64.

Definition shrincs_fxmss_message_valid (cm : shrincs_fxmss_message) : bool :=
  (size cm.1 <= 255) && Z.leb (Z.of_nat (size cm.2)) (Z.sub (Z.pow 2 61) 368).

Definition shrincs_fxmss_bound_message (cm : shrincs_fxmss_message) :
  shrincs_fxmss_bytes :=
  [:: uint U8 0; uint U8 (size cm.1)] ++ cm.1 ++ cm.2.
