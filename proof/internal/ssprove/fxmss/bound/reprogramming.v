(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bound.reprogramming

    The separated random-oracle bound at the public byte samplers and the
    FXMSS query quota. Separators retain both height and index. Query
    accounting is independent of setup time, so pre-GEN HASH calls spend
    the same quota. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import
  ro_plus reprogram_sep reprogram_bytes byte_sampling.
From Shrincs Require Import schemes.
From Shrincs.internal.ssprove.fxmss Require Import params.
From mathcomp Require Import reals distr realsum.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation GRing.Theory Num.Theory Order.POrderTheory.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Definition repro_suffix : choice_type :=
  (bytes 16 × bytes 16) × (shrincs_fxmss_coord × shrincs_fxmss_bytes).
Definition repro_separator (x : repro_suffix) : shrincs_fxmss_coord := x.2.1.
Definition repro_query_budget (Q : shrincs_fxmss_resources) : nat :=
  (shrincs_fxmss_hash_budget Q + shrincs_fxmss_sign_budget Q + 1)%nat.
Definition repro_interface : Interface :=
  I_RO (bytes 16) repro_suffix (bytes 32).

Lemma repro_separator_eq (x : shrincs_fxmss_hmsg_input) :
  repro_separator x.2 = shrincs_fxmss_hmsg_separator x.
Proof. by []. Qed.

Lemma repro_byte_uniform (b : word U8) :
  Pr_fst dByte b = (256%:R)^-1.
Proof. exact: byte_sampler_uniform. Qed.

Lemma repro_sep_sha256_bound (Q : shrincs_fxmss_resources) (A : nom_package)
    (VA : ValidPackage (loc A) repro_interface A_export A) :
  AdvOf (RO_repro_sep (bytes 16) repro_suffix (bytes 32) shrincs_fxmss_coord
    repro_separator (dBytes 16) (dBytes 32) (repro_query_budget Q)) A
  <= (shrincs_fxmss_hash_budget Q + shrincs_fxmss_sign_budget Q + 1)%:R / ((2 ^
    128)%nat)%:R.
Proof.
exact: (repro_sep_bytes_128_bound dByte repro_byte_uniform dBytes
  erefl (fun _ => erefl) repro_suffix (bytes 32) shrincs_fxmss_coord repro_separator
  (dBytes 32) (byte_tuple_lossless 32) (repro_query_budget Q) A VA).
Qed.

(** The quota counts calls, irrespective of GEN. A consumed separator's
    read-back costs no additional QUERY credit. *)
Definition repro_quota (Q : shrincs_fxmss_resources) (hc sc fc qc : nat) : Prop :=
  [ /\ (hc <= shrincs_fxmss_hash_budget Q)%nat, (sc <= shrincs_fxmss_sign_budget Q)%nat,
       (fc <= 1)%nat & (qc <= hc + sc + fc)%nat ].

Lemma repro_quota_empty Q : repro_quota Q 0 0 0 0.
Proof. by split; rewrite ?leq0n. Qed.

Lemma repro_query_capacity_hash Q hc sc fc qc :
  repro_quota Q hc sc fc qc -> (hc < shrincs_fxmss_hash_budget Q)%nat ->
  (qc < repro_query_budget Q)%nat.
Proof.
move=> [hh hs hf hq] hlt.
apply: leq_ltn_trans hq _.
have h := leq_add (leq_add hlt hs) hf.
by rewrite /repro_query_budget !addSn in h *.
Qed.

Lemma repro_query_capacity_sign Q hc sc fc qc :
  repro_quota Q hc sc fc qc -> (sc < shrincs_fxmss_sign_budget Q)%nat ->
  (qc < repro_query_budget Q)%nat.
Proof.
move=> [hh hs hf hq] hlt.
apply: leq_ltn_trans hq _.
have h := leq_add (leq_add hh hlt) hf.
by rewrite /repro_query_budget addnS addSn in h *.
Qed.

Lemma repro_query_capacity_forge Q hc sc fc qc :
  repro_quota Q hc sc fc qc -> (fc < 1)%nat ->
  (qc < repro_query_budget Q)%nat.
Proof.
move=> [hh hs hf hq] hlt.
apply: leq_ltn_trans hq _.
have h := leq_add (leq_add hh hs) hlt.
by rewrite /repro_query_budget addnS in h *.
Qed.

Lemma repro_quota_hash Q hc sc fc qc (charge : bool) :
  repro_quota Q hc sc fc qc -> (hc < shrincs_fxmss_hash_budget Q)%nat ->
  repro_quota Q hc.+1 sc fc (qc + charge).
Proof.
move=> [hh hs hf hq] hlt.
split=> //.
rewrite !addSn.
apply: leq_trans (leq_add hq (leq_b1 charge)) _.
by rewrite addn1.
Qed.

Lemma repro_quota_sign Q hc sc fc qc (charge : bool) :
  repro_quota Q hc sc fc qc -> (sc < shrincs_fxmss_sign_budget Q)%nat ->
  repro_quota Q hc sc.+1 fc (qc + charge).
Proof.
move=> [hh hs hf hq] hlt.
split=> //.
rewrite addnS addSn.
apply: leq_trans (leq_add hq (leq_b1 charge)) _.
by rewrite addn1.
Qed.

Lemma repro_quota_forge Q hc sc fc qc (charge : bool) :
  repro_quota Q hc sc fc qc -> (fc < 1)%nat ->
  repro_quota Q hc sc fc.+1 (qc + charge).
Proof.
move=> [hh hs hf hq] hlt.
split=> //.
rewrite addnS.
apply: leq_trans (leq_add hq (leq_b1 charge)) _.
by rewrite addn1.
Qed.
