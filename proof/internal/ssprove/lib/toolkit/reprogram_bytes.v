(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.reprogram_bytes

    Classical random-oracle comparisons and finite-map fill bounds on
    byte tuples. The supplied distributions satisfy the defining equations
    of the public independent-byte sampler; no second sampler is defined.
    The prefix transport is proved in byte_sampling. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import
  ro_plus reprogram reprogram_sep fill_avoid byte_sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From mathcomp Require Import reals distr realsum.

Import PackageNotation GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Lemma byte_card_positive n : (0 < 256 ^ n)%N.
Proof. by rewrite expn_gt0. Qed.

Lemma byte_card_bits n : (256 ^ n = 2 ^ (8 * n))%N.
Proof. by rewrite expnM. Qed.

Section ByteSamplers.
Context (db : dist ('word U8))
  (hbyte : forall b, Pr_fst db b = (256%:R)^-1)
  (ds : forall n, dist (chTuple ('word U8) n))
  (hzero : prog (ds 0) = ret (nil_tuple (word U8)))
  (hsucc : forall n, prog (ds n.+1) =
    (b ← db ;; bs ← ds n ;; ret (cons_tuple b bs))).

Lemma bytes_sampler_transport n :
  Pr_fst (ds n) = dmargin (bytes_unrank n) (uniform (256 ^ n)%N).π2.
Proof.
symmetry.
exact: (sample_tuple_unrank_uniform db hbyte (fun k => prog (ds k))
  hzero hsucc n).
Qed.

Lemma repro_bytes_bound n (X R : choice_type) (dR : dist R)
  (hR : LosslessCode dR) (qh qp : nat) (A : nom_package)
  (VA : ValidPackage (loc A) (I_RO (chTuple ('word U8) n) X R) A_export A) :
  AdvOf (RO_repro (chTuple ('word U8) n) X R (ds n) dR qh qp) A
  <= qp%:R * ((qh + qp.-1)%:R / ((256 ^ n)%N)%:R).
Proof.
exact: (repro_bound_finite (256 ^ n)%N (byte_card_positive n)
  (chTuple ('word U8) n) X R (ds n) (bytes_unrank n)
  (can_inj (bytes_unrankK n)) (bytes_sampler_transport n) dR hR qh qp A VA).
Qed.

Lemma repro_sep_bytes_bound n (X R I : choice_type) (sep : X -> I)
  (dR : dist R) (hR : LosslessCode dR) (qh : nat) (A : nom_package)
  (VA : ValidPackage (loc A) (I_RO (chTuple ('word U8) n) X R) A_export A) :
  AdvOf (RO_repro_sep (chTuple ('word U8) n) X R I sep (ds n) dR qh) A
  <= qh%:R / ((256 ^ n)%N)%:R.
Proof.
exact: (repro_sep_bound_finite (256 ^ n)%N (byte_card_positive n)
  (chTuple ('word U8) n) X R I sep (ds n) (bytes_unrank n)
  (can_inj (bytes_unrankK n)) (bytes_sampler_transport n) dR hR qh A VA).
Qed.

Corollary repro_bytes_128_bound (X R : choice_type) (dR : dist R)
  (hR : LosslessCode dR) (qh : nat) (A : nom_package)
  (VA : ValidPackage (loc A) (I_RO (chTuple ('word U8) 16) X R) A_export A) :
  AdvOf (RO_repro (chTuple ('word U8) 16) X R (ds 16) dR qh 1) A
  <= qh%:R / ((2 ^ 128)%N)%:R.
Proof.
have hb := repro_bytes_bound 16 X R dR hR qh 1 A VA.
by rewrite byte_card_bits addn0 mul1r in hb.
Qed.

Corollary repro_sep_bytes_128_bound (X R I : choice_type) (sep : X -> I)
  (dR : dist R) (hR : LosslessCode dR) (qh : nat) (A : nom_package)
  (VA : ValidPackage (loc A) (I_RO (chTuple ('word U8) 16) X R) A_export A) :
  AdvOf (RO_repro_sep (chTuple ('word U8) 16) X R I sep (ds 16) dR qh) A
  <= qh%:R / ((2 ^ 128)%N)%:R.
Proof.
have hb := repro_sep_bytes_bound 16 X R I sep dR hR qh A VA.
by rewrite byte_card_bits in hb.
Qed.

Lemma fill_bytes_bad_le {K : choice_type} n (js : seq K)
  (S : {fset chTuple ('word U8) n}) (m0 : chMap K (chTuple ('word U8) n)) :
  (forall v, v \in codomm m0 -> v \notin S) ->
  Pr_fst (sd ← fill_code (ds n) js m0 ;;
    ret (has (mem S) (codomm sd))) true
  <= (size js)%:R * (size S)%:R / ((256 ^ n)%N)%:R.
Proof.
exact: (fill_bad_finite_le (256 ^ n)%N (byte_card_positive n)
  (chTuple ('word U8) n) (ds n) (bytes_unrank n)
  (can_inj (bytes_unrankK n)) (bytes_sampler_transport n) js S m0).
Qed.

End ByteSamplers.
