(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.commitments

    GEN fixes one digest for each scheduled coordinate. The batch commitment
    reads that table in signing order; every later signing lookup reads the
    same value. Totality follows from the sampler, including failed leaves. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import params shape games leaf.paths.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation.
#[local] Open Scope package_scope.

Definition leaf_digest_total (as_ : seq shrincs_fxmss_coord) (sd :
  shrincs_fxmss_digest_table) :=
  all (fun a => isSome (getm sd a)) as_.

Definition leaf_committed_digest (sd : shrincs_fxmss_digest_table) (a :
  shrincs_fxmss_coord) :=
  odflt (zeros 32) (getm sd a).

Definition leaf_commitments (sp : shrincs_fxmss_structure) (sd :
  shrincs_fxmss_digest_table) :
    seq (shrincs_fxmss_coord * bytes 32) :=
  [seq (a, leaf_committed_digest sd a) | a <- shrincs_fxmss_schedule sp].

Definition leaf_digest_lookup (P : shrincs_fxmss_params) (sd :
  shrincs_fxmss_digest_table)
    (a : shrincs_fxmss_coord) : raw_code (bytes 32) :=
  match getm sd a with
  | Some md => ret md
  | None => md ← shrincs_fxmss_digest_dist P ;; ret md
  end.

Lemma leaf_digest_total_set as_ sd a md :
  leaf_digest_total as_ sd ->
  leaf_digest_total (a :: as_) (setm sd a md).
Proof.
move=> hsd.
rewrite /leaf_digest_total /= setmE eqxx /=.
apply/allP=> a' ha'.
rewrite setmE.
case: ifP => // _.
exact: (allP hsd a' ha').
Qed.

Lemma leaf_digest_total_lookup as_ sd a :
  leaf_digest_total as_ sd -> a \in as_ ->
  getm sd a = Some (leaf_committed_digest sd a).
Proof.
move=> hsd ha.
have := allP hsd a ha.
by rewrite /leaf_committed_digest; case: getm.
Qed.

Lemma leaf_commitments_length sp sd :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size (leaf_commitments sp sd) = shrincs_fxmss_leaf_count sp.1 sp.2.
Proof.
by move=> hsp; rewrite /leaf_commitments size_map leaf_schedule_length.
Qed.

Lemma leaf_commitments_coordinates sp sd :
  unzip1 (leaf_commitments sp sd) = shrincs_fxmss_schedule sp.
Proof. by rewrite /leaf_commitments /unzip1 -map_comp /= map_id. Qed.

Lemma leaf_commitment_nth sp sd q :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  q < shrincs_fxmss_leaf_count sp.1 sp.2 ->
  nth ((uint U8 0, uint U64 0), zeros 32) (leaf_commitments sp sd) q =
    (leaf_coord_at sp q, leaf_committed_digest sd (leaf_coord_at sp q)).
Proof.
move=> hsp hq.
rewrite /leaf_commitments (nth_map (uint U8 0, uint U64 0))
  ?leaf_schedule_length //.
by rewrite leaf_schedule_nth.
Qed.

Lemma leaf_digest_lookup_committed P sp sd q a :
  leaf_digest_total (shrincs_fxmss_schedule sp) sd ->
  shrincs_fxmss_select_leaf sp.1 sp.2 q = Some a ->
  leaf_digest_lookup P sd a = ret (leaf_committed_digest sd a).
Proof.
move=> hsd hs.
rewrite /leaf_digest_lookup (leaf_digest_total_lookup _ _ _ hsd) //.
exact: leaf_select_in_schedule hs.
Qed.

Lemma leaf_sample_digests_congr (P : shrincs_fxmss_params) (as_ : seq
  shrincs_fxmss_coord)
    (A : choice_type) (k0 k1 : shrincs_fxmss_digest_table -> raw_code A) :
  (forall sd, leaf_digest_total as_ sd -> k0 sd = k1 sd) ->
  (sd ← shrincs_fxmss_sample_digests P as_ ;; k0 sd) =
  (sd ← shrincs_fxmss_sample_digests P as_ ;; k1 sd).
Proof.
elim: as_ k0 k1 => [|a as_ ih] k0 k1 hk /=.
- exact: hk isT.
- (* A fresh head digest preserves totality of the table. *)
  rewrite !bind_assoc.
  congr (bind _ _).
  apply boolp.funext => md.
  rewrite !bind_assoc.
  apply: ih.
  move=> sd hsd.
  apply: hk.
  exact: leaf_digest_total_set hsd.
Qed.

Lemma leaf_sample_digests_total P as_ :
  (sd ← shrincs_fxmss_sample_digests P as_ ;; ret (sd, leaf_digest_total as_ sd)) =
  (sd ← shrincs_fxmss_sample_digests P as_ ;; ret (sd, true)).
Proof.
apply: leaf_sample_digests_congr.
by move=> sd ->.
Qed.

(** The later lookup in G_forge_filtered's SIGN is the value committed at GEN. *)
Lemma leaf_gen_digest_commitment P sp q a (A : choice_type)
    (k : shrincs_fxmss_digest_table -> bytes 32 -> raw_code A) :
  shrincs_fxmss_select_leaf sp.1 sp.2 q = Some a ->
  (sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule sp) ;;
   md ← leaf_digest_lookup P sd a ;; k sd md) =
  (sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule sp) ;;
   k sd (leaf_committed_digest sd a)).
Proof.
move=> hs.
apply: leaf_sample_digests_congr.
move=> sd hsd.
by rewrite (leaf_digest_lookup_committed P sp sd q a hsd hs).
Qed.

Lemma leaf_commitments_slot sp sd a :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  nth ((uint U8 0, uint U64 0), zeros 32)
    (leaf_commitments sp sd) (leaf_slot sp a) =
    (a, leaf_committed_digest sd a).
Proof.
move=> hsp ha.
have [hq he] := leaf_schedule_slot sp a hsp ha.
by rewrite (leaf_commitment_nth sp sd _ hsp hq) he.
Qed.
