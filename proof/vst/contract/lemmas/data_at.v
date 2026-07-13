(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.data_at: list/VST val bridges for blocks and addrs.

    Length, [Znth], [upd_Znth], and round-trip lemmas for the
    [block_to_vals] / [blocks_to_vals] / [adrs_to_vals] /
    [digits_to_vals] encodings that funspecs use to expose pure-Rocq
    blocks to the C side.  The [shrincs_adrs_put32] bridge lemmas connect the
    raw-byte [sublist] splice (the [shrincs_adrs_put32] funspec post) to the
    [adrs] setters. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.radrs.
From Vst Require Import theory.pure.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** [block_to_vals] -- list-shape and indexing. *)

Lemma block_to_vals_length : forall b,
  Zlength (block_to_vals b) = Zlength b.
Proof. intros. unfold block_to_vals. now rewrite Zlength_map. Qed.

Lemma block_to_vals_app : forall b1 b2,
  block_to_vals (b1 ++ b2) = block_to_vals b1 ++ block_to_vals b2.
Proof. intros. unfold block_to_vals. apply map_app. Qed.

Lemma block_to_vals_sublist : forall i j (b : block),
  block_to_vals (sublist i j b) = sublist i j (block_to_vals b).
Proof. intros. unfold block_to_vals. rewrite sublist_map. reflexivity. Qed.

Lemma Znth_block_to_vals : forall i b,
  0 <= i < Zlength b ->
  Znth i (block_to_vals b) = Vubyte (Byte.repr (Znth i b)).
Proof.
  intros. unfold block_to_vals.
  rewrite Znth_map by assumption.
  reflexivity.
Qed.

(** A [repeat] of C zero-int values is the [block_to_vals] encoding of the
    model [zeros k] block ([= repeat 0 k]).  Used to fold [memset] output
    back into the model preimage in the tweakable-hash body proofs. *)
Lemma zeros_to_vals : forall k,
  repeat (Vint (Int.repr 0)) k = block_to_vals (zeros k).
Proof.
  intros k. unfold zeros, block_to_vals.
  rewrite map_repeat.
  reflexivity.
Qed.

(** Split a zero-int [repeat] block by two nonnegative [Z] lengths.  Used
    to carve a [memset]-zeroed scratch buffer into preimage regions in the
    tweakable-hash body proofs. *)
Lemma repeat_Vint0_Zsplit : forall m n : Z,
  0 <= m -> 0 <= n ->
  repeat (Vint (Int.repr 0)) (Z.to_nat (m + n))
  = repeat (Vint (Int.repr 0)) (Z.to_nat m) ++ repeat (Vint (Int.repr 0)) (Z.to_nat n).
Proof. intros. rewrite Z2Nat.inj_add by lia. rewrite repeat_app. reflexivity. Qed.

(** A list of blocks flattened to a VST [list int]. *)
Definition block_ints (b : block) : list int :=
  map (fun x : byte => Int.repr (x mod 256)) b.

Lemma Zlength_concat_fixed : forall (bs : list block),
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (concat bs) = n_bytes * Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; intros HF.
  - reflexivity.
  - inversion HF; subst.
    simpl concat. simpl length.
    rewrite Zlength_app, IH by assumption.
    rewrite Nat2Z.inj_succ, H1. lia.
Qed.

Lemma blocks_to_vals_eq_Vint : forall bs,
  blocks_to_vals bs = map Vint (block_ints (concat bs)).
Proof.
  intros.
  unfold blocks_to_vals, block_ints, Vubyte.
  rewrite map_map.
  apply map_ext.
  intros x.
  f_equal.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  reflexivity.
Qed.

(** [blocks_to_vals] of a block list is [block_to_vals] of its flattening
    (both are [map (Vubyte o Byte.repr)] over [concat]). *)
Lemma blocks_to_vals_concat : forall bs,
  blocks_to_vals bs = block_to_vals (concat bs).
Proof. reflexivity. Qed.

Lemma block_to_vals_eq_Vint : forall b,
  block_to_vals b = map Vint (block_ints b).
Proof.
  intros.
  unfold block_to_vals, block_ints, Vubyte.
  rewrite map_map.
  apply map_ext.
  intros x.
  f_equal.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  reflexivity.
Qed.

Lemma Zlength_block_ints : forall b,
  Zlength (block_ints b) = Zlength b.
Proof.
  intros.
  unfold block_ints.
  apply Zlength_map.
Qed.

(** Every entry of [block_ints b] is a [uint8_t] range value. *)
Lemma Forall_block_ints_bound : forall b : block,
  Forall (fun i : int => 0 <= Int.unsigned i < 256) (block_ints b).
Proof.
  intros b.
  unfold block_ints.
  rewrite Forall_map.
  apply Forall_forall.
  intros x _.
  unfold Basics.compose.
  assert (Hb : 0 <= x mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  rewrite Int.unsigned_repr by rep_lia.
  lia.
Qed.

(* ================================================================= *)
(** ** [adrs_bytes] / [adrs_to_vals] -- length, byte-range, splices.

    ([to_byte]'s own length / Zlength facts are [to_byte_length] /
    [to_byte_Zlength] in [theory.pure], imported above.) *)

Lemma Zlength_adrs_bytes : forall a : adrs, Zlength (adrs_bytes a) = 22.
Proof.
  intros a. unfold adrs_bytes.
  rewrite !Zlength_app, !to_byte_Zlength. reflexivity.
Qed.

Lemma Zlength_adrs_to_vals : forall a, Zlength (adrs_to_vals a) = 22.
Proof.
  intros a. unfold adrs_to_vals.
  rewrite block_to_vals_length, Zlength_adrs_bytes. reflexivity.
Qed.

(** The [shrincs_adrs_put32] funspec leaves [addr] holding a raw-byte splice
    [sublist 0 off content ++ to_byte v 4 ++ sublist (off+4) 22 content].
    At the three call offsets this equals the setter applied to
    [adrs_bytes].  Proved by abstracting the seven [to_byte] segments and
    letting [list_solve] evaluate the [sublist]s from their lengths. *)

(** Splice a middle segment [M -> M'] of a 3-way split, addressed by the
    [Zlength] of the surrounding pieces.  Pure list arithmetic --
    [list_solve] handles the [sublist]s once the split is explicit. *)
Lemma sublist_splice_mid : forall (P M S M' : list byte),
  Zlength M' = Zlength M ->
  sublist 0 (Zlength P) (P ++ M ++ S) ++ M'
    ++ sublist (Zlength P + Zlength M) (Zlength P + Zlength M + Zlength S) (P ++ M ++ S)
  = P ++ M' ++ S.
Proof.
  intros P M S M' H.
  pose proof (Zlength_nonneg P).
  pose proof (Zlength_nonneg M).
  pose proof (Zlength_nonneg S).
  rewrite sublist_app1 by lia.
  rewrite sublist_same by lia.
  rewrite sublist_app2 by lia.
  replace (Zlength P + Zlength M - Zlength P) with (Zlength M) by lia.
  replace (Zlength P + Zlength M + Zlength S - Zlength P) with (Zlength M + Zlength S) by lia.
  rewrite sublist_app2 by lia.
  replace (Zlength M - Zlength M) with 0 by lia.
  replace (Zlength M + Zlength S - Zlength M) with (Zlength S) by lia.
  rewrite sublist_same by lia.
  reflexivity.
Qed.

(** [adrs_to_vals a] as the flat wire view -- the entry point for the
    byte-level store reasoning in the body proofs.  The bodies mutate
    [radrs] (the C's under-construction view: six [Z] wire fields, so
    every partial byte state is representable), and [radrs_bytes
    (adrs_to_raw a) = adrs_bytes a] bridges back at the funspec boundary. *)
Lemma adrs_to_vals_raw : forall a : adrs,
  adrs_to_vals a = block_to_vals (radrs_bytes (adrs_to_raw a)).
Proof. intros a. unfold adrs_to_vals. rewrite radrs_bytes_to_raw. reflexivity. Qed.

Lemma Zlength_radrs_bytes : forall r, Zlength (radrs_bytes r) = 22.
Proof.
  intros r. unfold radrs_bytes.
  rewrite !Zlength_app, !to_byte_Zlength. reflexivity.
Qed.

(** The [shrincs_adrs_put32] funspec leaves the buffer holding a raw-byte
    splice; at the three payload offsets it equals the corresponding
    [rset_payload_*] of the wire view.  The [Z]-valued fields make the
    splice exact -- no [repr]-truncation bridge is needed. *)
Lemma shrincs_adrs_put32_reserved : forall r v,
  sublist 0 10 (radrs_bytes r) ++ to_byte v 4 ++ sublist (10 + 4) 22 (radrs_bytes r)
  = radrs_bytes (rset_payload_a r v).
Proof.
  intros r v.
  pose (P := to_byte (rtag r) 1 ++ to_byte (ridx r) 8 ++ to_byte (rtype r) 1).
  pose (M := to_byte (rpa r) 4).
  pose (S := to_byte (rpb r) 4 ++ to_byte (rpc r) 4).
  assert (HP : Zlength P = 10)
    by (subst P; rewrite ?Zlength_app, ?to_byte_Zlength; reflexivity).
  assert (Hab : radrs_bytes r = P ++ M ++ S)
    by (subst P M S; unfold radrs_bytes; rewrite <- ?app_assoc; reflexivity).
  assert (Hab' : radrs_bytes (rset_payload_a r v) = P ++ to_byte v 4 ++ S)
    by (subst P S; unfold radrs_bytes, rset_payload_a;
        cbn [rtag ridx rtype rpa rpb rpc]; rewrite <- ?app_assoc; reflexivity).
  rewrite Hab, Hab'.
  replace 10 with (Zlength P) by lia.
  replace (Zlength P + 4) with (Zlength P + Zlength M)
    by (subst M; rewrite to_byte_Zlength; lia).
  replace 22 with (Zlength P + Zlength M + Zlength S)
    by (subst M S; rewrite ?Zlength_app, ?to_byte_Zlength, ?Zlength_nil; lia).
  apply sublist_splice_mid; subst M; rewrite !to_byte_Zlength; lia.
Qed.

Lemma shrincs_adrs_put32_chain : forall r v,
  sublist 0 14 (radrs_bytes r) ++ to_byte v 4 ++ sublist (14 + 4) 22 (radrs_bytes r)
  = radrs_bytes (rset_payload_b r v).
Proof.
  intros r v.
  pose (P := to_byte (rtag r) 1 ++ to_byte (ridx r) 8 ++ to_byte (rtype r) 1
             ++ to_byte (rpa r) 4).
  pose (M := to_byte (rpb r) 4).
  pose (S := to_byte (rpc r) 4).
  assert (HP : Zlength P = 14)
    by (subst P; rewrite ?Zlength_app, ?to_byte_Zlength; reflexivity).
  assert (Hab : radrs_bytes r = P ++ M ++ S)
    by (subst P M S; unfold radrs_bytes; rewrite <- ?app_assoc; reflexivity).
  assert (Hab' : radrs_bytes (rset_payload_b r v) = P ++ to_byte v 4 ++ S)
    by (subst P S; unfold radrs_bytes, rset_payload_b;
        cbn [rtag ridx rtype rpa rpb rpc]; rewrite <- ?app_assoc; reflexivity).
  rewrite Hab, Hab'.
  replace 14 with (Zlength P) by lia.
  replace (Zlength P + 4) with (Zlength P + Zlength M)
    by (subst M; rewrite to_byte_Zlength; lia).
  replace 22 with (Zlength P + Zlength M + Zlength S)
    by (subst M S; rewrite ?Zlength_app, ?to_byte_Zlength, ?Zlength_nil; lia).
  apply sublist_splice_mid; subst M; rewrite !to_byte_Zlength; lia.
Qed.

Lemma shrincs_adrs_put32_hash : forall r v,
  sublist 0 18 (radrs_bytes r) ++ to_byte v 4 ++ sublist (18 + 4) 22 (radrs_bytes r)
  = radrs_bytes (rset_payload_c r v).
Proof.
  intros r v.
  pose (P := to_byte (rtag r) 1 ++ to_byte (ridx r) 8 ++ to_byte (rtype r) 1
             ++ to_byte (rpa r) 4 ++ to_byte (rpb r) 4).
  pose (M := to_byte (rpc r) 4).
  pose (S := @nil byte).
  assert (HP : Zlength P = 18)
    by (subst P; rewrite ?Zlength_app, ?to_byte_Zlength; reflexivity).
  assert (Hab : radrs_bytes r = P ++ M ++ S)
    by (subst P M S; unfold radrs_bytes; rewrite ?app_nil_r, <- ?app_assoc; reflexivity).
  assert (Hab' : radrs_bytes (rset_payload_c r v) = P ++ to_byte v 4 ++ S)
    by (subst P S; unfold radrs_bytes, rset_payload_c;
        cbn [rtag ridx rtype rpa rpb rpc]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity).
  rewrite Hab, Hab'.
  replace 18 with (Zlength P) by lia.
  replace (Zlength P + 4) with (Zlength P + Zlength M)
    by (subst M; rewrite to_byte_Zlength; lia).
  replace 22 with (Zlength P + Zlength M + Zlength S)
    by (subst M S; rewrite ?Zlength_app, ?to_byte_Zlength, ?Zlength_nil; lia).
  apply sublist_splice_mid; subst M; rewrite !to_byte_Zlength; lia.
Qed.

(** The direct type-byte store [addr[9] = v]: index 9 of [radrs_bytes] is
    the single type byte, so [upd_Znth 9] with [Byte.repr (v mod 256)] (the
    value shape [forward] produces) realises [rset_type r (v mod 256)].
    Shared by every body that types the ADRS. *)
Lemma upd_adrs_type : forall r v,
  upd_Znth 9 (block_to_vals (radrs_bytes r)) (Vubyte (Byte.repr (v mod 256)))
  = block_to_vals (radrs_bytes (rset_type r v)).
Proof.
  intros r v.
  unfold block_to_vals.
  change (Vubyte (Byte.repr (v mod 256)))
    with ((fun x : byte => Vubyte (Byte.repr x)) (byte_mod256 v)).
  rewrite upd_Znth_map.
  f_equal.
Qed.

(** The first 10 bytes of [adrs_bytes] (height + index + type) as read by
    [shrincs_wots_h_grind]. *)
Lemma sublist_adrs_bytes_10 : forall a : adrs,
  sublist 0 10 (adrs_bytes a) = firstn 10 (adrs_bytes a).
Proof.
  intros a. rewrite sublist_firstn. reflexivity.
Qed.

(* ================================================================= *)
(** ** [digits_to_vals] and [blocks_to_vals] length / split. *)

Lemma Zlength_digits_to_vals : forall ds,
  Zlength (digits_to_vals ds) = Zlength ds.
Proof.
  intros.
  unfold digits_to_vals.
  apply Zlength_map.
Qed.

(** The digit-value bridge: an in-range [digits_to_vals] cell whose digit
    fits a byte is the [Vint] of that digit.  Shared by the chain loops
    that load [digits[i]] as a chain length. *)
Lemma Znth_digits_to_vals : forall (ds : list nat) (i : Z),
  0 <= i < Zlength ds ->
  (nth (Z.to_nat i) ds 0%nat <= 255)%nat ->
  Znth i (digits_to_vals ds) = Vint (Int.repr (Z.of_nat (nth (Z.to_nat i) ds 0%nat))).
Proof.
  intros ds i Hi Hb.
  unfold digits_to_vals.
  rewrite Znth_map by assumption.
  rewrite <- (nth_Znth i ds) by assumption.
  unfold Vubyte.
  do 2 f_equal.
  apply Byte.unsigned_repr.
  rep_lia.
Qed.

(** [blocks_to_vals] distributes over list concatenation. *)
Lemma blocks_to_vals_app : forall l1 l2,
  blocks_to_vals (l1 ++ l2) = blocks_to_vals l1 ++ blocks_to_vals l2.
Proof.
  intros.
  unfold blocks_to_vals.
  rewrite concat_app, map_app.
  reflexivity.
Qed.

(** [skipn i l] with [i] in range exposes its head [nth i l d]. *)
Lemma skipn_cons_nth : forall {A} (l : list A) i (d : A),
  (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
  induction l as [|x xs IH]; intros i d Hi.
  - simpl in Hi. lia.
  - destruct i as [|i'].
    + reflexivity.
    + simpl. apply IH. simpl in Hi. lia.
Qed.

(** Peel the head block [nth i bs d] off [blocks_to_vals (skipn i bs)]:
    the flattened tail from index [i] is that block's bytes followed by the
    flattening of the remaining blocks. *)
Lemma blocks_to_vals_skipn_hd : forall (bs : list block) i (d : block),
  (i < length bs)%nat ->
  blocks_to_vals (skipn i bs)
  = block_to_vals (nth i bs d) ++ blocks_to_vals (skipn (S i) bs).
Proof.
  intros bs i d Hi.
  rewrite (skipn_cons_nth bs i d Hi) at 1.
  change (nth i bs d :: skipn (S i) bs)
    with ([nth i bs d] ++ skipn (S i) bs).
  rewrite blocks_to_vals_app.
  f_equal.
  unfold blocks_to_vals, block_to_vals. simpl concat. rewrite app_nil_r.
  reflexivity.
Qed.

(** [nth k bs default] is fixed-length whenever [bs] is. *)
Lemma nth_block_Zlength_default : forall (bs : list block) (k : nat),
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (nth k bs default) = n_bytes.
Proof.
  intros bs k HF.
  destruct (Nat.lt_ge_cases k (length bs)) as [Hlt|Hge].
  - rewrite Forall_forall in HF.
    apply HF, nth_In, Hlt.
  - rewrite nth_overflow by exact Hge.
    reflexivity.
Qed.

(** [blocks_to_vals] of a [seq]-indexed map peels its last element. *)
Lemma blocks_to_vals_seq_S : forall (f : nat -> block) (i : nat),
  blocks_to_vals (map f (seq 0 (S i))) =
  blocks_to_vals (map f (seq 0 i)) ++ block_to_vals (f i).
Proof.
  intros. rewrite seq_S, map_app.
  unfold blocks_to_vals, block_to_vals.
  rewrite concat_app, map_app.
  simpl concat.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma Zlength_blocks_to_vals_fixed : forall (bs : list block),
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (blocks_to_vals bs) = n_bytes * Z.of_nat (length bs).
Proof.
  intros bs H.
  unfold blocks_to_vals.
  rewrite Zlength_map.
  apply Zlength_concat_fixed, H.
Qed.

(** The FILLED-prefix length: [k] mapped fixed-width blocks flatten to
    [16 * k] vals.  Shared by the chain-loop invariants (pkgen / sign /
    from_sig), whose FILLED prefix is [blocks_to_vals (map f (seq 0 k))]. *)
Lemma Zlength_blocks_to_vals_map_seq : forall (f : nat -> block) (k : nat),
  (forall j : nat, Zlength (f j) = n_bytes) ->
  Zlength (blocks_to_vals (map f (seq 0 k))) = 16 * Z.of_nat k.
Proof.
  intros f k Hf.
  rewrite Zlength_blocks_to_vals_fixed
    by (apply Forall_map, Forall_forall; intros j _; apply Hf).
  rewrite length_map, length_seq.
  change n_bytes with 16.
  lia.
Qed.
