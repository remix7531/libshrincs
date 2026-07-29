(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Model.theory.shrincs: derived views of [Model.shrincs].

    [Model.shrincs] is THE model of record -- the transcription of the
    normative Python spec, definitions only (see model/PORTING.md).
    This file is not a second model.  Everything here is a view ABOUT
    that one: a decomposition of a spec function into named pieces, a
    normal form for the 22-byte ADRS, or a bridge to the dependent
    [Model.address.adrs] the SSProve tweak space is built from.  Every
    decomposition comes with a REASSEMBLY lemma proving it rebuilds the
    spec function it decomposes, so nothing here can silently drift
    from the model of record.

    Why the decompositions exist at all: the spec inlines its loops
    (one [fold_left] over a [range] per function), but the games <->
    model correspondence is elementwise -- per chain, per tree node --
    so the proofs need a per-chain view.  [chain_tips] / [sign_chains]
    / [complete_ends] are that view; [wots_c_pubkey_gen_tips] and
    friends are the reassembly lemmas that tie them back down.

    Layer order (each section uses only the ones above it):

    1. list plumbing for [range] and the spec's [fold_left] shape;
    2. the fold <-> map pair -- the one piece of machinery every
       elementwise proof in the bridges routes through;
    3. [mk_adrs], the 22-byte ADRS normal form, and its field updates;
    4. [Model.address.adrs_bytes] as an [mk_adrs] (the dependent
       address type, serialized);
    5. WOTS+C decomposed: per-chain views of the port's [wots_c_*]
       loops ([chain_tips] / [sign_chains] / [complete_ends], the
       grinding search), each with its REASSEMBLY lemma, plus the
       facts the two refinement proofs consume (the digit vector's
       shape and range, the linear search's four directions, and the
       widths of everything).

    Stdlib-only, like the rest of [Model]: no SSProve, no VST. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Import byte shrincs.
(** [Require] without [Import]: [Model.address] and [Model.shrincs]
    both define [SL_WOTS_TW_HASH] and friends (at [byte] and at [Z]
    respectively), so [address] is reached only through its qualified
    name here.  [bounded] is needed for one fact only -- [Vec]'s
    output width, which pins every tweaked hash at 16 bytes. *)
From Model Require address bounded.

Import ListNotations.
#[local] Open Scope Z_scope.

(* ================================================================= *)
(** ** 1. [range] and byte-string plumbing *)

Lemma length_range (a b : Z) : length (range a b) = Z.to_nat (b - a).
Proof.
  unfold range.
  rewrite length_map, length_seq.
  reflexivity.
Qed.

(** [nth] into a mapped [seq], without the [nth_indep] dance the
    stdlib's [map_nth] would otherwise force (its default argument has
    to be literally [f d]). *)
Lemma nth_map_seq {A : Type} (f : nat -> A) (n st j : nat) (d : A) :
  (j < n)%nat -> nth j (map f (seq st n)) d = f (st + j)%nat.
Proof.
  revert st j; induction n as [|n IH]; intros st j Hj; [lia|].
  destruct j as [|j]; cbn.
  - f_equal. lia.
  - rewrite IH by lia. f_equal. lia.
Qed.

Lemma in_range (a b x : Z) : In x (range a b) -> a <= x < b.
Proof.
  unfold range. intros H.
  apply in_map_iff in H.
  destruct H as [k [<- Hk]].
  apply in_seq in Hk.
  lia.
Qed.

(** [range 0 n] peeled at the FRONT: the head is index 0 and the tail
    re-indexes by one -- which is how an index into [x] becomes an index
    into [tl x]. *)
Lemma range0_cons (n : nat) :
  range 0 (Z.of_nat (S n)) = 0 :: map (fun i => i + 1) (range 0 (Z.of_nat n)).
Proof.
  unfold range.
  rewrite !Z.sub_0_r, !Nat2Z.id.
  cbn [seq map].
  f_equal.
  rewrite <- seq_shift, !map_map.
  apply map_ext. intros a. lia.
Qed.

(** [range 0 n] peeled at the BACK. *)
Lemma range0_succ (n : nat) :
  range 0 (Z.of_nat (S n)) = range 0 (Z.of_nat n) ++ [Z.of_nat n].
Proof.
  unfold range.
  rewrite !Z.sub_0_r, !Nat2Z.id, seq_S, map_app.
  cbn [map Nat.add].
  reflexivity.
Qed.

Lemma range_nil (a : Z) : range a a = [].
Proof. unfold range. rewrite Z.sub_diag. reflexivity. Qed.

(** [range] from 0 IS the [nat] [seq] the VST loop invariants iterate
    over, transported.  This is the one bridge between the port's [Z]
    index world and a [seq 0 k] the C-refinement counts with. *)
Lemma range0_map_of_nat (k : nat) : range 0 (Z.of_nat k) = map Z.of_nat (seq 0 k).
Proof.
  unfold range.
  rewrite Z.sub_0_r, Nat2Z.id.
  apply map_ext. intros a. lia.
Qed.

Lemma flat_map_ext_in {A B : Type} (f g : A -> list B) (l : list A) :
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; cbn; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), (IH (fun b Hb => H b (or_intror Hb))).
  reflexivity.
Qed.

Lemma flat_map_map {A B C : Type} (f : B -> list C) (g : A -> B) (l : list A) :
  flat_map f (map g l) = flat_map (fun a => f (g a)) l.
Proof. induction l as [|a l IH]; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

(** Reading past a prepended byte. *)
Lemma index_cons (c : byte) (x : bytes) (i : Z) :
  0 <= i -> index (c :: x) (i + 1) = index x i.
Proof.
  intros Hi. unfold index. f_equal.
  rewrite Z2Nat.inj_add by lia.
  rewrite Nat.add_1_r. reflexivity.
Qed.

Lemma nth_range (a b : Z) (j : nat) (d : Z) :
  (j < Z.to_nat (b - a))%nat -> nth j (range a b) d = a + Z.of_nat j.
Proof.
  intros Hj.
  unfold range.
  rewrite (nth_map_seq _ _ 0%nat j d Hj).
  reflexivity.
Qed.

Lemma length_to_bytes_loop (n : nat) (x : Z) : length (to_bytes_loop n x) = n.
Proof.
  revert x; induction n as [|n IH]; intros x; cbn.
  - reflexivity.
  - rewrite length_app, IH. cbn. lia.
Qed.

Lemma length_to_bytes (x n : Z) : length (to_bytes x n) = Z.to_nat n.
Proof. unfold to_bytes. apply length_to_bytes_loop. Qed.

Lemma to_bytes_1 (x : Z) : to_bytes x 1 = [byte_mod256 x].
Proof. reflexivity. Qed.

(** [byte_mod256] is the [Z] truncation its name claims.  ([byte.v]'s
    [byte_mod256_small] covers only the already-in-range case, which is
    not enough to read a multi-byte [to_bytes] field back.) *)
Lemma byte_val_mod256 (x : Z) : byte_val (byte_mod256 x) = x mod 256.
Proof.
  unfold byte_val, byte_mod256.
  rewrite machine.Byte.unsigned_repr_eq, byte_modulus.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** 2. The spec's loop shape, as a [map]

    Every loop in [Model.shrincs] is
    [fold_left (fun '(acc, s) i => (acc ++ [f i s], g i s)) (range ..) ([], s0)]
    -- an appending value accumulator alongside a threaded [ADRS].
    That shape has no usable [nth] lemma as it stands, which is exactly
    what an elementwise bridge proof needs.

    The way out is that in every one of the spec's loops the per-step
    value does NOT depend on the threaded state: the step re-derives
    every [ADRS] field it hashes before hashing it (the same fact the
    drop-at-boundary appendix in model/PORTING.md discharges).  Under
    that hypothesis the value accumulator collapses to a [map], which
    has [nth_map] / [length_map] for free.

    [P] is the invariant the caller needs to make [Hinv] provable -- in
    practice "[s] is 22 bytes long". *)

Lemma fold_app_map {A S : Type} (P : S -> Prop) (f : Z -> S -> A) (g : Z -> S -> S)
      (Hpres : forall j s, P s -> P (g j s))
      (Hinv : forall i j s, P s -> f i (g j s) = f i s) :
  forall (l : list Z) (s0 : S) (acc0 : list A), P s0 ->
  fst (fold_left (fun p i => (fst p ++ [f i (snd p)], g i (snd p))) l (acc0, s0))
  = acc0 ++ map (fun i => f i s0) l.
Proof.
  induction l as [|i l IH]; intros s0 acc0 Hs0; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite (IH (g i s0) (acc0 ++ [f i s0]) (Hpres i s0 Hs0)).
    rewrite <- app_assoc. cbn.
    f_equal. f_equal.
    apply map_ext_in. intros k _. apply Hinv. exact Hs0.
Qed.

(** The state component of the same fold is the plain state fold. *)
Lemma fold_app_snd {A S : Type} (f : Z -> S -> A) (g : Z -> S -> S) :
  forall (l : list Z) (s0 : S) (acc0 : list A),
  snd (fold_left (fun p i => (fst p ++ [f i (snd p)], g i (snd p))) l (acc0, s0))
  = fold_left (fun s i => g i s) l s0.
Proof.
  induction l as [|i l IH]; intros s0 acc0; cbn.
  - reflexivity.
  - apply IH.
Qed.

(** Any observation of the final state that each step leaves alone is
    the observation of the initial state.  This is what absorbs a
    loop's [ADRS] writes into the statements that follow the loop and
    overwrite them. *)
Lemma fold_state_invariant {S A : Type} (P : S -> Prop) (g : Z -> S -> S) (k : S -> A)
      (Hpres : forall j s, P s -> P (g j s))
      (Hinv : forall j s, P s -> k (g j s) = k s) :
  forall (l : list Z) (s0 : S), P s0 ->
  k (fold_left (fun s i => g i s) l s0) = k s0.
Proof.
  induction l as [|i l IH]; intros s0 Hs0; cbn.
  - reflexivity.
  - rewrite (IH (g i s0) (Hpres i s0 Hs0)).
    apply Hinv. exact Hs0.
Qed.

(** The [nth] / [length] pair the elementwise bridge proofs consume,
    stated at the shape [fold_app_map] produces. *)

Lemma length_map_range {A : Type} (f : Z -> A) (a b : Z) :
  length (map f (range a b)) = Z.to_nat (b - a).
Proof. rewrite length_map. apply length_range. Qed.

Lemma nth_map_range {A : Type} (f : Z -> A) (a b : Z) (j : nat) (d : A) :
  (j < Z.to_nat (b - a))%nat -> nth j (map f (range a b)) d = f (a + Z.of_nat j).
Proof.
  intros Hj.
  rewrite (nth_indep _ d (f 0)) by (rewrite length_map, length_range; exact Hj).
  rewrite map_nth, nth_range by exact Hj.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** 3. [mk_adrs]: the 22-byte ADRS in normal form

    Every ADRS the spec builds is a 22-byte string laid out as the six
    fields of the wire format: a 1-byte anchor tag, an 8-byte anchor
    index, a 1-byte type, and three 4-byte payload words.  Naming that
    layout turns every [set_index] / [set_slice] the spec performs into
    a FIELD UPDATE, which makes the absorption facts the loop lemmas
    above need ("writing a field twice is writing it once") free. *)

Definition mk_adrs (nh ni ty pa pb pc : Z) : bytes :=
  to_bytes nh 1 ++ to_bytes ni 8 ++ to_bytes ty 1
  ++ to_bytes pa 4 ++ to_bytes pb 4 ++ to_bytes pc 4.

Lemma length_mk_adrs (nh ni ty pa pb pc : Z) :
  length (mk_adrs nh ni ty pa pb pc) = 22%nat.
Proof.
  unfold mk_adrs.
  rewrite !length_app, !length_to_bytes.
  reflexivity.
Qed.

(** A fresh [bytearray(22)] is the all-zero address. *)
Lemma zeros_22_mk_adrs : zeros 22 = mk_adrs 0 0 0 0 0 0.
Proof. reflexivity. Qed.

(** The six field updates.  Each is the spec's own write, at the spec's
    own slice indices, shown to hit exactly one field. *)

Lemma set_anchor_tag (nh ni ty pa pb pc v : Z) :
  set_index (mk_adrs nh ni ty pa pb pc) 0 v = mk_adrs v ni ty pa pb pc.
Proof. reflexivity. Qed.

Lemma set_anchor_idx (nh ni ty pa pb pc v : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 1 9 (to_bytes v 8) = mk_adrs nh v ty pa pb pc.
Proof. reflexivity. Qed.

Lemma set_type (nh ni ty pa pb pc v : Z) :
  set_index (mk_adrs nh ni ty pa pb pc) 9 v = mk_adrs nh ni v pa pb pc.
Proof. reflexivity. Qed.

Lemma set_payload_a (nh ni ty pa pb pc v : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 10 14 (to_bytes v 4) = mk_adrs nh ni ty v pb pc.
Proof. reflexivity. Qed.

Lemma set_payload_b (nh ni ty pa pb pc v : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 14 18 (to_bytes v 4) = mk_adrs nh ni ty pa v pc.
Proof. reflexivity. Qed.

Lemma set_payload_c (nh ni ty pa pb pc v : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 18 22 (to_bytes v 4) = mk_adrs nh ni ty pa pb v.
Proof. reflexivity. Qed.

(** The multi-field zeroing writes the spec uses. *)

Lemma zero_payload_a (nh ni ty pa pb pc : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 10 14 (zeros 4) = mk_adrs nh ni ty 0 pb pc.
Proof. reflexivity. Qed.

Lemma zero_payload_c (nh ni ty pa pb pc : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 18 22 (zeros 4) = mk_adrs nh ni ty pa pb 0.
Proof. reflexivity. Qed.

Lemma zero_payload_bc (nh ni ty pa pb pc : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 14 22 (zeros 8) = mk_adrs nh ni ty pa 0 0.
Proof. reflexivity. Qed.

Lemma zero_payload_abc (nh ni ty pa pb pc : Z) :
  set_slice (mk_adrs nh ni ty pa pb pc) 10 22 (zeros 12) = mk_adrs nh ni ty 0 0 0.
Proof. reflexivity. Qed.

(** [H_grind] hashes only the first 10 bytes -- the anchor and the
    type, none of the payload. *)
Lemma slice_mk_adrs_10 (nh ni ty pa pb pc : Z) :
  slice (mk_adrs nh ni ty pa pb pc) 0 10
  = to_bytes nh 1 ++ to_bytes ni 8 ++ to_bytes ty 1.
Proof. reflexivity. Qed.

(** Reading the anchor tag back, as [fxmss_pubkey_from_sig]'s
    [ADRS[0] += 1] does.  (In range; the spec's heights are bytes.) *)
Lemma index_anchor_tag (nh ni ty pa pb pc : Z) :
  (0 <= nh < 256)%Z -> index (mk_adrs nh ni ty pa pb pc) 0 = nh.
Proof.
  intros H.
  unfold index, mk_adrs.
  rewrite to_bytes_1.
  change (Z.to_nat 0) with 0%nat.
  cbn [app nth].
  rewrite (byte_mod256_small nh H).
  apply byte_val_of.
Qed.

(* ================================================================= *)
(** ** 4. The dependent address, serialized

    [Model.address.adrs] is the SSProve tweak space's carrier: the
    games index their hash-game tweaks by [#|adrs|], which needs a
    FINITE type, so the dependent union stays.  [adrs_bytes] is the
    bridge to this file's byte-level world, and it is an [mk_adrs] of
    the address's own [Z] projections -- definitionally, once
    [Model.address.to_byte] and [Model.shrincs.to_bytes] are seen to be
    the same recursion. *)

Lemma to_byte_to_bytes (x : Z) (y : nat) : address.to_byte x y = to_bytes x (Z.of_nat y).
Proof.
  unfold to_bytes.
  rewrite Nat2Z.id.
  revert x; induction y as [|y IH]; intros x; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma adrs_bytes_mk_adrs {cc pb_ : nat} (a : address.adrs cc pb_) :
  address.adrs_bytes a
  = mk_adrs (address.adrs_anchor_tag_z a) (address.adrs_anchor_idx_z a)
            (address.adrs_type a)
            (address.payload_a_z a) (address.payload_b_z a) (address.payload_c_z a).
Proof.
  unfold address.adrs_bytes, mk_adrs.
  rewrite !to_byte_to_bytes.
  reflexivity.
Qed.


(* ================================================================= *)
(** ** 5. WOTS+C, decomposed

    The port states each WOTS+C algorithm the way shrincs.py does: one
    [fold_left] over [range 0 WOTS_C_CHAIN_COUNT] with the output array
    and the mutated [ADRS] riding the accumulator.  Every proof ABOUT
    WOTS+C is elementwise (per chain), so this section names the
    per-chain pieces -- [chain_tips], [sign_chains], [complete_ends],
    and the grinding search -- and proves, at each of the port's three
    top-level functions, that the pieces REASSEMBLE into it.

    Everything here is stated at an ADRS in [mk_adrs] normal form,
    anchored at [(nh, ni)]: that is what the spec's callers hand in
    (a 22-byte wire address), and it is what makes the loops' [ADRS]
    writes collapse to field updates. *)

(** *** 5.1 The four WOTS+C addresses, at the anchor [(nh, ni)]. *)

Definition wc_grind_adrs (nh ni : Z) : bytes :=
  mk_adrs nh ni SF_WOTS_C_GRIND 0 0 0.

Definition wc_prf_adrs (nh ni i : Z) : bytes :=
  mk_adrs nh ni SF_WOTS_C_PRF 0 i 0.

Definition wc_hash_adrs (nh ni i pos : Z) : bytes :=
  mk_adrs nh ni SF_WOTS_C_HASH 0 i pos.

Definition wc_pk_adrs (nh ni : Z) : bytes :=
  mk_adrs nh ni SF_WOTS_C_PK 0 0 0.

(** *** 5.1b The dependent address's smart constructors, serialized.

    [Model.address]'s four WOTS+C constructors rebuild a typed sibling
    from an anchor carrier; serialized, each IS the corresponding
    address above, at the carrier's own anchor.  This is the dictionary
    between the SSProve/VST world (which indexes tweaks by a FINITE
    address type, so the dependent union stays) and this file's
    byte-level one.  Parametric in the address row, so the WOTS+C
    instantiation is the caller's business. *)

Lemma adrs_bytes_grind {cc pb : nat} (a : address.adrs cc pb) :
  address.adrs_bytes (address.shrincs_wots_grind_adrs a)
  = wc_grind_adrs (address.adrs_anchor_tag_z a) (address.adrs_anchor_idx_z a).
Proof. rewrite adrs_bytes_mk_adrs. destruct a; reflexivity. Qed.

Lemma adrs_bytes_prf {cc pb : nat} (a : address.adrs cc pb)
      (ci : fin.fin (Z.of_nat cc)) :
  address.adrs_bytes (address.shrincs_wots_prf_adrs a ci)
  = wc_prf_adrs (address.adrs_anchor_tag_z a) (address.adrs_anchor_idx_z a)
      (fin.fin_val ci).
Proof. rewrite adrs_bytes_mk_adrs. destruct a; reflexivity. Qed.

Lemma adrs_bytes_pk {cc pb : nat} (a : address.adrs cc pb) :
  address.adrs_bytes (address.shrincs_wots_pk_adrs a)
  = wc_pk_adrs (address.adrs_anchor_tag_z a) (address.adrs_anchor_idx_z a).
Proof. rewrite adrs_bytes_mk_adrs. destruct a; reflexivity. Qed.

Lemma adrs_bytes_hash_pos {cc pb : nat} (a : address.adrs cc pb)
      (hp : (0 < pb)%nat)
      (ci : fin.fin (Z.of_nat cc)) (cp : fin.fin (Z.of_nat pb)) :
  address.adrs_bytes
    (address.set_hash_pos (address.shrincs_wots_hash_adrs hp a ci) cp)
  = wc_hash_adrs (address.adrs_anchor_tag_z a) (address.adrs_anchor_idx_z a)
      (fin.fin_val ci) (fin.fin_val cp).
Proof. rewrite adrs_bytes_mk_adrs. destruct a; reflexivity. Qed.

(** The hash address before the chain writes any position: position 0. *)
Lemma adrs_bytes_hash {cc pb : nat} (a : address.adrs cc pb)
      (hp : (0 < pb)%nat) (ci : fin.fin (Z.of_nat cc)) :
  address.adrs_bytes (address.shrincs_wots_hash_adrs hp a ci)
  = wc_hash_adrs (address.adrs_anchor_tag_z a) (address.adrs_anchor_idx_z a)
      (fin.fin_val ci) 0.
Proof. rewrite adrs_bytes_mk_adrs. destruct a; reflexivity. Qed.

(** [H_grind] hashes only [ADRS[0:10]] -- the anchor and the type -- so
    the port's in-place [ADRS[9] = SF_WOTS_C_GRIND] (which leaves the
    caller's payload words alone) hashes as [wc_grind_adrs]. *)
Lemma H_grind_grind_adrs (pk_seed M : bytes) (nh ni pa pb pc counter : Z) :
  H_grind pk_seed (mk_adrs nh ni SF_WOTS_C_GRIND pa pb pc) M counter
  = H_grind pk_seed (wc_grind_adrs nh ni) M counter.
Proof.
  unfold H_grind, wc_grind_adrs.
  rewrite !slice_mk_adrs_10.
  reflexivity.
Qed.

(** *** 5.2 The chain, as a fold over its own positions.

    [wots_chain_iter] threads the ADRS through its loop only to write
    the position word before each [F]; in normal form that write is a
    field update, so the chain is a plain [fold_left] over the
    positions the spec visits. *)

Definition wc_chain (pk_seed : bytes) (nh ni i : Z) (node : bytes)
                    (start steps : Z) : bytes :=
  fold_left (fun node j => F pk_seed (wc_hash_adrs nh ni i j) node)
            (range start (start + steps)) node.

Lemma range_succ (a : Z) (n : nat) :
  range a (a + Z.of_nat (S n)) = range a (a + Z.of_nat n) ++ [a + Z.of_nat n].
Proof.
  unfold range.
  replace (a + Z.of_nat (S n) - a) with (Z.of_nat (S n)) by lia.
  replace (a + Z.of_nat n - a) with (Z.of_nat n) by lia.
  rewrite !Nat2Z.id, seq_S, map_app.
  cbn [map Nat.add].
  reflexivity.
Qed.

Lemma wc_chain_succ (pk_seed : bytes) (nh ni i : Z) (node : bytes)
      (start : Z) (n : nat) :
  wc_chain pk_seed nh ni i node start (Z.of_nat (S n))
  = F pk_seed (wc_hash_adrs nh ni i (start + Z.of_nat n))
      (wc_chain pk_seed nh ni i node start (Z.of_nat n)).
Proof.
  unfold wc_chain.
  rewrite range_succ, fold_left_app.
  reflexivity.
Qed.

Lemma wots_chain_iter_mk (pk_seed : bytes) (nh ni i : Z) :
  forall (l : list Z) (node : bytes) (pos : Z),
  fst (fold_left
         (fun '(node, ADRS) j =>
            let ADRS := set_slice ADRS 18 22 (to_bytes j 4) in
            let node := F pk_seed ADRS node in
            (node, ADRS))
         l (node, wc_hash_adrs nh ni i pos))
  = fold_left (fun node j => F pk_seed (wc_hash_adrs nh ni i j) node) l node.
Proof.
  induction l as [|j l IH]; intros node pos; [reflexivity|].
  cbn [fold_left].
  unfold wc_hash_adrs at 1 2.
  rewrite set_payload_c.
  apply (IH _ j).
Qed.

(** The chain, reassembled: the port's [wots_chain_iter] at a
    hash-typed normal-form ADRS IS [wc_chain].  The incoming position
    word is irrelevant -- the loop overwrites it before every [F]. *)
Lemma wots_chain_iter_wc_chain (pk_seed : bytes) (nh ni i pos : Z)
      (node : bytes) (start steps : Z) :
  wots_chain_iter node start steps pk_seed (wc_hash_adrs nh ni i pos)
  = wc_chain pk_seed nh ni i node start steps.
Proof. apply wots_chain_iter_mk. Qed.

(** *** 5.3 The grinding search.

    The port's [wots_c_grind_to_constant_sum_loop] recomputes its digit
    vector at every counter; [digest_of] names that vector,
    [good_counter] its constant-sum test, and [find_from] /
    [find_counter] the search itself. *)

Definition digest_of (pk_seed : bytes) (nh ni : Z) (M : bytes) (counter : Z)
  : list Z :=
  base_2b (H_grind pk_seed (wc_grind_adrs nh ni) M counter)
          WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT.

Definition valid_digest (ds : list Z) : bool :=
  sum_list ds =? WOTS_C_CONSTANT_SUM.

Definition good_counter (pk_seed : bytes) (nh ni : Z) (M : bytes) (counter : Z)
  : bool :=
  valid_digest (digest_of pk_seed nh ni M counter).

Fixpoint find_from (pk_seed : bytes) (nh ni : Z) (M : bytes)
                   (fuel : nat) (c : Z) : option Z :=
  match fuel with
  | O   => None
  | S f => if good_counter pk_seed nh ni M c
           then Some c
           else find_from pk_seed nh ni M f (c + 1)
  end.

Definition find_counter (pk_seed : bytes) (nh ni : Z) (M : bytes) : option Z :=
  find_from pk_seed nh ni M (Z.to_nat (2 ^ 16)) 0.

(** REASSEMBLY: the port's grinding loop is [find_from], paired with
    the digit vector at the counter it returns. *)
Lemma wots_c_grind_loop_find_from (pk_seed M : bytes) (nh ni pa pb pc : Z) :
  forall (remaining : nat) (c : Z),
  wots_c_grind_to_constant_sum_loop remaining c pk_seed M
    (mk_adrs nh ni SF_WOTS_C_GRIND pa pb pc)
  = option_map (fun cc => (cc, digest_of pk_seed nh ni M cc))
               (find_from pk_seed nh ni M remaining c).
Proof.
  induction remaining as [|remaining IH]; intros c; [reflexivity|].
  cbn [wots_c_grind_to_constant_sum_loop find_from].
  unfold good_counter, valid_digest, digest_of.
  rewrite H_grind_grind_adrs.
  destruct (sum_list (base_2b (H_grind pk_seed (wc_grind_adrs nh ni) M c)
                              WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT)
            =? WOTS_C_CONSTANT_SUM); [reflexivity|].
  apply IH.
Qed.

(** REASSEMBLY: the port's grinding function is [find_counter]. *)
Lemma wots_c_grind_find_counter (pk_seed M : bytes) (nh ni ty pa pb pc : Z) :
  wots_c_grind_to_constant_sum pk_seed M (mk_adrs nh ni ty pa pb pc)
  = option_map (fun cc => (cc, digest_of pk_seed nh ni M cc))
               (find_counter pk_seed nh ni M).
Proof.
  unfold wots_c_grind_to_constant_sum, find_counter.
  rewrite set_type.
  apply wots_c_grind_loop_find_from.
Qed.

(** REASSEMBLY: the port's counter validation is [good_counter]. *)
Lemma wots_c_map_digest_good_counter (pk_seed M : bytes)
      (nh ni ty pa pb pc counter : Z) :
  wots_c_map_digest pk_seed M (mk_adrs nh ni ty pa pb pc) counter
  = if good_counter pk_seed nh ni M counter
    then Some (digest_of pk_seed nh ni M counter)
    else None.
Proof.
  unfold wots_c_map_digest, good_counter, valid_digest, digest_of.
  rewrite set_type, H_grind_grind_adrs.
  reflexivity.
Qed.

(** *** 5.4 The three per-chain views.

    [derive_sk] is the port's PRF-derived chain start; [chain_tips] /
    [sign_chains] / [complete_ends] are the [len] chains the three
    top-level functions build, each a [map] over the spec's own
    [range]. *)

Definition index_block (l : list bytes) (i : Z) : bytes := nth (Z.to_nat i) l [].

Definition derive_sk (sk_seed pk_seed : bytes) (nh ni i : Z) : bytes :=
  PRF pk_seed sk_seed (wc_prf_adrs nh ni i).

Definition chain_tips (sk_seed pk_seed : bytes) (nh ni : Z) : list bytes :=
  map (fun i => wc_chain pk_seed nh ni i (derive_sk sk_seed pk_seed nh ni i)
                  0 (2 ^ WOTS_C_CHAIN_BITS - 1))
      (range 0 WOTS_C_CHAIN_COUNT).

Definition sign_chains (M sk_seed pk_seed : bytes) (nh ni counter : Z)
  : list bytes :=
  let ds := digest_of pk_seed nh ni M counter in
  map (fun i => wc_chain pk_seed nh ni i (derive_sk sk_seed pk_seed nh ni i)
                  0 (index_int ds i))
      (range 0 WOTS_C_CHAIN_COUNT).

Definition complete_ends (M : bytes) (sig : list bytes) (counter : Z)
                         (pk_seed : bytes) (nh ni : Z) : list bytes :=
  let ds := digest_of pk_seed nh ni M counter in
  map (fun i => wc_chain pk_seed nh ni i (index_block sig i)
                  (index_int ds i) (2 ^ WOTS_C_CHAIN_BITS - 1 - index_int ds i))
      (range 0 WOTS_C_CHAIN_COUNT).

(** *** 5.5 The loop machinery.

    The port's three WOTS+C loops share one shape: an appending value
    accumulator alongside the mutated [ADRS].  [fold_pair_app] is
    section 2's [fold_app_map] / [fold_app_snd] pair, restated at the
    spec's own pattern-matching lambda so it applies to the port's
    loops without an eta step at every site. *)

Lemma fold_pair_eta {A S : Type} (f : Z -> S -> A) (g : Z -> S -> S) :
  forall (l : list Z) (p : list A * S),
  fold_left (fun '(acc, s) i => (acc ++ [f i s], g i s)) l p
  = fold_left (fun q i => (fst q ++ [f i (snd q)], g i (snd q))) l p.
Proof.
  induction l as [|i l IH]; intros [acc s]; cbn; [reflexivity|apply IH].
Qed.

Lemma fold_pair_app {A S : Type} (P : S -> Prop) (f : Z -> S -> A) (g : Z -> S -> S)
      (Hpres : forall j s, P s -> P (g j s))
      (Hinv : forall i j s, P s -> f i (g j s) = f i s) :
  forall (l : list Z) (s0 : S) (acc0 : list A), P s0 ->
  fold_left (fun '(acc, s) i => (acc ++ [f i s], g i s)) l (acc0, s0)
  = (acc0 ++ map (fun i => f i s0) l, fold_left (fun s i => g i s) l s0).
Proof.
  intros l s0 acc0 Hs0.
  rewrite fold_pair_eta.
  rewrite <- (fold_app_map P f g Hpres Hinv l s0 acc0 Hs0).
  rewrite <- (fold_app_snd f g l s0 acc0).
  apply surjective_pairing.
Qed.

(** The invariant every WOTS+C loop preserves: the anchor and the
    keypair word stay put; the type byte and the two chain/position
    words are the loop's own. *)
Definition wc_anchored (nh ni pa : Z) (s : bytes) : Prop :=
  exists ty pb pc, s = mk_adrs nh ni ty pa pb pc.

(** The port's per-step ADRS writes, named so the loops below read as
    [fold_left (fun '(acc, s) i => (acc ++ [f i s], g i s))]. *)

Definition wc_prf_write (i : Z) (ADRS : bytes) : bytes :=
  set_slice (set_slice (set_index ADRS 9 SF_WOTS_C_PRF) 14 18 (to_bytes i 4))
            18 22 (zeros 4).

Definition wc_hash_write (i : Z) (ADRS : bytes) : bytes :=
  set_index (wc_prf_write i ADRS) 9 SF_WOTS_C_HASH.

Definition wc_chainidx_write (i : Z) (ADRS : bytes) : bytes :=
  set_slice ADRS 14 18 (to_bytes i 4).

Lemma wc_prf_write_mk (nh ni ty pa pb pc i : Z) :
  wc_prf_write i (mk_adrs nh ni ty pa pb pc) = mk_adrs nh ni SF_WOTS_C_PRF pa i 0.
Proof. reflexivity. Qed.

Lemma wc_hash_write_mk (nh ni ty pa pb pc i : Z) :
  wc_hash_write i (mk_adrs nh ni ty pa pb pc) = mk_adrs nh ni SF_WOTS_C_HASH pa i 0.
Proof. reflexivity. Qed.

Lemma wc_chainidx_write_mk (nh ni ty pa pb pc i : Z) :
  wc_chainidx_write i (mk_adrs nh ni ty pa pb pc) = mk_adrs nh ni ty pa i pc.
Proof. reflexivity. Qed.

(** The post-loop write every WOTS+C function ends with: retype to
    SF_WOTS_C_PK and zero both chain words.  It sees only the anchor and
    the keypair word, so it absorbs whatever the loop left behind. *)
Definition wc_pk_write (ADRS : bytes) : bytes :=
  set_slice (set_index ADRS 9 SF_WOTS_C_PK) 14 22 (zeros 8).

Lemma wc_pk_write_fold (nh ni : Z) (g : Z -> bytes -> bytes)
      (Hpres : forall j s, wc_anchored nh ni 0 s -> wc_anchored nh ni 0 (g j s)) :
  forall (l : list Z) (s0 : bytes), wc_anchored nh ni 0 s0 ->
  wc_pk_write (fold_left (fun s i => g i s) l s0) = wc_pk_adrs nh ni.
Proof.
  assert (Hk : forall s, wc_anchored nh ni 0 s -> wc_pk_write s = wc_pk_adrs nh ni).
  { intros s [ty [pb [pc ->]]]. reflexivity. }
  assert (Hinv : forall j s, wc_anchored nh ni 0 s ->
                   wc_pk_write (g j s) = wc_pk_write s).
  { intros j s Hs. rewrite (Hk _ (Hpres j s Hs)), (Hk s Hs). reflexivity. }
  intros l s0 Hs0.
  rewrite (fold_state_invariant (wc_anchored nh ni 0) g wc_pk_write Hpres Hinv
             l s0 Hs0).
  exact (Hk s0 Hs0).
Qed.

(** *** 5.6 REASSEMBLY: the three top-level WOTS+C functions. *)

(** The public-key loop's per-chain value. *)
Definition wc_gen_val (sk_seed pk_seed : bytes) (i : Z) (ADRS : bytes) : bytes :=
  wots_chain_iter (PRF pk_seed sk_seed (wc_prf_write i ADRS))
                  0 (2 ^ WOTS_C_CHAIN_BITS - 1) pk_seed (wc_hash_write i ADRS).

Lemma wots_c_pubkey_gen_loop (sk_seed pk_seed ADRS : bytes) :
  wots_c_pubkey_gen sk_seed pk_seed ADRS
  = let '(wots_pk, ADRS') :=
      fold_left (fun '(wots_pk, s) i =>
                   (wots_pk ++ [wc_gen_val sk_seed pk_seed i s], wc_hash_write i s))
                (range 0 WOTS_C_CHAIN_COUNT)
                ([], set_slice ADRS 10 14 (zeros 4)) in
    T_sf pk_seed (wc_pk_write ADRS') (concat wots_pk).
Proof. reflexivity. Qed.

Lemma wots_c_pubkey_gen_tips (sk_seed pk_seed : bytes) (nh ni ty pa pb pc : Z) :
  wots_c_pubkey_gen sk_seed pk_seed (mk_adrs nh ni ty pa pb pc)
  = T_sf pk_seed (wc_pk_adrs nh ni) (concat (chain_tips sk_seed pk_seed nh ni)).
Proof.
  rewrite wots_c_pubkey_gen_loop, zero_payload_a.
  assert (Hpres : forall j s, wc_anchored nh ni 0 s ->
                    wc_anchored nh ni 0 (wc_hash_write j s)).
  { intros j s [ty' [pb' [pc' ->]]]. rewrite wc_hash_write_mk.
    exists SF_WOTS_C_HASH, j, 0. reflexivity. }
  assert (Hval : forall i s, wc_anchored nh ni 0 s ->
                   wc_gen_val sk_seed pk_seed i s
                   = wc_chain pk_seed nh ni i (derive_sk sk_seed pk_seed nh ni i)
                       0 (2 ^ WOTS_C_CHAIN_BITS - 1)).
  { intros i s [ty' [pb' [pc' ->]]].
    unfold wc_gen_val, derive_sk, wc_prf_adrs.
    rewrite wc_prf_write_mk, wc_hash_write_mk.
    apply (wots_chain_iter_wc_chain pk_seed nh ni i 0). }
  assert (Hs0 : wc_anchored nh ni 0 (mk_adrs nh ni ty 0 pb pc))
    by (exists ty, pb, pc; reflexivity).
  rewrite (fold_pair_app (wc_anchored nh ni 0) (wc_gen_val sk_seed pk_seed)
             wc_hash_write Hpres
             (fun i j s Hs => eq_trans (Hval i _ (Hpres j s Hs))
                                       (eq_sym (Hval i s Hs)))
             (range 0 WOTS_C_CHAIN_COUNT) _ [] Hs0).
  rewrite (wc_pk_write_fold nh ni wc_hash_write Hpres _ _ Hs0).
  cbn [app].
  unfold chain_tips.
  rewrite (map_ext_in _ _ _ (fun i _ => Hval i _ Hs0)).
  reflexivity.
Qed.

(** The signing loop's per-chain value: same as the public key's, at
    the digest's own step count. *)
Definition wc_sign_val (ds : list Z) (sk_seed pk_seed : bytes) (i : Z) (ADRS : bytes)
  : bytes :=
  wots_chain_iter (PRF pk_seed sk_seed (wc_prf_write i ADRS))
                  0 (index_int ds i) pk_seed (wc_hash_write i ADRS).

Lemma wots_c_sign_loop (M sk_seed pk_seed ADRS : bytes) :
  wots_c_sign M sk_seed pk_seed ADRS
  = match wots_c_grind_to_constant_sum pk_seed M ADRS with
    | None => zeros (2 + WOTS_C_CHAINS_SIZE)
    | Some (counter, ds) =>
        let '(signature, _) :=
          fold_left (fun '(signature, s) i =>
                       (signature ++ [wc_sign_val ds sk_seed pk_seed i s],
                        wc_hash_write i s))
                    (range 0 WOTS_C_CHAIN_COUNT)
                    ([], set_slice ADRS 10 14 (zeros 4)) in
        to_bytes counter 2 ++ concat signature
    end.
Proof. reflexivity. Qed.

Lemma wots_c_sign_chains (M sk_seed pk_seed : bytes) (nh ni ty pa pb pc : Z) :
  wots_c_sign M sk_seed pk_seed (mk_adrs nh ni ty pa pb pc)
  = match find_counter pk_seed nh ni M with
    | None => zeros (2 + WOTS_C_CHAINS_SIZE)
    | Some counter =>
        to_bytes counter 2
        ++ concat (sign_chains M sk_seed pk_seed nh ni counter)
    end.
Proof.
  rewrite wots_c_sign_loop, wots_c_grind_find_counter.
  destruct (find_counter pk_seed nh ni M) as [counter|]; [|reflexivity].
  cbn [option_map].
  rewrite zero_payload_a.
  assert (Hpres : forall j s, wc_anchored nh ni 0 s ->
                    wc_anchored nh ni 0 (wc_hash_write j s)).
  { intros j s [ty' [pb' [pc' ->]]]. rewrite wc_hash_write_mk.
    exists SF_WOTS_C_HASH, j, 0. reflexivity. }
  assert (Hval : forall i s, wc_anchored nh ni 0 s ->
                   wc_sign_val (digest_of pk_seed nh ni M counter) sk_seed pk_seed i s
                   = wc_chain pk_seed nh ni i (derive_sk sk_seed pk_seed nh ni i)
                       0 (index_int (digest_of pk_seed nh ni M counter) i)).
  { intros i s [ty' [pb' [pc' ->]]].
    unfold wc_sign_val, derive_sk, wc_prf_adrs.
    rewrite wc_prf_write_mk, wc_hash_write_mk.
    apply (wots_chain_iter_wc_chain pk_seed nh ni i 0). }
  assert (Hs0 : wc_anchored nh ni 0 (mk_adrs nh ni ty 0 pb pc))
    by (exists ty, pb, pc; reflexivity).
  rewrite (fold_pair_app (wc_anchored nh ni 0)
             (wc_sign_val (digest_of pk_seed nh ni M counter) sk_seed pk_seed)
             wc_hash_write Hpres
             (fun i j s Hs => eq_trans (Hval i _ (Hpres j s Hs))
                                       (eq_sym (Hval i s Hs)))
             (range 0 WOTS_C_CHAIN_COUNT) _ [] Hs0).
  cbn [app].
  unfold sign_chains.
  rewrite (map_ext_in _ _ _ (fun i _ => Hval i _ Hs0)).
  reflexivity.
Qed.

(** The verifier loop's per-chain value: the received chain value,
    completed from its digit to the top of the chain. *)
Definition wc_ver_val (signature : bytes) (ds : list Z) (pk_seed : bytes)
                      (i : Z) (ADRS : bytes) : bytes :=
  wots_chain_iter (slice signature (2 + i * 16) (2 + (i + 1) * 16))
                  (index_int ds i) (2 ^ WOTS_C_CHAIN_BITS - 1 - index_int ds i)
                  pk_seed (wc_chainidx_write i ADRS).

Lemma wots_c_pubkey_from_sig_loop (signature M pk_seed ADRS : bytes) :
  wots_c_pubkey_from_sig signature M pk_seed ADRS
  = match wots_c_map_digest pk_seed M ADRS (from_bytes (slice signature 0 2)) with
    | None => None
    | Some ds =>
        let '(wots_pk, ADRS') :=
          fold_left (fun '(wots_pk, s) i =>
                       (wots_pk ++ [wc_ver_val signature ds pk_seed i s],
                        wc_chainidx_write i s))
                    (range 0 WOTS_C_CHAIN_COUNT)
                    ([], set_slice (set_index ADRS 9 SF_WOTS_C_HASH) 10 14 (zeros 4)) in
        Some (T_sf pk_seed (wc_pk_write ADRS') (concat wots_pk))
    end.
Proof. reflexivity. Qed.

(** The verifier's flat signature, as the spec lays it out: a two-byte
    counter followed by [WOTS_C_CHAIN_COUNT] 16-byte chain values.  This
    is what turns the port's slice arithmetic back into an index. *)
Lemma slice_uniform_blocks (k : nat) (l : list bytes) :
  (forall b, In b l -> length b = k) ->
  forall (i : nat), (i < length l)%nat ->
  firstn k (skipn (k * i) (List.concat l)) = nth i l [].
Proof.
  induction l as [|b l IH]; intros Hk i Hi; cbn in Hi; [lia|].
  assert (Hb : length b = k) by (apply Hk; left; reflexivity).
  assert (Hl : forall c, In c l -> length c = k)
    by (intros c Hc; apply Hk; right; exact Hc).
  destruct i as [|i]; cbn [List.concat nth].
  - rewrite Nat.mul_0_r. cbn [skipn].
    rewrite firstn_app, Hb, Nat.sub_diag.
    cbn [firstn]. rewrite app_nil_r.
    apply firstn_all2. lia.
  - rewrite Nat.mul_succ_r, <- skipn_skipn.
    rewrite skipn_app, Hb, Nat.sub_diag.
    rewrite (skipn_all2 (n := k) b) by lia.
    cbn [app skipn].
    apply IH; [exact Hl | lia].
Qed.

(** The counter field is the flat signature's first two bytes. *)
Lemma slice_counter_prefix (counter : Z) (rest : bytes) :
  slice (to_bytes counter 2 ++ rest) 0 2 = to_bytes counter 2.
Proof.
  unfold slice, to_bytes.
  cbn [Z.to_nat Pos.to_nat Pos.iter_op to_bytes_loop app skipn firstn].
  reflexivity.
Qed.

Lemma slice_sig_block (counter : Z) (sig : list bytes) (i : Z) :
  (forall b, In b sig -> length b = 16%nat) ->
  0 <= i -> (Z.to_nat i < length sig)%nat ->
  slice (to_bytes counter 2 ++ concat sig) (2 + i * 16) (2 + (i + 1) * 16)
  = index_block sig i.
Proof.
  intros Hk Hi0 Hi.
  unfold slice, index_block, concat.
  replace (2 + (i + 1) * 16 - (2 + i * 16)) with 16 by lia.
  replace (Z.to_nat (2 + i * 16)) with (16 * Z.to_nat i + 2)%nat by lia.
  change (Z.to_nat 16) with 16%nat.
  rewrite <- skipn_skipn.
  rewrite skipn_app, length_to_bytes.
  change (Z.to_nat 2) with 2%nat.
  rewrite (skipn_all2 (n := 2%nat) (to_bytes counter 2))
    by (rewrite length_to_bytes; cbn; lia).
  replace (2 - 2)%nat with 0%nat by lia.
  cbn [app skipn].
  apply (slice_uniform_blocks 16%nat sig Hk _ Hi).
Qed.

(** [from_bytes] inverts [to_bytes] on the two-byte counter field. *)
Lemma from_bytes_to_bytes_2 (c : Z) : 0 <= c < 2 ^ 16 -> from_bytes (to_bytes c 2) = c.
Proof.
  intros Hc.
  change (2 ^ 16) with 65536 in Hc.
  unfold from_bytes, to_bytes.
  change (Z.to_nat 2) with 2%nat.
  cbn [to_bytes_loop app fold_left].
  rewrite !byte_val_mod256.
  rewrite (Z.mod_small (c / 256) 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.mul_0_l, Z.add_0_l, Z.mul_comm.
  symmetry; apply Z.div_mod; lia.
Qed.

Lemma wots_c_pubkey_from_sig_ends (M : bytes) (sig : list bytes) (counter : Z)
      (pk_seed : bytes) (nh ni ty pa pb pc : Z) :
  0 <= counter < 2 ^ 16 ->
  length sig = Z.to_nat WOTS_C_CHAIN_COUNT ->
  (forall b, In b sig -> length b = 16%nat) ->
  wots_c_pubkey_from_sig (to_bytes counter 2 ++ concat sig) M pk_seed
    (mk_adrs nh ni ty pa pb pc)
  = if good_counter pk_seed nh ni M counter
    then Some (T_sf pk_seed (wc_pk_adrs nh ni)
                 (concat (complete_ends M sig counter pk_seed nh ni)))
    else None.
Proof.
  intros Hc Hlen Hk.
  rewrite wots_c_pubkey_from_sig_loop.
  rewrite (slice_counter_prefix counter (concat sig)).
  rewrite (from_bytes_to_bytes_2 counter Hc).
  rewrite wots_c_map_digest_good_counter.
  destruct (good_counter pk_seed nh ni M counter) eqn:Hgc; [|reflexivity].
  rewrite set_type, zero_payload_a.
  assert (Hpres : forall j s, wc_anchored nh ni 0 s ->
                    wc_anchored nh ni 0 (wc_chainidx_write j s)).
  { intros j s [ty' [pb' [pc' ->]]]. rewrite wc_chainidx_write_mk.
    exists ty', j, pc'. reflexivity. }
  assert (Hs0 : wc_anchored nh ni 0 (mk_adrs nh ni SF_WOTS_C_HASH 0 pb pc))
    by (exists SF_WOTS_C_HASH, pb, pc; reflexivity).
  assert (Hinv : forall i j s, wc_anchored nh ni 0 s ->
                   wc_ver_val (to_bytes counter 2 ++ concat sig)
                     (digest_of pk_seed nh ni M counter) pk_seed i (wc_chainidx_write j s)
                   = wc_ver_val (to_bytes counter 2 ++ concat sig)
                       (digest_of pk_seed nh ni M counter) pk_seed i s).
  { intros i j s [ty' [pb' [pc' ->]]].
    unfold wc_ver_val.
    rewrite !wc_chainidx_write_mk. reflexivity. }
  rewrite (fold_pair_app (wc_anchored nh ni 0)
             (wc_ver_val (to_bytes counter 2 ++ concat sig)
                (digest_of pk_seed nh ni M counter) pk_seed)
             wc_chainidx_write Hpres Hinv
             (range 0 WOTS_C_CHAIN_COUNT) _ [] Hs0).
  rewrite (wc_pk_write_fold nh ni wc_chainidx_write Hpres _ _ Hs0).
  cbn [app].
  assert (Hstep : forall i, In i (range 0 WOTS_C_CHAIN_COUNT) ->
    wc_ver_val (to_bytes counter 2 ++ concat sig)
      (digest_of pk_seed nh ni M counter) pk_seed i
      (mk_adrs nh ni SF_WOTS_C_HASH 0 pb pc)
    = wc_chain pk_seed nh ni i (index_block sig i)
        (index_int (digest_of pk_seed nh ni M counter) i)
        (2 ^ WOTS_C_CHAIN_BITS - 1
         - index_int (digest_of pk_seed nh ni M counter) i)).
  { intros i Hi.
    assert (Hi0 := in_range _ _ _ Hi).
    unfold WOTS_C_CHAIN_COUNT in Hi0.
    unfold wc_ver_val.
    rewrite wc_chainidx_write_mk.
    rewrite (slice_sig_block counter sig i Hk (proj1 Hi0));
      [| rewrite Hlen; unfold WOTS_C_CHAIN_COUNT; lia].
    apply (wots_chain_iter_wc_chain pk_seed nh ni i pc). }
  unfold complete_ends.
  rewrite (map_ext_in _ _ _ Hstep).
  reflexivity.
Qed.

(** *** 5.7 The digit vector, spelled out.

    [base_2b] is a generic bit-packing loop; at [b = 4] it is
    2-periodic (one byte in, two digits out, high nibble first), so the
    whole [WOTS_C_CHAIN_COUNT]-digit vector is the byte-wise nibble
    split of the grinding hash's first 16 bytes.  This is what makes
    the digits comparable to a games-layer digit vector at all. *)

#[local] Arguments index : simpl never.

(** Written with the spec's own pattern-matching lambda, so it is
    DEFINITIONALLY the loop body [Model.shrincs.base_2b] inlines. *)
Definition base_2b_step (x : bytes) (b : Z)
  : list Z * Z * Z * Z -> Z -> list Z * Z * Z * Z :=
  fun '(baseb, j, acc, bits_filled) i =>
    let '(j, acc, bits_filled) :=
      base_2b_fill (Z.to_nat ((b - bits_filled + 7) / 8)) x b j acc bits_filled in
    let bits_filled := bits_filled - b in
    (baseb ++ [Z.shiftr acc bits_filled], j, acc mod 2 ^ bits_filled, bits_filled).

Lemma base_2b_fold (x : bytes) (b outlen : Z) :
  base_2b x b outlen
  = let '(baseb, _, _, _) :=
      fold_left (base_2b_step x b) (range 0 outlen) ([], 0, 0, 0) in
    baseb.
Proof. reflexivity. Qed.

(** The nibble pair of the byte at index [j]. *)
Definition nib (x : bytes) (j : Z) : list Z :=
  [Z.shiftr (index x j) 4; index x j mod 2 ^ 4].

(** One byte per two loop iterations: at [bits_filled = 0] the loop
    reads a byte and emits its high nibble; at [bits_filled = 4] it
    reads nothing and emits the low one, returning to [bits_filled = 0]. *)
Lemma base_2b_step_pair (x : bytes) (B : list Z) (J i1 i2 : Z) :
  base_2b_step x 4 (base_2b_step x 4 (B, J, 0, 0) i1) i2
  = (B ++ nib x J, J + 1, 0, 0).
Proof.
  unfold base_2b_step, nib.
  simpl.
  rewrite Z.shiftr_0_r, Z.mod_1_r, <- app_assoc.
  reflexivity.
Qed.

Lemma base_2b_4_fold (x : bytes) (n : nat) :
  fold_left (base_2b_step x 4) (range 0 (Z.of_nat (2 * n))) ([], 0, 0, 0)
  = (flat_map (nib x) (range 0 (Z.of_nat n)), Z.of_nat n, 0, 0).
Proof.
  induction n as [|n IH]; [reflexivity|].
  replace (2 * S n)%nat with (S (S (2 * n))) by lia.
  rewrite (range0_succ (S (2 * n))), (range0_succ (2 * n)), <- app_assoc.
  rewrite fold_left_app, IH.
  cbn [app fold_left].
  rewrite base_2b_step_pair, range0_succ, flat_map_app.
  cbn [flat_map].
  rewrite app_nil_r.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
  reflexivity.
Qed.

Lemma base_2b_4 (x : bytes) (n : nat) :
  base_2b x 4 (Z.of_nat (2 * n)) = flat_map (nib x) (range 0 (Z.of_nat n)).
Proof. rewrite base_2b_fold, base_2b_4_fold. reflexivity. Qed.

(** [Model.sha256.SHA256]'s output width, unwrapped: what pins every
    tweaked hash of the port at 16 bytes. *)
Lemma length_sha256 (input : bytes) : length (sha256 input) = 32%nat.
Proof.
  unfold sha256. apply Nat2Z.inj.
  rewrite bounded.Vec.length_to_list. reflexivity.
Qed.

Lemma length_H_grind (pk_seed ADRS M : bytes) (counter : Z) :
  length (H_grind pk_seed ADRS M counter) = 16%nat.
Proof.
  unfold H_grind, slice.
  rewrite length_firstn, length_skipn, length_sha256.
  reflexivity.
Qed.

Lemma length_T_sf (pk_seed ADRS M : bytes) : length (T_sf pk_seed ADRS M) = 16%nat.
Proof.
  unfold T_sf, slice.
  rewrite length_firstn, length_skipn, length_sha256.
  reflexivity.
Qed.

Lemma length_F (pk_seed ADRS M : bytes) : length (F pk_seed ADRS M) = 16%nat.
Proof.
  unfold F, slice.
  rewrite length_firstn, length_skipn, length_sha256.
  reflexivity.
Qed.

Lemma length_PRF (pk_seed sk_seed ADRS : bytes) :
  length (PRF pk_seed sk_seed ADRS) = 16%nat.
Proof.
  unfold PRF, slice.
  rewrite length_firstn, length_skipn, length_sha256.
  reflexivity.
Qed.

Lemma digest_of_nib (pk_seed : bytes) (nh ni : Z) (M : bytes) (counter : Z) :
  digest_of pk_seed nh ni M counter
  = flat_map (nib (H_grind pk_seed (wc_grind_adrs nh ni) M counter)) (range 0 16).
Proof.
  unfold digest_of, WOTS_C_CHAIN_BITS, WOTS_C_CHAIN_COUNT.
  change 32 with (Z.of_nat (2 * 16)).
  rewrite base_2b_4.
  reflexivity.
Qed.

(* ================================================================= *)
(** *** 5.8 The WOTS+C verifier.

    The spec has no [wots_c_verify]: shrincs.py inlines the comparison
    into [fxmss_pubkey_from_sig].  Naming it here gives the C-refinement
    proof of [shrincs_wots_verify] something at the port to anchor on,
    and it is the only thing in this section that is a DEFINITION rather
    than a fact -- a view of [wots_c_pubkey_from_sig], not a new
    algorithm. *)

Definition wc_verify (pk signature M pk_seed ADRS : bytes) : bool :=
  match wots_c_pubkey_from_sig signature M pk_seed ADRS with
  | Some pk' => bytes_eqb pk' pk
  | None     => false
  end.

(** REASSEMBLY, at the flat signature layout: verification accepts
    exactly when the counter's digest is constant-sum AND the completed
    chains compress to [pk]. *)
Lemma wc_verify_ends (pk M : bytes) (sig : list bytes) (counter : Z)
      (pk_seed : bytes) (nh ni ty pa pb pc : Z) :
  0 <= counter < 2 ^ 16 ->
  length sig = Z.to_nat WOTS_C_CHAIN_COUNT ->
  (forall b, In b sig -> length b = 16%nat) ->
  wc_verify pk (to_bytes counter 2 ++ concat sig) M pk_seed
    (mk_adrs nh ni ty pa pb pc)
  = andb (good_counter pk_seed nh ni M counter)
         (bytes_eqb (T_sf pk_seed (wc_pk_adrs nh ni)
                       (concat (complete_ends M sig counter pk_seed nh ni))) pk).
Proof.
  intros Hc Hlen Hk.
  unfold wc_verify.
  rewrite (wots_c_pubkey_from_sig_ends M sig counter pk_seed _ _ _ _ _ _ Hc Hlen Hk).
  destruct (good_counter pk_seed nh ni M counter); reflexivity.
Qed.

(* ================================================================= *)
(** *** 5.9 Facts the C refinement consumes.

    The digit vector's shape and range, and the linear search's four
    correctness directions (sound / complete / in-range / refuting) --
    what the VST body proofs and the SSProve bridges both consume.
    Stated at the anchor [(nh, ni)] section 5 is parameterized by.  The search proofs are structural inductions
    on [find_from]'s own fuel and do not mention the hash at all. *)

(** Every nibble is a digit: [0, 15]. *)
Lemma nib_range (x : bytes) (j v : Z) : In v (nib x j) -> 0 <= v <= 15.
Proof.
  unfold nib, index.
  pose proof (byte_val_range (nth (Z.to_nat j) x zero_byte)) as Hb.
  set (b := byte_val (nth (Z.to_nat j) x zero_byte)) in *.
  intros [<-|[<-|[]]].
  - rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 4) with 16.
    assert (0 <= b / 16 < 16)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    lia.
  - change (2 ^ 4) with 16.
    pose proof (Z.mod_pos_bound b 16 ltac:(lia)). lia.
Qed.

Lemma length_digest_of (pk_seed : bytes) (nh ni : Z) (M : bytes) (counter : Z) :
  length (digest_of pk_seed nh ni M counter) = 32%nat.
Proof.
  rewrite digest_of_nib. reflexivity.
Qed.

(** Every digit of the vector is in [[0, 15]] -- unconditionally, since
    the digits are read off a hash, not off [M]. *)
Lemma digest_of_In_range (pk_seed : bytes) (nh ni : Z) (M : bytes)
      (counter v : Z) :
  In v (digest_of pk_seed nh ni M counter) -> 0 <= v <= 15.
Proof.
  rewrite digest_of_nib.
  intros Hin. apply in_flat_map in Hin.
  destruct Hin as [j [_ Hj]].
  exact (nib_range _ j v Hj).
Qed.

(** The same, read through the spec's own indexing (which returns 0 out
    of range, so no index hypothesis is needed). *)
Lemma index_int_digest_of_range (pk_seed : bytes) (nh ni : Z) (M : bytes)
      (counter i : Z) :
  0 <= index_int (digest_of pk_seed nh ni M counter) i <= 15.
Proof.
  unfold index_int.
  destruct (Nat.lt_ge_cases (Z.to_nat i)
              (length (digest_of pk_seed nh ni M counter))) as [Hi|Hi].
  - exact (digest_of_In_range _ _ _ _ _ _ (nth_In _ 0 Hi)).
  - rewrite nth_overflow by exact Hi. lia.
Qed.

(** [good_counter] as a statement about the [Z]-valued digit sum -- the
    form the C's [shrincs_wots_map_digest(...) == 240] test produces. *)
Lemma good_counter_Z_iff (pk_seed : bytes) (nh ni : Z) (M : bytes) (counter : Z) :
  good_counter pk_seed nh ni M counter = true
  <-> sum_list (digest_of pk_seed nh ni M counter) = WOTS_C_CONSTANT_SUM.
Proof.
  unfold good_counter, valid_digest.
  split; [apply Z.eqb_eq | apply Z.eqb_eq].
Qed.

(** *** The linear search, in four directions. *)

Lemma find_from_None_intro (pk_seed : bytes) (nh ni : Z) (M : bytes) :
  forall (fuel : nat) (c : Z),
  (forall d, c <= d < c + Z.of_nat fuel -> good_counter pk_seed nh ni M d = false) ->
  find_from pk_seed nh ni M fuel c = None.
Proof.
  induction fuel as [|f IH]; intros c Hbad; cbn [find_from]; [reflexivity|].
  rewrite (Hbad c) by (rewrite Nat2Z.inj_succ; lia).
  apply IH. intros d Hd. apply Hbad. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma find_from_Some_good (pk_seed : bytes) (nh ni : Z) (M : bytes) :
  forall (fuel : nat) (c c' : Z),
  find_from pk_seed nh ni M fuel c = Some c' ->
  good_counter pk_seed nh ni M c' = true.
Proof.
  induction fuel as [|f IH]; intros c c' H; cbn [find_from] in H; [discriminate|].
  destruct (good_counter pk_seed nh ni M c) eqn:Hc.
  - injection H as <-. exact Hc.
  - exact (IH _ _ H).
Qed.

Lemma find_from_Some_range (pk_seed : bytes) (nh ni : Z) (M : bytes) :
  forall (fuel : nat) (c c' : Z),
  find_from pk_seed nh ni M fuel c = Some c' -> c <= c' < c + Z.of_nat fuel.
Proof.
  induction fuel as [|f IH]; intros c c' H; cbn [find_from] in H; [discriminate|].
  rewrite Nat2Z.inj_succ.
  destruct (good_counter pk_seed nh ni M c) eqn:Hc.
  - injection H as <-. lia.
  - apply IH in H. lia.
Qed.

Lemma find_from_complete (pk_seed : bytes) (nh ni : Z) (M : bytes) :
  forall (fuel : nat) (c i : Z),
  c <= i < c + Z.of_nat fuel ->
  good_counter pk_seed nh ni M i = true ->
  (forall d, c <= d < i -> good_counter pk_seed nh ni M d = false) ->
  find_from pk_seed nh ni M fuel c = Some i.
Proof.
  induction fuel as [|f IH]; intros c i Hrange Hgood Hbad; cbn [find_from].
  - exfalso. cbn in Hrange. lia.
  - destruct (good_counter pk_seed nh ni M c) eqn:Hc.
    + destruct (Z.eq_dec c i) as [->|Hne]; [reflexivity|].
      exfalso. rewrite (Hbad c) in Hc by lia. discriminate.
    + apply IH.
      * rewrite Nat2Z.inj_succ in Hrange.
        assert (i <> c) by (intro; subst; congruence). lia.
      * exact Hgood.
      * intros d Hd. apply Hbad. lia.
Qed.

(** [find_counter] is [find_from] at the spec's own [2^16] counter span,
    so the four directions specialize.  [c_max] is kept spelled out
    ([2 ^ 16]) rather than named: the port takes the span from the
    spec's [range(2**16)] and never abbreviates it. *)

Lemma find_counter_good (pk_seed : bytes) (nh ni : Z) (M : bytes) (c : Z) :
  find_counter pk_seed nh ni M = Some c -> good_counter pk_seed nh ni M c = true.
Proof. unfold find_counter. apply find_from_Some_good. Qed.

Lemma find_counter_lt (pk_seed : bytes) (nh ni : Z) (M : bytes) (c : Z) :
  find_counter pk_seed nh ni M = Some c -> 0 <= c < 2 ^ 16.
Proof.
  unfold find_counter. intros H.
  apply find_from_Some_range in H.
  rewrite Z2Nat.id in H by lia. lia.
Qed.

Lemma find_counter_Some_least (pk_seed : bytes) (nh ni : Z) (M : bytes) (i : Z) :
  0 <= i < 2 ^ 16 ->
  good_counter pk_seed nh ni M i = true ->
  (forall d, 0 <= d < i -> good_counter pk_seed nh ni M d = false) ->
  find_counter pk_seed nh ni M = Some i.
Proof.
  unfold find_counter. intros Hi Hgood Hbad.
  apply find_from_complete; [| exact Hgood | exact Hbad].
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma find_counter_None (pk_seed : bytes) (nh ni : Z) (M : bytes) :
  (forall c, 0 <= c < 2 ^ 16 -> good_counter pk_seed nh ni M c = false) ->
  find_counter pk_seed nh ni M = None.
Proof.
  unfold find_counter. intros Hbad.
  apply find_from_None_intro.
  rewrite Z2Nat.id by lia.
  intros d Hd. apply Hbad. lia.
Qed.

(** *** Widths of the per-chain views. *)

Lemma length_wc_chain (pk_seed : bytes) (nh ni i : Z) (node : bytes)
      (start steps : Z) :
  0 < steps -> length (wc_chain pk_seed nh ni i node start steps) = 16%nat.
Proof.
  intros Hs. unfold wc_chain.
  replace steps with (Z.of_nat (S (Z.to_nat (steps - 1)))) by lia.
  rewrite range_succ, fold_left_app.
  cbn [fold_left].
  apply length_F.
Qed.

(** A zero-step chain is its own input. *)
Lemma wc_chain_0 (pk_seed : bytes) (nh ni i : Z) (node : bytes) (start : Z) :
  wc_chain pk_seed nh ni i node start 0 = node.
Proof. unfold wc_chain. rewrite Z.add_0_r, range_nil. reflexivity. Qed.

Lemma length_derive_sk (sk_seed pk_seed : bytes) (nh ni i : Z) :
  length (derive_sk sk_seed pk_seed nh ni i) = 16%nat.
Proof. apply length_PRF. Qed.

(** The three views are [WOTS_C_CHAIN_COUNT] blocks long. *)

Lemma length_chain_tips (sk_seed pk_seed : bytes) (nh ni : Z) :
  length (chain_tips sk_seed pk_seed nh ni) = 32%nat.
Proof. unfold chain_tips. rewrite length_map_range. reflexivity. Qed.

Lemma length_sign_chains (M sk_seed pk_seed : bytes) (nh ni counter : Z) :
  length (sign_chains M sk_seed pk_seed nh ni counter) = 32%nat.
Proof. unfold sign_chains. rewrite length_map_range. reflexivity. Qed.

Lemma length_complete_ends (M : bytes) (sig : list bytes) (counter : Z)
      (pk_seed : bytes) (nh ni : Z) :
  length (complete_ends M sig counter pk_seed nh ni) = 32%nat.
Proof. unfold complete_ends. rewrite length_map_range. reflexivity. Qed.

(** Each block of [chain_tips] / [complete_ends] is a 16-byte hash: the
    tips run [w - 1 = 15] steps from 0, and a completed end runs
    [15 - ds[i]] steps -- zero only when the digit is already at the top
    of its chain, where the block is the signature's own (16 bytes by
    the caller's own hypothesis).  [sign_chains] has no such lemma: a
    digit of 0 leaves the PRF output, which IS 16 bytes. *)

Lemma Forall_length_chain_tips (sk_seed pk_seed : bytes) (nh ni : Z) :
  Forall (fun b => length b = 16%nat) (chain_tips sk_seed pk_seed nh ni).
Proof.
  unfold chain_tips.
  apply Forall_forall. intros b Hb.
  apply in_map_iff in Hb. destruct Hb as [i [<- _]].
  apply length_wc_chain. cbn. lia.
Qed.

Lemma Forall_length_sign_chains (M sk_seed pk_seed : bytes) (nh ni counter : Z) :
  Forall (fun b => length b = 16%nat)
         (sign_chains M sk_seed pk_seed nh ni counter).
Proof.
  unfold sign_chains.
  apply Forall_forall. intros b Hb.
  apply in_map_iff in Hb. destruct Hb as [i [<- _]].
  pose proof (index_int_digest_of_range pk_seed nh ni M counter i) as Hd.
  destruct (Z.eq_dec (index_int (digest_of pk_seed nh ni M counter) i) 0) as [Hz|Hz].
  - rewrite Hz, wc_chain_0. apply length_derive_sk.
  - apply length_wc_chain. lia.
Qed.

(** A completed end is 16 bytes.  The [length sig] hypothesis is real:
    at digit 15 the chain runs ZERO steps and the block IS the
    signature's own, so the width has to come from the caller.  (Both
    hypotheses are exactly [wots_c_pubkey_from_sig_ends]'.) *)
Lemma Forall_length_complete_ends (M : bytes) (sig : list bytes) (counter : Z)
      (pk_seed : bytes) (nh ni : Z) :
  length sig = Z.to_nat WOTS_C_CHAIN_COUNT ->
  (forall b, In b sig -> length b = 16%nat) ->
  Forall (fun b => length b = 16%nat) (complete_ends M sig counter pk_seed nh ni).
Proof.
  intros Hlen Hk.
  unfold complete_ends.
  apply Forall_forall. intros b Hb.
  apply in_map_iff in Hb. destruct Hb as [i [<- Hi]].
  pose proof (index_int_digest_of_range pk_seed nh ni M counter i) as Hd.
  pose proof (in_range _ _ _ Hi) as Hir.
  unfold WOTS_C_CHAIN_COUNT in Hir.
  destruct (Z.eq_dec (2 ^ WOTS_C_CHAIN_BITS - 1
                      - index_int (digest_of pk_seed nh ni M counter) i) 0)
    as [Hz|Hz].
  - rewrite Hz, wc_chain_0.
    unfold index_block.
    apply Hk, nth_In.
    rewrite Hlen. unfold WOTS_C_CHAIN_COUNT. lia.
  - apply length_wc_chain. unfold WOTS_C_CHAIN_BITS in *. lia.
Qed.
