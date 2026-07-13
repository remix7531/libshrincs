(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.chain_blocks: per-chain block steps shared by
    [body_shrincs_wots_pubkey_gen], [body_shrincs_wots_sign], and
    [body_shrincs_wots_pubkey_from_sig] (the [set_type_byte_prf_hash] type-byte
    bridge is also reused by [body_shrincs_wots_chain_from_seed]).

    In the WOTS+C construction each chain is launched from the named
    [shrincs_wots_hash_adrs a i] address and started from the PRF-derived secret
    [shrincs_wots_derive_sk i]; the loop invariants only need the caller's address
    prefix ([adrs_struct_eq]) preserved.  The per-chain address-stepping
    lemmas are proved alongside the body proofs that use them. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.lengths.
From Vst Require Import contract.lemmas.data_at.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** Per-chain blocks. *)

(** The [i]-th chain tip of [shrincs_wots_pubkey_gen].

    These VST-side per-chain blocks are plain [nat]-indexed (so the loop
    invariants below stay non-dependent) but build the model's [fin 32]
    chain index via the C-refinement totalizer [to_chain32] and iterate
    with the total [chain_iter_c] wrapper.  The [_map] bridges then relate
    them to the dependent model ([chain_tips] / [sign_chains] /
    [complete_ends], written with [fin_of_nat] + the dependent
    [shrincs_wots_chain_iter]) via [for_idx_dep_map_eq]. *)
Definition pkgen_block (sk_seed pk_seed : block) (a : adrs) (i : nat) : block :=
  chain_iter_c (shrincs_wots_derive_sk (to_chain32 i) sk_seed pk_seed a) 0 w_pred pk_seed
                  (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 i)).

(** The [i]-th chain signature of [shrincs_wots_sign] (for digit vector [ds]). *)
Definition sign_block (sk_seed pk_seed : block) (a : adrs) (ds : list nat)
                      (i : nat) : block :=
  chain_iter_c (shrincs_wots_derive_sk (to_chain32 i) sk_seed pk_seed a) 0 (nth i ds 0%nat) pk_seed
                  (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 i)).

(** The [i]-th completed chain tip of [shrincs_wots_pubkey_from_sig]. *)
Definition complete_block (sig : list block) (ds : list nat) (pk_seed : block)
                          (a : adrs) (i : nat) : block :=
  chain_iter_c (nth i sig default) (nth i ds 0%nat)
                  (w_pred - nth i ds 0%nat) pk_seed (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 i)).

Lemma pkgen_block_Zlength : forall sk pub a i,
  Zlength (pkgen_block sk pub a i) = n_bytes.
Proof. intros. unfold pkgen_block. apply chain_iter_c_Zlength, shrincs_wots_derive_sk_Zlength. Qed.

Lemma sign_block_Zlength : forall sk pub a ds i,
  Zlength (sign_block sk pub a ds i) = n_bytes.
Proof. intros. unfold sign_block. apply chain_iter_c_Zlength, shrincs_wots_derive_sk_Zlength. Qed.

Lemma complete_block_Zlength : forall sig ds pub a i,
  Zlength (nth i sig default) = n_bytes ->
  Zlength (complete_block sig ds pub a i) = n_bytes.
Proof. intros. unfold complete_block. apply chain_iter_c_Zlength. assumption. Qed.

(* ================================================================= *)
(** ** [chain_tips] / [sign_chains] / [complete_ends] as maps. *)

Lemma chain_tips_map : forall sk pub a,
  chain_tips sk pub a = map (pkgen_block sk pub a) (seq 0 len).
Proof.
  intros sk pub a. unfold chain_tips. apply for_idx_dep_map_eq. intros i Hi.
  unfold pkgen_block.
  rewrite (chain_iter_c_eq _ _ _ _ _ full_chain_bound).
  rewrite !(to_chain32_id i (chain_idx_lt i Hi)).
  reflexivity.
Qed.

Lemma sign_chains_map : forall msg sk pub a counter,
  sign_chains msg sk pub a counter
  = map (sign_block sk pub a (digest_of pub a msg counter)) (seq 0 len).
Proof.
  intros msg sk pub a counter. unfold sign_chains. cbv zeta.
  apply for_idx_dep_map_eq. intros i Hi. unfold sign_block.
  rewrite (chain_iter_c_eq _ _ _ _ _ (sign_chain_bound pub a msg counter i)).
  rewrite !(to_chain32_id i (chain_idx_lt i Hi)).
  reflexivity.
Qed.

Lemma complete_ends_map : forall msg sig counter pub a,
  complete_ends msg sig counter pub a
  = map (complete_block sig (digest_of pub a msg counter) pub a) (seq 0 len).
Proof.
  intros msg sig counter pub a. unfold complete_ends. cbv zeta.
  apply for_idx_dep_map_eq. intros i Hi. unfold complete_block.
  rewrite (chain_iter_c_eq _ _ _ _ _ (complete_chain_bound pub a msg counter i)).
  rewrite !(to_chain32_id i (chain_idx_lt i Hi)).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Lengths of the tip lists (for the T_sf compression buffer). *)

Lemma chain_tips_length : forall sk pub a,
  length (chain_tips sk pub a) = len.
Proof. intros. unfold chain_tips. apply length_for_idx_dep. Qed.

Lemma chain_tips_Forall_Zlength : forall sk pub a,
  Forall (fun b => Zlength b = n_bytes) (chain_tips sk pub a).
Proof.
  intros. rewrite chain_tips_map. apply Forall_map, Forall_forall.
  intros k _. apply pkgen_block_Zlength.
Qed.

Lemma complete_ends_length : forall msg sig counter pub a,
  length (complete_ends msg sig counter pub a) = len.
Proof. intros. unfold complete_ends. apply length_for_idx_dep. Qed.

Lemma complete_ends_Forall_Zlength : forall msg sig counter pub a,
  Forall (fun b => Zlength b = n_bytes) sig ->
  Forall (fun b => Zlength b = n_bytes) (complete_ends msg sig counter pub a).
Proof.
  intros msg sig counter pub a Hs.
  rewrite complete_ends_map. apply Forall_map, Forall_forall.
  intros k _. apply complete_block_Zlength, nth_block_Zlength_default, Hs.
Qed.

(** The concatenated tip buffers have exactly [len * n] bytes. *)
Lemma Zlength_concat_chain_tips : forall sk pub a,
  Zlength (concat (chain_tips sk pub a)) = Z.of_nat (len * n).
Proof.
  intros. rewrite Zlength_concat_fixed by apply chain_tips_Forall_Zlength.
  rewrite chain_tips_length. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

Lemma Zlength_concat_complete_ends : forall msg sig counter pub a,
  Forall (fun b => Zlength b = n_bytes) sig ->
  Zlength (concat (complete_ends msg sig counter pub a)) = Z.of_nat (len * n).
Proof.
  intros msg sig counter pub a Hs.
  rewrite Zlength_concat_fixed by (apply complete_ends_Forall_Zlength, Hs).
  rewrite complete_ends_length. rewrite Nat2Z.inj_mul. reflexivity.
Qed.

(* ================================================================= *)
(** ** Address-stepping lemmas shared by the pkgen / sign / from_sig
    body proofs (and [shrincs_wots_chain_from_seed]).

    The named PRF / hash / pk constructors reset the type / reserved /
    chain / hash fields to values keyed only on [i]; hence two addresses
    that agree on the caller-prefilled prefix ([adrs_struct_eq]) produce
    the same constructed address.  This lets the chain loops carry an
    [adrs_struct_eq] invariant and still relate each call back to the base
    address [a] used by the model. *)

(** Two addresses sharing the caller prefix ([adrs_struct_eq]) share the
    fin-anchor ([adrs_nh]/[adrs_ni]) too, so the named WOTS+C constructors
    (built from that anchor) agree on both. *)
Lemma adrs_struct_eq_anchor : forall b a,
  adrs_struct_eq b a -> adrs_nh b = adrs_nh a /\ adrs_ni b = adrs_ni a.
Proof.
  intros b a (Hh & Hi). split; apply fin_val_inj.
  - rewrite !adrs_nh_tag_z; exact Hh.
  - rewrite !adrs_ni_idx_z; exact Hi.
Qed.

Lemma shrincs_wots_prf_adrs_congr : forall b a i,
  adrs_struct_eq b a -> shrincs_wots_prf_adrs b i = shrincs_wots_prf_adrs a i.
Proof.
  intros b a i Hba. destruct (adrs_struct_eq_anchor b a Hba) as (Hnh & Hni).
  unfold shrincs_wots_prf_adrs. rewrite Hnh, Hni. reflexivity.
Qed.

Lemma shrincs_wots_hash_adrs_congr : forall b a i,
  adrs_struct_eq b a -> shrincs_wots_hash_adrs w_pred_pos b i = shrincs_wots_hash_adrs w_pred_pos a i.
Proof.
  intros b a i Hba. destruct (adrs_struct_eq_anchor b a Hba) as (Hnh & Hni).
  unfold shrincs_wots_hash_adrs. rewrite Hnh, Hni. reflexivity.
Qed.

Lemma shrincs_wots_pk_adrs_congr : forall b a,
  adrs_struct_eq b a -> shrincs_wots_pk_adrs b = shrincs_wots_pk_adrs a.
Proof.
  intros b a Hba. destruct (adrs_struct_eq_anchor b a Hba) as (Hnh & Hni).
  unfold shrincs_wots_pk_adrs. rewrite Hnh, Hni. reflexivity.
Qed.

(** [shrincs_wots_derive_sk] reads the base address only through [shrincs_wots_prf_adrs],
    hence only through the caller-prefilled prefix. *)
Lemma shrincs_wots_derive_sk_congr : forall i sk pk x a,
  adrs_struct_eq x a -> shrincs_wots_derive_sk i sk pk x = shrincs_wots_derive_sk i sk pk a.
Proof.
  intros i sk pk x a Hxa.
  unfold shrincs_wots_derive_sk.
  rewrite (shrincs_wots_prf_adrs_congr x a i Hxa).
  reflexivity.
Qed.

(** Storing the HASH type byte over the wire view ([adrs_to_raw]) of a
    PRF-typed address yields the wire view of the hash-typed address at
    the same chain index: they differ only in the type byte (the PRF
    address's zero hash slot already matches the hash address's
    position 0). *)
Lemma set_type_byte_prf_hash : forall a i,
  rset_type (adrs_to_raw (shrincs_wots_prf_adrs a i)) (byte_val SF_SHRINCS_WOTS_HASH)
  = adrs_to_raw (shrincs_wots_hash_adrs w_pred_pos a i).
Proof. intros a i. reflexivity. Qed.

(** ([chain_addr_post_struct_eq] lives in [contract.helpers], next to
    [chain_addr_post]'s definition, since that file compiles after this one.) *)

(** The post-loop PK-typing sequence [addr[9]=17; put32(CHAIN,0);
    put32(HASH,0)] realises exactly the wire view of [shrincs_wots_pk_adrs a]
    on any wire view still carrying the caller prefix and a zero reserved
    word. *)
Lemma pkaddr_final_eq : forall (ai a : adrs),
  adrs_struct_eq ai a ->
  payload_a_z ai = 0 ->
  rset_payload_c (rset_payload_b (rset_type (adrs_to_raw ai) (byte_val SF_SHRINCS_WOTS_PK)) 0) 0
  = adrs_to_raw (shrincs_wots_pk_adrs a).
Proof.
  intros ai a (Hh & Hi) Hr.
  unfold rset_payload_c, rset_payload_b, rset_type, adrs_to_raw, shrincs_wots_pk_adrs.
  cbn [rtag ridx rtype rpa rpb rpc adrs_anchor_tag_z adrs_anchor_idx_z
       adrs_type payload_a_z payload_b_z payload_c_z].
  rewrite Hr, Hh, Hi, <- (adrs_nh_tag_z _ _ a), <- (adrs_ni_idx_z _ _ a).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** [chain_iter_c] step laws (loop entry / one step / position
    independence), shared by the chain_iter and pubkey_from_sig body
    proofs. *)

(** [chain_iter_c] with zero steps is the identity (loop entry). *)
Lemma chain_iter_c_0 : forall X start pk_seed a,
  chain_iter_c X start 0 pk_seed a = X.
Proof. intros. unfold chain_iter_c. destruct (le_dec (start + 0) w_pred); reflexivity. Qed.

(** One more chain step on a hash address: [chain_iter_c] at [S i] is [F]
    of the position-[start+i] hash address applied to the [i]-step prefix.
    Both wrappers reduce (via [chain_iter_c_eq]) to the dependent model
    [shrincs_wots_chain_iter]; the position field is the value-faithful
    [to_pos15 (start+i)] and the step/position proofs are proof-irrelevant
    ([le_unique] / [fin_val_inj]). *)
Lemma chain_iter_c_step_hash : forall in_buf start i pk_seed nh ni chain pos,
  (start + S i <= w_pred)%nat ->
  chain_iter_c in_buf start (S i) pk_seed (Wc_hash nh ni chain pos)
  = F pk_seed (Wc_hash nh ni chain (to_pos15 (start + i)))
      (chain_iter_c in_buf start i pk_seed (Wc_hash nh ni chain pos)).
Proof.
  intros in_buf start i pk_seed nh ni chain pos Hb.
  assert (Hb' : (start + i <= w_pred)%nat) by lia.
  rewrite (chain_iter_c_eq _ _ _ _ _ Hb).
  rewrite (chain_iter_c_eq _ _ _ _ _ Hb').
  simpl shrincs_wots_chain_iter. unfold F. f_equal.
  - cbn [set_hash_pos]. f_equal. apply fin_val_inj.
    rewrite fin_val_of_nat, to_pos15_val by (unfold w_pred in Hb; lia). reflexivity.
  - f_equal. apply le_unique.
Qed.

(** [shrincs_wots_chain_iter] rewrites the ADRS position before every [F],
    so its result is invariant under the incoming position word.  Stated
    on the dependent model iterate: the step-bound proofs are irrelevant
    ([le_unique]) and the per-step position field is rebuilt at index
    [start + k] regardless of the incoming [pos] ([fin_val_inj]). *)
Lemma chain_iter_dep_pos_indep : forall s X st pk_seed nh ni ch p q
    (H1 H2 : (st + s <= w_pred)%nat),
  shrincs_wots_chain_iter X st s pk_seed (Wc_hash nh ni ch p) H1
  = shrincs_wots_chain_iter X st s pk_seed (Wc_hash nh ni ch q) H2.
Proof.
  induction s as [|k IH]; intros X st pk_seed nh ni ch p q H1 H2.
  - reflexivity.
  - cbn [shrincs_wots_chain_iter].
    f_equal.
    + cbn [set_hash_pos].
      f_equal.
      apply fin_val_inj. reflexivity.
    + apply IH.
Qed.

(** Position independence lifts to the total wrapper [chain_iter_c]. *)
Lemma chain_iter_c_pos_indep : forall X st s pk_seed nh ni ch p q,
  chain_iter_c X st s pk_seed (Wc_hash nh ni ch p)
  = chain_iter_c X st s pk_seed (Wc_hash nh ni ch q).
Proof.
  intros X st s pk_seed nh ni ch p q. unfold chain_iter_c.
  destruct (le_dec (st + s) w_pred) as [Hle|Hle].
  - apply chain_iter_dep_pos_indep.
  - reflexivity.
Qed.

(* ================================================================= *)
(** ** The chain-launch address [wc_set_chain] (dependent-union ADRS),
    used by [body_shrincs_wots_pubkey_from_sig]'s completion loop.

    The C completes each chain by writing only the chain-index word
    ([shrincs_adrs_put32 ADRS_CHAIN]) on the residual address left by
    the previous chain -- it never re-zeroes the hash-position word.  So
    the union threaded through the loop carries an arbitrary residual
    position, which [wc_set_chain] overwrites the chain index of; the
    chain iteration then re-writes the position before every [F], making
    its result invariant under the residual ([chain_iter_c_pos_indep]). *)

(** Overwrite the WOTS+C chain index of a hash-typed address; identity on
    any non-hash arm.  Its wire view is exactly the [ADRS_CHAIN] splice on
    the raw view (the C's [shrincs_adrs_put32] post). *)
Definition wc_set_chain (a : adrs) (c : nat) : adrs :=
  match a with
  | Wc_hash nh ni _ pos => Wc_hash nh ni (to_chain32 c : fin (Z.of_nat len)) pos
  | _ => a
  end.

Lemma wc_set_chain_struct_eq : forall ai c,
  adrs_struct_eq (wc_set_chain ai c) ai.
Proof. intros ai c. destruct ai; split; reflexivity. Qed.

Lemma wc_set_chain_type : forall ai c,
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  adrs_type (wc_set_chain ai c) = SF_SHRINCS_WOTS_HASH.
Proof.
  intros ai c Ht.
  destruct ai as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht.
  reflexivity.
Qed.

(** A hash-typed address is a [Wc_hash] (used to discharge the
    [shrincs_wots_chain_iter] funspec's [exists .. = Wc_hash] precondition). *)
Lemma adrs_hash_is_Wc_hash : forall x : adrs,
  adrs_type x = SF_SHRINCS_WOTS_HASH ->
  exists nh ni chain pos, x = Wc_hash nh ni chain pos.
Proof.
  intros x Ht.
  destruct x as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht.
  do 4 eexists. reflexivity.
Qed.

(** The [ADRS_CHAIN] store on the wire view of a hash-typed address is the
    wire view of [wc_set_chain]: the [Z]-valued raw field takes the stored
    index directly ([to_chain32] is value-faithful in range). *)
Lemma wc_set_chain_raw : forall ai i,
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  0 <= i < 32 ->
  adrs_to_raw (wc_set_chain ai (Z.to_nat i)) = rset_payload_b (adrs_to_raw ai) i.
Proof.
  intros ai i Ht Hi.
  destruct ai as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht.
  cbn [wc_set_chain].
  unfold adrs_to_raw, rset_payload_b.
  cbn [adrs_type adrs_anchor_tag_z adrs_anchor_idx_z
       payload_a_z payload_b_z payload_c_z rtag ridx rtype rpa rpb rpc].
  f_equal.
  rewrite to_chain32_val by (pose proof len_eq_Z; lia).
  reflexivity.
Qed.

(** The chain the C runs from slot [i] -- launched from the previous
    chain's residual address with its chain index reset to [i] -- computes
    exactly the model's [complete_block] at the named [shrincs_wots_hash_adrs a
    i]: the two addresses agree on the caller anchor ([adrs_struct_eq]) and
    on the chain index, and the position is immaterial. *)
Lemma chain_wc_set_chain : forall X st s pk_seed ai a i,
  adrs_struct_eq ai a ->
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  chain_iter_c X st s pk_seed (wc_set_chain ai (Z.to_nat i))
  = chain_iter_c X st s pk_seed (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 (Z.to_nat i))).
Proof.
  intros X st s pk_seed ai a i Hse Ht.
  destruct ai as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht.
  destruct Hse as [Hh Hi].
  cbn [adrs_anchor_tag_z adrs_anchor_idx_z] in Hh, Hi.
  assert (Hnh : nh = adrs_nh a) by (apply fin_val_inj; rewrite adrs_nh_tag_z; exact Hh).
  assert (Hni : ni = adrs_ni a) by (apply fin_val_inj; rewrite adrs_ni_idx_z; exact Hi).
  cbn [wc_set_chain].
  unfold shrincs_wots_hash_adrs.
  rewrite Hnh, Hni.
  apply chain_iter_c_pos_indep.
Qed.

Lemma complete_block_from_ai : forall sig ds pk_seed ai a i,
  adrs_struct_eq ai a ->
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  chain_iter_c (nth (Z.to_nat i) sig default) (nth (Z.to_nat i) ds 0%nat)
    (w_pred - nth (Z.to_nat i) ds 0%nat) pk_seed (wc_set_chain ai (Z.to_nat i))
  = complete_block sig ds pk_seed a (Z.to_nat i).
Proof.
  intros sig ds pk_seed ai a i Hse Ht.
  unfold complete_block.
  apply chain_wc_set_chain; assumption.
Qed.

(* ================================================================= *)
(** ** Per-iteration block folds: the loop bodies compute the named
    blocks over the residual address, re-keyed onto the base address. *)

(** One completed loop iteration on a structurally-equal address computes the
    canonical [pkgen_block]: derive the secret, re-type to hash, chain [w-1]
    steps.  Both [shrincs_wots_derive_sk] and the hash address only see the prefix fields,
    which [b] shares with [a]. *)
Lemma iter_eq_pkgen_block : forall sk_seed pk_seed a b i,
  adrs_struct_eq b a ->
  chain_iter_c (shrincs_wots_derive_sk (to_chain32 i) sk_seed pk_seed b) 0 w_pred pk_seed
                  (shrincs_wots_hash_adrs w_pred_pos b (to_chain32 i))
  = pkgen_block sk_seed pk_seed a i.
Proof.
  intros sk_seed pk_seed a b i Hs.
  unfold pkgen_block.
  rewrite (shrincs_wots_derive_sk_congr (to_chain32 i) sk_seed pk_seed b a Hs).
  rewrite (shrincs_wots_hash_adrs_congr b a (to_chain32 i) Hs).
  reflexivity.
Qed.

(** The [sign_block] sibling of [iter_eq_pkgen_block]: one signing-loop
    iteration on a structurally-equal address computes the canonical
    [sign_block] (chain [nth i ds] steps instead of [w_pred]). *)
Lemma iter_eq_sign_block : forall sk_seed pk_seed a b ds i,
  adrs_struct_eq b a ->
  chain_iter_c (shrincs_wots_derive_sk (to_chain32 i) sk_seed pk_seed b) 0 (nth i ds 0%nat) pk_seed
                  (shrincs_wots_hash_adrs w_pred_pos b (to_chain32 i))
  = sign_block sk_seed pk_seed a ds i.
Proof.
  intros sk_seed pk_seed a b ds i Hs.
  unfold sign_block.
  rewrite (shrincs_wots_derive_sk_congr (to_chain32 i) sk_seed pk_seed b a Hs).
  rewrite (shrincs_wots_hash_adrs_congr b a (to_chain32 i) Hs).
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Wire-view store folds: the type-byte + [shrincs_adrs_put32]
    sequences realise the named model addresses. *)

(** The wire view ([radrs]) built by the C's four in-place stores (type
    := 21, reserved := 0, chain := chain_i, hash := 0) is exactly
    [adrs_to_raw] of the PRF address [shrincs_wots_prf_adrs a chain_i].
    The union constructor's chain field is built by the C-refinement
    totalizer [to_chain32]; in range ([chain_i < len = 32]) it is
    value-faithful ([to_chain32_val]), so the stored [chain_i] matches. *)
Lemma prf_raw_stores : forall a chain_i,
  0 <= chain_i < Z.of_nat len ->
  rset_payload_c (rset_payload_b (rset_payload_a
    (rset_type (adrs_to_raw a) 21) 0) chain_i) 0
  = adrs_to_raw (shrincs_wots_prf_adrs a (to_chain32 (Z.to_nat chain_i))).
Proof.
  intros a chain_i Hc.
  unfold rset_payload_c, rset_payload_b, rset_payload_a, rset_type,
    adrs_to_raw, shrincs_wots_prf_adrs.
  cbn [rtag ridx rtype rpa rpb rpc adrs_anchor_tag_z adrs_anchor_idx_z
       adrs_type payload_a_z payload_b_z payload_c_z].
  rewrite <- (adrs_nh_tag_z _ _ a), <- (adrs_ni_idx_z _ _ a).
  f_equal. rewrite to_chain32_val by lia. reflexivity.
Qed.

(** Under the clean-anchor precondition (payload words zero), storing the
    GRIND type byte over the wire view of [a] IS the grind address's
    serialization: both keep [a]'s anchor, set the type to 22, and carry
    zero payload words. *)
Lemma grind_addr_stores : forall a : adrs,
  payload_a_z a = 0 -> payload_b_z a = 0 -> payload_c_z a = 0 ->
  block_to_vals (radrs_bytes (rset_type (adrs_to_raw a) 22))
  = adrs_to_vals (shrincs_wots_grind_adrs a).
Proof.
  intros a Hpa Hpb Hpc.
  unfold adrs_to_vals. f_equal.
  unfold radrs_bytes, rset_type, adrs_to_raw, adrs_bytes, shrincs_wots_grind_adrs.
  cbn [rtag ridx rtype rpa rpb rpc adrs_anchor_tag_z adrs_anchor_idx_z
       payload_a_z payload_b_z payload_c_z adrs_type].
  rewrite Hpa, Hpb, Hpc, <- (adrs_nh_tag_z _ _ a), <- (adrs_ni_idx_z _ _ a).
  reflexivity.
Qed.

(** Loop-entry fold: after [addr[9]=HASH; put32(RESERVED,0)] on the grind
    address, the wire view is exactly [adrs_to_raw (shrincs_wots_hash_adrs a
    0)] (same anchor, hash type byte, all payload words zero). *)
Lemma hash0_raw : forall a : adrs,
  rset_payload_a (rset_type (adrs_to_raw (shrincs_wots_grind_adrs a)) 16) 0
  = adrs_to_raw (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 0)).
Proof. intros a. reflexivity. Qed.

(** Post-loop PK-typing: [addr[9]=17; put32(CHAIN,0); put32(HASH,0)]
    realises the wire view of [shrincs_wots_pk_adrs a] (shared
    [pkaddr_final_eq], with the [17] literal the store produces). *)
Lemma pkaddr_final_17 : forall (ai a : adrs),
  adrs_struct_eq ai a ->
  payload_a_z ai = 0 ->
  rset_payload_c (rset_payload_b (rset_type (adrs_to_raw ai) 17) 0) 0
  = adrs_to_raw (shrincs_wots_pk_adrs a).
Proof.
  intros ai a Hse Hr.
  change 17 with (byte_val SF_SHRINCS_WOTS_PK).
  apply pkaddr_final_eq; assumption.
Qed.
