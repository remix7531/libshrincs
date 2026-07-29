(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.chain_blocks: per-chain block steps shared by
    [body_shrincs_wots_pubkey_gen], [body_shrincs_wots_sign], and
    [body_shrincs_wots_pubkey_from_sig] (the [set_type_byte_prf_hash] type-byte
    bridge is also reused by [body_shrincs_wots_chain_from_seed]).

    In the WOTS+C construction each chain is launched from the PRF-derived
    secret [derive_sk] and iterated by [wc_chain] at the caller's anchor
    ([anchor_nh] / [anchor_ni]) and the chain's own index; the loop
    invariants only need the caller's address prefix ([adrs_struct_eq])
    preserved.  The per-chain address-stepping lemmas are proved alongside
    the body proofs that use them.

    The port's chain ([Model.theory.shrincs] section 5.2) is a plain
    [fold_left] over the positions the spec visits: it is TOTAL, takes
    [nh]/[ni]/the chain index as bare [Z]s, and does not read the ADRS
    position word at all.  So the previous model's totalizing wrapper and
    its position-independence / proof-irrelevance family are gone -- what
    is left below is only what the C refinement genuinely needs. *)

From VST Require Import floyd.proofauto.
From Vst Require Import contract.public.
From Vst Require Import contract.lemmas.lengths.
From Vst Require Import contract.lemmas.data_at.

Open Scope Z_scope.

Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** Per-chain blocks.

    These VST-side per-chain blocks are plain [nat]-indexed, so the loop
    invariants below stay non-dependent and iterate [seq 0 len]; the
    port's own views are [map]s over [range 0 WOTS_C_CHAIN_COUNT].
    [map_range_seq] is the bridge, and the [_map] lemmas below are where
    it is spent. *)

(** The [i]-th chain tip of [shrincs_wots_pubkey_gen]. *)
Definition pkgen_block (sk_seed pk_seed : block) (a : adrs) (i : nat) : block :=
  wc_chain pk_seed (anchor_nh a) (anchor_ni a) (Z.of_nat i)
    (derive_sk sk_seed pk_seed (anchor_nh a) (anchor_ni a) (Z.of_nat i))
    0 (Z.of_nat w_pred).

(** The [i]-th chain signature of [shrincs_wots_sign] (for digit vector [ds]). *)
Definition sign_block (sk_seed pk_seed : block) (a : adrs) (ds : list Z)
                      (i : nat) : block :=
  wc_chain pk_seed (anchor_nh a) (anchor_ni a) (Z.of_nat i)
    (derive_sk sk_seed pk_seed (anchor_nh a) (anchor_ni a) (Z.of_nat i))
    0 (shrincs.index_int ds (Z.of_nat i)).

(** The [i]-th completed chain tip of [shrincs_wots_pubkey_from_sig]. *)
Definition complete_block (sig : list block) (ds : list Z) (pk_seed : block)
                          (a : adrs) (i : nat) : block :=
  wc_chain pk_seed (anchor_nh a) (anchor_ni a) (Z.of_nat i)
    (index_block sig (Z.of_nat i))
    (shrincs.index_int ds (Z.of_nat i))
    (Z.of_nat w_pred - shrincs.index_int ds (Z.of_nat i)).

Lemma pkgen_block_Zlength : forall sk pub a i,
  Zlength (pkgen_block sk pub a i) = n_bytes.
Proof. intros. apply wc_chain_Zlength, derive_sk_Zlength. Qed.

Lemma sign_block_Zlength : forall sk pub a ds i,
  Zlength (sign_block sk pub a ds i) = n_bytes.
Proof. intros. apply wc_chain_Zlength, derive_sk_Zlength. Qed.

(** A completed end is [n] bytes as soon as its launch block is: a digit
    of 15 runs ZERO steps, so the block IS the signature's own. *)
Lemma complete_block_Zlength : forall sig ds pub a i,
  Zlength (index_block sig (Z.of_nat i)) = n_bytes ->
  Zlength (complete_block sig ds pub a i) = n_bytes.
Proof. intros. apply wc_chain_Zlength. assumption. Qed.

(** In-range indexing into a fixed-width block list.  The port's
    [index_block] defaults to the EMPTY block (not a zero block), so the
    caller's length hypothesis is what rules the default out. *)
Lemma index_block_Zlength : forall (bs : list block) (i : Z),
  0 <= i < Z.of_nat (length bs) ->
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (index_block bs i) = n_bytes.
Proof.
  intros bs i [Hi0 Hi1] HF.
  rewrite Forall_forall in HF.
  apply HF, nth_In.
  (* [nth_In] instantiates the element type as the port's [bytes], so the
     two [length bs] are only CONVERTIBLE ([block := list byte]) -- [lia]
     would see them as distinct atoms. *)
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. exact Hi1.
Qed.

(* ================================================================= *)
(** ** [chain_tips] / [sign_chains] / [complete_ends] as maps.

    Each port view is a [map] over [range 0 WOTS_C_CHAIN_COUNT]; [len_port]
    re-reads that count as [Z.of_nat len] and [map_range_seq] turns the
    [range] into the [seq 0 len] the C loops count over. *)

Lemma chain_tips_map : forall sk pub a,
  chain_tips sk pub (anchor_nh a) (anchor_ni a)
  = map (pkgen_block sk pub a) (seq 0 len).
Proof.
  intros sk pub a. unfold chain_tips.
  rewrite <- len_port, map_range_seq.
  reflexivity.
Qed.

Lemma sign_chains_map : forall msg sk pub a counter,
  sign_chains msg sk pub (anchor_nh a) (anchor_ni a) counter
  = map (sign_block sk pub a
           (digest_of pub (anchor_nh a) (anchor_ni a) msg counter))
        (seq 0 len).
Proof.
  intros msg sk pub a counter. unfold sign_chains. cbv zeta.
  rewrite <- len_port, map_range_seq.
  reflexivity.
Qed.

Lemma complete_ends_map : forall msg sig counter pub a,
  complete_ends msg sig counter pub (anchor_nh a) (anchor_ni a)
  = map (complete_block sig
           (digest_of pub (anchor_nh a) (anchor_ni a) msg counter) pub a)
        (seq 0 len).
Proof.
  intros msg sig counter pub a. unfold complete_ends. cbv zeta.
  rewrite <- len_port, map_range_seq.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Lengths of the tip lists (for the T_sf compression buffer).

    The block widths are [Model.theory.shrincs]'s; these only restate them
    at VST's [Zlength] and push them through [concat]. *)

Lemma chain_tips_Forall_Zlength : forall sk pub nh ni,
  Forall (fun b => Zlength b = n_bytes) (chain_tips sk pub nh ni).
Proof.
  intros sk pub nh ni.
  pose proof (Forall_length_chain_tips sk pub nh ni) as HL.
  rewrite Forall_forall in HL |- *.
  intros b Hb. rewrite Zlength_correct, (HL b Hb). reflexivity.
Qed.

(** The [length sig] hypothesis is real: at digit 15 the chain runs zero
    steps and the end block IS the signature's own. *)
Lemma complete_ends_Forall_Zlength : forall msg sig counter pub nh ni,
  length sig = len ->
  Forall (fun b => Zlength b = n_bytes) sig ->
  Forall (fun b => Zlength b = n_bytes) (complete_ends msg sig counter pub nh ni).
Proof.
  intros msg sig counter pub nh ni Hlen HF.
  rewrite Forall_forall in HF.
  assert (Hk : forall b, In b sig -> length b = 16%nat).
  { intros b Hb. specialize (HF b Hb).
    rewrite Zlength_correct, n_bytes_eq in HF. lia. }
  pose proof (Forall_length_complete_ends msg sig counter pub nh ni
                ltac:(rewrite Hlen; reflexivity) Hk) as HL.
  rewrite Forall_forall in HL |- *.
  intros b Hb. rewrite Zlength_correct, (HL b Hb). reflexivity.
Qed.

(** The concatenated tip buffers have exactly [len * n] bytes. *)
Lemma Zlength_concat_chain_tips : forall sk pub nh ni,
  Zlength (concat (chain_tips sk pub nh ni)) = Z.of_nat (len * n).
Proof.
  intros. rewrite Zlength_concat_fixed by apply chain_tips_Forall_Zlength.
  rewrite length_chain_tips. reflexivity.
Qed.

Lemma Zlength_concat_complete_ends : forall msg sig counter pub nh ni,
  length sig = len ->
  Forall (fun b => Zlength b = n_bytes) sig ->
  Zlength (concat (complete_ends msg sig counter pub nh ni)) = Z.of_nat (len * n).
Proof.
  intros msg sig counter pub nh ni Hlen HF.
  rewrite Zlength_concat_fixed
    by (apply complete_ends_Forall_Zlength; assumption).
  rewrite length_complete_ends. reflexivity.
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

(** [derive_sk] reads the address only through its anchor, which is
    exactly what [adrs_struct_eq] preserves. *)
Lemma derive_sk_congr : forall sk pk x a i,
  adrs_struct_eq x a ->
  derive_sk sk pk (anchor_nh x) (anchor_ni x) i
  = derive_sk sk pk (anchor_nh a) (anchor_ni a) i.
Proof. intros sk pk x a i (Hh & Hi). rewrite Hh, Hi. reflexivity. Qed.

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
(** ** The [wc_chain] step law used by the [shrincs_wots_chain_iter] loop.

    [wc_chain_succ] peels the last step at [Z.of_nat (S n)]; the C loop
    counts at [Z], so this is the same law at [j + 1].  (Loop entry is
    [Model.theory.shrincs]'s [wc_chain_0] -- nothing to add here.) *)
Lemma wc_chain_step : forall pk_seed nh ni ci node start j,
  0 <= j ->
  wc_chain pk_seed nh ni ci node start (j + 1)
  = shrincs.F pk_seed (wc_hash_adrs nh ni ci (start + j))
      (wc_chain pk_seed nh ni ci node start j).
Proof.
  intros pk_seed nh ni ci node start j Hj.
  rewrite <- (Z2Nat.id j) by lia.
  replace (Z.of_nat (Z.to_nat j) + 1) with (Z.of_nat (S (Z.to_nat j))) by lia.
  apply wc_chain_succ.
Qed.

(* ================================================================= *)
(** ** The chain-launch address [wc_set_chain] (dependent-union ADRS),
    used by [body_shrincs_wots_pubkey_from_sig]'s completion loop.

    The C completes each chain by writing only the chain-index word
    ([shrincs_adrs_put32 ADRS_CHAIN]) on the residual address left by
    the previous chain -- it never re-zeroes the hash-position word.  So
    the union threaded through the loop carries an arbitrary residual
    position, which [wc_set_chain] overwrites the chain index of.  The
    position is immaterial to the model: [wc_chain] reads only the anchor
    and the chain index. *)

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

(** The chain index [wc_chain] reads back off the launch address is the
    one that was stored ([to_chain32] is value-faithful in range). *)
Lemma wc_set_chain_chain_of : forall ai c,
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  0 <= c < Z.of_nat len ->
  chain_of (wc_set_chain ai (Z.to_nat c)) = c.
Proof.
  intros ai c Ht Hc.
  destruct ai as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht.
  apply to_chain32_val, Hc.
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
    chain's residual address with its chain index reset to [i] -- is the
    model's chain at the base anchor and index [i]: the two addresses
    agree on the caller anchor ([adrs_struct_eq]) and on the chain index,
    and neither the residual position nor anything else is read. *)
Lemma wc_chain_wc_set_chain : forall X st sp pk_seed ai a i,
  adrs_struct_eq ai a ->
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  0 <= i < Z.of_nat len ->
  wc_chain pk_seed (anchor_nh (wc_set_chain ai (Z.to_nat i)))
                   (anchor_ni (wc_set_chain ai (Z.to_nat i)))
                   (chain_of (wc_set_chain ai (Z.to_nat i))) X st sp
  = wc_chain pk_seed (anchor_nh a) (anchor_ni a) i X st sp.
Proof.
  intros X st sp pk_seed ai a i Hse Ht Hi.
  destruct (wc_set_chain_struct_eq ai (Z.to_nat i)) as (Hh & Hn).
  destruct Hse as (Hh' & Hn').
  rewrite Hh, Hn, Hh', Hn', (wc_set_chain_chain_of ai i Ht Hi).
  reflexivity.
Qed.

Lemma complete_block_from_ai : forall sig ds pk_seed ai a i,
  adrs_struct_eq ai a ->
  adrs_type ai = SF_SHRINCS_WOTS_HASH ->
  0 <= i < Z.of_nat len ->
  wc_chain pk_seed (anchor_nh (wc_set_chain ai (Z.to_nat i)))
                   (anchor_ni (wc_set_chain ai (Z.to_nat i)))
                   (chain_of (wc_set_chain ai (Z.to_nat i)))
                   (index_block sig i)
                   (shrincs.index_int ds i)
                   (Z.of_nat w_pred - shrincs.index_int ds i)
  = complete_block sig ds pk_seed a (Z.to_nat i).
Proof.
  intros sig ds pk_seed ai a i Hse Ht Hi.
  unfold complete_block. rewrite Z2Nat.id by lia.
  apply wc_chain_wc_set_chain; assumption.
Qed.

(* ================================================================= *)
(** ** Per-iteration block folds: the loop bodies compute the named
    blocks over the residual address, re-keyed onto the base address. *)

(** One completed loop iteration on a structurally-equal address computes
    the canonical [pkgen_block]: derive the secret, re-type to hash, chain
    [w-1] steps.  Both [derive_sk] and [wc_chain] see the address only
    through its anchor, which [b] shares with [a].  Stated at the [Z]
    chain index the C loop carries, which is what
    [shrincs_wots_chain_from_seed]'s POST hands the body. *)
Lemma iter_eq_pkgen_block : forall sk_seed pk_seed a b i,
  adrs_struct_eq b a ->
  0 <= i ->
  wc_chain pk_seed (anchor_nh b) (anchor_ni b) i
    (derive_sk sk_seed pk_seed (anchor_nh b) (anchor_ni b) i)
    0 (Z.of_nat w_pred)
  = pkgen_block sk_seed pk_seed a (Z.to_nat i).
Proof.
  intros sk_seed pk_seed a b i (Hh & Hn) Hi.
  unfold pkgen_block. rewrite Z2Nat.id by lia.
  rewrite Hh, Hn. reflexivity.
Qed.

(** The [sign_block] sibling of [iter_eq_pkgen_block]: one signing-loop
    iteration chains [ds[i]] steps instead of [w_pred]. *)
Lemma iter_eq_sign_block : forall sk_seed pk_seed a b ds i,
  adrs_struct_eq b a ->
  0 <= i ->
  wc_chain pk_seed (anchor_nh b) (anchor_ni b) i
    (derive_sk sk_seed pk_seed (anchor_nh b) (anchor_ni b) i)
    0 (shrincs.index_int ds i)
  = sign_block sk_seed pk_seed a ds (Z.to_nat i).
Proof.
  intros sk_seed pk_seed a b ds i (Hh & Hn) Hi.
  unfold sign_block. rewrite Z2Nat.id by lia.
  rewrite Hh, Hn. reflexivity.
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
