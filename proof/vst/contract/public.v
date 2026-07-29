(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.public: VST funspecs for the WOTS+C C library.

    Re-exports the tree's model surface ([model.wots], which is the
    spec port [Model.shrincs] plus [Model.theory.shrincs] section 5's
    per-chain views) and wraps it in VST contracts for the four public
    entry points.  Internal helper funspecs live in [contract.helpers].

    The four POSTs below name the PORT's own [wots_c_*] functions at
    [adrs_bytes a] -- the C's 22-byte ADRS, which is what the spec
    hashes.  Section 5's reassembly lemmas ([wots_c_pubkey_gen_tips],
    [wots_c_sign_chains], [wots_c_pubkey_from_sig_ends]) are what each
    body proof rewrites with once, to turn that into the per-chain view
    its loop invariant iterates. *)

From Vst Require Export contract.repr.
From Model Require Import theory.address.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope Z_scope.

(** WOTS+C instantiates [Model.address]'s parametric ADRS at
    [chain_count = len] and [pos_bound = w_pred]; this notation keeps
    every bare [adrs] type mention resolving to [address.adrs len w_pred]. *)
Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** Address-structure equality (WOTS+C anchor preservation). *)

(** Two addresses agree on the caller-prefilled anchor (height/tag +
    8-byte index) that the WOTS+C algorithms leave untouched -- they
    only set the type byte and the payload words. Used as the
    loop-invariant "address prefix" carried through
    [contract.lemmas.chain_blocks]. *)
Definition adrs_struct_eq (a b : adrs) : Prop :=
  adrs_anchor_tag_z a = adrs_anchor_tag_z b
  /\ adrs_anchor_idx_z a = adrs_anchor_idx_z b.

Lemma adrs_struct_eq_refl : forall a, adrs_struct_eq a a.
Proof. intros; repeat split. Qed.

Lemma adrs_struct_eq_sym : forall a b,
  adrs_struct_eq a b -> adrs_struct_eq b a.
Proof. intros a b (?&?); repeat split; symmetry; assumption. Qed.

Lemma adrs_struct_eq_trans : forall a b c,
  adrs_struct_eq a b -> adrs_struct_eq b c -> adrs_struct_eq a c.
Proof. intros a b c (?&?) (?&?); repeat split; congruence. Qed.

(** [set_hash_pos] touches only the WOTS+C position field, hence
    preserves the anchor. *)
Lemma set_hash_pos_struct_eq : forall a p,
  adrs_struct_eq (set_hash_pos a p) a.
Proof. intros a p; destruct a; split; reflexivity. Qed.

(** The named WOTS+C constructors rebuild the typed sibling from [a]'s
    anchor ([adrs_nh]/[adrs_ni]), which is exactly the wire anchor
    ([adrs_nh_tag_z] / [adrs_ni_idx_z]), hence they preserve it. *)
Lemma shrincs_wots_prf_adrs_struct_eq : forall a i,
  adrs_struct_eq (shrincs_wots_prf_adrs a i) a.
Proof.
  intros a i; unfold shrincs_wots_prf_adrs; split; cbn [adrs_anchor_tag_z adrs_anchor_idx_z].
  - apply adrs_nh_tag_z.
  - apply adrs_ni_idx_z.
Qed.

Lemma shrincs_wots_hash_adrs_struct_eq : forall a i,
  adrs_struct_eq (shrincs_wots_hash_adrs w_pred_pos a i) a.
Proof.
  intros a i; unfold shrincs_wots_hash_adrs; split; cbn [adrs_anchor_tag_z adrs_anchor_idx_z].
  - apply adrs_nh_tag_z.
  - apply adrs_ni_idx_z.
Qed.

Lemma shrincs_wots_pk_adrs_struct_eq : forall a,
  adrs_struct_eq (shrincs_wots_pk_adrs a) a.
Proof.
  intros a; unfold shrincs_wots_pk_adrs; split; cbn [adrs_anchor_tag_z adrs_anchor_idx_z].
  - apply adrs_nh_tag_z.
  - apply adrs_ni_idx_z.
Qed.

Lemma shrincs_wots_grind_adrs_struct_eq : forall a,
  adrs_struct_eq (shrincs_wots_grind_adrs a) a.
Proof.
  intros a; unfold shrincs_wots_grind_adrs; split; cbn [adrs_anchor_tag_z adrs_anchor_idx_z].
  - apply adrs_nh_tag_z.
  - apply adrs_ni_idx_z.
Qed.

(* ================================================================= *)
(** ** [rep_lia] hints for WOTS+C parameter constants.

    Register the WOTS+C parameter equalities with [rep_lia] so the solver
    sees [pk_bytes], [sig_bytes], [len] and [constant_sum] as their numeric
    values automatically. (The scheme-neutral widths [n_bytes] / [msg_bytes]
    / [Byte.*] are hinted in [contract.repr].) *)

Lemma pk_bytes_eq         : pk_bytes         = 16.     Proof. reflexivity. Qed.
Lemma sig_bytes_eq        : sig_bytes        = 514.    Proof. reflexivity. Qed.
Lemma len_eq_Z            : Z.of_nat len     = 32.     Proof. reflexivity. Qed.
Lemma constant_sum_eq     : constant_sum     = 240.    Proof. reflexivity. Qed.
Lemma w_pred_eq           : w_pred           = 15%nat. Proof. reflexivity. Qed.

#[export] Hint Rewrite
  pk_bytes_eq sig_bytes_eq len_eq_Z constant_sum_eq
  : rep_lia.

(* ================================================================= *)
(** ** The C-refinement chain-index totalizer.

    [Model.address]'s WOTS+C constructors ([shrincs_wots_hash_adrs] /
    [shrincs_wots_prf_adrs]) take a bound-carrying [fin 32] chain index
    directly (the exact reachable-states model).  The C step functions carry the chain index
    as a plain [nat]/[Z] word with the bound only in the funspec [PROP],
    which is NOT in scope in the funspec POST.  [to_chain32] is the forced
    total [nat -> fin 32] inverse used at this C-refinement boundary --
    value-preserving whenever the index is in range (which every WOTS+C
    caller guarantees: chain index [< chain_count = 32]), saturating to 0
    otherwise.  It is the VST-side sibling of [Sec.addressing.chain_of_nat]
    (the SSProve fold's totalizer); the pure model itself stays clamp-free.

    Value-faithfulness ([to_chain32_val] / [to_chain32_id]) is all the
    bodies need: in range it equals the model's exact [fin_of_nat 32 i _],
    so the byte-level splices go through and the [chain_tips]/[sign_chains]/
    [complete_ends] bridge (below) reconciles against the dependent model. *)

Definition to_chain32 (i : nat) : fin (Z.of_nat len) :=
  match Z_lt_dec (Z.of_nat i) (Z.of_nat len) with
  | left  H => fin_of_nat (Z.of_nat len) i H
  | right _ => fin_of_Z (Z.of_nat len) 0 ltac:(pose proof len_eq_Z; lia)
  end.

Lemma to_chain32_id : forall i (H : Z.of_nat i < Z.of_nat len), to_chain32 i = fin_of_nat (Z.of_nat len) i H.
Proof.
  intros i H. unfold to_chain32. destruct (Z_lt_dec (Z.of_nat i) (Z.of_nat len)) as [H'|H'].
  - apply fin_val_inj. rewrite !fin_val_of_nat. reflexivity.
  - exfalso. exact (H' H).
Qed.

Lemma to_chain32_val : forall c, 0 <= c < Z.of_nat len -> fin_val (to_chain32 (Z.to_nat c)) = c.
Proof.
  intros c Hc. unfold to_chain32.
  destruct (Z_lt_dec (Z.of_nat (Z.to_nat c)) (Z.of_nat len)) as [H'|H'].
  - rewrite fin_val_of_nat, Z2Nat.id by lia. reflexivity.
  - exfalso. apply H'. rewrite Z2Nat.id by lia. lia.
Qed.

(** The position sibling of [to_chain32]: the C-refinement's total
    [nat -> fin 15] inverse for the WOTS+C chain position (chain climbs to
    [w - 1 = 14], so positions are [< 15]).  Used only to describe the
    residual C address after a chain loop ([chain_addr_post]); value-
    faithful whenever the position is in range (which the [start + steps <=
    w_pred] funspec bound guarantees). *)
Definition to_pos15 (p : nat) : fin (Z.of_nat w_pred) :=
  match Z_lt_dec (Z.of_nat p) (Z.of_nat w_pred) with
  | left  H => fin_of_nat (Z.of_nat w_pred) p H
  | right _ => fin_of_Z (Z.of_nat w_pred) 0 ltac:(pose proof w_pred_pos; lia)
  end.

Lemma to_pos15_val : forall p, (p < 15)%nat -> fin_val (to_pos15 p) = Z.of_nat p.
Proof.
  intros p Hp. unfold to_pos15. destruct (Z_lt_dec (Z.of_nat p) (Z.of_nat w_pred)) as [H'|H'].
  - rewrite fin_val_of_nat. reflexivity.
  - exfalso. apply H'. unfold w_pred. lia.
Qed.

(** Bridge from the port's [range]-indexed per-chain views to the plain
    [map (_) (seq 0 k)] the VST loop invariants iterate over.  The port
    indexes at [Z] (the spec's ints are [Z] throughout); the C counts at
    [nat], so every [map f (range 0 (Z.of_nat k))] the model produces is
    the [seq 0 k] map of [f o Z.of_nat].

    This REPLACES the dependent-comprehension bridge the previous model
    needed ([for_idx_dep_map_eq]): the port's loops are plain [map]s, so
    no [i < k] proof is threaded and nothing has to be discharged
    inside. *)
Lemma map_range_seq {A} (k : nat) (f : Z -> A) :
  map f (shrincs.range 0 (Z.of_nat k)) = map (fun i => f (Z.of_nat i)) (seq 0 k).
Proof. rewrite range0_map_of_nat, map_map. reflexivity. Qed.

(** The chain index the C carries in the address's second payload word.
    [wc_chain] takes it as a plain [Z] argument (the port addresses at
    the byte level, so there is no bound to thread); on a WOTS+C hash
    address it IS [payload_b_z]. *)
Notation chain_of a := (payload_b_z a).

(* ================================================================= *)
(** ** Public API funspecs.

    The grinding search ([find_counter] / [find_from], [Model.theory.
    shrincs] section 5.3) is a deterministic loop over counters
    [0, 1, .., c_max - 1] ([c_max = 2^16], the span the spec's own
    [range(2**16)] gives it): it always terminates within that many
    steps and returns either [Some c] (the smallest good counter) or
    [None] (no counter below [c_max] is good).  It is not open-ended or
    possibly-non-terminating -- "grinding failure" just means [None]
    came back, an ordinary (negligible-probability) outcome, not
    divergence.  [shrincs_wots_sign] leaves [addr] in a scratch state
    that depends on which of these two outcomes occurred, so its
    post-condition existentially quantifies it.

    [shrincs_wots_pubkey_from_sig] and [shrincs_wots_verify] do not
    grind -- they each probe a single, caller-supplied [counter] -- so
    their residual address is deterministic and stated exactly:
    [shrincs_wots_pk_adrs a] when the port's [wots_c_pubkey_from_sig]
    accepts that counter (equivalently, when its digest is constant-sum
    -- section 5's [wots_c_pubkey_from_sig_ends] proves the two the
    same under this funspec's own PROP), else [shrincs_wots_grind_adrs
    a].  This is keyed on the PORT's accept/reject, NOT on the C's
    return value: [shrincs_wots_verify] can still return -1 (pk
    mismatch) on an accepted counter, and the address is left pk-typed
    in that case too.  [shrincs_wots_pubkey_gen] does not grind at all
    and ends in the deterministic pk-typed address
    [shrincs_wots_pk_adrs a].

    WHERE THE PORT IS TOTAL AND THE C IS NOT.  [Model.shrincs.
    wots_c_sign] keeps the spec's signature: it has no [None], and
    returns [zeros (2 + WOTS_C_CHAINS_SIZE)] when grinding fails
    (model/PORTING.md's assert/raise table, verdict (4)).  The C
    instead returns -2 and leaves the buffer uninitialised.  So the sign
    POST is keyed on [find_counter] -- the port's own search, section
    5.3 -- and names [wots_c_sign] only on the branch where the spec and
    the C agree.  [wots_c_pubkey_from_sig] IS partial ([option bytes]),
    so from_sig/verify key on it directly.

    CALLER OBLIGATION (clean anchor): [shrincs_wots_sign],
    [shrincs_wots_pubkey_from_sig] and [shrincs_wots_verify] additionally
    require the incoming [a] to be anchor-only -- all three payload words
    ([payload_a_z a = 0], [payload_b_z a = 0], [payload_c_z a = 0]) zero.
    Every real C caller guarantees this (a freshly built, or freshly
    stepped-to, WOTS+C address never carries stale payload bits when
    handed to a public entry point); it is what lets the smart
    constructors ([shrincs_wots_grind_adrs] and friends, in
    [model.address]) retype the address for grinding while still treating
    it as clean. See the per-funspec PROP for the exact hypotheses. *)

(** [clean_anchor a]: the address carries no in-progress chain state --
    all three payload words (keypair/chain index, chain/height, hash/index)
    are zero.  This is the clean-anchor caller obligation documented above,
    packaged as one hypothesis for the public entry points and the grinding
    helpers. *)
Definition clean_anchor (a : adrs) : Prop :=
  payload_a_z a = 0 /\ payload_b_z a = 0 /\ payload_c_z a = 0.

Definition shrincs_wots_pubkey_gen_spec : ident * funspec :=
  DECLARE _shrincs_wots_pubkey_gen
  WITH pk_ptr : val, sk_ptr : val, ps_ptr : val, a_ptr : val,
       sk_seed : block, pk_seed : block, a : adrs,
       sh_pk : share, sh_sk : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_pk; writable_share sh_a;
          readable_share sh_sk; readable_share sh_ps)
    PARAMS (pk_ptr; sk_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_pk (tarray tuchar pk_bytes) pk_ptr;
         data_at sh_sk (tarray tuchar seed_bytes) (block_to_vals sk_seed) sk_ptr;
         data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)        a_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh_pk (tarray tuchar pk_bytes)
           (block_to_vals
              (shrincs.wots_c_pubkey_gen sk_seed pk_seed (adrs_bytes a))) pk_ptr;
         data_at sh_sk (tarray tuchar seed_bytes) (block_to_vals sk_seed) sk_ptr;
         data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals (shrincs_wots_pk_adrs a)) a_ptr).

(** [sig] holds the 2-byte big-endian counter [to_bytes counter 2]
    followed by the [len] chain signatures -- the spec's own flat
    layout, which is what [wots_c_sign] returns whole.  The buffer is
    written only when grinding succeeds ([find_counter ... = Some _]);
    on failure the return is -2 and the buffer is left uninitialised
    (where the port, being total, would return its zero block). *)
Definition shrincs_wots_sign_spec : ident * funspec :=
  DECLARE _shrincs_wots_sign
  WITH sig_ptr : val, msg_ptr : val, sk_ptr : val, ps_ptr : val, a_ptr : val,
       msg : block, sk_seed : block, pk_seed : block, a : adrs,
       sh_sig : share, sh_m : share, sh_sk : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_sig; writable_share sh_a;
          readable_share sh_m; readable_share sh_sk; readable_share sh_ps;
          Zlength msg = msg_bytes; Zlength pk_seed = seed_bytes; Zlength sk_seed = seed_bytes;
          (* clean anchor: caller obligation, see the "Public API funspecs"
             section header above. *)
          clean_anchor a)
    PARAMS (sig_ptr; msg_ptr; sk_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_sig (tarray tuchar sig_bytes) sig_ptr;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_sk (tarray tuchar seed_bytes) (block_to_vals sk_seed)  sk_ptr;
         data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tint ]
    EX a' : adrs,
    PROP ()
    RETURN (Vint (Int.repr
             (match find_counter pk_seed (anchor_nh a) (anchor_ni a) msg with
              | Some _ => 0 | None => -2 end)))
    SEP (match find_counter pk_seed (anchor_nh a) (anchor_ni a) msg with
         | Some _ =>
             data_at sh_sig (tarray tuchar sig_bytes)
               (block_to_vals
                  (shrincs.wots_c_sign msg sk_seed pk_seed (adrs_bytes a))) sig_ptr
         | None => data_at_ sh_sig (tarray tuchar sig_bytes) sig_ptr
         end;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_sk (tarray tuchar seed_bytes) (block_to_vals sk_seed)  sk_ptr;
         data_at sh_ps (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a')        a_ptr).

(** [sig] holds the 2-byte counter followed by [len] chain signatures.
    The candidate pk (a single [n]-byte block) is written exactly when
    the port's [wots_c_pubkey_from_sig] returns [Some] -- i.e. when the
    digest at the counter is constant-sum; otherwise the return is -1
    and pk is left uninitialised. *)
Definition shrincs_wots_pubkey_from_sig_spec : ident * funspec :=
  DECLARE _shrincs_wots_pubkey_from_sig
  WITH pk_ptr : val, sig_ptr : val, msg_ptr : val, ps_ptr : val, a_ptr : val,
       sig : list block, counter : Z, msg : block, pk_seed : block, a : adrs,
       sh_pk : share, sh_sig : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_pk; writable_share sh_a;
          readable_share sh_sig; readable_share sh_m; readable_share sh_ps;
          length sig = len; 0 <= counter < 2 ^ 16;
          Zlength msg = msg_bytes; Zlength pk_seed = seed_bytes;
          Forall (fun b => Zlength b = n_bytes) sig;
          (* clean anchor: caller obligation, see the "Public API funspecs"
             section header above. *)
          clean_anchor a)
    PARAMS (pk_ptr; sig_ptr; msg_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_pk (tarray tuchar pk_bytes) pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes)
           (block_to_vals (shrincs.to_bytes counter 2) ++ blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar msg_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a   t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr
             (match shrincs.wots_c_pubkey_from_sig
                      (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                      msg pk_seed (adrs_bytes a) with
              | Some _ => 0 | None => -1 end)))
    SEP (match shrincs.wots_c_pubkey_from_sig
                 (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                 msg pk_seed (adrs_bytes a) with
         | Some pk => data_at sh_pk (tarray tuchar pk_bytes)
                        (block_to_vals pk) pk_ptr
         | None    => data_at_ sh_pk (tarray tuchar pk_bytes) pk_ptr
         end;
         data_at sh_sig (tarray tuchar sig_bytes)
           (block_to_vals (shrincs.to_bytes counter 2) ++ blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar msg_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a   t_addr
                 (adrs_to_vals
                   (if good_counter pk_seed (anchor_nh a) (anchor_ni a) msg counter
                    then shrincs_wots_pk_adrs a
                    else shrincs_wots_grind_adrs a))
                 a_ptr).

Definition shrincs_wots_verify_spec : ident * funspec :=
  DECLARE _shrincs_wots_verify
  WITH pk_ptr : val, sig_ptr : val, msg_ptr : val, ps_ptr : val, a_ptr : val,
       pk : block, sig : list block, counter : Z, msg : block, pk_seed : block, a : adrs,
       sh_pk : share, sh_sig : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_a;
          readable_share sh_pk; readable_share sh_sig;
          readable_share sh_m; readable_share sh_ps;
          Zlength pk = pk_bytes; length sig = len; 0 <= counter < 2 ^ 16;
          Zlength msg = msg_bytes; Zlength pk_seed = seed_bytes;
          Forall (fun b => Zlength b = n_bytes) sig;
          (* clean anchor: caller obligation, see the "Public API funspecs"
             section header above. *)
          clean_anchor a)
    PARAMS (pk_ptr; sig_ptr; msg_ptr; ps_ptr; a_ptr)
    SEP (data_at sh_pk  (tarray tuchar pk_bytes)  (block_to_vals pk)  pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes)
           (block_to_vals (shrincs.to_bytes counter 2) ++ blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar msg_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a   t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr
             (if wc_verify pk (shrincs.to_bytes counter 2 ++ shrincs.concat sig)
                    msg pk_seed (adrs_bytes a)
              then 0 else -1)))
    SEP (data_at sh_pk  (tarray tuchar pk_bytes)  (block_to_vals pk)  pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes)
           (block_to_vals (shrincs.to_bytes counter 2) ++ blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar msg_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar seed_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a   t_addr
                 (adrs_to_vals
                   (if good_counter pk_seed (anchor_nh a) (anchor_ni a) msg counter
                    then shrincs_wots_pk_adrs a
                    else shrincs_wots_grind_adrs a))
                 a_ptr).
