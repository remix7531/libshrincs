(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.wots: WOTS+C -- types, primitives, and algorithms.

    The WOTS+C (grinding / constant-sum Winternitz) one-time signature as
    used for the SHRINCS stateful (FXMSS) leaf.  Every tweakable hash is
    SHA-256 truncated to [n = 16] bytes over [pk_seed || zeros(48) || ADRS
    || M]; there are no bitmasks.  Instead of a Winternitz checksum,
    signing grinds a 16-bit counter until the message digest maps to
    [len = 32] base-[w] digits summing to [constant_sum = 240]; the
    counter is prepended to the signature.

    This is the shared, Stdlib-only ground-truth model for WOTS+C: the
    VST tree bridges its C-refinement proof to it directly, and the
    SSProve tree's headline theorem is instantiated against it (see
    proof/ssprove/axioms.v and theorem.v's PRF-keyed
    instantiation). Its address handling comes from [Model.address]
    (the full shrincs-bip ADRS space) rather than a WOTS+C-only local
    record.

    Definitions only -- no lemmas.  Facts about these definitions
    (search-correctness, [sign_inv], etc.) live in [model.wots_facts]
    instead, so "what WOTS+C computes" and "why the computation has
    property X" stay in separate files.

    Reference: shrincs-bip/impl/shrincs.py (the authoritative spec).
    Deliberate deviation from a literal transcription: [PRF]'s argument
    order is [pk_seed -> ADRS -> sk_seed] (pp, address, payload),
    matching [F]/[T_sf]/[H_grind] and the SSProve tree's own hash
    [Context] convention, rather than the spec's literal
    [PRF(pk_seed, sk_seed, ADRS)] (ADRS last) -- see
    [proof/ssprove/wots/hop/prf.v]'s header, which documents the spec's
    order as "a byte-level instantiation detail."

    The top-level algorithms ([shrincs_wots_pubkey_gen], [shrincs_wots_sign],
    [shrincs_wots_pubkey_from_sig], [shrincs_wots_verify]) at the bottom of this file
    mirror the shrincs.py [wots_c_*] functions (this repo's own naming;
    shrincs-bip's reference implementation is a separate, unaffected repo
    and keeps its own naming). *)

From Stdlib Require Import List ZArith Lia.
From Shrincs.internal.common Require Export address sha256 iteration.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** SHRINCS WOTS+C parameters. *)

Definition n     : nat := 16.   (** hash output = [sha256(...)[:16]] *)
Definition w     : Z   := 16.   (** Winternitz radix *)
Definition len   : nat := 32.   (** chain count (= number of digits) *)

(** [w - 1] as a [nat] (chain-step count). *)
Definition w_pred : nat := 15.

(** WOTS+C instantiates [Model.address]'s parametric ADRS at
    [chain_count = len] and [pos_bound = w_pred].  This notation keeps
    every [adrs] type mention in this file resolving to the fully
    applied [address.adrs len w_pred] (the parameters are otherwise
    explicit on the type constructor). *)
Local Abbreviation adrs := (address.adrs len w_pred).

(** Positivity of the instantiated position bound -- discharges the
    [0 < pos_bound] side condition of [shrincs_wots_hash_adrs]. *)
Lemma w_pred_pos : (0 < w_pred)%nat.
Proof. unfold w_pred; lia. Qed.

(** WOTS+C grinding parameters.  A valid counter maps the message to
    [len] base-[w] digits summing to [constant_sum = floor(len*(w-1)/2)
    = 240]; the counter is a 16-bit field, so grinding is bounded by
    [c_max = 2^16]. *)
Definition constant_sum : nat := 240.
Definition c_max    : Z   := 2 ^ 16.

Definition pk_bytes  : Z := Z.of_nat n.               (* 16 = single T_sf hash *)
Definition sig_bytes : Z := 2 + Z.of_nat (len * n).   (* 514 = 2-byte counter ++ chains *)

(* ================================================================= *)
(** ** [block]: a byte string ([Model.sha256]'s), [zero_block]/
    [trunc16]/[zeros] specialized to WOTS+C's width [n = 16]. *)

Definition zero_block : block := repeat zero_byte n.
#[global] Instance default_block : Default block := zero_block.

(* ================================================================= *)
(** ** The tweakable hashes.

    [SHA256] ([Model.sha256]) outputs [hash_bytes = 32] bytes; the
    tweakable hashes truncate to [n = 16]. *)

Definition zeros (k : nat) : block := repeat zero_byte k.
Definition trunc16 (b : block) : block := firstn n b.

(** [SHA256], unwrapped back to plain [block] on both ends: every
    [thash]/[H_grind] input in this file is a handful of fixed-width
    pieces (well under [sha256_max_input_len]), so callers keep
    passing plain [list byte] instead of threading a length invariant
    through the whole model; [BList.clip] never actually truncates
    anything a real call here produces (see [Model.sha256]'s header
    comment). *)
Definition sha256' (input : block) : block :=
  Vec.to_list (SHA256 (BList.clip sha256_max_input_len ltac:(unfold sha256_max_input_len; lia) input)).

(** The SHRINCS tweakable hash:
    [thash pk_seed ADRS M = SHA256(pk_seed || zeros(48) || ADRS || M)[:16]].
    [F] (chain step), [PRF] (secret derivation) and [T_sf] (tip
    compression) are the same construction; only [M] and the ADRS type
    byte differ. *)
Definition thash (pk_seed : block) (ADRS : adrs) (M : block) : block :=
  trunc16 (sha256' (pk_seed ++ zeros 48 ++ adrs_bytes ADRS ++ M)).

Definition F (pk_seed : block) (ADRS : adrs) (M : block) : block :=
  thash pk_seed ADRS M.

Definition PRF (pk_seed : block) (ADRS : adrs) (sk_seed : block) : block :=
  thash pk_seed ADRS sk_seed.

Definition T_sf (pk_seed : block) (ADRS : adrs) (Ml : block) : block :=
  thash pk_seed ADRS Ml.

(** WOTS+C grinding hash.  Hashes [pk_seed], the first 10 bytes of the
    grind-typed ADRS (height + index + type), the 32-byte message digest,
    four zero bytes, and the 16-bit counter, truncated to [n]:
    [H_grind = SHA256(pk_seed || zeros(48) || ADRS[0..10) || M
                      || zeros(4) || to_byte(counter,2))[:16]]. *)
Definition H_grind (pk_seed : block) (ADRS : adrs) (M : block) (counter : Z) : block :=
  trunc16 (sha256' (pk_seed ++ zeros 48 ++ firstn 10 (adrs_bytes ADRS)
                   ++ M ++ zeros 4 ++ to_byte counter 2)).

(* ================================================================= *)
(** ** Winternitz chaining. *)

(** Bound obligations for the dependent [chain_iter] below, factored
    out as named lemmas: an [ltac:(lia)] inside the Fixpoint term cannot
    see the match-bound hypothesis, so the position / recursion proofs
    are supplied by these. *)

(** At step [S k] under [i + S k <= w_pred = 15], the source position
    [i + k] is [< 15] -- so [set_hash_pos] receives a real [fin 15]. *)
Lemma chain_iter_pos_lt (i k : nat) (H : (i + S k <= w_pred)%nat) : Z.of_nat (i + k) < Z.of_nat w_pred.
Proof. unfold w_pred in H |- *. lia. Qed.

(** The recursive call's bound [i + k <= w_pred] follows from
    [i + S k <= w_pred]. *)
Lemma chain_iter_rec_le (i k : nat) (H : (i + S k <= w_pred)%nat) : (i + k <= w_pred)%nat.
Proof. lia. Qed.

(** [shrincs_wots_chain_iter X i s pk_seed ADRS Hs]: iterate the
    tweakable hash [F] on [X] for [s] steps, with the ADRS position
    field set to [i], [i+1], ..., [i+s-1] in turn (via
    [Model.address.set_hash_pos]).  The ADRS must already carry the
    WOTS+C chain type / index; only the position varies.  The step
    bound [Hs : i + s <= w_pred] is threaded so every position field is
    a real [fin 15] -- no clamp, exactly reachable-states.  It is
    proof-irrelevant ([Peano_dec.le_unique]), so the result does not
    depend on which proof is supplied (see [chain_iter_pirr] in
    [model.correct]). *)
Fixpoint shrincs_wots_chain_iter (X : block) (i s : nat)
               (pk_seed : block) (ADRS : adrs) {struct s}
  : (i + s <= w_pred)%nat -> block :=
  match s return (i + s <= w_pred)%nat -> block with
  | O    => fun _  => X
  | S k  => fun Hs =>
      F pk_seed (set_hash_pos ADRS (fin_of_nat (Z.of_nat w_pred) (i + k) (chain_iter_pos_lt i k Hs)))
        (shrincs_wots_chain_iter X i k pk_seed ADRS (chain_iter_rec_le i k Hs))
  end.

(* ================================================================= *)
(** ** [base_2b] specialised to [w = 16].

    Splits each byte into its high and low nibble (MSB-first), then keeps
    the first [out_len] nibbles. *)

Definition base_2b (X : list byte) (out_len : nat) : list nat :=
  firstn out_len
    (flat_map (fun b : byte => [Z.to_nat (b / 16); Z.to_nat (b mod 16)]) X).

(* ================================================================= *)
(** ** Pseudorandom per-chain secret key.

    [sk[i] = PRF(pk_seed, ADRS')] where [ADRS'] is typed for the
    WOTS+C PRF with chain address [i], zero reserved + hash. *)

Definition shrincs_wots_derive_sk (chain : fin (Z.of_nat len)) (sk_seed pk_seed : block) (ADRS : adrs) : block :=
  PRF pk_seed (shrincs_wots_prf_adrs ADRS chain) sk_seed.

(* ================================================================= *)
(** ** WOTS+C grinding: message -> constant-sum digit vector.

    [digest_of pk_seed ADRS M counter] is the [len] base-[w] digits of the
    grinding hash at counter [counter] (grind-typing applied inside, as in
    the C [shrincs_wots_map_digest]).  A counter is [good] when its digit vector
    is [valid], i.e. sums to [constant_sum].  [find_counter] is the
    fuel-bounded linear search for the SMALLEST good counter below
    [c_max]. *)

Definition digest_of (pk_seed : block) (ADRS : adrs) (M : block) (counter : Z)
  : list nat :=
  base_2b (H_grind pk_seed (shrincs_wots_grind_adrs ADRS) M counter) len.

Definition valid_digest (ds : list nat) : bool :=
  Nat.eqb (list_sum ds) constant_sum.

Definition good_counter (pk_seed : block) (ADRS : adrs) (M : block) (counter : Z)
  : bool :=
  valid_digest (digest_of pk_seed ADRS M counter).

(** Fuel-bounded search over [c, c+1, ..., c+fuel-1] for the first good
    counter. *)
Fixpoint find_from (pk_seed : block) (ADRS : adrs) (M : block)
                   (fuel : nat) (c : Z) : option Z :=
  match fuel with
  | O    => None
  | S f  => if good_counter pk_seed ADRS M c
            then Some c
            else find_from pk_seed ADRS M f (c + 1)
  end.

Definition find_counter (pk_seed : block) (ADRS : adrs) (M : block) : option Z :=
  find_from pk_seed ADRS M (Z.to_nat c_max) 0.

(* ================================================================= *)
(** ** Digit / chain-index bounds (needed to build the chains EXACTLY).

    The dependent [chain_iter] requires [start + steps <= w_pred] and
    every chain-index field requires [< 32]; for signing / verification
    the step count is a message digit, so we need each digit
    [<= w_pred = 15].  Digits come off a truncated SHA-256 (via
    [base_2b]), so the bound is unconditional -- no hypothesis on [M].
    These facts live HERE, not in [model.theory.wots], because
    [sign_chains] / [complete_ends] below consume them at DEFINITION
    time (to discharge the dependent [chain_iter] / [fin_of_nat]
    obligations) -- the dependent types make a handful of bound lemmas
    unavoidable in this file. *)

(** Every nibble [base_2b] produces is [<= 15] (a [byte] is [< 256], so
    both its high and low nibble are [< 16]). *)
Lemma base_2b_le_15 : forall X k x, In x (base_2b X k) -> (x <= 15)%nat.
Proof.
  intros X k x Hin. unfold base_2b in Hin.
  assert (Hin' : In x (flat_map
    (fun b : byte => [Z.to_nat (b / 16); Z.to_nat (b mod 16)]) X)).
  { rewrite <- (firstn_skipn k
      (flat_map (fun b : byte =>
        [Z.to_nat (b / 16); Z.to_nat (b mod 16)]) X)).
    apply in_or_app. left. exact Hin. }
  rewrite in_flat_map in Hin'.
  destruct Hin' as [b [Hb Hx]].
  pose proof (byte_val_range b) as HX.
  destruct Hx as [Hx|[Hx|[]]]; subst.
  - assert (H1 : 0 <= b / 16 < 16)
      by (split; [apply Z.div_pos; lia
                 |apply Z.div_lt_upper_bound; lia]).
    change 15%nat with (Z.to_nat 15).
    apply Z2Nat.inj_le; lia.
  - pose proof (Z.mod_pos_bound b 16 ltac:(lia)) as H2.
    change 15%nat with (Z.to_nat 15).
    apply Z2Nat.inj_le; lia.
Qed.

(** Every digit of [digest_of] is [<= 15]; read off a truncated hash, so
    no hypothesis on [M]. *)
Lemma nth_digest_of_le_15 : forall pk_seed ADRS M counter i,
  (nth i (digest_of pk_seed ADRS M counter) 0%nat <= 15)%nat.
Proof.
  intros pk_seed ADRS M counter i.
  destruct (Nat.lt_ge_cases i (length (digest_of pk_seed ADRS M counter)))
    as [Hi|Hi]; [|rewrite nth_overflow by lia; lia].
  pose proof (nth_In _ 0%nat Hi) as Hin.
  unfold digest_of in Hin.
  eapply base_2b_le_15; exact Hin.
Qed.

(** [i < len] gives the chain-index bound [Z.of_nat i < 32]. *)
Lemma chain_idx_lt (i : nat) (Hi : (i < len)%nat) : Z.of_nat i < Z.of_nat len.
Proof. lia. Qed.

(** A full chain runs [w_pred] steps from position 0. *)
Lemma full_chain_bound : (0 + w_pred <= w_pred)%nat.
Proof. lia. Qed.

(** Signing chain [i]: [ds[i]] steps from position 0 ([ds[i] <= w_pred]). *)
Lemma sign_chain_bound : forall pk_seed ADRS M counter i,
  (0 + nth i (digest_of pk_seed ADRS M counter) 0%nat <= w_pred)%nat.
Proof. intros. pose proof (nth_digest_of_le_15 pk_seed ADRS M counter i). unfold w_pred. lia. Qed.

(** Completing chain [i]: from [ds[i]] to [w_pred] ([ds[i] <= w_pred]). *)
Lemma complete_chain_bound : forall pk_seed ADRS M counter i,
  (nth i (digest_of pk_seed ADRS M counter) 0%nat
    + (w_pred - nth i (digest_of pk_seed ADRS M counter) 0%nat) <= w_pred)%nat.
Proof. intros. pose proof (nth_digest_of_le_15 pk_seed ADRS M counter i). unfold w_pred. lia. Qed.

(* ================================================================= *)
(** ** WOTS+C algorithms.

    [shrincs_wots_pubkey_gen] chains every secret to [w-1] and T_sf-compresses
    the [len] tips to a single [n]-byte public key.  [shrincs_wots_sign] grinds
    for a good counter, then chains each secret up to its digit; it is
    partial ([None] on grinding failure) and returns the winning counter
    alongside the chain signatures.  [shrincs_wots_pubkey_from_sig] completes
    each chain using the digest recomputed at the signature's counter --
    no re-grinding -- and T_sf-compresses; [shrincs_wots_verify] additionally
    rejects unless the digest is [valid]. *)

(** The [len] chain tips: each secret [shrincs_wots_derive_sk i] chained to [w - 1].
    [for_idx_dep] hands the body [i < len], from which [chain_idx_lt]
    builds the [fin 32] chain index exactly (no clamp). *)
Definition chain_tips (sk_seed pk_seed : block) (ADRS : adrs) : list block :=
  for i in range len as Hi {{
    shrincs_wots_chain_iter
      (shrincs_wots_derive_sk (fin_of_nat (Z.of_nat len) i (chain_idx_lt i Hi)) sk_seed pk_seed ADRS)
      0 w_pred pk_seed
      (shrincs_wots_hash_adrs w_pred_pos ADRS (fin_of_nat (Z.of_nat len) i (chain_idx_lt i Hi)))
      full_chain_bound }}.

(** WOTS+C public key: T_sf of the concatenated chain tips. *)
Definition shrincs_wots_pubkey_gen (sk_seed pk_seed : block) (ADRS : adrs) : block :=
  T_sf pk_seed (shrincs_wots_pk_adrs ADRS) (concat (chain_tips sk_seed pk_seed ADRS)).

(** The [len] chain signatures for digest [ds] at base address [ADRS]. *)
Definition sign_chains (M sk_seed pk_seed : block) (ADRS : adrs) (counter : Z)
  : list block :=
  let ds := digest_of pk_seed ADRS M counter in
  for i in range len as Hi {{
    shrincs_wots_chain_iter
      (shrincs_wots_derive_sk (fin_of_nat (Z.of_nat len) i (chain_idx_lt i Hi)) sk_seed pk_seed ADRS)
      0 ds[i] pk_seed
      (shrincs_wots_hash_adrs w_pred_pos ADRS (fin_of_nat (Z.of_nat len) i (chain_idx_lt i Hi)))
      (sign_chain_bound pk_seed ADRS M counter i) }}.

(** WOTS+C signing: grind, then sign the digits.  [None] on grinding
    failure (negligible probability). *)
Definition shrincs_wots_sign (M sk_seed pk_seed : block) (ADRS : adrs)
  : option (list block * Z) :=
  match find_counter pk_seed ADRS M with
  | None         => None
  | Some counter => Some (sign_chains M sk_seed pk_seed ADRS counter, counter)
  end.

(** The [len] completed chain tips recovered from a signature: complete
    each chain from [ds[i]] to [w - 1]. *)
Definition complete_ends (M : block) (sig : list block) (counter : Z)
                         (pk_seed : block) (ADRS : adrs) : list block :=
  let ds := digest_of pk_seed ADRS M counter in
  for i in range len as Hi {{
    shrincs_wots_chain_iter sig[i] ds[i] (w_pred - ds[i])%nat pk_seed
      (shrincs_wots_hash_adrs w_pred_pos ADRS (fin_of_nat (Z.of_nat len) i (chain_idx_lt i Hi)))
      (complete_chain_bound pk_seed ADRS M counter i) }}.

(** WOTS+C candidate public key from a signature: T_sf of the completed
    tips. *)
Definition shrincs_wots_pubkey_from_sig (M : block) (sig : list block) (counter : Z)
                     (pk_seed : block) (ADRS : adrs) : block :=
  T_sf pk_seed (shrincs_wots_pk_adrs ADRS) (concat (complete_ends M sig counter pk_seed ADRS)).

(** Signature verification -- accept iff the digest at [counter] is valid
    (constant-sum gate) and [shrincs_wots_pubkey_from_sig] recovers [pk]. *)
Definition shrincs_wots_verify (pk : block) (sig : list block) (M : block) (counter : Z)
                  (pk_seed : block) (ADRS : adrs) : bool :=
  valid_digest (digest_of pk_seed ADRS M counter)
  && (if list_eq_dec byte_eq_dec (shrincs_wots_pubkey_from_sig M sig counter pk_seed ADRS) pk
      then true else false).
