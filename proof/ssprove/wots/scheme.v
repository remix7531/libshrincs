(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.scheme

    WOTS+C (Compressed WOTS+), the stateful one-time signature scheme,
    as a [sig_scheme] with a pure correctness lemma.  Definitions and
    correctness only; the security proof lives in the surrounding
    files.

    Building blocks ([Sec.wots.params] carries them as record fields;
    letter key in that file's header):
    - [wcp_F]      chain hash, called on SF_SHRINCS_WOTS_HASH (type 16)
               addresses (F : B^n x B^288 x B^n -> B^n);
    - [wcp_T_sf]   public-key compression T_sf, called on the
               SF_SHRINCS_WOTS_PK (type 17) address (T_sf : B^n x B^288
               x B^{ln} -> B^n); the chain_count chain ends are modeled as a
               [seq N]; at the games layer this is a thf with
               th_M := 'list N;
    - [wcp_H_grind] grinding hash, called on the SF_SHRINCS_WOTS_GRIND (type 22)
               address (H_grind : B^n x B^288 x B^{2n} x B^{8c}
               -> B^n); at the games layer th_M := M × 'nat (message,
               counter) and th_N := 'nat — the n-byte digest is
               modeled as a [nat], parsed into base-w digits by
               [encoding.digits_w] (same data as parsing the byte
               string in base w).

    Parameters: everything lives in ONE record value [P : wc_params]
    ([Sec.wots.params]) -- the Winternitz parameter [wcp_w], the chain
    count [wcp_chain_count] (= ceil(n / log w)), the target chain-sum
    [wcp_constant_sum] (0 <= constant_sum <= chain_count(w-1)), the
    grinding-counter bound [wcp_c_max] (the counter is an 8c-bit value,
    so c_max = 2^{8c}; bounded search as in Sec.lib.games.stcrp), and
    the imaginary-tree anchor [(wcp_zstar, wcp_istar)]: the node-height
    and node-index fields of all this instance's addresses.  The
    instance addresses themselves ([grind_adrs P], [chain_adrs P],
    [pk_adrs P], [prf_adrs P]) are params.v definitions.

    Modeling choices (documented deviations):
    - The chain_count secret chain starts are SAMPLED ([sample_seq dN chain_count]) rather
      than derived from SKseed via PRF_f on WOTS_PRF_SF addresses; the
      PRF_f derivation and the game hop replacing it by true
      randomness belong to the surrounding tree layer, so this scheme
      starts from ideal keys.  Hence Sk = (PKseed, chain starts)
      instead of (PKseed, SKseed, ADRS).
    - Pk = (PKseed, compressed pk); a full PK also carries ADRS, which
      here is the instance anchor (z_star, i_star).
    - Grinding failure: if no counter below [c_max] satisfies the
      digit-sum predicate, [find_counter] is None and [sign] refuses
      (option signing of Sec.lib.sig.scheme; no loops in packages).
      [find_counter] is a pure function, so the counter iteration is
      always the same by construction.
    - Verification recomputes the digest at the SIGNATURE's counter —
      no re-grinding — rejects unless its digit sum is constant_sum, then
      completes each chain and recompresses, comparing with pk.  We
      additionally check [size sg == chain_count] (sigma is exactly chain_count chain
      values) and [wf_digits] (automatic for recomputed digests
      whenever 0 < w, by [wf_digits_w]).
    - One-time scheme: [sign] returns the key unchanged (the EU-CMA
      statement uses signing budget q_s = 1). *)

From Sec.lib Require Import prelude sig.scheme toolkit.sample_seq chain.core wots.wotsc.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Sec Require Import addressing.
From Sec.wots Require Import addressing.
From Sec.wots Require Export params.
From Stdlib Require Import Bool.

Import PackageNotation.
#[local] Open Scope package_scope.

Section WOTSCScheme.

(** The WOTS+C parameter record (see Sec.wots.params). *)
Context (P : wc_params).

(** Every definition below is a DEFINITIONAL instance of the one generic
    WOTS+C construction [Sec.lib.wots.wotsc], at this record's building
    blocks, this instance's three addresses, and MSB-first digit order
    ([dig_msb := true]).  The FXMSS tree's [SHRINCS.wotsc.scheme] is the
    same construction at [dig_msb := false]; there is exactly one
    [sig_scheme] behind both. *)

(* ------------------------------------------------------------------ *)
(** ** Grinding

    Pure bounded search, the STCRP modeling: the digest at counter [c]
    is decoded into [chain_count] base-w digits, and [find_counter] returns the
    SMALLEST counter below [c_max] whose digit sum is [constant_sum] (an
    unbounded iteration ctr = 0, 1, 2, ... bounded by [c_max]). *)

(** Base-w digit vector of the digest at counter [c], MOST-SIGNIFICANT
    digit first (d parsed as (a_1, ..., a_l) with a_1 the top digit) --
    the same reading order as shrincs.py's base-w parse and
    [Model.wots.base_2b], so the games<->model correspondence
    (Sec.wots.model_bridge) is a plain equality. *)
Definition digest_of (pp : wcp_PP P) (m : wcp_M P) (c : nat) : seq nat :=
  wotsc_digest_of (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_M P) (wc_adrs P)
    (wcp_H_grind P) (grind_adrs P) true pp m c.

(** The post-grinding digest space: well-formed digits summing to the
    target (sum_i a_i = constant_sum). *)
Definition valid_digest (ds : seq nat) : bool :=
  wotsc_valid_digest (wcp_w P) (wcp_constant_sum P) ds.

Definition good_counter (pp : wcp_PP P) (m : wcp_M P) (c : nat) : bool :=
  wotsc_good_ctr (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_M P) (wc_adrs P)
    (wcp_H_grind P) (wcp_constant_sum P) (grind_adrs P) true pp m c.

Definition find_counter (pp : wcp_PP P) (m : wcp_M P) : option nat :=
  wotsc_find_ctr (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_M P) (wc_adrs P)
    (wcp_H_grind P) (wcp_constant_sum P) (wcp_c_max P) (grind_adrs P) true pp m.

Lemma size_digest_of pp m c : size (digest_of pp m c) = wcp_chain_count P.
Proof. exact: wotsc_size_digest_of. Qed.

Lemma find_counterP pp m c :
  find_counter pp m = Some c -> good_counter pp m c && (c < wcp_c_max P).
Proof. exact: wotsc_find_ctrP. Qed.

Lemma find_counter_good pp m c : find_counter pp m = Some c -> good_counter pp m c.
Proof. by move=> /find_counterP /andP[h _]. Qed.

Lemma find_counter_lt pp m c : find_counter pp m = Some c -> c < wcp_c_max P.
Proof. by move=> /find_counterP /andP[_ h]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

(** Chain step of the [i]-th chain: the (total, clamp-free) chain
    address at position [p].  Every fold ever reaches only positions
    [< w.-1], where [chain_adrs P] is the exact address.

    Per-hash-call tweak distinctness lives at the tweak level
    ([params.chain_tweak_inj]): the chain tweak carries its
    [(chain, position)] indices untruncated.  Cross-class distinctness
    (chain vs pk vs grind addresses) follows from [encode_tweak_inj]
    plus the distinct type bytes of the underlying [Model.address]
    constructors. *)
Definition chainf (pp : wcp_PP P) (i : nat) : nat -> wcp_N P -> wcp_N P :=
  wotsc_chainf (wcp_PP P) (wcp_N P) (wc_adrs P) (wcp_F P) (chain_adrs P) pp i.

(** Chain ends: the [i]-th component is the end (position w-1) of the
    [i]-th chain from the [i]-th secret
    (pk_i = c^{0, w-1}(sk_i, i, PKseed, ADRS^h)). *)
Definition chain_ends (pp : wcp_PP P) (xs : seq (wcp_N P)) : seq (wcp_N P) :=
  wotsc_chain_ends (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wc_adrs P)
    (wcp_F P) (chain_adrs P) pp xs.

(** Compressed public key
    (pk = T_sf(PKseed, ADRS^pk, pk_1 || ... || pk_l)). *)
Definition shrincs_wots_pubkey (pp : wcp_PP P) (xs : seq (wcp_N P)) : wcp_N P :=
  wotsc_pubkey (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wc_adrs P)
    (wcp_F P) (wcp_T_sf P) (pk_adrs P) (chain_adrs P) pp xs.

(** Signature chain values for digit vector [ds]
    (sigma_i = c^{0, a_i}(sk_i, i, PKseed, ADRS^h)). *)
Definition sign_chains (pp : wcp_PP P) (xs : seq (wcp_N P)) (ds : seq nat) : seq (wcp_N P) :=
  wotsc_sign_chains (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wc_adrs P)
    (wcp_F P) (chain_adrs P) pp xs ds.

(** Verifier-side chain completion
    (c^{a_i, w-1-a_i}(sigma_i, i, PKseed, ADRS^h)). *)
Definition complete_ends (pp : wcp_PP P) (ds : seq nat) (ys : seq (wcp_N P)) : seq (wcp_N P) :=
  wotsc_complete_ends (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wc_adrs P)
    (wcp_F P) (chain_adrs P) pp ds ys.

(** Verification: recompute the digest at the signature's counter,
    reject unless it lies in the post-grinding digest space, complete
    the chains, recompress, compare with pk.  A signature is (chain
    values, counter). *)
Definition shrincs_wots_verify (pp : wcp_PP P) (root : wcp_N P) (m : wcp_M P)
    (sg : seq (wcp_N P) * nat) : bool :=
  wotsc_verify (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wcp_M P) (wc_adrs P)
    (wcp_F P) (wcp_T_sf P) (wcp_H_grind P) (wcp_constant_sum P)
    (grind_adrs P) (pk_adrs P) (chain_adrs P) true pp root m sg.

(** Signing as a pure partial function: grind, then sign the digits;
    None on grinding failure (sign refusal). *)
Definition shrincs_wots_sign (pp : wcp_PP P) (xs : seq (wcp_N P)) (m : wcp_M P)
    : option (seq (wcp_N P) * nat) :=
  wotsc_sign (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wcp_M P) (wc_adrs P)
    (wcp_F P) (wcp_H_grind P) (wcp_constant_sum P) (wcp_c_max P)
    (grind_adrs P) (chain_adrs P) true pp xs m.

Lemma shrincs_wots_sign_None pp xs m : find_counter pp m = None -> shrincs_wots_sign pp xs m = None.
Proof. by rewrite /shrincs_wots_sign /wotsc_sign -/(find_counter pp m) => ->. Qed.

Lemma shrincs_wots_sign_Some pp xs m c :
  find_counter pp m = Some c ->
  shrincs_wots_sign pp xs m = Some (sign_chains pp xs (digest_of pp m c), c).
Proof. by rewrite /shrincs_wots_sign /wotsc_sign -/(find_counter pp m) => ->. Qed.

(* ------------------------------------------------------------------ *)
(** ** Definitional views

    Each wrapper above is a [wotsc_*] application; these restate its
    body in the pre-merge form.  All are [Proof. by []. Qed.] --- pure
    conversion --- and exist so that proof scripts can [rewrite fooE]
    instead of [rewrite /foo] and stay independent of how many delta
    steps separate a name from its body. *)

Lemma digest_of_def pp m c :
  digest_of pp m c
  = rev (digits_w (wcp_w P) (wcp_chain_count P) (wcp_H_grind P pp (grind_adrs P) (m, c))).
Proof. by []. Qed.

Lemma valid_digest_def ds :
  valid_digest ds = wf_digits (wcp_w P) ds && (sumn ds == wcp_constant_sum P).
Proof. by []. Qed.

Lemma good_counter_def pp m c : good_counter pp m c = valid_digest (digest_of pp m c).
Proof. by []. Qed.

Lemma find_counter_def pp m :
  find_counter pp m = ohead [seq c <- iota 0 (wcp_c_max P) | good_counter pp m c].
Proof. by []. Qed.

Lemma chainf_def pp i p x : chainf pp i p x = wcp_F P pp (chain_adrs P i p) x.
Proof. by []. Qed.

Lemma chain_ends_def pp xs :
  chain_ends pp xs
  = [seq chain (chainf pp ix.1) ix.2 0 (wcp_w P).-1
    | ix <- zip (iota 0 (wcp_chain_count P)) xs].
Proof. by []. Qed.

Lemma shrincs_wots_pubkey_def pp xs :
  shrincs_wots_pubkey pp xs = wcp_T_sf P pp (pk_adrs P) (chain_ends pp xs).
Proof. by []. Qed.

Lemma sign_chains_def pp xs ds :
  sign_chains pp xs ds
  = [seq chain (chainf pp ixd.1.1) ixd.1.2 0 ixd.2
    | ixd <- zip (zip (iota 0 (wcp_chain_count P)) xs) ds].
Proof. by []. Qed.

Lemma complete_ends_def pp ds ys :
  complete_ends pp ds ys
  = [seq chain (chainf pp q.1) q.2.2 q.2.1 ((wcp_w P).-1 - q.2.1)
    | q <- zip (iota 0 (wcp_chain_count P)) (zip ds ys)].
Proof. by []. Qed.

Lemma shrincs_wots_verify_def pp root m sg :
  shrincs_wots_verify pp root m sg
  = [&& valid_digest (digest_of pp m sg.2), size sg.1 == wcp_chain_count P
      & wcp_T_sf P pp (pk_adrs P) (complete_ends pp (digest_of pp m sg.2) sg.1) == root].
Proof. by []. Qed.

Lemma shrincs_wots_sign_def pp xs m :
  shrincs_wots_sign pp xs m
  = omap (fun c => (sign_chains pp xs (digest_of pp m c), c)) (find_counter pp m).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Size sanity lemmas *)

Lemma size_chain_ends pp xs : size (chain_ends pp xs) = minn (wcp_chain_count P) (size xs).
Proof. exact: wotsc_size_chain_ends. Qed.

Lemma size_chain_ends_l pp xs :
  size xs = wcp_chain_count P -> size (chain_ends pp xs) = wcp_chain_count P.
Proof. by move=> hxs; rewrite size_chain_ends hxs minnn. Qed.

Lemma size_sign_chains pp xs ds :
  size (sign_chains pp xs ds) = minn (minn (wcp_chain_count P) (size xs)) (size ds).
Proof. exact: wotsc_size_sign_chains. Qed.

Lemma size_sign_chains_l pp xs ds :
  size xs = wcp_chain_count P -> size ds = wcp_chain_count P ->
  size (sign_chains pp xs ds) = wcp_chain_count P.
Proof. by move=> hxs hds; rewrite size_sign_chains hxs hds !minnn. Qed.

Lemma size_complete_ends pp ds ys :
  size (complete_ends pp ds ys) = minn (wcp_chain_count P) (minn (size ds) (size ys)).
Proof. exact: wotsc_size_complete_ends. Qed.

(* ------------------------------------------------------------------ *)
(** ** Correctness *)

(** Pointwise core, generalized over the starting chain index [st]: a
    LIST equality (the verifier recompresses) stating that completing
    each honest signature value (chain from [x] to position [d]) with
    [w-1 - d] more steps yields the chain end; [chain_split] with
    [j := 0], [i := d], [e := w.-1]. *)
Lemma complete_sign_chain pp st (xs : seq (wcp_N P)) (ds : seq nat) :
  size ds = size xs -> wf_digits (wcp_w P) ds ->
  [seq chain (chainf pp q.1) q.2.2 q.2.1 ((wcp_w P).-1 - q.2.1)
  | q <- zip (iota st (size xs))
             (zip ds
                  [seq chain (chainf pp ixd.1.1) ixd.1.2 0 ixd.2
                  | ixd <- zip (zip (iota st (size xs)) xs) ds])]
  = [seq chain (chainf pp ix.1) ix.2 0 (wcp_w P).-1
    | ix <- zip (iota st (size xs)) xs].
Proof. exact: wotsc_complete_sign_chain. Qed.

(** THE correctness lemma: if grinding succeeds, the honest signature
    verifies under the honest compressed public key.  Re-grinding is
    NOT part of verification: the verifier only checks the digit-sum
    predicate on the digest recomputed at the signature's counter,
    which holds by [find_counter_good]. *)
Lemma verify_sign pp xs m c :
  size xs = wcp_chain_count P ->
  find_counter pp m = Some c ->
  shrincs_wots_verify pp (shrincs_wots_pubkey pp xs) m (sign_chains pp xs (digest_of pp m c), c) = true.
Proof. exact: wotsc_verify_sign_digits. Qed.

(** Correctness through the signing function. *)
Lemma shrincs_wots_verify_sign pp xs m sg :
  size xs = wcp_chain_count P ->
  shrincs_wots_sign pp xs m = Some sg ->
  shrincs_wots_verify pp (shrincs_wots_pubkey pp xs) m sg = true.
Proof. exact: wotsc_verify_sign. Qed.

(* ------------------------------------------------------------------ *)
(** ** The scheme as a [sig_scheme]

    One-time scheme: [sign] returns the key unchanged and refuses
    ([None]) on grinding failure.  The public parameter PKseed is
    sampled by [keygen] and carried in both keys; see the header for
    the PRF-vs-sampling deviation. *)

Definition shrincs_wots_scheme : sig_scheme :=
  wotsc_scheme (wcp_w P) (wcp_chain_count P) (wcp_PP P) (wcp_N P) (wcp_M P) (wc_adrs P)
    (wcp_F P) (wcp_T_sf P) (wcp_H_grind P) (wcp_dPP P) (wcp_dN P)
    (wcp_constant_sum P) (wcp_c_max P)
    (grind_adrs P) (pk_adrs P) (chain_adrs P) true.

End WOTSCScheme.
