(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.wotsc.scheme

    WOTS+C (Compressed WOTS+), the one-time signature scheme of the
    stateful SHRINCS path, as a [sig_scheme] with a pure correctness
    lemma.  Definitions + correctness only; NO security proofs here
    (those are later P5 files).

    Counterparts: wotsc.tex sec:wotsc ("Parameters", "WOTS+C scheme":
    chaining function, grinding step, kg / sign / vf / pkFromSig);
    construction.tex sec:functions for the typed building blocks F,
    Th_l, Hgrind and sec:adressing-stateful for their address types.
    The generic fixed-sum WOTS construction in [Sec.lib.chain.core]
    supplies its checksum-free chain core. WOTS+C adds grinding,
    public-key compression, and the concrete stateful addresses from
    [SHRINCS.addressing].

    Building blocks (wotsc.tex "Parameters", instantiation list):
    - [F]      chain hash, called on WOTS_HASH_SF (type 10) addresses
               (tex: F : B^n x B^288 x B^n -> B^n);
    - [Tl]     public-key compression Theta_l, called on the
               WOTS_PK_SF (type 11) address (tex: Th_l : B^n x B^288
               x B^{ln} -> B^n); the l chain ends are modeled as a
               [seq N]; at the games layer this is a thf with
               th_M := 'list N;
    - [Hgrind] grinding hash, called on the WOTS_GRIND_SF (type 8)
               address (tex: Hgrind : B^n x B^288 x B^{2n} x B^{8c}
               -> B^n); at the games layer th_M := M × 'nat (message,
               counter) and th_N := 'nat — the n-byte digest is
               modeled as a [nat], parsed into base-w digits by
               [Encoding.digits_w] (the tex parses the byte string in
               base w; same data).

    Parameters (wotsc.tex names in comments; concrete numbers stay
    abstract): [w] the Winternitz parameter, [l] the number of chains
    (tex: l = ceil(n / log w)), [S_wn] the target chain-sum
    (0 <= S_wn <= l(w-1)), [c_max] the grinding-counter bound (the
    tex counter is an 8c-bit value, so c_max = 2^{8c}; bounded search
    exactly as in Sec.lib.games.stcrp).  The instance is anchored at the
    imaginary-tree position (z_star, i_star) (wotsc.tex kg: "with
    node-height and node-index fields set to the imaginary-tree
    position (z_star, i_star) of this WOTS+C instance").

    Deviations from the tex (documented):
    - The l secret chain starts are SAMPLED ([sample_seq dN l])
      rather than derived from SKseed via PRF_f on WOTS_PRF_SF
      addresses (wotsc.tex kg); the PRF_f derivation and the game hop
      replacing it by true randomness belong to the surrounding FXMSS
      layer (hop F.1 -> F.2), while the generic fixed-sum WOTS proof starts
      from ideal keys. Hence Sk = (PKseed, chain
      starts) instead of the tex's (PKseed, SKseed, ADRS).
    - Pk = (PKseed, compressed pk); the tex's PK also carries ADRS,
      which here is the section anchor (z_star, i_star).
    - Grinding failure: if no counter below [c_max] satisfies the
      digit-sum predicate, [find_ctr] is None and [sign] refuses
      (option signing of Sec.lib.sig.scheme; "no loops in packages",
      docs/ARCHITECTURE.md).  [find_ctr] is a pure function, so "the
      counter iteration must always be the same" (wotsc.tex RED note
      under the grinding step) holds by construction.
    - Verification follows wotsc.tex vf: recompute the digest at the
      SIGNATURE's counter — no re-grinding — reject unless its digit
      sum is S_wn, then complete each chain and recompress, comparing
      with pk.  We additionally check [size sg == l] (the tex parses
      sigma as exactly l chain values) and [wf_digits] (automatic for
      recomputed digests whenever 0 < w, by [wf_digits_w]).
    - One-time scheme: [sign] returns the key unchanged (the EU-CMA
      statement will use signing budget q_s = 1). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme toolkit.sample_seq wots.wotsc.
From SHRINCS Require Import addressing.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

Section WOTSCScheme.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).

(** Public parameter (PKseed), hash domain (n-byte strings), message
    space (the 2n-bit output of Hmsg^sf feeding the grinding step). *)
Context (PP N M : choice_type).

(** Chain hash F: tweaked with WOTS_HASH_SF addresses. *)
Context (F : PP -> adrs_sf -> N -> N).

(** Public-key compression Theta_l: tweaked with the WOTS_PK_SF
    address; input = the l chain ends (tex: pk_1 || ... || pk_l). *)
Context (Tl : PP -> adrs_sf -> seq N -> N).

(** Grinding hash Hgrind: tweaked with the WOTS_GRIND_SF address;
    input = (message, counter); output = digest as a [nat]. *)
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).

(** Samplers for key generation. *)
Context (dPP : dist PP) (dN : dist N).

(** Winternitz parameter, number of chains, target chain-sum,
    grinding-counter bound (see header). *)
Context (S_wn c_max : nat).

(** Imaginary-tree anchor (z_star, i_star) of this WOTS+C instance:
    the (node height, node index) fields of all its addresses. *)
Context (zstar istar : nat).

(* ------------------------------------------------------------------ *)
(** ** Addresses of this instance (addressing smart constructors) *)

Definition anchor : nat * nat := (zstar, istar).

(** ADRS^g of wotsc.tex (type 8). *)
Definition grind_adrs : adrs_sf := shrincs_fxmss_wots_grind_adrs anchor.

(** ADRS^h with chain index [i] and hash index [pos] (type 10). *)
Definition chain_adrs (i pos : nat) : adrs_sf := shrincs_fxmss_wots_chain_adrs anchor i pos.

(** ADRS^pk of wotsc.tex (type 11). *)
Definition pk_adrs : adrs_sf := shrincs_fxmss_wots_pk_adrs anchor.

(** Distinct-tweak facts at this instance (consumed by the SM-* side
    conditions; the cross-class facts are the adrs_*_neq_* lemmas of
    SHRINCS.addressing). *)
Lemma chain_adrs_inj i pos i' pos' :
  anchor_bounded anchor ->
  component_bounded l i ->
  component_bounded w.-1 pos ->
  component_bounded l i' ->
  component_bounded w.-1 pos' ->
  chain_adrs i pos = chain_adrs i' pos' -> (i, pos) = (i', pos').
Proof.
move=> Ha Hi Hp Hi' Hp'.
move/(shrincs_fxmss_wots_chain_adrs_inj l w _ _ _ _ _ _ _ _
  Ha Ha Hi Hp Hi' Hp') => [_ _ -> ->].
by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The instance

    Every definition below is a DEFINITIONAL instance of the one generic
    WOTS+C construction [Sec.lib.wots.wotsc], at this section's building
    blocks, this instance's three addresses, and LSB-first digit order
    ([dig_msb := false]).  The native tree's [Sec.wots.scheme] is the
    same construction at [dig_msb := true]; there is exactly one
    [sig_scheme] behind both. *)

(** Base-w digit vector of the digest at counter [c] (tex: d parsed
    as (a_1, ..., a_l)). *)
Definition digest_of (pp : PP) (m : M) (c : nat) : seq nat :=
  wotsc_digest_of w l PP M adrs_sf Hgrind grind_adrs false pp m c.

(** The post-grinding digest space: well-formed digits summing to the
    target (wotsc.tex: sum_i a_i = S_wn). *)
Definition valid_digest (ds : seq nat) : bool :=
  wotsc_valid_digest w S_wn ds.

Definition good_ctr (pp : PP) (m : M) (c : nat) : bool :=
  wotsc_good_ctr w l PP M adrs_sf Hgrind S_wn grind_adrs false pp m c.

Definition find_ctr (pp : PP) (m : M) : option nat :=
  wotsc_find_ctr w l PP M adrs_sf Hgrind S_wn c_max grind_adrs false pp m.

Lemma size_digest_of pp m c : size (digest_of pp m c) = l.
Proof. exact: wotsc_size_digest_of. Qed.

Lemma find_ctrP pp m c : find_ctr pp m = Some c -> good_ctr pp m c && (c < c_max).
Proof. exact: wotsc_find_ctrP. Qed.

Lemma find_ctr_good pp m c : find_ctr pp m = Some c -> good_ctr pp m c.
Proof. by move=> /find_ctrP /andP[h _]. Qed.

Lemma find_ctr_lt pp m c : find_ctr pp m = Some c -> c < c_max.
Proof. by move=> /find_ctrP /andP[_ h]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

(** Chain step of the [i]-th chain (Sec.lib.math.chain conventions: the
    chain position [pos] is the first argument of the step function);
    tex: the chaining function c^{j,k} on ADRS^h. *)
Definition chainf (pp : PP) (i : nat) : nat -> N -> N :=
  wotsc_chainf PP N adrs_sf F chain_adrs pp i.

(** Chain ends: the [i]-th component is the end (position w-1) of the
    [i]-th chain from the [i]-th secret (tex kg:
    pk_i = c^{0, w-1}(sk_i, i, PKseed, ADRS^h)). *)
Definition chain_ends (pp : PP) (xs : seq N) : seq N :=
  wotsc_chain_ends w l PP N adrs_sf F chain_adrs pp xs.

(** Compressed public key (tex kg:
    pk = Th_l(PKseed, ADRS^pk, pk_1 || ... || pk_l)). *)
Definition shrincs_fxmss_wots_public_key (pp : PP) (xs : seq N) : N :=
  wotsc_pubkey w l PP N adrs_sf F Tl pk_adrs chain_adrs pp xs.

(** Signature chain values for digit vector [ds] (tex sign:
    sigma_i = c^{0, a_i}(sk_i, i, PKseed, ADRS^h)). *)
Definition sign_digits (pp : PP) (xs : seq N) (ds : seq nat) : seq N :=
  wotsc_sign_chains l PP N adrs_sf F chain_adrs pp xs ds.

(** Verifier-side chain completion (tex vf:
    c^{a_i, w-1-a_i}(sigma_i, i, PKseed, ADRS^h)). *)
Definition complete_ends (pp : PP) (ds : seq nat) (ys : seq N) : seq N :=
  wotsc_complete_ends w l PP N adrs_sf F chain_adrs pp ds ys.

(** Verification (wotsc.tex vf): recompute the digest at the
    signature's counter, reject unless it lies in the post-grinding
    digest space, complete the chains, recompress, compare with pk.
    A signature is (chain values, counter). *)
Definition shrincs_fxmss_wots_verify (pp : PP) (root : N) (m : M) (sg : seq N * nat) : bool :=
  wotsc_verify w l PP N M adrs_sf F Tl Hgrind S_wn grind_adrs pk_adrs chain_adrs false pp root m sg.

(** Signing as a pure partial function: grind, then sign the digits;
    None on grinding failure (sign refusal). *)
Definition shrincs_fxmss_wots_sign (pp : PP) (xs : seq N) (m : M) : option (seq N * nat) :=
  wotsc_sign w l PP N M adrs_sf F Hgrind S_wn c_max grind_adrs chain_adrs false pp xs m.

Lemma shrincs_fxmss_wots_sign_None pp xs m : find_ctr pp m = None -> shrincs_fxmss_wots_sign pp xs m = None.
Proof. by rewrite /shrincs_fxmss_wots_sign /wotsc_sign -/(find_ctr pp m) => ->. Qed.

Lemma shrincs_fxmss_wots_sign_Some pp xs m c :
  find_ctr pp m = Some c ->
  shrincs_fxmss_wots_sign pp xs m = Some (sign_digits pp xs (digest_of pp m c), c).
Proof. by rewrite /shrincs_fxmss_wots_sign /wotsc_sign -/(find_ctr pp m) => ->. Qed.

(* ------------------------------------------------------------------ *)
(** ** Definitional views

    Each definition above is a [wotsc_*] application; these restate its
    body in the pre-merge form.  All are pure conversion, and exist so
    that proof scripts can [rewrite fooE] instead of [rewrite /foo] and
    stay independent of how many delta steps separate a name from its
    body. *)

Lemma digest_of_def pp m c : digest_of pp m c = digits_w w l (Hgrind pp grind_adrs (m, c)).
Proof. by []. Qed.

Lemma valid_digest_def ds : valid_digest ds = wf_digits w ds && (sumn ds == S_wn).
Proof. by []. Qed.

Lemma good_ctr_def pp m c : good_ctr pp m c = valid_digest (digest_of pp m c).
Proof. by []. Qed.

Lemma find_ctr_def pp m : find_ctr pp m = ohead [seq c <- iota 0 c_max | good_ctr pp m c].
Proof. by []. Qed.

Lemma chainf_def pp i pos x : chainf pp i pos x = F pp (chain_adrs i pos) x.
Proof. by []. Qed.

Lemma chain_ends_def pp xs :
  chain_ends pp xs = [seq chain (chainf pp ix.1) ix.2 0 w.-1 | ix <- zip (iota 0 l) xs].
Proof. by []. Qed.

Lemma shrincs_fxmss_wots_public_key_def pp xs :
  shrincs_fxmss_wots_public_key pp xs = Tl pp pk_adrs (chain_ends pp xs).
Proof. by []. Qed.

Lemma sign_digits_def pp xs ds :
  sign_digits pp xs ds
  = [seq chain (chainf pp ixd.1.1) ixd.1.2 0 ixd.2 | ixd <- zip (zip (iota 0 l) xs) ds].
Proof. by []. Qed.

Lemma complete_ends_def pp ds ys :
  complete_ends pp ds ys
  = [seq chain (chainf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1) | q <- zip (iota 0 l) (zip ds ys)].
Proof. by []. Qed.

Lemma shrincs_fxmss_wots_verify_def pp root m sg :
  shrincs_fxmss_wots_verify pp root m sg
  = [&& valid_digest (digest_of pp m sg.2), size sg.1 == l
      & Tl pp pk_adrs (complete_ends pp (digest_of pp m sg.2) sg.1) == root].
Proof. by []. Qed.

Lemma shrincs_fxmss_wots_sign_def pp xs m :
  shrincs_fxmss_wots_sign pp xs m
  = omap (fun c => (sign_digits pp xs (digest_of pp m c), c)) (find_ctr pp m).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Size sanity lemmas *)

Lemma size_chain_ends pp xs : size (chain_ends pp xs) = minn l (size xs).
Proof. exact: wotsc_size_chain_ends. Qed.

Lemma size_chain_ends_l pp xs :
  size xs = l -> size (chain_ends pp xs) = l.
Proof. by move=> hxs; rewrite size_chain_ends hxs minnn. Qed.

Lemma size_sign_digits pp xs ds :
  size (sign_digits pp xs ds) = minn (minn l (size xs)) (size ds).
Proof. exact: wotsc_size_sign_chains. Qed.

Lemma size_sign_digits_l pp xs ds :
  size xs = l -> size ds = l -> size (sign_digits pp xs ds) = l.
Proof. by move=> hxs hds; rewrite size_sign_digits hxs hds !minnn. Qed.

Lemma size_complete_ends pp ds ys :
  size (complete_ends pp ds ys) = minn l (minn (size ds) (size ys)).
Proof. exact: wotsc_size_complete_ends. Qed.

(* ------------------------------------------------------------------ *)
(** ** Correctness *)

(** Pointwise core, generalized over the starting chain index [st]
    (fixed_sum_scheme.all_chain_checks, upgraded from an [all] of checks
    to a LIST equality because the verifier recompresses): completing
    each honest signature value (chain from [x] to position [d]) with
    [w-1 - d] more steps yields the chain end; [chain_split] with
    [j := 0], [i := d], [e := w.-1]. *)
Lemma complete_sign_chain pp st (xs : seq N) (ds : seq nat) :
  size ds = size xs -> wf_digits w ds ->
  [seq chain (chainf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota st (size xs))
             (zip ds
                  [seq chain (chainf pp ixd.1.1) ixd.1.2 0 ixd.2
                  | ixd <- zip (zip (iota st (size xs)) xs) ds])]
  = [seq chain (chainf pp ix.1) ix.2 0 w.-1 | ix <- zip (iota st (size xs)) xs].
Proof. exact: wotsc_complete_sign_chain. Qed.

(** THE correctness lemma: if grinding succeeds, the honest signature
    verifies under the honest compressed public key.  Re-grinding is
    NOT part of verification (wotsc.tex vf): the verifier only checks
    the digit-sum predicate on the digest recomputed at the
    signature's counter, which holds by [find_ctr_good]. *)
Lemma shrincs_fxmss_wots_verify_digits pp xs m c :
  size xs = l ->
  find_ctr pp m = Some c ->
  shrincs_fxmss_wots_verify pp (shrincs_fxmss_wots_public_key pp xs) m (sign_digits pp xs (digest_of pp m c), c) = true.
Proof. exact: wotsc_verify_sign_digits. Qed.

(** Correctness through the signing function. *)
Lemma shrincs_fxmss_wots_verify_sign pp xs m sg :
  size xs = l ->
  shrincs_fxmss_wots_sign pp xs m = Some sg ->
  shrincs_fxmss_wots_verify pp (shrincs_fxmss_wots_public_key pp xs) m sg = true.
Proof. exact: wotsc_verify_sign. Qed.

(* ------------------------------------------------------------------ *)
(** ** The scheme as a [sig_scheme]

    One-time scheme: [sign] returns the key unchanged and refuses
    ([None]) on grinding failure.  The public parameter PKseed is
    sampled by [keygen] and carried in both keys (wotsc.tex kg, where
    PKseed is part of both SK and PK); see the header for the
    PRF-vs-sampling deviation. *)

Definition shrincs_fxmss_wots_scheme : sig_scheme :=
  wotsc_scheme w l PP N M adrs_sf F Tl Hgrind dPP dN S_wn c_max grind_adrs pk_adrs chain_adrs false.

End WOTSCScheme.
