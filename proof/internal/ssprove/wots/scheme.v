(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.scheme

    WOTS+C (Compressed WOTS+), the stateful one-time signature scheme,
    as a [sig_scheme] with a pure correctness lemma.  Definitions and
    correctness only; the security proof lives in the surrounding
    files.

    Building blocks ([Shrincs.internal.ssprove.wots.params] carries them as record fields;
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
               counter) and th_N := [wcp_G] — the n-byte digest,
               read as base-w digits by [wcp_digits].

    Parameters: everything lives in ONE record value [P : wc_params]
    ([Shrincs.internal.ssprove.wots.params]) -- the Winternitz parameter [wcp_w], the chain
    count [wcp_chain_count] (= ceil(n / log w)), the target chain-sum
    [wcp_constant_sum] (0 <= constant_sum <= chain_count(w-1)), the
    grinding-counter bound [wcp_c_max] (the counter is an 8c-bit value,
    so c_max = 2^{8c}; bounded search as in Shrincs.games.stcrp), and
    the tweaks of the instance.  The imaginary-tree anchor (node height
    and node index) is inside them.  The instance addresses
    ([grind_adrs P], [chain_adrs P], [pk_adrs P], [prf_adrs P]) are
    params.v definitions.

    Modeling choices (documented deviations):
    - The chain_count secret chain starts are SAMPLED ([sample_seq dN chain_count]) rather
      than derived from SKseed via PRF_f on WOTS_PRF_SF addresses; the
      PRF_f derivation and the game hop replacing it by true
      randomness belong to the surrounding tree layer, so this scheme
      starts from ideal keys.  Hence Sk = (PKseed, chain starts)
      instead of (PKseed, SKseed, ADRS).
    - Pk = (PKseed, compressed pk); a full PK also carries ADRS, which
      here is the instance anchor, fixed by the record.
    - Grinding failure: if no counter below [c_max] satisfies the
      digit-sum predicate, [find_counter] is None and [sign] refuses
      (option signing of Shrincs.games; no loops in packages).
      [find_counter] is a pure function, so the counter iteration is
      always the same by construction.
    - Verification recomputes the digest at the SIGNATURE's counter —
      no re-grinding — rejects unless its digit sum is constant_sum, then
      completes each chain and recompresses, comparing with pk.  We
      additionally check [size sg == chain_count] (sigma is exactly chain_count chain
      values) and [wf_digits] (every digit below w; an instance whose
      [wcp_digits] only produces such digits makes it redundant).
    - One-time scheme: [sign] returns the key unchanged (the EU-CMA
      statement uses signing budget q_s = 1).
    - The pure functions below work on the two parts of a signature,
      (chain values, counter).  The scheme record exchanges the
      encoded signature [wcp_Sig P]: [sign] encodes and [verify]
      decodes first. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.sample_seq chain.core.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.wots Require Export params.
From Stdlib Require Import Bool.

Import PackageNotation.
#[local] Open Scope package_scope.

Section WOTSCScheme.

(** The WOTS+C parameter record (see Shrincs.internal.ssprove.wots.params). *)
Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** ** Grinding

    Pure bounded search, the STCRP modeling: the digest at counter [c]
    is decoded into [chain_count] base-w digits, and [find_counter] returns the
    SMALLEST counter below [c_max] whose digit sum is [constant_sum] (an
    unbounded iteration ctr = 0, 1, 2, ... bounded by [c_max]). *)

(** Digit vector of the digest at counter [c]: the instance's reading
    [wcp_digits] of the grinding hash output, one digit per chain. *)
Definition digest_of (pp : wcp_PP P) (m : wcp_M P) (c : nat) : seq nat :=
  wcp_digits P (wcp_H_grind P pp (grind_adrs P) (m, c)).

(** The post-grinding digest space: well-formed digits summing to the
    target (sum_i a_i = constant_sum). *)
Definition valid_digest (ds : seq nat) : bool :=
  wf_digits (wcp_w P) ds && (sumn ds == wcp_constant_sum P).

Definition good_counter (pp : wcp_PP P) (m : wcp_M P) (c : nat) : bool :=
  valid_digest (digest_of pp m c).

Definition find_counter (pp : wcp_PP P) (m : wcp_M P) : option nat :=
  ohead [seq c <- iota 0 (wcp_c_max P) | good_counter pp m c].

Lemma size_digest_of pp m c : size (digest_of pp m c) = wcp_chain_count P.
Proof. exact: wcp_digits_size. Qed.

Lemma find_counterP pp m c :
  find_counter pp m = Some c -> good_counter pp m c && (c < wcp_c_max P).
Proof.
rewrite /find_counter.
case E: [seq c0 <- iota 0 (wcp_c_max P) | good_counter pp m c0] => [|c0 cs] //= [<-].
move: (mem_head c0 cs).
by rewrite -E mem_filter mem_iota add0n => /andP[-> /andP[_ ->]].
Qed.

Lemma find_counter_good pp m c : find_counter pp m = Some c -> good_counter pp m c.
Proof. by move=> /find_counterP /andP[h _]. Qed.

Lemma find_counter_lt pp m c : find_counter pp m = Some c -> c < wcp_c_max P.
Proof. by move=> /find_counterP /andP[_ h]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

(** Chain step of the [i]-th chain at position [p]: [F] at the chain
    address.  This instantiates the abstract chain library's [F']
    ([Shrincs.internal.ssprove.lib.chain.core]), so all chains below go
    through the fold [chainc].

    Per-hash-call tweak distinctness lives at the tweak level
    ([params.chain_tweak_inj]).  No proof here needs the four tweak
    classes (chain, start, pk, grind) to be apart from each other:
    each class is the tweak of a different function of the record. *)
Definition chainf (pp : wcp_PP P) (i : nat) (p : nat) (x : wcp_N P) : wcp_N P :=
  wcp_F P pp (chain_adrs P i p) x.

(** Chain ends: the [i]-th component is the end (position w-1) of the
    [i]-th chain from the [i]-th secret
    (pk_i = c^{0, w-1}(sk_i, i, PKseed, ADRS^h)).  The zip/iota
    formulation avoids a default element. *)
Definition chain_ends (pp : wcp_PP P) (xs : seq (wcp_N P)) : seq (wcp_N P) :=
  [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp ix.1 ix.2 0 (wcp_w P).-1
  | ix <- zip (iota 0 (wcp_chain_count P)) xs].

(** Compressed public key
    (pk = T_sf(PKseed, ADRS^pk, pk_1 || ... || pk_l)). *)
Definition shrincs_wots_pubkey (pp : wcp_PP P) (xs : seq (wcp_N P)) : wcp_N P :=
  wcp_T_sf P pp (pk_adrs P) (chain_ends pp xs).

(** Signature chain values for digit vector [ds]
    (sigma_i = c^{0, a_i}(sk_i, i, PKseed, ADRS^h)). *)
Definition sign_chains (pp : wcp_PP P) (xs : seq (wcp_N P)) (ds : seq nat) : seq (wcp_N P) :=
  [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp ixd.1.1 ixd.1.2 0 ixd.2
  | ixd <- zip (zip (iota 0 (wcp_chain_count P)) xs) ds].

(** Verifier-side chain completion
    (c^{a_i, w-1-a_i}(sigma_i, i, PKseed, ADRS^h)). *)
Definition complete_ends (pp : wcp_PP P) (ds : seq nat) (ys : seq (wcp_N P)) : seq (wcp_N P) :=
  [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp q.1 q.2.2 q.2.1 ((wcp_w P).-1 - q.2.1)
  | q <- zip (iota 0 (wcp_chain_count P)) (zip ds ys)].

(** Verification: recompute the digest at the signature's counter,
    reject unless it lies in the post-grinding digest space, complete
    the chains, recompress, compare with pk.  A signature is (chain
    values, counter). *)
Definition shrincs_wots_verify (pp : wcp_PP P) (root : wcp_N P) (m : wcp_M P)
    (sg : seq (wcp_N P) * nat) : bool :=
  [&& valid_digest (digest_of pp m sg.2), size sg.1 == wcp_chain_count P
    & wcp_T_sf P pp (pk_adrs P) (complete_ends pp (digest_of pp m sg.2) sg.1) == root].

(** Signing as a pure partial function: grind, then sign the digits;
    None on grinding failure (sign refusal). *)
Definition shrincs_wots_sign (pp : wcp_PP P) (xs : seq (wcp_N P)) (m : wcp_M P)
    : option (seq (wcp_N P) * nat) :=
  omap (fun c => (sign_chains pp xs (digest_of pp m c), c)) (find_counter pp m).

Lemma shrincs_wots_sign_None pp xs m : find_counter pp m = None -> shrincs_wots_sign pp xs m = None.
Proof. by rewrite /shrincs_wots_sign => ->. Qed.

Lemma shrincs_wots_sign_Some pp xs m c :
  find_counter pp m = Some c ->
  shrincs_wots_sign pp xs m = Some (sign_chains pp xs (digest_of pp m c), c).
Proof. by rewrite /shrincs_wots_sign => ->. Qed.

(* ------------------------------------------------------------------ *)
(** ** Size sanity lemmas *)

Lemma size_chain_ends pp xs : size (chain_ends pp xs) = minn (wcp_chain_count P) (size xs).
Proof. by rewrite size_map size_zip size_iota. Qed.

Lemma size_chain_ends_l pp xs :
  size xs = wcp_chain_count P -> size (chain_ends pp xs) = wcp_chain_count P.
Proof. by move=> hxs; rewrite size_chain_ends hxs minnn. Qed.

Lemma size_sign_chains pp xs ds :
  size (sign_chains pp xs ds) = minn (minn (wcp_chain_count P) (size xs)) (size ds).
Proof. by rewrite size_map !size_zip size_iota. Qed.

Lemma size_sign_chains_l pp xs ds :
  size xs = wcp_chain_count P -> size ds = wcp_chain_count P ->
  size (sign_chains pp xs ds) = wcp_chain_count P.
Proof. by move=> hxs hds; rewrite size_sign_chains hxs hds !minnn. Qed.

Lemma size_complete_ends pp ds ys :
  size (complete_ends pp ds ys) = minn (wcp_chain_count P) (minn (size ds) (size ys)).
Proof. by rewrite size_map !size_zip size_iota. Qed.

(* ------------------------------------------------------------------ *)
(** ** Indexed forms

    The three chain maps above zip their inputs with the chain indices.
    When the inputs are themselves indexed by the chain, each is a
    plain map over the indices: the shape a loop [for i in range(n)]
    has.  The digit of chain [i] is read with [nth]. *)

Lemma zip_iota_map (A : Type) (n : nat) (f : nat -> A) :
  zip (iota 0 n) [seq f i | i <- iota 0 n] = [seq (i, f i) | i <- iota 0 n].
Proof. by rewrite -[X in zip X _]map_id zip_map. Qed.

Lemma chain_ends_mkseq pp (f : nat -> wcp_N P) :
  chain_ends pp [seq f i | i <- iota 0 (wcp_chain_count P)]
  = [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp i (f i) 0 (wcp_w P).-1
    | i <- iota 0 (wcp_chain_count P)].
Proof. by rewrite /chain_ends zip_iota_map -map_comp. Qed.

Lemma sign_chains_mkseq pp (f : nat -> wcp_N P) (ds : seq nat) :
  size ds = wcp_chain_count P ->
  sign_chains pp [seq f i | i <- iota 0 (wcp_chain_count P)] ds
  = [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp i (f i) 0 (nth 0 ds i)
    | i <- iota 0 (wcp_chain_count P)].
Proof.
move=> hds.
rewrite -[in LHS](mkseq_nth 0 ds) hds /sign_chains /mkseq.
by rewrite zip_iota_map zip_map -map_comp.
Qed.

Lemma complete_ends_mkseq pp (ds : seq nat) (f : nat -> wcp_N P) :
  size ds = wcp_chain_count P ->
  complete_ends pp ds [seq f i | i <- iota 0 (wcp_chain_count P)]
  = [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp i (f i) (nth 0 ds i)
           ((wcp_w P).-1 - nth 0 ds i)
    | i <- iota 0 (wcp_chain_count P)].
Proof.
move=> hds.
rewrite -[in LHS](mkseq_nth 0 ds) hds /complete_ends /mkseq.
by rewrite zip_map zip_iota_map -map_comp.
Qed.

(** Every digit of a digest is below [w], also past the end of the
    digest, where [nth] reads its default. *)
Lemma nth_digest_of_lt pp m c i : nth 0 (digest_of pp m c) i < wcp_w P.
Proof.
case: (ltnP i (size (digest_of pp m c))) => hi.
- exact: (all_nthP 0 (wcp_digits_wf P _)).
- by rewrite nth_default //; exact: (ltnW (wcp_Hw P)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Correctness *)

(** Pointwise core, generalized over the starting chain index [st]: a
    LIST equality (the verifier recompresses) stating that completing
    each honest signature value (chain from [x] to position [d]) with
    [w-1 - d] more steps yields the chain end; [chain_split] with
    [j := 0], [i := d], [e := w.-1]. *)
Lemma complete_sign_chain pp st (xs : seq (wcp_N P)) (ds : seq nat) :
  size ds = size xs -> wf_digits (wcp_w P) ds ->
  [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp q.1 q.2.2 q.2.1 ((wcp_w P).-1 - q.2.1)
  | q <- zip (iota st (size xs))
             (zip ds
                  [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp ixd.1.1 ixd.1.2 0 ixd.2
                  | ixd <- zip (zip (iota st (size xs)) xs) ds])]
  = [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp ix.1 ix.2 0 (wcp_w P).-1
    | ix <- zip (iota st (size xs)) xs].
Proof.
elim: xs st ds => [|x xs IH] st [|d ds] //= [hsz] /andP[hd hds].
have hdw : d <= (wcp_w P).-1 by rewrite -ltnS (ltn_predK hd).
have hsp := chainc_split (wcp_PP P) (wcp_N P) (wcp_w P) chainf pp st x 0 d (wcp_w P).-1 (leq0n d) hdw.
rewrite !subn0 in hsp.
by rewrite -hsp; congr (_ :: _); apply: IH.
Qed.

(** THE correctness lemma: if grinding succeeds, the honest signature
    verifies under the honest compressed public key.  Re-grinding is
    NOT part of verification: the verifier only checks the digit-sum
    predicate on the digest recomputed at the signature's counter,
    which holds by [find_counter_good]. *)
Lemma verify_sign pp xs m c :
  size xs = wcp_chain_count P ->
  find_counter pp m = Some c ->
  shrincs_wots_verify pp (shrincs_wots_pubkey pp xs) m (sign_chains pp xs (digest_of pp m c), c) = true.
Proof.
move=> hxs hc.
have hgood : good_counter pp m c := find_counter_good _ _ _ hc.
have /andP[hwf _] := hgood.
have hszd : size (digest_of pp m c) = wcp_chain_count P by rewrite size_digest_of.
rewrite /shrincs_wots_verify /=.
apply/and3P; split.
- exact: hgood.
- by rewrite size_sign_chains_l ?eqxx.
- apply/eqP; rewrite /shrincs_wots_pubkey; congr (wcp_T_sf P _ _ _).
  rewrite /complete_ends /chain_ends /sign_chains -hxs.
  apply: complete_sign_chain; last exact: hwf.
  by rewrite hszd hxs.
Qed.

(** Correctness through the signing function. *)
Lemma shrincs_wots_verify_sign pp xs m sg :
  size xs = wcp_chain_count P ->
  shrincs_wots_sign pp xs m = Some sg ->
  shrincs_wots_verify pp (shrincs_wots_pubkey pp xs) m sg = true.
Proof.
move=> hxs; rewrite /shrincs_wots_sign.
case E: (find_counter pp m) => [c|] //= [<-].
by apply: verify_sign.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The scheme as a [sig_scheme]

    One-time scheme: [sign] returns the key unchanged and refuses
    ([None]) on grinding failure.  The public parameter PKseed is
    sampled by [keygen] and carried in both keys; see the header for
    the PRF-vs-sampling deviation. *)

Definition shrincs_wots_scheme : sig_scheme := {|
  Pk := wcp_PP P × wcp_N P ;
  Sk := wcp_PP P × ('list (wcp_N P)) ;
  Msg := wcp_M P ;
  Sig := wcp_Sig P ;
  SParam := 'unit ;
  keygen := fun _ => {code
    pp ← wcp_dPP P ;;
    xs ← sample_seq (wcp_dN P) (wcp_chain_count P) ;;
    ret ((pp, xs), (pp, shrincs_wots_pubkey pp xs)) } ;
  sign := fun sk m => {code
    ret (omap (fun sg => (wcp_sig_encode P sg, sk)) (shrincs_wots_sign sk.1 sk.2 m)) } ;
  verify := fun pk m sg => shrincs_wots_verify pk.1 pk.2 m (wcp_sig_decode P sg)
|}.

End WOTSCScheme.
