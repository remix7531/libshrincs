(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.analysis

    The PURE forgery-analysis layer of the WOTS+C one-time security
    proof: the four-way forgery classifier [shrincs_wots_forgery_classify]
    and the SM-TCR(F) target bookkeeping at encoded chain addresses.

    The argument: an adversary who observes a valid pair (mes, sigma)
    and attempts to forge must, if every a_i' is at least a_i (so
    equality of sums forces a_i' = a_i for all i), find a target
    collision for H_grind; otherwise some a_i' < a_i and the forger
    must invert F at some position.  This is refined into the four
    cases the game hops consume.  The WOTS+C chain layer is the
    generic chain library at the address-wrapped chain hash [Fw]
    (defined in Sec.games), so the per-chain classification
    ([forgery_cases]), the PRE post-processing
    ([forgery_pre_preimage]), the digit selector ([forged_digit_lt],
    [eq_sumn_exists_lt]) and the whole TCR bookkeeping
    ([tcr_targets]/[tcr_index]/...) are instantiated, not re-proved.

    ** The four cases (the disjuncts of [shrincs_wots_forgery_classify])

    Signed: message [m], counter [c] (grinding success, [good_counter]),
    digest [d := digest_of pp m c], per-chain signature values [sg]
    (in G_forge_uniformchains these are [sample_sig_roots] outputs re-rooted at the
    digits of [d]), public key
    [pk := T_sf pp pk_adrs (complete_ends pp d sg)].
    Forged: fresh [mstar != m] with signature [(ystar, cstar)] that
    verifies; verification forces [dstar := digest_of pp mstar cstar]
    valid ([valid_digest]), [size ystar = chain_count], and the recompressed
    completed ends to hit [pk].

    1. GRIND ([dstar = d] as digit vectors): both digests are < w^chain_count
       (the [Hrange] side condition), and [digits_w] is injective
       there ([digits_w_inj]), so the two H_grind OUTPUTS collide:
       [H_grind pp grind_adrs (mstar, cstar) = H_grind pp grind_adrs
       (m, c)] with [mstar != m] — exactly STCRP's SCHECK win at the
       single committed grinding target (whose stored counter is [c]
       by Games.[grind_search_find_ctr]): the reduction feeds
       SCHECK (0, (mstar, cstar)).
    2. COMPRESS ([dstar != d] but the completed ends differ while
       their T_sf compressions agree): SM-TCR(T_sf) collision at the
       single committed target (encode_tweak pk_adrs, honest ends):
       the reduction feeds CHECK (0, complete_ends pp dstar ystar).
    3. CHAIN COLLISION ([dstar != d], completed ends EQUAL): both
       digit vectors sum to constant_sum, so some chain [i] has
       [dstar_i < d_i] ([forged_digit_lt]); walking both chains
       forward ([chain_extract]) finds [k] with an F-collision
       against the honest chain value at position [k >= d_i] — the
       input the reduction committed at tweak
       [encode_tweak (chain_adrs i k)] ([shrincs_wots_tcr_targets]): it feeds
       CHECK (tcr_index w d i k, u), recomputing [u] by re-running
       [chain_extract] (which is how it decides case 3 vs 4, the
       chain library's [tcr_decision] pattern).
    4. CHAIN MEET (otherwise): the forged chain reaches [sg_i] at
       position [d_i] (note [0 < d_i] since [dstar_i < d_i]); one
       step earlier it is an F-preimage of [sg_i] at tweak
       [encode_tweak (chain_adrs i (d_i - 1))].  In G_forge_uniformchains with
       [d_i > 0], [sg_i = F pp (chain_adrs i (d_i - 1)) u_i] for a
       hidden uniform [u_i] — the SM-PRE oracle's answer — so the
       reduction feeds PCHECK (index of chain i, that preimage).

    ** The Hrange side condition

    Case 1 needs equal digit VECTORS to give equal H_grind OUTPUTS;
    [digits_w w chain_count] is only injective below [w ^ chain_count], so
    [shrincs_wots_forgery_classify] takes the DATA-level side condition
    [Hrange : forall pp a x, H_grind pp a x < w ^ chain_count] as an explicit
    lemma argument (not a section hypothesis).  It is discharged at
    instantiation: H_grind outputs n-bit strings parsed as exactly chain_count
    base-w digits (chain_count = ceil(n / log w)), i.e. the digest space embeds
    into [0, w^chain_count).

    ** TCR bookkeeping at encoded tweaks

    The SM-TCR(F) game's tweak space is [adrs_sf_ch], so the
    committed target list re-tags the chain library's [tcr_targets]
    with [shrincs_wots_tweak (i, k) := encode_tweak (chain_adrs i k)]
    (injective: [encode_tweak_inj] + [chain_adrs_inj]); positions in
    the list are unchanged, so the library's [tcr_index w] IS the
    CHECK index (chosen over a nat*nat-tweaked wrapper thf so that all
    three instances of Sec.games share one tweak space and the
    distinct-address lemmas of Sec.wots.addressing apply directly). *)

From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf toolkit.sample_seq.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Sec.lib Require Import chain.core.
From Sec Require Import addressing.
From Sec.wots Require Import addressing.
From Sec.wots Require Import scheme games.

Import PackageNotation.
#[local] Open Scope package_scope.

Section WOTSCAnalysis.

(** The WOTS+C parameter record (see Sec.wots.params); the same context
    as Sec.wots.scheme.  This layer is pure. *)
Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** *** Bridges into the chain-library analysis

    All by conversion ([Fw] beta-reduces to [F] at [chain_adrs], and
    shrincs_wots_scheme's verifier-side [complete_ends] is the chain library's
    [ends_from_sig] at [FW]); stated once so the proofs below can
    rewrite instead of relying on implicit conversion. *)

Lemma wcendsE pp (ds : seq nat) (ys : seq (wcp_N P)) :
  complete_ends P pp ds ys = ends_from_sig (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds ys.
Proof. by []. Qed.

(** A grinded digest is a valid chain-library message (digit vector
    of size chain_count, digits < w, digit sum constant_sum) — the digit-selector
    lemmas [forged_digit_lt] / [valid_msg_digit] apply to digests. *)
Lemma vdigest_valid_msg pp (m : wcp_M P) c :
  valid_digest P (digest_of P pp m c) ->
  valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c).
Proof.
case/andP=> h1 h2.
by rewrite /valid_msg (size_digest_of P) eqxx h1 h2.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Case 1 (GRIND): digit-vector equality lifts to H_grind-output
    equality

    [digits_w w chain_count] is injective below [w ^ chain_count] ([digits_w_inj]); the
    degenerate radix [w = 0] is handled separately (then [Hrange]
    forces [chain_count = 0] and both outputs are 0). *)

Lemma wdigest_inj pp (m1 : wcp_M P) (c1 : nat) (m2 : wcp_M P) (c2 : nat) :
  grind_range P ->
  digest_of P pp m1 c1 = digest_of P pp m2 c2 ->
  wcp_H_grind P pp (grind_adrs P) (m1, c1) = wcp_H_grind P pp (grind_adrs P) (m2, c2).
Proof.
move=> Hr heq.
have h1 := Hr pp (grind_adrs P) (m1, c1).
have h2 := Hr pp (grind_adrs P) (m2, c2).
(* [digest_of] is MSB-first ([rev] of [digits_w]); peel the [rev] by
   its injectivity, then [digits_w] is injective below [w ^ chain_count]
   ([w = 0] is impossible: [wcp_Hw : 1 < w]). *)
move: heq; rewrite /digest_of => /(inv_inj revK) heq.
exact: (digits_w_inj (ltnW (wcp_Hw P)) h1 h2 heq).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Cases 3/4 (CHAINS): the per-chain classifier at WOTS+C
    addresses

    The chain library's [forgery_cases] instantiated at [FW]; the
    statement is restated with shrincs_wots_scheme's [chainf] and explicit
    [chain_adrs] tweaks (convertible), so consumers never see [FW]'s
    pair tweaks. *)

Lemma shrincs_wots_chain_cases pp i d (sigi : wcp_N P) dstar (sigstar : wcp_N P) :
  dstar < d -> d < wcp_w P ->
  chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigstar dstar ((wcp_w P).-1 - dstar)
    = chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigi d ((wcp_w P).-1 - d) ->
  match chain_extract (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigstar dstar sigi d (wcp_w P).-1 with
  | ChainColl k u v =>
      [/\ d <= k < (wcp_w P).-1,
          v = chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigi d (k - d),
          u != v
        & wcp_F P pp (chain_adrs P i k) u = wcp_F P pp (chain_adrs P i k) v]
  | ChainMeet => chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigstar dstar (d - dstar) = sigi
  end.
Proof.
move=> hlt hdw hch.
move: (forgery_cases (wcp_PP P) (wcp_N P) (Fw P) (wcp_w P) pp i d sigi dstar sigstar hlt hdw hch).
case: (chain_extract _ _ _ _ _ _) => [k u v|]; last by [].
by move=> [hk hv hne hcol]; split.
Qed.

(** Case-4 post-processing ([forgery_pre_preimage] at [FW]): a chain
    meet at position [d] yields the F-preimage of [sigi] at chain
    address (i, d-1) that wins SM-PRE's PCHECK. *)
Lemma shrincs_wots_pre_preimage pp i d (sigi sigstar : wcp_N P) (dstar : nat) :
  dstar < d -> d < wcp_w P ->
  chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigstar dstar (d - dstar) = sigi ->
  wcp_F P pp (chain_adrs P i d.-1)
    (chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) sigstar dstar (d.-1 - dstar)) = sigi.
Proof.
move=> hlt hdw hmeet.
exact: (forgery_pre_preimage (wcp_PP P) (wcp_N P) (Fw P) pp i d sigi sigstar
          dstar hlt hmeet).
Qed.

(** nth-form access to an equality of completed-ends lists: at every
    chain [i < chain_count] the forged completion hits the honest one (via
    [ends_from_sig_nth] at [FW], twice). *)
Lemma wcends_nth_eq pp (ds ds' : seq nat) (ys ys' : seq (wcp_N P)) (y0 : wcp_N P) i :
  size ds = wcp_chain_count P -> size ys = wcp_chain_count P ->
  size ds' = wcp_chain_count P -> size ys' = wcp_chain_count P -> i < wcp_chain_count P ->
  complete_ends P pp ds ys = complete_ends P pp ds' ys' ->
  chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) (nth y0 ys i) (nth 0 ds i) ((wcp_w P).-1 - nth 0 ds i)
  = chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) (nth y0 ys' i) (nth 0 ds' i) ((wcp_w P).-1 - nth 0 ds' i).
Proof.
move=> h1 h2 h3 h4 hi /(congr1 (fun s => nth y0 s i)).
rewrite !wcendsE (ends_from_sig_nth (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds ys y0 i h1 h2 hi)
        (ends_from_sig_nth (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds' ys' y0 i h3 h4 hi).
exact: id.
Qed.

(* ------------------------------------------------------------------ *)
(** *** THE four-way forgery classifier

    Hypotheses are exactly what G_forge_uniformchains's KFORGE provides on a winning
    real run: the grinding fact for the signed counter
    ([find_counter_isSome_good] of Sec.games delivers [wgood] from the
    COMMIT assert), the stored signature size (G_forge_uniformchains samples one root
    per digit of a length-chain_count digest), the verification of the forgery
    against the stored public key, and log-freshness ([notin_log_neq]
    below).  Each disjunct carries the data its reduction feeds to
    the corresponding check oracle (header). *)

Lemma shrincs_wots_forgery_classify
    (Hrange : grind_range P)
    pp (m mstar : wcp_M P) (c cstar : nat) (sg ystar : seq (wcp_N P)) (y0 : wcp_N P) :
  good_counter P pp m c ->
  size sg = wcp_chain_count P ->
  shrincs_wots_verify P pp
    (wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg))
    mstar (ystar, cstar) ->
  mstar != m ->
  [\/ (* 1: GRIND — SCHECK (0, (mstar, cstar)) wins STCRP(H_grind) *)
      wcp_H_grind P pp (grind_adrs P) (mstar, cstar) = wcp_H_grind P pp (grind_adrs P) (m, c)
   ,  (* 2: COMPRESS — CHECK (0, forged ends) wins SM-TCR(T_sf) *)
      complete_ends P pp (digest_of P pp mstar cstar) ystar
        != complete_ends P pp (digest_of P pp m c) sg
      /\ wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp mstar cstar) ystar)
         = wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)
   ,  (* 3: CHAIN COLLISION — CHECK (tcr_index w d i k, u) wins
         SM-TCR(F) at tweak encode_tweak (chain_adrs i k); the stored
         target input is the honest chain value u is compared to *)
      exists i k (u : wcp_N P),
        [/\ i < wcp_chain_count P,
            nth 0 (digest_of P pp m c) i <= k < (wcp_w P).-1,
            u != chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) (nth y0 sg i) (nth 0 (digest_of P pp m c) i)
                       (k - nth 0 (digest_of P pp m c) i)
          & wcp_F P pp (chain_adrs P i k) u
            = wcp_F P pp (chain_adrs P i k)
                (chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) (nth y0 sg i) (nth 0 (digest_of P pp m c) i)
                       (k - nth 0 (digest_of P pp m c) i))]
   |  (* 4: CHAIN MEET — PCHECK (pre-index of i, preimage) wins
         SM-PRE(F) at tweak encode_tweak (chain_adrs i (d_i - 1)) *)
      exists i,
        [/\ i < wcp_chain_count P,
            nth 0 (digest_of P pp mstar cstar) i < nth 0 (digest_of P pp m c) i
          & wcp_F P pp (chain_adrs P i (nth 0 (digest_of P pp m c) i).-1)
              (chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) (nth y0 ystar i)
                     (nth 0 (digest_of P pp mstar cstar) i)
                     ((nth 0 (digest_of P pp m c) i).-1
                        - nth 0 (digest_of P pp mstar cstar) i))
            = nth y0 sg i]
  ].
Proof.
move=> hgood hsg hver hne.
have hvd : valid_digest P (digest_of P pp m c) := hgood.
move: hver; rewrite /shrincs_wots_verify /= => /and3P[hvd' /eqP hsy /eqP hTl].
case: (altP (digest_of P pp mstar cstar =P digest_of P pp m c)) => [heqd|hned].
- (* 1: equal digit vectors *)
  by apply: Or41; apply: (wdigest_inj pp mstar cstar m c Hrange heqd).
- case: (altP (complete_ends P pp (digest_of P pp mstar cstar) ystar
                 =P complete_ends P pp (digest_of P pp m c) sg)) => [heqe|hnee]; last first.
  + (* 2: distinct ends, equal compression (from verification) *)
    by apply: Or42; split.
  + (* 3/4: equal ends; select the down-going chain and classify *)
    have hvm : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c)
      := vdigest_valid_msg pp m c hvd.
    have hvm' : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp mstar cstar)
      := vdigest_valid_msg pp mstar cstar hvd'.
    have [i hi hlt] := forged_digit_lt (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c)
                         (digest_of P pp mstar cstar) hvm hvm' hned.
    have hdw : nth 0 (digest_of P pp m c) i < wcp_w P
      := valid_msg_digit (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c) i hvm hi.
    have hsz : size (digest_of P pp m c) = wcp_chain_count P
      := size_digest_of P pp m c.
    have hsz' : size (digest_of P pp mstar cstar) = wcp_chain_count P
      := size_digest_of P pp mstar cstar.
    have hch := wcends_nth_eq pp _ _ _ _ y0 i hsz' hsy hsz hsg hi heqe.
    have := shrincs_wots_chain_cases pp i (nth 0 (digest_of P pp m c) i) (nth y0 sg i)
              (nth 0 (digest_of P pp mstar cstar) i) (nth y0 ystar i) hlt hdw hch.
    case: (chain_extract _ _ _ _ _ _) => [k u v|].
    * (* 3 *)
      case=> hk hv hneuv hcol.
      apply: Or43; exists i, k, u.
      by rewrite -hv; split.
    * (* 4 *)
      move=> hmeet.
      apply: Or44; exists i; split=> //.
      exact: (shrincs_wots_pre_preimage pp i (nth 0 (digest_of P pp m c) i)
               (nth y0 sg i) (nth y0 ystar i)
               (nth 0 (digest_of P pp mstar cstar) i) hlt hdw hmeet).
Qed.

(** KFORGE's log freshness in the form the classifier consumes (the
    log of G_forge_sampledkey/G_forge_uniformchains is the single signed message). *)
Lemma notin_log_neq (m mstar : wcp_M P) : mstar \notin [:: m] -> mstar != m.
Proof. by rewrite inE. Qed.

(* ------------------------------------------------------------------ *)
(** *** Case-3 target bookkeeping at encoded chain addresses

    The chain library's committed-target list [tcr_targets] (one
    target per (chain, position >= signed digit), lexicographic, list
    position = CHECK index) re-tagged with encoded chain addresses;
    positions are untouched, so the library's [tcr_index w] and
    [tcr_index_lt] are consumed unchanged (no wrapper here). *)

Definition shrincs_wots_tweak (ik : nat * nat) : wc_adrs_ch P :=
  chain_tweak P ik.1 ik.2.

(** Distinct in-range (chain, position) pairs are distinct tweaks — the
    TQUERY freshness asserts and the CHECK index mapping rest on this.
    Because the exact tweak is the encoded address whose chain/position
    fields are clamped at [chain_count]/[w.-1], injectivity is CONDITIONAL
    on the indices being in range; the consumers discharge those ranges
    from [tcr_targets_mem_range] (every committed target is in range). *)
Lemma shrincs_wots_tweak_inj (ik ik' : nat * nat) :
  (ik.1 < wcp_chain_count P)%nat -> (ik'.1 < wcp_chain_count P)%nat ->
  (ik.2 < (wcp_w P).-1)%nat -> (ik'.2 < (wcp_w P).-1)%nat ->
  shrincs_wots_tweak ik = shrincs_wots_tweak ik' -> ik = ik'.
Proof.
move: ik ik' => [i k] [i' k'] /= hi hi' hk hk'.
rewrite /shrincs_wots_tweak /= => Heq.
by have [-> ->] := chain_tweak_inj P i k i' k' hi hi' hk hk' Heq.
Qed.

Definition shrincs_wots_tcr_targets (pp : wcp_PP P) (ds : seq nat) (sigs : seq (wcp_N P)) :
    seq (wc_adrs_ch P * wcp_N P) :=
  [seq (shrincs_wots_tweak q.1, q.2)
  | q <- tcr_targets (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs].

Lemma size_wotsc_tcr_targets pp (ds : seq nat) (sigs : seq (wcp_N P)) :
  size ds = wcp_chain_count P -> size sigs = wcp_chain_count P ->
  size (shrincs_wots_tcr_targets pp ds sigs) = sumn [seq (wcp_w P).-1 - d | d <- ds].
Proof.
move=> h1 h2; rewrite size_map.
exact: (size_tcr_targets (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs h1 h2).
Qed.

(** The SM-TCR budget [chain_count * w] suffices for the full list. *)
Lemma size_wotsc_tcr_targets_leq pp (ds : seq nat) (sigs : seq (wcp_N P)) :
  size ds = wcp_chain_count P -> size sigs = wcp_chain_count P ->
  size (shrincs_wots_tcr_targets pp ds sigs) <= wcp_chain_count P * wcp_w P.
Proof.
move=> h1 h2; rewrite size_map.
exact: (size_tcr_targets_leq (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs h1 h2).
Qed.

(** The CHECK index of target (i, k) is in range. *)
Lemma shrincs_wots_tcr_index_lt pp (ds : seq nat) (sigs : seq (wcp_N P)) i k :
  size ds = wcp_chain_count P -> size sigs = wcp_chain_count P ->
  i < wcp_chain_count P -> nth 0 ds i <= k < (wcp_w P).-1 ->
  tcr_index (wcp_w P) ds i k < size (shrincs_wots_tcr_targets pp ds sigs).
Proof.
move=> h1 h2 hi hk.
rewrite size_wotsc_tcr_targets //.
exact: (tcr_index_lt (wcp_chain_count P) (wcp_w P) ds i k h1 hi hk).
Qed.

(** THE bookkeeping lemma: at CHECK index [tcr_index w ds i k] the
    reduction committed exactly the encoded chain address (i, k) with
    input the honest chain value at [k] (recomputed from the [i]-th
    signature value) — disjunct 3 of [shrincs_wots_forgery_classify] maps to
    a winning CHECK query against this target. *)
Lemma shrincs_wots_tcr_targets_nth pp (ds : seq nat) (sigs : seq (wcp_N P)) i k
    (x0 : wc_adrs_ch P * wcp_N P) (y0 : wcp_N P) :
  size ds = wcp_chain_count P -> size sigs = wcp_chain_count P ->
  i < wcp_chain_count P -> nth 0 ds i <= k < (wcp_w P).-1 ->
  nth x0 (shrincs_wots_tcr_targets pp ds sigs) (tcr_index (wcp_w P) ds i k)
  = (shrincs_wots_tweak (i, k),
     chain (Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) (Fw P) pp i) (nth y0 sigs i) (nth 0 ds i) (k - nth 0 ds i)).
Proof.
move=> hds hsigs hi hk.
have hlt : tcr_index (wcp_w P) ds i k
             < size (tcr_targets (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs).
  rewrite (size_tcr_targets (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs hds hsigs).
  exact: (tcr_index_lt (wcp_chain_count P) (wcp_w P) ds i k hds hi hk).
rewrite /shrincs_wots_tcr_targets (nth_map ((0, 0), y0)) //.
by rewrite (tcr_targets_nth (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs i k ((0, 0), y0) y0).
Qed.

(** Tweak distinctness of the committed list (the TQUERY freshness
    assert passes at every commit in list order). *)
Lemma shrincs_wots_tcr_targets_tweaks_uniq pp (ds : seq nat) (sigs : seq (wcp_N P)) :
  size ds = wcp_chain_count P -> uniq (unzip1 (shrincs_wots_tcr_targets pp ds sigs)).
Proof.
move=> hds.
have he : (fst \o (fun q : (nat * nat) * (wcp_N P) => (shrincs_wots_tweak q.1, q.2)))
            =1 (shrincs_wots_tweak \o fst).
  by [].
have hinj : {in unzip1 (tcr_targets (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs) &,
              injective shrincs_wots_tweak}.
  move=> x y hx hy.
  have [hx1 hx2] := tcr_targets_mem_range (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs x hds hx.
  have [hy1 hy2] := tcr_targets_mem_range (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs y hds hy.
  exact: (shrincs_wots_tweak_inj x y hx1 hy1 hx2 hy2).
rewrite /shrincs_wots_tcr_targets /unzip1 -map_comp (eq_map he) map_comp.
rewrite (map_inj_in_uniq hinj).
exact: (tcr_targets_tweaks_uniq (wcp_PP P) (wcp_N P) (Fw P) (wcp_chain_count P) (wcp_w P) pp ds sigs hds).
Qed.

End WOTSCAnalysis.
