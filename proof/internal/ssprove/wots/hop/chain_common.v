(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.chain_common

    Shared substrate of the two chain hops [Sec.hop.chain_tcr]
    (SM-TCR(F), G_post_compress -> G_post_chain) and [Sec.hop.chain_pre] (SM-PRE(F),
    G_post_chain -> G_forge_uniformchains-ideal): the section context and tweak/notation
    abbreviations, the pure re-tagging of the abstract chain
    bookkeeping into encoded addresses ([wq] and friends), the bridge
    lemmas turning a WOTS+C forgery into a chain forgery against the
    honest key ([verify_from_ends] +
    [wtcr_decisionP]/[wpre_decisionP]/[wclassify_some]).  The shared
    [G_post_chain] endpoint of both chain hops is defined in
    [Sec.hop.intermediates] (re-abbreviated by each half); keeping
    this substrate in its own file lets the TCR and PRE proofs
    type-check in parallel. *)

From mathcomp.experimental_reals Require Import distr.
From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf games.smtcr games.smpre toolkit.sample_seq toolkit.relational_rules.
From Model Require Import math.chain math.encoding.
From Sec.lib Require Import chain.core.
From Sec Require Import addressing.
From Sec.wots Require Import addressing.
From Sec.wots Require Import scheme games analysis.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** [qnth] through a map (companion to [qnth_cat_l/r]) *)

Lemma qnth_map {X Y : Type} (f : X -> Y) (s : seq X) (i : nat) :
  qnth [seq f x | x <- s] i = omap f (qnth s i).
Proof. by rewrite /qnth -map_drop; case: (drop i s). Qed.

(** A found committed entry's tweak is a member of the tweak list. *)
Lemma qnth_mem_unzip1 {X Y : eqType} (s : seq (X * Y)) j t v :
  qnth s j = Some (t, v) -> t \in [seq p.1 | p <- s].
Proof.
rewrite /qnth; case E: (drop j s) => [|a r] //= [= ea].
rewrite ea in E.
have hs : (t, v) \in s.
  rewrite -(cat_take_drop j s) E mem_cat.
  by apply/orP; right; apply: mem_head.
exact: (map_f (fun p : X * Y => p.1) hs).
Qed.

Section ChainCommon.

(** The WOTS+C parameter record (see Sec.wots.params), as in
    Sec.wots.games. *)
Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the re-tagging into encoded tweaks

    The chain bookkeeping lists ([commit_queries], [pre_queries]) live
    over abstract (chain, position) tweaks; the SM-TCR/SM-PRE games on
    [thf_chain] store ENCODED addresses.  [wq] re-tags one committed entry;
    positions are untouched, so all indices ([q_index], [pre_index])
    are consumed unchanged. *)

Local Abbreviation qentry := ((nat * nat) * wcp_N P)%type.

Definition wq (q : qentry) : wc_adrs_ch P * wcp_N P := (shrincs_wots_tweak P q.1, q.2).

(** [unzip1] commutes with the re-tagging. *)
Lemma unzip1_wq (Q : seq qentry) :
  unzip1 [seq wq q | q <- Q] = [seq shrincs_wots_tweak P t | t <- unzip1 Q].
Proof. by rewrite /unzip1 -!map_comp; apply: eq_map => q. Qed.

(** Freshness transfers along the re-tagging.  The tweak encoding is
    only injective on in-range (chain, position) pairs (the exact tweak
    clamps out-of-range indices), so freshness transfer is CONDITIONAL on
    the queried tweak and every earlier tweak being in range; the
    consumers discharge those ranges from [tcr_targets_mem_range]. *)
Lemma wtw_notin (t : nat * nat) (ts : seq (nat * nat)) :
  (t.1 < wcp_chain_count P)%nat -> (t.2 < (wcp_w P).-1)%nat ->
  (forall t', t' \in ts -> (t'.1 < wcp_chain_count P)%nat /\ (t'.2 < (wcp_w P).-1)%nat) ->
  t \notin ts -> shrincs_wots_tweak P t \notin [seq shrincs_wots_tweak P t' | t' <- ts].
Proof.
move=> ht1 ht2 hts hnotin.
apply/negP => /mapP[t' ht' e].
have [ht'1 ht'2] := hts t' ht'.
have heq : t = t' := shrincs_wots_tweak_inj P t t' ht1 ht'1 ht2 ht'2 e.
by move: ht'; rewrite -heq (negbTE hnotin).
Qed.

(** [th_eval thf_chain] at a chain tweak is the wrapped chain hash: decoding
    the untruncated chain tweak reproduces exactly the concrete chain
    address ([decode_chain_tweak]), so [th_eval] computes the
    scheme's real [F] at that address -- the untruncated index encoding
    is invisible to the hash. *)
Lemma th_eval_wtw pp (t : nat * nat) (x : wcp_N P) :
  th_eval (thf_chain P) pp (shrincs_wots_tweak P t) x = wcp_F P pp (chain_adrs P t.1 t.2) x.
Proof.
by rewrite /shrincs_wots_tweak /th_eval /thf_chain /thf_chain_core /= core_decodeE decode_chain_tweak.
Qed.

(** In range, the SM-TCR(F) oracle at a chain tweak IS the abstract total
    chain step [Fc]: [th_eval TF (wtw t)] evaluates [F] at the exact
    chain address, which is [Fc]'s in-range value ([FcE]).  This is the
    bridge the relational cores use to identify oracle answers with the
    [chainc]/[Fc]-computed chain values (positions are always [< w.-1 < w]). *)
Lemma Fc_wtw pp (t : nat * nat) (x : wcp_N P) :
  (t.2 < wcp_w P)%N ->
  th_eval (thf_chain P) pp (shrincs_wots_tweak P t) x
  = Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t x.
Proof.
case: t => t1 t2 htw.
by rewrite (th_eval_wtw pp (t1, t2) x) (FcE (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t1 t2 x htw).
Qed.

(** Every tweak committed by the chain queries has position [< w.-1]
    (sigma below the digit, walk up to [w.-2]); needed to discharge the
    [< w] guard of [Fc_wtw] at every committed target. *)
Lemma commit_queries_pos_all pp st (ds : seq nat) (us : seq (wcp_N P)) :
  size us = size ds ->
  all (λ d : nat, (d < wcp_w P)%N) ds ->
  all (λ t : nat * nat, (t.2 < (wcp_w P).-1)%N) (unzip1 (wcommitq P pp st ds us)).
Proof.
elim: ds st us => [|d ds IH] st [|u us] //= [hsz] /andP[hd hds].
rewrite /wcommitq (commit_queries_cons (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P)) unzip1_cat all_cat.
apply/andP; split; last exact: IH.
have hdle : (d <= (wcp_w P).-1)%N by rewrite -ltnS (ltn_predK (wcp_Hw P)).
rewrite /chain_queries unzip1_cat all_cat; apply/andP; split.
- case: d hd hdle => [|d'] hd hdle //=.
  by rewrite andbT.
- have hk : (d + ((wcp_w P).-1 - d) <= (wcp_w P).-1)%N by rewrite subnKC.
  exact: (walkq_tweak2 (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp st d ((wcp_w P).-1 - d) _ (wcp_w P).-1 hk).
Qed.

(** THE bridge consumed by the KFORGE tails: a committed target of a
    valid message evaluates its SM-TCR(F) oracle as the abstract [Fc]. *)
Lemma wcheck_bridge pp (m : wcp_M P) (c : nat) (us : seq (wcp_N P)) j t v (x : wcp_N P) :
  good_counter P pp m c -> size us = wcp_chain_count P ->
  qnth (wcommitq P pp 0 (digest_of P pp m c) us) j = Some (t, v) ->
  th_eval (thf_chain P) pp (shrincs_wots_tweak P t) x
  = Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t x.
Proof.
move=> hgood hus hqn.
have hsz : size (digest_of P pp m c) = wcp_chain_count P
  := size_digest_of P pp m c.
have /andP[hwf _] := hgood.
have hpos := commit_queries_pos_all pp 0 (digest_of P pp m c) us
               (etrans hus (esym hsz)) hwf.
have hin := qnth_mem_unzip1 _ _ _ _ hqn.
have htlt := allP hpos t hin.
apply: Fc_wtw.
have hwpred : ((wcp_w P).-1 < wcp_w P)%N by rewrite ltn_predL; exact: (ltnW (wcp_Hw P)).
exact: (ltn_trans htlt hwpred).
Qed.

(** The SM-PRE analogue: every committed PQUERY tweak has position
    [< w.-1] (it is one below a positive digit [< w]). *)
Lemma pre_queries_pos_all st (ds : seq nat) (us : seq (wcp_N P)) :
  size us = size ds ->
  all (λ d : nat, (d < wcp_w P)%N) ds ->
  all (λ t : nat * nat, (t.2 < (wcp_w P).-1)%N) (unzip1 (wpreq P st ds us)).
Proof.
elim: ds st us => [|d ds IH] st [|u us] //= [hsz] /andP[hd hds].
rewrite /wpreq (pre_queries_cons (wcp_N P)) unzip1_cat all_cat.
apply/andP; split; last exact: IH.
have hdle : (d <= (wcp_w P).-1)%N by rewrite -ltnS (ltn_predK (wcp_Hw P)).
case: d hd hdle => [|d'] hd hdle //=.
by rewrite andbT.
Qed.

(** The PRE bridge consumed by the KFORGE tail. *)
Lemma wpre_check_bridge pp (m : wcp_M P) (c : nat) (us : seq (wcp_N P)) j t v (x : wcp_N P) :
  good_counter P pp m c -> size us = wcp_chain_count P ->
  qnth (wpreq P 0 (digest_of P pp m c) us) j = Some (t, v) ->
  th_eval (thf_chain P) pp (shrincs_wots_tweak P t) x
  = Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t x.
Proof.
move=> hgood hus hqn.
have hsz : size (digest_of P pp m c) = wcp_chain_count P
  := size_digest_of P pp m c.
have /andP[hwf _] := hgood.
have hpos := pre_queries_pos_all 0 (digest_of P pp m c) us
               (etrans hus (esym hsz)) hwf.
have hin := qnth_mem_unzip1 _ _ _ _ hqn.
have htlt := allP hpos t hin.
apply: Fc_wtw.
have hwpred : ((wcp_w P).-1 < wcp_w P)%N by rewrite ltn_predL; exact: (ltnW (wcp_Hw P)).
exact: (ltn_trans htlt hwpred).
Qed.

(** Conversion bridge: the COLLQ answer at the grinding address,
    post-processed by the loop's [inr]-projection, IS the scheme's
    H_grind output (canonical tweaks compute).  Shared by both chain
    halves (each uses it once in its COMMIT). *)
Lemma ct_collq_H_E pp (m : wcp_M P) (c : nat) :
  (if tc_eval (coll_chain P) pp (encode_tweak P (grind_adrs P)) (inr (m, c)) is inr h then h else 0)
  = wcp_H_grind P pp (grind_adrs P) (m, c).
Proof.
rewrite /tc_eval /coll_chain /coll_chain_core /=.
congr wcp_H_grind.
rewrite core_decodeE.
exact: (encode_tweakK P (grind_adrs P)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the CHAIN branch is a chain forgery

    In the CHAIN branch of G_post_compress's KFORGE the discriminants provide:
    a VALID forged digit vector (verification), [size ystar = chain_count]
    (verification), and completed ends that HIT the honest ones (the
    negated COMPRESS discriminant).  That is literally a verifying
    chain forgery at [Fw] against the honest [ends_from_sig] key —
    [verify_from_ends] — which feeds the classifier specs below. *)

(** Completing a forged signature against its own completion list
    passes every chain check (each check is [x == x]). *)
Lemma all_check_refl pp st n (ds : seq nat) (ys : seq (wcp_N P)) :
  all (fun q => chain_check (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st n)
           (zip ds (zip ys
              [seq chainc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp q.1 q.2.2 q.2.1 ((wcp_w P).-1 - q.2.1)
              | q <- zip (iota st n) (zip ds ys)]))).
Proof.
elim: n st ds ys => [|n IH] st ds ys;
  first by case: ds => [|d ds]; case: ys => [|y ys].
case: ds => [|d ds]; case: ys => [|y ys] => //=.
apply/andP; split; last exact: IH.
by rewrite /chain_check eqxx.
Qed.

(** THE bridge: equal completed ends turn the shrincs_wots_scheme forgery data into
    a verifying chain forgery against the honest key. *)
Lemma verify_from_ends pp (mstar ds : seq nat) (ystar sg : seq (wcp_N P)) :
  valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) mstar ->
  (size ystar == wcp_chain_count P)%B ->
  ends_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp mstar ystar
    = ends_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp ds sg ->
  verify_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P) pp
    (ends_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp ds sg) mstar ystar.
Proof.
move=> hvm hys heq.
rewrite /Sec.lib.chain.core.verify_sig hvm hys /=.
rewrite -heq /ends_from_sig.
exact: all_check_refl.
Qed.

(** The classifier specs at shrincs_wots_scheme hypotheses (the reductions' CHAIN
    branches consume exactly these).  Hypotheses are what the KFORGE
    discriminants provide: grinding success of the signed counter,
    the stored-roots shape, the forged digest's validity and
    signature size (verification), the ends EQUALITY (negated
    COMPRESS discriminant) and the digit-vector freshness (negated
    GRIND discriminant). *)

Lemma wtcr_decisionP pp (m mstar : wcp_M P) (c cstar : nat) (us ystar : seq (wcp_N P)) :
  good_counter P pp m c -> size us = wcp_chain_count P ->
  valid_digest P (digest_of P pp mstar cstar) -> (size ystar == wcp_chain_count P)%B ->
  complete_ends P pp (digest_of P pp mstar cstar) ystar
    = complete_ends P pp (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us) ->
  digest_of P pp mstar cstar != digest_of P pp m c ->
  match wtcr_dec P pp (digest_of P pp m c) (digest_of P pp mstar cstar)
          (wsigs P pp 0 (digest_of P pp m c) us) ystar with
  | Some (j, u) =>
      exists t v,
        [/\ qnth (wcommitq P pp 0 (digest_of P pp m c) us) j = Some (t, v),
            u != v
          & Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t u
            = Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t v]
  | None => True
  end.
Proof.
move=> hgood hus hvd' hys hends hned.
have hvm : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c)
  := vdigest_valid_msg P pp m c hgood.
have hvm' : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp mstar cstar)
  := vdigest_valid_msg P pp mstar cstar hvd'.
have hd : size (digest_of P pp m c) = wcp_chain_count P
  := size_digest_of P pp m c.
have hver : verify_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P) pp
    (ends_of (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp 0 (digest_of P pp m c)
       (wsigs P pp 0 (digest_of P pp m c) us))
    (digest_of P pp mstar cstar) ystar.
  rewrite (ends_of_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp _ _ hd).
  by apply: verify_from_ends.
have hnin : digest_of P pp mstar cstar \notin [:: digest_of P pp m c].
  by rewrite inE.
exact: (tcr_decisionP (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P)
          pp _ _ us ystar hvm hus hver hnin).
Qed.

Lemma wpre_decisionP pp (m mstar : wcp_M P) (c cstar : nat) (us ystar : seq (wcp_N P)) :
  good_counter P pp m c -> size us = wcp_chain_count P ->
  valid_digest P (digest_of P pp mstar cstar) -> (size ystar == wcp_chain_count P)%B ->
  complete_ends P pp (digest_of P pp mstar cstar) ystar
    = complete_ends P pp (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us) ->
  digest_of P pp mstar cstar != digest_of P pp m c ->
  match wpre_dec P pp (digest_of P pp m c) (digest_of P pp mstar cstar)
          (wsigs P pp 0 (digest_of P pp m c) us) ystar with
  | Some (j, x) =>
      exists t u,
        qnth (wpreq P 0 (digest_of P pp m c) us) j = Some (t, u)
        /\ Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t x
           = Fc (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) pp t u
  | None => True
  end.
Proof.
move=> hgood hus hvd' hys hends hned.
have hvm : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c)
  := vdigest_valid_msg P pp m c hgood.
have hvm' : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp mstar cstar)
  := vdigest_valid_msg P pp mstar cstar hvd'.
have hver : verify_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P) pp
    (ends_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp
       (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us))
    (digest_of P pp mstar cstar) ystar.
  by apply: verify_from_ends.
have hnin : digest_of P pp mstar cstar \notin [:: digest_of P pp m c].
  by rewrite inE.
exact: (pre_decisionP (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P)
          pp _ _ us ystar hvm hus hver hnin).
Qed.

(** Classifier totality on the CHAIN branch: if ChainColl declined,
    ChainMeet fires (the ideal-side dead branch of R_chain_pre). *)
Lemma wclassify_some pp (m mstar : wcp_M P) (c cstar : nat) (us ystar : seq (wcp_N P)) :
  good_counter P pp m c -> size us = wcp_chain_count P ->
  valid_digest P (digest_of P pp mstar cstar) -> (size ystar == wcp_chain_count P)%B ->
  complete_ends P pp (digest_of P pp mstar cstar) ystar
    = complete_ends P pp (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us) ->
  digest_of P pp mstar cstar != digest_of P pp m c ->
  wtcr_dec P pp (digest_of P pp m c) (digest_of P pp mstar cstar)
    (wsigs P pp 0 (digest_of P pp m c) us) ystar = None ->
  wpre_dec P pp (digest_of P pp m c) (digest_of P pp mstar cstar)
    (wsigs P pp 0 (digest_of P pp m c) us) ystar != None.
Proof.
move=> hgood hus hvd' hys hends hned.
have hvm : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp m c)
  := vdigest_valid_msg P pp m c hgood.
have hvm' : valid_msg (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (digest_of P pp mstar cstar)
  := vdigest_valid_msg P pp mstar cstar hvd'.
have hver : verify_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P) pp
    (ends_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp
       (digest_of P pp m c) (wsigs P pp 0 (digest_of P pp m c) us))
    (digest_of P pp mstar cstar) ystar.
  by apply: verify_from_ends.
have hnin : digest_of P pp mstar cstar \notin [:: digest_of P pp m c].
  by rewrite inE.
exact: (classify_some (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (wcp_constant_sum P) (Fw P)
          pp _ _ us ystar hvm hus hver hnin).
Qed.

(* ------------------------------------------------------------------ *)
(** ** G_post_chain (the chain hops' shared endpoint)

    [G_post_chain] (G_post_compress with ALSO the ChainColl answers of the shared
    classifier nulled) is defined in [Sec.hop.intermediates] so the
    hops type-check in parallel; the two chain halves abbreviate it as
    [intermediates.G_post_chain] under their own context. *)

End ChainCommon.
