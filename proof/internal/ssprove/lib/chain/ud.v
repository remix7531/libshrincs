(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.chain.ud

    The PURE per-chain sampling-map layer of the SM-UD hybrid argument
    for a Winternitz-style chain signature, generic over the tweakable
    hash [F].  Every hybrid/reduction game samples ONE uniform value per
    chain and post-processes it purely; these are the post-processings
    as maps over (digit list, sampled list), plus the identities between
    them that the hybrid endpoints and the reduction's real/ideal
    answers require, and the two reference-sampler couplings.

    - [roots_map s]: the hybrid's signature digits (root at position
      [minn s d.-1], chained up to the digit).
    - [uq_real_map s]: what the real SM-UD oracle hands the reduction
      ([F pp (i,s) x] for the queried chains, the raw root otherwise).
    - [rud_sig s]: how the reduction turns oracle answers into signature
      digits.
    - [sig_map]: [chain.core.sample_sig_roots]'s post-processing (one
      [F]-step below the digit).

    Identities: [rud_sig_real]/[rud_sig_ideal] (reduction answers are the
    neighbouring hybrids), [roots_map_sign]/[ends_from_roots_map0] (the
    [s = 0] endpoint is the honest [sign_digits]/[chain_ends]),
    [sig_map_roots] (the [s = w.-2] endpoint is the [sample_sig_roots]
    shape).  The sampler couplings [r_sample_seq_size]/[r_sample_sig_roots]
    feed a continuation the size of the sampled list resp. the pure
    post-processing, under an arbitrary precondition.

    Generic over [F]; WOTS+C instantiates at the address-wrapped chain
    hash [Fw].  The generic one-sided relational rules used here live in
    [toolkit.relational_rules]. *)

From Shrincs.internal.ssprove.lib Require Import prelude sig.scheme
  toolkit.sample_seq toolkit.relational_rules chain.core.
From Shrincs.internal.common Require Import math.chain math.encoding.

Import PackageNotation.
#[local] Open Scope package_scope.

Section ChainUD.

Context (PP N : choice_type).
Context (l w : nat).
(** Position-tweaked hash in [Model.math.chain]'s DEPENDENT shape (the
    abstract [F'] of [Sec.lib.chain.core]): all chain walks below go
    through the total fold [chainc] and its total step [Fc]. *)
Context (F' : PP -> nat -> forall p : nat, (p < w)%N -> N -> N).
Context (dN : dist N).

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the per-chain sampling maps *)

Fixpoint roots_map (pp : PP) (s i : nat) (m : seq nat) (xs : seq N)
    {struct m} : seq N :=
  match m, xs with
  | d :: m', x :: xs' =>
      chainc PP N w F' pp i x (minn s d.-1) (d - minn s d.-1)
        :: roots_map pp s i.+1 m' xs'
  | _, _ => [::]
  end.

Fixpoint uq_real_map (pp : PP) (s i : nat) (m : seq nat) (xs : seq N)
    {struct m} : seq N :=
  match m, xs with
  | d :: m', x :: xs' =>
      (if s.+2 <= d then Fc PP N w F' pp (i, s) x else x)
        :: uq_real_map pp s i.+1 m' xs'
  | _, _ => [::]
  end.

Fixpoint rud_sig (pp : PP) (s i : nat) (m : seq nat) (ys : seq N)
    {struct m} : seq N :=
  match m, ys with
  | d :: m', y :: ys' =>
      (if s.+2 <= d
       then chainc PP N w F' pp i y s.+1 (d - s.+1)
       else chainc PP N w F' pp i y (minn s d.-1) (d - minn s d.-1))
        :: rud_sig pp s i.+1 m' ys'
  | _, _ => [::]
  end.

Fixpoint sig_map (pp : PP) (i : nat) (m : seq nat) (xs : seq N)
    {struct m} : seq N :=
  match m, xs with
  | d :: m', x :: xs' =>
      (if d is d'.+1 then Fc PP N w F' pp (i, d') x else x)
        :: sig_map pp i.+1 m' xs'
  | _, _ => [::]
  end.

(* ------------------------------------------------------------------ *)
(** *** Pure identities between the maps *)

(** Digit arithmetic for the queried chains ([d >= s + 2]). *)
Let big_digit_pred s d : s.+2 <= d -> s.+1 <= d.-1.
Proof.
move=> hd.
have h0d : 0 < d := leq_trans (ltn0Sn s.+1) hd.
by rewrite -ltnS (ltn_predK h0d).
Qed.

(** The reduction's post-processing of the REAL oracle answers is the
    [roots_map s] sampling map: queried chains walk [F pp (i,s) x] from
    [s+1], which is the root [x] at [s] walked one step further. *)
Lemma rud_sig_real (pp : PP) (s i : nat) (m : seq nat) (xs : seq N) :
  rud_sig pp s i m (uq_real_map pp s i m xs) = roots_map pp s i m xs.
Proof.
elim: m i xs => [|d m IH] i [|x xs] //=.
case: (boolP (s.+2 <= d)) => hd; rewrite IH //.
congr cons.
have hs1 : s.+1 <= d.-1 := big_digit_pred _ _ hd.
have hsd : s < d := ltnW hd.
have -> : minn s d.-1 = s by apply/minn_idPl; exact: ltnW hs1.
have -> : d - s = (d - s.+1).+1 by rewrite subnS prednK // subn_gt0.
by rewrite (chainc_shift PP N w F' pp i x s (d - s.+1)).
Qed.

(** The reduction's post-processing of the IDEAL oracle answers (the
    raw fresh values) is the [roots_map s.+1] sampling map. *)
Lemma rud_sig_ideal (pp : PP) (s i : nat) (m : seq nat) (ys : seq N) :
  rud_sig pp s i m ys = roots_map pp s.+1 i m ys.
Proof.
elim: m i ys => [|d m IH] i [|y ys] //=.
rewrite IH; congr cons.
case: (boolP (s.+2 <= d)) => hd.
- have hs1 : s.+1 <= d.-1 := big_digit_pred _ _ hd.
  by rewrite (minn_idPl hs1).
- rewrite -ltnNge ltnS in hd.
  have hds : d.-1 <= s by rewrite -subn1 leq_subLR add1n.
  by rewrite (minn_idPr hds) (minn_idPr (leq_trans hds (leqnSn s))).
Qed.

(** Endpoint [s = 0]: roots at position 0, signature digit = the honest
    chain walk. *)
Lemma roots_map0E (pp : PP) (i : nat) (ds : seq nat) (xs : seq N) :
  roots_map pp 0 i ds xs
  = [seq chainc PP N w F' pp q.1.1 q.1.2 0 q.2
    | q <- zip (zip (iota i (size ds)) xs) ds].
Proof.
by elim: ds i xs => [|d ds IH] i [|x xs] //=; rewrite min0n subn0 IH.
Qed.

Lemma roots_map_sign (pp : PP) (m : seq nat) (xs : seq N) :
  size m = l ->
  roots_map pp 0 0 m xs = sign_digits PP N l w F' pp xs m.
Proof. by move=> hm; rewrite roots_map0E /sign_digits hm. Qed.

(** Endpoint [s = 0], public ends: completing the [roots_map 0] digit
    [chain x 0 d] with [w.-1 - d] more steps is the honest chain end
    [chain x 0 w.-1] ([chain_split]). *)
Lemma ends_roots_map0 (pp : PP) (i : nat) (ds : seq nat) (xs : seq N) :
  wf_digits w ds ->
  [seq chainc PP N w F' pp q.1 q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota i (size ds)) (zip ds (roots_map pp 0 i ds xs))]
  = [seq chainc PP N w F' pp ix.1 ix.2 0 w.-1 | ix <- zip (iota i (size ds)) xs].
Proof.
elim: ds i xs => [|d ds IH] i [|x xs] //= /andP[hd hds].
rewrite min0n subn0 IH //; congr cons.
have hdw : d <= w.-1 by rewrite -ltnS (ltn_predK hd).
have h := chainc_split PP N w F' pp i x 0 d w.-1 (leq0n d) hdw.
by rewrite !subn0 in h; rewrite -h.
Qed.

Lemma ends_from_roots_map0 (pp : PP) (m : seq nat) (xs : seq N) :
  size m = l -> wf_digits w m ->
  ends_from_sig PP N l w F' pp m (roots_map pp 0 0 m xs)
  = chain_ends PP N l w F' pp xs.
Proof.
move=> hm hwd.
by rewrite /ends_from_sig /chain_ends -hm ends_roots_map0.
Qed.

(** Endpoint [s = w.-2]: for valid digits ([d < w]) the root position
    [minn w.-2 d.-1] is [d.-1], so the [roots_map w.-2] digit is the
    [sample_sig_roots] shape ([x] itself for [d = 0], one [F]-step for
    [d > 0]). *)
Lemma sig_map_roots (pp : PP) (i : nat) (ds : seq nat) (xs : seq N) :
  wf_digits w ds ->
  sig_map pp i ds xs = roots_map pp w.-2 i ds xs.
Proof.
elim: ds i xs => [|d ds IH] i [|x xs] //= /andP[hd hds].
rewrite IH //; congr cons.
case: d hd => [|d'] hd.
- by rewrite minn0 subn0.
- have hle1 : d' < w.-1 by rewrite -ltnS (ltn_predK hd).
  have hle2 : d' <= w.-2 by rewrite -ltnS (ltn_predK hle1).
  by rewrite (minn_idPr hle2) subSnn.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Relational sampler couplings

    [sample_seq dN n] is the reference sampler of all games here; the
    two lemmas below couple it (identically) with itself resp. with
    [sample_sig_roots], handing the continuation the size of the sampled
    list resp. the pure post-processing.  Both are stated in
    continuation-passing form under an ARBITRARY precondition, via
    [toolkit.relational_rules.r_scheme_bind]. *)

Lemma r_sample_seq_size {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k₀ k₁ : chList N -> raw_code B) :
  (forall xs : seq N, size xs = n -> ⊢ ⦃ pre ⦄ k₀ xs ≈ k₁ xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xs ← sample_seq dN n ;; k₀ xs ≈ xs ← sample_seq dN n ;; k₁ xs
  ⦃ post ⦄.
Proof.
elim: n k₀ k₁ => [|n IH] k₀ k₁ hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact _|].
  move=> x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

Lemma r_sample_sig_roots {B : choiceType} (pp : PP) (i : nat)
    (m : seq nat) (pre : precond) (post : postcond B B)
    (k₀ k₁ : chList N -> raw_code B) :
  (forall xs : seq N, size xs = size m ->
    ⊢ ⦃ pre ⦄ k₀ (sig_map pp i m xs) ≈ k₁ xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    sg ← sample_sig_roots PP N w F' dN pp i m ;; k₀ sg
    ≈ xs ← sample_seq dN (size m) ;; k₁ xs
  ⦃ post ⦄.
Proof.
elim: m i k₀ k₁ => [|d m IH] i k₀ k₁ hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact _|].
  move=> x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

End ChainUD.
