(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.lib.chain.core

    The generic Winternitz-style chain-signature layer, generic over a
    tweakable hash [F].  This file is the MERGE of the former
    Shrincs.internal.ssprove.lib.chain.{Scheme, Sample, Forgery, Decision} — kept as one
    compilation unit (four [Section]s below) so the genuinely-serial
    content chain pays the SSProve load floor ONCE instead of four
    times.  The file opens with the generic seq/fmap/tweak helpers
    merged in from the former [Shrincs.internal.ssprove.lib.toolkit.QSeq] ([qnth], [qmap_from],
    [tweak_lt]); they live here rather than under [Toolkit] only so the
    merge keeps them on the right side of the load floor — a layering
    compromise for build time.  Then come the four former-[Chain.*]
    sections, in dependency order:

      - [ChainScheme]   : pure scheme machinery (chains, ends, signing,
                          verification);
      - [ChainSample]   : signature-root sampling for the SM-UD hybrid;
      - [ChainForgery]  : pure forgery analysis + TCR target bookkeeping;
      - [ChainDecisionTCR] / [ChainDecisionPRE] : the computable
                          SM-TCR / SM-PRE forgery classifiers.

    THE CHAIN STEP.  The abstract hash [F' : PP -> nat -> nat -> N -> N]
    takes a chain index and a position.  Every chain goes through the
    step [Fc], which applies [F'] at positions below [w] and is the
    identity at or above, and through the fold [chainc] over [Fc].
    Every position the scheme reaches is below [w.-1], so [FcE] always
    applies there.
    The composition algebra [chainc_cat] / [chainc_split] /
    [chainc_rcons] holds unconditionally.  [chain_searchc] /
    [chain_extractc] compare a forged chain against the honest one, with
    specification [chain_searchcP].

    See each section's header comment for details. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.sample_seq.
From Shrincs Require Export games.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ===== merged Shrincs.internal.ssprove.lib.toolkit.QSeq (generic seq/fmap/tweak helpers) ===== *)


(* ------------------------------------------------------------------ *)
(** ** Generic seq access: total nth via [ohead (drop i s)]

    The hash domain [N] is an abstract [choice_type] with no canonical
    inhabitant, so [nth] (which needs a default) is unusable inside
    code.  [qnth] is the option-valued variant; the lemmas connect it
    back to [nth] once a witness is at hand. *)

Section QNth.

Context {X : Type}.

Definition qnth (s : seq X) (i : nat) : option X := ohead (drop i s).

Lemma qnth_size (s : seq X) i x : qnth s i = Some x -> i < size s.
Proof.
rewrite /qnth; case: (ltnP i (size s)) => // hle.
by rewrite drop_oversize.
Qed.

Lemma qnth_nth (x0 : X) s i x : qnth s i = Some x -> nth x0 s i = x.
Proof.
by elim: s i => [|a s IH] [|i] //=; [case=> -> | exact: IH].
Qed.

Lemma qnth_some (s : seq X) i : i < size s -> exists x, qnth s i = Some x.
Proof.
move=> hi; rewrite /qnth; case E: (drop i s) => [|a r]; last by exists a.
have := size_drop i s; rewrite E /= => /esym/eqP.
by rewrite subn_eq0 leqNgt hi.
Qed.

Lemma qnth_cat_r (s t : seq X) j : qnth (s ++ t) (size s + j)%N = qnth t j.
Proof. by rewrite /qnth drop_cat ltnNge leq_addr /= addKn. Qed.

Lemma qnth_cat_l (s t : seq X) j : j < size s -> qnth (s ++ t) j = qnth s j.
Proof.
move=> hj; rewrite /qnth drop_cat hj.
case E: (drop j s) => [|a r] //=.
have := size_drop j s; rewrite E /= => /esym/eqP.
by rewrite subn_eq0 leqNgt hj.
Qed.

(** [qnth] through a cons (definitional; companion to [qnth_cat_l/r]). *)
Lemma qnth_cons (e : X) (s : seq X) (k : nat) :
  qnth (e :: s) k.+1 = qnth s k.
Proof. by []. Qed.

End QNth.

(* ------------------------------------------------------------------ *)
(** ** Insertion-ordered fmaps from lists

    SM-TCR's target map grows by [setm tgts (size tws) (t, m)], i.e.
    the j-th committed target lands at key j.  [qmap_from j Q] is the
    fmap holding list [Q] at keys [j, j+1, ...]; [qmap_from_rcons] is
    exactly the oracle's update step, [qmap_from_get] the CHECK-time
    lookup. *)

Section QMap.

Context {X : Type}.

Fixpoint qmap_from (j : nat) (Q : seq X) : {fmap nat -> X} :=
  if Q is e :: Q' then setm (qmap_from j.+1 Q') j e else emptym.

Lemma qmap_from_rcons j Q e :
  qmap_from j (rcons Q e) = setm (qmap_from j Q) (j + size Q)%N e.
Proof.
elim: Q j => [|a Q IH] j /=; first by rewrite addn0.
rewrite IH setmC; first by apply/negbT/gtn_eqF; rewrite addSn ltnS leq_addr.
by rewrite addSn addnS.
Qed.

Lemma qmap_from_get j Q i : getm (qmap_from j Q) (j + i)%N = qnth Q i.
Proof.
elim: Q j i => [|e Q IH] j i /=; first by rewrite emptymE /qnth; case: i.
rewrite setmE; case: i => [|i] /=.
- by rewrite addn0 eqxx.
- case: eqP => [heq|_].
  + have : j < (j + i.+1)%N by rewrite addnS ltnS leq_addr.
    by rewrite heq ltnn.
  + by rewrite -addSnnS IH.
Qed.

End QMap.

(* ------------------------------------------------------------------ *)
(** ** Tweak-order bookkeeping for freshness

    [tweak_lt i k t]: tweak [t] was committed strictly before position
    [(i, k)] in the reduction's per-chain order. *)

Definition tweak_lt (i k : nat) (t : nat * nat) : bool :=
  (t.1 < i) || ((t.1 == i) && (t.2 < k)).

Lemma tlt_notin i k (ts : seq (nat * nat)) :
  all (tweak_lt i k) ts -> (i, k) \notin ts.
Proof.
move=> /allP h; apply/negP => hin.
by have := h _ hin; rewrite /tweak_lt /= ltnn eqxx ltnn.
Qed.

Lemma all_tlt_widen i k (ts : seq (nat * nat)) :
  all (tweak_lt i k) ts -> all (tweak_lt i k.+1) ts.
Proof.
apply: sub_all => t; rewrite /tweak_lt => /orP[-> //|/andP[e hk]].
by rewrite e ltnS (ltnW hk) orbT.
Qed.

Lemma all_lt_tlt i k (ts : seq (nat * nat)) :
  all (λ t : nat * nat, t.1 < i) ts -> all (tweak_lt i k) ts.
Proof. by apply: sub_all => t; rewrite /tweak_lt => ->. Qed.

Lemma lt_notin st d' (ts : seq (nat * nat)) :
  all (λ t : nat * nat, t.1 < st) ts -> (st, d') \notin ts.
Proof.
move=> /allP h; apply/negP => hin.
by have := h _ hin; rewrite /= ltnn.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Generic seq facts (missing from MathComp's seq.v) *)

(** [unzip1] distributes over [++] (it is a [map]). *)
Lemma unzip1_cat (X Y : Type) (s t : seq (X * Y)) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
Proof. exact: map_cat. Qed.

(** A sum of elements all below [n] is below [size * n]. *)
Lemma sumn_all_leq n (s : seq nat) :
  all (fun x => x <= n) s -> sumn s <= size s * n.
Proof.
elim: s => [//|a s IH] /= /andP[ha hs].
rewrite mulSn; exact: leq_add ha (IH hs).
Qed.

(** [ohead s = Some x] witnesses membership (the head is in the list). *)
Lemma ohead_mem {T : eqType} {s : seq T} {x : T} : ohead s = Some x -> x \in s.
Proof. by case: s => //= a s [<-]; rewrite in_cons eqxx. Qed.

(* ------------------------------------------------------------------ *)
(** ** Digit vectors

    A digit vector is a [seq nat].  From the chain value at depth [d]
    anyone can compute the values at every depth [d' >= d], so a forged
    digit vector is only useful at a coordinate where the forged digit
    is strictly below the honest one.  [eq_sumn_exists_lt] finds such a
    coordinate for two distinct vectors with the same digit sum: the
    fixed sum plays the role of the WOTS+ checksum. *)

(** Well-formed digit vectors: every digit below the radix. *)
Definition wf_digits (w : nat) (ds : seq nat) : bool := all (fun d => d < w) ds.

(** A strictly smaller sum forces a strictly smaller coordinate. *)
Lemma ltn_sumn_exists_lt {u v : seq nat} :
  size u = size v -> sumn u < sumn v ->
  exists2 k, k < size u & nth 0 u k < nth 0 v k.
Proof.
elim: u v => [|a u IH] [|b v] //= [sz] hlt.
case: (ltnP a b) => hab; first by exists 0.
have hlt' : sumn u < sumn v.
  rewrite -(ltn_add2l b); apply: leq_ltn_trans hlt.
  by rewrite leq_add2r.
have [k hk hd] := IH v sz hlt'.
by exists k.+1.
Qed.

(** Two distinct vectors of the same size and the same digit sum: [u]
    is strictly below [v] at some coordinate.  Consumed with
    [u := forged] and [v := honest]. *)
Lemma eq_sumn_exists_lt {u v : seq nat} :
  size u = size v -> sumn u = sumn v -> u <> v ->
  exists2 k, k < size u & nth 0 u k < nth 0 v k.
Proof.
elim: u v => [|a u IH] [|b v] //= [sz] hsum hne.
case: (ltngtP a b) => hab.
- by exists 0.
- have hlt : sumn u < sumn v by rewrite -(ltn_add2l b) -hsum ltn_add2r.
  have [k hk hd] := ltn_sumn_exists_lt sz hlt.
  by exists k.+1.
- have hsum' : sumn u = sumn v by move: hsum; rewrite hab => /addnI.
  have hne' : u <> v by move=> e; apply: hne; rewrite hab e.
  have [k hk hd] := IH v sz hsum' hne'.
  by exists k.+1.
Qed.


(* ================= merged Shrincs.internal.ssprove.lib.chain.* ================= *)

(** All the [F]-using content is one [Section] so the four former
    [Chain.*] layers share the step [F'] and the wrappers [Fc] /
    [chainc] / [chain_extractc] (which must be in scope across all
    four).  Section-variable generalisation still drops the variables a
    given definition does not use, so each public name keeps its
    natural parameter list. *)

Section ChainCore.

(** Public parameter and hash domain (one hash-output type [N]). *)
Context (PP N : choice_type).

(** Number of chains, digit bound (digits in [0..w-1]), target sum. *)
Context (l w tsum : nat).

(** Position-tweaked hash, at chain index and position. *)
Context (F' : PP -> nat -> nat -> N -> N).

(** Output distribution for the SM-UD signature-root sampler. *)
Context (dN : dist N).

(* ================================================================== *)
(** ** The chain step and the chain fold *)

(** The step: apply [F'] at position [p] when [p < w], else identity.
    The guard is a [Bool.bool_dec] sumbool, which [simpl] leaves alone
    on an abstract position, so a goal keeps the step folded. *)
Definition Fc (pp : PP) (t : nat * nat) (x : N) : N :=
  match Bool.bool_dec ((t.2)%N < w)%N true with
  | left _ => F' pp t.1 t.2 x
  | right _ => x
  end.

(** In range, [Fc] IS the hash. *)
Lemma FcE pp i p x (H : (p < w)%N) : Fc pp (i, p) x = F' pp i p x.
Proof.
rewrite /Fc /=; case: (Bool.bool_dec (p < w)%N true) => [//|H0].
by case: (H0 H).
Qed.

(** The fold: apply [Fc] at positions [s, ..., s + n - 1] from [x]. *)
Fixpoint chainc (pp : PP) (i : nat) (x : N) (s n : nat) {struct n} : N :=
  if n is n'.+1 then chainc pp i (Fc pp (i, s) x) s.+1 n' else x.

Lemma chainc_0 pp i x s : chainc pp i x s 0 = x.
Proof. by []. Qed.

(** Definitional front-peel (unconditional): the one-step peel the
    query/walk lemmas rely on. *)
Lemma chainc_shift pp i x k j :
  chainc pp i x k j.+1 = chainc pp i (Fc pp (i, k) x) k.+1 j.
Proof. by []. Qed.

(** The fold as a [foldl] over its positions. *)
Lemma chainc_foldl pp i x s n :
  chainc pp i x s n = foldl (fun y j => Fc pp (i, j) y) x (iota s n).
Proof. by elim: n x s => [|n IH] x s //=; rewrite IH. Qed.

(** Composition (UNCONDITIONAL — the fold is total). *)
Lemma chainc_cat pp i x s m n :
  chainc pp i x s (m + n) = chainc pp i (chainc pp i x s m) (s + m) n.
Proof.
elim: m s x => [|m IH] s x; first by rewrite add0n addn0.
by rewrite addSn /= IH addSnnS.
Qed.

(** Re-split at an intermediate position (UNCONDITIONAL). *)
Lemma chainc_split pp i y j i0 e :
  j <= i0 -> i0 <= e ->
  chainc pp i y j (e - j) = chainc pp i (chainc pp i y j (i0 - j)) i0 (e - i0).
Proof.
move=> hji hie.
have E : (e - j = (i0 - j) + (e - i0))%N.
  by rewrite addnBA // addnC addnBA // subnAC addnK.
by rewrite E chainc_cat subnKC.
Qed.

(** End-peel (UNCONDITIONAL). *)
Lemma chainc_rcons pp i x s n :
  chainc pp i x s n.+1 = Fc pp (i, (s + n)%N) (chainc pp i x s n).
Proof.
elim: n s x => [|n IH] s x; first by rewrite addn0.
rewrite (chainc_shift pp i x s n.+1) IH (chainc_shift pp i x s n).
by rewrite addSnnS.
Qed.

(** Outcome of comparing a forged chain against the honest chain. *)
Variant ccase : Type :=
  | ChainColl of nat & N & N
    (** [ChainColl k u v]: collision at step [k]: [u != v],
        [Fc (i, k) u = Fc (i, k) v], [u] the forged-side and [v] the
        honest-side value at position [k]. *)
  | ChainMeet
    (** The forged chain meets the honest chain exactly at the honest
        chain's start position. *).

(** Walk both chains forward from position [k] ([u] forged-side
    value, [v] honest-side value, [n] steps remaining) and report the
    FIRST step at which distinct inputs hash to equal outputs.  Once
    the values differ they keep differing until such a step, so under
    endpoint equality [ChainMeet] is only returned when [u == v] at the
    entry position. *)
Fixpoint chain_searchc (pp : PP) (i : nat) (u v : N) (k n : nat) {struct n} : ccase :=
  if n is n'.+1 then
    (if u == v then ChainMeet
     else if Fc pp (i, k) u == Fc pp (i, k) v then ChainColl k u v
     else chain_searchc pp i (Fc pp (i, k) u) (Fc pp (i, k) v) k.+1 n')
  else ChainMeet.

Lemma chain_searchcP pp i u v k n :
  chainc pp i u k n = chainc pp i v k n ->
  match chain_searchc pp i u v k n with
  | ChainColl k' u' v' =>
      [/\ k <= k' < k + n,
          u' = chainc pp i u k (k' - k),
          v' = chainc pp i v k (k' - k),
          u' != v'
        & Fc pp (i, k') u' = Fc pp (i, k') v']
  | ChainMeet => u = v
  end.
Proof.
elim: n u v k => [|n IH] u v k /= heq; first exact: heq.
case: (altP (u =P v)) => [//|hne].
case: (altP (Fc pp (i, k) u =P Fc pp (i, k) v)) => [hcol|hncol].
- by split; rewrite ?subnn ?leqnn ?addnS ?ltnS ?leq_addr.
- move: (IH _ _ k.+1 heq).
  case: (chain_searchc pp i (Fc pp (i, k) u) (Fc pp (i, k) v) k.+1 n) => [k' u' v'|]; last first.
    by move=> hfeq; rewrite hfeq eqxx in hncol.
  move=> [/andP[h1 h2] hu' hv' hne' hcol']; split=> //.
  + by rewrite (ltnW h1) -addSnnS h2.
  + by rewrite hu' -(subnSK h1).
  + by rewrite hv' -(subnSK h1).
Qed.

(** Forgery classifier: forged chain from [y] at position [j], honest
    chain from [z] at position [i'], both ending at position [e]. *)
Definition chain_extractc (pp : PP) (i : nat) (y : N) (j : nat) (z : N) (i' e : nat)
    : ccase :=
  chain_searchc pp i (chainc pp i y j (i' - j)) z i' (e - i').


(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

(** Message validity: [l] digits, all below [w], digit sum exactly
    [tsum] (the WOTS+C post-grinding message space). *)
Definition valid_msg (m : seq nat) : bool :=
  [&& size m == l, wf_digits w m & sumn m == tsum].

(** Public chain ends: the [i]-th component is the end (position
    [w.-1]) of the [i]-th chain started from the [i]-th secret. *)
Definition chain_ends (pp : PP) (xs : seq N) : seq N :=
  [seq chainc pp ix.1 ix.2 0 w.-1 | ix <- zip (iota 0 l) xs].

(** Signature digits: the [i]-th component is the [i]-th chain walked
    from the secret start to position [m_i]. *)
Definition sign_digits (pp : PP) (xs : seq N) (m : seq nat) : seq N :=
  [seq chainc pp ixd.1.1 ixd.1.2 0 ixd.2
  | ixd <- zip (zip (iota 0 l) xs) m].

(** One verification check: completing the [i]-th chain from the
    claimed value [y] at position [d] must reach the public end. *)
Definition chain_check (pp : PP) (i d : nat) (y e : N) : bool :=
  chainc pp i y d (w.-1 - d) == e.

Definition verify_sig (pp : PP) (ends : seq N) (m : seq nat) (sg : seq N) : bool :=
  [&& valid_msg m, size sg == l
    & all (fun q => chain_check pp q.1 q.2.1 q.2.2.1 q.2.2.2)
          (zip (iota 0 l) (zip m (zip sg ends)))].

(* ------------------------------------------------------------------ *)
(** ** Size sanity lemmas *)

Lemma size_chain_ends pp xs : size (chain_ends pp xs) = minn l (size xs).
Proof. by rewrite size_map size_zip size_iota. Qed.

Lemma size_chain_ends_l pp xs :
  size xs = l -> size (chain_ends pp xs) = l.
Proof. by move=> hxs; rewrite size_chain_ends hxs minnn. Qed.

Lemma size_sign_digits pp xs m :
  size (sign_digits pp xs m) = minn (minn l (size xs)) (size m).
Proof. by rewrite size_map !size_zip size_iota. Qed.

Lemma size_sign_digits_l pp xs m :
  size xs = l -> size m = l -> size (sign_digits pp xs m) = l.
Proof. by move=> hxs hm; rewrite size_sign_digits hxs hm !minnn. Qed.

(* ------------------------------------------------------------------ *)
(** ** Correctness *)

(** Pointwise core, generalized over the starting chain index [st] so
    that induction on the secrets goes through.  For each position:
    completing the honest signature value (chain from [x] to position
    [d]) with [w.-1 - d] more steps reaches the chain end; this is
    exactly [chainc_split] with [j := 0], [i := d], [e := w.-1]
    (where [d <= w.-1] because [d < w]). *)
Lemma all_chain_checks pp st (xs : seq N) (m : seq nat) :
  size m = size xs -> wf_digits w m ->
  all (fun q => chain_check pp q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st (size xs))
           (zip m
                (zip [seq chainc pp ixd.1.1 ixd.1.2 0 ixd.2
                     | ixd <- zip (zip (iota st (size xs)) xs) m]
                     [seq chainc pp ix.1 ix.2 0 w.-1
                     | ix <- zip (iota st (size xs)) xs]))).
Proof.
elim: xs st m => [|x xs IH] st [|d m] //= [hsz] /andP[hd hm].
apply/andP; split; last by apply: IH.
rewrite /chain_check; apply/eqP.
have hdw : (d <= w.-1)%N by rewrite -ltnS (ltn_predK hd).
have hsp := chainc_split pp st x 0 d w.-1 (leq0n d) hdw.
by rewrite !subn0 in hsp; rewrite -hsp.
Qed.

(** THE correctness lemma: honestly generated chain ends verify the
    honestly signed digits of any valid message. *)
Lemma verify_sign pp xs m :
  size xs = l -> valid_msg m ->
  verify_sig pp (chain_ends pp xs) m (sign_digits pp xs m) = true.
Proof.
move=> hxs hvm.
have /and3P[/eqP hm hw _] := hvm.
rewrite /verify_sig hvm /=.
apply/andP; split; first by rewrite size_sign_digits_l.
rewrite /chain_ends /sign_digits -hxs.
by apply: all_chain_checks; rewrite ?hm ?hxs.
Qed.


Fixpoint sample_sig_roots (pp : PP) (i : nat) (m : seq nat) :
    raw_code (chList N) :=
  match m with
  | [::] => ret [::]
  | d :: m' =>
      u ← dN ;;
      sg ← sample_sig_roots pp i.+1 m' ;;
      ret ((if d is d'.+1 then Fc pp (i, d') u else u) :: sg)
  end.

#[export] Instance sample_sig_roots_valid
  (L : Locations) (I : Interface) pp i m :
  ValidCode L I (sample_sig_roots pp i m).
Proof.
elim: m i => [|d m IH] i /=.
- apply valid_ret.
- eapply valid_bind.
  + eapply valid_scheme, prog_valid.
  + move=> u; eapply valid_bind; [exact: IH | move=> sg; apply valid_ret].
Qed.

(** Public chain ends, re-rooted at the signature digits: the [i]-th
    end completes the [i]-th chain from value [σ_i] at position
    [m_i]. *)
Definition ends_from_sig (pp : PP) (m : seq nat) (sg : seq N) : seq N :=
  [seq chainc pp q.1 q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota 0 l) (zip m sg)].


(* ------------------------------------------------------------------ *)
(** *** Digit-vector selectors *)

(** Every digit of a valid message is below [w] (gives the [d < w] side
    condition of [forgery_cases]). *)
Lemma valid_msg_digit (m : seq nat) i :
  valid_msg m -> i < l -> nth 0 m i < w.
Proof.
case/and3P=> /eqP hm hw _ hi.
have /(all_nthP 0) hnth := hw.
by have := hnth i; rewrite hm => /(_ hi).
Qed.

(** THE message-level selector (wrap of [eq_sumn_exists_lt],
    the fixed digit sum playing the role of the WOTS+ checksum): two
    distinct valid messages give a chain index where the FORGED digit is
    strictly below the signed one — the only place a forger cannot walk
    forward from revealed values.  Consumed with [m] the signed and
    [mstar] the forged message. *)
Lemma forged_digit_lt (m mstar : seq nat) :
  valid_msg m -> valid_msg mstar -> mstar != m ->
  exists2 i, i < l & nth 0 mstar i < nth 0 m i.
Proof.
case/and3P=> /eqP hm _ /eqP hs.
case/and3P=> /eqP hm' _ /eqP hs' hne.
have hsz : size mstar = size m by rewrite hm hm'.
have hsum : sumn mstar = sumn m by rewrite hs hs'.
have hneq : mstar <> m by apply/eqP.
have [i hi hlt] := eq_sumn_exists_lt hsz hsum hneq.
by exists i => //; rewrite -hm'.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain forgery classifier *)

(** THE classifier ([chain_searchcP] at the forged chain walked up to
    the honest position): on the selected chain [i], the signer
    revealed [sigi] at position
    [d] and published [end_i = chainc sigi d (w.-1 - d)]; the forger
    claims [sigstar] at the strictly smaller position [dstar] and
    verification forces the same endpoint.  Then
    [chain_extractc pp i sigstar dstar sigi d w.-1] returns
    - [ChainColl k u v] with [d <= k < w.-1]: [v] is the HONEST chain
      value at position [k], recomputable from [sigi] — exactly the
      input of the TCR target the reduction committed at tweak [(i, k)]
      — and [u != v] with [Fc pp (i,k) u = Fc pp (i,k) v]:
      [u] at that target's index wins SM-TCR's CHECK;
    - [ChainMeet]: the forged chain reaches [sigi] at position [d]
      (note [0 < d] since [dstar < d]); [forgery_pre_preimage] below
      extracts the SM-PRE witness.
    (What [u] is in terms of [sigstar] is dropped: the reduction
    submits [u] itself.) *)
Lemma forgery_cases pp i d (sigi : N) dstar (sigstar : N) :
  dstar < d -> d < w ->
  chainc pp i sigstar dstar (w.-1 - dstar)
    = chainc pp i sigi d (w.-1 - d) ->
  match chain_extractc pp i sigstar dstar sigi d w.-1 with
  | ChainColl k u v =>
      [/\ d <= k < w.-1,
          v = chainc pp i sigi d (k - d),
          u != v
        & Fc pp (i, k) u = Fc pp (i, k) v]
  | ChainMeet => chainc pp i sigstar dstar (d - dstar) = sigi
  end.
Proof.
move=> hdd hdw heq.
have hji : (dstar <= d)%N := ltnW hdd.
have hie : (d <= w.-1)%N by rewrite -ltnS (ltn_predK hdw).
have hinner : chainc pp i (chainc pp i sigstar dstar (d - dstar)) d (w.-1 - d)
              = chainc pp i sigi d (w.-1 - d).
  by rewrite -(chainc_split pp i sigstar dstar d w.-1 hji hie).
rewrite /chain_extractc.
move: (chain_searchcP pp i _ _ d (w.-1 - d) hinner).
case: (chain_searchc pp i _ sigi d (w.-1 - d)) => [k u v|] //.
move=> [hk _ hv hne hcol]; split=> //.
by move: hk; rewrite (subnKC hie).
Qed.

(** PRE-case post-processing: if the forged chain meets [sigi] at
    position [d] then its value ONE step earlier (recomputable by the
    reduction from the forged signature) is an [Fc]-preimage of [sigi] at
    tweak [(i, d.-1)].  Post-UD, [sigi = Fc pp (i, d.-1) u_i] with [u_i]
    hidden uniform — i.e. [sigi] is literally the SM-PRE oracle's answer
    at tweak [(i, d.-1)], so this is the message that wins PCHECK. *)
Lemma forgery_pre_preimage pp i d (sigi sigstar : N) dstar :
  dstar < d ->
  chainc pp i sigstar dstar (d - dstar) = sigi ->
  Fc pp (i, d.-1) (chainc pp i sigstar dstar (d.-1 - dstar)) = sigi.
Proof.
move=> hdd hmeet.
have hd1 : dstar <= d.-1 by rewrite -ltnS (ltn_predK hdd).
have hn : d - dstar = (d.-1 - dstar).+1.
  by rewrite -subSn // (ltn_predK hdd).
by move: hmeet; rewrite hn chainc_rcons subnKC.
Qed.

(* ------------------------------------------------------------------ *)
(** *** nth-form access to the verification equation *)

(** A passing verification forces, at every chain [i < l], the forged
    completion to hit the public end. *)
Lemma verify_sig_nth pp (ends : seq N) (m : seq nat) (sg : seq N)
    (y0 : N) i :
  verify_sig pp ends m sg ->
  size ends = l -> i < l ->
  chainc pp i (nth y0 sg i) (nth 0 m i) (w.-1 - nth 0 m i)
  = nth y0 ends i.
Proof.
case/and3P=> /and3P[/eqP hm _ _] /eqP hsg hall hends hi.
have hzs : size (zip (iota 0 l) (zip m (zip sg ends))) = l.
  by rewrite !size_zip size_iota hm hsg hends !minnn.
move/(all_nthP (0, (0, (y0, y0)))): hall => /(_ i).
rewrite hzs => /(_ hi).
rewrite nth_zip ?size_iota ?size_zip ?hm ?hsg ?hends ?minnn //.
rewrite nth_zip ?size_zip ?hm ?hsg ?hends ?minnn //.
rewrite nth_zip ?hsg ?hends //=.
by rewrite /chain_check nth_iota // add0n => /eqP.
Qed.

(** Size of an [ends_from_sig] public key. *)
Lemma size_ends_from_sig pp (m : seq nat) (sg : seq N) :
  size m = l -> size sg = l ->
  size (ends_from_sig pp m sg) = l.
Proof.
move=> hm hsg.
by rewrite /ends_from_sig size_map !size_zip size_iota hm hsg !minnn.
Qed.

(** The [i]-th [ends_from_sig] end in chain form. *)
Lemma ends_from_sig_nth pp (m : seq nat) (sg : seq N) (y0 : N) i :
  size m = l -> size sg = l -> i < l ->
  nth y0 (ends_from_sig pp m sg) i
  = chainc pp i (nth y0 sg i) (nth 0 m i) (w.-1 - nth 0 m i).
Proof.
move=> hm hsg hi.
rewrite /ends_from_sig (nth_map (0, (0, y0))) ?size_zip ?size_iota
        ?hm ?hsg ?minnn //.
rewrite nth_zip ?size_iota ?size_zip ?hm ?hsg ?minnn //.
rewrite nth_zip ?hm ?hsg //=.
by rewrite nth_iota // add0n.
Qed.


(* ================================================================== *)
(** ** TCR decision and committed-query bookkeeping *)

(* ------------------------------------------------------------------ *)
(** *** Pure layer: committed queries, signatures, ends, indices *)

(** The committed (tweak, input) pairs live in the carrier of SM-TCR's
    target entry type. *)
Local Abbreviation qentry := ((nat * nat) * N)%type.

(** Signature digit of chain [i] with digit [d] from root [u]. *)
Definition sig_of_root (pp : PP) (i d : nat) (u : N) : N :=
  if d is d'.+1 then Fc pp (i, d') u else u.

(** Queries of the upward walk of chain [i]: positions [k .. k+n-1],
    inputs the successive chain values from [x] at [k]. *)
Definition walkq (pp : PP) (i k n : nat) (x : N) : seq qentry :=
  [seq ((i, (j + k)%N), chainc pp i x k j) | j <- iota 0 n].

Lemma size_walkq pp i k n x : size (walkq pp i k n x) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma walkq_cons pp i k n x :
  walkq pp i k n.+1 x
  = ((i, k), x) :: walkq pp i k.+1 n (Fc pp (i, k) x).
Proof.
rewrite /walkq /=; congr (_ :: _).
rewrite -[1]/(1 + 0)%N iotaDl -map_comp.
apply: eq_map => j /=.
by rewrite add1n addSnnS.
Qed.

Lemma walkq_tweak1 pp i k n x :
  all (λ t : nat * nat, (t.1 == i)%B) (unzip1 (walkq pp i k n x)).
Proof.
rewrite /walkq /unzip1 -map_comp all_map.
by apply/allP => j _ /=.
Qed.

(** Every walk tweak has position [< k + n]. *)
Lemma walkq_tweak2 pp i k n x b :
  (k + n <= b)%N ->
  all (λ t : nat * nat, (t.2 < b)%N) (unzip1 (walkq pp i k n x)).
Proof.
move=> hb; rewrite /walkq /unzip1 -map_comp all_map.
apply/allP => j; rewrite mem_iota add0n => /andP[_ hj] /=.
by rewrite addnC; apply: leq_trans hb; rewrite ltn_add2l.
Qed.

(** All queries of one chain: the sigma query (for positive digits)
    followed by the walk from the signature position. *)
Definition chain_queries (pp : PP) (i d : nat) (u : N) : seq qentry :=
  (if d is d'.+1 then [:: ((i, d'), u)] else [::])
  ++ walkq pp i d (w.-1 - d) (sig_of_root pp i d u).

(** Number of queries of one chain / of a digit list. *)
Definition chain_query_count (d : nat) : nat := (0 < d) + (w.-1 - d).
Definition total_query_count (ds : seq nat) : nat := sumn [seq chain_query_count d | d <- ds].

Lemma size_chain_queries pp i d u : size (chain_queries pp i d u) = chain_query_count d.
Proof. by rewrite size_cat size_walkq /chain_query_count; case: d. Qed.

Lemma chain_queries_tweaks pp i d u :
  all (λ t : nat * nat, (t.1 == i)%B) (unzip1 (chain_queries pp i d u)).
Proof.
rewrite /chain_queries unzip1_cat all_cat walkq_tweak1 andbT.
by case: d => //= d; rewrite eqxx.
Qed.

(** Full committed list, chains [st, st+1, ...] with digits [ds] and
    roots [us]. *)
Definition commit_queries (pp : PP) (st : nat) (ds : seq nat) (us : seq N) :
    seq qentry :=
  flatten [seq chain_queries pp q.1 q.2.1 q.2.2
          | q <- zip (iota st (size ds)) (zip ds us)].

Lemma commit_queries_cons pp st d ds u us :
  commit_queries pp st (d :: ds) (u :: us)
  = chain_queries pp st d u ++ commit_queries pp st.+1 ds us.
Proof. by []. Qed.

(** Budget cap: [total_query_count] of any [l]-digit message fits in [tcr_budget]. *)
Lemma nqs_le (ds : seq nat) : size ds = l -> total_query_count ds <= tcr_budget l w.
Proof.
move=> hsz.
have hall : all (λ x, x <= w.+1) [seq chain_query_count d | d <- ds].
  apply/allP => x /mapP[d _ ->]; rewrite /chain_query_count.
  apply: (@leq_trans (1 + w.-1)%N).
  - by apply: leq_add; [case: (0 < d) | exact: leq_subr].
  - by rewrite add1n ltnS leq_pred.
have := sumn_all_leq _ _ hall.
by rewrite size_map hsz /tcr_budget mulnSr addnC.
Qed.

(** Signature digits and public ends, generalized over the start chain. *)
Definition sigs_of (pp : PP) (st : nat) (ds : seq nat) (us : seq N) : seq N :=
  [seq sig_of_root pp q.1 q.2.1 q.2.2 | q <- zip (iota st (size ds)) (zip ds us)].

Lemma size_sigs_of pp st ds us :
  size us = size ds -> size (sigs_of pp st ds us) = size ds.
Proof. by move=> h; rewrite size_map !size_zip size_iota h !minnn. Qed.

Lemma qnth_sigs_of pp st ds us i ui :
  size us = size ds -> i < size ds -> qnth us i = Some ui ->
  qnth (sigs_of pp st ds us) i
  = Some (sig_of_root pp (st + i)%N (nth 0 ds i) ui).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu.
- by case: hu => <-; rewrite addn0.
- by rewrite -addSnnS; apply: IH.
Qed.

Definition ends_of (pp : PP) (st : nat) (ds : seq nat) (sgs : seq N) : seq N :=
  [seq chainc pp q.1 q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota st (size ds)) (zip ds sgs)].

Lemma ends_of_from_sig pp (m : seq nat) (sgs : seq N) :
  size m = l ->
  ends_of pp 0 m sgs = ends_from_sig pp m sgs.
Proof. by move=> hm; rewrite /ends_of /ends_from_sig hm. Qed.

(** CHECK index of the walk target [(i, k)] in the committed order. *)
Definition q_index (ds : seq nat) (i k : nat) : nat :=
  total_query_count (take i ds) + ((0 < nth 0 ds i) + (k - nth 0 ds i)).

(** Position of [(i,k)] inside one chain's queries. *)
Lemma qnth_chain_queries pp i d u k :
  d <= k < w.-1 ->
  qnth (chain_queries pp i d u) ((0 < d) + (k - d))
  = Some ((i, k), chainc pp i (sig_of_root pp i d u) d (k - d)).
Proof.
move=> /andP[hdk hkw].
have hdw : d < w.-1 := leq_ltn_trans hdk hkw.
have hlt : k - d < w.-1 - d := ltn_sub2r hdw hkw.
have hw : qnth (walkq pp i d (w.-1 - d) (sig_of_root pp i d u)) (k - d)
          = Some ((i, k), chainc pp i (sig_of_root pp i d u) d (k - d)).
  rewrite /qnth /walkq -map_drop (drop_nth 0) ?size_iota //=.
  by rewrite nth_iota // add0n subnK.
by case: d hdk hdw hlt hw => [|d'] hdk hdw hlt hw; rewrite /chain_queries //=.
Qed.

(** THE bookkeeping lemma. *)
Lemma qnth_commit_queries pp st ds us i k ui :
  size us = size ds -> i < size ds -> qnth us i = Some ui ->
  nth 0 ds i <= k < w.-1 ->
  qnth (commit_queries pp st ds us) (q_index ds i k)
  = Some (((st + i)%N, k),
          chainc pp (st + i)%N (sig_of_root pp (st + i)%N (nth 0 ds i) ui)
                (nth 0 ds i) (k - nth 0 ds i)%N).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu hk.
- case: hu => <-; rewrite addn0 /q_index /= add0n.
  rewrite qnth_cat_l ?size_chain_queries.
    rewrite /chain_query_count ltn_add2l; apply: ltn_sub2r; last by case/andP: hk.
    by apply: leq_ltn_trans (proj1 (andP hk)) (proj2 (andP hk)).
  exact: qnth_chain_queries.
- rewrite /q_index /= -addnA.
  rewrite -(size_chain_queries pp st d u) qnth_cat_r.
  by rewrite -addSnnS; apply: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The forgery classifier, as a computable decision *)

Definition tcr_decision (pp : PP) (m mstar : seq nat) (sgs sgstar : seq N) :
    option (nat * N) :=
  match ohead [seq i <- iota 0 l | nth 0 mstar i < nth 0 m i] with
  | Some i =>
      match qnth sgs i, qnth sgstar i with
      | Some si, Some si' =>
          match chain_extractc pp i si' (nth 0 mstar i) si (nth 0 m i) w.-1 with
          | ChainColl k u _ => Some (q_index m i k, u)
          | ChainMeet => None
          end
      | _, _ => None
      end
  | None => None
  end.

(** Specification: on a verifying fresh forgery against the
    [ends_from_sig] key, a [Some (j, u)] decision points at a committed
    pair [(t, v)] with [u != v] and [Fc pp t u = Fc pp t v]. *)
Lemma tcr_decisionP (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg m -> size us = l ->
  verify_sig pp
    (ends_of pp 0 m (sigs_of pp 0 m us)) mstar sgstar ->
  mstar \notin [:: m] ->
  match tcr_decision pp m mstar (sigs_of pp 0 m us) sgstar with
  | Some (j, u) =>
      exists t v,
        [/\ qnth (commit_queries pp 0 m us) j = Some (t, v),
            u != v & Fc pp t u = Fc pp t v]
  | None => True
  end.
Proof.
move=> hvm hus hver hnin.
have hm : size m = l by case/and3P: hvm => /eqP.
have hussz : size us = size m by rewrite hus hm.
have hsgs : size (sigs_of pp 0 m us) = l by rewrite size_sigs_of // hm.
rewrite (ends_of_from_sig pp m _ hm) in hver.
rewrite /tcr_decision.
case E1: (ohead _) => [i|]; last by [].
move: (ohead_mem E1); rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
case E2: (qnth (sigs_of pp 0 m us) i) => [si|]; last by [].
case E3: (qnth sgstar i) => [si'|]; last by [].
have hdw : (nth 0 m i < w)%N := valid_msg_digit _ _ hvm hil.
have hends := size_ends_from_sig pp m _ hm hsgs.
have h1 := verify_sig_nth pp _ mstar sgstar si' i hver hends hil.
rewrite (ends_from_sig_nth pp m _ si' i hm hsgs hil) in h1.
rewrite (qnth_nth si' _ _ _ E3) (qnth_nth si' _ _ _ E2) in h1.
have := forgery_cases pp i (nth 0 m i) si (nth 0 mstar i) si' hlt hdw h1.
case E4: (chain_extractc pp i si' (nth 0 mstar i) si (nth 0 m i) w.-1) => [k u v|];
  last by [].
move=> [hk hv hne hcol].
have hilm : (i < size m)%N by rewrite hm.
have [ui hui] : exists ui, qnth us i = Some ui.
  by apply: qnth_some; rewrite hus.
have hsig : sig_of_root pp i (nth 0 m i) ui = si.
  have h2 := qnth_sigs_of pp 0 m us i ui hussz hilm hui.
  rewrite add0n E2 in h2.
  by case: h2 => ->.
exists (i, k), v; split.
- have h2 := qnth_commit_queries pp 0 m us i k ui hussz hilm hui hk.
  by rewrite add0n hsig -hv in h2.
- exact: hne.
- exact: hcol.
Qed.


(* ================================================================== *)
(** ** PRE decision and committed-query bookkeeping *)

(** Queries of one chain: one PQUERY at [(i, d-1)] for positive digits,
    none for digit 0.  The stored entry is the HIDDEN input [u]. *)
Definition pre_query (i d : nat) (u : N) : seq qentry :=
  if d is d'.+1 then [:: ((i, d'), u)] else [::].

(** Full committed list, chains [st, st+1, ...] with digits [ds] and
    hidden inputs [us]. *)
Definition pre_queries (st : nat) (ds : seq nat) (us : seq N) :
    seq qentry :=
  flatten [seq pre_query q.1 q.2.1 q.2.2
          | q <- zip (iota st (size ds)) (zip ds us)].

Lemma pre_queries_cons st d ds u us :
  pre_queries st (d :: ds) (u :: us)
  = pre_query st d u ++ pre_queries st.+1 ds us.
Proof. by []. Qed.

(** Number of PQUERYs of a digit list / budget cap. *)
Definition preimage_query_count (ds : seq nat) : nat := count (λ d, 0 < d) ds.

Lemma npq_le (ds : seq nat) : size ds = l -> preimage_query_count ds <= l.
Proof. by move=> h; rewrite -h; exact: count_size. Qed.

(** CHECK index of chain [i]'s PQUERY. *)
Definition pre_index (ds : seq nat) (i : nat) : nat :=
  preimage_query_count (take i ds).

(** THE bookkeeping lemma. *)
Lemma qnth_pre_queries st ds us i ui :
  size us = size ds -> i < size ds -> qnth us i = Some ui ->
  0 < nth 0 ds i ->
  qnth (pre_queries st ds us) (pre_index ds i)
  = Some (((st + i)%N, (nth 0 ds i).-1), ui).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu hd.
- case: hu => <-; rewrite addn0 /pre_index /preimage_query_count take0 /=.
  by case: d hd => [|d'].
- have -> : pre_index (d :: ds) i.+1 = ((0 < d) + pre_index ds i)%N.
    by rewrite /pre_index /preimage_query_count.
  rewrite pre_queries_cons -addSnnS.
  case: d hd => [|d'] hd /=.
  + by rewrite add0n; apply: IH.
  + by rewrite add1n qnth_cons; apply: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The PRE classifier (computable counterpart of the ChainMeet
    case; complement of [tcr_decision]) *)

Definition pre_decision (pp : PP) (m mstar : seq nat)
    (sgs sgstar : seq N) : option (nat * N) :=
  match ohead [seq i <- iota 0 l | nth 0 mstar i < nth 0 m i] with
  | Some i =>
      match qnth sgs i, qnth sgstar i with
      | Some si, Some si' =>
          match chain_extractc pp i si' (nth 0 mstar i) si
                  (nth 0 m i) w.-1 with
          | ChainColl _ _ _ => None
          | ChainMeet =>
              Some (pre_index m i,
                    chainc pp i si' (nth 0 mstar i)
                          ((nth 0 m i).-1 - nth 0 mstar i))
          end
      | _, _ => None
      end
  | None => None
  end.

(** Specification of the [Some] case: the submitted message is an
    [Fc]-preimage of the stored target's image. *)
Lemma pre_decisionP (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg m -> size us = l ->
  verify_sig pp
    (ends_from_sig pp m (sigs_of pp 0 m us))
    mstar sgstar ->
  mstar \notin [:: m] ->
  match pre_decision pp m mstar (sigs_of pp 0 m us) sgstar with
  | Some (j, x) =>
      exists t u,
        [/\ qnth (pre_queries 0 m us) j = Some (t, u)
          & Fc pp t x = Fc pp t u]
  | None => True
  end.
Proof.
move=> hvm hus hver hnin.
have hm : size m = l by case/and3P: hvm => /eqP.
have hussz : size us = size m by rewrite hus hm.
have hsgs : size (sigs_of pp 0 m us) = l.
  by rewrite size_sigs_of // hm.
rewrite /pre_decision.
case E1: (ohead _) => [i|]; last by [].
move: (ohead_mem E1); rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
case E2: (qnth (sigs_of pp 0 m us) i) => [si|]; last by [].
case E3: (qnth sgstar i) => [si'|]; last by [].
case E4: (chain_extractc pp i si' (nth 0 mstar i) si (nth 0 m i) w.-1) => [k u v|];
  first by [].
have hdw : (nth 0 m i < w)%N := valid_msg_digit _ _ hvm hil.
have hends := size_ends_from_sig pp m _ hm hsgs.
have h1 := verify_sig_nth pp _ mstar sgstar si' i hver hends hil.
rewrite (ends_from_sig_nth pp m _ si' i hm hsgs hil) in h1.
rewrite (qnth_nth si' _ _ _ E3) (qnth_nth si' _ _ _ E2) in h1.
have := forgery_cases pp i (nth 0 m i) si (nth 0 mstar i) si' hlt hdw h1.
rewrite E4 => hmeet.
have hpim := forgery_pre_preimage pp i (nth 0 m i) si si'
               (nth 0 mstar i) hlt hmeet.
have hilm : (i < size m)%N by rewrite hm.
have [ui hui] : exists ui, qnth us i = Some ui.
  by apply: qnth_some; rewrite hus.
have hsig0 := qnth_sigs_of pp 0 m us i ui hussz hilm hui.
rewrite add0n E2 in hsig0.
case: hsig0 => hsig.
have hd0 : 0 < nth 0 m i := leq_ltn_trans (leq0n _) hlt.
have hsr : sig_of_root pp i (nth 0 m i) ui
           = Fc pp (i, (nth 0 m i).-1) ui.
  by case: (nth 0 m i) hd0.
exists ((i, (nth 0 m i).-1)), ui; split.
- by rewrite (qnth_pre_queries 0 m us i ui hussz hilm hui hd0).
- by rewrite hpim hsig hsr.
Qed.

(** Classifier completeness: on a verifying fresh forgery the
    degenerate branches cannot occur — if [tcr_decision] declined,
    [pre_decision] fires. *)
Lemma classify_some (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg m -> size us = l ->
  verify_sig pp
    (ends_from_sig pp m (sigs_of pp 0 m us))
    mstar sgstar ->
  mstar \notin [:: m] ->
  tcr_decision pp m mstar (sigs_of pp 0 m us) sgstar = None ->
  pre_decision pp m mstar (sigs_of pp 0 m us) sgstar != None.
Proof.
move=> hvm hus hver hnin.
have hm : size m = l by case/and3P: hvm => /eqP.
have hsgs : size (sigs_of pp 0 m us) = l.
  by rewrite size_sigs_of // hus hm.
have hvm' : valid_msg mstar by case/and3P: hver.
have hne : mstar != m by move: hnin; rewrite in_cons negb_or => /andP[].
have [i0 hi0 hlt0] := forged_digit_lt m mstar hvm hvm' hne.
have hhas : has (fun i => nth 0 mstar i < nth 0 m i) (iota 0 l).
  by apply/hasP; exists i0; rewrite ?mem_iota //=.
rewrite /tcr_decision /pre_decision.
case E1: (ohead _) => [i|]; last first.
  move: E1; case Ef: (filter _ _) => [|a s] //= _.
  by move: hhas; rewrite has_filter Ef eqxx.
move: (ohead_mem E1); rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
have [si E2] : exists si, qnth (sigs_of pp 0 m us) i = Some si.
  by apply: qnth_some; rewrite hsgs.
have hsgst : size sgstar = l.
  by case/and3P: hver => _ /eqP.
have [si' E3] : exists si', qnth sgstar i = Some si'.
  by apply: qnth_some; rewrite hsgst.
rewrite E2 E3.
by case: (chain_extractc pp i si' (nth 0 mstar i) si (nth 0 m i) w.-1).
Qed.

End ChainCore.
