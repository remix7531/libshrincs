(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.chain.core

    The generic Winternitz-style chain-signature layer, generic over a
    tweakable hash [F].  This file is the MERGE of the former
    Sec.lib.chain.{Scheme, Sample, Forgery, Decision} — kept as one
    compilation unit (four [Section]s below) so the genuinely-serial
    content chain pays the SSProve load floor ONCE instead of four
    times.  The file opens with the generic seq/fmap/tweak helpers
    merged in from the former [Sec.lib.toolkit.QSeq] ([qnth], [qmap_from],
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

    THE CHAIN LADDER.  The fold, the forged/honest walk and the forgery
    classifier are [Sec.lib.math.chain]'s [chain] / [chain_search] /
    [chain_extract], applied at the step [chainf pp i] of chain [i].
    That is the ONE generic ladder in this repo: both the native
    single-anchor WOTS+C proof ([Sec.wots.*]) and the banked FXMSS leaf
    bound ([SHRINCS.fxmss.leaf2_*]) instantiate it.

    (Before the exact-or-zero address facade landed, this layer's own
    step carried a dependent type and had to be wrapped in a
    position-guarding total step [Fc] with a bridge [FcE]; every
    concrete step now ignores the bound proof, so the guard had no
    content left and both are gone.  A separate width-bounded model
    chain and its bridge [chaincE] existed for the same reason and are
    likewise gone -- nothing consumed either.)

    See each section's header comment for details. *)

From Model Require Import math.encoding.
From Sec.lib Require Import prelude sig.scheme
  toolkit.sample_seq math.chain.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ===== merged Sec.lib.toolkit.QSeq (generic seq/fmap/tweak helpers) ===== *)


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
rewrite IH setmC; last by apply/negbT/gtn_eqF; rewrite addSn ltnS leq_addr.
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

(** Widen a per-chain bound to the next chain index. *)
Lemma all_tlt_lt i k (ts : seq (nat * nat)) :
  all (tweak_lt i k) ts -> all (λ t : nat * nat, t.1 < i.+1) ts.
Proof.
apply: sub_all => t; rewrite /tweak_lt => /orP[h|/andP[/eqP -> _]] //.
exact: ltnW.
Qed.

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


(* ================= merged Sec.lib.chain.* ================= *)

(** All the [F]-using content is one [Section] so the four former
    [Chain.*] layers share the step [F] and its per-chain currying
    [chainf] (which must be in scope across all four).  The context is
    declared in the order [PP N; F; dPP dN; l w tsum]; section-variable
    generalisation drops the variables a given definition does not use,
    so each public name keeps its natural parameter list. *)

Section ChainCore.

(** Public parameter and hash domain (one hash-output type [N]). *)
Context (PP N : choice_type).

(** Position-tweaked hash; the tweak is (chain index, chain position). *)
Context (F : PP -> nat * nat -> N -> N).

(** Samplers for key generation and for the SM-UD root sampler. *)
Context (dPP : dist PP) (dN : dist N).

(** Number of chains, digit bound (digits in [0..w-1]), target sum. *)
Context (l w tsum : nat).

(** Chain step of chain [i], in [Sec.lib.math.chain]'s position-first
    shape: the position is the step function's first argument. *)
Definition chainf (pp : PP) (i : nat) : nat -> N -> N :=
  fun pos x => F pp (i, pos) x.

(* ================= former Sec.lib.chain.scheme ================= *)

(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

(** Message validity: [l] digits, all below [w], digit sum exactly
    [tsum] (the WOTS+C post-grinding message space). *)
Definition valid_msg (m : seq nat) : bool :=
  [&& size m == l, wf_digits w m & sumn m == tsum].

(** Public chain ends: the [i]-th component is the end (position
    [w.-1]) of the [i]-th chain started from the [i]-th secret. *)
Definition chain_ends (pp : PP) (xs : seq N) : seq N :=
  [seq chain (chainf pp ix.1) ix.2 0 w.-1 | ix <- zip (iota 0 l) xs].

(** Signature digits: the [i]-th component is the [i]-th chain walked
    from the secret start to position [m_i]. *)
Definition sign_digits (pp : PP) (xs : seq N) (m : seq nat) : seq N :=
  [seq chain (chainf pp ixd.1.1) ixd.1.2 0 ixd.2
  | ixd <- zip (zip (iota 0 l) xs) m].

(** One verification check: completing the [i]-th chain from the
    claimed value [y] at position [d] must reach the public end. *)
Definition chain_check (pp : PP) (i d : nat) (y e : N) : bool :=
  chain (chainf pp i) y d (w.-1 - d) == e.

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
    exactly [chain_split] with [j := 0], [i := d], [e := w.-1]
    (where [d <= w.-1] because [d < w]). *)
Lemma all_chain_checks pp st (xs : seq N) (m : seq nat) :
  size m = size xs -> wf_digits w m ->
  all (fun q => chain_check pp q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st (size xs))
           (zip m
                (zip [seq chain (chainf pp ixd.1.1) ixd.1.2 0 ixd.2
                     | ixd <- zip (zip (iota st (size xs)) xs) m]
                     [seq chain (chainf pp ix.1) ix.2 0 w.-1
                     | ix <- zip (iota st (size xs)) xs]))).
Proof.
elim: xs st m => [|x xs IH] st [|d m] //= [hsz] /andP[hd hm].
apply/andP; split; last by apply: IH.
rewrite /chain_check; apply/eqP.
have hdw : (d <= w.-1)%N by rewrite -ltnS (ltn_predK hd).
have hsp := chain_split (chainf pp st) x (leq0n d) hdw.
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

(* ------------------------------------------------------------------ *)
(** ** The scheme as a [sig_scheme]

    The generic checksum-free fixed-sum Winternitz one-time signature:
    WOTS+C minus grinding and minus concrete addressing, with the fixed
    digit sum playing the role of the WOTS+ checksum.  [sign] returns
    the key unchanged (the EU-CMA one-time statement uses signing budget
    [q_s = 1]) and refuses ([None]) on messages outside the fixed-sum
    space.  The public parameter is sampled by [keygen] and carried in
    both keys (no separate parameter phase: PKseed is part of the public
    key). *)

Definition fixed_sum_scheme : sig_scheme := {|
  Pk := PP × 'list N ;
  Sk := PP × 'list N ;
  Msg := 'list ('nat) ;
  Sig := 'list N ;
  SParam := 'unit ;
  keygen := fun _ => {code
    pp ← dPP ;;
    xs ← sample_seq dN l ;;
    ret ((pp, xs), (pp, chain_ends pp xs)) } ;
  sign := fun sk m => {code
    if valid_msg m
    then ret (Some (sign_digits sk.1 sk.2 m, sk))
    else ret None } ;
  verify := fun pk m sg => verify_sig pk.1 pk.2 m sg
|}.

(* ================= former Sec.lib.chain.Sample ================= *)

Fixpoint sample_sig_roots (pp : PP) (i : nat) (m : seq nat) :
    raw_code (chList N) :=
  match m with
  | [::] => ret [::]
  | d :: m' =>
      u ← dN ;;
      sg ← sample_sig_roots pp i.+1 m' ;;
      ret ((if d is d'.+1 then F pp (i, d') u else u) :: sg)
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
  [seq chain (chainf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota 0 l) (zip m sg)].

(* ================= former Sec.lib.chain.Forgery ================= *)

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

(** THE message-level selector (wrap of [encoding.eq_sumn_exists_lt],
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

(** THE classifier (restatement of [chain.chain_extractP] with
    [y := sigstar], [j := dstar], [z := sigi], [i := d], [e := w.-1]):
    on the selected chain [i], the signer revealed [sigi] at position
    [d] and published [end_i = chain (chainf pp i) sigi d (w.-1 - d)];
    the forger
    claims [sigstar] at the strictly smaller position [dstar] and
    verification forces the same endpoint.  Then
    [chain_extract (chainf pp i) sigstar dstar sigi d w.-1] returns
    - [ChainColl k u v] with [d <= k < w.-1]: [v] is the HONEST chain
      value at position [k], recomputable from [sigi] — exactly the
      input of the TCR target the reduction committed at tweak [(i, k)]
      — and [u != v] with [F pp (i,k) u = F pp (i,k) v]:
      [(tcr_index m i k, u)] wins SM-TCR's CHECK;
    - [ChainMeet]: the forged chain reaches [sigi] at position [d]
      (note [0 < d] since [dstar < d]); [forgery_pre_preimage] below
      extracts the SM-PRE witness.
    ([chain_extract_ok]'s [u]-component [u = chain (chainf pp i) sigstar
    dstar (k - dstar)] is dropped: the reduction submits [u] itself.) *)
Lemma forgery_cases pp i d (sigi : N) dstar (sigstar : N) :
  dstar < d -> d < w ->
  chain (chainf pp i) sigstar dstar (w.-1 - dstar)
    = chain (chainf pp i) sigi d (w.-1 - d) ->
  match chain_extract (chainf pp i) sigstar dstar sigi d w.-1 with
  | ChainColl k u v =>
      [/\ d <= k < w.-1,
          v = chain (chainf pp i) sigi d (k - d),
          u != v
        & F pp (i, k) u = F pp (i, k) v]
  | ChainMeet => chain (chainf pp i) sigstar dstar (d - dstar) = sigi
  end.
Proof.
move=> hdd hdw heq.
have hji : (dstar <= d)%N := ltnW hdd.
have hie : (d <= w.-1)%N by rewrite -ltnS (ltn_predK hdw).
have := chain_extractP hji hie heq.
rewrite /chain_extract_ok.
case: (chain_extract _ _ _ _ _ _) => [k u v|] //.
by case=> hk _ hv hne hcol; split.
Qed.

(** PRE-case post-processing: if the forged chain meets [sigi] at
    position [d] then its value ONE step earlier (recomputable by the
    reduction from the forged signature) is an [F]-preimage of [sigi] at
    tweak [(i, d.-1)].  Post-UD, [sigi = F pp (i, d.-1) u_i] with [u_i]
    hidden uniform — i.e. [sigi] is literally the SM-PRE oracle's answer
    at tweak [(i, d.-1)], so this is the message that wins PCHECK. *)
Lemma forgery_pre_preimage pp i d (sigi sigstar : N) dstar :
  dstar < d ->
  chain (chainf pp i) sigstar dstar (d - dstar) = sigi ->
  F pp (i, d.-1) (chain (chainf pp i) sigstar dstar (d.-1 - dstar)) = sigi.
Proof.
move=> hdd hmeet.
have hd1 : dstar <= d.-1 by rewrite -ltnS (ltn_predK hdd).
have hn : d - dstar = (d.-1 - dstar).+1.
  by rewrite -subSn // (ltn_predK hdd).
by move: hmeet; rewrite hn chain_rcons subnKC.
Qed.

(* ------------------------------------------------------------------ *)
(** *** nth-form access to the verification equation *)

(** A passing verification forces, at every chain [i < l], the forged
    completion to hit the public end. *)
Lemma verify_sig_nth pp (ends : seq N) (m : seq nat) (sg : seq N)
    (y0 : N) i :
  verify_sig pp ends m sg ->
  size ends = l -> i < l ->
  chain (chainf pp i) (nth y0 sg i) (nth 0 m i) (w.-1 - nth 0 m i)
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
  = chain (chainf pp i) (nth y0 sg i) (nth 0 m i) (w.-1 - nth 0 m i).
Proof.
move=> hm hsg hi.
rewrite /ends_from_sig (nth_map (0, (0, y0))) ?size_zip ?size_iota
        ?hm ?hsg ?minnn //.
rewrite nth_zip ?size_iota ?size_zip ?hm ?hsg ?minnn //.
rewrite nth_zip ?hm ?hsg //=.
by rewrite nth_iota // add0n.
Qed.

(** THE composed forgery pipeline, packaged for the reduction. *)
Lemma forgery_classify pp (m mstar : seq nat) (sg sgstar : seq N)
    (y0 : N) :
  valid_msg m -> size sg = l ->
  verify_sig pp (ends_from_sig pp m sg) mstar sgstar ->
  mstar != m ->
  exists2 i, i < l &
    [/\ nth 0 mstar i < nth 0 m i, nth 0 m i < w &
        match chain_extract (chainf pp i) (nth y0 sgstar i) (nth 0 mstar i)
                            (nth y0 sg i) (nth 0 m i) w.-1 with
        | ChainColl k u v =>
            [/\ nth 0 m i <= k < w.-1,
                v = chain (chainf pp i) (nth y0 sg i) (nth 0 m i)
                          (k - nth 0 m i),
                u != v
              & F pp (i, k) u = F pp (i, k) v]
        | ChainMeet =>
            chain (chainf pp i) (nth y0 sgstar i) (nth 0 mstar i)
                  (nth 0 m i - nth 0 mstar i) = nth y0 sg i
        end].
Proof.
move=> hvm hsg hver hne.
have hvm' : valid_msg mstar by case/and3P: hver.
have hm : size m = l by case/and3P: hvm => /eqP.
have [i hi hlt] := forged_digit_lt _ _ hvm hvm' hne.
exists i => //.
have hdw : nth 0 m i < w := valid_msg_digit _ _ hvm hi.
have hends := size_ends_from_sig pp _ _ hm hsg.
have h1 := verify_sig_nth _ _ _ _ y0 _ hver hends hi.
rewrite (ends_from_sig_nth pp _ _ y0 _ hm hsg hi) in h1.
split=> //.
exact: (forgery_cases _ _ _ _ _ _ hlt hdw h1).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Target bookkeeping for the TCR reduction *)

(** Targets of one chain: position [k] runs over
    [iota d_i (w.-1 - d_i)] = [d_i, ..., w.-2]; the input committed at
    [(i, k)] is the honest chain value at [k], walked from the signature
    digit. *)
Definition tcr_chain (pp : PP) (i d : nat) (sg : N) :
    seq ((nat * nat) * N) :=
  [seq ((i, k), chain (chainf pp i) sg d (k - d)) | k <- iota d (w.-1 - d)].

(** The full committed target list. *)
Definition tcr_targets (pp : PP) (m : seq nat) (sigs : seq N) :
    seq ((nat * nat) * N) :=
  flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
          | q <- zip (iota 0 l) (zip m sigs)].

(** Position of target [(i, k)] in [tcr_targets]. *)
Definition tcr_index (m : seq nat) (i k : nat) : nat :=
  sumn [seq w.-1 - d | d <- take i m] + (k - nth 0 m i).

(** Auxiliary forms, generalized over the starting chain index [st]. *)

Lemma size_tcr_targets_from pp st (ds : seq nat) (ss : seq N) :
  size ss = size ds ->
  size (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                | q <- zip (iota st (size ds)) (zip ds ss)])
  = sumn [seq w.-1 - d | d <- ds].
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //= [hss].
by rewrite size_cat size_map size_iota (IH st.+1 ss hss).
Qed.

Lemma tcr_targets_from_nth pp st (ds : seq nat) (ss : seq N) i k
    (x0 : (nat * nat) * N) (y0 : N) :
  size ss = size ds -> i < size ds -> nth 0 ds i <= k < w.-1 ->
  nth x0
    (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
             | q <- zip (iota st (size ds)) (zip ds ss)])
    (sumn [seq w.-1 - d | d <- take i ds] + (k - nth 0 ds i))
  = (((st + i)%N, k),
     chain (chainf pp (st + i)) (nth y0 ss i) (nth 0 ds i)
           (k - nth 0 ds i)).
Proof.
elim: ds st ss i => [|d ds IH] st ss i hss hi hk.
  by rewrite ltn0 in hi.
case: ss hss => [|s ss] //= [hss]; case: i hi hk => [|i] hi hk.
- move: hk => /andP[hdk hkw].
  have hdw : d < w.-1 := leq_ltn_trans hdk hkw.
  have hlt : k - d < w.-1 - d := ltn_sub2r hdw hkw.
  have hsz : k - d < size (iota d (w.-1 - d)) by rewrite size_iota.
  rewrite /= add0n addn0 nth_cat size_map size_iota hlt (nth_map 0) //.
  by rewrite nth_iota // subnKC.
- rewrite /= -addnA nth_cat size_map size_iota ltnNge leq_addr /= addKn.
  by rewrite (IH st.+1 ss i hss hi hk) addSnnS.
Qed.

Lemma tcr_tweaks_from_ge pp st (ds : seq nat) (ss : seq N) :
  all (fun t : nat * nat => st <= t.1)
      (unzip1 (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                       | q <- zip (iota st (size ds)) (zip ds ss)])).
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //=.
rewrite unzip1_cat all_cat; apply/andP; split.
- rewrite /tcr_chain /unzip1 -map_comp all_map.
  by apply/allP => k _ /=.
- apply/allP => t ht.
  have /allP/(_ t ht) /= hge := IH st.+1 ss.
  exact: ltnW.
Qed.

Lemma tcr_tweaks_from_uniq pp st (ds : seq nat) (ss : seq N) :
  uniq (unzip1 (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                        | q <- zip (iota st (size ds)) (zip ds ss)])).
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //=.
rewrite unzip1_cat cat_uniq; apply/and3P; split.
- rewrite /tcr_chain /unzip1 -map_comp map_inj_uniq ?iota_uniq //.
  by move=> k1 k2 /(congr1 (fun p : nat * nat => p.2)) e; exact: e.
- apply/hasPn => t ht /=.
  have /allP/(_ t ht) /= hge := tcr_tweaks_from_ge pp st.+1 ds ss.
  rewrite /tcr_chain /unzip1 -map_comp.
  apply/negP => /mapP[k _ et].
  by move: hge; rewrite et ltnn.
- exact: IH.
Qed.

(** Size of the committed list. *)
Lemma size_tcr_targets pp (m : seq nat) (sigs : seq N) :
  size m = l -> size sigs = l ->
  size (tcr_targets pp m sigs) = sumn [seq w.-1 - d | d <- m].
Proof.
move=> hm hsigs.
by rewrite /tcr_targets -hm size_tcr_targets_from // hsigs hm.
Qed.

(** Crude cap: the SM-TCR budget [p := l * w] always suffices. *)
Lemma size_tcr_targets_leq pp (m : seq nat) (sigs : seq N) :
  size m = l -> size sigs = l ->
  size (tcr_targets pp m sigs) <= l * w.
Proof.
move=> hm hsigs.
rewrite size_tcr_targets //.
have hall : all (fun x => x <= w) [seq w.-1 - d | d <- m].
  apply/allP => x /mapP[d _ ->].
  exact: leq_trans (leq_subr _ _) (leq_pred _).
have := sumn_all_leq _ _ hall.
by rewrite size_map hm.
Qed.

(** The committed index of [(i, k)] is in range. *)
Lemma tcr_index_lt (m : seq nat) i k :
  size m = l -> i < l -> nth 0 m i <= k < w.-1 ->
  tcr_index m i k < sumn [seq w.-1 - d | d <- m].
Proof.
move=> hm hi /andP[hdk hkw].
rewrite /tcr_index -[in X in _ < X](cat_take_drop i m) (drop_nth 0) ?hm //.
rewrite map_cat sumn_cat /= ltn_add2l.
apply: ltn_addr; apply: ltn_sub2r => //.
exact: leq_ltn_trans hdk hkw.
Qed.

(** THE bookkeeping lemma: at index [tcr_index m i k] the reduction
    committed exactly tweak [(i, k)] with input the honest chain value
    at [k]. *)
Lemma tcr_targets_nth pp (m : seq nat) (sigs : seq N) i k
    (x0 : (nat * nat) * N) (y0 : N) :
  size m = l -> size sigs = l -> i < l ->
  nth 0 m i <= k < w.-1 ->
  nth x0 (tcr_targets pp m sigs) (tcr_index m i k)
  = ((i, k),
     chain (chainf pp i) (nth y0 sigs i) (nth 0 m i) (k - nth 0 m i)).
Proof.
move=> hm hsigs hi hk.
have hss : size sigs = size m by rewrite hsigs hm.
have hi' : i < size m by rewrite hm.
rewrite /tcr_targets /tcr_index -hm.
by rewrite (tcr_targets_from_nth pp 0 _ _ _ _ x0 y0 hss hi' hk) ?add0n.
Qed.

(** Tweak distinctness. *)
Lemma tcr_targets_tweaks_uniq pp (m : seq nat) (sigs : seq N) :
  size m = l -> uniq (unzip1 (tcr_targets pp m sigs)).
Proof.
move=> hm; rewrite /tcr_targets -hm.
exact: tcr_tweaks_from_uniq.
Qed.

(** Every committed tweak-target has chain index [< st + size ds] and
    position [< w.-1]. *)
Lemma tcr_tweaks_from_range pp st (ds : seq nat) (ss : seq N) :
  all (fun t : nat * nat => (t.1 < st + size ds)%N && (t.2 < w.-1)%N)
      (unzip1 (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                       | q <- zip (iota st (size ds)) (zip ds ss)])).
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //=.
rewrite unzip1_cat all_cat; apply/andP; split.
- rewrite /tcr_chain /unzip1 -map_comp all_map.
  apply/allP => k; rewrite mem_iota => /andP[hdk hk2] /=.
  have hlt : d < w.-1.
    by move: (leq_ltn_trans hdk hk2); rewrite -{1}(addn0 d) ltn_add2l subn_gt0.
  apply/andP; split.
  + by rewrite addnS ltnS leq_addr.
  + by move: hk2; rewrite (subnKC (ltnW hlt)).
- apply/allP => t ht.
  have /allP/(_ t ht) := IH st.+1 ss.
  by rewrite addSnnS.
Qed.

(** THE range bookkeeping lemma consumed by the encoded-tweak
    injectivity side conditions. *)
Lemma tcr_targets_mem_range pp (m : seq nat) (sigs : seq N) t :
  size m = l -> t \in unzip1 (tcr_targets pp m sigs) ->
  (t.1 < l)%N /\ (t.2 < w.-1)%N.
Proof.
move=> hm ht; move: ht; rewrite /tcr_targets -hm => ht.
have /allP/(_ t ht) := tcr_tweaks_from_range pp 0 m sigs.
by rewrite add0n hm => /andP[h1 h2]; split.
Qed.

(* ================= former Sec.lib.chain.Decision (TCR) ================= *)

(* ================================================================== *)
(** ** TCR decision and committed-query bookkeeping *)

(** SM-TCR budget: [l] sigma queries plus at most [l * w] walk queries. *)
Definition tcr_budget : nat := l + l * w.

(* ------------------------------------------------------------------ *)
(** *** Pure layer: committed queries, signatures, ends, indices *)

(** The committed (tweak, input) pairs live in the carrier of SM-TCR's
    target entry type. *)
Local Notation qentry := ((nat * nat) * N)%type.

(** Signature digit of chain [i] with digit [d] from root [u]. *)
Definition sig_of_root (pp : PP) (i d : nat) (u : N) : N :=
  if d is d'.+1 then F pp (i, d') u else u.

(** Queries of the upward walk of chain [i]: positions [k .. k+n-1],
    inputs the successive chain values from [x] at [k]. *)
Definition walkq (pp : PP) (i k n : nat) (x : N) : seq qentry :=
  [seq ((i, (j + k)%N), chain (chainf pp i) x k j) | j <- iota 0 n].

Lemma size_walkq pp i k n x : size (walkq pp i k n x) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma walkq_cons pp i k n x :
  walkq pp i k n.+1 x
  = ((i, k), x) :: walkq pp i k.+1 n (F pp (i, k) x).
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
Lemma nqs_le (ds : seq nat) : size ds = l -> total_query_count ds <= tcr_budget.
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
  [seq chain (chainf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
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
  = Some ((i, k), chain (chainf pp i) (sig_of_root pp i d u) d (k - d)).
Proof.
move=> /andP[hdk hkw].
have hdw : d < w.-1 := leq_ltn_trans hdk hkw.
have hlt : k - d < w.-1 - d := ltn_sub2r hdw hkw.
have hw : qnth (walkq pp i d (w.-1 - d) (sig_of_root pp i d u)) (k - d)
          = Some ((i, k), chain (chainf pp i) (sig_of_root pp i d u) d (k - d)).
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
          chain (chainf pp (st + i)%N) (sig_of_root pp (st + i)%N (nth 0 ds i) ui)
                (nth 0 ds i) (k - nth 0 ds i)%N).
Proof.
elim: ds st us i => [|d ds IH] st us i //; case: us => [|u us] //= [hsz].
case: i => [|i] hi hu hk.
- case: hu => <-; rewrite addn0 /q_index /= add0n.
  rewrite qnth_cat_l ?size_chain_queries; last first.
    rewrite /chain_query_count ltn_add2l; apply: ltn_sub2r; last by case/andP: hk.
    by apply: leq_ltn_trans (proj1 (andP hk)) (proj2 (andP hk)).
  exact: qnth_chain_queries.
- rewrite /q_index /= -addnA.
  rewrite -(size_chain_queries pp st d u) qnth_cat_r.
  by rewrite -addSnnS; apply: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The forgery classifier (computable counterpart of
    [forgery_classify]) *)

Definition tcr_decision (pp : PP) (m mstar : seq nat) (sgs sgstar : seq N) :
    option (nat * N) :=
  match ohead [seq i <- iota 0 l | nth 0 mstar i < nth 0 m i] with
  | Some i =>
      match qnth sgs i, qnth sgstar i with
      | Some si, Some si' =>
          match chain_extract (chainf pp i) si' (nth 0 mstar i) si (nth 0 m i) w.-1 with
          | ChainColl k u _ => Some (q_index m i k, u)
          | ChainMeet => None
          end
      | _, _ => None
      end
  | None => None
  end.

(** Specification: on a verifying fresh forgery against the
    [ends_from_sig] key, a [Some (j, u)] decision points at a committed
    pair [(t, v)] with [u != v] and [F pp t u = F pp t v]. *)
Lemma tcr_decisionP (pp : PP) (m mstar : seq nat) (us sgstar : seq N) :
  valid_msg m -> size us = l ->
  verify_sig pp
    (ends_of pp 0 m (sigs_of pp 0 m us)) mstar sgstar ->
  mstar \notin [:: m] ->
  match tcr_decision pp m mstar (sigs_of pp 0 m us) sgstar with
  | Some (j, u) =>
      exists t v,
        [/\ qnth (commit_queries pp 0 m us) j = Some (t, v),
            u != v & F pp t u = F pp t v]
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
case E4: (chain_extract (chainf pp i) si' (nth 0 mstar i) si (nth 0 m i) w.-1) => [k u v|];
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

(* ================= former Sec.lib.chain.Decision (PRE) ================= *)

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
          match chain_extract (chainf pp i) si' (nth 0 mstar i) si
                  (nth 0 m i) w.-1 with
          | ChainColl _ _ _ => None
          | ChainMeet =>
              Some (pre_index m i,
                    chain (chainf pp i) si' (nth 0 mstar i)
                          ((nth 0 m i).-1 - nth 0 mstar i))
          end
      | _, _ => None
      end
  | None => None
  end.

(** Specification of the [Some] case: the submitted message is an
    [F]-preimage of the stored target's image. *)
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
          & F pp t x = F pp t u]
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
case E4: (chain_extract (chainf pp i) si' (nth 0 mstar i) si (nth 0 m i) w.-1) => [k u v|];
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
           = F pp (i, (nth 0 m i).-1) ui.
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
by case: (chain_extract (chainf pp i) si' (nth 0 mstar i) si (nth 0 m i) w.-1).
Qed.

End ChainCore.
