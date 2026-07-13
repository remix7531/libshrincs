(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Model.math.chain

    Winternitz hash chains with the chain POSITION as abstract tweak,
    and the collision-or-preimage extraction lemma that is the pure
    core of the WOTS(+C) forgery analysis.  The extraction is a total
    computable classifier ([chain_extract]) with a spec lemma in
    [match]-style ([chain_extractP]).

    DEPENDENT (width-bounded) DESIGN.  Everything is parameterised by a
    chain width [w : nat].  The step function

      [f : forall p : nat, (p < w)%N -> A -> A]

    RECEIVES the proof that its position [p] is in range, so a consumer
    (the SSProve address builder) can construct an EXACT [fin]-bounded
    position at every fold step with NO saturating clamp.  The chain
    fold [chain x s n] is then a FUNCTION of a bound proof
    [(s + n <= w)%N] which it threads to each [f]-application; likewise
    [chain_search].  Because [(p < w)%N] is a MathComp boolean,
    [is_true]-proofs of it are unique ([bool_irrelevance]); hence
    [f p H1 x = f p H2 x] for any two bound proofs, the value of a
    chain does not depend on WHICH proof is supplied ([chain_pirr]),
    and every value-level lemma below is stated up to that
    proof-irrelevance (via [chain_congr]).

    INDEX CONVENTIONS (consumers rely on these; do not change):

    - [chain x s n H] applies the step function [f] at positions
      [s, s.+1, ..., s + n - 1] starting from [x]; [H : s + n <= w]
      certifies every one of those positions is [< w].  The "value at
      position p" of a chain started from [x] at position [s] is
      [chain x s (p - s)]; in particular the honest chain from
      secret [x] has value [chain x 0 p] at position [p], and
      [chain x 0 p.+1 = f p _ (chain x 0 p)] ([chain_succ]).
    - [f] is the position-tweaked chain step: the caller instantiates
      [f p := F (address-for-position p)], so a position [p] uniquely
      identifies a committed hash target.
    - A COLLISION AT STEP [k] is a pair of inputs [u != v] at position
      [k] with equal outputs [f k _ u = f k _ v] at position [k.+1].
    - [chain_extract y j z i e ..] compares the forged chain (started
      from [y] at position [j]) with the honest chain (started from
      [z] at position [i]), both ending at position [e], where
      [j <= i <= e].  Under endpoint equality
      [chain y j (e - j) = chain z i (e - i)] it returns either
      [ChainColl k u v] with [i <= k < e], [u] the forged-side value
      at position [k] (i.e. [chain y j (k - j)]) and [v] the
      HONEST-side value at position [k] (i.e. [chain z i (k - i)]);
      or [ChainMeet]: the forged chain meets the honest chain exactly
      at position [i], [chain y j (i - j) = z] -- the forger
      produced a preimage chain into the honest value at position [i]
      (the SM-PRE / SM-UD case for the crypto layer).
      Collisions at steps below [i] are never reported: if the chains
      disagree at [i] then they already disagree at the first
      compared position, and the classifier walks forward from [i].
      [ChainColl] keeps reporting a plain [nat] position [k]: the
      spec's [i <= k < e] together with the ambient [e <= w] lets the
      consumer derive [k < w] FOR FREE, so no [fin] is needed in the
      outcome type.

    Pure MathComp; no SSProve imports (see proof/STYLE.md's Imports section,
    "Carve-out: math/"). *)

From mathcomp Require Import all_boot all_order.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Chain.

Context {A : eqType}.

(** Chain width: every applied position must be [< w]. *)
Variable w : nat.

(** Position-tweaked chain step (see header): receives the in-range
    proof so consumers build an exact [fin] position with no clamp. *)
Variable f : forall p : nat, (p < w)%N -> A -> A.

(* ------------------------------------------------------------------ *)
(** ** Bound obligations threaded through the fold.

    At the head step under [s + n.+1 <= w] the source position [s] is
    [< w] ([chain_hd_lt]); the recursive tail's bound [s.+1 + n <= w]
    follows too ([chain_tl_le]).  Factored out as named lemmas so the
    [Fixpoint] body can name them (a bare [ltac:] cannot see the
    match-bound hypothesis). *)

Lemma chain_hd_lt s n (H : (s + n.+1 <= w)%N) : (s < w)%N.
Proof. by apply: leq_trans H; rewrite -addSnnS leq_addr. Qed.

Lemma chain_tl_le s n (H : (s + n.+1 <= w)%N) : (s.+1 + n <= w)%N.
Proof. by rewrite addSnnS. Qed.

(* ------------------------------------------------------------------ *)
(** ** The chain function and its algebra *)

(** Apply [f] at positions [s, ..., s + n - 1] starting from [x],
    threading the in-range proof to each step. *)
Fixpoint chain (x : A) (s n : nat) {struct n} : (s + n <= w)%N -> A :=
  match n return (s + n <= w)%N -> A with
  | n'.+1 => fun H => @chain (f (chain_hd_lt H) x) s.+1 n' (chain_tl_le H)
  | 0     => fun _ => x
  end.
Arguments chain : clear implicits.

(** Proof-irrelevance of the width bound: the chain value never
    depends on WHICH proof of [s + n <= w] is supplied (the bound is a
    MathComp boolean, so its [is_true]-proofs are unique). *)
Lemma chain_pirr x s n (H1 H2 : (s + n <= w)%N) : chain x s n H1 = chain x s n H2.
Proof. by rewrite (bool_irrelevance H1 H2). Qed.

(** Congruence: [chain] depends only on [x], [s], [n] as values -- the
    bound proof is irrelevant, so equal indices give equal chains. *)
Lemma chain_congr x s1 s2 n1 n2 (H1 : (s1 + n1 <= w)%N) (H2 : (s2 + n2 <= w)%N) :
  s1 = s2 -> n1 = n2 -> chain x s1 n1 H1 = chain x s2 n2 H2.
Proof. move=> es en; subst s2 n2; exact: chain_pirr. Qed.

Lemma chain0 x s (H : (s + 0 <= w)%N) : chain x s 0 H = x.
Proof. by []. Qed.

(** Peel one step at the front. *)
Lemma chainS x s n (H : (s + n.+1 <= w)%N) :
  chain x s n.+1 H = chain (f (chain_hd_lt H) x) s.+1 n (chain_tl_le H).
Proof. by []. Qed.

Lemma chain1 x s (H : (s + 1 <= w)%N) : chain x s 1 H = f (chain_hd_lt H) x.
Proof. by []. Qed.

(** Front-peel with an ARBITRARY head bound [Hf] and tail bound [Ht]:
    the canonical [chainS] proofs are reconciled by irrelevance.  This
    is the workhorse that lets the compositional proofs peel a step
    with whatever bound proofs are convenient. *)
Lemma chainSr x s n (H : (s + n.+1 <= w)%N) (Hf : (s < w)%N) (Ht : (s.+1 + n <= w)%N) :
  chain x s n.+1 H = chain (f Hf x) s.+1 n Ht.
Proof. by rewrite chainS (bool_irrelevance (chain_hd_lt H) Hf); apply: chain_pirr. Qed.

(** Composition. *)
Lemma chain_cat x s m n (Hm : (s + m <= w)%N) (Hn : (s + m + n <= w)%N)
    (Hsum : (s + (m + n) <= w)%N) :
  chain x s (m + n) Hsum = chain (chain x s m Hm) (s + m) n Hn.
Proof.
elim: m x s Hm Hn Hsum => [|m IH] x s Hm Hn Hsum.
- rewrite chain0.
  apply: chain_congr; by rewrite ?addn0.
- rewrite (chainSr x Hsum (chain_hd_lt Hm) (chain_tl_le Hsum)) chainS.
  have Hn' : (s.+1 + m + n <= w)%N by rewrite addSnnS.
  rewrite (IH (f (chain_hd_lt Hm) x) s.+1 (chain_tl_le Hm) Hn' (chain_tl_le Hsum)).
  apply: chain_congr; by rewrite ?addSnnS.
Qed.

(** Peel one step at the end. *)
Lemma chain_rcons x s n (H : (s + n.+1 <= w)%N) (Hlt : (s + n < w)%N)
    (Hn : (s + n <= w)%N) :
  chain x s n.+1 H = f Hlt (chain x s n Hn).
Proof.
have Hs1 : (s + (n + 1) <= w)%N by rewrite addn1.
have Hn1 : (s + n + 1 <= w)%N by rewrite addn1.
rewrite (chain_congr x H Hs1 (erefl s) (esym (addn1 n))).
rewrite (chain_cat x Hn Hn1 Hs1) chain1.
by rewrite (bool_irrelevance (chain_hd_lt Hn1) Hlt).
Qed.

(** Honest-chain step: the honest value at position [k.+1] is the
    [f k]-image of the honest value at position [k]. *)
Lemma chain_succ x k (H : (0 + k.+1 <= w)%N) (Hlt : (k < w)%N) (Hk : (0 + k <= w)%N) :
  chain x 0 k.+1 H = f Hlt (chain x 0 k Hk).
Proof. by rewrite (chain_rcons x H Hlt Hk). Qed.

(** Re-split a chain at an intermediate position [i]: the value at
    position [e] of the chain from [y] at [j] equals the chain
    restarted at position [i] from the intermediate value. *)
Lemma chain_split y j i e
    (Hej : (j + (e - j) <= w)%N) (Hij : (j + (i - j) <= w)%N)
    (Hie' : (i + (e - i) <= w)%N) :
  j <= i -> i <= e ->
  chain y j (e - j) Hej = chain (chain y j (i - j) Hij) i (e - i) Hie'.
Proof.
move=> hji hie.
have Esplit : e - j = (i - j) + (e - i).
  by rewrite addnBA // addnC addnBA // subnAC addnK.
have Hsum : (j + ((i - j) + (e - i)) <= w)%N by rewrite -Esplit.
have Hn' : (j + (i - j) + (e - i) <= w)%N by rewrite (subnKC hji).
rewrite (chain_congr y Hej Hsum (erefl j) Esplit).
rewrite (chain_cat y Hij Hn' Hsum).
apply: chain_congr; by rewrite ?(subnKC hji).
Qed.

(** A length-0 chain (propositional [m = 0]) is the identity. *)
Lemma chain_eq0 x s m (H : (s + m <= w)%N) : m = 0 -> chain x s m H = x.
Proof. move=> e; move: H; rewrite e => H; exact: chain0. Qed.

(* ------------------------------------------------------------------ *)
(** ** Forgery analysis *)

(** Outcome of comparing a forged chain against the honest chain
    (index conventions in the header).  The collision position is a
    plain [nat]: its [< w] bound comes for free from the walk's range. *)
Variant ccase : Type :=
  | ChainColl of nat & A & A
    (** [ChainColl k u v]: collision at step [k]: [u != v],
        [f k _ u = f k _ v], [u] forged-side and [v] honest-side value
        at position [k]. *)
  | ChainMeet
    (** The forged chain meets the honest chain exactly at the honest
        chain's start position. *).

(** Walk both chains forward from position [k] ([u] forged-side
    value, [v] honest-side value, [n] steps remaining) and report the
    FIRST step at which distinct inputs hash to equal outputs.  The
    invariant [k + n <= w] certifies every walked position is [< w].
    Once the values differ they keep differing until such a step, so
    under endpoint equality [ChainMeet] is only returned when [u == v]
    at the entry position. *)
Fixpoint chain_search (u v : A) (k n : nat) {struct n} : (k + n <= w)%N -> ccase :=
  match n return (k + n <= w)%N -> ccase with
  | n'.+1 => fun H =>
      if u == v then ChainMeet
      else if f (chain_hd_lt H) u == f (chain_hd_lt H) v then ChainColl k u v
      else @chain_search (f (chain_hd_lt H) u) (f (chain_hd_lt H) v) k.+1 n' (chain_tl_le H)
  | 0     => fun _ => ChainMeet
  end.
Arguments chain_search : clear implicits.

(** The forged/honest walk classifier is correct.  In the [ChainColl]
    case the value equalities and the collision equality are stated
    "for all bound proofs" -- by irrelevance the choice is immaterial
    and the consumer instantiates with whatever proof it holds. *)
Lemma chain_searchP u v k n (H : (k + n <= w)%N) :
  chain u k n H = chain v k n H ->
  match chain_search u v k n H with
  | ChainColl k' u' v' =>
      [/\ k <= k' < k + n,
          forall Hsub : (k + (k' - k) <= w)%N, u' = chain u k (k' - k) Hsub,
          forall Hsub : (k + (k' - k) <= w)%N, v' = chain v k (k' - k) Hsub,
          u' != v' &
          forall Hk' : (k' < w)%N, f Hk' u' = f Hk' v']
  | ChainMeet => u = v
  end.
Proof.
elim: n u v k H => [|n IH] u v k H /= heq.
- exact: heq.
- case: (altP (u =P v)) => [heqv|hne] /=; first exact: heqv.
  case: (altP (f (chain_hd_lt H) u =P f (chain_hd_lt H) v)) => [hcol|hncol] /=.
  + split.
    * by rewrite leqnn addnS ltnS leq_addr.
    * by move=> Hsub; rewrite (chain_eq0 u Hsub (subnn k)).
    * by move=> Hsub; rewrite (chain_eq0 v Hsub (subnn k)).
    * exact: hne.
    * by move=> Hk'; rewrite (bool_irrelevance Hk' (chain_hd_lt H)).
  + move: (IH (f (chain_hd_lt H) u) (f (chain_hd_lt H) v) k.+1 (chain_tl_le H) heq).
    case: (chain_search (f (chain_hd_lt H) u) (f (chain_hd_lt H) v) k.+1 n (chain_tl_le H))
      => [k' u' v'|]; last first.
      by move=> hfeq; rewrite hfeq eqxx in hncol.
    move=> [hk' hu' hv' hne' hcol']; split.
    * by case/andP: hk' => h1 h2; rewrite -addSnnS (ltnW h1) h2.
    * move=> Hsub.
      have hlt : (k < k')%N by case/andP: hk'.
      have Hsub2 : (k + (k' - k.+1).+1 <= w)%N by rewrite (subnSK hlt).
      rewrite (chain_congr u Hsub Hsub2 (erefl k) (esym (subnSK hlt))).
      rewrite (chainSr u Hsub2 (chain_hd_lt H) (chain_tl_le Hsub2)).
      exact: (hu' (chain_tl_le Hsub2)).
    * move=> Hsub.
      have hlt : (k < k')%N by case/andP: hk'.
      have Hsub2 : (k + (k' - k.+1).+1 <= w)%N by rewrite (subnSK hlt).
      rewrite (chain_congr v Hsub Hsub2 (erefl k) (esym (subnSK hlt))).
      rewrite (chainSr v Hsub2 (chain_hd_lt H) (chain_tl_le Hsub2)).
      exact: (hv' (chain_tl_le Hsub2)).
    * exact: hne'.
    * exact: hcol'.
Qed.

(** Forgery classifier: forged chain from [y] at position [j], honest
    chain from [z] at position [i], both ending at position [e].
    Total function; [chain_extractP] characterizes its output under
    the verification invariant.  Takes the two chain-bound proofs
    directly (the caller supplies the exact ones it built). *)
Definition chain_extract (y : A) (j : nat) (z : A) (i e : nat)
    (Hij : (j + (i - j) <= w)%N) (Hie : (i + (e - i) <= w)%N) : ccase :=
  chain_search (chain y j (i - j) Hij) z i (e - i) Hie.
Arguments chain_extract : clear implicits.

(** Specification of [chain_extract]'s outcomes. *)
Definition chain_extract_ok (y : A) (j : nat) (z : A) (i e : nat)
    (c : ccase) : Prop :=
  match c with
  | ChainColl k u v =>
      [/\ i <= k < e,
          forall Hk : (j + (k - j) <= w)%N, u = chain y j (k - j) Hk,
          forall Hk : (i + (k - i) <= w)%N, v = chain z i (k - i) Hk,
          u != v &
          forall Hk : (k < w)%N, f Hk u = f Hk v]
  | ChainMeet => forall Hk : (j + (i - j) <= w)%N, chain y j (i - j) Hk = z
  end.

Lemma chain_extractP y j z i e
    (Hij : (j + (i - j) <= w)%N) (Hie : (i + (e - i) <= w)%N)
    (Hej : (j + (e - j) <= w)%N) :
  j <= i -> i <= e ->
  chain y j (e - j) Hej = chain z i (e - i) Hie ->
  chain_extract_ok y j z i e (chain_extract y j z i e Hij Hie).
Proof.
move=> hji hie heq.
have hinner : chain (chain y j (i - j) Hij) i (e - i) Hie = chain z i (e - i) Hie.
  by rewrite -(chain_split y Hej Hij Hie hji hie).
rewrite /chain_extract_ok /chain_extract.
move: (chain_searchP hinner).
case: (chain_search (chain y j (i - j) Hij) z i (e - i) Hie) => [k u v|]; last first.
  by move=> hmeet Hk; rewrite (chain_pirr y Hk Hij).
move=> [hk hu hv hne hcol]; split.
- by move: hk; rewrite (subnKC hie).
- move=> Hk.
  move: hk; rewrite (subnKC hie); case/andP => hik hke.
  have hew : (e <= w)%N by rewrite -(subnKC hie).
  have Hik : (i + (k - i) <= w)%N by rewrite (subnKC hik) (leq_trans (ltnW hke) hew).
  rewrite (chain_split y Hk Hij Hik hji hik).
  exact: (hu Hik).
- by move=> Hk; exact: (hv Hk).
- exact: hne.
- exact: hcol.
Qed.

(** Specialization to the honest full-length chain: the honest signer
    starts from secret [x] at position 0, so the honest value at
    position [p] is [chain x 0 p] and the honest-side collision input
    [v] is identified by its position alone ([v = chain x 0 k], with
    honest output [f k v = chain x 0 k.+1] by [chain_succ]).  This is
    the statement consumed by the WOTS+C reduction: a forger knowing
    the honest value at position [i] reveals [y] claimed at position
    [j < i] whose continuation matches the honest endpoint at [e]. *)
Lemma chain_extract_honestP y j x i e
    (Hij : (j + (i - j) <= w)%N) (Hie : (i + (e - i) <= w)%N)
    (Hej : (j + (e - j) <= w)%N) (Hxi : (0 + i <= w)%N) (He : (0 + e <= w)%N) :
  j <= i -> i <= e ->
  chain y j (e - j) Hej = chain x 0 e He ->
  match chain_extract y j (chain x 0 i Hxi) i e Hij Hie with
  | ChainColl k u v =>
      [/\ i <= k < e,
          forall Hk : (j + (k - j) <= w)%N, u = chain y j (k - j) Hk,
          forall Hk : (0 + k <= w)%N, v = chain x 0 k Hk,
          u != v &
          forall Hk : (k < w)%N, f Hk u = f Hk v]
  | ChainMeet => forall Hk : (j + (i - j) <= w)%N, chain y j (i - j) Hk = chain x 0 i Hxi
  end.
Proof.
move=> hji hie heq.
(* honest split from position 0: [chain x 0 a = chain (chain x 0 m) m (a - m)]. *)
have hsplit0 : forall (a m : nat) (Hm : (0 + m <= w)%N) (Ha : (0 + a <= w)%N)
    (Ham : (m + (a - m) <= w)%N), m <= a ->
    chain x 0 a Ha = chain (chain x 0 m Hm) m (a - m) Ham.
  move=> a m Hm Ha Ham hma.
  have Em : a = m + (a - m) by rewrite subnKC.
  have Hsum : (0 + (m + (a - m)) <= w)%N by rewrite -Em.
  have Hcat : (0 + m + (a - m) <= w)%N by rewrite add0n.
  rewrite (chain_congr x Ha Hsum (erefl 0) Em) (chain_cat x Hm Hcat Hsum).
  apply: chain_congr; by rewrite ?add0n.
have h0 : chain y j (e - j) Hej = chain (chain x 0 i Hxi) i (e - i) Hie.
  by rewrite heq; apply: (hsplit0 e i Hxi He Hie hie).
move: (chain_extractP Hij hji hie h0).
rewrite /chain_extract_ok.
case: (chain_extract y j (chain x 0 i Hxi) i e Hij Hie) => [k u v|]; last by [].
move=> [hk hu hv hne hcol]; split.
- exact: hk.
- exact: hu.
- move=> Hk.
  have hik : i <= k by case/andP: hk.
  have Hik : (i + (k - i) <= w)%N by rewrite (subnKC hik).
  rewrite (hsplit0 k i Hxi Hk Hik hik).
  exact: (hv Hik).
- exact: hne.
- exact: hcol.
Qed.

(** If the forged chain meets the honest chain at position [i], it
    agrees with it at EVERY later position (in particular at all
    positions up to the end of the chain). *)
Lemma chain_meet_agree y j x i m
    (Hij : (j + (i - j) <= w)%N) (Hjm : (j + (m - j) <= w)%N)
    (Him : (i + (m - i) <= w)%N) (Hxi : (0 + i <= w)%N) (Hxm : (0 + m <= w)%N) :
  j <= i -> i <= m ->
  chain y j (i - j) Hij = chain x 0 i Hxi ->
  chain y j (m - j) Hjm = chain x 0 m Hxm.
Proof.
move=> hji him hmeet.
have hs : chain x 0 m Hxm = chain (chain x 0 i Hxi) i (m - i) Him.
  have Em : m = i + (m - i) by rewrite subnKC.
  have Hsum : (0 + (i + (m - i)) <= w)%N by rewrite -Em.
  have Hcat : (0 + i + (m - i) <= w)%N by rewrite add0n.
  rewrite (chain_congr x Hxm Hsum (erefl 0) Em) (chain_cat x Hxi Hcat Hsum).
  apply: chain_congr; by rewrite ?add0n.
by rewrite (chain_split y Hjm Hij Him hji him) hmeet -hs.
Qed.

End Chain.
