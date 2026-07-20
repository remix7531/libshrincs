(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * HBS.math.chain

    Winternitz hash chains with the chain POSITION as abstract tweak,
    and the collision-or-preimage extraction lemma that is the pure
    core of the WOTS(+C) forgery analysis.

    Counterpart of the chain function [ch]/[cf] and the chain
    collision/preimage machinery ([is_coll], [find_collidx_l]/
    [find_collidx_r], [extr_coll_l]/[extr_coll_r], [extr_pre]) of
    [resources/FV-SPHINCSPLUS-EC/proofs/WOTS_TW_ES.ec].  As in
    HBS.math.Merkle, the extraction is a total computable classifier
    ([chain_extract]) with a spec lemma in [match]-style
    ([chain_extractP], cf. [extractP] there).

    INDEX CONVENTIONS (consumers rely on these; do not change):

    - [chain f x s n] applies the step function [f] at positions
      [s, s.+1, ..., s + n - 1] starting from [x].  The "value at
      position p" of a chain started from [x] at position [s] is
      [chain f x s (p - s)]; in particular the honest chain from
      secret [x] has value [chain f x 0 p] at position [p], and
      [chain f x 0 p.+1 = f p (chain f x 0 p)] ([chain_succ]).
    - [f] is the position-tweaked chain step: the caller instantiates
      [f p := F (address-for-position p)], so a position [p] uniquely
      identifies a committed hash target.
    - A COLLISION AT STEP [k] is a pair of inputs [u != v] at position
      [k] with equal outputs [f k u = f k v] at position [k.+1].
    - [chain_extract y j z i e] compares the forged chain (started
      from [y] at position [j]) with the honest chain (started from
      [z] at position [i]), both ending at position [e], where
      [j <= i <= e].  Under endpoint equality
      [chain f y j (e - j) = chain f z i (e - i)] it returns either
      [ChainColl k u v] with [i <= k < e], [u] the forged-side value
      at position [k] (i.e. [chain f y j (k - j)]) and [v] the
      HONEST-side value at position [k] (i.e. [chain f z i (k - i)]);
      or [ChainMeet]: the forged chain meets the honest chain exactly
      at position [i], [chain f y j (i - j) = z] — the forger
      produced a preimage chain into the honest value at position [i]
      (the SM-PRE / SM-UD case for the crypto layer).
      Collisions at steps below [i] are never reported: if the chains
      disagree at [i] then they already disagree at the first
      compared position, and the classifier walks forward from [i].

    Pure MathComp; no SSProve imports (docs/STYLE.md rule 5). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_boot all_order.
Set Warnings "notation-overridden,ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Chain.

Context {A : eqType}.

(** Position-tweaked chain step (see header). *)
Variable f : nat -> A -> A.

(* ------------------------------------------------------------------ *)
(** ** The chain function and its algebra *)

(** Apply [f] at positions [s, ..., s + n - 1] starting from [x]. *)
Fixpoint chain (x : A) (s n : nat) {struct n} : A :=
  if n is n'.+1 then chain (f s x) s.+1 n' else x.

Lemma chain0 x s : chain x s 0 = x.
Proof. by []. Qed.

(** Peel one step at the front. *)
Lemma chainS x s n : chain x s n.+1 = chain (f s x) s.+1 n.
Proof. by []. Qed.

Lemma chain1 x s : chain x s 1 = f s x.
Proof. by []. Qed.

(** Composition: counterpart of [ch_comp] in WOTS_TW_ES.ec. *)
Lemma chain_cat x s m n : chain x s (m + n) = chain (chain x s m) (s + m) n.
Proof.
by elim: m x s => [|m IH] x s /=; [rewrite addn0 | rewrite IH addSnnS].
Qed.

(** Peel one step at the end: counterpart of [chS] in WOTS_TW_ES.ec. *)
Lemma chain_rcons x s n : chain x s n.+1 = f (s + n) (chain x s n).
Proof. by rewrite -addn1 chain_cat. Qed.

(** Honest-chain step: the honest value at position [k.+1] is the
    [f k]-image of the honest value at position [k]. *)
Lemma chain_succ x k : chain x 0 k.+1 = f k (chain x 0 k).
Proof. by rewrite chain_rcons. Qed.

(** Re-split a chain at an intermediate position [i]: the value at
    position [e] of the chain from [y] at [j] equals the chain
    restarted at position [i] from the intermediate value. *)
Lemma chain_split y j i e :
  j <= i -> i <= e ->
  chain y j (e - j) = chain (chain y j (i - j)) i (e - i).
Proof.
move=> hji hie.
have -> : e - j = (i - j) + (e - i).
  by rewrite addnBA // addnC addnBA // subnAC addnK.
by rewrite chain_cat subnKC.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Forgery analysis *)

(** Outcome of comparing a forged chain against the honest chain
    (index conventions in the header). *)
Variant ccase : Type :=
  | ChainColl of nat & A & A
    (** [ChainColl k u v]: collision at step [k]: [u != v],
        [f k u = f k v], [u] forged-side and [v] honest-side value at
        position [k]. *)
  | ChainMeet
    (** The forged chain meets the honest chain exactly at the honest
        chain's start position. *).

(** Walk both chains forward from position [k] ([u] forged-side
    value, [v] honest-side value, [n] steps remaining) and report the
    FIRST step at which distinct inputs hash to equal outputs.  Once
    the values differ they keep differing until such a step, so under
    endpoint equality [ChainMeet] is only returned when [u == v] at
    the entry position. *)
Fixpoint chain_search (u v : A) (k n : nat) {struct n} : ccase :=
  if n is n'.+1 then
    if u == v then ChainMeet
    else if f k u == f k v then ChainColl k u v
    else chain_search (f k u) (f k v) k.+1 n'
  else ChainMeet.

Lemma chain_searchP u v k n :
  chain u k n = chain v k n ->
  match chain_search u v k n with
  | ChainColl k' u' v' =>
      [/\ k <= k' < k + n,
          u' = chain u k (k' - k), v' = chain v k (k' - k),
          u' != v' & f k' u' = f k' v']
  | ChainMeet => u = v
  end.
Proof.
elim: n u v k => [|n IH] u v k /= heq; first exact: heq.
case: (altP (u =P v)) => [heqv|hne] /=; first exact: heqv.
case: (altP (f k u =P f k v)) => [hcol|hncol] /=.
- (* collision at the entry step *)
  split; rewrite ?subnn //.
  by rewrite leqnn addnS ltnS leq_addr.
- (* values still differ after one step: recurse *)
  have := IH (f k u) (f k v) k.+1 heq.
  case: (chain_search _ _ _ _) => [k' u' v'|]; last first.
    by move=> hfeq; rewrite hfeq eqxx in hncol.
  move=> [hk' hu' hv' hne' hcol']; split=> //.
  + by case/andP: hk' => h1 h2; rewrite -addSnnS (ltnW h1) h2.
  + have hlt : k < k' by case/andP: hk'.
    by rewrite hu' -(subnSK hlt) /=.
  + have hlt : k < k' by case/andP: hk'.
    by rewrite hv' -(subnSK hlt) /=.
Qed.

(** Forgery classifier: forged chain from [y] at position [j], honest
    chain from [z] at position [i], both ending at position [e].
    Total function; [chain_extractP] characterizes its output under
    the verification invariant. *)
Definition chain_extract (y : A) (j : nat) (z : A) (i e : nat) : ccase :=
  chain_search (chain y j (i - j)) z i (e - i).

(** Specification of [chain_extract]'s outcomes. *)
Definition chain_extract_ok (y : A) (j : nat) (z : A) (i e : nat)
    (c : ccase) : Prop :=
  match c with
  | ChainColl k u v =>
      [/\ i <= k < e,
          u = chain y j (k - j), v = chain z i (k - i),
          u != v & f k u = f k v]
  | ChainMeet => chain y j (i - j) = z
  end.

Lemma chain_extractP y j z i e :
  j <= i -> i <= e ->
  chain y j (e - j) = chain z i (e - i) ->
  chain_extract_ok y j z i e (chain_extract y j z i e).
Proof.
move=> hji hie heq.
have hinner : chain (chain y j (i - j)) i (e - i) = chain z i (e - i).
  by rewrite -chain_split.
rewrite /chain_extract_ok /chain_extract.
have := chain_searchP hinner.
case: (chain_search _ _ _ _) => [k u v|] //.
move=> [hk hu hv hne hcol]; split=> //.
- by move: hk; rewrite subnKC.
- have hik : i <= k by case/andP: hk.
  by rewrite hu -(chain_split y hji hik).
Qed.

(** Specialization to the honest full-length chain: the honest signer
    starts from secret [x] at position 0, so the honest value at
    position [p] is [chain x 0 p] and the honest-side collision input
    [v] is identified by its position alone ([v = chain x 0 k], with
    honest output [f k v = chain x 0 k.+1] by [chain_succ]).  This is
    the statement consumed by the WOTS+C reduction: a forger knowing
    the honest value at position [i] reveals [y] claimed at position
    [j < i] whose continuation matches the honest endpoint at [e]. *)
Lemma chain_extract_honestP y j x i e :
  j <= i -> i <= e ->
  chain y j (e - j) = chain x 0 e ->
  match chain_extract y j (chain x 0 i) i e with
  | ChainColl k u v =>
      [/\ i <= k < e,
          u = chain y j (k - j), v = chain x 0 k,
          u != v & f k u = f k v]
  | ChainMeet => chain y j (i - j) = chain x 0 i
  end.
Proof.
move=> hji hie heq.
have hsp := chain_split x (leq0n i) hie; rewrite !subn0 in hsp.
have h0 : chain y j (e - j) = chain (chain x 0 i) i (e - i).
  by rewrite heq.
have := chain_extractP hji hie h0.
rewrite /chain_extract_ok.
case: (chain_extract _ _ _ _ _) => [k u v|] //.
move=> [hk hu hv hne hcol]; split=> //.
have hik : i <= k by case/andP: hk.
have hsk := chain_split x (leq0n i) hik; rewrite !subn0 in hsk.
by rewrite hv -hsk.
Qed.

(** If the forged chain meets the honest chain at position [i], it
    agrees with it at EVERY later position (in particular at all
    positions up to the end of the chain). *)
Lemma chain_meet_agree y j x i m :
  j <= i -> i <= m ->
  chain y j (i - j) = chain x 0 i ->
  chain y j (m - j) = chain x 0 m.
Proof.
move=> hji him hmeet.
have hs := chain_split x (leq0n i) him; rewrite !subn0 in hs.
by rewrite (chain_split y hji him) hmeet -hs.
Qed.

End Chain.
