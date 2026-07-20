(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * HBS.wots.scheme

    A generic Winternitz-style one-time signature without a checksum,
    over messages represented by digit vectors with a fixed digit sum.

    Counterpart: wotsc.tex (Compressed WOTS+).  This scheme is WOTS+C
    minus the grinding step and minus concrete addressing: the message
    space is directly the post-grinding digit vectors (length [l],
    digits in [0..w-1], digit sum exactly [tsum]), and the tweak is
    the abstract pair (chain index, chain position).  The fixed digit
    sum plays the role of the WOTS+ checksum (wotsc.tex, one-time
    security paragraph); the corresponding pure forgery-analysis fact
    is [eq_sumn_exists_lt] in HBS.math.Encoding (used by the EU-CMA
    proof in the companion modules, not here).

    This file contains only the scheme as a [sig_scheme] instance and
    the pure correctness lemma [verify_sign]; the security proof
    lives in the companion game and hop modules.

    Design notes / deviations from the obvious transliteration:
    - [chain_ends] and [sign_digits] are maps over [zip (iota 0 l) _]
      (chain index paired with chain start / digit), and the
      verification predicate is one [all] over
      [zip (iota 0 l) (zip m (zip sg ends))].  This zip/iota
      formulation avoids needing a default element of [N] (the
      choice_type [N] has no canonical inhabitant), and correctness
      goes through one structural induction ([all_chain_checks])
      instead of [nth]-juggling.
    - [verify_sig] checks [size sg == l]; [valid_msg m] forces
      [size m = l]; the size of [ends] is NOT checked (honest keys
      have [size ends = l] by [size_chain_ends]; an [ends] shorter
      than [l] only truncates the [all], i.e. only weakens keys the
      key generator never produces).
    - No positivity assumption on [w] is needed: [verify_sign] only
      reasons about positions [i < l], where [valid_msg m] gives
      [nth 0 m i < w] and hence [0 < w] for free; if [l = 0] the
      verification [all] is vacuous. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import prelude math.chain math.encoding sig.scheme toolkit.sample_seq.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

Section fixed_sum_scheme.

(** Public parameter and hash domain (one hash-output type [N]). *)
Context (PP N : choice_type).

(** Tweaked hash; the tweak is (chain index, chain position). *)
Context (F : PP -> nat * nat -> N -> N).

(** Samplers for key generation. *)
Context (dPP : dist PP) (dN : dist N).

(** Number of chains, digit bound (digits in [0..w-1]), target sum. *)
Context (l w tsum : nat).

(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

(** Chain step of the [i]-th chain (HBS.math.Chain conventions: the
    position is the first argument of the step function). *)
Definition chainf (pp : PP) (i : nat) : nat -> N -> N :=
  fun pos x => F pp (i, pos) x.

(** Message validity: [l] digits, all below [w], digit sum exactly
    [tsum] (the WOTS+C post-grinding message space, wotsc.tex). *)
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
have hdw : d <= w.-1 by rewrite -ltnS (ltn_predK hd).
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

    One-time scheme: [sign] returns the key unchanged (the EU-CMA
    one-time statement uses signing budget [q_s = 1]); it
    refuses ([None]) on messages outside the fixed-sum space.  The
    public parameter is sampled by [keygen] and carried in both keys
    (no separate parameter phase, as in wotsc.tex where PK.seed is
    part of the public key). *)

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

End fixed_sum_scheme.
