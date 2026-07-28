(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.lib.wots.analysis

    The valid-commit game pair [G0v]/[G1v] of the fixed-sum WOTS
    security proof (definitions only; the hops live in ud_hop.v /
    tcr_hop.v / pre_hop.v).

    The pure forgery analysis these games are attacked through -- the
    digit selectors, the per-chain classifier [forgery_cases], the
    composed [forgery_classify] and the SM-TCR target bookkeeping -- is
    NOT here: it is [Sec.lib.chain.core], shared with the native WOTS+C
    proof.

    [G0v]/[G1v] are the
    valid-commit variants of games.v's [G0flat]/[G1] (the theorem is
    stated for these per the proof architecture's sign-refusal decision): COMMIT
    additionally [#assert]s [valid_msg m], so the refusal branch
    aborts the experiment and both games sign unconditionally
    afterwards.  Fresh locations 210/211, shared between G0v and G1v
    (the two are never composed; sharing keeps the UD-hybrid
    invariants small, as for G0flat/G1). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme sig.kots games.thf toolkit.sample_seq.
From Sec.lib Require Import chain.core wots.games.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Part 2: the valid-commit games G0v / G1v (definitions only) *)

Section wots_valid_games.

(** Same context as wots.games. *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (l w tsum : nat).

Local Notation FS := (fixed_sum_scheme PP N F dPP dN l w tsum).

Definition g0v_pk_loc := mkloc 210 (None : option (Pk FS)).
Definition g0v_log_loc := mkloc 211 ([::] : seq (Msg FS)).

(** [G0v] = [G0flat] with [#assert (valid_msg m)] in COMMIT
    (the proof architecture edge-case decision: an invalid commitment aborts
    the experiment; the refusal branch of G0flat disappears and
    COMMIT always logs and signs). *)
Definition G0v (b : bool) : game (I_KOTS FS) :=
  [package [fmap g0v_pk_loc ; g0v_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0v_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      pp ← dPP ;;
      xs ← sample_seq dN l ;;
      #put g0v_pk_loc := Some (pp, chain_ends PP N F l w pp xs) ;;
      #put g0v_log_loc := [:: m] ;;
      ret ((pp, chain_ends PP N F l w pp xs),
           Some (sign_digits PP N F l pp xs m))
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0v_pk_loc ;;
        log ← get g0v_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(** [G1v] = same assert + [G1]'s post-UD sampling (Games.v:
    [sample_sig_roots] hides one uniform per chain one hash step
    before the signature digit; [ends_from_sig] re-roots the public
    ends there).  G1's refusal branch is gone: it is exactly what the
    assert cuts off. *)
Definition G1v (b : bool) : game (I_KOTS FS) :=
  [package [fmap g0v_pk_loc ; g0v_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0v_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      pp ← dPP ;;
      sg ← sample_sig_roots PP N F dN pp 0 m ;;
      #put g0v_pk_loc := Some (pp, ends_from_sig PP N F l w pp m sg) ;;
      #put g0v_log_loc := [:: m] ;;
      ret ((pp, ends_from_sig PP N F l w pp m sg), Some sg)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0v_pk_loc ;;
        log ← get g0v_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

End wots_valid_games.
