(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.lib.wots.games

    Game-instance scaffolding for the fixed-sum WOTS security proof:
    the [thf]/[thf_coll] instances shared by the
    whole proof, the flattened starting game [G0flat] with the proved
    equivalence [G0flat_perfect] relating it to the generic
    known-message game [KOTS_game fixed_sum_scheme], and the post-UD-hybrid
    game [G1] (definition only; its hops live in UDHop.v).

    [G0flat] is a self-contained flattened game:
    package: the bodies of COMMIT and KFORGE inline the scheme's
    keygen/sign/verify (sampling [pp] and the chain starts directly,
    computing [chain_ends]/[sign_digits]/[verify_sig] as pure
    operations).  It deliberately uses FRESH locations (ids 200+)
    instead of reusing [kots_pk_loc]/[kots_log_loc], so that
    [G0flat_perfect] exercises the real relational machinery: a
    [heap_ignore] invariant over the four private locations, joined
    with two [couple_cross _ _ eq] semi-invariants stating that each
    KOTS location on the left holds the same value as the
    corresponding G0flat location on the right.

    Orientation: [perfect (I_KOTS FS) (KOTS_game FS b) (G0flat b)],
    i.e. the generic game is the LEFT/lhs program.  This matches the
    [couple_cross] convention (lhs location first) and lets later
    hops start from [G0flat] by [perfect_trans]. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme sig.kots games.thf toolkit.sample_seq.
From Sec.lib Require Import chain.core toolkit.relational_rules.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section wots_games.

(** Same section context as wots.scheme. *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (l w tsum : nat).

(* ------------------------------------------------------------------ *)
(** ** The tweakable hash instance under attack

    The tweak space is the abstract chain address (chain index, chain
    position); input and output spaces coincide ([N]).  The carrier
    of ['nat × 'nat] is definitionally [nat * nat], so [F] is directly
    a [th_eval].  No collection access is needed for this construction:
    [Cots] is the trivial collection. *)

Definition Tots : thf :=
  {| th_PP := PP ; th_T := 'nat × 'nat ; th_M := N ; th_N := N ;
     th_eval := F ; th_dPP := dPP ; th_dM := dN ; th_dN := dN |}.

Definition Cots : thf_coll Tots := trivial_coll Tots.

Local Notation FS := (fixed_sum_scheme PP N F dPP dN l w tsum).

(* ------------------------------------------------------------------ *)
(** ** G0flat: the flattened KOTS game *)

Definition g0_pk_loc := mkloc 200 (None : option (Pk FS)).
Definition g0_log_loc := mkloc 201 ([::] : seq (Msg FS)).

Definition G0flat (b : bool) : game (I_KOTS FS) :=
  [package [fmap g0_pk_loc ; g0_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      xs ← sample_seq dN l ;;
      #put g0_pk_loc := Some (pp, chain_ends PP N F l w pp xs) ;;
      if valid_msg l w tsum m
      then
        #put g0_log_loc := [:: m] ;;
        ret ((pp, chain_ends PP N F l w pp xs),
             Some (sign_digits PP N F l pp xs m))
      else ret ((pp, chain_ends PP N F l w pp xs), None)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0_pk_loc ;;
        log ← get g0_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** KOTS_game FS ≈ G0flat *)

(** The invariant: heaps agree outside the four private locations;
    the KOTS locations on the left mirror the G0flat locations on the
    right. *)
Notation inv0 := (
  heap_ignore ([fmap kots_pk_loc FS ; kots_log_loc FS ; g0_pk_loc ; g0_log_loc ])
  ⋊ couple_cross (kots_pk_loc FS) g0_pk_loc eq
  ⋊ couple_cross (kots_log_loc FS) g0_log_loc eq
).

Lemma G0flat_perfect b :
  perfect (I_KOTS FS) (KOTS_game FS b) (G0flat b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv0).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT: after code simplification both sides are the same
     get/assert/sample/sample/put/if-put program, modulo location
     names.  Cross-remember the two pk reads, sync the assert, strip
     the two scheme samplings, then discharge the puts against the
     invariant. *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e.
  subst pko'.
  ssprove_sync => hpko.
  eapply r_scheme_bind; [ exact _ |] => pp.
  eapply r_scheme_bind; [ exact _ |] => xs.
  apply r_put_vs_put.
  ssprove_restore_mem.
  { ssprove_invariant. }
  destruct (valid_msg l w tsum m).
  + apply r_put_vs_put.
    ssprove_restore_pre.
    { ssprove_invariant. }
    by apply r_ret.
  + by apply r_ret.
- (* KFORGE: pure reads; cross-remember pk and log, then return. *)
  destruct arg as [m s].
  destruct b; last by apply r_ret.
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e.
  subst pko'.
  ssprove_sync => hpko.
  eapply r_get_remember_lhs => log.
  eapply r_get_remember_rhs => log'.
  ssprove_rem_rel 0%N => e'.
  subst log'.
  ssprove_forget_all.
  by apply r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** G1: the post-UD-hybrid game (definition only)

    Target of the SM-UD hybrid chain of the proof architecture.  In G0 the
    secret of chain [i] sits at position 0 and everything (signature
    digit, public end) is chained from there.  Each UD step replaces,
    for every chain that is signed past position [s], the value at
    position [s+1] by a fresh hidden sample.  After all steps the
    sampling structure on a VALID committed message [m] is, per chain
    [i] with digit [d := m_i]:

    - one fresh hidden uniform [u_i] ~ [dN];
    - the revealed signature digit is
        [σ_i := if d == 0 then u_i else F pp (i, d-1) u_i],
      i.e. for [d > 0] the hidden uniform sits at position [d-1] and
      the signature is ONE hash step away from it — exactly the
      distribution of the SM-PRE oracle's challenge (the PRE
      embedding in TCRPREHop.v is therefore distribution-perfect);
      for [d = 0] the digit IS the (uniform) chain start;
    - the public end is chained onward from the signature position:
        [pk_i := chain (chainf pp i) σ_i d (w.-1 - d)];
      positions before [d-1] are never sampled at all (they are
      unobservable, which is what the UD hybrids prove).

    On the refusal branch (invalid [m]) no UD step ever fires (no
    digit is revealed), so G1 keeps G0's sampling: secrets at
    position 0 and [chain_ends].  This implements the "sign refusal"
    edge-case choice of the proof architecture: the hybrid argument only
    rewrites the valid-message branch.

    G1 reuses G0flat's locations: the two games are never composed,
    and sharing locations makes the UD hybrid invariants smaller. *)

Definition G1 (b : bool) : game (I_KOTS FS) :=
  [package [fmap g0_pk_loc ; g0_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      if valid_msg l w tsum m
      then
        sg ← sample_sig_roots PP N F dN pp 0 m ;;
        #put g0_pk_loc := Some (pp, ends_from_sig PP N F l w pp m sg) ;;
        #put g0_log_loc := [:: m] ;;
        ret ((pp, ends_from_sig PP N F l w pp m sg), Some sg)
      else
        xs ← sample_seq dN l ;;
        #put g0_pk_loc := Some (pp, chain_ends PP N F l w pp xs) ;;
        ret ((pp, chain_ends PP N F l w pp xs), None)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0_pk_loc ;;
        log ← get g0_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

End wots_games.
