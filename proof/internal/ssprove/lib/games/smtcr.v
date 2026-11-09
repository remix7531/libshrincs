(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.lib.games.smtcr

    Single-function Multi-target Target-Collision Resistance, as a
    real/ideal game pair (see Shrincs.internal.ssprove.lib.games.thf for the convention).

    Experiment structure: a first stage commits up to [p]
    targets (tweak, message) through an oracle for Th(P,.,.) with
    DISTINCT tweaks, without seeing P; the second stage receives P
    and must output (j, M) with M <> M_j and
    Th(P,T_j,M) = Th(P,T_j,M_j).

    Game encoding:
    - [TQUERY (t, m)]: commit a target; allowed only before [GETPP]
      was called, caps at [p] targets, enforces tweak freshness
      in-oracle (the paper's DIST condition), returns Th(P,t,m).
    - [COLLQ]: evaluate the other collection members under the same
      (hidden) P; available in both phases.
    - [GETPP]: reveal P; afterwards TQUERY is disabled.
    - [CHECK (j, m)]: real game returns the win predicate; ideal
      game returns false.

    SM-TCR advantage of A: [AdvOf (SMTCR_game T C p) A]. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.thf.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SMTCRGame.

Context (T : thf) (C : thf_coll T) (p : nat).

Definition TQUERY : nat := 40.
Definition GETPP : nat := 41.
Definition CHECK : nat := 42.
Definition COLLQ : nat := 43.

Definition tcr_pp_loc := mkloc 44 (None : option (th_PP T)).
Definition tcr_tgts_loc :=
  mkloc 45 (emptym : {fmap nat → (th_T T × th_M T)}).
Definition tcr_tws_loc := mkloc 46 ([::] : seq (th_T T)).
Definition tcr_rev_loc := mkloc 47 (false : bool).

Definition I_SMTCR :=
  [interface
    [ TQUERY ] : { th_T T × th_M T ~> th_N T } ;
    [ GETPP ] : { 'unit ~> th_PP T } ;
    [ CHECK ] : { 'nat × th_M T ~> 'bool } ;
    [ COLLQ ] : { tc_T C × tc_M C ~> tc_N C }
  ].

Definition SMTCR_game (b : bool) : game I_SMTCR :=
  [package [fmap tcr_pp_loc ; tcr_tgts_loc ; tcr_tws_loc ; tcr_rev_loc ] ;
    [ TQUERY ] : { th_T T × th_M T ~> th_N T } '(t, m) {
      revealed ← get tcr_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get tcr_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      tgts ← get tcr_tgts_loc ;;
      #put tcr_tgts_loc := setm tgts (size tws) (t, m) ;;
      #put tcr_tws_loc := rcons tws t ;;
      ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t m)
    } ;
    [ GETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put tcr_rev_loc := true ;;
      ret pp
    } ;
    [ CHECK ] : { 'nat × th_M T ~> 'bool } '(j, m) {
      revealed ← get tcr_rev_loc ;;
      #assert revealed ;;
      if b then
        tgts ← get tcr_tgts_loc ;;
        match getm tgts j with
        | Some (t0, m0) =>
            ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
            ret ((m != m0) && (th_eval T pp t0 m == th_eval T pp t0 m0))
        | None => ret false
        end
      else
        ret false
    } ;
    [ COLLQ ] : { tc_T C × tc_M C ~> tc_N C } '(t, m) {
      ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (tc_eval C pp t m)
    }
  ].

End SMTCRGame.
