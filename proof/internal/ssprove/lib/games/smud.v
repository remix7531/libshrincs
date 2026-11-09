(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.games.smud

    Single-function Multi-target Undetectability.

    Unlike the search games (SM-TCR, SM-PRE), SM-UD is NATIVELY a
    distinguishing notion: the paper defines the advantage directly
    as the difference between the adversary's output distributions
    against the two oracles O_P(.,0) (hash of a hidden random input)
    and O_P(.,1) (uniformly random output).  Accordingly there is no
    CHECK oracle here; the game pair [SMUD_game] IS the paper's pair
    of experiments, and [AdvOf (SMUD_game T C p) A] coincides with
    the paper's Adv^{UD}_{Th,p}(A) (no real/ideal check-oracle
    convention needed, cf. Sec.lib.games.thf).

    Experiment structure (paper): a first stage queries the oracle on
    up to [p] DISTINCT tweaks, without seeing P; the second stage
    receives P and outputs a guess bit.

    Game encoding:
    - [UQUERY t]: allowed only before [UGETPP] was called, caps at
      [p] queries, enforces tweak freshness in-oracle; real ([true]):
      sample x and return Th(P,t,x); ideal ([false]): return a fresh
      uniform output.
    - [UCOLLQ]: evaluate the other collection members under the same
      (hidden) P; available in both phases.
    - [UGETPP]: reveal P; afterwards UQUERY is disabled.

    SM-UD advantage of A: [AdvOf (SMUD_game T C p) A]. *)

From Sec.lib Require Import prelude games.thf.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SMUDGame.

Context (T : thf) (C : thf_coll T) (p : nat).

Definition UQUERY : nat := 60.
Definition UGETPP : nat := 61.
Definition UCOLLQ : nat := 62.

Definition ud_pp_loc := mkloc 64 (None : option (th_PP T)).
Definition ud_tws_loc := mkloc 65 ([::] : seq (th_T T)).
Definition ud_rev_loc := mkloc 66 (false : bool).

Definition I_SMUD :=
  [interface
    [ UQUERY ] : { th_T T ~> th_N T } ;
    [ UGETPP ] : { 'unit ~> th_PP T } ;
    [ UCOLLQ ] : { tc_T C × tc_M C ~> tc_N C }
  ].

Definition SMUD_game (b : bool) : game I_SMUD :=
  [package [fmap ud_pp_loc ; ud_tws_loc ; ud_rev_loc ] ;
    [ UQUERY ] : { th_T T ~> th_N T } (t) {
      revealed ← get ud_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get ud_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      (* Freshness bookkeeping is recorded for BOTH bits, before the
         branch: real and ideal enforce the same query count and
         distinctness.  The ideal branch below uses neither [t] nor
         [pp] (it samples a fresh [y]); only the count/distinctness has
         to match the real game, so there is no information leak. *)
      #put ud_tws_loc := rcons tws t ;;
      if b then
        ppo ← get ud_pp_loc ;;
        pp ← match ppo with
             | Some pp => ret pp
             | None =>
                 pp ← th_dPP T ;;
                 #put ud_pp_loc := Some pp ;;
                 ret pp
             end ;;
        x ← th_dM T ;;
        ret (th_eval T pp t x)
      else
        y ← th_dN T ;;
        ret y
    } ;
    [ UGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get ud_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put ud_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put ud_rev_loc := true ;;
      ret pp
    } ;
    [ UCOLLQ ] : { tc_T C × tc_M C ~> tc_N C } '(t, m) {
      ppo ← get ud_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put ud_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (tc_eval C pp t m)
    }
  ].

End SMUDGame.
