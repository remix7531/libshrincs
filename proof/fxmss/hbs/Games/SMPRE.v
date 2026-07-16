(** * HBS.Games.SMPRE

    Single-function Multi-target Preimage Resistance, as a
    real/ideal game pair (see HBS.Games.THF for the convention).

    Counterpart: preliminaries.tex def:sm-pre; EasyCrypt
    `SM_DT_PRE_C` (collection variant) in TweakableHashFunctions.eca,
    used throughout resources/FV-SPHINCSPLUS-EC.

    Experiment structure (paper): a first stage queries, up to [p]
    times with DISTINCT tweaks, an oracle Th(P,T,x_i) where the
    inputs x_i are sampled uniformly and HIDDEN from the adversary,
    without seeing P; the second stage receives P and must output
    (j, M) with Th(P,T_j,M) = Th(P,T_j,x_j) — a preimage of the j-th
    target (no M <> x_j condition, unlike SM-TCR).

    Game encoding:
    - [PQUERY t]: commit a target; allowed only before [PGETPP] was
      called, caps at [p] targets, enforces tweak freshness in-oracle
      (the paper's DIST condition), samples x internally (hidden),
      records (t, x), returns Th(P,t,x).
    - [PCOLLQ]: evaluate the other collection members under the same
      (hidden) P; available in both phases.
    - [PGETPP]: reveal P; afterwards PQUERY is disabled.
    - [PCHECK (j, m)]: real game returns the win predicate; ideal
      game returns false.

    SM-PRE advantage of A: [AdvOf (SMPRE_game T C p) A]. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Games.THF.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SMPREGame.

Context (T : thf) (C : thf_coll T) (p : nat).

Definition PQUERY : nat := 50.
Definition PGETPP : nat := 51.
Definition PCHECK : nat := 52.
Definition PCOLLQ : nat := 53.

Definition pre_pp_loc := mkloc 54 (None : option (th_PP T)).
Definition pre_tgts_loc :=
  mkloc 55 (emptym : {fmap nat → (th_T T × th_M T)}).
Definition pre_tws_loc := mkloc 56 ([::] : seq (th_T T)).
Definition pre_rev_loc := mkloc 57 (false : bool).

Definition I_SMPRE :=
  [interface
    [ PQUERY ] : { th_T T ~> th_N T } ;
    [ PGETPP ] : { 'unit ~> th_PP T } ;
    [ PCHECK ] : { 'nat × th_M T ~> 'bool } ;
    [ PCOLLQ ] : { tc_T C × tc_M C ~> tc_N C }
  ].

Definition SMPRE_game (b : bool) : game I_SMPRE :=
  [package [fmap pre_pp_loc ; pre_tgts_loc ; pre_tws_loc ; pre_rev_loc ] ;
    [ PQUERY ] : { th_T T ~> th_N T } (t) {
      revealed ← get pre_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get pre_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      x ← th_dM T ;;
      tgts ← get pre_tgts_loc ;;
      #put pre_tgts_loc := setm tgts (size tws) (t, x) ;;
      #put pre_tws_loc := rcons tws t ;;
      ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t x)
    } ;
    [ PGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put pre_rev_loc := true ;;
      ret pp
    } ;
    [ PCHECK ] : { 'nat × th_M T ~> 'bool } '(j, m) {
      if b then
        revealed ← get pre_rev_loc ;;
        #assert revealed ;;
        tgts ← get pre_tgts_loc ;;
        match getm tgts j with
        | Some (t0, x0) =>
            ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
            ret (th_eval T pp t0 m == th_eval T pp t0 x0)%B
        | None => ret false
        end
      else
        ret false
    } ;
    [ PCOLLQ ] : { tc_T C × tc_M C ~> tc_N C } '(t, m) {
      ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (tc_eval C pp t m)
    }
  ].

End SMPREGame.
