(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.lib.games.stcrp

    S-TCR(Prop): Special Target-Collision Resistance with predicate
    search, as a real/ideal game pair (see Shrincs.internal.ssprove.lib.games.thf for the
    convention).

    This is the SM-TCR variant (Shrincs.internal.ssprove.lib.games.smtcr) where the challenge
    oracle, on query
    (T, M), finds the smallest counter i with
    Prop(Th(P, T, M || i)) = 1 and returns (Th(P, T, M || i), i);
    the concatenation M || i is abstracted as [enc : Mb -> nat ->
    th_M T].  The adversary wins with (j, M, ctr) such that
    Th(P, T_j, M_j || i_j) = Th(P, T_j, M || ctr) and M <> M_j (the
    counters may coincide or differ; only the base messages must
    differ).

    DEVIATION from the paper: the paper's counter search is
    unbounded; here it is capped at [cap] iterations, matching the
    implementation reality of WOTS+C-style grinding where the
    counter is a fixed-width field.  If no i < cap satisfies the
    predicate, the oracle aborts ([#assert false]) — equivalently,
    the oracle refuses to answer; this grinding-failure event only
    ever lowers the adversary's advantage.

    Game encoding:
    - [SQUERY (t, m)]: commit a target; allowed only before [SGETPP]
      was called (phase 1), caps at [p] targets, enforces tweak
      distinctness in-oracle (the paper's DIST condition); runs the
      bounded predicate search and returns (Th(P, t, m||i), i).
    - [SGETPP]: reveal P; afterwards SQUERY is disabled.
    - [SCHECK (j, (m, ctr))]: real game returns the win predicate;
      ideal game returns false.
    - [SCOLLQ]: evaluate the other collection members under the same
      (hidden) P; available in both phases.

    S-TCR(Prop) advantage of A:
    [AdvOf (STCRP_game T C Mb enc prp cap p) A]. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.thf.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section STCRPGame.

Context (T : thf) (C : thf_coll T).
Context (Mb : choice_type)                  (* base message type        *)
        (enc : Mb -> nat -> th_M T)         (* m || i, abstract         *)
        (prp : th_N T -> bool)              (* the predicate Prop       *)
        (cap : nat)                         (* counter search bound     *)
        (p : nat).                          (* target budget            *)

Definition SQUERY : nat := 70.
Definition SGETPP : nat := 71.
Definition SCHECK : nat := 72.
Definition SCOLLQ : nat := 73.

Definition stcr_pp_loc := mkloc 74 (None : option (th_PP T)).
Definition stcr_tgts_loc :=
  mkloc 75 (emptym : {fmap nat → (th_T T × (Mb × 'nat))}).
Definition stcr_tws_loc := mkloc 76 ([::] : seq (th_T T)).
Definition stcr_rev_loc := mkloc 77 (false : bool).

Definition I_STCRP :=
  [interface
    [ SQUERY ] : { th_T T × Mb ~> th_N T × 'nat } ;
    [ SGETPP ] : { 'unit ~> th_PP T } ;
    [ SCHECK ] : { 'nat × (Mb × 'nat) ~> 'bool } ;
    [ SCOLLQ ] : { tc_T C × tc_M C ~> tc_N C }
  ].

Definition STCRP_game (b : bool) : game I_STCRP :=
  [package [fmap stcr_pp_loc ; stcr_tgts_loc ; stcr_tws_loc ; stcr_rev_loc ] ;
    [ SQUERY ] : { th_T T × Mb ~> th_N T × 'nat } '(t, m) {
      revealed ← get stcr_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get stcr_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      ppo ← get stcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put stcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      let found := [seq i <- iota 0 cap | prp (th_eval T pp t (enc m i))] in
      match found with
      | i :: _ =>
          tgts ← get stcr_tgts_loc ;;
          #put stcr_tgts_loc := setm tgts (size tws) (t, (m, i)) ;;
          #put stcr_tws_loc := rcons tws t ;;
          ret (th_eval T pp t (enc m i), i)
      | [::] =>
          (* grinding failure: no counter below [cap] satisfies Prop.
             Modeled as abort [#assert false] => measure 0, so it can
             only LOWER the adversary's advantage, never help.  In the
             WOTS+C instantiation it is in fact unreachable: G_forge_sampledkey's
             COMMIT pre-asserts [isSome (find_ctr ...)] (grinding has
             already succeeded before SQUERY).  Continuation is dead. *)
          #assert false ;;
          ret (th_eval T pp t (enc m 0), 0)
      end
    } ;
    [ SGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get stcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put stcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put stcr_rev_loc := true ;;
      ret pp
    } ;
    [ SCHECK ] : { 'nat × (Mb × 'nat) ~> 'bool } '(j, (m, ctr)) {
      revealed ← get stcr_rev_loc ;;
      #assert revealed ;;
      if b then
        tgts ← get stcr_tgts_loc ;;
        match getm tgts j with
        | Some (t0, (m0, i0)) =>
            ppo ← get stcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put stcr_pp_loc := Some pp ;;
               ret pp
           end ;;
            ret ((m != m0) &&
                 (th_eval T pp t0 (enc m0 i0) == th_eval T pp t0 (enc m ctr)))
        | None => ret false
        end
      else
        ret false
    } ;
    [ SCOLLQ ] : { tc_T C × tc_M C ~> tc_N C } '(t, m) {
      ppo ← get stcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put stcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (tc_eval C pp t m)
    }
  ].

End STCRPGame.
