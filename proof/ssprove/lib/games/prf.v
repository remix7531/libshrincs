(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.games.prf

    Keyed-hash distinguishing game (the PRF assumption), for a [khf]
    (Sec.lib.games.thf).

    Like SM-UD, this is NATIVELY a distinguishing notion: the game
    pair IS the paper's pair of experiments (no CHECK oracle, no
    real/ideal check convention; cf. Sec.lib.games.thf).  The [true] game
    answers queries with [kh_eval k m] under a hidden key [k]; the
    [false] game answers with fresh uniform outputs.

    Game encoding:
    - [FQUERY m]: caps at [q] queries and enforces query freshness
      in-oracle; real ([true]): lazily sample the hidden key [k] once
      and return Kh(k, m); ideal ([false]): return a fresh uniform
      output.

    The distinct-query restriction makes the ideal branch the "random
    function on at most [q] distinct points" oracle WITHOUT
    memoization: on distinct queries, lazily sampling a random
    function's table row and sampling a fresh output are the same
    distribution.  A standard PRF distinguisher bound therefore
    implies a bound on [AdvOf (PRF_game K q) A].

    That last step is PROVEN, not argued informally, in
    [Sec.lib.games.prf_link] ([prf_distinct_reduce]): this game is a
    REDUCTION to the CANONICAL adaptive game
    ([Sec.lib.games.prf_adaptive]), at the same query cap [q] and with
    no additive loss.  Prefer the adaptive game for a new assumption;
    this variant survives for the fixed derivation loops
    ([Sec.lib.games.prf_derive]) whose queries are distinct by
    construction.

    PRF advantage of A: [AdvOf (PRF_game K q) A]. *)

From Sec.lib Require Import prelude games.thf.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section PRFGame.

Context (K : khf) (q : nat).

Definition FQUERY : nat := 80.

Definition prf_k_loc := mkloc 84 (None : option (kh_K K)).
Definition prf_qs_loc := mkloc 85 ([::] : seq (kh_M K)).

Definition I_PRF :=
  [interface
    [ FQUERY ] : { kh_M K ~> kh_N K }
  ].

Definition PRF_game (b : bool) : game I_PRF :=
  [package [fmap prf_k_loc ; prf_qs_loc ] ;
    [ FQUERY ] : { kh_M K ~> kh_N K } (m) {
      ms ← get prf_qs_loc ;;
      #assert (size ms < q)%N ;;
      #assert (m \notin ms) ;;
      (* Freshness bookkeeping is recorded for BOTH bits, before the
         branch: real and ideal enforce the same query count and
         distinctness (the ideal branch uses neither [m] nor [k]). *)
      #put prf_qs_loc := rcons ms m ;;
      if b then
        ko ← get prf_k_loc ;;
        k ← match ko with
            | Some k => ret k
            | None =>
                k ← kh_dK K ;;
                #put prf_k_loc := Some k ;;
                ret k
            end ;;
        ret (kh_eval K k m)
      else
        y ← kh_dN K ;;
        ret y
    }
  ].

End PRFGame.
