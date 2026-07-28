(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.lib.games.prf_adaptive

    Adaptive PRF game for an abstract keyed hash function.  The real
    oracle lazily samples one key and evaluates the keyed function.  The
    ideal oracle implements a lazy random function: repeated inputs return
    the same table entry, while new inputs receive independent samples.
    Both sides enforce the same total query bound.

    Unlike [Sec.lib.games.prf], this game permits repeated and adaptively
    selected inputs.  The distinct-query game remains useful for fixed
    derivation loops; this variant is the reusable assumption needed by
    FXMSS key generation. *)

From Sec.lib Require Import prelude games.thf.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section PRFAdaptiveGame.

Context (F : khf) (q : nat).

Definition EVAL : nat := 30.
Definition prf_key_loc := mkloc 31 (None : option (kh_K F)).
Definition prf_tab_loc := mkloc 32 (emptym : {fmap (kh_M F) -> kh_N F}).
Definition prf_cnt_loc := mkloc 33 (0 : nat).

Definition I_PRF := [interface [ EVAL ] : { kh_M F ~> kh_N F } ].

Definition PRF_game (b : bool) : game I_PRF :=
  [package [fmap prf_key_loc ; prf_tab_loc ; prf_cnt_loc ] ;
    [ EVAL ] : { kh_M F ~> kh_N F } (m) {
      cnt ← get prf_cnt_loc ;;
      #assert (cnt < q)%N ;;
      #put prf_cnt_loc := cnt.+1 ;;
      if b then
        ko ← get prf_key_loc ;;
        match ko with
        | Some k => ret (kh_eval F k m)
        | None =>
            k ← kh_dK F ;;
            #put prf_key_loc := Some k ;;
            ret (kh_eval F k m)
        end
      else
        t ← get prf_tab_loc ;;
        match getm t m with
        | Some y => ret y
        | None =>
            y ← kh_dN F ;;
            #put prf_tab_loc := setm t m y ;;
            ret y
        end
    }
  ].

End PRFAdaptiveGame.
