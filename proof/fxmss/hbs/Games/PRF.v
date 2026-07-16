(** * HBS.Games.PRF

    The PRF game pair for an abstract keyed hash function.

    Counterpart: preliminaries.tex def:prf; EasyCrypt
    `KeyedHashFunctionsx2.eca` PRF clones used in SPHINCS_PLUS.ec
    (SKG_PRF / MKG_PRF).  Generalizes
    resources/ssprove/theories/Crypt/examples/PRF.v to arbitrary
    choice types and samplers (and nominal style).

    Real ([true]): a key is sampled lazily; EVAL m = F k m.
    Ideal ([false]): EVAL is a lazily sampled random function.
    Both sides cap the number of EVAL queries at [q].

    PRF advantage of A: [AdvOf (PRF_game F q) A]. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Games.THF.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section PRFGame.

Context (F : khf) (q : nat).

Definition EVAL : nat := 30.
Definition prf_key_loc := mkloc 31 (None : option (kh_K F)).
Definition prf_tab_loc := mkloc 32 (emptym : {fmap (kh_M F) → (kh_N F)}).
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

End PRFGame.
