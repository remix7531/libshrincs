(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Sec.lib.toolkit.ro_plus

    Random oracle with adaptive reprogramming, as a bool-indexed game
    pair.

    Counterpart: resources/SHRINCS-security-specification/
    reprogramming.tex, Definition "Adaptive reprogramming"
    (def:QROM reprogramming, after [AC:GHHM21]), classical access.
    The classical bound (lemma:ROM reprogramming) is proved in
    Sec.lib.toolkit.reprogram.

    ** The experiment

    The paper's [Repro_b]: a random oracle
    [O : X1 × X2 -> Y] plus a reprogramming oracle that, on the
    adversary's suffix [x2], samples a fresh prefix [x1 <- X1] and a
    fresh output [y <- Y], reprograms [O_1(x1, x2) := y] and returns
    [x1].  The adversary talks to [O_b]; in the [b = false] world the
    oracle is never reprogrammed.  Crucially, the freshly sampled
    prefix is returned AFTER any potential earlier query, so the
    adversary can only detect the resampling if it managed to query
    the (still unpredictable) prefix beforehand.

    ** Game encoding (paper name on the left)

    - [O_b]      -> [QUERY : { Pfx × X ~> R }], a lazily sampled
      random oracle held in a [chMap] location, capped at [qh]
      queries by a counter ([#assert] aborts past the cap).
    - [Reprogram] -> [REPRO : { X ~> Pfx }], capped at [qp] queries;
      it always samples and returns the fresh prefix [r <- dPfx];
      only the [b = true] game additionally samples [y <- dR] and
      overwrites the map at [(r, x)].
    - [X1/X2/Y]  -> [Pfx]/[X]/[R] with samplers [dPfx]/[dR]
      (the paper samples uniformly; the games are stated for any
      sampler, the bound in Reprogram.v for the uniform [dPfx]).

    The reprogramming distinguishing advantage of [A] is
    [AdvOf (RO_repro ...) A]; it instantiates the paper's
    [Succ^Repro_{R,q}(A)] with [R := qp], [q := qh].

    Micro-test at the end of the file (docs/STYLE.md rule 12). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

Section ROPlus.

Context (Pfx X R : choice_type).
Context (dPfx : dist Pfx) (dR : dist R).
Context (qh qp : nat).

Definition QUERY : nat := 60.
Definition REPRO : nat := 61.

Definition ro_map_loc : Location :=
  mkloc 62 (emptym : chMap (Pfx × X) R).
Definition ro_qcnt_loc : Location := mkloc 63 (0 : 'nat).
(* id 78, not 64: 64 collides with Sec.lib.games.smud's [ud_pp_loc] at the
   FXMSS instantiation (see proof/LOCATIONS.md). *)
Definition ro_rcnt_loc : Location := mkloc 78 (0 : 'nat).

Definition I_RO :=
  [interface
    [ QUERY ] : { Pfx × X ~> R } ;
    [ REPRO ] : { X ~> Pfx }
  ].

Definition RO_repro (b : bool) : game I_RO :=
  [package [fmap ro_map_loc ; ro_qcnt_loc ; ro_rcnt_loc ] ;
    [ QUERY ] : { Pfx × X ~> R } (q) {
      qc ← get ro_qcnt_loc ;;
      #assert (qc < qh)%N ;;
      #put ro_qcnt_loc := qc.+1 ;;
      m ← get ro_map_loc ;;
      match getm m q with
      | Some y => ret y
      | None =>
          y ← dR ;;
          #put ro_map_loc := setm m q y ;;
          ret y
      end
    } ;
    [ REPRO ] : { X ~> Pfx } (x) {
      rc ← get ro_rcnt_loc ;;
      #assert (rc < qp)%N ;;
      #put ro_rcnt_loc := rc.+1 ;;
      r ← dPfx ;;
      if b then
        m ← get ro_map_loc ;;
        y ← dR ;;
        #put ro_map_loc := setm m (r, x) y ;;
        ret r
      else
        ret r
    }
  ].

End ROPlus.

(* Micro-test: the game pair validates on concrete parameters and a
   toy adversary (one QUERY, one REPRO, then a detection re-QUERY)
   composes with it. *)
Module ROPlusTest.

Definition d3 : dist (chFin 3) := {code x ← sample uniform 3 ;; ret x}.
Definition dB : dist 'bool := {code x ← sample uniform 2 ;; ret (odd x)}.

Definition test_game (b : bool) : game (I_RO (chFin 3) 'nat 'bool) :=
  RO_repro (chFin 3) 'nat 'bool d3 dB 5 1 b.

Definition test_adv : package (I_RO (chFin 3) 'nat 'bool) A_export :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> 'bool } (_) {
      y ← call [ QUERY ] : { chFin 3 × 'nat ~> 'bool } (gfin 0, 7%N) ;;
      r ← call [ REPRO ] : { 'nat ~> chFin 3 } 7%N ;;
      y' ← call [ QUERY ] : { chFin 3 × 'nat ~> 'bool } (r, 7%N) ;;
      ret (xorb y y')
    }
  ].

Lemma test_valid (b : bool) :
  ValidPackage (loc (test_adv ∘ test_game b)%sep)
    Game_import A_export (test_adv ∘ test_game b)%sep.
Proof. ssprove_valid. Qed.

End ROPlusTest.
