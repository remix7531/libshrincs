(** * SHRINCS.FXMSS.DigestHopBound

    Assembly of the digest-collision abort hop (G3c -> G4c) of the
    SHRINCS FXMSS proof.  The two halves are proved in the sibling
    files:

    - [DigestHopBound_eq.DIG_eq]   : [Adv (G3c b) (G4m b) A = 0]
      (G3c and the eager-presample game G4m are perfectly
      indistinguishable; a [GF_presample]-style equality with the
      suffix-average coupling and the [g4_lsd_indep] collapse);
    - [DigestHopBound_diff.DIG_diff] : the identical-until-bad bound
      [Adv (G4m b) (G4c b) A <= q_s * ((q_h + q_f) / |D|)].

    [Digest_hop] telescopes them through [G4m] with [Adv_triangle]. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq Toolkit.ROPlus Toolkit.Reprogram.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.PRFHop FXMSS.ReproHop FXMSS.DigestHop
  FXMSS.DigestHopBound_eq FXMSS.DigestHopBound_diff.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FXMSSDigestBound.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).
Context (PP N M R : choice_type) (d_n : nat).
Context (F : PP -> adrs_sf -> N -> N) (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> (chFin d_n.+1) * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R).
Context (S_wn c_max h_sf q_s q_h n_max q_f : nat).
Local Notation Dfin := (chFin d_n.+1).
Local Notation dDu := (rp_dPfx d_n).
Local Notation G3C b := (ReproHop.G3c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4M b := (G4m PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4C b := (G4c PP N Dfin M R F Tl Hgrind Htree dPP dN dR dDu S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation IG := (I_G0fL PP N Dfin M R).

(** The digest-collision abort hop.  [eps_coll = n_max * (q_h + q_f) / |D|].
    M5: the SIGN oracle is now the adversary-chosen-leaf-id interface
    [I_G0fL], and the per-leaf digest presample rescales the budget from
    [q_s] to [n_max] (the number of tree leaves). *)
Theorem Digest_hop (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) (I_G0fL PP N Dfin M R) A_export A) :
  (Adv (G3C b) (G4C b) A <= n_max%:R * ((q_h + q_f)%:R / d_n.+1%:R) :> Axioms.R)%R.
Proof.
apply: le_trans (@Adv_triangle _ (G4M b) _ A) _.
rewrite (DIG_eq PP N M R d_n F Tl Hgrind Htree dPP dN dR S_wn c_max h_sf
           q_s q_h n_max q_f b A VA).
rewrite GRing.add0r.
exact: (DIG_diff PP N M R d_n F Tl Hgrind Htree dPP dN dR S_wn c_max h_sf
           q_s q_h n_max q_f b A VA).
Qed.

End FXMSSDigestBound.
