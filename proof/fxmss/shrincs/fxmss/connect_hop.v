(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.connect_hop

    The budget-reconciliation connection between [G2f] and [G2c]. The
    [q_f] FORGE budget is threaded through [fxmss.games] and
    [fxmss.prf_hop], making [G2c] extensionally equal to budgeted [G2f]:

      [G2f_G2c : G2f ... q_f b = G2c ... q_f b]   (definitional)

    Therefore the chain

      G0f -PRFf_hop- G1f -PRFmsg_hop- G2f = G2c -Repro_hop- G3c

    composes with no seam.  [G2c_perfect] is the [perfect] reading
    of the equality (what a telescope built from [Adv_perfect_*]
    consumes, if it prefers not to rewrite).

    Both lemmas are stated in the shared game context. [package_ext]
    resolves the irrelevant [ValidPackage] proof fields. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import prelude math.bin_tree math.merkle sig.scheme
  games.thf toolkit.sample_seq.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.prf_hop fxmss.repro_hop.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section FXMSSConnectHop.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(** The budgeted G2f IS ReproHop's G2c.

    Under the M5 lift both games are assembled by the DIRECTED
    [valid_package_cons] idiom (Games.v / repro_hop.v), so their
    [pack_valid] proof fields are built from DIFFERENT opaque leaf
    [ValidCode] lemmas ([sign2f_body_valid] vs [g2c_sign_body_valid]
    ...) and are no longer convertible — [reflexivity] (which the
    pre-M5 shared-[package]-notation elaboration admitted) no longer
    closes it.  But the [locs] and [pack] (raw-package) fields ARE
    convertible: the oracle bodies coincide up to the section-local
    notation aliases ([Lst]=[shrincs_fxmss_st_loc], [flok]=[leaf_okP], [flidx]=
    [lidx], [fxsignx]=[shrincs_fxmss_sign_x], ReproHop's [shrincs_fxmss_fcnt_loc]=Games.v's,
    ...).  [package_ext] closes the [pack_valid] gap by
    [proof_irrelevance] (already in the development's axiom base:
    [SPropBase.ax_proof_irrel]), leaving two [=1] goals both discharged
    by pointwise convertibility. *)
Lemma G2f_G2c (b : bool) :
  G2f PP N D M R F Tl Hgrind Htree dPP dN dR dD
    S_wn c_max h_sf q_s q_h n_max q_f b
  = G2c PP N D M R F Tl Hgrind Htree dPP dN dR dD
      S_wn c_max h_sf q_s q_h n_max q_f b.
Proof. apply: package_ext; move=> x; reflexivity. Qed.

(** The [perfect] reading (for telescopes that consume
    [Adv_perfect_l]/[Adv_perfect_r] rather than rewriting). *)
Lemma G2c_perfect (b : bool) :
  perfect (I_G0fL PP N D M R)
    (G2f PP N D M R F Tl Hgrind Htree dPP dN dR dD
       S_wn c_max h_sf q_s q_h n_max q_f b)
    (G2c PP N D M R F Tl Hgrind Htree dPP dN dR dD
       S_wn c_max h_sf q_s q_h n_max q_f b).
Proof. move=> A VA; rewrite G2f_G2c; exact: Adv_same. Qed.

End FXMSSConnectHop.
