(** * SHRINCS.FXMSS.ConnectHop

    The budget reconciliation seam-closer (P6; PROOF_PLAN.md
    "ReproHop.v status & lessons", consequence 1): with the [q_f]
    FORGE budget threaded through FXMSS/Games.v (counter
    [fx_fcnt_loc] 408) and PRFHop.v, ReproHop's corrected real game
    [G2c] — defined there as "G2f + FORGE budget" while Games.v could
    not be modified — is now LITERALLY the budgeted [G2f]:

      [G2f_G2c : G2f ... q_f b = G2c ... q_f b]   (definitional)

    so the chain

      G0f -PRFf_hop- G1f -PRFmsg_hop- G2f = G2c -Repro_hop- G3c

    composes with no seam.  [G2c_perfect] is the [perfect] reading
    of the equality (what a telescope built from [Adv_perfect_*]
    consumes, if it prefers not to rewrite).

    Both lemmas are stated in ReproHop's section context (the games'
    common parameter list); the proof is [reflexivity] — the two
    [package] elaborations are syntactically identical. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.PRFHop FXMSS.ReproHop.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section FXMSSConnectHop.

Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (w l S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(** The budgeted G2f IS ReproHop's G2c.

    Under the M5 lift both games are assembled by the DIRECTED
    [valid_package_cons] idiom (Games.v / ReproHop.v), so their
    [pack_valid] proof fields are built from DIFFERENT opaque leaf
    [ValidCode] lemmas ([sign2f_body_valid] vs [g2c_sign_body_valid]
    ...) and are no longer convertible — [reflexivity] (which the
    pre-M5 shared-[package]-notation elaboration admitted) no longer
    closes it.  But the [locs] and [pack] (raw-package) fields ARE
    convertible: the oracle bodies coincide up to the section-local
    notation aliases ([Lst]=[fx_st_loc], [flok]=[leaf_okP], [flidx]=
    [lidx], [fxsignx]=[fx_sign_x], ReproHop's [fx_fcnt_loc]=Games.v's,
    ...).  [package_ext] closes the [pack_valid] gap by
    [proof_irrelevance] (already in the development's axiom base:
    [SPropBase.ax_proof_irrel]), leaving two [=1] goals both discharged
    by pointwise convertibility. *)
Lemma G2f_G2c (b : bool) :
  G2f PP N D M R F Tl Hgrind Htree dPP dN dR dD
    w l S_wn c_max h_sf q_s q_h n_max q_f b
  = G2c PP N D M R F Tl Hgrind Htree dPP dN dR dD
      w l S_wn c_max h_sf q_s q_h n_max q_f b.
Proof. apply: package_ext; move=> x; reflexivity. Qed.

(** The [perfect] reading (for telescopes that consume
    [Adv_perfect_l]/[Adv_perfect_r] rather than rewriting). *)
Lemma G2c_perfect (b : bool) :
  perfect (I_G0fL PP N D M R)
    (G2f PP N D M R F Tl Hgrind Htree dPP dN dR dD
       w l S_wn c_max h_sf q_s q_h n_max q_f b)
    (G2c PP N D M R F Tl Hgrind Htree dPP dN dR dD
       w l S_wn c_max h_sf q_s q_h n_max q_f b).
Proof. move=> A VA; rewrite G2f_G2c; exact: Adv_same. Qed.

End FXMSSConnectHop.
