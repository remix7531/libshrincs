(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.theorem

    Assembles the ten proved forward-chain hops into a single EU-CMA
    security statement [shrincs_fxmss_secure] for the fixed / counter-schedule
    shrincs_fxmss_scheme signature game [G0f].  The chain (all games over the shared
    interface [I_G0f], with the digest space [D := 'fin d_n.+1] and the
    randomness space [R := 'fin r_n.+1] fixed to the finite prefix-sampler
    families the reprogramming/digest hops require):

      G0f --PRFf--> G1f --PRFmsg--> G2f =(G2f_G2c)= G2c --Repro--> G3c
          --Digest--> G4c --Grind--> G5f --Leaf(6 terms)--> G6f
          --Tree--> G7f --Tcrx--> G8f,   capped by Final_hop (G8f true ~ G8f false).

    Each hop is a same-[b] bound [Adv (Gi b)(Gi+1 b) A <= term_i b], so the
    EU-CMA advantage [Adv (G0f true)(G0f false) A] is bounded by telescoping
    DOWN the b=true chain to [G8f true], crossing to [G8f false] for FREE via
    [Final_hop] (a genuine [perfect], Adv = 0 — F.10 "success probability is
    zero"), then telescoping BACK UP the b=false chain to [G0f false].  Hence
    the bound is [shrincs_fxmss_leg true + shrincs_fxmss_leg false], where [shrincs_fxmss_leg b] is the
    eight-summand single-leg bound

        Adv PRF_f     (A o R_prf b)                         (prf_hop.PRFf_hop)
      + Adv PRF_msg   (A o R_prfm b)                         (prf_hop.PRFmsg_hop)
      + q_s*(q_h+q_s+q_f+q_s.-1)/r_n.+1                      (repro_hop.Repro_hop)
      + n_max*(q_h+q_f)/d_n.+1                               (digest_hop_bound.Digest_hop)
      + n_max*n_ug/d_n.+1                                    (grind_assert_hop.Grind_hop)
      + [6 leaf terms at (A o R_leaf_km b)]                  (leaf2_theorem.Leaf_hop)
      + Adv SM-TCR(tree) (A o R_tree b)                      (tree_hop_proof.Tree_hop)
      + Adv TCRX         (A o R_x b).                        (tcrx_hop_proof.Tcrx_hop)

    The b=true leg matches the paper's telescoping sum (thm:fxmss-main)
    term-for-term; the b=false leg is the mirror the SSProve
    real/ideal-endpoint encoding of the EU-CMA win forces (unavoidable with
    the shared same-[b] hops, since the intermediate games all carry [b] —
    unlike shrincs_fxmss_wots_scheme's b-free middle).

    SCOPE (M5 lift complete): this is the ADVERSARY-CHOSEN-LEAF-ID EU-CMA
    adversary — SIGN takes the pair [M × ('nat × 'nat)] (message and chosen
    leaf id [(z, i)]) over interface [I_G0fL], validates
    the chosen id against the committed tree ([leaf_okP]) and refuses re-used
    ids (used-set [shrincs_fxmss_used_loc], loc 410), signing at slot [lidx st.2.1 zi]
    (security.tex:96-97, "all queried leaf identifiers are pairwise distinct").
    The former FIXED counter-schedule (per-SIGN id = running counter) is the
    special case the lift generalizes; the whole ten-hop chain is re-typed to
    [I_G0fL].  The lift rescaled the per-leaf digest/grind terms [q_s → n_max]
    (the digest is presampled PER-LEAF over [iota 0 n_max], not per-counter-
    query): the Digest term is [n_max*(q_h+q_f)/d_n.+1] and the Grind term is
    [n_max*n_ug/d_n.+1].  The lift adds NO axiom (leaf_okP / used-set are pure,
    the static gate and exchangeability are Prop/def content).

    Side conditions carried as honest premises (none faked premise-free):
    - [Hh : h_sf <= 255] — the address's one-byte height field, matching the
      spec's [FXMSS_HEIGHT = 255] (shrincs.py).  The eight-byte INDEX field
      is not covered by this premise: it is bounded per position, by
      [shrincs_fxmss_wf_shape] on the honest side and by the verifier's
      [shrincs_fxmss_leaf_id_ok] (the spec's
      [leaf_index < 2 ** min(64, leaf_depth)]) on the forgery side;
    - [hw : 0 < w], [Hdeg : S_wn != l*w.-1], [Hrange : Hgrind < w^l]
      — the leaf-hop data/degeneracy conditions (leaf2_theorem.Leaf_hop);
    - [n_ug]/[Hug] — the per-anchor ungrindable-digest count bound feeding the
      grind term (grind_assert_hop.Grind_hop; 0 in the tex's unbounded grinding);
    - the data inhabitants [m0 : M] (PRFmsg pin), [n0 : N] (dead-branch
      hash inhabitant), [d0 : D] (leaf digest inhabitant) — trivially
      discharged where the types are bit-strings.
    The reprogramming-sampler losslessness ([LosslessCode (rp_dPfx d_n)]) is
    DISCHARGED internally (digest_hop_bound_diff.dDu_ll), not a premise. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From mathcomp Require Import all_boot all_order reals.
From Sec.lib Require Import prelude math.bin_tree math.merkle math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme sig.kots games.thf games.prf_adaptive games.smtcr games.smpre games.smud games.stcrp games.tcrx toolkit.sample_seq toolkit.ro_plus toolkit.reprogram.
From Sec.lib Require Import chain.core wots.games wots.tcr_hop wots.ud_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games
  fxmss.prf_hop fxmss.repro_hop fxmss.connect_hop fxmss.digest_hop
  fxmss.digest_hop_bound fxmss.digest_hop_bound_diff fxmss.grind_assert_hop
  fxmss.tree_hop fxmss.leaf_km fxmss.leaf2_ud fxmss.leaf2_grind fxmss.leaf2_compress
  fxmss.leaf2_chain_tcr fxmss.leaf2_chain_pre fxmss.leaf2_theorem
  fxmss.tree_hop_proof fxmss.tcrx_hop_proof fxmss.final_hop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FXMSSTheorem.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** The shared data context.  [D]/[R] are fixed to the finite prefix-sampler
    families the reprogramming (repro) and digest hops require. *)
Context (PP N M Ks Kp : choice_type).
Context (d_n r_n : nat).
Local Notation D := ('fin d_n.+1).
Local Notation R := ('fin r_n.+1).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (PRFf : PP -> Ks -> adrs_sf -> N).
Context (PRFmsg : Kp -> nat * nat -> M -> R).
Context (dPP : dist PP) (dKs : dist Ks) (dKp : dist Kp) (dN : dist N).
Local Notation dD := (rp_dPfx d_n).
Local Notation dR := (rp_dPfx r_n).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).
Context (m0 : M) (n0 : N) (d0 : D).

Local Notation IG := (I_G0fL PP N D M R).

(* ------------------------------------------------------------------ *)
(** ** Game notations along the chain. *)

Local Notation G0F b :=
  (G0f PP N D M R Ks Kp F Tl Hgrind Htree PRFf PRFmsg dPP dKs dKp dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G1F b :=
  (G1f PP N D M R Kp F Tl Hgrind Htree PRFmsg dPP dKp dN dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G2F b :=
  (G2f PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G2C b :=
  (repro_hop.G2c PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G3C b :=
  (repro_hop.G3c PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G4C b :=
  (digest_hop.G4c PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G5F b :=
  (late_games.G5f PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G6F b :=
  (late_games.G6f PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G7F b :=
  (late_games.G7f PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G8F b :=
  (late_games.G8f PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f b).

(* ------------------------------------------------------------------ *)
(** ** Assumption games + reductions of each hop. *)

Local Notation PGF := (PRF_game (Kf PP N Ks PRFf dKs dN) (@q_prf l n_max)).
Local Notation PGM := (PRF_game (Kpm M R Kp PRFmsg dKp dR) (q_prfm q_s)).
Local Notation Rprf b :=
  (prf_hop.R_prf PP N D M R Ks Kp F Tl Hgrind Htree PRFf PRFmsg
     dPP dKs dKp dN dD S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation Rprfm b :=
  (prf_hop.R_prfm PP N D M R Kp F Tl Hgrind Htree PRFmsg
     dPP dKp dN dR dD S_wn c_max h_sf q_s q_h n_max q_f m0 b).

Local Notation SMTg :=
  (SMTCR_game (tree_hop.Th PP N Htree dPP dN)
     (tree_hop.Cth PP N D F Tl Hgrind Htree dPP dN) (n_max - 1)).
Local Notation Rtree b :=
  (tree_hop_proof.R_tree PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f n0 b).

Local Notation TCRXg :=
  (TCRX_game (tcrx_hop_proof.Txc PP N Tl Htree dPP dN)
     (tcrx_hop_proof.Cxc PP N D F Tl Hgrind Htree dPP dN)
     tcrx_hop_proof.paired tcrx_hop_proof.omega (2 * n_max - 1)).
Local Notation Rx b :=
  (tcrx_hop_proof.R_x PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f n0 b).

(** Leaf-hop challenge THFs / collections / reductions (Leaf2Theorem's). *)
Local Notation TFn  := (Tf  PP N F dPP dN).
Local Notation TGRn := (Tgr PP D Hgrind dPP dD).
Local Notation TPn  := (Tpk PP N Tl dPP dN).
Local Notation CUDn := (leaf2_ud.CUD_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation CGRn := (leaf2_grind.CGl_leaf PP N D F Tl Hgrind Htree dPP dD).
Local Notation CPn  := (leaf2_compress.CPl_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation CTn  := (leaf2_chain_tcr.CFl_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation CPRn := (leaf2_chain_pre.CFl_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation gencn := (grind_enc D).
Local Notation gprpn := (@grind_prp w l S_wn).
Local Notation RGRl :=
  (leaf2_grind.R_gr_leaf PP N D F Tl Hgrind Htree dPP dN dD S_wn c_max n_max n0).
Local Notation RCPl :=
  (leaf2_compress.R_cp_leaf PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max n0).
Local Notation RCTl :=
  (leaf2_chain_tcr.R_ctcr_leaf PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max n0).
Local Notation RPRl :=
  (leaf2_chain_pre.R_cpre_leaf PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max n0).
Local Notation RUDl b s :=
  (leaf2_ud.R_ud_leaf PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max n0 b s).
Local Notation Rleaf b :=
  (leaf_km.R_leaf_km PP N D M R F Tl Hgrind Htree dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f n0 d0 b).

(* ------------------------------------------------------------------ *)
(** ** The single-leg bound (right-nested to match the telescope peel). *)

Definition shrincs_fxmss_leg (A : nom_package) (n_ug : nat) (b : bool) : Axioms.R :=
  ( AdvOf PGF (A ∘ Rprf b)
  + ( AdvOf PGM (A ∘ Rprfm b)
    + ( q_s%:R * ((q_h + q_s + q_f + q_s.-1)%:R / r_n.+1%:R)
      + ( n_max%:R * ((q_h + q_f)%:R / d_n.+1%:R)
        + ( n_max%:R * (n_ug%:R / d_n.+1%:R)
          + ( ( \sum_(0 <= s < w.-2)
                  AdvOf (SMUD_game TFn CUDn (n_max * l)) ((A ∘ Rleaf b) ∘ RUDl true s)
              + ( AdvOf (STCRP_game TGRn CGRn D gencn gprpn c_max n_max) ((A ∘ Rleaf b) ∘ RGRl)
                + ( AdvOf (SMTCR_game TPn CPn n_max) ((A ∘ Rleaf b) ∘ RCPl)
                  + ( AdvOf (SMTCR_game TFn CTn (n_max * core.tcr_budget l w)) ((A ∘ Rleaf b) ∘ RCTl)
                    + ( AdvOf (SMPRE_game TFn CPRn (n_max * l)) ((A ∘ Rleaf b) ∘ RPRl)
                      + \sum_(0 <= s < w.-2)
                          AdvOf (SMUD_game TFn CUDn (n_max * l)) ((A ∘ Rleaf b) ∘ RUDl false s) ) ) ) ) )
            + ( AdvOf SMTg (A ∘ Rtree b)
              + AdvOf TCRXg (A ∘ Rx b) ) ) ) ) ) ) )%R.

(* ================================================================== *)
(** ** [shrincs_fxmss_secure]: the end-to-end EU-CMA bound. *)
(* ================================================================== *)

Theorem shrincs_fxmss_secure
    (n_ug : nat)
    (Hug : forall (pp : PP) (zi : nat * nat),
        ((\sum_(y : 'I_d_n.+1)
            (~~ isSome (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp y)
             : nat)) <= n_ug)%N)
    (Hh : (h_sf <= 255)%N)
    (hw : (0 < w)%N)
    (Hdeg : S_wn != (l * w.-1)%N)
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : D * nat), (Hgrind pp' a x < w ^ l)%N)
    (A : nom_package) (VA : ValidPackage (loc A) IG A_export A) :
  (Adv (G0F true) (G0F false) A
     <= shrincs_fxmss_leg A n_ug true + shrincs_fxmss_leg A n_ug false)%R.
Proof.
(* Each leg telescopes DOWN a b-fixed chain from [G0f b] to [G8f b]. *)
have leg : forall b, (Adv (G0F b) (G8F b) A <= shrincs_fxmss_leg A n_ug b)%R.
{ move=> b.
  have hPRFf := prf_hop.PRFf_hop PP N D M R Ks Kp F Tl Hgrind Htree PRFf PRFmsg
                 dPP dKs dKp dN dD S_wn c_max h_sf q_s q_h n_max q_f Hh b A VA.
  have hPRFm := prf_hop.PRFmsg_hop PP N D M R Kp F Tl Hgrind Htree PRFmsg
                 dPP dKp dN dR dD S_wn c_max h_sf q_s q_h n_max q_f m0 b A VA.
  have hCon := connect_hop.G2f_G2c PP N D M R F Tl Hgrind Htree dPP dN dR dD
                 S_wn c_max h_sf q_s q_h n_max q_f b.
  have hRep := repro_hop.Repro_hop PP N D M r_n F Tl Hgrind Htree dPP dN dD
                 (digest_hop_bound_diff.dDu_ll d_n)
                 S_wn c_max h_sf q_s q_h n_max q_f b A VA.
  have hDig := digest_hop_bound.Digest_hop PP N M R d_n F Tl Hgrind Htree dPP dN dR
                 S_wn c_max h_sf q_s q_h n_max q_f b A VA.
  have hGr := grind_assert_hop.Grind_hop PP N M R d_n F Tl Hgrind Htree dPP dN dR
                 S_wn c_max h_sf q_s q_h n_max q_f n_ug Hug b A VA.
  have hLeaf := leaf2_theorem.Leaf_hop PP N D M R F Tl Hgrind Htree dPP dN dR dD
                 S_wn c_max h_sf q_s q_h n_max q_f n0 d0 Hh hw Hdeg Hrange b A VA.
  have hTree := tree_hop_proof.Tree_hop PP N D M R F Tl Hgrind Htree dPP dN dR dD
                 S_wn c_max h_sf Hh q_s q_h n_max q_f n0 b A VA.
  have hTcrx := tcrx_hop_proof.Tcrx_hop PP N D M R F Tl Hgrind Htree dPP dN dR dD
                 S_wn c_max h_sf Hh q_s q_h n_max q_f n0 b A VA.
  rewrite /shrincs_fxmss_leg.
  (* PRFf *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G1F b)).
  rewrite hPRFf; apply: lerD; first exact: lexx.
  (* PRFmsg *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G2F b)).
  rewrite hPRFm; apply: lerD; first exact: lexx.
  (* connect G2f = G2c *)
  rewrite hCon.
  (* Repro *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G3C b)).
  apply: lerD; first exact: hRep.
  (* Digest *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G4C b)).
  apply: lerD; first exact: hDig.
  (* Grind *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G5F b)).
  apply: lerD; first exact: hGr.
  (* Leaf *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G6F b)).
  apply: lerD; first exact: hLeaf.
  (* Tree *)
  eapply le_trans; first exact: (Adv_triangle (G2 := G7F b)).
  rewrite hTree; apply: lerD; first exact: lexx.
  (* Tcrx *)
  by rewrite hTcrx. }
(* Assemble: down b=true, Final_hop cap to G8f false (Adv = 0), up b=false. *)
have hfin := final_hop.Final_hop PP N D M R F Tl Hgrind Htree dPP dN dR dD
               S_wn c_max h_sf q_s q_h n_max q_f A VA.
eapply le_trans; first exact: (Adv_triangle (G2 := G8F true)).
apply: lerD; first exact: (leg true).
eapply le_trans; first exact: (Adv_triangle (G2 := G8F false)).
rewrite hfin GRing.add0r Adv_sym.
exact: (leg false).
Qed.

(** Spec conformance, proof of delivery.  The spec's recommended tree height is
    [FXMSS_HEIGHT = 255] (shrincs.py); the bound above holds THERE, with the
    height premise discharged outright.  The statement is not vacuous at that
    height: the spec's depth-255 UXMSS tree, with all 256 of its WOTS+C
    anchors, is an admissible shape parameter
    ([scheme.shrincs_fxmss_uxmss_at_spec_height]).  Under the retired
    [h_sf <= 64] premise neither was available. *)
Corollary shrincs_fxmss_secure_at_spec_height
    (n_ug : nat)
    (Hug : forall (pp : PP) (zi : nat * nat),
        ((\sum_(y : 'I_d_n.+1)
            (~~ isSome (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2 pp y)
             : nat)) <= n_ug)%N)
    (H255 : h_sf = 255)
    (hw : (0 < w)%N)
    (Hdeg : S_wn != (l * w.-1)%N)
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : D * nat), (Hgrind pp' a x < w ^ l)%N)
    (A : nom_package) (VA : ValidPackage (loc A) IG A_export A) :
  (Adv (G0F true) (G0F false) A
     <= shrincs_fxmss_leg A n_ug true + shrincs_fxmss_leg A n_ug false)%R.
Proof.
apply: (shrincs_fxmss_secure n_ug Hug _ hw Hdeg Hrange A VA).
by rewrite H255.
Qed.

End FXMSSTheorem.
