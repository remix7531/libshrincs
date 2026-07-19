(** * SHRINCS.FXMSS.Leaf2Theorem  (M3 — layer-(ii) assembly + Leaf_hop)

    Assembles the six BANKED per-hop leaf sub-bounds into the concrete
    multi-leaf leaf-hop bound [Leaf_MIW_km_bound], then combines it with
    the layer-(i) equality [LeafKM.Leaf_to_MIW_kmS] into [Leaf_hop] — the
    [G5f -> G6f] statement that WP7 ([FXMSS_secure]) consumes.

    The game ladder (all over the shared [MKMLocs], interface [I_MIW_km]):

      MIW_kmS true --UD(up)-->  G1l   --GRIND->  Glmid1 --COMPRESS->
      Glmid2      --CHAIN-TCR-> Glmid3 --CHAIN-PRE-> G1l' --UD(down)-->
      MIW_kmS false

    yielding the six terms

      Σ_{s<w-2} SM-UD(F)[n_max·l] (B∘R_ud_leaf true s)          (sub_ud_up)
      + STCRP(Hgrind)[n_max]      (B∘R_gr_leaf)                  (sub_gr)
      + SM-TCR(Θl)[n_max]         (B∘R_cp_leaf)                  (sub_cp)
      + SM-TCR(F)[n_max·p_tcr]    (B∘R_ctcr_leaf)                (sub_ctcr)
      + SM-PRE(F)[n_max·l]        (B∘R_cpre_leaf)                (sub_cpre)
      + Σ_{s<w-2} SM-UD(F)[n_max·l] (B∘R_ud_leaf false s).       (sub_ud_down)

    This is the multi-instance mirror of the single-instance WOTS+C bound
    [WOTSC.Theorem.WOTSC_secure]; the proof skeleton is byte-for-byte the
    same telescope (Adv_triangle + lerD, RIGHT-nested accumulator, then
    [rewrite !addrA lexx] to reconcile with the left-nested goal).

    Side conditions (all discharged by the master at instantiation, exactly
    as the finish plan / the M2 [sub_ud] note in Leaf2UD.v anticipates):
    - [hw : 0 < w]     — the re-rooting endpoints of both UD legs
                         (Leaf2UD.[sub_ud_up]/[sub_ud_down]; WOTS+C needs w>=2);
    - [Hdeg : S_wn != l*w.-1] — the CHAIN-PRE virtual-reroot non-degeneracy
                         (Leaf2ChainPRE section [Context (Hdeg ...)] feeding
                         [sub_cpre]);
    - [Hrange : Hgrind < w^l] — the grinding data side condition ([sub_gr]).

    (* FRONTIER: none — every leaf-layer term is a BANKED Qed sub-bound; this
       file is admit-free and adds NO axiom.  See the report at the bottom. *) *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix,-deprecated-coq-env-var".
From HBS Require Import Prelude Math.BinTree Math.Merkle Math.Chain Math.Encoding
  Sig.Scheme Games.THF Games.SMTCR Games.SMPRE Games.STCRP Games.SMUD
  Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Games FixedSumOTS.TCRHop
  FixedSumOTS.UDHop.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames FXMSS.TreeHop
  FXMSS.LeafReduction FXMSS.LeafKM FXMSS.Leaf2Common FXMSS.Leaf2Games
  FXMSS.Leaf2Grind FXMSS.Leaf2Compress FXMSS.Leaf2ChainTCR FXMSS.Leaf2ChainPRE
  FXMSS.Leaf2UD.
From mathcomp Require Import all_ssreflect reals.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section Leaf2Theorem.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** The full shared DATA-ONLY section context (identical to the five
    Leaf2* sub-bound files and to LeafKM). *)
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
Context (n0 : N) (d0 : D).

Local Notation IKM := (@I_MIW_km w l PP N D).
Local Notation IG  := (I_G0fL PP N D M R).

(** Challenge THFs. *)
Local Notation TFn  := (Tf  PP N F dPP dN).
Local Notation TGRn := (Tgr PP D Hgrind dPP dD).
Local Notation TPn  := (Tpk PP N Tl dPP dN).

(** Per-hop challenger collections (CFl_leaf is defined in BOTH ChainTCR
    and ChainPRE — qualify it). *)
Local Notation CGRn := (CGl_leaf PP N D F Tl Hgrind Htree dPP dD).
Local Notation CPn  := (CPl_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation CTn  := (Leaf2ChainTCR.CFl_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation CPRn := (Leaf2ChainPRE.CFl_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation CUDn := (CUD_leaf PP N D F Tl Hgrind Htree dPP dN).
Local Notation genc := (grind_enc D).
Local Notation gprp := (@grind_prp w l S_wn).

(** The multi-leaf reductions. *)
Local Notation RGR := (R_gr_leaf   PP N D F Tl Hgrind Htree dPP dN dD S_wn c_max n_max n0).
Local Notation RCP := (R_cp_leaf   PP N D F Tl Hgrind Htree dPP dN    S_wn c_max n_max n0).
Local Notation RCT := (R_ctcr_leaf PP N D F Tl Hgrind Htree dPP dN    S_wn c_max n_max n0).
Local Notation RPR := (R_cpre_leaf PP N D F Tl Hgrind Htree dPP dN    S_wn c_max n_max n0).
Local Notation RUD b s := (R_ud_leaf PP N D F Tl Hgrind Htree dPP dN  S_wn c_max n_max n0 b s).

(** The endpoint + intermediate games of the ladder. *)
Local Notation MIWkm b := (MIW_kmS PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max b).
Local Notation G1lg    := (G1l     PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation GM1     := (Glmid1  PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation GM2     := (Glmid2  PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation GM3     := (Glmid3  PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).
Local Notation G1lg'   := (G1l'    PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max).

(* ================================================================== *)
(** ** [Leaf_MIW_km_bound]: the assembled multi-leaf leaf-hop bound. *)
(* ================================================================== *)

Theorem Leaf_MIW_km_bound
    (hw : (0 < w)%N)
    (Hdeg : S_wn != (l * w.-1)%N)
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : D * nat), (Hgrind pp' a x < w ^ l)%N)
    (B : nom_package) (VB : ValidPackage (loc B) IKM A_export B) :
  Adv (MIWkm true) (MIWkm false) B
    <= \sum_(0 <= s < w.-2) AdvOf (SMUD_game TFn CUDn (n_max * l)) (B ∘ RUD true s)
     + (AdvOf (STCRP_game TGRn CGRn D genc gprp c_max n_max) (B ∘ RGR)
        + (AdvOf (SMTCR_game TPn CPn n_max) (B ∘ RCP)
           + (AdvOf (SMTCR_game TFn CTn (n_max * p_tcr l w)) (B ∘ RCT)
              + (AdvOf (SMPRE_game TFn CPRn (n_max * l)) (B ∘ RPR)
                 + \sum_(0 <= s < w.-2) AdvOf (SMUD_game TFn CUDn (n_max * l)) (B ∘ RUD false s))))).
Proof.
have hGR := sub_gr   PP N D F Tl Hgrind Htree dPP dN dD S_wn c_max n_max n0 hw Hrange B VB.
have hCP := sub_cp   PP N D F Tl Hgrind Htree dPP dN    S_wn c_max n_max n0 B VB.
have hCT := sub_ctcr PP N D F Tl Hgrind Htree dPP dN    S_wn c_max n_max n0 hw B VB.
have hPR := sub_cpre PP N D F Tl Hgrind Htree dPP dN    S_wn c_max n_max n0 d0 Hdeg hw B VB.
have hUD1 := sub_ud_up   PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max n0 hw B VB.
have hUD0 := sub_ud_down PP N D F Tl Hgrind Htree dPP dN S_wn c_max n_max n0 hw B VB.
(* Front-peel the RIGHT-nested RHS along the ladder
     MIW_kmS true -> G1l -> Glmid1 -> Glmid2 -> Glmid3 -> G1l' -> MIW_kmS false
   with Adv_triangle + lerD.  No [set] and no [!addrA]: [set] does a
   binder-aware traversal that is catastrophically slow on the multi-leaf
   ([n_max]-instance) terms, and the right-nested shape needs no reassociation.
   Each [lerD] peels ONE hop off the head; the four middle equalities close the
   left leg by [lexx], the two UD legs by [hUD1]/[hUD0].  (Mirrors the fast
   [.leaf-scratch/Mid4Assembly.v] middle-four peel, extended at both ends.) *)
eapply le_trans; first exact: (Adv_triangle (G2 := G1lg)).
apply: lerD; first exact: hUD1.
eapply le_trans; first exact: (Adv_triangle (G2 := GM1)).
rewrite hGR; apply: lerD; first exact: lexx.
eapply le_trans; first exact: (Adv_triangle (G2 := GM2)).
rewrite hCP; apply: lerD; first exact: lexx.
eapply le_trans; first exact: (Adv_triangle (G2 := GM3)).
rewrite hCT; apply: lerD; first exact: lexx.
eapply le_trans; first exact: (Adv_triangle (G2 := G1lg')).
rewrite hPR; apply: lerD; first exact: lexx.
exact: hUD0.
Qed.

(* ================================================================== *)
(** ** [Leaf_hop]: the [G5f -> G6f] combine (what WP7 consumes). *)
(* ================================================================== *)

Local Notation G5f' b :=
  (G5f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G6f' b :=
  (G6f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation Rleaf b :=
  (R_leaf_km PP N D M R F Tl Hgrind Htree dN dR dD S_wn c_max h_sf q_s q_h n_max q_f n0 d0 b).

Theorem Leaf_hop
    (Hh : (h_sf <= 64)%N)
    (hw : (0 < w)%N)
    (Hdeg : S_wn != (l * w.-1)%N)
    (Hrange : forall (pp' : PP) (a : adrs_sf) (x : D * nat), (Hgrind pp' a x < w ^ l)%N)
    (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G5f' b) (G6f' b) A
    <= \sum_(0 <= s < w.-2) AdvOf (SMUD_game TFn CUDn (n_max * l)) ((A ∘ Rleaf b) ∘ RUD true s)
     + (AdvOf (STCRP_game TGRn CGRn D genc gprp c_max n_max) ((A ∘ Rleaf b) ∘ RGR)
        + (AdvOf (SMTCR_game TPn CPn n_max) ((A ∘ Rleaf b) ∘ RCP)
           + (AdvOf (SMTCR_game TFn CTn (n_max * p_tcr l w)) ((A ∘ Rleaf b) ∘ RCT)
              + (AdvOf (SMPRE_game TFn CPRn (n_max * l)) ((A ∘ Rleaf b) ∘ RPR)
                 + \sum_(0 <= s < w.-2) AdvOf (SMUD_game TFn CUDn (n_max * l)) ((A ∘ Rleaf b) ∘ RUD false s))))).
Proof.
rewrite (Leaf_to_MIW_kmS PP N D M R F Tl Hgrind Htree dPP dN dR dD
           S_wn c_max h_sf Hh q_s q_h n_max q_f n0 d0 b A VA).
have VB : ValidPackage (loc (A ∘ Rleaf b)%sep) IKM A_export (A ∘ Rleaf b)%sep.
{ eapply valid_sep_link_weak;
    [exact: VA | exact: (pack_valid (Rleaf b)) | exact: fsubmapxx]. }
exact: (Leaf_MIW_km_bound hw Hdeg Hrange (A ∘ Rleaf b)%sep VB).
Qed.

End Leaf2Theorem.
