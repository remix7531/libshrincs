(** * SHRINCS.FXMSS.FinalHop

    Hop 9, the capstone of the FXMSS EU-CMA chain (PROOF_PLAN.md
    "Final step (9)" / [claim:fxmss-win]; security.tex F.10
    "success probability is zero"):

      [Final_hop : perfect IG (G8f ... true) (G8f ... false)].

    [G8f b = Gkeep keepNone b] (FXMSS/LateGames.v).  After the option-(a)
    reshape (FINAL_ASSEMBLY_NOTES.md) every game's FORGE oracle runs its
    bookkeeping UNCONDITIONALLY and gates ONLY the returned verdict on
    [b]:

      forge_keep_body keepNone b m sg
        = <bookkeeping> ;; ret (if b then fverd keepNone ... else false).

    Since [fverd_keepNone : fverd keepNone ... = false] (LateGames.v),
    BOTH the [b = true] verdict ([if true then false else false]) and the
    [b = false] verdict ([if false then ... else false]) collapse to the
    constant [false].  GEN/SIGN/HASH are b-INDEPENDENT and byte-identical
    between [G8f true] and [G8f false] (same [Gkeep keepNone] skeleton).
    So the two packages are observationally identical: a single [perfect]
    proof over the full-heap-agreement invariant ([heap_ignore emptym])
    closes it, the FORGE verdicts meeting at [false] (no [r_forge_verdict],
    no reduction, no [extractP] — [keepNone] never forces the classifier).

    This is the ONLY hop where the [b = true] and [b = false] members of
    the chain meet; the per-call [q_f] budget asymmetry that broke the
    PRE-reshape [perfect (G8f true) (G8f false)] (FINALHOP_NOTES.md) is now
    symmetric (the [#assert (fc < q_f)] + counter run on BOTH b-sides), so
    it cancels here exactly as the paper's telescoping sum requires (the
    budget is consumed at the Repro hop, not here).

    [Require]s the COMPILED FXMSS.LateGames (mirrors TreeHopProof /
    TCRXHopProof: never recompile the game file). *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.LateGames.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section FXMSSFinalHop.

(** Same DATA section context as FXMSS/TreeHopProof.v (NO assumed
    perfect/Adv premises). *)
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

(* ------------------------------------------------------------------ *)
(** ** Shorthands (LateGames') *)

Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (FxSig N R).
Local Notation LateLocs0 := (LateLocs PP N D M R).
Local Notation keepN := (keepNone N).
Local Notation forge_keep :=
  (forge_keep_body PP N D M R F Tl Hgrind Htree dD w l S_wn h_sf q_f).
Local Notation fverdN :=
  (fverd PP N D M R F Tl Hgrind Htree w l S_wn h_sf).

Local Notation G8 b :=
  (G8f PP N D M R F Tl Hgrind Htree dPP dN dR dD w l S_wn c_max h_sf
     q_s q_h n_max q_f b).

(* ------------------------------------------------------------------ *)
(** ** The full-heap-agreement invariant ([heap_ignore] over the EMPTY
    ignore set = every location forced equal lhs<->rhs), and reflexivity
    of an identical body under it (LeafHop's [heq] / [r_refl_heq]; copied
    here so FinalHop stays standalone).  The two [G8f] members share ALL
    locations and ALL of GEN/SIGN/HASH, so this dispatches those three in
    ONE step each. *)

Local Notation EMPTYL := (emptym : Locations).
Local Notation heq := (heap_ignore EMPTYL).

Lemma heq_get_pre (l0 : Location) : get_pre_cond l0 heq.
Proof. by move=> s0 s1 hh; apply: hh; rewrite domm0 in_fset0. Qed.

Lemma heq_put_pre (l0 : Location) (v : l0) : put_pre_cond l0 v heq.
Proof.
move=> s0 s1 hh l1 hni.
rewrite /get_heap /set_heap !setmE.
by case: (_ == _)%B => //=; apply: hh.
Qed.

Lemma r_refl_heq {B : choiceType} (L : Locations) (c : raw_code B) :
  ValidCode L Game_import c ->
  ⊢ ⦃ λ '(s0, s1), heq (s0, s1) ⦄
     c ≈ c
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ heq (s0, s1) ⦄.
Proof.
move=> hc.
exact: (r_reflexivity_alt heq c hc
          (fun l0 _ => heq_get_pre l0) (fun l0 v _ => heq_put_pre l0 v)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The verdict collapse: at [keepNone] BOTH b-sides return [false],
    so the two FORGE bodies are EQUAL as raw code. *)

Lemma forge_keepNone_const (b : bool) (m : M) (sg : FXSIG) :
  forge_keep keepN b m sg = forge_keep keepN false m sg.
Proof.
rewrite /forge_keep_body.
congr (getr _ _); apply: boolp.funext => fc.
congr (assertD _ _); apply: boolp.funext => _.
congr (getr _ _); apply: boolp.funext => v.
congr (assertD _ _); apply: boolp.funext => vSome.
congr (getr _ _); apply: boolp.funext => lg.
congr (getr _ _); apply: boolp.funext => mp.
congr (getr _ _); apply: boolp.funext => tb.
congr (getr _ _); apply: boolp.funext => sd.
congr (bind _ _); apply: boolp.funext => md.
congr (putr _ _ _).
congr (putr _ _ _).
by rewrite !fverd_keepNone if_same.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Hop 9 *)

Lemma Final_hop : perfect IG (G8 true) (G8 false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ heq).
{ ssprove_invariant. }
simplify_eq_rel arg.
- (* GEN: identical b-independent body *)
  apply: (r_refl_heq LateLocs0); exact _.
- (* SIGN: identical b-independent body *)
  apply: (r_refl_heq LateLocs0); exact _.
- (* HASH: identical b-independent body (emitted before FORGE: the
     interface [I_G0f] writes FXHASH before FXFORGE) *)
  apply: (r_refl_heq LateLocs0); exact _.
- (* FORGE: keepNone collapses both verdicts to [false] -> identical
     bodies, so reflexivity closes it *)
  destruct arg as [m sg].
  rewrite (forge_keepNone_const true m sg).
  apply: (r_refl_heq LateLocs0); exact _.
Qed.

End FXMSSFinalHop.
