(** * SHRINCS.WOTSC.ZeroGames

    Game scaffolding and pure forgery analysis for the ZERO-QUERY
    companion bound of WOTS+C (P6 work package "WOTSC_zero";
    theories/SHRINCS/FXMSS/PROOF_PLAN.md, section "Leaf layer", Option
    1's zero-query companion): the adversary sees the public key of
    ONE WOTS+C instance that never signs and must forge against it.
    This is the bound the FXMSS per-anchor hybrid uses for anchors
    whose WOTS instance is never used (the tex's own treatment of
    unused leaves, security.tex F.5/F.7/F.8).

    Delivered here (the hops live in ZeroUDHop.v / ZeroChainHop.v,
    the assembled bound [WOTSC_zero] in ZeroTheorem.v):

    - the zero-query interface [I_KZ] (COMMIT reveals the pk and
      signs NOTHING; KFORGE is plain verification — the log is empty,
      so there is no freshness conjunct);
    - the game pair [G0z] (honest sampling: chains rooted at position
      0, [pk_of] compression) and the post-SM-UD game [G1z] (each
      chain re-rooted at the END: one hidden uniform [u_i] one hash
      step below the chain end, [sg_i = F (chain_adrs i (w-2)) u_i],
      pk = the Theta_l compression of the [sg_i]);
    - the intermediate game [Gzmid] (G1z-real with KFORGE answering
      false exactly on the COMPRESS case);
    - the PURE analysis layer.

    ** The zero-query forgery analysis

    A never-used instance is the one-time instance at the VIRTUAL
    digit vector [nseq l w.-1] (every chain "signed" at its end
    position, nothing revealed): the verifier-side completion
    [complete_ends pp (nseq l w.-1) sg] is [sg] itself ([wzends_id]),
    and [sample_sig_roots] at that digit vector is exactly G1z's
    re-rooted sampling.  A verifying forgery [(mstar, (ystar, cstar))]
    against [pk = Tl pp pk_adrs sg] classifies into TWO cases only:

    1. COMPRESS ([complete_ends pp d* y* != sg]): an SM-TCR(Theta_l)
       collision at the single honest target [(pk_adrs, sg)] — the
       same case 2 as the used instance's classifier
       (Analysis.[wotsc_forgery_classify]), with an empty log.
    2. CHAIN MEET (completions equal): the forged digest [d*] is
       valid, so under the side condition [S_wn != l * w.-1] some
       chain [i] has [d*_i < w.-1] ([zsel]/[zsel_dead]); the forged
       chain walks INTO the honest end [sg_i] ([zends_nth]), and one
       step earlier it is an F-preimage of [sg_i] at chain address
       [(i, w.-2)] ([zmeet_preimage]) — in G1z, [sg_i] is literally
       the SM-PRE oracle's answer at that tweak.

    There is NO chain-collision (SM-TCR(F)) case: the used instance's
    case 3 lives at honest positions [d_i <= k < w-1], an EMPTY range
    at the virtual digit [d_i = w-1] (FXMSS/PROOF_PLAN.md listed an
    SM-TCR(F) term for WOTSC_zero conservatively; the worked-out
    classification shows it is not needed — a strictly smaller
    bound).  And NO grinding (STCRP) case: nothing is signed, so no
    grinding target exists and no grinding assert is performed.

    ** The [S_wn != l * w.-1] side condition (Hdeg)

    The CHAIN MEET case needs a chain with [d*_i < w.-1].  If
    [S_wn = l * (w-1)], the all-(w-1) digit vector is a valid digest
    and a forger reaching it walks zero steps — no preimage, no
    collision: the bound is genuinely false for that degenerate
    parameter choice (e.g. [l = 0], where every verification
    succeeds).  [Hdeg : S_wn != l * w.-1] is a DATA-level side
    condition (an inequality between fixed parameters, not a
    hardness assumption; docs/STYLE.md rule 2), discharged at
    instantiation — real parameter sets have S_wn ~ l(w-1)/2.  It is
    consumed ONLY by the ideal-side PRE lemma ([R_zp_ideal], the
    deadness of the no-such-chain branch), mirroring how [Hrange] is
    consumed only by GrindHop's real side.  Note [Hrange] itself is
    NOT needed here (no GRIND case).

    Locations 370/371 ([zpk_loc]/[zsg_loc], shared by G1z and Gzmid
    the way G0w/G1w/Gmid* share 300-302; [zsg_loc] stores the honest
    chain-end list — never read by G1z's KFORGE, but Gzmid's COMPRESS
    discriminant and the reduction invariants need the honest ends). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games
  FixedSumOTS.Analysis.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games WOTSC.Analysis.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section WOTSCZeroGames.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).

(** Same section context as SHRINCS.WOTSC.Games minus the dummy
    message sampler [dM] (Tgr/STCRP are not involved in the
    zero-query bound). *)
Context (PP N M : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).
Context (dPP : dist PP) (dN : dist N).
Context (S_wn c_max : nat).
Context (zstar istar : nat).

Local Notation WC :=
  (WOTSC PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).
Local Notation FW := (Fw PP N F zstar istar).
Local Notation cf := (chainf PP N F zstar istar).
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation cadrs := (chain_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation gtw := (@encode_adrs l w gadrs).
Local Notation ptw := (@encode_adrs l w padrs).
Local Notation wdigest := (digest_of PP M Hgrind zstar istar).
Local Notation wpk_of := (pk_of PP N F Tl zstar istar).
Local Notation wcends := (complete_ends PP N F zstar istar).
Local Notation wverify :=
  (verify_sig PP N M F Tl Hgrind S_wn zstar istar).
Local Notation vdigest := (@valid_digest w S_wn).

(** The virtual digit vector of a never-used instance: every chain at
    its end position. *)
Local Notation zdig := (nseq l w.-1).

(* ------------------------------------------------------------------ *)
(** ** Pure layer *)

(** Verifier-side completion at the virtual digits is the identity
    (zero steps per chain). *)
Lemma zcends_aux pp st n (ys : seq N) :
  size ys = n ->
  [seq chain (cf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota st n) (zip (nseq n w.-1) ys)] = ys.
Proof.
elim: n st ys => [|n IH] st [|y ys] //= [hsz].
by rewrite subnn chain0 IH.
Qed.

Lemma wzends_id pp (ys : seq N) :
  size ys = l -> wcends pp zdig ys = ys.
Proof. by move=> h; rewrite /complete_ends zcends_aux. Qed.

(** nth-form access to an equality of a completion with the honest
    end list (the CHAIN MEET equation, per chain). *)
Lemma zends_nth pp (ds : seq nat) (ys sg : seq N) (y0 : N) i :
  size ds = l -> size ys = l -> size sg = l -> i < l ->
  wcends pp ds ys = sg ->
  chain (cf pp i) (nth y0 ys i) (nth 0 ds i) (w.-1 - nth 0 ds i)
  = nth y0 sg i.
Proof.
move=> hds hys hsg hi /(congr1 (fun s => nth y0 s i)).
rewrite (wcendsE PP N F zstar istar)
        (ends_from_sig_nth PP N FW l w pp ds ys y0 i hds hys hi).
exact: id.
Qed.

(** CHAIN MEET post-processing: a forged chain reaching the honest
    end [sgi] from a strictly smaller position is, one step earlier,
    an F-preimage of [sgi] at chain address [(i, w-2)]
    ([wotsc_pre_preimage] at the virtual digit [w.-1]). *)
Lemma zmeet_preimage pp i (dst : nat) (yst sgi : N) :
  dst < w.-1 ->
  chain (cf pp i) yst dst (w.-1 - dst) = sgi ->
  F pp (cadrs i w.-2) (chain (cf pp i) yst dst (w.-2 - dst)) = sgi.
Proof.
move=> h1 h2.
exact: (wotsc_pre_preimage PP N F zstar istar pp i w.-1 sgi yst dst h1 h2).
Qed.

(* ------------------------------------------------------------------ *)
(** *** The attacked-chain selector (computable, consumed by the PRE
    reduction's KFORGE) *)

(** First chain whose forged digit is strictly below the virtual
    digit [w.-1]; [None] iff there is none. *)
Definition zsel (ds : seq nat) : option nat :=
  if (find (fun d => (d < w.-1)%N) ds < size ds)%N
  then Some (find (fun d => (d < w.-1)%N) ds)
  else None.

Lemma zselP (ds : seq nat) i :
  zsel ds = Some i -> (i < size ds)%N /\ (nth 0 ds i < w.-1)%N.
Proof.
rewrite /zsel; case: ifP => // hlt [<-]; split; first by [].
have hhas : has (fun d => (d < w.-1)%N) ds by rewrite has_find.
exact: (nth_find 0 hhas).
Qed.

Lemma zsel_none (ds : seq nat) :
  zsel ds = None -> all (fun d => (w.-1 <= d)%N) ds.
Proof.
rewrite /zsel; case: ifP => hlt // _.
have hhas : ~~ has (fun d => (d < w.-1)%N) ds by rewrite has_find hlt.
apply/allP => d hd; rewrite leqNgt.
by apply/negP => hdlt; move/negP: hhas; apply; apply/hasP; exists d.
Qed.

(** Deadness of the no-such-chain branch: a VALID digest with no
    digit below [w.-1] forces [S_wn = l * w.-1] — excluded by the
    [Hdeg] side condition (header).  Uniform in [w] (for [w = 0],
    well-formedness forces the empty digest, covered by the same
    counting). *)
Lemma zsel_dead (ds : seq nat) :
  S_wn != (l * w.-1)%N -> vdigest ds -> size ds = l -> zsel ds = None ->
  False.
Proof.
move=> hdeg /andP[hwf /eqP hsum] hsz hnone.
have hge := zsel_none ds hnone.
have hall : all (pred1 w.-1) ds.
{ apply/allP => d hd.
  have h1 : d < w := allP hwf d hd.
  have h2 : w.-1 <= d := allP hge d hd.
  by rewrite /= eqn_leq h2 andbT -ltnS (ltn_predK h1). }
have hds : ds = nseq (size ds) w.-1 := all_pred1P _ _ hall.
move/eqP: hdeg; apply.
by rewrite -hsum hds sumn_nseq hsz mulnC.
Qed.

(* ------------------------------------------------------------------ *)
(** *** Tweak facts for the compress hop's pin (ZeroChainHop.v) *)

(** The grinding and pk addresses are distinct tweaks (the dummy
    first TQUERY of the compress reduction is fresh). *)
Lemma ptw_notin_gtw : ptw \notin [:: gtw].
Proof.
rewrite in_cons in_nil orbF.
by apply/negP => /eqP /encode_adrs_inj.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The zero-query interface and games *)

Definition I_KZ :=
  [interface
    [ COMMIT ] : { 'unit ~> Pk WC } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool }
  ].

Definition zpk_loc := mkloc 370 (None : option (Pk WC)).
Definition zsg_loc := mkloc 371 (None : option (chList N)).

(** [G0z]: the honest zero-query game.  COMMIT samples PKseed and the
    chain starts, reveals the WOTS+C public key and signs NOTHING;
    KFORGE is plain verification (empty log: no freshness). *)
Definition G0z (b : bool) : game I_KZ :=
  [package [fmap zpk_loc ] ;
    [ COMMIT ] : { 'unit ~> Pk WC } (_) {
      pko ← get zpk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      xs ← sample_seq dN l ;;
      #put zpk_loc := Some (pp, wpk_of pp xs) ;;
      ret (pp, wpk_of pp xs)
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(m, s) {
      if b then
        pk ← getSome zpk_loc ;;
        ret (wverify pk.1 pk.2 m s)
      else
        ret false
    }
  ].

(** [G1z]: the post-SM-UD game.  Per chain ONE hidden uniform one
    hash step below the end ([sample_sig_roots] at the virtual digit
    vector: [sg_i = F pp (chain_adrs i (w-2)) u_i], or [u_i] itself
    for [w <= 1]); pk = the Theta_l compression of the ends [sg]
    (completion at the virtual digits is the identity, [wzends_id]).
    The honest ends are stored in [zsg_loc] for the later hops. *)
Definition G1z (b : bool) : game I_KZ :=
  [package [fmap zpk_loc ; zsg_loc ] ;
    [ COMMIT ] : { 'unit ~> Pk WC } (_) {
      pko ← get zpk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      sg ← sample_sig_roots PP N FW dN pp 0 zdig ;;
      #put zpk_loc := Some (pp, Tl pp padrs sg) ;;
      #put zsg_loc := Some sg ;;
      ret (pp, Tl pp padrs sg)
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(m, s) {
      if b then
        pk ← getSome zpk_loc ;;
        ret (wverify pk.1 pk.2 m s)
      else
        ret false
    }
  ].

(** [Gzmid]: G1z-real with KFORGE answering false exactly on the
    COMPRESS case (forged completion differs from the honest ends;
    within the verified branch the Theta_l coincidence is forced by
    verification, so the single boolean discriminant captures the
    classifier's COMPRESS disjunct).  COMMIT is VERBATIM G1z's. *)
Definition Gzmid : game I_KZ :=
  [package [fmap zpk_loc ; zsg_loc ] ;
    [ COMMIT ] : { 'unit ~> Pk WC } (_) {
      pko ← get zpk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      sg ← sample_sig_roots PP N FW dN pp 0 zdig ;;
      #put zpk_loc := Some (pp, Tl pp padrs sg) ;;
      #put zsg_loc := Some sg ;;
      ret (pp, Tl pp padrs sg)
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(mst, sgst) {
      pk ← getSome zpk_loc ;;
      sgo ← get zsg_loc ;;
      match sgo with
      | Some sg =>
          ret (wverify pk.1 pk.2 mst sgst
               && (wcends pk.1 (wdigest pk.1 mst sgst.2) sgst.1 == sg))
      | None => ret false
      end
    }
  ].

End WOTSCZeroGames.
