(** * HBS.Examples.FixedSumOTS.Analysis

    The PURE forgery-analysis layer of the FixedSumOTS security proof
    (PROOF_PLAN.md, step "G1 → SM-TCR + SM-PRE split"), plus the
    valid-commit game pair [G0v]/[G1v] (definitions only; the hops
    live in UDHop.v / TCRPREHop.v).

    Part 1 (Section [FixedSumOTSAnalysis], no samplers, no packages):
    the post-UD game G1v reveals, for each chain [i] with digit
    [d_i := nth 0 m i], a signature digit
      [σ_i = if d_i == 0 then u_i else F pp (i, d_i - 1) u_i]
    ([sample_sig_roots]'s pure shape) and the public end
      [end_i = chain (cf pp i) σ_i d_i (w.-1 - d_i)]
    ([ends_from_sig]).  A forgery on [m* != m] yields (via
    [forged_digit_lt]) a chain [i] with [d*_i < d_i], on which
    [forgery_cases] (a restatement of [Chain.chain_extractP] for this
    instantiation) classifies the forged value into the TCR case
    (collision at a committed position [k >= d_i] against the honest
    chain value, which the reduction recomputes from [σ_i]) or the
    PRE case (the forged chain meets [σ_i]; [forgery_pre_preimage]
    turns the meet into the preimage handed to SM-PRE's PCHECK).
    [forgery_classify] composes the whole pipeline for a verifying
    forgery against an [ends_from_sig] key.

    Part 1 also fixes the TCR reduction's target bookkeeping: the
    reduction commits, for chain [i = 0..l-1] and position
    [k = d_i..w.-2] (in lexicographic order), the target
    [((i, k), honest chain value at k)] through TQUERY; [tcr_targets]
    is that committed list, [tcr_index] the position of target
    [(i, k)] in it.  [tcr_targets_nth] / [tcr_index_lt] /
    [size_tcr_targets] / [size_tcr_targets_leq] /
    [tcr_targets_tweaks_uniq] are exactly the facts the package-level
    reduction needs to discharge the TQUERY asserts (count below the
    cap [l * w], all tweaks distinct) and to map [ChainColl]'s [(i,k)]
    to the index submitted to CHECK.

    Part 2 (Section [FixedSumOTSVGames]): [G0v]/[G1v], the
    valid-commit variants of Games.v's [G0flat]/[G1] (the theorem is
    stated for these per PROOF_PLAN.md's sign-refusal decision): COMMIT
    additionally [#assert]s [valid_msg m], so the refusal branch
    aborts the experiment and both games sign unconditionally
    afterwards.  Fresh locations 210/211, shared between G0v and G1v
    (the two are never composed; sharing keeps the UD-hybrid
    invariants small, as for G0flat/G1). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Math.Chain Math.Encoding Sig.Scheme Sig.KOTS
  Games.THF Toolkit.SampleSeq.
From HBS.Examples Require Import FixedSumOTS.Scheme FixedSumOTS.Games.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic seq facts (missing from MathComp's seq.v) *)

(** [unzip1] distributes over [++] (it is a [map]). *)
Lemma unzip1_cat (X Y : Type) (s t : seq (X * Y)) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
Proof. exact: map_cat. Qed.

(** A sum of elements all below [n] is below [size * n]. *)
Lemma sumn_all_leq n (s : seq nat) :
  all (fun x => x <= n) s -> sumn s <= size s * n.
Proof.
elim: s => [//|a s IH] /= /andP[ha hs].
rewrite mulSn; exact: leq_add ha (IH hs).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Part 1: pure forgery analysis *)

Section FixedSumOTSAnalysis.

(** Same context as FixedSumOTS.Scheme, minus the samplers (this part
    is pure; docs/STYLE.md rule 5 in spirit — the file needs SSProve
    only for Part 2). *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (l w tsum : nat).

(** Chain step of chain [i] (HBS.Math.Chain position convention). *)
Local Notation cf := (chainf PP N F).

(* ------------------------------------------------------------------ *)
(** *** Digit-vector selectors *)

(** Every digit of a valid message is below [w] (gives the [d < w]
    side condition of [forgery_cases]). *)
Lemma valid_msg_digit (m : seq nat) i :
  valid_msg l w tsum m -> i < l -> nth 0 m i < w.
Proof.
case/and3P=> /eqP hm hw _ hi.
have /(all_nthP 0) hnth := hw.
by have := hnth i; rewrite hm => /(_ hi).
Qed.

(** THE message-level selector (wrap of [Encoding.eq_sumn_exists_lt],
    the fixed digit sum playing the role of the WOTS+ checksum): two
    distinct valid messages give a chain index where the FORGED digit
    is strictly below the signed one — the only place a forger cannot
    walk forward from revealed values.  Consumed with [m] the signed
    and [mstar] the forged message. *)
Lemma forged_digit_lt (m mstar : seq nat) :
  valid_msg l w tsum m -> valid_msg l w tsum mstar -> mstar != m ->
  exists2 i, i < l & nth 0 mstar i < nth 0 m i.
Proof.
case/and3P=> /eqP hm _ /eqP hs.
case/and3P=> /eqP hm' _ /eqP hs' hne.
have hsz : size mstar = size m by rewrite hm hm'.
have hsum : sumn mstar = sumn m by rewrite hs hs'.
have hneq : mstar <> m by apply/eqP.
have [i hi hlt] := eq_sumn_exists_lt hsz hsum hneq.
by exists i => //; rewrite -hm'.
Qed.

(* ------------------------------------------------------------------ *)
(** *** The per-chain forgery classifier *)

(** THE classifier (restatement of [Chain.chain_extractP] with
    [y := sigstar], [j := dstar], [z := sigi], [i := d], [e := w.-1]):
    on the selected chain [i], the signer revealed [sigi] at position
    [d] and published [end_i = chain sigi d (w.-1 - d)]; the forger
    claims [sigstar] at the strictly smaller position [dstar] and
    verification forces the same endpoint.  Then
    [chain_extract (cf pp i) sigstar dstar sigi d w.-1] returns
    - [ChainColl k u v] with [d <= k < w.-1]: [v] is the HONEST chain
      value at position [k], recomputable from [sigi] — exactly the
      input of the TCR target the reduction committed at tweak
      [(i, k)] — and [u != v] with [F pp (i,k) u = F pp (i,k) v]:
      [(tcr_index m i k, u)] wins SM-TCR's CHECK;
    - [ChainMeet]: the forged chain reaches [sigi] at position [d]
      (note [0 < d] since [dstar < d]); [forgery_pre_preimage] below
      extracts the SM-PRE witness.
    ([chain_extract_ok]'s [u]-component [u = chain sigstar dstar
    (k - dstar)] is dropped: the reduction submits [u] itself.) *)
Lemma forgery_cases pp i d (sigi : N) dstar (sigstar : N) :
  dstar < d -> d < w ->
  chain (cf pp i) sigstar dstar (w.-1 - dstar)
    = chain (cf pp i) sigi d (w.-1 - d) ->
  match chain_extract (cf pp i) sigstar dstar sigi d w.-1 with
  | ChainColl k u v =>
      [/\ d <= k < w.-1,
          v = chain (cf pp i) sigi d (k - d),
          u != v
        & F pp (i, k) u = F pp (i, k) v]
  | ChainMeet => chain (cf pp i) sigstar dstar (d - dstar) = sigi
  end.
Proof.
move=> hdd hdw heq.
have hji : dstar <= d := ltnW hdd.
have hie : d <= w.-1 by rewrite -ltnS (ltn_predK hdw).
have := chain_extractP hji hie heq.
rewrite /chain_extract_ok.
case: (chain_extract _ _ _ _ _ _) => [k u v|] //.
by case=> hk _ hv hne hcol; split.
Qed.

(** PRE-case post-processing: if the forged chain meets [sigi] at
    position [d] then its value ONE step earlier (recomputable by the
    reduction from the forged signature) is an [F]-preimage of [sigi]
    at tweak [(i, d.-1)].  In G1v, [sigi = F pp (i, d.-1) u_i] with
    [u_i] hidden uniform — i.e. [sigi] is literally the SM-PRE
    oracle's answer at tweak [(i, d.-1)], so this is the message that
    wins PCHECK. *)
Lemma forgery_pre_preimage pp i d (sigi sigstar : N) dstar :
  dstar < d ->
  chain (cf pp i) sigstar dstar (d - dstar) = sigi ->
  F pp (i, d.-1) (chain (cf pp i) sigstar dstar (d.-1 - dstar)) = sigi.
Proof.
move=> hdd hmeet.
have hd1 : dstar <= d.-1 by rewrite -ltnS (ltn_predK hdd).
have hn : d - dstar = (d.-1 - dstar).+1.
  by rewrite -subSn // (ltn_predK hdd).
by move: hmeet; rewrite hn chain_rcons subnKC.
Qed.

(* ------------------------------------------------------------------ *)
(** *** nth-form access to the verification equation

    [verify_sig] is one [all] over a zip (Scheme.v); the analysis
    needs its per-chain content pointwise.  Both lemmas are stated
    with an explicit default [y0 : N] (the choice_type [N] has no
    canonical inhabitant); the indices are in range, so the default
    is irrelevant. *)

(** A passing verification forces, at every chain [i < l], the forged
    completion to hit the public end. *)
Lemma verify_sig_nth pp (ends : seq N) (m : seq nat) (sg : seq N)
    (y0 : N) i :
  verify_sig PP N F l w tsum pp ends m sg ->
  size ends = l -> i < l ->
  chain (cf pp i) (nth y0 sg i) (nth 0 m i) (w.-1 - nth 0 m i)
  = nth y0 ends i.
Proof.
case/and3P=> /and3P[/eqP hm _ _] /eqP hsg hall hends hi.
have hzs : size (zip (iota 0 l) (zip m (zip sg ends))) = l.
  by rewrite !size_zip size_iota hm hsg hends !minnn.
move/(all_nthP (0, (0, (y0, y0)))): hall => /(_ i).
rewrite hzs => /(_ hi).
rewrite nth_zip ?size_iota ?size_zip ?hm ?hsg ?hends ?minnn //.
rewrite nth_zip ?size_zip ?hm ?hsg ?hends ?minnn //.
rewrite nth_zip ?hsg ?hends //=.
by rewrite /chain_check nth_iota // add0n => /eqP.
Qed.

(** Size of an [ends_from_sig] public key (used to discharge
    [verify_sig_nth]'s [size ends = l]). *)
Lemma size_ends_from_sig pp (m : seq nat) (sg : seq N) :
  size m = l -> size sg = l ->
  size (ends_from_sig PP N F l w pp m sg) = l.
Proof.
move=> hm hsg.
by rewrite /ends_from_sig size_map !size_zip size_iota hm hsg !minnn.
Qed.

(** The [i]-th [ends_from_sig] end in chain form. *)
Lemma ends_from_sig_nth pp (m : seq nat) (sg : seq N) (y0 : N) i :
  size m = l -> size sg = l -> i < l ->
  nth y0 (ends_from_sig PP N F l w pp m sg) i
  = chain (cf pp i) (nth y0 sg i) (nth 0 m i) (w.-1 - nth 0 m i).
Proof.
move=> hm hsg hi.
rewrite /ends_from_sig (nth_map (0, (0, y0))) ?size_zip ?size_iota
        ?hm ?hsg ?minnn //.
rewrite nth_zip ?size_iota ?size_zip ?hm ?hsg ?minnn //.
rewrite nth_zip ?hm ?hsg //=.
by rewrite nth_iota // add0n.
Qed.

(** THE composed forgery pipeline, packaged for the reduction: a
    verifying forgery [(mstar, sgstar)] against the G1v key
    [ends_from_sig pp m sg] on a fresh message yields a chain [i]
    with a strictly smaller forged digit on which [forgery_cases]
    classifies the forged signature value.  Everything is phrased in
    [nth] so the package layer never re-derives zip arithmetic. *)
Lemma forgery_classify pp (m mstar : seq nat) (sg sgstar : seq N)
    (y0 : N) :
  valid_msg l w tsum m -> size sg = l ->
  verify_sig PP N F l w tsum pp (ends_from_sig PP N F l w pp m sg)
    mstar sgstar ->
  mstar != m ->
  exists2 i, i < l &
    [/\ nth 0 mstar i < nth 0 m i, nth 0 m i < w &
        match chain_extract (cf pp i) (nth y0 sgstar i) (nth 0 mstar i)
                            (nth y0 sg i) (nth 0 m i) w.-1 with
        | ChainColl k u v =>
            [/\ nth 0 m i <= k < w.-1,
                v = chain (cf pp i) (nth y0 sg i) (nth 0 m i)
                          (k - nth 0 m i),
                u != v
              & F pp (i, k) u = F pp (i, k) v]
        | ChainMeet =>
            chain (cf pp i) (nth y0 sgstar i) (nth 0 mstar i)
                  (nth 0 m i - nth 0 mstar i) = nth y0 sg i
        end].
Proof.
move=> hvm hsg hver hne.
have hvm' : valid_msg l w tsum mstar by case/and3P: hver.
have hm : size m = l by case/and3P: hvm => /eqP.
have [i hi hlt] := forged_digit_lt _ _ hvm hvm' hne.
exists i => //.
have hdw : nth 0 m i < w := valid_msg_digit _ _ hvm hi.
have hends := size_ends_from_sig pp _ _ hm hsg.
have h1 := verify_sig_nth _ _ _ _ y0 _ hver hends hi.
rewrite (ends_from_sig_nth pp _ _ y0 _ hm hsg hi) in h1.
split=> //.
exact: (forgery_cases _ _ _ _ _ _ hlt hdw h1).
Qed.

(* ------------------------------------------------------------------ *)
(** *** Target bookkeeping for the TCR reduction

    The reduction commits one TQUERY per (chain, position) pair, in
    lexicographic order (chain [i] ascending, position [k] ascending
    from the signed digit [d_i] to [w.-2]): the [j]-th TQUERY lands at
    fmap key [j] in [SMTCR_game]'s [tcr_tgts_loc], so positions in
    [tcr_targets] ARE the CHECK indices. *)

(** Targets of one chain: position [k] runs over
    [iota d_i (w.-1 - d_i)] = [d_i, ..., w.-2]; the input committed at
    [(i, k)] is the honest chain value at [k], walked from the
    signature digit. *)
Definition tcr_chain (pp : PP) (i d : nat) (sg : N) :
    seq ((nat * nat) * N) :=
  [seq ((i, k), chain (cf pp i) sg d (k - d)) | k <- iota d (w.-1 - d)].

(** The full committed target list ((tweak, input) pairs; the tweak
    type is the carrier of ['nat × 'nat]). *)
Definition tcr_targets (pp : PP) (m : seq nat) (sigs : seq N) :
    seq ((nat * nat) * N) :=
  flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
          | q <- zip (iota 0 l) (zip m sigs)].

(** Position of target [(i, k)] in [tcr_targets]: all targets of the
    earlier chains ([w.-1 - d_j] each), plus the offset inside chain
    [i]. *)
Definition tcr_index (m : seq nat) (i k : nat) : nat :=
  sumn [seq w.-1 - d | d <- take i m] + (k - nth 0 m i).

(** Auxiliary forms, generalized over the starting chain index [st]
    so that induction on the digit list goes through (same device as
    [Scheme.all_chain_checks]). *)

Lemma size_tcr_targets_from pp st (ds : seq nat) (ss : seq N) :
  size ss = size ds ->
  size (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                | q <- zip (iota st (size ds)) (zip ds ss)])
  = sumn [seq w.-1 - d | d <- ds].
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //= [hss].
by rewrite size_cat size_map size_iota (IH st.+1 ss hss).
Qed.

Lemma tcr_targets_from_nth pp st (ds : seq nat) (ss : seq N) i k
    (x0 : (nat * nat) * N) (y0 : N) :
  size ss = size ds -> i < size ds -> nth 0 ds i <= k < w.-1 ->
  nth x0
    (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
             | q <- zip (iota st (size ds)) (zip ds ss)])
    (sumn [seq w.-1 - d | d <- take i ds] + (k - nth 0 ds i))
  = (((st + i)%N, k),
     chain (cf pp (st + i)) (nth y0 ss i) (nth 0 ds i)
           (k - nth 0 ds i)).
Proof.
elim: ds st ss i => [|d ds IH] st ss i hss hi hk.
  by rewrite ltn0 in hi.
case: ss hss => [|s ss] //= [hss]; case: i hi hk => [|i] hi hk.
- (* i = 0: the target sits in this chain's block *)
  move: hk => /andP[hdk hkw].
  have hdw : d < w.-1 := leq_ltn_trans hdk hkw.
  have hlt : k - d < w.-1 - d := ltn_sub2r hdw hkw.
  have hsz : k - d < size (iota d (w.-1 - d)) by rewrite size_iota.
  rewrite /= add0n addn0 nth_cat size_map size_iota hlt (nth_map 0) //.
  by rewrite nth_iota // subnKC.
- (* i.+1: skip this chain's [w.-1 - d] targets, recurse at st.+1 *)
  rewrite /= -addnA nth_cat size_map size_iota ltnNge leq_addr /= addKn.
  by rewrite (IH st.+1 ss i hss hi hk) addSnnS.
Qed.

(** All tweaks produced from starting chain [st] have first component
    at least [st] (cross-chain disjointness for uniqueness). *)
Lemma tcr_tweaks_from_ge pp st (ds : seq nat) (ss : seq N) :
  all (fun t : nat * nat => st <= t.1)
      (unzip1 (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                       | q <- zip (iota st (size ds)) (zip ds ss)])).
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //=.
rewrite unzip1_cat all_cat; apply/andP; split.
- rewrite /tcr_chain /unzip1 -map_comp all_map.
  by apply/allP => k _ /=.
- apply/allP => t ht.
  have /allP/(_ t ht) /= hge := IH st.+1 ss.
  exact: ltnW.
Qed.

Lemma tcr_tweaks_from_uniq pp st (ds : seq nat) (ss : seq N) :
  uniq (unzip1 (flatten [seq tcr_chain pp q.1 q.2.1 q.2.2
                        | q <- zip (iota st (size ds)) (zip ds ss)])).
Proof.
elim: ds st ss => [|d ds IH] st [|s ss] //=.
rewrite unzip1_cat cat_uniq; apply/and3P; split.
- (* within one chain: positions are an iota *)
  rewrite /tcr_chain /unzip1 -map_comp map_inj_uniq ?iota_uniq //.
  by move=> k1 k2 /(congr1 (fun p : nat * nat => p.2)) e; exact: e.
- (* across chains: later chains have first component > st *)
  apply/hasPn => t ht /=.
  have /allP/(_ t ht) /= hge := tcr_tweaks_from_ge pp st.+1 ds ss.
  rewrite /tcr_chain /unzip1 -map_comp.
  apply/negP => /mapP[k _ et].
  by move: hge; rewrite et ltnn.
- exact: IH.
Qed.

(** Size of the committed list: one target per (chain, position
    above the signed digit) — the seq-sum form of
    [\sum_(j < l) (w.-1 - d_j)]. *)
Lemma size_tcr_targets pp (m : seq nat) (sigs : seq N) :
  size m = l -> size sigs = l ->
  size (tcr_targets pp m sigs) = sumn [seq w.-1 - d | d <- m].
Proof.
move=> hm hsigs.
by rewrite /tcr_targets -hm size_tcr_targets_from // hsigs hm.
Qed.

(** Crude cap: the SM-TCR budget [p := l * w] always suffices (the
    TQUERY assert [size tws < p] passes at every commit since even
    the FULL list is at most [l * w.-1 <= l * w]... the strict
    in-prefix bound follows from [tcr_index_lt] + [size_tcr_targets]
    at the consumer). *)
Lemma size_tcr_targets_leq pp (m : seq nat) (sigs : seq N) :
  size m = l -> size sigs = l ->
  size (tcr_targets pp m sigs) <= l * w.
Proof.
move=> hm hsigs.
rewrite size_tcr_targets //.
have hall : all (fun x => x <= w) [seq w.-1 - d | d <- m].
  apply/allP => x /mapP[d _ ->].
  exact: leq_trans (leq_subr _ _) (leq_pred _).
have := sumn_all_leq _ _ hall.
by rewrite size_map hm.
Qed.

(** The committed index of [(i, k)] is in range (CHECK's [getm] is a
    [Some]; also gives [size tws < p] at each intermediate commit by
    monotonicity at the consumer). *)
Lemma tcr_index_lt (m : seq nat) i k :
  size m = l -> i < l -> nth 0 m i <= k < w.-1 ->
  tcr_index m i k < sumn [seq w.-1 - d | d <- m].
Proof.
move=> hm hi /andP[hdk hkw].
rewrite /tcr_index -[in X in _ < X](cat_take_drop i m) (drop_nth 0) ?hm //.
rewrite map_cat sumn_cat /= ltn_add2l.
apply: ltn_addr; apply: ltn_sub2r => //.
exact: leq_ltn_trans hdk hkw.
Qed.

(** THE bookkeeping lemma: at index [tcr_index m i k] the reduction
    committed exactly tweak [(i, k)] with input the honest chain
    value at [k] (recomputed from the [i]-th signature digit) — so
    [ChainColl k u v] of [forgery_cases]/[forgery_classify] maps to
    CHECK index [tcr_index m i k], whose stored target input is [v]. *)
Lemma tcr_targets_nth pp (m : seq nat) (sigs : seq N) i k
    (x0 : (nat * nat) * N) (y0 : N) :
  size m = l -> size sigs = l -> i < l ->
  nth 0 m i <= k < w.-1 ->
  nth x0 (tcr_targets pp m sigs) (tcr_index m i k)
  = ((i, k),
     chain (cf pp i) (nth y0 sigs i) (nth 0 m i) (k - nth 0 m i)).
Proof.
move=> hm hsigs hi hk.
have hss : size sigs = size m by rewrite hsigs hm.
have hi' : i < size m by rewrite hm.
rewrite /tcr_targets /tcr_index -hm.
by rewrite (tcr_targets_from_nth pp 0 _ _ _ _ x0 y0 hss hi' hk) ?add0n.
Qed.

(** Tweak distinctness: the TQUERY assert [t \notin tws] passes for
    every commit in [tcr_targets]'s order. *)
Lemma tcr_targets_tweaks_uniq pp (m : seq nat) (sigs : seq N) :
  size m = l -> uniq (unzip1 (tcr_targets pp m sigs)).
Proof.
move=> hm; rewrite /tcr_targets -hm.
exact: tcr_tweaks_from_uniq.
Qed.

End FixedSumOTSAnalysis.

(* ------------------------------------------------------------------ *)
(** ** Part 2: the valid-commit games G0v / G1v (definitions only) *)

Section FixedSumOTSVGames.

(** Same context as FixedSumOTS.Games. *)
Context (PP N : choice_type).
Context (F : PP -> nat * nat -> N -> N).
Context (dPP : dist PP) (dN : dist N).
Context (l w tsum : nat).

Local Notation FS := (FixedSumOTS PP N F dPP dN l w tsum).

Definition g0v_pk_loc := mkloc 210 (None : option (Pk FS)).
Definition g0v_log_loc := mkloc 211 ([::] : seq (Msg FS)).

(** [G0v] = [G0flat] with [#assert (valid_msg m)] in COMMIT
    (PROOF_PLAN.md edge-case decision: an invalid commitment aborts
    the experiment; the refusal branch of G0flat disappears and
    COMMIT always logs and signs). *)
Definition G0v (b : bool) : game (I_KOTS FS) :=
  [package [fmap g0v_pk_loc ; g0v_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0v_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      pp ← dPP ;;
      xs ← sample_seq dN l ;;
      #put g0v_pk_loc := Some (pp, chain_ends PP N F l w pp xs) ;;
      #put g0v_log_loc := [:: m] ;;
      ret ((pp, chain_ends PP N F l w pp xs),
           Some (sign_digits PP N F l pp xs m))
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0v_pk_loc ;;
        log ← get g0v_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(** [G1v] = same assert + [G1]'s post-UD sampling (Games.v:
    [sample_sig_roots] hides one uniform per chain one hash step
    before the signature digit; [ends_from_sig] re-roots the public
    ends there).  G1's refusal branch is gone: it is exactly what the
    assert cuts off. *)
Definition G1v (b : bool) : game (I_KOTS FS) :=
  [package [fmap g0v_pk_loc ; g0v_log_loc ] ;
    [ COMMIT ] : { SParam FS × Msg FS ~> Pk FS × 'option (Sig FS) } '(sp, m) {
      pko ← get g0v_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      #assert (valid_msg l w tsum m) ;;
      pp ← dPP ;;
      sg ← sample_sig_roots PP N F dN pp 0 m ;;
      #put g0v_pk_loc := Some (pp, ends_from_sig PP N F l w pp m sg) ;;
      #put g0v_log_loc := [:: m] ;;
      ret ((pp, ends_from_sig PP N F l w pp m sg), Some sg)
    } ;
    [ KFORGE ] : { Msg FS × Sig FS ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0v_pk_loc ;;
        log ← get g0v_log_loc ;;
        ret (verify_sig PP N F l w tsum pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

End FixedSumOTSVGames.
