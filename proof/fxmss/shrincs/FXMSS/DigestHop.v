(** * SHRINCS.FXMSS.DigestHop

    Hop 4 of the FXMSS EU-CMA chain (P6; plan in
    theories/SHRINCS/FXMSS/PROOF_PLAN.md, "Digest layer" + the
    corrected design of "ReproHop.v status & lessons" consequence 2
    and "DeferHop.v status & lessons" design adjustment 2): the
    digest-collision abort, played AFTER reprogramming as the hop
    G3c -> G4c, with the Pr-level statistical bound [eps_coll]
    (the tex's F.0 -> F.1 / claim:fxmss-etcr, whose InSec^rkTCR term
    is realized here as its concrete ROM value; PROOF_PLAN.md
    deviation 3).

    ** The game [G4c] (G3c + presampled digests + the abort in FORGE)

    [G3c] (FXMSS/ReproHop.v) samples the digest of SIGN query j
    lazily (a fresh [md <- dD] per signing-table miss, reprogrammed
    into the rom).  The DeferHop consumer obligation requires the
    hop-4 abort to cover ALL q_s presampled digests — used or unused
    — so that in the leaf hybrid the committed-message freshness
    conjunct of [G01]'s KFORGE is transparent for EVERY anchor with a
    digest slot, including anchors the adversary never queries.  A
    lazily sampled digest that does not exist at FORGE time cannot be
    covered by any abort, hence [G4c] PRESAMPLES:

    - GEN additionally samples the q_s-slot digest map
      [sd : chMap 'nat D] ([fill_code (iota 0 q_s) emptym], one
      independent [dD] draw per slot j < q_s) into the new location
      [fx_sd_loc] (409);
    - SIGN's table-miss branch CONSUMES slot [sc] (the per-call
      budget counter: each call burns at most one slot, each slot is
      read at most once) instead of sampling [md <- dD]; everything
      else (the reprogramming write, refusal handling) is G3c's;
    - FORGE (real branch) returns G3c's verdict AND-ed with the
      negated abort event [coll_ev] below.

    ** The abort event (the design choice the plan left open)

      coll_ev sd tb (zi', m') r' md' :=
        (md' \in codomm sd) && (getm tb (zi', m') != Some r')

    i.e. the forged digest md* (the rom value at the forgery's digest
    point p* = (r*, (pk, (zi*, m* )))) equals one of the q_s
    presampled slot digests AND p* is NOT a cached signing point (the
    signing table [fx_rt_loc] maps the (zi, m) of every signing-table
    miss to its fresh randomness r; p* is the rom point of a signing
    slot exactly when tb (zi*, m* ) = Some r* ).

    Why the cached-point exemption is both NECESSARY and HARMLESS:

    - Necessary: without it the abort fires with certainty on the
      "refused replay" — the adversary asks SIGN(m), is REFUSED
      (grinding failure; m is then NOT in the log), and submits a
      forgery on m at the same leaf with the (revealed or guessed)
      randomness r_j: the recomputed digest IS the consumed slot
      digest y_j, read off the same rom point.  [fx_verify] does not
      cap the carried grinding counter at c_max (WOTSC.Scheme's
      documented deviation), so the verdict can be TRUE on such a
      digest, and no q/|D|-style statistical bound can absorb an
      event the adversary triggers at will.
    - Harmless downstream: the consumer (the leaf hybrid, via G5f)
      needs "verdict true ==> md* != y_j for every slot j" only in
      the grind-valid game G5f (hop 5 asserts ALL presampled digests
      grindable at GEN), where refusals do not exist: there every
      consumed slot is logged, so a verdict-true forgery (fresh:
      m* notin log) cannot sit on a cached signing point — the
      exemption conjunct is identically true under the verdict, and
      the abort covers all q_s slots.  (Consumed slots: cached point
      excluded by freshness, value collision at any other point
      excluded by the abort; unconsumed slots: excluded by the abort
      directly.)

    ** Statements

    - [G4c] — the game (generic samplers, like G2c/G3c); [G4m] is
      internal scaffolding (G3c + the presampled map, NO abort).
    - [Digest_hop (b) (A) (VA) :
         Adv (G3c … b) (G4c … b) A
         <= q_s%:R * ((q_h + q_f)%:R / d_n.+1%:R)]
      at the documented scope [D := chFin d_n.+1] with the uniform
      digest sampler [rp_dPfx d_n] (so |D| = d_n.+1; PROOF_PLAN.md
      "Side conditions" — the same chFin+uniform scoping as
      Reprogram.v).  This is the plan's
      [q_s * (q_h + q_s + q_f) / |D|]-SHAPED bound, in fact SMALLER:
      the factorization below never charges a signing-slot digest
      against the rom (signing writes land on cached points, which
      the event exempts), so the q_s^2 term disappears;

        eps_coll := q_s * (q_h + q_f) / |D|.

    ** Proof shape (Reprogram.v's Pr-level architecture, two hops)

    No relational step can relate G3c to G4c (the presampled slot
    couples with a lazy sample that happens arbitrarily many oracle
    calls later — the GF_presample obstruction).  The hop factors
    through [G4m]:

    - [DIG_eq] (G3c = G4m, an EQUALITY): induction over the
      adversary's ValidCode comparing [Pr (c ∘ G3c) h] against the
      average, over iid-uniform fillings of the still-unread digest
      slots [js], of [Pr (c ∘ G4m) (h with sd := filling)].  GEN's
      own [fill_code] sampling materializes the average (js = all
      q_s slots); a SIGN table-miss at counter sc PEELS slot sc off
      the average ([fill_peel]) and couples it with G3c's lazy
      [md <- dD] — the eager/lazy core.  Everything is [eq_dlet_at]
      plumbing; no norm bounds, hence no |D| restriction (generic
      [dD], lossless).
    - [DIG_diff] (G4m vs G4c, identical-until-bad): the two games
      share ALL code except FORGE's final verdict, so they run in
      LOCKSTEP on the same heap.  Invariant [dig_inv]: every rom
      value at a NON-CACHED point avoids codomm sd.  Charges: at GEN,
      the freshly sampled slot digests must avoid the (<= q_h)
      pre-GEN rom values ([fill_split_le], q_s * |rom|/|D|); at each
      HASH/FORGE rom miss, the fresh rom value must avoid the <= q_s
      slot digests ([uniform_split_le], q_s/|D| each).  SIGN costs
      NOTHING: its rom writes land on cached points.  Under the
      invariant the two FORGE verdicts are EQUAL (a hit at a
      non-cached point has md* notin codomm sd; a cached hit is
      exempted by the event's second conjunct), so the whole
      difference is the charged bad mass:
        |Pr (c ∘ G4m) h - Pr (c ∘ G4c) h| <= q_s * Bn(h) / |D|,
      Bn(h) := (q_h - hc) + (q_f - fc) + (|rom| if pre-GEN else 0),
      which at the empty heap is the headline eps_coll.

    Locations: G4m/G4c = Games.v's 400-407 + [fx_fcnt_loc] 408
    (shared with G2c/G3c, ReproHop.v) + [fx_sd_loc] 409.

    Style: Toolkit/Reprogram.v + Games/TCRXRom.v (the Pr-level
    toolkit and its lessons: named lazy helpers with explicit
    ValidCode hints, named boolean event [coll_ev], oracle-level
    stepping lemmas, paired rewrites anchored with [in X in _ - X]).
    ReproHop.v supplies the section discipline and G3c. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From mathcomp Require Import reals distr realsum.
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme
  Games.THF Toolkit.SampleSeq Toolkit.ROPlus Toolkit.Reprogram.
From SHRINCS Require Import Addressing WOTSC.Scheme WOTSC.Games
  FXMSS.Scheme FXMSS.Games FXMSS.PRFHop FXMSS.ReproHop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic helpers (section-free) *)

(** Two heaps with the same [get_heap] view at EVERY location give the
    same output distribution, for arbitrary raw code (an [opr] node
    yields [dnull] on both sides).  Used to erase the statement's
    vacuous [set_heap _ fx_sd_loc emptym] against the default-empty
    heap at the top level. *)
Lemma dPr_eqheap_full {T' : choiceType} (c : raw_code T') :
  ∀ h1 h2 : heap,
    (∀ ℓ : Location, get_heap h1 ℓ = get_heap h2 ℓ) →
    ∀ z, dfst (Pr_code c h1) z = dfst (Pr_code c h2) z.
Proof.
induction c as [a | o x k IH | l k IH | l v c IH | op k IH].
- by move=> h1 h2 hagree z; rewrite 2!dPr_ret.
- move=> h1 h2 hagree z.
  have -> : Pr_code (opr o x k) h1 = dnull by exact: Pr_code_call.
  have -> : Pr_code (opr o x k) h2 = dnull by exact: Pr_code_call.
  by [].
- move=> h1 h2 hagree z.
  rewrite 2!Pr_code_get (hagree l).
  exact: IH.
- move=> h1 h2 hagree z.
  rewrite 2!Pr_code_put.
  apply: IH => ℓ.
  case: (eqVneq ℓ.1 l.1) => [e | ne].
  + by rewrite /get_heap /set_heap !setmE e eqxx.
  + by rewrite !get_set_heap_neq // hagree.
- move=> h1 h2 hagree z.
  rewrite 2!dPr_sample.
  apply: eq_dlet_at => a.
  exact: IH.
Qed.

(** The counting backbone of the "fresh value hits a stored digest"
    splits: a map has no more values than keys. *)
Lemma size_codomm_le {T S : ordType} (m : {fmap T -> S}) :
  (size (codomm m) <= size (domm m))%N.
Proof.
case: (altP (fset0Pn (codomm m))) => [[y0 hy0] | ]; last first.
- by rewrite negbK => /eqP ->; rewrite sizes0.
- have hsub : codomm m :<=: (λ k, odflt y0 (getm m k)) @: domm m.
  { apply/fsubsetP => y /codommP [k hk].
    have hkd : k \in domm m by rewrite mem_domm hk.
    have := mem_imfset (λ k', odflt y0 (getm m k')) hkd.
    by rewrite hk. }
  apply: leq_trans (fsubset_leq_size hsub) _.
  exact: size_imfset.
Qed.

(* ------------------------------------------------------------------ *)

Section FXMSSDigestHop.

Context {w l : nat}.
Local Notation adrs_sf := (Addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (Addressing.adrs_sf_ch l w).

(** Same section context as FXMSS/ReproHop.v (whose [G3c] is the
    hop's left endpoint). *)
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

(* ------------------------------------------------------------------ *)
(** ** Shorthands (ReproHop's) *)

Local Notation tshape := (shape_of h_sf).
Local Notation spath := (sign_path h_sf).
Local Notation posid := (pos_id h_sf).
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).
Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (FxSig N R).
Local Notation FXST := (FxSt PP N).
Local Notation ROIN := (RoIn PP N M R).
Local Notation fxroot := (fx_root_x PP N F Tl Htree h_sf).
Local Notation fxsignx :=
  (fx_sign_x PP N D R F Tl Hgrind Htree S_wn c_max h_sf).
Local Notation fxvermd :=
  (fx_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation skeys := (@sample_keys l N dN).

Local Notation Lst := (fx_st_loc PP N).
Local Notation Llog := (fx_log_loc M).
Local Notation Lrom := (fx_rom_loc PP N D M R).
Local Notation Lrt := (fx_rt_loc M R).

Local Notation G3 :=
  (G3c PP N D M R F Tl Hgrind Htree dPP dN dR dD
     S_wn c_max h_sf q_s q_h n_max q_f).

(** The signing-table key space (ReproHop's RTKey). *)
Local Notation RTK := (('nat × 'nat) × M).

(** The presampled digest map (slot j < q_s ↦ digest). *)
Definition fx_sd_loc := mkloc 409 (emptym : chMap 'nat D).
Local Notation Lsd := fx_sd_loc.

(* ------------------------------------------------------------------ *)
(** ** The slot sampler [fill_code] *)

(** [fill_code js m0]: extend [m0] with one independent [dD] draw per
    index in [js].  GEN's sampler is [fill_code (iota 0 q_s) emptym];
    the same code with general [js]/[m0] is the averaging operator of
    the DIG_eq statement. *)
Fixpoint fill_code (js : seq nat) (m0 : chMap 'nat D) :
    raw_code (chMap 'nat D) :=
  match js with
  | [::] => ret m0
  | j :: js' => y ← dD ;; fill_code js' (setm m0 j y)
  end.

#[export] Instance fill_code_valid (L : Locations) (I : Interface)
    (js : seq nat) (m0 : chMap 'nat D) :
  ValidCode L I (fill_code js m0).
Proof.
elim: js m0 => [|j js IH] m0 /=.
- apply valid_ret.
- eapply valid_bind.
  + eapply valid_scheme, prog_valid.
  + move=> y. exact: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The abort event *)

(** [coll_ev sd tb zim r md]: the digest [md], read off the rom point
    (r, (pk, zim)), collides with a presampled slot digest, and the
    point is not a cached signing point (header).  A named boolean
    definition so proofs can case on the exact application occurring
    in the game (TCRXRom lesson). *)
Definition coll_ev (sd : chMap 'nat D) (tb : chMap RTK R)
    (zim : ('nat × 'nat) × M) (r : R) (md : D) : bool :=
  (md \in codomm sd) && (getm tb zim != Some r).

(* ------------------------------------------------------------------ *)
(** ** M5 lift: named oracle bodies + DIRECTED game assembly

    The lifted used-set SIGN body defeats the plain [package] TC search
    (>30-min wall; M5_CAMPAIGN §1.5), so — exactly as Games.v/ReproHop.v
    — each oracle is a named definition with a hand-proved [ValidCode]
    instance and the games [G4m]/[G4c] are assembled by the directed
    [valid_package_cons] idiom (peel FORGE->HASH->SIGN->GEN).

    The lift changes GEN (fill the per-leaf slot map over the STATIC
    domain [iota 0 n_max] — slot j = leaf j of the committed shape) and
    SIGN (input [mz : M × ('nat × 'nat)]; validate the adversary id with
    [flok], refuse re-used ids via [fx_used_loc], read the presampled
    digest at slot [flidx st.2.1 mz.2] on a table miss).  HASH and FORGE
    are leaf-agnostic — [coll_ev] keeps [md \in codomm sd], the forgery
    reads its own leaf id from the signature. *)

Definition geno : opsig := (FXGEN, ('list 'bool, PP × N)).
Definition sgo : opsig := (FXSIGN, (M × ('nat × 'nat), 'option FXSIG)).
Definition hho : opsig := (FXHASH, (ROIN, D)).
Definition fgo : opsig := (FXFORGE, (M × FXSIG, 'bool)).

Definition G4_locs : Locations :=
  [fmap Lst ; fx_used_loc ; fx_scnt_loc ; Llog ; Lrom ;
        fx_hcnt_loc ; Lrt ; fx_fcnt_loc ; fx_sd_loc ].

(** G3c's GEN (= ReproHop's [gc_gen_body]); no presample. *)
Definition gen3_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   #put Lst := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   ret (pp, fxroot pp sp xss)).

(** G4m/G4c's GEN: presample the per-leaf slot map over [iota 0 n_max]. *)
Definition gen4_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   sd ← fill_code (iota 0 n_max) emptym ;;
   #put Lst := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   #put Lsd := sd ;;
   ret (pp, fxroot pp sp xss)).

(** G3c's SIGN (= ReproHop's [g3c_sign_body]): reprogrammed lazy digest. *)
Definition sign3_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get fx_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get fx_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     match getm tb (mz.2, mz.1) with
     | Some r =>
         #put fx_used_loc := setm us mz.2 Datatypes.tt ;;
         #put Lrt := setm tb (mz.2, mz.1) r ;;
         md ← (match getm mp (r, (st.1, (mz.2, mz.1))) with
               | Some d => ret d
               | None => d ← dD ;; ret d
               end) ;;
         #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put Llog := rcons lg mz.1 ;;
             #put fx_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put fx_scnt_loc := sc.+1 ;;
             ret None
         end
     | None =>
         r ← dR ;;
         md ← dD ;;
         #put fx_used_loc := setm us mz.2 Datatypes.tt ;;
         #put Lrt := setm tb (mz.2, mz.1) r ;;
         #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put Llog := rcons lg mz.1 ;;
             #put fx_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put fx_scnt_loc := sc.+1 ;;
             ret None
         end
     end
   else
     #put fx_scnt_loc := sc.+1 ;;
     ret None).

(** G4m/G4c's SIGN: identical to [sign3_body] except a table miss reads
    the presampled digest at slot [flidx st.2.1 mz.2] (rather than a
    fresh [dD] draw). *)
Definition sign4_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get fx_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get fx_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     match getm tb (mz.2, mz.1) with
     | Some r =>
         #put fx_used_loc := setm us mz.2 Datatypes.tt ;;
         #put Lrt := setm tb (mz.2, mz.1) r ;;
         md ← (match getm mp (r, (st.1, (mz.2, mz.1))) with
               | Some d => ret d
               | None => d ← dD ;; ret d
               end) ;;
         #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put Llog := rcons lg mz.1 ;;
             #put fx_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put fx_scnt_loc := sc.+1 ;;
             ret None
         end
     | None =>
         r ← dR ;;
         sd ← get Lsd ;;
         md ← (match getm sd (flidx st.2.1 mz.2) with
               | Some d => ret d
               | None => d ← dD ;; ret d
               end) ;;
         #put fx_used_loc := setm us mz.2 Datatypes.tt ;;
         #put Lrt := setm tb (mz.2, mz.1) r ;;
         #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put Llog := rcons lg mz.1 ;;
             #put fx_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put fx_scnt_loc := sc.+1 ;;
             ret None
         end
     end
   else
     #put fx_scnt_loc := sc.+1 ;;
     ret None).

Definition hash_body (x : ROIN) : raw_code D :=
  (hc ← get fx_hcnt_loc ;;
   #assert (hc < q_h)%N ;;
   mp ← get Lrom ;;
   md ← (match getm mp x with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp x md ;;
   #put fx_hcnt_loc := hc.+1 ;;
   ret md).

(** The forgery's digest point and the (G3c/G4m) verdict. *)
Definition fgpt (st : FXST) (m : M) (sg : FXSIG) : ROIN :=
  (sg.1.2, (st.1, (sg.1.1, m))).
Definition fgverd (st : FXST) (lg : seq M) (m : M) (sg : FXSIG)
    (md : D) : bool :=
  fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2 && (m \notin lg).

(** G3c/G4m's FORGE body (no abort; [b]-gated verdict). *)
Definition forge3f_body (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get fx_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put fx_fcnt_loc := fc.+1 ;;
   ret (if b then
          fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
          && (m \notin lg)
        else false)).

(** G4c's FORGE body ([b]-gated verdict AND the collision abort). *)
Definition forge4cf_body (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get fx_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put fx_fcnt_loc := fc.+1 ;;
   ret (if b then
          (fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
           && (m \notin lg))
          && ~~ coll_ev sd tb (sg.1.1, m) sg.1.2 md
        else false)).

(** Unconditional-verdict bodies (consumed by the [forge3_step] /
    [forge4c_step] oracle-step lemmas; the [b]-gate is discharged by the
    walk that instantiates them). *)
Definition forge3_body (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get fx_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put fx_fcnt_loc := fc.+1 ;;
   ret (fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
        && (m \notin lg))).

Definition forge4c_body (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get fx_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put fx_fcnt_loc := fc.+1 ;;
   ret ((fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
         && (m \notin lg))
        && ~~ coll_ev sd tb (sg.1.1, m) sg.1.2 md)).

(* ------------------------------------------------------------------ *)
(** ** ValidCode instances (hand-proved; the directed assembly bullets) *)

#[export] Instance gen4_body_valid (I : Interface) (sp : 'list 'bool) :
  ValidCode G4_locs I (gen4_body sp).
Proof.
rewrite /gen4_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_bind; first by apply: fill_code_valid. move=> sd.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance hash_body_valid (I : Interface) (x : ROIN) :
  ValidCode G4_locs I (hash_body x).
Proof.
rewrite /hash_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance forge3f_body_valid (I : Interface) (b : bool)
    (m : M) (sg : FXSIG) :
  ValidCode G4_locs I (forge3f_body b m sg).
Proof.
rewrite /forge3f_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance forge4cf_body_valid (I : Interface) (b : bool)
    (m : M) (sg : FXSIG) :
  ValidCode G4_locs I (forge4cf_body b m sg).
Proof.
rewrite /forge4cf_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance sign4_body_valid (I : Interface)
    (mz : M × ('nat × 'nat)) :
  ValidCode G4_locs I (sign4_body mz).
Proof.
rewrite /sign4_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
case: (getm tb _) => [r|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_bind.
    case: (getm mp _) => [d|]; first by apply valid_ret.
    by eapply valid_bind; first eapply valid_scheme, prog_valid;
       move=> d; apply valid_ret.
  move=> md.
  eapply valid_putr; first by fmap_solve.
  case: (fxsignx _ _ _ _ _ _) => [sg|].
  + eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve.
    apply valid_ret.
  + eapply valid_putr; first by fmap_solve. apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> r.
  eapply valid_getr; first by fmap_solve. move=> sd.
  eapply valid_bind.
    case: (getm sd _) => [d|]; first by apply valid_ret.
    by eapply valid_bind; first eapply valid_scheme, prog_valid;
       move=> d; apply valid_ret.
  move=> md.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  case: (fxsignx _ _ _ _ _ _) => [sg|].
  + eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve.
    apply valid_ret.
  + eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** G4m: G3c + the presampled digest map (NO abort; scaffolding) *)

Definition G4m (b : bool) : game IG.
Proof.
notypeclasses refine [package G4_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { gen4_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      sign4_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { forge3f_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge3f_body_valid. } }
    { intros x; exact: hash_body_valid. } }
  { intro mz; exact: sign4_body_valid. } }
{ intro sp; exact: gen4_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** G4c: G4m + the collision abort in FORGE (the deliverable) *)

Definition G4c (b : bool) : game IG.
Proof.
notypeclasses refine [package G4_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { gen4_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      sign4_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { forge4cf_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge4cf_body_valid. } }
    { intros x; exact: hash_body_valid. } }
  { intro mz; exact: sign4_body_valid. } }
{ intro sp; exact: gen4_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Resolve equations (extract the oracle body from each game) *)

Lemma resolve_g3_gen (b : bool) (sp : 'list 'bool) :
  resolve (G3 b) geno sp = gen3_body sp.
Proof. by rewrite /G3c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g3_sign (b : bool) (mz : M × ('nat × 'nat)) :
  resolve (G3 b) sgo mz = sign3_body mz.
Proof. by rewrite /G3c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g3_hash (b : bool) (x : ROIN) :
  resolve (G3 b) hho x = hash_body x.
Proof. by rewrite /G3c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g3_forge (b : bool) (m : M) (sg : FXSIG) :
  resolve (G3 b) fgo (m, sg) = forge3f_body b m sg.
Proof. by rewrite /G3c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4m_gen (b : bool) (sp : 'list 'bool) :
  resolve (G4m b) geno sp = gen4_body sp.
Proof. by rewrite /G4m /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4m_sign (b : bool) (mz : M × ('nat × 'nat)) :
  resolve (G4m b) sgo mz = sign4_body mz.
Proof. by rewrite /G4m /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4m_hash (b : bool) (x : ROIN) :
  resolve (G4m b) hho x = hash_body x.
Proof. by rewrite /G4m /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4m_forge (b : bool) (m : M) (sg : FXSIG) :
  resolve (G4m b) fgo (m, sg) = forge3f_body b m sg.
Proof. by rewrite /G4m /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4c_gen (b : bool) (sp : 'list 'bool) :
  resolve (G4c b) geno sp = gen4_body sp.
Proof. by rewrite /G4c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4c_sign (b : bool) (mz : M × ('nat × 'nat)) :
  resolve (G4c b) sgo mz = sign4_body mz.
Proof. by rewrite /G4c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4c_hash (b : bool) (x : ROIN) :
  resolve (G4c b) hho x = hash_body x.
Proof. by rewrite /G4c /resolve /= coerce_kleisliE. Qed.

Lemma resolve_g4c_forge (b : bool) (m : M) (sg : FXSIG) :
  resolve (G4c b) fgo (m, sg) = forge4cf_body b m sg.
Proof. by rewrite /G4c /resolve /= coerce_kleisliE. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure finishers (the deterministic tails as heap functions) *)

(** SIGN's tail once (r, md) are fixed: result and final heap.  SEALED
    with ssreflect's [locked] idiom (kernel never delta-unfolds the giant
    body; the ~45 GB SIGN goal collapse, [DIGEST_OPT_NOTES.md]).  The
    lifted tail writes [fx_used_loc] (the used-set) in place of the
    deleted [fx_q_loc] counter. *)
Definition sign_fin :
    heap -> FXST -> nat -> nat -> chMap ('nat × 'nat) 'unit -> seq M ->
    chMap ROIN D -> chMap RTK R -> (M × ('nat × 'nat)) -> R -> D ->
    option FXSIG * heap :=
  locked (fun (h : heap) (st : FXST) (qv sc : nat)
    (us : chMap ('nat × 'nat) 'unit) (lg : seq M)
    (mp : chMap ROIN D) (tb : chMap RTK R)
    (mz : M × ('nat × 'nat)) (r : R) (md : D) =>
  let h2 :=
    set_heap
      (set_heap
         (set_heap h fx_used_loc (setm us mz.2 Datatypes.tt))
         Lrt (setm tb (mz.2, mz.1) r))
      Lrom (setm mp (r, (st.1, (mz.2, mz.1))) md) in
  match fxsignx st.1.1 st.2.1 st.2.2 qv r md with
  | Some sg =>
      (Some sg,
       set_heap (set_heap h2 Llog (rcons lg mz.1)) fx_scnt_loc sc.+1)
  | None => (None, set_heap h2 fx_scnt_loc sc.+1)
  end).

Lemma sign_finE :
  sign_fin = (fun (h : heap) (st : FXST) (qv sc : nat)
    (us : chMap ('nat × 'nat) 'unit) (lg : seq M)
    (mp : chMap ROIN D) (tb : chMap RTK R)
    (mz : M × ('nat × 'nat)) (r : R) (md : D) =>
  let h2 :=
    set_heap
      (set_heap
         (set_heap h fx_used_loc (setm us mz.2 Datatypes.tt))
         Lrt (setm tb (mz.2, mz.1) r))
      Lrom (setm mp (r, (st.1, (mz.2, mz.1))) md) in
  match fxsignx st.1.1 st.2.1 st.2.2 qv r md with
  | Some sg =>
      (Some sg,
       set_heap (set_heap h2 Llog (rcons lg mz.1)) fx_scnt_loc sc.+1)
  | None => (None, set_heap h2 fx_scnt_loc sc.+1)
  end).
Proof. by rewrite /sign_fin -lock. Qed.

Definition hash_fin : heap -> nat -> chMap ROIN D -> ROIN -> D -> heap :=
  locked (fun (h : heap) (hc : nat) (mp : chMap ROIN D)
    (x : ROIN) (md : D) =>
  set_heap (set_heap h Lrom (setm mp x md)) fx_hcnt_loc hc.+1).

Lemma hash_finE :
  hash_fin = (fun (h : heap) (hc : nat) (mp : chMap ROIN D)
    (x : ROIN) (md : D) =>
  set_heap (set_heap h Lrom (setm mp x md)) fx_hcnt_loc hc.+1).
Proof. by rewrite /hash_fin -lock. Qed.

Definition forge_fin : heap -> nat -> chMap ROIN D -> ROIN -> D -> heap :=
  locked (fun (h : heap) (fc : nat) (mp : chMap ROIN D)
    (pt : ROIN) (md : D) =>
  set_heap (set_heap h Lrom (setm mp pt md)) fx_fcnt_loc fc.+1).

Lemma forge_finE :
  forge_fin = (fun (h : heap) (fc : nat) (mp : chMap ROIN D)
    (pt : ROIN) (md : D) =>
  set_heap (set_heap h Lrom (setm mp pt md)) fx_fcnt_loc fc.+1).
Proof. by rewrite /forge_fin -lock. Qed.

(* ------------------------------------------------------------------ *)
(** ** Oracle-level stepping lemmas (each walks one body once) *)

Section OracleSteps.

Context {T' : choiceType}.

Lemma gen3_step (sp : 'list 'bool) {k : _ → raw_code T'} {h : heap}
    {z : T'} :
  dfst (Pr_code (bind (gen3_body sp) k) h) z
  = if ~~ isSome (get_heap h Lst)
       && (size (leaf_paths (tshape sp)) <= n_max)%N
    then (\dlet_(pp <- Pr_fst dPP)
          \dlet_(_ <- Pr_fst dN)
          \dlet_(_ <- Pr_fst dR)
          \dlet_(xss <- Pr_fst (skeys (size (leaf_paths (tshape sp)))))
            dfst (Pr_code (k (pp, fxroot pp sp xss))
                    (set_heap h Lst
                       (Some ((pp, fxroot pp sp xss), (sp, xss)))))) z
    else 0.
Proof.
rewrite /gen3_body. cbn [bind].
rewrite Pr_code_get.
case E1: (isSome (get_heap h Lst)).
{ by rewrite -[~~ true]/false assertD_false dPr_bind_fail. }
rewrite -[~~ false]/true assertD_true /=. cbn [bind].
case E2: ((size (leaf_paths (tshape sp)) <= n_max)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => pp.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => x1.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => x2.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => xss.
cbn [bind].
by rewrite Pr_code_put.
Qed.

Lemma gen4_step (sp : 'list 'bool) {k : _ → raw_code T'} {h : heap}
    {z : T'} :
  dfst (Pr_code (bind (gen4_body sp) k) h) z
  = if ~~ isSome (get_heap h Lst)
       && (size (leaf_paths (tshape sp)) <= n_max)%N
    then (\dlet_(pp <- Pr_fst dPP)
          \dlet_(_ <- Pr_fst dN)
          \dlet_(_ <- Pr_fst dR)
          \dlet_(xss <- Pr_fst (skeys (size (leaf_paths (tshape sp)))))
          \dlet_(sdm <- Pr_fst (fill_code (iota 0 n_max) emptym))
            dfst (Pr_code (k (pp, fxroot pp sp xss))
                    (set_heap
                       (set_heap h Lst
                          (Some ((pp, fxroot pp sp xss), (sp, xss))))
                       Lsd sdm))) z
    else 0.
Proof.
rewrite /gen4_body. cbn [bind].
rewrite Pr_code_get.
case E1: (isSome (get_heap h Lst)).
{ by rewrite -[~~ true]/false assertD_false dPr_bind_fail. }
rewrite -[~~ false]/true assertD_true /=. cbn [bind].
case E2: ((size (leaf_paths (tshape sp)) <= n_max)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => pp.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => x1.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => x2.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => xss.
rewrite bind_assoc dPr_dist.
apply: eq_dlet_at => sdm.
cbn [bind].
by rewrite 2!Pr_code_put.
Qed.

Lemma hash_step (x : ROIN) {k : _ → raw_code T'} {h : heap} {z : T'} :
  dfst (Pr_code (bind (hash_body x) k) h) z
  = if (get_heap h fx_hcnt_loc < q_h)%N then
      match getm (get_heap h Lrom) x with
      | Some md =>
          dfst (Pr_code (k md)
                  (hash_fin h (get_heap h fx_hcnt_loc)
                     (get_heap h Lrom) x md)) z
      | None =>
          (\dlet_(md <- Pr_fst dD)
             dfst (Pr_code (k md)
                     (hash_fin h (get_heap h fx_hcnt_loc)
                        (get_heap h Lrom) x md))) z
      end
    else 0.
Proof.
rewrite /hash_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((get_heap h fx_hcnt_loc < q_h)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
rewrite hash_finE.
case E2: (getm (get_heap h Lrom) x) => [md|].
- cbn [bind]. by rewrite 2!Pr_code_put.
- rewrite bind_assoc. cbn [bind].
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. by rewrite 2!Pr_code_put.
Qed.

Lemma forge3_step (m : M) (sg : FXSIG) {k : _ → raw_code T'}
    {h : heap} {z : T'} :
  dfst (Pr_code (bind (forge3_body m sg) k) h) z
  = if (get_heap h fx_fcnt_loc < q_f)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          match getm (get_heap h Lrom) (fgpt st m sg) with
          | Some md =>
              dfst (Pr_code (k (fgverd st (get_heap h Llog) m sg md))
                      (forge_fin h (get_heap h fx_fcnt_loc)
                         (get_heap h Lrom) (fgpt st m sg) md)) z
          | None =>
              (\dlet_(md <- Pr_fst dD)
                 dfst (Pr_code (k (fgverd st (get_heap h Llog) m sg md))
                         (forge_fin h (get_heap h fx_fcnt_loc)
                            (get_heap h Lrom) (fgpt st m sg) md))) z
          end
      end
    else 0.
Proof.
rewrite /forge3_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((get_heap h fx_fcnt_loc < q_f)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [bind].
rewrite 2!Pr_code_get.
rewrite -[(sg.1.2, (st.1, (sg.1.1, m)))]/(fgpt st m sg).
case E3: (getm (get_heap h Lrom) (fgpt st m sg)) => [md|].
- cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE /fgverd.
- rewrite bind_assoc. cbn [bind].
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE /fgverd.
Qed.

Lemma forge4c_step (m : M) (sg : FXSIG) {k : _ → raw_code T'}
    {h : heap} {z : T'} :
  dfst (Pr_code (bind (forge4c_body m sg) k) h) z
  = if (get_heap h fx_fcnt_loc < q_f)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          match getm (get_heap h Lrom) (fgpt st m sg) with
          | Some md =>
              dfst (Pr_code
                      (k (fgverd st (get_heap h Llog) m sg md
                          && ~~ coll_ev (get_heap h Lsd) (get_heap h Lrt)
                               (sg.1.1, m) sg.1.2 md))
                      (forge_fin h (get_heap h fx_fcnt_loc)
                         (get_heap h Lrom) (fgpt st m sg) md)) z
          | None =>
              (\dlet_(md <- Pr_fst dD)
                 dfst (Pr_code
                         (k (fgverd st (get_heap h Llog) m sg md
                             && ~~ coll_ev (get_heap h Lsd)
                                  (get_heap h Lrt)
                                  (sg.1.1, m) sg.1.2 md))
                         (forge_fin h (get_heap h fx_fcnt_loc)
                            (get_heap h Lrom) (fgpt st m sg) md))) z
          end
      end
    else 0.
Proof.
rewrite /forge4c_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((get_heap h fx_fcnt_loc < q_f)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [bind].
rewrite 4!Pr_code_get.
rewrite -[(sg.1.2, (st.1, (sg.1.1, m)))]/(fgpt st m sg).
case E3: (getm (get_heap h Lrom) (fgpt st m sg)) => [md|].
- cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE /fgverd.
- rewrite bind_assoc. cbn [bind].
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 2!Pr_code_put.
  by rewrite forge_finE /fgverd.
Qed.

Lemma sign3_step (mz : M × ('nat × 'nat)) {k : _ → raw_code T'}
    {h : heap} {z : T'} :
  dfst (Pr_code (bind (sign3_body mz) k) h) z
  = if (get_heap h fx_scnt_loc < q_s)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          if [&& flok st.2.1 mz.2 & mz.2 \notin domm (get_heap h fx_used_loc)]
          then
            match getm (get_heap h Lrt) (mz.2, mz.1) with
            | Some r =>
                match getm (get_heap h Lrom) (r, (st.1, (mz.2, mz.1))) with
                | Some md =>
                    dfst (Pr_code
                      (k (sign_fin h st (flidx st.2.1 mz.2)
                            (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                            (get_heap h Llog) (get_heap h Lrom)
                            (get_heap h Lrt) mz r md).1)
                      (sign_fin h st (flidx st.2.1 mz.2)
                         (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                         (get_heap h Llog) (get_heap h Lrom)
                         (get_heap h Lrt) mz r md).2) z
                | None =>
                    (\dlet_(md <- Pr_fst dD)
                       dfst (Pr_code
                         (k (sign_fin h st (flidx st.2.1 mz.2)
                               (get_heap h fx_scnt_loc)
                               (get_heap h fx_used_loc) (get_heap h Llog)
                               (get_heap h Lrom) (get_heap h Lrt)
                               mz r md).1)
                         (sign_fin h st (flidx st.2.1 mz.2)
                            (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                            (get_heap h Llog) (get_heap h Lrom)
                            (get_heap h Lrt) mz r md).2)) z
                end
            | None =>
                (\dlet_(r <- Pr_fst dR) \dlet_(md <- Pr_fst dD)
                   dfst (Pr_code
                     (k (sign_fin h st (flidx st.2.1 mz.2)
                           (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                           (get_heap h Llog) (get_heap h Lrom)
                           (get_heap h Lrt) mz r md).1)
                     (sign_fin h st (flidx st.2.1 mz.2)
                        (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                        (get_heap h Llog) (get_heap h Lrom)
                        (get_heap h Lrt) mz r md).2)) z
            end
          else
            dfst (Pr_code (k None)
                    (set_heap h fx_scnt_loc
                       (get_heap h fx_scnt_loc).+1)) z
      end
    else 0.
Proof.
rewrite /sign3_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((get_heap h fx_scnt_loc < q_s)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [bind].
rewrite 4!Pr_code_get.
case Eg: ([&& flok st.2.1 mz.2
           & mz.2 \notin domm (get_heap h fx_used_loc)]); last first.
{ cbn [bind]. by rewrite Pr_code_put. }
case E4: (getm (get_heap h Lrt) (mz.2, mz.1)) => [r|].
- cbn [bind]. rewrite Pr_code_put Pr_code_put.
  case E5: (getm (get_heap h Lrom) (r, (st.1, (mz.2, mz.1)))) => [md|].
  + cbn [bind]. rewrite Pr_code_put.
    rewrite sign_finE.
    case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
      => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
  + rewrite bind_assoc. cbn [bind].
    rewrite bind_assoc dPr_dist.
    apply: eq_dlet_at => md.
    cbn [bind]. rewrite Pr_code_put.
    rewrite sign_finE.
    case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
      => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
- rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => r.
  rewrite bind_assoc dPr_dist.
  apply: eq_dlet_at => md.
  cbn [bind]. rewrite 3!Pr_code_put.
  rewrite sign_finE.
  case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
    => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
Qed.

Lemma sign4_step (mz : M × ('nat × 'nat)) {k : _ → raw_code T'}
    {h : heap} {z : T'} :
  dfst (Pr_code (bind (sign4_body mz) k) h) z
  = if (get_heap h fx_scnt_loc < q_s)%N then
      match get_heap h Lst with
      | None => 0
      | Some st =>
          if [&& flok st.2.1 mz.2 & mz.2 \notin domm (get_heap h fx_used_loc)]
          then
            match getm (get_heap h Lrt) (mz.2, mz.1) with
            | Some r =>
                match getm (get_heap h Lrom) (r, (st.1, (mz.2, mz.1))) with
                | Some md =>
                    dfst (Pr_code
                      (k (sign_fin h st (flidx st.2.1 mz.2)
                            (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                            (get_heap h Llog) (get_heap h Lrom)
                            (get_heap h Lrt) mz r md).1)
                      (sign_fin h st (flidx st.2.1 mz.2)
                         (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                         (get_heap h Llog) (get_heap h Lrom)
                         (get_heap h Lrt) mz r md).2) z
                | None =>
                    (\dlet_(md <- Pr_fst dD)
                       dfst (Pr_code
                         (k (sign_fin h st (flidx st.2.1 mz.2)
                               (get_heap h fx_scnt_loc)
                               (get_heap h fx_used_loc) (get_heap h Llog)
                               (get_heap h Lrom) (get_heap h Lrt)
                               mz r md).1)
                         (sign_fin h st (flidx st.2.1 mz.2)
                            (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                            (get_heap h Llog) (get_heap h Lrom)
                            (get_heap h Lrt) mz r md).2)) z
                end
            | None =>
                match getm (get_heap h Lsd) (flidx st.2.1 mz.2) with
                | Some md =>
                    (\dlet_(r <- Pr_fst dR)
                       dfst (Pr_code
                         (k (sign_fin h st (flidx st.2.1 mz.2)
                               (get_heap h fx_scnt_loc)
                               (get_heap h fx_used_loc) (get_heap h Llog)
                               (get_heap h Lrom) (get_heap h Lrt)
                               mz r md).1)
                         (sign_fin h st (flidx st.2.1 mz.2)
                            (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                            (get_heap h Llog) (get_heap h Lrom)
                            (get_heap h Lrt) mz r md).2)) z
                | None =>
                    (\dlet_(r <- Pr_fst dR) \dlet_(md <- Pr_fst dD)
                       dfst (Pr_code
                         (k (sign_fin h st (flidx st.2.1 mz.2)
                               (get_heap h fx_scnt_loc)
                               (get_heap h fx_used_loc) (get_heap h Llog)
                               (get_heap h Lrom) (get_heap h Lrt)
                               mz r md).1)
                         (sign_fin h st (flidx st.2.1 mz.2)
                            (get_heap h fx_scnt_loc) (get_heap h fx_used_loc)
                            (get_heap h Llog) (get_heap h Lrom)
                            (get_heap h Lrt) mz r md).2)) z
                end
            end
          else
            dfst (Pr_code (k None)
                    (set_heap h fx_scnt_loc
                       (get_heap h fx_scnt_loc).+1)) z
      end
    else 0.
Proof.
rewrite /sign4_body. cbn [bind].
rewrite Pr_code_get.
case E1: ((get_heap h fx_scnt_loc < q_s)%N); last first.
{ by rewrite assertD_false dPr_bind_fail. }
rewrite assertD_true. cbn [bind].
rewrite Pr_code_get.
case E2: (get_heap h Lst) => [st|]; last first.
{ by rewrite -[isSome None]/false assertD_false dPr_bind_fail. }
rewrite -[isSome (Some st)]/true assertD_true. cbn [bind].
rewrite 4!Pr_code_get.
case Eg: ([&& flok st.2.1 mz.2
           & mz.2 \notin domm (get_heap h fx_used_loc)]); last first.
{ cbn [bind]. by rewrite Pr_code_put. }
case E4: (getm (get_heap h Lrt) (mz.2, mz.1)) => [r|].
- cbn [bind]. rewrite Pr_code_put Pr_code_put.
  case E5: (getm (get_heap h Lrom) (r, (st.1, (mz.2, mz.1)))) => [md|].
  + cbn [bind]. rewrite Pr_code_put.
    rewrite sign_finE.
    case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
      => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
  + rewrite bind_assoc. cbn [bind].
    rewrite bind_assoc dPr_dist.
    apply: eq_dlet_at => md.
    cbn [bind]. rewrite Pr_code_put.
    rewrite sign_finE.
    case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
      => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
- rewrite bind_assoc dPr_dist.
  case E5: (getm (get_heap h Lsd) (flidx st.2.1 mz.2)) => [md|].
  + apply: eq_dlet_at => r.
    cbn [bind]. rewrite Pr_code_get E5. cbn [bind].
    rewrite 3!Pr_code_put.
    rewrite sign_finE.
    case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
      => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
  + apply: eq_dlet_at => r.
    cbn [bind]. rewrite Pr_code_get E5.
    rewrite bind_assoc. cbn [bind].
    rewrite bind_assoc dPr_dist.
    apply: eq_dlet_at => md.
    cbn [bind]. rewrite 3!Pr_code_put.
    rewrite sign_finE.
    case E6: (fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md)
      => [sg|] /=; cbn [bind]; by rewrite !Pr_code_put.
Qed.

End OracleSteps.

End FXMSSDigestHop.
