(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.reprogram_sep

    Classical adaptive reprogramming at distinct separators.

    QUERY charges its budget only while its separator has not been
    reprogrammed. REPRO rejects a previously used separator before the
    game bit is inspected. Thus read-backs at already reprogrammed
    separators are free. A final query at an unused separator still
    consumes one unit: reserving one extra unit gives (qh + 1)/|Pfx|
    for a reduction with qh forwarded queries and one terminal check.

    The potential is the unused query budget plus the number of stored
    points whose separators remain unused, divided by |Pfx|. A query
    adds at most the unit it consumes. Reprogramming removes an entire
    separator slice, paying for every prefix that could cause a bad
    event. No factor depending on the number of signatures is needed. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import probability ro_plus reprogram.

From mathcomp Require Import reals distr realsum.

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section Game.

Context (Pfx X R I : choice_type) (sep : X -> I).
Context (dPfx : dist Pfx) (dR : dist R) (qh : nat).

Definition ro_used_loc : Location := mkloc 1205 ([::] : chList I).

Definition RO_repro_sep (b : bool) : game (I_RO Pfx X R) :=
  [package [fmap ro_map_loc Pfx X R; ro_qcnt_loc; ro_used_loc] ;
    [ QUERY ] : { Pfx × X ~> R } (q) {
      used ← get ro_used_loc ;;
      qc ← get ro_qcnt_loc ;;
      #assert ((sep q.2 \in used) || (qc < qh)%N) ;;
      #put ro_qcnt_loc := (qc + (sep q.2 \notin used))%N ;;
      m ← get (ro_map_loc Pfx X R) ;;
      match getm m q with
      | Some y => ret y
      | None =>
          y ← dR ;;
          #put (ro_map_loc Pfx X R) := setm m q y ;;
          ret y
      end
    } ;
    [ REPRO ] : { X ~> Pfx } (x) {
      used ← get ro_used_loc ;;
      #assert (sep x \notin used) ;;
      #put ro_used_loc := sep x :: used ;;
      r ← dPfx ;;
      if b then
        m ← get (ro_map_loc Pfx X R) ;;
        y ← dR ;;
        #put (ro_map_loc Pfx X R) := setm m (r, x) y ;;
        ret r
      else
        ret r
    }
  ].

End Game.

(* ------------------------------------------------------------------ *)
(** ** Finite-set accounting *)

Section Counting.
Context {K : ordType}.

Lemma count_fsetU1 (p : pred K) (x : K) (s : {fset K}) :
  count p (x |` s) = (((x \notin s) && p x) + count p s)%N.
Proof.
case hx: (x \in s).
- have -> : x |` s = s by apply/fsetUidPr; rewrite fsub1set hx.
  by rewrite /= add0n.
- rewrite -!sum1_count big_fsetU1 ?hx //=.
  by case: (p x); rewrite ?add0n.
Qed.

End Counting.

Section Accounting.
Context (Pfx X R I : choice_type) (sep : X -> I).

Definition pending (used : seq I) (m : chMap (Pfx × X) R) : nat :=
  count (fun p => sep p.2 \notin used) (domm m).

Definition slice (x : X) (m : chMap (Pfx × X) R) : nat :=
  count (fun p => sep p.2 == sep x) (domm m).

Lemma pending_repro (used : seq I) (m : chMap (Pfx × X) R) (x : X) :
  sep x \notin used ->
  pending used m = (slice x m + pending (sep x :: used) m)%N.
Proof.
move=> hx; rewrite /pending /slice.
elim: (domm m : seq (chProd Pfx X)) => [|p ps IH] //=.
rewrite in_cons.
case E: (sep p.2 == sep x).
- move/eqP: E => E; rewrite E hx /= IH addSn.
  by rewrite !add0n add1n addSn.
- by rewrite /= IH addnCA.
Qed.

Lemma pending_set (used : seq I) (m : chMap (Pfx × X) R) (p : Pfx × X) y :
  (pending used (setm m p y) <= (sep p.2 \notin used) + pending used m)%N.
Proof.
rewrite /pending domm_set count_fsetU1.
apply: leq_add => //.
by case: (p \notin domm m); case: (sep p.2 \notin used).
Qed.

Lemma pending_set_used (used : seq I) (m : chMap (Pfx × X) R) (p : Pfx × X) y :
  sep p.2 \in used -> pending used (setm m p y) = pending used m.
Proof.
move=> hp; by rewrite /pending domm_set count_fsetU1 hp andbF add0n.
Qed.

Lemma sum_in_slice_le (n : nat) (enc : 'I_n.+1 -> Pfx)
  (henc : injective enc) (x : X) (m : chMap (Pfx × X) R) :
  ((\sum_(r : 'I_n.+1) (((enc r, x) \in domm m) : nat)) <= slice x m)%N.
Proof.
have -> : (\sum_(r : 'I_n.+1) (((enc r, x) \in domm m) : nat))%N
  = count (fun r => (enc r, x) \in domm m) (index_enum 'I_n.+1).
{ rewrite -sum1_count [in RHS]big_mkcond /=.
  by apply: eq_bigr => r _; case: ((enc r, x) \in domm m). }
rewrite /slice -!size_filter -(size_map (fun r : 'I_n.+1 => (enc r, x))).
apply: uniq_leq_size.
- rewrite map_inj_uniq; first by move=> a b [heq]; exact: henc heq.
  apply: filter_uniq.
  exact: index_enum_uniq.
- move=> p /mapP [r].
  rewrite mem_filter => /andP [hr _] ->.
  by rewrite mem_filter /= eqxx hr.
Qed.

End Accounting.

(* ------------------------------------------------------------------ *)
(** ** The one-point lazy sampling identity *)

Section SeparatedBound.
Context (n : nat) (Pfx X R I : choice_type) (sep : X -> I).
Context (dPfx : dist Pfx) (enc : 'I_n.+1 -> Pfx) (henc : injective enc).
Context (huniform : Pr_fst dPfx = dmargin enc (uniform n.+1).π2).
Context (dR : dist R) (dR_ll : LosslessCode dR) (qh : nat).
Abbreviation IRO := (I_RO Pfx X R).
Abbreviation Gm b := (RO_repro_sep Pfx X R I sep dPfx dR qh b).
Abbreviation mloc := (ro_map_loc Pfx X R).
Abbreviation qloc := ro_qcnt_loc.
Abbreviation uloc := (ro_used_loc I).
Abbreviation muR := (Pr_fst dR).

Lemma sep_neq_qm : qloc.1 != mloc.1. Proof. by []. Qed.
Lemma sep_neq_um : uloc.1 != mloc.1. Proof. by []. Qed.
Lemma sep_neq_uq : uloc.1 != qloc.1. Proof. by []. Qed.

Lemma sep_resolve_query (b : bool) (q : Pfx × X) :
  resolve (Gm b) (mkopsig QUERY (Pfx × X) R) q =
  (used ← get uloc ;;
   qc ← get qloc ;;
   #assert ((sep q.2 \in used) || (qc < qh)%N) ;;
   #put qloc := (qc + (sep q.2 \notin used))%N ;;
   m ← get mloc ;;
   match getm m q with
   | Some y => ret y
   | None => y ← dR ;; #put mloc := setm m q y ;; ret y
   end).
Proof. by rewrite /RO_repro_sep /resolve /= coerce_kleisliE. Qed.

Lemma sep_resolve_repro_false (x : X) :
  resolve (Gm false) (mkopsig REPRO X Pfx) x =
  (used ← get uloc ;;
   #assert (sep x \notin used) ;;
   #put uloc := sep x :: used ;;
   r ← dPfx ;;
   ret r).
Proof. by rewrite /RO_repro_sep /resolve /= coerce_kleisliE. Qed.

Lemma sep_resolve_repro_true (x : X) :
  resolve (Gm true) (mkopsig REPRO X Pfx) x =
  (used ← get uloc ;;
   #assert (sep x \notin used) ;;
   #put uloc := sep x :: used ;;
   r ← dPfx ;;
   m ← get mloc ;;
   y ← dR ;;
   #put mloc := setm m (r, x) y ;;
   ret r).
Proof. by rewrite /RO_repro_sep /resolve /= coerce_kleisliE. Qed.

Section Adversary.
Context (LA : Locations).
Context (sepL : fseparate LA [fmap mloc; qloc; uloc]).

Lemma sep_advloc_neq (l : Location) :
  fhas LA l ->
  [&& l.1 != mloc.1, l.1 != qloc.1 & l.1 != uloc.1].
Proof.
move=> hl.
have hn := notin_has_separate _ _ _ hl sepL.
rewrite domm_mkfmap !inE /= !negb_or in hn.
by case/and3P: hn => -> -> ->.
Qed.

Lemma sep_gf_presample {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IRO c) :
  ∀ (h : heap) (p : chProd Pfx X),
    p \notin domm (get_heap h mloc) →
    ∀ z,
      dfst (Pr_code (code_link c (Gm false)) h) z
      = (\dlet_(y <- muR)
           dfst (Pr_code (code_link c (Gm false)) (updm Pfx X R h p y))) z.
Proof.
induction VA as [a | o x k Ho Hk IH | l k Hl Hk IH
                | l v k Hl Hk IH | op k Hk IH].
- (* ret *)
  move=> h p hp z. cbn [code_link].
  rewrite dPr_ret. symmetry.
  transitivity ((\dlet_(_ <- muR) dunit a) z).
  { apply: eq_dlet_at => y. by rewrite dPr_ret. }
  by rewrite (Pr_fstC dR_ll).
- (* opr: QUERY / REPRO *)
  fmap_invert Ho.
  + (* QUERY, argument x *)
    move=> h p hp z. cbn [code_link].
    rewrite sep_resolve_query. cbn [bind].
    rewrite !Pr_code_get.
    case E: (((sep x.2 \in get_heap h uloc) || (get_heap h qloc < qh)%N)%B); last first.
    { (* query budget exhausted: both sides fail *)
      rewrite assertD_false dPr_bind_fail. symmetry.
      apply: dlet_at0 => y.
      rewrite !Pr_code_get /updm !get_set_heap_neq //.
      by rewrite E assertD_false dPr_bind_fail. }
    rewrite assertD_true. cbn [bind].
    rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
    set qc := get_heap h qloc.
    set M := get_heap h mloc.
    set h1 := set_heap h qloc (qc + (sep x.2 \notin get_heap h uloc))%N.
    case Eq: (getm M x) => [y0 |].
    * (* answered from the map: x <> p, recurse *)
      have xnp : x != p.
      { apply: contraNneq hp => <-. by rewrite mem_domm Eq. }
      have hp1 : p \notin domm (get_heap h1 mloc).
      { by rewrite get_set_heap_neq. }
      cbn [bind].
      rewrite (IH y0 h1 p hp1 z).
      apply: eq_dlet_at => y.
      rewrite !Pr_code_get /(updm Pfx X R h p y) !get_set_heap_neq // E.
      rewrite assertD_true. cbn [bind].
      rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
      rewrite get_set_heap_eq setmE (negbTE xnp) Eq. cbn [bind].
      rewrite /updm get_set_heap_neq // -/M.
      by rewrite set_heap_commut.
    * (* not yet sampled *)
      rewrite bind_assoc. cbn [bind].
      rewrite dPr_dist.
      case: (eqVneq x p) => [xeqp | xnp].
      { (* x = p: the lazy sample IS the presample; no recursion *)
        rewrite -xeqp.
        apply: eq_dlet_at => y.
        rewrite Pr_code_put.
        rewrite !Pr_code_get /(updm Pfx X R h x y) !get_set_heap_neq // E.
        rewrite assertD_true. cbn [bind].
        rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
        rewrite get_set_heap_eq -/M setmE eqxx. cbn [bind].
        by rewrite set_heap_commut.
      }
      (* x <> p: recurse under the lazy sample, then swap *)
      have hpx : ∀ y', p \notin domm (setm M x y').
      { move=> y'. rewrite domm_set in_fset1U negb_or eq_sym xnp /=.
        exact: hp. }
      transitivity
        ((\dlet_(y' <- muR) \dlet_(y <- muR)
            dfst (Pr_code (code_link (k y') (Gm false))
                    (updm Pfx X R (set_heap h1 mloc (setm M x y')) p y))) z).
      { apply: eq_dlet_at => y'.
        rewrite Pr_code_put.
        apply: (IH y' _ p _ z).
        by rewrite get_set_heap_eq. }
      rewrite dlet_commut.
      apply: eq_dlet_at => y.
      rewrite !Pr_code_get /(updm Pfx X R h p y) !get_set_heap_neq // E.
      rewrite assertD_true. cbn [bind].
      rewrite Pr_code_put Pr_code_get get_set_heap_neq //.
      rewrite get_set_heap_eq -/M setmE (negbTE xnp) Eq.
      rewrite bind_assoc. cbn [bind].
      rewrite dPr_dist.
      apply: eq_dlet_at => y'.
      rewrite Pr_code_put.
      rewrite /updm get_set_heap_eq set_heap_contract.
      rewrite (setmC _ _ _ xnp).
      rewrite [in X in _ = X]set_heap_commut //.
      rewrite [in X in _ = X]set_heap_contract.
      by rewrite /h1 set_heap_commut.
  + (* REPRO records the separator but leaves the oracle map unchanged. *)
    move=> h p hp z. cbn [code_link].
    rewrite sep_resolve_repro_false. cbn [bind].
    rewrite Pr_code_get.
    case Er: (sep x \notin get_heap h uloc); last first.
    { rewrite assertD_false dPr_bind_fail. symmetry.
      apply: dlet_at0 => y.
      rewrite !Pr_code_get /updm !get_set_heap_neq //.
      by rewrite Er assertD_false dPr_bind_fail. }
    rewrite assertD_true. cbn [bind].
    rewrite Pr_code_put.
    set used := get_heap h uloc.
    set h1 := set_heap h uloc (sep x :: used).
    rewrite ?bind_ret dPr_dist.
    have hp1 : p \notin domm (get_heap h1 mloc).
    { by rewrite get_set_heap_neq. }
    transitivity
      ((\dlet_(r <- Pr_fst dPfx) \dlet_(y <- muR)
          dfst (Pr_code (code_link (k r) (Gm false)) (updm Pfx X R h1 p y))) z).
    { apply: eq_dlet_at => r. exact: (IH r h1 p hp1 z). }
    rewrite dlet_commut.
    apply: eq_dlet_at => y.
    rewrite !Pr_code_get /(updm Pfx X R h p y) !get_set_heap_neq // Er.
    rewrite assertD_true. cbn [bind].
    rewrite Pr_code_put.
    rewrite ?bind_ret dPr_dist.
    apply: eq_dlet_at => r.
    rewrite /updm get_set_heap_neq //.
    by rewrite set_heap_commut.
- (* getr (adversary location) *)
  move=> h p hp z. cbn [code_link].
  case/and3P: (sep_advloc_neq _ Hl) => nm nq nr.
  rewrite Pr_code_get (IH _ h p hp z).
  apply: eq_dlet_at => y.
  rewrite !Pr_code_get /updm !get_set_heap_neq //.
- (* putr (adversary location) *)
  move=> h p hp z. cbn [code_link].
  case/and3P: (sep_advloc_neq _ Hl) => nm nq nr.
  have hp' : p \notin domm (get_heap (set_heap h l v) mloc).
  { by rewrite get_set_heap_neq // eq_sym. }
  rewrite Pr_code_put (IH (set_heap h l v) p hp' z).
  apply: eq_dlet_at => y.
  by rewrite Pr_code_put updm_set_heap.
- (* sampler *)
  move=> h p hp z. cbn [code_link].
  rewrite dPr_sample.
  transitivity
    ((\dlet_(a <- op.π2) \dlet_(y <- muR)
        dfst (Pr_code (code_link (k a) (Gm false)) (updm Pfx X R h p y))) z).
  { apply: eq_dlet_at => a. exact: (IH a h p hp z). }
  rewrite dlet_commut.
  apply: eq_dlet_at => y.
  by rewrite dPr_sample.
Qed.

Definition sep_potential (h : heap) : Axioms.R :=
  (qh - get_heap h qloc +
   pending Pfx X R I sep (get_heap h uloc) (get_heap h mloc))%:R / n.+1%:R.

Lemma sep_potential_ge0 h : 0 <= sep_potential h.
Proof. by rewrite /sep_potential divr_ge0 ?ler0n. Qed.
Lemma sep_query_credit (qc t a : nat) (fresh : bool) :
  (qc <= qh)%N -> (~~ fresh || (qc < qh)%N)%B ->
  (t <= fresh + a)%N ->
  (qc + fresh <= qh)%N /\ (qh - (qc + fresh) + t <= qh - qc + a)%N.
Proof.
case: fresh => /= hqc hcap ht.
- rewrite addn1; split; first exact: hcap.
  apply: leq_trans (leq_add (leqnn _) ht) _.
  by rewrite add1n addnS -(subnSK hcap).
- rewrite addn0; split; first exact: hqc.
  exact: leq_add (leqnn _) ht.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Amortized identical-until-bad bound *)

Lemma sep_gt_gf_diff {T' : choiceType} {c : raw_code T'}
    (VA : ValidCode LA IRO c) :
  forall h, (get_heap h qloc <= qh)%N -> forall z,
    `| dfst (Pr_code (code_link c (Gm true)) h) z
     - dfst (Pr_code (code_link c (Gm false)) h) z |
    <= sep_potential h.
Proof.
induction VA as [a | o x k Ho Hk IH | l k Hl Hk IH
                | l v k Hl Hk IH | op k Hk IH].
- move=> h hqc z; cbn [code_link].
  rewrite subrr normr0; exact: sep_potential_ge0.
- (* Each oracle call preserves the amortized discrepancy bound. *)
  fmap_invert Ho.
  + (* Query credit bounds the cached and fresh-query continuations. *)
    move=> h hqc z; cbn [code_link].
    rewrite !sep_resolve_query; cbn [bind].
    rewrite !Pr_code_get.
    case E: (((sep x.2 \in get_heap h uloc) || (get_heap h qloc < qh)%N)%B); last first.
    { rewrite !assertD_false !dPr_bind_fail subrr normr0.
      exact: sep_potential_ge0. }
    rewrite !assertD_true; cbn [bind].
    rewrite !Pr_code_put !Pr_code_get !get_set_heap_neq //.
    set used := get_heap h uloc.
    set qc := get_heap h qloc.
    set M := get_heap h mloc.
    set fresh := sep x.2 \notin used.
    set h1 := set_heap h qloc (qc + fresh)%N.
    have cap : (~~ fresh || (qc < qh)%N)%B by rewrite /fresh negbK.
    case Eq: (getm M x) => [y0 |].
    * (* A cached query consumes no fresh random-oracle sample. *)
      cbn [bind].
      have [hq1 hp1] := sep_query_credit qc
        (pending Pfx X R I sep used M) (pending Pfx X R I sep used M) fresh
        hqc cap (leq_addl _ _).
      apply: le_trans (IH y0 h1 _ z) _.
      { by rewrite /h1 get_set_heap_eq. }
      rewrite /sep_potential /h1 get_set_heap_eq !get_set_heap_neq //.
      apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
      by rewrite ler_nat.
    * (* A fresh query updates the table and its remaining allowance. *)
      rewrite !bind_assoc; cbn [bind].
      rewrite !dPr_dist.
      apply: dlet_diff_le; first exact: sep_potential_ge0.
      move=> y; rewrite !Pr_code_put.
      have [hq1 hp1] := sep_query_credit qc
        (pending Pfx X R I sep used (setm M x y)) (pending Pfx X R I sep used M) fresh
        hqc cap (pending_set Pfx X R I sep used M x y).
      apply: le_trans (IH y (set_heap h1 mloc (setm M x y)) _ z) _.
      { by rewrite get_set_heap_neq // /h1 get_set_heap_eq. }
      rewrite /sep_potential /h1 get_set_heap_eq.
      rewrite !(get_set_heap_neq _ mloc) // get_set_heap_eq.
      rewrite !(get_set_heap_neq _ qloc) //.
      apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
      by rewrite ler_nat.
  + (* A fresh separator pays for the reprogramming discrepancy. *)
    move=> h hqc z; cbn [code_link].
    rewrite sep_resolve_repro_true sep_resolve_repro_false; cbn [bind].
    rewrite !Pr_code_get.
    case Er: (sep x \notin get_heap h uloc); last first.
    { rewrite !assertD_false !dPr_bind_fail subrr normr0.
      exact: sep_potential_ge0. }
    rewrite !assertD_true; cbn [bind].
    rewrite !Pr_code_put !bind_assoc; cbn [bind].
    rewrite ?bind_ret !dPr_dist.
    set used := get_heap h uloc.
    set M := get_heap h mloc.
    set h1 := set_heap h uloc (sep x :: used).
    set c' := sep_potential h1.
    have c'_ge0 : 0 <= c' by exact: sep_potential_ge0.
    have hcnt := sum_in_slice_le Pfx X R I sep n enc henc x M.
    have HU := uniform_split_encoded n Pfx dPfx enc huniform
      _ _ (fun r => (r, x) \in domm M) _ _ _ c'_ge0 _ hcnt.
    apply: le_trans (HU _ _ _ _ _) _.
    * (* An unqueried prefix permits coupling to a fresh sample. *)
      move=> r hgood.
      rewrite Pr_code_get get_set_heap_neq // -/M.
      rewrite bind_assoc; cbn [bind].
      rewrite dPr_dist.
      have hfresh : (r, x) \notin domm (get_heap h1 mloc).
      { by rewrite /h1 get_set_heap_neq. }
      rewrite (sep_gf_presample (Hk r) _ _ hfresh z).
      apply: dlet_diff_le; first exact: c'_ge0.
      move=> y; rewrite Pr_code_put /updm get_set_heap_neq // -/M.
      apply: le_trans (IH r (set_heap h1 mloc (setm M (r, x) y)) _ z) _.
      { by rewrite get_set_heap_neq // /h1 get_set_heap_neq. }
      rewrite /c' /sep_potential /h1 get_set_heap_eq.
      rewrite !(get_set_heap_neq _ mloc) // get_set_heap_eq.
      rewrite !(get_set_heap_neq _ uloc) //.
      rewrite pending_set_used; last exact: lexx.
      by rewrite /= in_cons eqxx.
    * (* The reprogramming allowance covers the remaining potential. *)
      rewrite /c' /sep_potential /h1 get_set_heap_eq.
      rewrite !(get_set_heap_neq _ uloc) //.
      rewrite -mulrDl -natrD.
      rewrite (pending_repro Pfx X R I sep used M x Er).
      by rewrite addnCA.
- move=> h hqc z; cbn [code_link].
  rewrite !Pr_code_get; exact: (IH _ h hqc z).
- (* Adversary writes preserve the query counter and potential. *)
  move=> h hqc z; cbn [code_link].
  case/and3P: (sep_advloc_neq _ Hl) => nm nq nu.
  rewrite !Pr_code_put.
  have hqc' : (get_heap (set_heap h l v) qloc <= qh)%N.
  { by rewrite get_set_heap_neq // eq_sym. }
  apply: le_trans (IH _ hqc' z) _.
  by rewrite /sep_potential !get_set_heap_neq // eq_sym.
- move=> h hqc z; cbn [code_link].
  rewrite !dPr_sample.
  apply: dlet_diff_le; first exact: sep_potential_ge0.
  move=> a; exact: (IH a h hqc z).
Qed.

End Adversary.

(* ------------------------------------------------------------------ *)
(** ** Advantage bounds *)

(** Only QUERY calls at an as-yet unused separator consume [qh].
    All REPRO separator checks precede the game bit. There is no cap
    on REPRO calls beyond separator uniqueness. QUERY uses the same
    lazy map as RO_repro, with its quota refined to charge only unused
    separators; this admits every execution obeying a total-query cap
    of qh, and additionally admits free read-backs. No bound is
    assumed of the adversary's distinguishing advantage. *)
Lemma repro_sep_bound_uniform (A : nom_package)
    (VA : ValidPackage (loc A) IRO A_export A) :
  AdvOf (RO_repro_sep Pfx X R I sep dPfx dR qh) A
  <= qh%:R / n.+1%:R.
Proof.
apply: (Adv_nom_ind _ _ _ IRO (fun x : Axioms.R => x <= qh%:R / n.+1%:R)) => //.
move=> A' LA' VA' _ sep1 sep2.
rewrite /AdvantageE.
have hRUN : fhas A_export RUN by fmap_solve.
have VC := valid_resolve _ _ _ _ RUN tt VA' hRUN.
have hqc0 : (get_heap empty_heap qloc <= qh)%N by exact: leq0n.
rewrite 2!Pr_Pr_code 2!resolve_link.
apply: le_trans (sep_gt_gf_diff LA' sep1 VC empty_heap hqc0 true) _.
rewrite /sep_potential /pending /= subn0.
have -> : get_heap empty_heap mloc = emptym by [].
by rewrite domm0 /= addn0.
Qed.

End SeparatedBound.

(** Finite-carrier form used by byte-prefix samplers. *)
Lemma repro_sep_bound_finite (N : nat) (hN : (0 < N)%N)
  (Pfx X R I : choice_type) (sep : X -> I)
  (dPfx : dist Pfx) (enc : 'I_N -> Pfx) (henc : injective enc)
  (huniform : Pr_fst dPfx = dmargin enc (uniform N).π2)
  (dR : dist R) (dR_ll : LosslessCode dR) (qh : nat)
  (A : nom_package) (VA : ValidPackage (loc A) (I_RO Pfx X R) A_export A) :
  AdvOf (RO_repro_sep Pfx X R I sep dPfx dR qh) A <= qh%:R / N%:R.
Proof.
case: N hN enc henc huniform => [|n] hN enc henc huniform //.
exact: (repro_sep_bound_uniform n Pfx X R I sep dPfx enc henc huniform
  dR dR_ll qh A VA).
Qed.

(** Ordinal specialization of the carrier-independent comparison. *)
Lemma repro_sep_bound (n : nat) (X R I : choice_type) (sep : X -> I)
  (dR : dist R) (dR_ll : LosslessCode dR) (qh : nat)
  (A : nom_package)
  (VA : ValidPackage (loc A) (I_RO (chFin n.+1) X R) A_export A) :
  AdvOf (RO_repro_sep (chFin n.+1) X R I sep (rp_d_pfx n) dR qh) A
  <= qh%:R / n.+1%:R.
Proof.
exact: (repro_sep_bound_uniform n (chFin n.+1) X R I sep
  (rp_d_pfx n) id (fun x y h => h) (rp_d_pfx_uniform n)
  dR dR_ll qh A VA).
Qed.

(** A reduction forwarding [qh] queries can reserve one additional
    query for a terminal check at an unused separator. Read-backs at
    used separators need no reservation. *)
Corollary repro_sep_bound_with_terminal
    (n : nat) (X R I : choice_type) (sep : X -> I)
    (dR : dist R) (dR_ll : LosslessCode dR) (qh : nat)
    (A : nom_package)
    (VA : ValidPackage (loc A) (I_RO (chFin n.+1) X R) A_export A) :
  AdvOf (RO_repro_sep (chFin n.+1) X R I sep (rp_d_pfx n) dR qh.+1) A
  <= (qh + 1)%:R / n.+1%:R.
Proof.
rewrite addn1.
exact: (repro_sep_bound n X R I sep dR dR_ll qh.+1 A VA).
Qed.

(* Micro-test: two distinct reprogrammings and their read-backs fit a
   zero pre-query budget, and have zero distinguishing advantage. *)
Module ReprogramSepTest.

Definition readbacks : package (I_RO (chFin 3) 'nat 'bool) A_export :=
  [package emptym ;
    [ 0%N ] : { 'unit ~> 'bool } (_) {
      r0 ← call [ REPRO ] : { 'nat ~> chFin 3 } 0%N ;;
      y0 ← call [ QUERY ] : { chFin 3 × 'nat ~> 'bool } (r0, 0%N) ;;
      r1 ← call [ REPRO ] : { 'nat ~> chFin 3 } 1%N ;;
      y1 ← call [ QUERY ] : { chFin 3 × 'nat ~> 'bool } (r1, 1%N) ;;
      ret (xorb y0 y1)
    }
  ].

Lemma readbacks_bound :
  AdvOf (RO_repro_sep (chFin 3) 'nat 'bool 'nat id
    (rp_d_pfx 2) ROPlusTest.dB 0) readbacks <= 0.
Proof.
have H := repro_sep_bound 2 'nat 'bool 'nat id
  ROPlusTest.dB ReprogramTest.dB_ll 0 readbacks (pack_valid readbacks).
by move: H; rewrite mulr0n mul0r.
Qed.

End ReprogramSepTest.
