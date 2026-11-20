(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.fill_avoid

    Independent uniform fills of a finite map avoid a fixed bad value
    set except with loss at most [size js * size S / (n + 1)].
    [fill_split_uniform_le] lifts a bound on safe continuations through the fills.
    Keys are arbitrary; repeated keys and overwrites are allowed.
    The sampler reuses [sample_seq], followed by a pure fold into the map.
    Finite values use a proved injective uniform enumeration. The ordinal
    specializations retain [chFin n.+1]; the generic bounds also accept
    byte-tuple samplers. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import sample_seq probability.

From mathcomp Require Import reals distr realsum.

Import PackageNotation.
Import Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FillCode.

Context {K D : choice_type} (d : dist D).

Definition fill_code (js : seq K) (m0 : chMap K D) : raw_code (chMap K D) :=
  ys ← sample_seq d (size js) ;;
  ret (foldl (fun m kv => setm m kv.1 kv.2) m0 (zip js ys)).

#[export] Instance fill_code_valid (L : Locations) (I : Interface)
    (js : seq K) (m0 : chMap K D) : ValidCode L I (fill_code js m0).
Proof.
apply valid_bind.
- exact: sample_seq_valid.
- move=> ys; apply valid_ret.
Qed.

Lemma fill_code_nil (m0 : chMap K D) : fill_code [::] m0 = ret m0.
Proof. by []. Qed.

Lemma fill_code_cons (j : K) (js : seq K) (m0 : chMap K D) :
  fill_code (j :: js) m0 = (y ← d ;; fill_code js (setm m0 j y)).
Proof.
rewrite /fill_code /= bind_assoc.
congr (bind _ _).
apply functional_extensionality => y.
by rewrite bind_assoc.
Qed.

End FillCode.

Section FillAvoid.

Context {K : choice_type} (n : nat) (D : choice_type) (d : dist D).
Context (enc : 'I_n.+1 -> D) (henc : injective enc).
Context (huniform : Pr_fst d = dmargin enc (uniform n.+1).π2).

Lemma fill_dlet_cons_uniform {T : choiceType} (j : K) (js : seq K)
  (m0 : chMap K D) (G : chMap K D -> {distr T / Axioms.R}) (z : T) :
  (\dlet_(sd <- Pr_fst (fill_code d (j :: js) m0)) G sd) z =
  (\dlet_(y <- Pr_fst d)
    \dlet_(sd <- Pr_fst (fill_code d js (setm m0 j y))) G sd) z.
Proof.
by rewrite fill_code_cons Pr_fst_bind // dlet_dlet_ext.
Qed.

Lemma sum_encoded_in_fset (S : {fset D}) :
  ((\sum_(r : 'I_n.+1) ((enc r \in S) : nat)) <= size S)%N.
Proof.
exact: (sum_in_fset_le enc S henc).
Qed.

(** Safe continuations differ by at most [c]; each fresh fill adds
    at most [size S / (n + 1)] to their pointwise probability difference. *)
Lemma fill_split_uniform_le {T : choiceType} (js : seq K) (S : {fset D})
    (c : Axioms.R) (z : T) :
  0 <= c ->
  forall (m0 : chMap K D) (G0 G1 : chMap K D -> {distr T / Axioms.R}),
  (forall v, v \in codomm m0 -> v \notin S) ->
  (forall sd, (forall v, v \in codomm sd -> v \notin S) ->
    (size (domm sd) <= size (domm m0) + size js)%N ->
    `|G0 sd z - G1 sd z| <= c) ->
  `|(\dlet_(sd <- Pr_fst (fill_code d js m0)) G0 sd) z
    - (\dlet_(sd <- Pr_fst (fill_code d js m0)) G1 sd) z|
  <= (size js)%:R * (size S)%:R / n.+1%:R + c.
Proof.
move=> hc.
elim: js => [|j js ih] m0 G0 G1 hm0 hgood.
- rewrite fill_code_nil Pr_fst_ret 2!dlet_unit_ext /=.
  rewrite mul0r mul0r GRing.add0r.
  apply: (hgood m0 hm0).
  by rewrite addn0.
- rewrite 2!fill_dlet_cons_uniform.
  set c' := (size js)%:R * (size S)%:R / n.+1%:R + c.
  have hc' : 0 <= c'.
  { rewrite /c'.
    apply: addr_ge0 => //.
    by rewrite divr_ge0 ?ler0n // mulr_ge0 ?ler0n. }
  have hu := uniform_split_encoded n D d enc huniform
    (fun y : D => \dlet_(sd <- Pr_fst (fill_code d js (setm m0 j y))) G0 sd)
    (fun y : D => \dlet_(sd <- Pr_fst (fill_code d js (setm m0 j y))) G1 sd)
    (fun r : D => r \in S) z c' (size S) hc'.
  apply: le_trans (hu _ _) _.
  + (* Safe sample: extend the map and use the induction hypothesis. *)
    move=> r hr.
    have hm0' : forall v, v \in codomm (setm m0 j r) -> v \notin S.
    { move=> v /codommP [k hk].
      move: hk; rewrite setmE; case: eqP => [_ [<-] | _ hk].
      - by rewrite -[r \in S]/(r \in S : bool) (negbTE hr).
      - apply: hm0.
        apply/codommP.
        by exists k. }
    apply: (ih (setm m0 j r) G0 G1 hm0').
    move=> sd hsd hszsd.
    apply: hgood => //.
    apply: leq_trans hszsd _.
    rewrite domm_set sizesU1 -addnA [size (j :: js)]/= addnS.
    apply: leq_trans (leq_add (leq_b1 (j \notin domm m0)) (leqnn _)) _.
    by rewrite add1n.
  + exact: sum_encoded_in_fset.
  + (* The remaining sum fits within the updated collision allowance. *)
    rewrite /c' /= addrA.
    apply: lerD; last exact: lexx.
    rewrite -mulrDl.
    apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
    by rewrite -natr1 mulrDl mul1r addrC.
Qed.

(** Probability that the filled map contains a bad value.  The initial
    map must avoid [S]; no freshness or uniqueness condition on [js] is needed. *)
Lemma fill_bad_uniform_le (js : seq K) (S : {fset D}) (m0 : chMap K D) :
  (forall v, v \in codomm m0 -> v \notin S) ->
  Pr_fst (sd ← fill_code d js m0 ;;
          ret (has (mem S) (codomm sd))) true
  <= (size js)%:R * (size S)%:R / n.+1%:R.
Proof.
move=> hm0.
have hgood : forall sd : chMap K D,
    (forall v, v \in codomm sd -> v \notin S) ->
    (size (domm sd) <= size (domm m0) + size js)%N ->
    `|dunit (has (mem S) (codomm sd)) true - dunit false true|
      <= (0 : Axioms.R).
{ move=> sd hsd _.
  have hbad : has (mem S) (codomm sd) = false.
  { apply/negbTE/hasPn => v hv.
    exact: hsd v hv. }
  by rewrite hbad subrr normr0. }
have hbound := fill_split_uniform_le js S 0 true (lexx _) m0
  (fun sd => dunit (has (mem S) (codomm sd)))
  (fun _ => dunit false) hm0 hgood.
have hzero : (\dlet_(_ <- Pr_fst (fill_code d js m0)) dunit false) true = 0.
{ apply: dlet_at0 => sd.
  by rewrite dunit1E. }
rewrite hzero subr0 addr0 in hbound.
rewrite Pr_fst_bind //.
have -> : (\dlet_(sd <- Pr_fst (fill_code d js m0))
    Pr_fst (ret (has (mem S) (codomm sd))))
  = (\dlet_(sd <- Pr_fst (fill_code d js m0))
    dunit (has (mem S) (codomm sd))).
{ apply: eq_dlet => sd.
  by rewrite Pr_fst_ret. }
exact: le_trans (ler_norm _) hbound.
Qed.

End FillAvoid.

Section OrdinalFill.
Context {K : choice_type} (n : nat).
Local Abbreviation D := (chFin n.+1).
Local Abbreviation d := (rp_d_pfx n).

Lemma fill_dlet_cons {T : choiceType} (j : K) (js : seq K)
    (m0 : chMap K D) (G : chMap K D -> {distr T / Axioms.R}) (z : T) :
  (\dlet_(sd <- Pr_fst (fill_code d (j :: js) m0)) G sd) z
  = (\dlet_(y <- (uniform n.+1).π2)
       \dlet_(sd <- Pr_fst (fill_code d js (setm m0 j y))) G sd) z.
Proof.
rewrite fill_code_cons (Pr_fst_bind (c := d)) //.
rewrite dlet_dlet_ext.
have hd : Pr_fst d = \dlet_(r <- (uniform n.+1).π2) dunit r.
{ by rewrite /rp_d_pfx Pr_fst_sample;
    apply: eq_dlet => r; rewrite Pr_fst_ret. }
rewrite hd dlet_dlet_ext.
apply: eq_dlet_at => y.
by rewrite dlet_unit_ext.
Qed.

Lemma sum_ord_in_fset (S : {fset D}) :
  ((\sum_(r : 'I_n.+1) ((r \in S) : nat)) <= size S)%N.
Proof.
exact: (sum_in_fset_le (fun r : 'I_n.+1 => r) S (fun a b e => e)).
Qed.

Lemma fill_split_le {T : choiceType} (js : seq K) (S : {fset D})
    (c : Axioms.R) (z : T) :
  0 <= c ->
  forall (m0 : chMap K D) (G0 G1 : chMap K D -> {distr T / Axioms.R}),
  (forall v, v \in codomm m0 -> v \notin S) ->
  (forall sd, (forall v, v \in codomm sd -> v \notin S) ->
    (size (domm sd) <= size (domm m0) + size js)%N ->
    `|G0 sd z - G1 sd z| <= c) ->
  `|(\dlet_(sd <- Pr_fst (fill_code d js m0)) G0 sd) z
    - (\dlet_(sd <- Pr_fst (fill_code d js m0)) G1 sd) z|
  <= (size js)%:R * (size S)%:R / n.+1%:R + c.
Proof.
exact: (fill_split_uniform_le n D d id (fun x y h => h)
  (rp_d_pfx_uniform n) js S c z).
Qed.

Lemma fill_bad_le (js : seq K) (S : {fset D}) (m0 : chMap K D) :
  (forall v, v \in codomm m0 -> v \notin S) ->
  Pr_fst (sd ← fill_code d js m0 ;;
          ret (has (mem S) (codomm sd))) true
  <= (size js)%:R * (size S)%:R / n.+1%:R.
Proof.
exact: (fill_bad_uniform_le n D d id (fun x y h => h)
  (rp_d_pfx_uniform n) js S m0).
Qed.
End OrdinalFill.

(** Nonempty finite carriers, including byte tuples. *)
Lemma fill_bad_finite_le {K : choice_type} (N : nat) (hN : (0 < N)%N)
  (D : choice_type) (d : dist D) (enc : 'I_N -> D) (henc : injective enc)
  (huniform : Pr_fst d = dmargin enc (uniform N).π2)
  (js : seq K) (S : {fset D}) (m0 : chMap K D) :
  (forall v, v \in codomm m0 -> v \notin S) ->
  Pr_fst (sd ← fill_code d js m0 ;;
    ret (has (mem S) (codomm sd))) true
  <= (size js)%:R * (size S)%:R / N%:R.
Proof.
case: N hN enc henc huniform => [|n] hN enc henc huniform //.
exact: (fill_bad_uniform_le n D d enc henc huniform js S m0).
Qed.

Lemma fill_split_finite_le {K : choice_type} (N : nat) (hN : (0 < N)%N)
  (D : choice_type) (d : dist D) (enc : 'I_N -> D) (henc : injective enc)
  (huniform : Pr_fst d = dmargin enc (uniform N).π2)
  {T : choiceType} (js : seq K) (S : {fset D}) (c : Axioms.R) (z : T) :
  0 <= c ->
  forall (m0 : chMap K D) (G0 G1 : chMap K D -> {distr T / Axioms.R}),
  (forall v, v \in codomm m0 -> v \notin S) ->
  (forall sd, (forall v, v \in codomm sd -> v \notin S) ->
    (size (domm sd) <= size (domm m0) + size js)%N ->
    `|G0 sd z - G1 sd z| <= c) ->
  `|(\dlet_(sd <- Pr_fst (fill_code d js m0)) G0 sd) z
    - (\dlet_(sd <- Pr_fst (fill_code d js m0)) G1 sd) z|
  <= (size js)%:R * (size S)%:R / N%:R + c.
Proof.
case: N hN enc henc huniform => [|n] hN enc henc huniform //.
exact: (fill_split_uniform_le n D d enc henc huniform js S c z).
Qed.
