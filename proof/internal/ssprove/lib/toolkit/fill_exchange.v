(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.fill_exchange

    Exchange an adaptively selected fresh entry of an independent finite
    map fill with an immediate sample. Keys and value carriers are generic. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import probability fill_avoid.
From mathcomp Require Import reals distr realsum.

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FillExchange.
Context {K D : choice_type} (d : dist D).
Lemma fill_union_setm (js : seq K) (j : K) (y : D)
    {Tz : choiceType} (G0 : chMap K D -> {distr Tz / Axioms.R})
    (z : Tz) :
  forall (sd0 m0 : chMap K D),
    j \notin js ->
    j \notin domm sd0 ->
    (forall k, k \in js -> k \notin domm sd0) ->
    (\dlet_(rest <- Pr_fst (fill_code d js (setm m0 j y)))
        G0 (unionm sd0 rest)) z
    = (\dlet_(rest <- Pr_fst (fill_code d js m0))
          G0 (unionm (setm sd0 j y) rest)) z.
Proof.
elim: js => [|a js IH] sd0 m0 hj hjd hkd.
- rewrite !fill_code_nil. rewrite 2!Pr_fst_ret 2!dlet_unit_ext.
  congr (G0 _ z).
  have hsd0j : sd0 j = None.
  { by apply/dommPn. }
  apply/eq_fmap => k. rewrite 2!unionmE.
  rewrite (setmE m0) (setmE sd0).
  case: (eqVneq k j) => [-> | kj].
  + rewrite hsd0j /=.
    by case: (m0 j).
  + by case: (sd0 k).
- (* The head update commutes with the distinct distinguished key. *)
  have hcons : forall (m : chMap K D),
    fill_code d (a :: js) m = (y ← d ;; fill_code d js (setm m a y)).
  { exact: fill_code_cons. }
  rewrite (hcons (setm m0 j y)) (hcons m0).
  rewrite Pr_fst_bind.
  rewrite Pr_fst_bind.
  rewrite (dlet_dlet_ext (t := Pr_fst d)).
  rewrite [in X in _ = X](dlet_dlet_ext (t := Pr_fst d)).
  apply: eq_dlet_at => v.
  have ha : a \notin domm sd0 by apply: hkd; rewrite inE eqxx.
  have hja : j != a by move: hj; rewrite inE negb_or => /andP[].
  have hjjs : j \notin js by move: hj; rewrite inE negb_or => /andP[].
  rewrite (@setmC _ _ m0 j y a v hja).
  apply: (IH sd0 (setm m0 a v) hjjs hjd).
  move=> k hk. apply: hkd. by rewrite inE hk orbT.
Qed.

(** Peel an arbitrary unconsumed slot from an independently sampled table. *)
Lemma fill_peel_at {Tz : choiceType} (j : K) :
  forall (js : seq K) (sd0 : chMap K D)
         (G0 : chMap K D -> {distr Tz / Axioms.R}) (z : Tz),
  j \in js -> uniq js ->
  (forall k, k \in js -> k \notin domm sd0) ->
  (\dlet_(rest <- Pr_fst (fill_code d js emptym)) G0 (unionm sd0 rest)) z
  = (\dlet_(y <- Pr_fst d)
       \dlet_(rest <- Pr_fst (fill_code d (rem j js) emptym))
          G0 (unionm (setm sd0 j y) rest)) z.
Proof.
elim=> [|a js IH] sd0 G0 z hj huniq hkd; first by move: hj; rewrite in_nil.
move: huniq => /andP[hanotin huniq].
have hconsL : fill_code d (a :: js) emptym
  = (y ← d ;; fill_code d js (setm emptym a y)) by rewrite fill_code_cons.
rewrite hconsL Pr_fst_bind (dlet_dlet_ext (t := Pr_fst d)).
have had : a \notin domm sd0 by apply: hkd; rewrite inE eqxx.
case: (eqVneq a j) => [<- | haj].
- (* j = a : head peel, no swap needed *)
  apply: eq_dlet_at => y.
  have hrem : rem a (a :: js) = js by rewrite /= eqxx.
  rewrite hrem.
  apply: (fill_union_setm js a y G0 z sd0 emptym hanotin had).
  move=> k hk. apply: hkd. by rewrite inE hk orbT.
- (* j != a : prefix-absorb, IH, dlet swap, refold *)
  have hj' : j \in js.
  { move: hj; rewrite inE => /orP[/eqP e|//]. by move: haj; rewrite e eqxx. }
  have hrem : rem j (a :: js) = a :: rem j js by rewrite /= (negbTE haj).
  transitivity
    ((\dlet_(v <- Pr_fst d)
        \dlet_(y <- Pr_fst d)
          \dlet_(rest <- Pr_fst (fill_code d (rem j js) emptym))
             G0 (unionm (setm (setm sd0 a v) j y) rest)) z).
  { apply: eq_dlet_at => v.
    have htail : forall k, k \in js -> k \notin domm sd0.
    { move=> k hk. apply: hkd. by rewrite inE hk orbT. }
    rewrite (fill_union_setm js a v G0 z sd0 emptym hanotin had htail).
    apply: (IH (setm sd0 a v) G0 z hj' huniq).
    move=> k hk. rewrite domm_set in_fset1U negb_or.
    apply/andP; split.
    - by apply/eqP => e; move: hanotin; rewrite -e hk.
    - by apply: hkd; rewrite inE hk orbT. }
  rewrite dlet_commut.
  apply: eq_dlet_at => y.
  rewrite hrem.
  have hconsR : fill_code d (a :: rem j js) emptym
    = (v ← d ;; fill_code d (rem j js) (setm emptym a v)) by rewrite fill_code_cons.
  rewrite hconsR Pr_fst_bind (dlet_dlet_ext (t := Pr_fst d)).
  apply: eq_dlet_at => v.
  have hjrem : forall k, k \in rem j js -> (k != j) && (k \in js).
  { move=> k hk. by move: hk; rewrite (mem_rem_uniq _ huniq) inE => /andP[-> ->]. }
  rewrite (@setmC _ _ sd0 a v j y haj).
  rewrite (fill_union_setm (rem j js) a v G0 z (setm sd0 j y) emptym) //.
  - by apply/negP => /hjrem /andP[_ hin]; move: hanotin; rewrite hin.
  - rewrite domm_set in_fset1U negb_or haj /=. exact: had.
  - move=> k hk. move: (hjrem k hk) => /andP[hkj hkjs].
    rewrite domm_set in_fset1U negb_or hkj /=.
    by apply: hkd; rewrite inE hkjs orbT.
Qed.

Lemma fill_fresh_cons (j : K) (js : seq K) : j \notin js ->
  Pr_fst (fill_code d (j :: js) emptym) =
  \dlet_(y <- Pr_fst d)
    \dlet_(rest <- Pr_fst (fill_code d js emptym)) dunit (setm rest j y).
Proof.
move=> hj.
rewrite fill_code_cons Pr_fst_bind.
apply: eq_dlet => y.
apply/distr_ext => z.
have h0 : j \notin domm (emptym : chMap K D).
{ by rewrite domm0 in_fset0. }
have hs : forall k, k \in js -> k \notin domm (emptym : chMap K D).
{ by move=> k _; rewrite domm0 in_fset0. }
have he := fill_union_setm js j y (fun m : chMap K D => dunit m)
  z emptym emptym hj h0 hs.
cbn beta in he.
have hl : (fun rest : chMap K D => dunit (unionm emptym rest)) =
    (fun rest : chMap K D => dunit rest).
{ move=> R0. apply boolp.funext => rest. by rewrite union0m. }
have hr : (fun rest : chMap K D =>
    @dunit Axioms.R (chMap K D) (unionm (setm emptym j y) rest)) =
    (fun rest : chMap K D => @dunit Axioms.R (chMap K D) (setm rest j y)).
{ apply boolp.funext => rest. by rewrite -setm_union union0m. }
rewrite hl hr dlet_dunit_id in he.
exact he.
Qed.

Lemma fill_const (hdM : LosslessCode d)
    (js : seq K) (sd : chMap K D)
    {U : choiceType} (mu : {distr U / Axioms.R}) :
  (\dlet_(_ <- Pr_fst (fill_code d js sd)) mu) = mu.
Proof.
elim: js sd => [|j js IH] sd.
- by rewrite fill_code_nil Pr_fst_ret dlet_unit_ext.
- rewrite fill_code_cons.
  rewrite Pr_fst_bind dlet_dlet_ext.
  under eq_dlet => y. { rewrite IH. over. }
  exact: Pr_fstC hdM.
Qed.
End FillExchange.

(** A single finite draw, with the carrier supplied by an injective encoding. *)
Lemma finite_sample_split_le (N : nat) (hN : (0 < N)%nat)
    (D : choice_type) (d : dist D) (enc : 'I_N -> D)
    (henc : injective enc)
    (hu : Pr_fst d = dmargin enc (uniform N).π2)
    {T : choiceType} (S : {fset D}) (c : Axioms.R) (z : T)
    (G0 G1 : D -> {distr T / Axioms.R}) :
  0 <= c ->
  (forall y, y \notin S -> `|G0 y z - G1 y z| <= c) ->
  `|(\dlet_(y <- Pr_fst d) G0 y) z -
    (\dlet_(y <- Pr_fst d) G1 y) z| <= (size S)%:R / N%:R + c.
Proof.
case: N hN enc henc hu => [|n] hN enc henc hu //.
move=> hc hg.
apply: (uniform_split_encoded n D d enc hu G0 G1
  (fun y => y \in S) z c (size S) hc hg).
exact: sum_in_fset_le henc.
Qed.
