(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.digest.invariant

    The digest filter's safe map relation. Signing exempts its cached
    point; an ordinary fresh ROM read must avoid the assigned digest set. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import schemes.
From Shrincs.internal.ssprove.fxmss Require Import params games.
From mathcomp Require Import reals distr.

Import PackageNotation Num.Theory Order.POrderTheory GRing.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Definition digest_avoid
    (mp : chMap shrincs_fxmss_hmsg_input (bytes 32))
    (rt : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16))
    (sd : shrincs_fxmss_digest_table) : Prop :=
  forall x md, getm mp x = Some md ->
    getm rt x.2.2 != Some x.1 -> md \notin codomm sd.

Lemma digest_avoid_empty rt sd : digest_avoid emptym rt sd.
Proof. by move=> x md; rewrite emptymE. Qed.

Lemma digest_avoid_no_targets mp rt : digest_avoid mp rt emptym.
Proof. by move=> x md _ _; rewrite codomm0 in_fset0. Qed.

Lemma digest_avoid_read mp rt sd x md :
  digest_avoid mp rt sd ->
  (md \notin codomm sd \/ getm mp x = Some md) ->
  digest_avoid (setm mp x md) rt sd.
Proof.
move=> hi hm y v.
rewrite setmE.
case: eqP => [-> [<-] hg|hne hy hg]; last exact: hi hy hg.
case: hm => hm; first exact hm.
exact: hi hm hg.
Qed.

Lemma digest_avoid_cached mp rt sd (x : shrincs_fxmss_hmsg_input) md :
  digest_avoid mp rt sd ->
  (getm rt x.2.2 = None \/ getm rt x.2.2 = Some x.1) ->
  digest_avoid (setm mp x md) (setm rt x.2.2 x.1) sd.
Proof.
move=> hi ht y v.
rewrite setmE.
case: eqP => [-> _|hne hy] hg.
- by move: hg; rewrite setmE eqxx eqxx.
- (* Other queries retain the avoidance condition after the update. *)
  apply: hi hy _.
  move: hg.
  rewrite setmE.
  case: (eqVneq y.2.2 x.2.2) => [he|he] hg; last exact hg.
  apply/negP => ha.
  move: hg => /negP; apply.
  move: ha.
  rewrite he.
  by case: ht => ->.
Qed.

Lemma digest_filter_safe mp rt sd x md :
  digest_avoid mp rt sd -> getm mp x = Some md ->
  ~~ ((md \in codomm sd) && (getm rt x.2.2 != Some x.1)).
Proof.
move=> hi hm.
case he: (getm rt x.2.2 != Some x.1); last by rewrite andbF.
by rewrite (negbTE (hi x md hm he)).
Qed.

Definition digest_remaining (Q : shrincs_fxmss_resources) (ready : bool)
    (hc : nat) (done : bool) : nat :=
  if ready then (shrincs_fxmss_hash_budget Q - hc + ~~ done)%nat
  else (shrincs_fxmss_hash_budget Q + 1)%nat.

Definition digest_error (Q : shrincs_fxmss_resources) (ready : bool)
    (hc : nat) (done : bool) : Axioms.R :=
  (shrincs_fxmss_leaf_capacity Q)%:R * (digest_remaining Q ready hc done)%:R /
    ((2 ^ 256)%nat)%:R.

Lemma digest_error_ge0 Q ready hc done :
  0 <= digest_error Q ready hc done.
Proof.
by rewrite /digest_error divr_ge0 ?ler0n // mulr_ge0 ?ler0n.
Qed.

Lemma digest_gen_charge Q hc : (hc <= shrincs_fxmss_hash_budget Q)%nat ->
  (shrincs_fxmss_leaf_capacity Q)%:R * hc%:R / ((2 ^ 256)%nat)%:R +
    digest_error Q true hc false = digest_error Q false hc false.
Proof.
move=> hhc.
rewrite /digest_error /digest_remaining /= -mulrDl -mulrDr -natrD.
by rewrite addnCA addnA subnK.
Qed.

Lemma digest_query_charge Q hc done s :
  (hc < shrincs_fxmss_hash_budget Q)%nat -> (s <= shrincs_fxmss_leaf_capacity Q)%nat ->
  s%:R / ((2 ^ 256)%nat)%:R + digest_error Q true hc.+1 done
    <= digest_error Q true hc done.
Proof.
move=> hhc hs.
rewrite /digest_error /digest_remaining -mulrDl.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
have he : (shrincs_fxmss_hash_budget Q - hc = (shrincs_fxmss_hash_budget Q -
  hc.+1).+1)%nat.
{ by rewrite subnS prednK // subn_gt0. }
rewrite he addSn -natr1 mulrDr mulr1 addrC.
by rewrite lerD2l ler_nat.
Qed.

Definition digest_safe (Q : shrincs_fxmss_resources) (h : heap) : Prop :=
  [ /\ digest_avoid (get_heap h shrincs_fxmss_rom_loc) (get_heap h shrincs_fxmss_rt_loc)
         (get_heap h shrincs_fxmss_sd_loc),
       (size (codomm (get_heap h shrincs_fxmss_sd_loc)) <= shrincs_fxmss_leaf_capacity
         Q)%nat,
       (get_heap h shrincs_fxmss_hcnt_loc <= shrincs_fxmss_hash_budget Q)%nat &
       get_heap h shrincs_fxmss_st_loc = None ->
         get_heap h shrincs_fxmss_sd_loc = emptym /\
         (size (domm (get_heap h shrincs_fxmss_rom_loc)) <= get_heap h
           shrincs_fxmss_hcnt_loc)%nat ].

Definition digest_heap_error Q h : Axioms.R :=
  digest_error Q (isSome (get_heap h shrincs_fxmss_st_loc))
    (get_heap h shrincs_fxmss_hcnt_loc) (get_heap h shrincs_fxmss_done_loc).

Lemma digest_safe_empty Q : digest_safe Q empty_heap.
Proof.
split.
- exact: digest_avoid_empty.
- by rewrite codomm0 sizes0 leq0n.
- exact: leq0n.
- move=> _. split=> //.
  by rewrite domm0 sizes0.
Qed.

Lemma digest_safe_frame Q h h' :
  get_heap h' shrincs_fxmss_st_loc = get_heap h shrincs_fxmss_st_loc ->
  get_heap h' shrincs_fxmss_rom_loc = get_heap h shrincs_fxmss_rom_loc ->
  get_heap h' shrincs_fxmss_rt_loc = get_heap h shrincs_fxmss_rt_loc ->
  get_heap h' shrincs_fxmss_sd_loc = get_heap h shrincs_fxmss_sd_loc ->
  get_heap h' shrincs_fxmss_hcnt_loc = get_heap h shrincs_fxmss_hcnt_loc ->
  digest_safe Q h -> digest_safe Q h'.
Proof.
by move=> hs hm hr hd hc; rewrite /digest_safe hs hm hr hd hc.
Qed.

Lemma digest_avoid_separated mp rt sd :
  (forall md, md \in codomm sd -> md \notin codomm mp) ->
  digest_avoid mp rt sd.
Proof.
move=> hd x md hm _.
apply/negP => hin.
have hn := hd md hin.
have hmem : md \in codomm mp by apply/codommP; exists x.
by rewrite hmem in hn.
Qed.

Lemma digest_safe_sign Q h h' st (x : shrincs_fxmss_hmsg_input) md :
  digest_safe Q h -> get_heap h shrincs_fxmss_st_loc = Some st ->
  (getm (get_heap h shrincs_fxmss_rt_loc) x.2.2 = None \/
   getm (get_heap h shrincs_fxmss_rt_loc) x.2.2 = Some x.1) ->
  get_heap h' shrincs_fxmss_st_loc = get_heap h shrincs_fxmss_st_loc ->
  get_heap h' shrincs_fxmss_rom_loc = setm (get_heap h shrincs_fxmss_rom_loc) x md ->
  get_heap h' shrincs_fxmss_rt_loc = setm (get_heap h shrincs_fxmss_rt_loc) x.2.2 x.1 ->
  get_heap h' shrincs_fxmss_sd_loc = get_heap h shrincs_fxmss_sd_loc ->
  get_heap h' shrincs_fxmss_hcnt_loc = get_heap h shrincs_fxmss_hcnt_loc ->
  digest_safe Q h'.
Proof.
move=> [hi hz hc hp] hs ht hst hm hr hd hh.
split.
- rewrite hm hr hd. exact: digest_avoid_cached hi ht.
- by rewrite hd.
- by rewrite hh.
- by rewrite hst hs.
Qed.

Lemma digest_safe_read Q h h' x md :
  digest_safe Q h -> (get_heap h shrincs_fxmss_hcnt_loc < shrincs_fxmss_hash_budget
    Q)%nat ->
  (md \notin codomm (get_heap h shrincs_fxmss_sd_loc) \/
   getm (get_heap h shrincs_fxmss_rom_loc) x = Some md) ->
  get_heap h' shrincs_fxmss_st_loc = get_heap h shrincs_fxmss_st_loc ->
  get_heap h' shrincs_fxmss_rom_loc = setm (get_heap h shrincs_fxmss_rom_loc) x md ->
  get_heap h' shrincs_fxmss_rt_loc = get_heap h shrincs_fxmss_rt_loc ->
  get_heap h' shrincs_fxmss_sd_loc = get_heap h shrincs_fxmss_sd_loc ->
  get_heap h' shrincs_fxmss_hcnt_loc = (get_heap h shrincs_fxmss_hcnt_loc).+1 ->
  digest_safe Q h'.
Proof.
move=> [hi hz hc hp] hlt hv hs hm hr hd hh.
split.
- rewrite hm hr hd. exact: digest_avoid_read hi hv.
- by rewrite hd.
- by rewrite hh.
- (* Before generation, a fresh hash adds at most one table entry. *)
  rewrite hs => hn.
  have [he hsz] := hp hn.
  split; first by rewrite hd.
  rewrite hm hh domm_set sizesU1.
  apply: leq_trans (leq_add (leq_b1 _) hsz) _.
  by rewrite add1n.
Qed.

Lemma digest_safe_generated Q h h' st sd :
  (get_heap h shrincs_fxmss_hcnt_loc <= shrincs_fxmss_hash_budget Q)%nat ->
  (size (codomm sd) <= shrincs_fxmss_leaf_capacity Q)%nat ->
  (forall md, md \in codomm sd -> md \notin codomm (get_heap h shrincs_fxmss_rom_loc))
    ->
  get_heap h' shrincs_fxmss_st_loc = Some st ->
  get_heap h' shrincs_fxmss_rom_loc = get_heap h shrincs_fxmss_rom_loc ->
  get_heap h' shrincs_fxmss_sd_loc = sd ->
  get_heap h' shrincs_fxmss_hcnt_loc = get_heap h shrincs_fxmss_hcnt_loc ->
  digest_safe Q h'.
Proof.
move=> hc hz ha hs hm hd hh.
split.
- rewrite hm hd. exact: digest_avoid_separated ha.
- by rewrite hd.
- by rewrite hh.
- by rewrite hs.
Qed.

Lemma digest_forge_charge Q hc s : (s <= shrincs_fxmss_leaf_capacity Q)%nat ->
  s%:R / ((2 ^ 256)%nat)%:R + digest_error Q true hc true
    <= digest_error Q true hc false.
Proof.
move=> hs.
rewrite /digest_error /digest_remaining /= addn0 addn1 -mulrDl.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
rewrite -natr1 mulrDr mulr1 addrC.
by rewrite lerD2l ler_nat.
Qed.

Lemma digest_safe_lookup Q h h' st x md :
  digest_safe Q h -> get_heap h shrincs_fxmss_st_loc = Some st ->
  (md \notin codomm (get_heap h shrincs_fxmss_sd_loc) \/
   getm (get_heap h shrincs_fxmss_rom_loc) x = Some md) ->
  get_heap h' shrincs_fxmss_st_loc = get_heap h shrincs_fxmss_st_loc ->
  get_heap h' shrincs_fxmss_rom_loc = setm (get_heap h shrincs_fxmss_rom_loc) x md ->
  get_heap h' shrincs_fxmss_rt_loc = get_heap h shrincs_fxmss_rt_loc ->
  get_heap h' shrincs_fxmss_sd_loc = get_heap h shrincs_fxmss_sd_loc ->
  get_heap h' shrincs_fxmss_hcnt_loc = get_heap h shrincs_fxmss_hcnt_loc ->
  digest_safe Q h'.
Proof.
move=> [hi hz hc hp] hs hv hst hm hr hd hh.
split.
- rewrite hm hr hd. exact: digest_avoid_read hi hv.
- by rewrite hd.
- by rewrite hh.
- by rewrite hst hs.
Qed.

Lemma digest_ratio_cancel a b q :
  ((2 ^ a)%nat)%:R * (q%:R / ((2 ^ (a + b))%nat)%:R) =
    q%:R / ((2 ^ b)%nat)%:R :> Axioms.R.
Proof.
have hL : ((2 ^ a)%nat)%:R != (0 : Axioms.R).
{ by rewrite pnatr_eq0 expn_eq0. }
rewrite expnD natrM invfM !mulrA.
by rewrite [X in X * _]mulrAC mulfV // mul1r.
Qed.

Lemma digest_budget_normalize Q :
  (shrincs_fxmss_leaf_capacity Q)%:R * ((shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^
    256)%nat)%:R) =
    (shrincs_fxmss_hash_budget Q + 1)%:R / ((2 ^ 192)%nat)%:R :> Axioms.R.
Proof.
exact: (digest_ratio_cancel 64 192 (shrincs_fxmss_hash_budget Q + 1)%nat).
Qed.
