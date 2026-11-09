(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.games.prf_derive

    Generic PRF-derived-keys loop machinery, factored out of the WOTS+C
    PRF hop.  A scheme derives a batch of secrets by querying one keyed
    hash [Kh : khf] (Sec.lib.games.thf) at [q] distinct, nat-indexed
    tweaks; this file packages the state-separating reasoning that a
    reduction routes that derivation through the [FQUERY] oracle of
    [PRF_game Kh q] (Sec.lib.games.prf):

      - [prf_sks]: the oracle-routed derivation loop (one FQUERY per
        index [i], collecting the answers), with its [ValidCode] instance;
      - [resolve_fq] / [resolve_fq_false]: the linked FQUERY bodies of the
        real/ideal PRF game, computed once;
      - the pure query-list bookkeeping ([ptw_fresh], [qs_iotaS], [size_qs])
        over an ABSTRACT injective tweak [tw : nat -> kh_M Kh];
      - the block precondition [kblk] and its update lemmas
        ([kblk_qupd], [kblk_set_k]) over an ambient ignore-set;
      - the single-step FQUERY couplings ([r_fquery_known],
        [r_fquery_first], [r_fquery_ideal]) and their loop inductions
        ([r_prf_sks_some], [r_prf_sks_first], [r_prf_sks_ideal]).

    The concrete decode bridge [kh_eval Kh k (tw i) = ev k i] and the
    ambient ignore-set membership facts travel as section [Context]
    parameters (never [Hypothesis] -- the audit gate forbids it), so the
    section lemmas emerge parameterized over exactly the data an
    instantiation supplies.

    Instantiated at [Sec.wots.hop.prf]: [Kh := khf_prf],
    [tw := fun i => (pp, prf_tweak P i)], [ev := fun k i => PRF pp (prf_adrs P i) k],
    the bridge is [kh_eval_ptw], and the ignore-set is that hop's [IGNK].
    The keyed WOTS+C scheme, the reduction [R_prf], and the two
    [R_prf_real] / [R_prf_ideal] perfect lemmas stay there and CALL the
    loop lemmas below.

    ** FXMSS reuse

    The tweak is deliberately a bare [nat -> kh_M Kh].  When the FXMSS
    address type lands, its per-key tweak sequence (a structured
    walk over the hypertree, not a flat chain index) plugs in as a
    different [tw]; only the injective range condition [tw_inj] and the
    bridge [ev] change.  The loop machinery -- freshness bookkeeping,
    the lazy-key coupling, the ideal fresh-output coupling -- is reused
    verbatim. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.thf games.prf
  toolkit.sample_seq toolkit.relational_rules.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section PRFDerive.

(** The keyed hash under attack, the query cap, and the abstract
    nat-indexed tweak the derivation walks. *)
Context (Kh : khf) (q : nat).
Context (tw : nat -> kh_M Kh).

(** Distinct in-range indices query distinct tweaks (the exact-address
    injectivity, restricted to the [q] indices the loop uses). *)
Context (tw_inj : forall i j : nat, (i < q)%N -> (j < q)%N -> tw i = tw j -> i = j).

(** The decode bridge: at tweak [tw i] the keyed hash computes the
    scheme's derived value [ev k i].  [Sec.wots.hop.prf] supplies it
    with [kh_eval_ptw]. *)
Context (ev : kh_K Kh -> nat -> kh_N Kh).
Context (kh_eval_tw : forall (k : kh_K Kh) (i : nat), kh_eval Kh k (tw i) = ev k i).

(** The ambient ignore-set of the enclosing hop invariant; it holds
    both PRF locations, so a write to either preserves [heap_ignore]. *)
Context (Lig : Locations).
Context (hk_dom : (prf_k_loc Kh).1 \in domm Lig).
Context (hq_dom : (prf_qs_loc Kh).1 \in domm Lig).

Local Abbreviation PRFG b := (PRF_game Kh q b).
Local Abbreviation prf_k_loc' := (prf_k_loc Kh).
Local Abbreviation prf_qs_loc' := (prf_qs_loc Kh).

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed derivation loop *)

(** FQUERY's opsig as committed to [I_PRF Kh]. *)
Definition fqo : opsig := (FQUERY, (kh_M Kh, kh_N Kh)).

(** One FQUERY per index [i .. i+n-1], collecting the answers in order. *)
Fixpoint prf_sks (i n : nat) : raw_code (chList (kh_N Kh)) :=
  match n with
  | 0 => ret [::]
  | n'.+1 =>
      x ← opr fqo (tw i) (λ r, ret r) ;;
      xs ← prf_sks i.+1 n' ;;
      ret (x :: xs)
  end.

#[export] Instance prf_sks_valid (L : Locations) (i n : nat) :
  ValidCode L (I_PRF Kh) (prf_sks i n).
Proof.
elim: n i => [|n IH] i /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> x; eapply valid_bind; first exact: IH.
  move=> xs; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Linked oracle bodies (resolve equations, computed once) *)

Lemma resolve_fq (x : kh_M Kh) :
  resolve (PRFG true) fqo x =
  (ms ← get prf_qs_loc' ;;
   #assert (size ms < q)%N ;;
   #assert (x \notin ms) ;;
   #put prf_qs_loc' := rcons ms x ;;
   ko ← get prf_k_loc' ;;
   k ← match ko with
       | Some k => ret k
       | None =>
           k ← kh_dK Kh ;;
           #put prf_k_loc' := Some k ;;
           ret k
       end ;;
   ret (kh_eval Kh k x)).
Proof.
simplify_linking.
reflexivity.
Qed.

(** Ideal-side FQUERY answers a fresh uniform output. *)
Lemma resolve_fq_false (x : kh_M Kh) :
  resolve (PRFG false) fqo x =
  (ms ← get prf_qs_loc' ;;
   #assert (size ms < q)%N ;;
   #assert (x \notin ms) ;;
   #put prf_qs_loc' := rcons ms x ;;
   y ← kh_dN Kh ;;
   ret y).
Proof.
simplify_linking.
reflexivity.
Qed.

(* Keep the resolved oracle bodies folded under [simpl] from here on. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments PRF_game : simpl never.
#[local] Arguments kh_eval : simpl never.

(* ------------------------------------------------------------------ *)
(** ** Pure bookkeeping: the query list of the derivation loop *)

(** Distinct indices query distinct tweaks: the freshness assert of
    query [i] holds against the previous queries [0 .. i-1]. *)
Lemma ptw_fresh (i : nat) :
  (i < q)%N -> tw i \notin [seq tw t | t <- iota 0 i].
Proof.
move=> hi; apply/negP => /mapP[t ht e].
move: ht; rewrite mem_iota add0n => /andP[_ ht].
have ht' : (t < q)%N := ltn_trans ht hi.
have ei : i = t := tw_inj i t hi ht' e.
by rewrite ei ltnn in ht.
Qed.

(** Appending query [i] to the queries [0 .. i-1]. *)
Lemma qs_iotaS (i : nat) :
  rcons [seq tw t | t <- iota 0 i] (tw i)
  = [seq tw t | t <- iota 0 i.+1].
Proof.
by rewrite -addn1 iotaD add0n /= map_cat cats1.
Qed.

Lemma size_qs (i : nat) :
  size [seq tw t | t <- iota 0 i] = i.
Proof. by rewrite size_map size_iota. Qed.

(* ------------------------------------------------------------------ *)
(** ** The block precondition (inside COMMIT, machinery dropped) *)

Definition kblk (ko : option (kh_K Kh)) (ms : seq (kh_M Kh)) : precond :=
  λ '(s0, s1),
  [/\ heap_ignore Lig (s0, s1),
      get_heap s1 prf_k_loc' = ko &
      get_heap s1 prf_qs_loc' = ms].

Arguments kblk : simpl never.

(** The FQUERY state update (put qs). *)
Lemma kblk_qupd (ko : option (kh_K Kh)) (ms : seq (kh_M Kh)) (x : kh_M Kh) s0 s1 :
  kblk ko ms (s0, s1) ->
  kblk ko (rcons ms x) (s0, set_heap s1 prf_qs_loc' (rcons ms x)).
Proof.
move=> [h0 h1 h2]; split.
- by apply: heap_ignore_set_r h0; exact: hq_dom.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
Qed.

(** The lazy key sampling (put k, at the first query). *)
Lemma kblk_set_k (ms : seq (kh_M Kh)) (kk : kh_K Kh) s0 s1 :
  kblk None ms (s0, s1) ->
  kblk (Some kk) ms (s0, set_heap s1 prf_k_loc' (Some kk)).
Proof.
move=> [h0 h1 h2]; split.
- by apply: heap_ignore_set_r h0; exact: hk_dom.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked FQUERY *)

(** [fquery_log ms hsz hfresh]: route one linked FQUERY through the
    query log -- read [prf_qs_loc'], discharge the size-cap ([hsz]) and
    freshness ([hfresh]) asserts, then append [tw i].  Shared verbatim by
    the three [r_fquery_*] lemmas.  The two hypotheses travel as [Ltac]
    arguments (ssreflect would otherwise globalize their names at
    definition time, before they exist). *)
Local Ltac fquery_log ms hsz hfresh :=
  eapply (r_get_bind_rhs prf_qs_loc' ms);
    first (by move=> ? ? [_ _ ?]);
  cbv beta;
  eapply r_bind_assertD_rhs; first (by move=> *; exact: hsz);
  move=> _;
  eapply r_bind_assertD_rhs; first (by move=> *; exact: hfresh);
  move=> _;
  eapply r_put_bind_rhs;
    first (by move=> ? ? ?; eapply kblk_qupd; eassumption).

(** Key already sampled (queries after the first): the oracle's reply
    is the derived value [ev kk i]. *)
Lemma r_fquery_known {B : choiceType} (kk : kh_K Kh) (i : nat)
    (ms : seq (kh_M Kh)) (c0 : raw_code B) (k1 : kh_N Kh -> raw_code B)
    (post : postcond B B) :
  (size ms < q)%N ->
  tw i \notin ms ->
  ⊢ ⦃ λ '(s0, s1), kblk (Some kk) (rcons ms (tw i)) (s0, s1) ⦄
     c0 ≈ k1 (ev kk i) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), kblk (Some kk) ms (s0, s1) ⦄
     c0 ≈ bind (resolve (PRFG true) fqo (tw i)) k1 ⦃ post ⦄.
Proof.
move=> hsz hfresh h.
rewrite (resolve_fq (tw i)).
fquery_log ms hsz hfresh.
eapply (r_get_bind_rhs prf_k_loc' (Some kk)).
  by move=> s0 s1 [_ h' _].
simpl.
by rewrite kh_eval_tw.
Qed.

(** The first query: the oracle samples the hidden key; the lhs's
    eager [k ← kh_dK] couples with it. *)
Lemma r_fquery_first {B : choiceType} (i : nat)
    (ms : seq (kh_M Kh)) (k0 : kh_K Kh -> raw_code B) (k1 : kh_N Kh -> raw_code B)
    (post : postcond B B) :
  (size ms < q)%N ->
  tw i \notin ms ->
  (forall kk : kh_K Kh,
     ⊢ ⦃ λ '(s0, s1), kblk (Some kk) (rcons ms (tw i)) (s0, s1) ⦄
        k0 kk ≈ k1 (ev kk i) ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), kblk None ms (s0, s1) ⦄
     bind (kh_dK Kh) k0 ≈ bind (resolve (PRFG true) fqo (tw i)) k1 ⦃ post ⦄.
Proof.
move=> hsz hfresh h.
rewrite (resolve_fq (tw i)).
fquery_log ms hsz hfresh.
eapply (r_get_bind_rhs prf_k_loc' None).
  by move=> s0 s1 [_ h' _].
rewrite !bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> kk; cbv beta.
eapply r_put_bind_rhs.
  by move=> s0 s1 hpre; exact: (kblk_set_k _ kk _ _ hpre).
simpl.
by rewrite kh_eval_tw.
Qed.

(** Ideal side: the oracle's reply is a fresh sample; the lhs's
    [kh_dN] (one step of [sample_seq]) couples with it. *)
Lemma r_fquery_ideal {B : choiceType} (i : nat)
    (ms : seq (kh_M Kh)) (k0 k1 : kh_N Kh -> raw_code B) (post : postcond B B) :
  (size ms < q)%N ->
  tw i \notin ms ->
  (forall y : kh_N Kh,
     ⊢ ⦃ λ '(s0, s1), kblk None (rcons ms (tw i)) (s0, s1) ⦄
        k0 y ≈ k1 y ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1), kblk None ms (s0, s1) ⦄
     bind (kh_dN Kh) k0 ≈ bind (resolve (PRFG false) fqo (tw i)) k1 ⦃ post ⦄.
Proof.
move=> hsz hfresh h.
rewrite (resolve_fq_false (tw i)).
fquery_log ms hsz hfresh.
rewrite !bind_assoc.
eapply r_scheme_bind; first exact: prog_valid.
move=> y; cbv beta.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The derivation-loop inductions *)

(** Key sampled (tail of the loop): all remaining queries are pure
    derivations; the lhs is untouched. *)
Lemma r_prf_sks_some {B : choiceType} (kk : kh_K Kh) :
  forall (n i : nat) (c0 : raw_code B) (k1 : chList (kh_N Kh) -> raw_code B)
         (post : postcond B B),
  (i + n <= q)%N ->
  ⊢ ⦃ λ '(s0, s1),
        kblk (Some kk) [seq tw t | t <- iota 0 (i + n)] (s0, s1) ⦄
     c0 ≈ k1 [seq ev kk t | t <- iota i n] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1),
        kblk (Some kk) [seq tw t | t <- iota 0 i] (s0, s1) ⦄
     c0 ≈ bind (code_link (prf_sks i n) (PRFG true)) k1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i c0 k1 post hbud h.
- (* n = 0 : the loop is [ret [::]] *)
  move: h; rewrite addn0 /=.
  by [].
- (* n = n.+1 : one known-key query, then the tail *)
  rewrite /= bind_assoc.
  eapply r_fquery_known.
  + by rewrite size_qs; apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + apply: ptw_fresh.
    by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + rewrite qs_iotaS.
    rewrite code_link_bind bind_assoc.
    eapply IH; first by rewrite addSnnS.
    rewrite addSnnS.
    exact: h.
Qed.

(** The full loop, real side: the first query samples the key. *)
Lemma r_prf_sks_first {B : choiceType} :
  forall (n i : nat) (k0 : kh_K Kh -> raw_code B) (k1 : chList (kh_N Kh) -> raw_code B)
         (post : postcond B B),
  (0 < n)%N ->
  (i + n <= q)%N ->
  (forall kk : kh_K Kh,
     ⊢ ⦃ λ '(s0, s1),
           kblk (Some kk) [seq tw t | t <- iota 0 (i + n)] (s0, s1) ⦄
        k0 kk ≈ k1 [seq ev kk t | t <- iota i n] ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1),
        kblk None [seq tw t | t <- iota 0 i] (s0, s1) ⦄
     bind (kh_dK Kh) k0 ≈ bind (code_link (prf_sks i n) (PRFG true)) k1 ⦃ post ⦄.
Proof.
case=> [|n] // i k0 k1 post _ hbud h.
rewrite /= bind_assoc.
eapply r_fquery_first.
- by rewrite size_qs; apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
- apply: ptw_fresh.
  by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
- move=> kk.
  rewrite qs_iotaS.
  rewrite code_link_bind bind_assoc.
  eapply r_prf_sks_some; first by rewrite addSnnS.
  rewrite addSnnS.
  exact: h kk.
Qed.

(** The full loop, ideal side: fresh oracle outputs couple with the
    lhs's [sample_seq]. *)
Lemma r_prf_sks_ideal {B : choiceType} :
  forall (n i : nat) (K0 K1 : chList (kh_N Kh) -> raw_code B)
         (post : postcond B B),
  (i + n <= q)%N ->
  (forall xs : chList (kh_N Kh), size xs = n ->
     ⊢ ⦃ λ '(s0, s1),
           kblk None [seq tw t | t <- iota 0 (i + n)] (s0, s1) ⦄
        K0 xs ≈ K1 xs ⦃ post ⦄) ->
  ⊢ ⦃ λ '(s0, s1),
        kblk None [seq tw t | t <- iota 0 i] (s0, s1) ⦄
     bind (sample_seq (kh_dN Kh) n) K0
   ≈ bind (code_link (prf_sks i n) (PRFG false)) K1 ⦃ post ⦄.
Proof.
elim=> [|n IH] i K0 K1 post hbud h.
- (* n = 0 : both sides are pure *)
  move: (h [::] erefl); rewrite addn0 /=.
  by [].
- (* n = n.+1 : couple one sample with one ideal query *)
  rewrite /= !bind_assoc.
  eapply r_fquery_ideal.
  + by rewrite size_qs; apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + apply: ptw_fresh.
    by apply: leq_trans hbud; rewrite addnS ltnS leq_addr.
  + move=> y; cbv beta.
    rewrite qs_iotaS.
    rewrite code_link_bind !bind_assoc.
    eapply IH; first by rewrite addSnnS.
    move=> xs hxs.
    rewrite addSnnS.
    move: (h (y :: xs)); rewrite /= hxs => /(_ erefl).
    by [].
Qed.

End PRFDerive.
