(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.prf

    The PRF-derived secret-key hop: the keyed known-message game
    [G_forge_keyed] (chain starts derived from a hidden PRF key on
    SF_SHRINCS_WOTS_PRF addresses, as in the spec) is one PRF-distinguishing
    step away from the ideal-key game [G_forge_sampledkey] (chain starts sampled).
    Delivered:

      [R_prf_real  : perfect (I_KOTS WC) (G_forge_keyed b)
                             (R_prf b ∘ PRF_game khf_prf chain_count true)]
      [R_prf_ideal : perfect (I_KOTS WC) (G_forge_sampledkey b)
                             (R_prf b ∘ PRF_game khf_prf chain_count false)]

    so [Adv (G_forge_keyed b) (G_forge_sampledkey b) A = AdvOf (PRF_game khf_prf chain_count)
    (A ∘ R_prf b)] at the consumer (Sec.bound.prf).  This hop
    composes OUTSIDE the proven ideal-key theorem
    ([shrincs_wots_secure_ideal_sk]) by the advantage triangle — the UD
    telescope and the four middle hops are never reopened.

    The generic PRF-derived-keys loop machinery (the oracle-routed
    derivation loop, its query-list bookkeeping, and the FQUERY
    couplings) lives in [Sec.lib.games.prf_derive]; this file
    instantiates it at [khf_prf] and the WOTS+C addresses.

    ** Design

    - [khf_prf] is the [khf] (Sec.lib.games.thf) of the secret-key derivation:
      hidden key = SKseed, query input = (PKseed, encoded address) —
      the distinguisher knows both — output = an n-byte chain start.
      Argument order of the section parameter [PRF] follows the
      repo's hash convention (pp, address, payload); the spec's
      PRF(pk_seed, sk_seed, ADRS) order is a byte-level
      instantiation detail.
    - [derive_sk pp k] derives the [chain_count] chain starts at the
      SF_SHRINCS_WOTS_PRF (type 21) addresses of this instance — the first
      real consumer of [shrincs_wots_prf_adrs].
    - [G_forge_keyed b] is verbatim [G_forge_sampledkey b] with the chain-start sampling
      [sample_seq dN chain_count] replaced by [k ← dK] plus the pure
      derivation; same locations (the games are never composed, and
      sharing G_forge_sampledkey's locations keeps ONE invariant for both perfect
      lemmas, exactly as G_forge_udideal/Gmid* do), same valid-commit [#assert],
      same interface [I_KOTS WC].
    - [R_prf b] samples PKseed ITSELF (it is public), computes the
      grinding assert purely, and issues one FQUERY per chain at the
      encoded SF_SHRINCS_WOTS_PRF addresses; the PRF game's hidden key is
      sampled lazily at the first query — the same trace position as
      G_forge_keyed's eager [k ← dK].  KFORGE is local (no oracle call): the
      real/ideal KOTS bit [b] stays a parameter of the reduction.
    - Side condition [Hcc : 0 < chain_count], REAL side only: with no
      chains, G_forge_keyed samples a key that R ∘ PRF_game never samples,
      which a lossy [dK] would distinguish.  A data side condition
      like [Hrange], discharged at instantiation (the spec has
      chain_count = 32).

    ** Invariant

    [heap_ignore] over the eight private locations joined with one
    [rel_app] relation [RK]: the game's pk/log/sig locations mirror
    R's, and BEFORE commitment (pk = None) the PRF oracle is in its
    initial state (no key, no queries).  After commitment nothing
    more is needed — KFORGE never touches the PRF oracle.

    Locations 370-372 (R's copies). *)

From mathcomp.experimental_reals Require Import distr.
From Shrincs.internal.ssprove.lib Require Import prelude sig.scheme sig.kots
  games.thf games.prf games.prf_derive toolkit.sample_seq toolkit.relational_rules
  toolkit.hop_tactics.
From Shrincs.internal.common Require Import math.chain math.encoding.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import scheme games.
From Stdlib Require Import Lia.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(** The khf instance over the anchor-free core (see params.v /
    games.v: the assumption-facing instances provably cannot see the
    anchor); [khf_prf] below wraps it at [wc_core_of P]. *)
Section KhfPrfCore.

Context (H : wc_params_core).
Context (K : choice_type).
Context (PRF : wcc_PP H -> wc_adrs_core H -> K -> wcc_N H).
Context (dK : dist K).

Definition khf_prf_core : khf :=
  {| kh_K := K ; kh_M := wcc_PP H × wc_adrs_ch_core H ; kh_N := wcc_N H ;
     kh_eval := fun k pt => PRF pt.1 (decode_tweak_core H pt.2) k ;
     kh_dK := dK ; kh_dN := wcc_dN H |}.

End KhfPrfCore.

Section PrfHop.

(** The WOTS+C parameter record [P] (Sec.wots.params), plus the keyed
    derivation data: the SKseed space [K], the derivation function
    [PRF] and the SKseed sampler [dK]. *)
Context (P : wc_params).
Context (K : choice_type).
Context (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P).
Context (dK : dist K).

(** The PRF tweak ([params.prf_tweak], the encoded SF_SHRINCS_WOTS_PRF
    address of chain [i]) carries its chain index untruncated, so
    [ptw_fresh] below -- distinct chains query distinct PRF inputs --
    holds with no range side condition, while [kh_eval_ptw] shows it
    still computes the scheme's real PRF at [prf_adrs P i]. *)

(* ------------------------------------------------------------------ *)
(** ** The khf instance and the key derivation *)

(** The keyed hash under attack: hidden key = SKseed; the query input
    carries (PKseed, encoded address) — both known to the
    distinguisher; output sampler [dN] (the ideal branch returns
    fresh n-byte strings, exactly the ideal-key chain starts). *)
Definition khf_prf : khf := khf_prf_core (wc_core_of P) K PRF dK.

(** On encoded (canonical) tweaks [khf_prf] evaluates the derivation — the
    consumers' interface to [kh_eval]. *)
Lemma kh_evalE (k : K) (pp : wcp_PP P) (a : wc_adrs P) :
  kh_eval khf_prf k (pp, encode_tweak P a) = PRF pp a k.
Proof. by rewrite /kh_eval /khf_prf /khf_prf_core /= core_decodeE encode_tweakK. Qed.

(** On a PRF tweak [khf_prf] evaluates the scheme's derivation: decoding the
    untruncated PRF tweak reproduces the concrete PRF address. *)
Lemma kh_eval_ptw (k : K) (pp : wcp_PP P) (i : nat) :
  kh_eval khf_prf k (pp, prf_tweak P i) = PRF pp (prf_adrs P i) k.
Proof. by rewrite /kh_eval /khf_prf /khf_prf_core /= core_decodeE decode_prf_tweak. Qed.

(** The spec's per-chain secret derivation: chain [i]'s start is the
    PRF at the SF_SHRINCS_WOTS_PRF address of chain [i]. *)
Definition derive_sk (pp : wcp_PP P) (k : K) : seq (wcp_N P) :=
  [seq PRF pp (prf_adrs P i) k | i <- iota 0 (wcp_chain_count P)].

Lemma size_derive_sk pp k : size (derive_sk pp k) = wcp_chain_count P.
Proof. by rewrite size_map size_iota. Qed.

(* ------------------------------------------------------------------ *)
(** ** The keyed scheme (the spec's keygen) and its correctness *)

(** The spec's [shrincs_wots_pubkey_gen]: compress the ends of the chains
    grown from the PRF-derived starts. *)
Definition shrincs_wots_pubkey_gen (pp : wcp_PP P) (k : K) : wcp_N P :=
  shrincs_wots_pubkey P pp (derive_sk pp k).

(** WOTS+C with PRF-derived keys as a [sig_scheme]:
    Sk = (PKseed, SKseed). *)
Definition shrincs_wots_keyed : sig_scheme := {|
  Pk := wcp_PP P × wcp_N P ;
  Sk := wcp_PP P × K ;
  Msg := wcp_M P ;
  Sig := ('list (wcp_N P)) × 'nat ;
  SParam := 'unit ;
  keygen := fun _ => {code
    pp ← wcp_dPP P ;;
    k ← dK ;;
    ret ((pp, k), (pp, shrincs_wots_pubkey_gen pp k)) } ;
  sign := fun sk m => {code
    ret (omap (fun sg => (sg, sk))
              (shrincs_wots_sign P sk.1 (derive_sk sk.1 sk.2) m)) } ;
  verify := fun pk m sg => shrincs_wots_verify P pk.1 pk.2 m sg
|}.

(** Correctness through the keyed signing function (from the pure
    correctness of the ideal-key scheme, at the derived starts). *)
Lemma shrincs_wots_keyed_verify_sign pp k m sg :
  shrincs_wots_sign P pp (derive_sk pp k) m = Some sg ->
  shrincs_wots_verify P pp (shrincs_wots_pubkey_gen pp k) m sg = true.
Proof.
exact: (shrincs_wots_verify_sign P pp (derive_sk pp k) m sg (size_derive_sk pp k)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** G_forge_keyed: the keyed valid-commit known-message game

    Verbatim [G_forge_sampledkey] with [sample_seq dN chain_count] replaced by
    [k ← dK] + [derive_sk] (same locations, see header). *)

Definition G_forge_keyed (b : bool) : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap (forge_pk_loc P) ; (forge_log_loc P) ; (forge_sig_loc P) ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get (forge_pk_loc P) ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      k ← dK ;;
      #put (forge_pk_loc P) := Some (pp, shrincs_wots_pubkey P pp (derive_sk pp k)) ;;
      #put (forge_log_loc P) := [:: m] ;;
      #put (forge_sig_loc P) := Some (sign_chains P pp (derive_sk pp k) (digest_of P pp m c), c) ;;
      ret ((pp, shrincs_wots_pubkey P pp (derive_sk pp k)),
           Some (sign_chains P pp (derive_sk pp k) (digest_of P pp m c), c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, s) {
      pk ← getSome (forge_pk_loc P) ;;
      log ← get (forge_log_loc P) ;;
      if b then
        ret (shrincs_wots_verify P pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** The reduction package *)

(** R's own locations (370+, see header). *)
Definition r_prf_pk_loc := mkloc 370 (None : option (Pk (shrincs_wots_scheme P))).
Definition r_prf_log_loc := mkloc 371 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition r_prf_sig_loc := mkloc 372 (None : option (Sig (shrincs_wots_scheme P))).

(** THE reduction: plays [I_KOTS WC] using the FQUERY oracle.  COMMIT
    samples PKseed itself (public) and computes the grinding assert
    purely; KFORGE is local (see header). *)
Definition R_prf (b : bool) : package (I_PRF khf_prf) (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap r_prf_pk_loc ; r_prf_log_loc ; r_prf_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P) ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get r_prf_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      xs ← prf_sks khf_prf (fun i => (pp, prf_tweak P i)) 0 (wcp_chain_count P) ;;
      #put r_prf_pk_loc := Some (pp, shrincs_wots_pubkey P pp xs) ;;
      #put r_prf_log_loc := [:: m] ;;
      #put r_prf_sig_loc := Some (sign_chains P pp xs (digest_of P pp m c), c) ;;
      ret ((pp, shrincs_wots_pubkey P pp xs), Some (sign_chains P pp xs (digest_of P pp m c), c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome r_prf_pk_loc ;;
      log ← get r_prf_log_loc ;;
      if b then
        ret (shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log))
      else
        ret false
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** Local abbreviations for the linked PRF game *)

Local Abbreviation PRFG b := (PRF_game khf_prf (wcp_chain_count P) b).
Local Abbreviation prf_k_loc' := (prf_k_loc khf_prf).
Local Abbreviation prf_qs_loc' := (prf_qs_loc khf_prf).

(* Keep the packages and the (Sec.lib.games.prf_derive) resolved oracle
   bodies folded under [simpl] from here on. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments PRF_game : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments find_counter : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments sign_chains : simpl never.
#[local] Arguments shrincs_wots_pubkey : simpl never.
#[local] Arguments derive_sk : simpl never.
#[local] Arguments kh_eval : simpl never.
#[local] Arguments Sec.wots.params.decode_tweak : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The invariant (header)

    Hop-invariant template (Sec.hop.grind), with a TRIVIAL
    committed branch: KFORGE makes no oracle call, so only the
    initial-state facts (needed by COMMIT) are recorded. *)

Definition IGNK : Locations :=
  [fmap (forge_pk_loc P) ; (forge_log_loc P) ; (forge_sig_loc P) ; r_prf_pk_loc ; r_prf_log_loc ; r_prf_sig_loc ;
        prf_k_loc' ; prf_qs_loc' ].

Definition RK (pko : option (Pk (shrincs_wots_scheme P))) (lg : seq (Msg (shrincs_wots_scheme P)))
    (sgo : option (Sig (shrincs_wots_scheme P)))
    (pko' : option (Pk (shrincs_wots_scheme P))) (lg' : seq (Msg (shrincs_wots_scheme P))) (sgo' : option (Sig (shrincs_wots_scheme P)))
    (ko : option K) (qs : seq (kh_M khf_prf)) : Prop :=
  [/\ pko' = pko, lg' = lg, sgo' = sgo &
      match pko with
      | None => [/\ lg = [::], sgo = None, ko = None & qs = [::]]
      | Some _ => True
      end].

Definition kinv : precond :=
  heap_ignore IGNK
  ⋊ rel_app [:: (lhs, (forge_pk_loc P)) ; (lhs, (forge_log_loc P)) ; (lhs, (forge_sig_loc P)) ;
                (rhs, r_prf_pk_loc) ; (rhs, r_prf_log_loc) ; (rhs, r_prf_sig_loc) ;
                (rhs, prf_k_loc') ; (rhs, prf_qs_loc') ] RK.

Arguments kinv : simpl never.

Lemma kinvE s0 s1 :
  kinv (s0, s1) ->
  heap_ignore IGNK (s0, s1) /\
  RK (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_prf_pk_loc) (get_heap s1 r_prf_log_loc) (get_heap s1 r_prf_sig_loc)
     (get_heap s1 prf_k_loc') (get_heap s1 prf_qs_loc').
Proof. by move=> [h1 h2]; split. Qed.

Lemma kinvI s0 s1 :
  heap_ignore IGNK (s0, s1) ->
  RK (get_heap s0 (forge_pk_loc P)) (get_heap s0 (forge_log_loc P)) (get_heap s0 (forge_sig_loc P))
     (get_heap s1 r_prf_pk_loc) (get_heap s1 r_prf_log_loc) (get_heap s1 r_prf_sig_loc)
     (get_heap s1 prf_k_loc') (get_heap s1 prf_qs_loc') ->
  kinv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** Instantiating the generic PRF-derived-keys loop machinery

    The block precondition [kblk], its update lemmas, the single-step
    FQUERY couplings, and the loop inductions now live in
    [Sec.lib.games.prf_derive].  They are called below at
    [Kh := khf_prf], the concrete PRF tweak [tw i = (pp, prf_tweak P i)]
    and evaluation [ev k i = PRF pp (prf_adrs P i) k], and the ambient
    ignore-set [IGNK].  The three obligations that instantiation owes —
    exact-tweak injectivity on the [chain_count] indices and the two
    PRF-location memberships — are discharged here. *)

(** The block precondition of the loop, pinned to this hop's [khf_prf]
    and ignore-set [IGNK]. *)
Local Abbreviation kblk' := (kblk khf_prf IGNK).
Arguments kblk : simpl never.

(** Exact-tweak injectivity in the pair form the loop's [tw] needs:
    distinct chains query distinct PRF inputs (conditional on the two
    chain indices being in range, as [prf_tweak_inj] requires). *)
Lemma prf_tw_inj (pp : wcp_PP P) (i j : nat) :
  (i < wcp_chain_count P)%N -> (j < wcp_chain_count P)%N ->
  (pp, prf_tweak P i) = (pp, prf_tweak P j) -> i = j.
Proof.
move=> hi hj e.
apply: (prf_tweak_inj P i j hi hj).
exact: (congr1 (fun p : wcp_PP P * wc_adrs_ch P => p.2) e).
Qed.

(** The two PRF locations live in this hop's ignore-set. *)
Lemma prf_k_in : (prf_k_loc khf_prf).1 \in domm IGNK.
Proof. by rewrite mem_domm. Qed.

Lemma prf_qs_in : (prf_qs_loc khf_prf).1 \in domm IGNK.
Proof. by rewrite mem_domm. Qed.

(* ------------------------------------------------------------------ *)
(** ** The common COMMIT tail

    Both sides store the same key/log/signature values and return the
    same result; the invariant is re-established with a trivially-true
    committed branch. *)

Lemma r_prf_tail (pp : wcp_PP P) (m : wcp_M P) (c : nat) (xs : seq (wcp_N P))
    (ko : option K) (ms : seq (kh_M khf_prf)) :
  ⊢ ⦃ λ '(s0, s1), kblk' ko ms (s0, s1) ⦄
     (#put (forge_pk_loc P) := Some (pp, shrincs_wots_pubkey P pp xs) ;;
      #put (forge_log_loc P) := [:: m] ;;
      #put (forge_sig_loc P) := Some (sign_chains P pp xs (digest_of P pp m c), c) ;;
      ret ((pp, shrincs_wots_pubkey P pp xs), Some (sign_chains P pp xs (digest_of P pp m c), c)))
   ≈ (#put r_prf_pk_loc := Some (pp, shrincs_wots_pubkey P pp xs) ;;
      #put r_prf_log_loc := [:: m] ;;
      #put r_prf_sig_loc := Some (sign_chains P pp xs (digest_of P pp m c), c) ;;
      ret ((pp, shrincs_wots_pubkey P pp xs), Some (sign_chains P pp xs (digest_of P pp m c), c)))
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 /\ kinv (s0, s1) ⦄.
Proof.
do 3 eapply r_put_lhs.
do 3 eapply r_put_rhs.
apply r_ret => s0 s1 hpre.
case: hpre => s1c [hpre1 ->].
case: hpre1 => s1d [hpre2 ->].
case: hpre2 => s1e [hpre3 ->].
case: hpre3 => s0c [hpre4 ->].
case: hpre4 => s0d [hpre5 ->].
case: hpre5 => s0e [hblk ->].
case: hblk => hign hko hqs.
split; first by [].
apply: kinvI.
- do 3 (apply: heap_ignore_set_l; first by rewrite mem_domm).
  do 3 (apply: heap_ignore_set_r; first by rewrite mem_domm).
  exact: hign.
- simplify_heap_reads.
  by split.
Qed.

(** From the block precondition (the invariant plus the two remembered
    public-key reads), the game's key equals R's copy -- [RK]'s first
    conjunct.  Discharges the [sync_eq pko pko'] equality side goal, shared
    by COMMIT and the real-KOTS-bit KFORGE branch on both sides. *)
Lemma sync_pko_eq (pko : forge_pk_loc P) (pko' : r_prf_pk_loc) (s0 s1 : heap) :
  (kinv ⋊ rem_lhs (forge_pk_loc P) pko ⋊ rem_rhs r_prf_pk_loc pko') (s0, s1) ->
  pko' = pko.
Proof.
move=> [[hinv hrem0] hrem1].
case/kinvE: hinv => _ [e1 _ _ _].
rewrite /rem_inv /= in hrem0 hrem1.
by rewrite -hrem0 -hrem1.
Qed.

(** [sync_pko]: remember the two public-key reads and identify them via
    [sync_pko_eq], leaving the continuation with [pko'] substituted away.
    Factors the block that recurs 4x across the real/ideal COMMIT and KFORGE. *)
Local Ltac sync_pko :=
  sync_eq pko pko';
  [ by move=> ? ? /sync_pko_eq -> | move=> -> ].

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence

    [Hcc] is a data-level side condition of the REAL side only (see
    header): the first query is where the hidden key gets sampled. *)

Lemma R_prf_real (b : bool) :
  perfect (I_KOTS (shrincs_wots_scheme P)) (G_forge_keyed b) (R_prf b ∘ PRF_game khf_prf (wcp_chain_count P) true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ kinv).
{ rewrite /kinv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), kblk' None [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/kinvE: hinv => hign hRK.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRK => _ _ _; rewrite hrem0 => -[_ _ hko hqs].
    by split. }
  simpl.
  (* couple the public-parameter sample *)
  rewrite code_link_bind.
  rewrite (code_link_scheme _ _ _ _ (prog_valid (wcp_dPP P))).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  (* the grinding assert, on both sides *)
  rewrite code_link_assertD.
  eapply r_assertD_same => e1.
  (* the derivation loop: eager k ← dK vs the lazily-keyed queries.
     Instantiate the generic loop lemma at this hop's tweak/eval/ignore-set. *)
  rewrite (code_link_bind (prf_sks khf_prf (fun i => (pp, prf_tweak P i)) 0 (wcp_chain_count P))).
  eapply (r_prf_sks_first khf_prf (wcp_chain_count P)
            (fun i => (pp, prf_tweak P i)) (prf_tw_inj pp)
            (fun k i => PRF pp (prf_adrs P i) k) (fun k i => kh_eval_ptw k pp i)
            IGNK prf_k_in prf_qs_in (wcp_chain_count P) 0).
  + exact: (wcp_Hcc P).
  + by rewrite add0n.
  + move=> kk; exact: r_prf_tail.
- (* KFORGE: local on both sides *)
  destruct arg as [mst sgst].
  simpl.
  sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/kinvE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  case: b => /=;
    apply r_ret => s0 s1 hpre; split=> //;
    by case: hpre => [[[[hinv _] _] _] _].
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence *)

Lemma R_prf_ideal (b : bool) :
  perfect (I_KOTS (shrincs_wots_scheme P)) (G_forge_sampledkey P b) (R_prf b ∘ PRF_game khf_prf (wcp_chain_count P) false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ kinv).
{ rewrite /kinv; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  case: pko e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), kblk' None [::] (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    case/kinvE: hinv => hign hRK.
    rewrite /rem_inv /= in hrem0 hrem1.
    case: hRK => _ _ _; rewrite hrem0 => -[_ _ hko hqs].
    by split. }
  simpl.
  rewrite code_link_bind.
  rewrite (code_link_scheme _ _ _ _ (prog_valid (wcp_dPP P))).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite code_link_assertD.
  eapply r_assertD_same => e1.
  (* couple the chain-start samples with the ideal queries *)
  rewrite (code_link_bind (prf_sks khf_prf (fun i => (pp, prf_tweak P i)) 0 (wcp_chain_count P))).
  eapply (r_prf_sks_ideal khf_prf (wcp_chain_count P)
            (fun i => (pp, prf_tweak P i)) (prf_tw_inj pp)
            IGNK prf_qs_in (wcp_chain_count P) 0).
  + by rewrite add0n.
  + move=> xs hxs; exact: r_prf_tail.
- (* KFORGE: identical to the real-side case (the PRF bit is spent) *)
  destruct arg as [mst sgst].
  simpl.
  sync_pko.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: pko e0 e1 => [pk|] e0 e1; last by discriminate e0.
  simpl.
  sync_eq lg lg'.
    { move=> s0 s1 [[[[hinv _] _] hrem0] hrem1].
      case/kinvE: hinv => _ [_ e2 _ _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1. }
  move=> e; subst lg'.
  case: b => /=;
    apply r_ret => s0 s1 hpre; split=> //;
    by case: hpre => [[[[hinv _] _] _] _].
Qed.

End PrfHop.
