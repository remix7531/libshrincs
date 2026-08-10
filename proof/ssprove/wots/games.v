(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.games

    Game-instance scaffolding for the WOTS+C one-time security proof:
    the [thf] / [thf_coll] instances for the three tweakable hash
    functions under attack (F, T_sf, H_grind), and the valid-commit
    known-message game pair [G_forge_sampledkey] /
    [G_forge_uniformchains] (definitions only; the hops live in later
    files).

    [G_forge_sampledkey]/[G_forge_uniformchains] are the generic
    known-message game pair specialized to the WOTS+C scheme operations
    (grinding, pk compression, concrete stateful addresses); the SM-UD
    re-rooting machinery ([sample_sig_roots]) comes from the chain
    library (Sec.lib.chain) at the address-wrapped chain hash [Fw].

    ** The thf instances (documented th_* choices)

    All three instances share th_PP := PP (PKseed) and
    th_T := [wc_adrs_ch P], the encoded stateful address space of
    Sec.addressing (thf tweaks must be a [choice_type]; the
    scheme's structured [wc_adrs P] addresses enter via [encode_tweak],
    and [th_eval] decodes with the proven-cancelling [decode_tweak] —
    the junk branch on non-canonical tuples is dead code, see
    [th_evalE_*]):

    - [thf_chain]  (chain hash F):           th_M := N, th_N := N;
            samplers dN/dN (SM-PRE samples hidden inputs, SM-UD ideal
            samples outputs — both n-byte strings).
    - [thf_pkcompress] (pk compression T_sf): th_M := 'list N (the chain_count chain
            ends), th_N := N; only SM-TCR is assumed on T_sf, which
            never samples th_M/th_N, so th_dM is a dummy (ret [::]).
    - [thf_grind] (grinding hash H_grind):   th_M := M × 'nat (message,
            counter — STCRP's [enc m c := (m, c)]), th_N := 'nat (the
            digest as a [nat], parsed base-w downstream, exactly as in
            Sec.wots.scheme); only S-TCR(Prop) is assumed on H_grind,
            which never samples th_M/th_N, so both samplers are
            dummies (th_dM needs SOME inhabitant of M, whence the
            record field [wcp_dM] — data only, never used by the
            games; instantiations have a canonical 2n-bit-string
            sampler).

    ** Collections

    Each instance's collection exposes the OTHER members of the
    collection that the reductions must evaluate under the
    still-hidden PKseed:
    - [coll_chain]: T_sf and H_grind.  The SM-UD/SM-TCR/SM-PRE reductions
      on F must compute the grinded digest BEFORE their first query
      (the digest determines the queried tweaks), hence H_grind;
      T_sf is included for uniformity (pk compression could also
      wait until after GETPP).
    - [coll_pkcompress]: F and H_grind.  The SM-TCR(T_sf) reduction must commit
      the honest chain ends as its target before GETPP, and those are
      F-chains over an H_grind digest.
    - [coll_grind]: F and T_sf.  (STCRP's SQUERY does the grinding
      in-oracle and nothing forces queries after the digest, so the
      trivial collection would do; the symmetric choice is free.)
    Tweaks of collection members are also encoded addresses; inputs
    and outputs are tagged with the evident sums.

    ** The STCRP instantiation for H_grind

    Mb := M, [grind_enc m c := (m, c)], [grind_prp] := the digit-sum
    predicate (decode base-w, check [valid_digest] — exactly
    [good_counter]'s structure), cap := c_max.  [grind_search_find_ctr]
    proves that STCRP's in-oracle bounded search at the encoded
    grinding address IS the scheme's [find_counter].

    ** G_forge_sampledkey / G_forge_uniformchains (the valid-commit game pair)

    [G_forge_sampledkey] is the known-message game (Sec.lib.sig.kots) for the
    shrincs_wots_scheme scheme, flattened into one self-contained package, in the
    VALID-COMMIT variant: COMMIT [#assert]s grinding success
    ([isSome (find_counter ...)]) right after sampling PKseed, so a
    grinding failure aborts the experiment and COMMIT always signs.
    Rationale: after a refusal nothing is revealed, and bounding
    refusal-branch forgeries would need targets at EVERY position
    with no consumer — and the tree layer only ever signs grindable
    digests by construction.  This is the VALID-COMMIT variant
    [KOTS_vc_game shrincs_wots_scheme] (Sec.lib.sig.kots), not the
    plain [KOTS_game]; the correspondence between this flat game (and
    its keyed sibling [G_forge_keyed], Sec.wots.hop.prf) and
    [KOTS_vc_game] is now MACHINE-CHECKED, unconditionally and
    perfectly, in Sec.wots.kots_link — no longer a merely-documented
    deviation.

    COMMIT also stores the issued signature (chain values + counter)
    in [forge_sig_loc]: KFORGE never reads it, but the later reduction
    hops need the signed data and sharing one location set keeps their
    invariants small.

    [G_forge_uniformchains] is the
    post-SM-UD-hybrid game, named for its state: the signature chain
    values are uniform (re-rooted) rather than chain-folded from a
    sampled key.  The grinding still happens (digest first — it
    determines the chain digits), then each chain's signature value is
    sampled RE-ROOTED at its digit position via [sample_sig_roots] at
    [Fw] (digit 0: the value itself is a fresh uniform; digit d > 0: a
    hidden uniform sits one hash step below,
    [σ_i = F (chain_adrs P i (d-1)) u_i] — the SM-PRE oracle's
    distribution), and the public key is the T_sf compression of the
    chain ends completed from the signature values ([complete_ends],
    the verifier's own completion).

    ** Shared reduction vocabulary ([wsigs] and friends)

    The tail of this file names the chain library's query/decision
    combinators at this instance's [Fw] once ([wsigs], [wends],
    [wcommitq], [wpreq], [wtcr_dec], [wpre_dec]), so the hop and bound
    files share one spelling instead of each pinning the applications
    locally.

    Location ids 300+. *)

From Sec.lib Require Import prelude sig.scheme sig.kots
  games.thf games.smtcr games.smpre games.smud games.stcrp toolkit.sample_seq.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Sec.lib Require Import chain.core.
From Sec Require Import addressing.
From Sec.wots Require Import scheme.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ================================================================== *)
(** ** The hash-game instances over the anchor-free core

    Every instance a hash ASSUMPTION quantifies over is defined here,
    over [wc_params_core] (see params.v): the games can provably not
    see the anchor.  The [wc_params] spellings further below are
    transparent wrappers over [wc_core_of P], so nothing downstream
    changes -- the two spellings coincide by conversion. *)

Section WOTSCGamesCore.

Context (H : wc_params_core).

Definition thf_chain_core : thf :=
  {| th_PP := wcc_PP H ; th_T := wc_adrs_ch_core H ; th_M := wcc_N H ; th_N := wcc_N H ;
     th_eval := fun pp t x => wcc_F H pp (decode_tweak_core H t) x ;
     th_dPP := wcc_dPP H ; th_dM := wcc_dN H ; th_dN := wcc_dN H |}.

Definition thf_pkcompress_core : thf :=
  {| th_PP := wcc_PP H ; th_T := wc_adrs_ch_core H ; th_M := 'list (wcc_N H) ; th_N := wcc_N H ;
     th_eval := fun pp t xs => wcc_T_sf H pp (decode_tweak_core H t) xs ;
     th_dPP := wcc_dPP H ; th_dM := {code ret ([::] : seq (wcc_N H)) } ; th_dN := wcc_dN H |}.

Definition thf_grind_core : thf :=
  {| th_PP := wcc_PP H ; th_T := wc_adrs_ch_core H ; th_M := wcc_M H × 'nat ; th_N := 'nat ;
     th_eval := fun pp t mc => wcc_H_grind H pp (decode_tweak_core H t) mc ;
     th_dPP := wcc_dPP H ;
     th_dM := {code m ← wcc_dM H ;; ret (m, 0) } ;
     th_dN := {code ret 0 } |}.

Definition coll_chain_core : thf_coll thf_chain_core :=
  Build_thf_coll thf_chain_core (wc_adrs_ch_core H) (('list (wcc_N H)) ∐ (wcc_M H × 'nat)) ((wcc_N H) ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl xs => inl (wcc_T_sf H pp (decode_tweak_core H t) xs)
       | inr mc => inr (wcc_H_grind H pp (decode_tweak_core H t) mc)
       end).

Definition coll_pkcompress_core : thf_coll thf_pkcompress_core :=
  Build_thf_coll thf_pkcompress_core (wc_adrs_ch_core H) ((wcc_N H) ∐ (wcc_M H × 'nat)) ((wcc_N H) ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl y => inl (wcc_F H pp (decode_tweak_core H t) y)
       | inr mc => inr (wcc_H_grind H pp (decode_tweak_core H t) mc)
       end).

Definition coll_grind_core : thf_coll thf_grind_core :=
  Build_thf_coll thf_grind_core (wc_adrs_ch_core H) ((wcc_N H) ∐ ('list (wcc_N H))) ((wcc_N H) ∐ (wcc_N H))
    (fun pp t x =>
       match x with
       | inl y => inl (wcc_F H pp (decode_tweak_core H t) y)
       | inr xs => inr (wcc_T_sf H pp (decode_tweak_core H t) xs)
       end).

Definition grind_enc_core (m : wcc_M H) (c : nat) : wcc_M H * nat := (m, c).

(** [scheme.valid_digest] spelled over the core fields (w and the
    target sum are core data), MSB-first as there. *)
Definition grind_prp_core (x : nat) : bool :=
  wf_digits (wcc_w H) (rev (digits_w (wcc_w H) (wcc_chain_count H) x))
  && (sumn (rev (digits_w (wcc_w H) (wcc_chain_count H) x)) == wcc_constant_sum H).

End WOTSCGamesCore.

Section WOTSCGames.

(** The WOTS+C parameter record (see Sec.wots.params). *)
Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** ** The three thf instances (th_* choices in the header)

    [th_eval] must be total on the encoded tweak space [wc_adrs_ch P];
    [decode_tweak] is a TOTAL structural round trip (see params.v /
    addressing.v), so no default/fallback is needed here at all.
    All are wrappers over the core instances above. *)

Definition thf_chain : thf := thf_chain_core (wc_core_of P).

Definition thf_pkcompress : thf := thf_pkcompress_core (wc_core_of P).

(** [thf_grind]: the grinding hash, output modeled as a bare [nat] (the
    n-byte digest read base-w by [digits_w]; case-1 soundness rests on
    [digits_w] injectivity below [w^chain_count], i.e. the [grind_range]
    premise of [shrincs_wots_secure_ideal_sk]).  [th_dM]/[th_dN] are DUMMY
    samplers (data only) — they would be wrong for a search game that
    samples its challenge, so [thf_grind] is only ever used to build
    [STCRP_game thf_grind ...]; it is never instantiated into
    SMUD/SMPRE. *)
Definition thf_grind : thf := thf_grind_core (wc_core_of P).

(** The core decoder at [wc_core_of P] IS the instance decoder (one
    delta each side). *)
Lemma core_decodeE (t : wc_adrs_ch P) :
  decode_tweak_core (wc_core_of P) t = decode_tweak P t.
Proof. by []. Qed.

(** Sanity: on encoded (canonical) tweaks the instances evaluate the
    scheme's functions — the consumers' interface to [th_eval]. *)
Lemma th_evalE_Tf pp (a : wc_adrs P) (x : wcp_N P) :
  th_eval thf_chain pp (encode_tweak P a) x = wcp_F P pp a x.
Proof. by rewrite /th_eval /thf_chain /thf_chain_core /= core_decodeE encode_tweakK. Qed.

Lemma th_evalE_Tpk pp (a : wc_adrs P) (xs : seq (wcp_N P)) :
  th_eval thf_pkcompress pp (encode_tweak P a) xs = wcp_T_sf P pp a xs.
Proof. by rewrite /th_eval /thf_pkcompress /thf_pkcompress_core /= core_decodeE encode_tweakK. Qed.

Lemma th_evalE_Tgr pp (a : wc_adrs P) (mc : wcp_M P * nat) :
  th_eval thf_grind pp (encode_tweak P a) mc = wcp_H_grind P pp a mc.
Proof. by rewrite /th_eval /thf_grind /thf_grind_core /= core_decodeE encode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** ** Collections (header: each instance exposes the other two) *)

Definition coll_chain : thf_coll thf_chain := coll_chain_core (wc_core_of P).

Definition coll_pkcompress : thf_coll thf_pkcompress :=
  coll_pkcompress_core (wc_core_of P).

Definition coll_grind : thf_coll thf_grind := coll_grind_core (wc_core_of P).

(* ------------------------------------------------------------------ *)
(** ** The STCRP instantiation for H_grind

    Sec.lib.games.stcrp is parameterized by (Mb, enc, prp, cap); the
    grinding instance is Mb := M, enc := pairing with the counter,
    prp := the digit-sum predicate on the decoded digest, cap :=
    c_max (the bounded-search deviation documented in stcrp.v matches
    the scheme's [find_counter] exactly). *)

Definition grind_enc (m : wcp_M P) (c : nat) : wcp_M P * nat :=
  grind_enc_core (wc_core_of P) m c.

(** MSB-first, matching [scheme.digest_of]'s [rev] (the predicate is
    rev-invariant -- [wf_digits]/[sumn] don't see order -- but keeping
    the same spelling makes [grind_search_find_ctr] definitional).
    [grind_prp_core] is [valid_digest] one delta away. *)
Definition grind_prp (x : nat) : bool := grind_prp_core (wc_core_of P) x.

(** STCRP's in-oracle search at the encoded grinding address is the
    scheme's grinding ([find_counter]); in particular the counter stored
    with the SQUERY target is the signed counter, and SQUERY aborts
    exactly when COMMIT's grinding assert fails. *)
Lemma grind_search_find_ctr pp (m : wcp_M P) :
  ohead [seq i <- iota 0 (wcp_c_max P)
        | grind_prp (th_eval thf_grind pp (encode_tweak P (grind_adrs P)) (grind_enc m i))]
  = find_counter P pp m.
Proof.
rewrite /find_counter; congr ohead; apply: eq_filter => i.
by rewrite /good_counter /grind_prp /digest_of th_evalE_Tgr.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The address-wrapped chain hash

    [Fw] is [F] at this instance's chain addresses, in the abstract
    (chain index, position) tweak shape of the generic chain library —
    THE bridge that lets the chain library's analysis and its
    [sample_sig_roots] re-rooting machinery apply to WOTS+C. *)

Definition Fw (pp : wcp_PP P) (t : nat * nat) (x : wcp_N P) : wcp_N P :=
  wcp_F P pp (chain_adrs P t.1 t.2) x.

(** [Fw]'s chain steps are the scheme's ([chainf] of Sec.wots.scheme ==
    the chain library's [chainf] at [Fw]); stated once so consumers
    can rewrite instead of relying on conversion. *)
Lemma chainf_Fw pp i :
  Sec.lib.chain.core.chainf (wcp_PP P) (wcp_N P) Fw pp i = chainf P pp i.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Shared reduction vocabulary (header): the chain library's
    query/decision combinators at this instance's [Fw]. *)

Definition wsigs := sigs_of (wcp_PP P) (wcp_N P) Fw.
Definition wends := ends_of (wcp_PP P) (wcp_N P) Fw (wcp_w P).
Definition wcommitq := commit_queries (wcp_PP P) (wcp_N P) Fw (wcp_w P).
Definition wpreq := pre_queries (wcp_N P).
Definition wtcr_dec := tcr_decision (wcp_PP P) (wcp_N P) Fw (wcp_chain_count P) (wcp_w P).
Definition wpre_dec := pre_decision (wcp_PP P) (wcp_N P) Fw (wcp_chain_count P) (wcp_w P).

(* ------------------------------------------------------------------ *)
(** ** G_forge_sampledkey: the flat valid-commit known-message game *)

Definition forge_pk_loc := mkloc 300 (None : option (Pk (shrincs_wots_scheme P))).
Definition forge_log_loc := mkloc 301 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition forge_sig_loc := mkloc 302 (None : option (Sig (shrincs_wots_scheme P))).

Definition G_forge_sampledkey (b : bool) : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap forge_pk_loc ; forge_log_loc ; forge_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P)
                   ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get forge_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      xs ← sample_seq (wcp_dN P) (wcp_chain_count P) ;;
      #put forge_pk_loc := Some (pp, shrincs_wots_pubkey P pp xs) ;;
      #put forge_log_loc := [:: m] ;;
      #put forge_sig_loc := Some (sign_chains P pp xs (digest_of P pp m c), c) ;;
      ret ((pp, shrincs_wots_pubkey P pp xs), Some (sign_chains P pp xs (digest_of P pp m c), c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, s) {
      if b then
        pk ← getSome forge_pk_loc ;;
        log ← get forge_log_loc ;;
        ret (shrincs_wots_verify P pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(** Sanity (pure correctness through the assert + odflt plumbing):
    the signature G_forge_sampledkey issues verifies under the pk it stores. *)
Lemma G_forge_sampledkey_sign_verifies pp (xs : seq (wcp_N P)) (m : wcp_M P) :
  size xs = wcp_chain_count P -> isSome (find_counter P pp m) ->
  shrincs_wots_verify P pp (shrincs_wots_pubkey P pp xs) m
    (sign_chains P pp xs (digest_of P pp m (odflt 0 (find_counter P pp m))),
     odflt 0 (find_counter P pp m)).
Proof.
move=> hxs; case E: (find_counter P pp m) => [c|] // _ /=.
by rewrite (verify_sign P pp xs m c hxs E).
Qed.

(* ------------------------------------------------------------------ *)
(** ** G_forge_uniformchains: the post-UD-hybrid game (definition only;
    header) *)

Definition G_forge_uniformchains (b : bool) : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap forge_pk_loc ; forge_log_loc ; forge_sig_loc ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P)
                   ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get forge_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      sg ← sample_sig_roots (wcp_PP P) (wcp_N P) Fw (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put forge_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc := [:: m] ;;
      #put forge_sig_loc := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, s) {
      if b then
        pk ← getSome forge_pk_loc ;;
        log ← get forge_log_loc ;;
        ret (shrincs_wots_verify P pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(** The grinding assert in code form delivers exactly the pure fact
    the analysis layer consumes ([good_counter] at the signed counter). *)
Lemma find_counter_isSome_good pp (m : wcp_M P) :
  isSome (find_counter P pp m) -> good_counter P pp m (odflt 0 (find_counter P pp m)).
Proof.
case E: (find_counter P pp m) => [c|] //= _.
exact: (find_counter_good P pp m c E).
Qed.

End WOTSCGames.
