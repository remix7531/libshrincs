(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.wotsc.games

    Game-instance scaffolding for the WOTS+C one-time security proof: the
    [thf] /
    [thf_coll] instances for the three tweakable hash functions under
    attack (F, Theta_l, Hgrind), and the valid-commit known-message
    game pair [G0w] / [G1w] (definitions only; the hops live in later
    P5 files).

    Counterparts: wotsc.tex sec:wotsc (one-time security paragraph),
    construction.tex sec:functions (the collection Th_lambda sharing
    one PKseed). [G0w]/[G1w] instantiate the generic fixed-sum WOTS
    [G0v]/[G1v] structure with the
    WOTS+C scheme operations (grinding, pk compression, concrete
    stateful addresses); the SM-UD re-rooting machinery
    ([sample_sig_roots]) is REUSED from wots.games at the
    address-wrapped chain hash [Fw].

    ** The thf instances (documented th_* choices)

    All three instances share th_PP := PP (PKseed) and
    th_T := [adrs_sf_ch], the encoded stateful address space of
    SHRINCS.addressing (thf tweaks must be a [choice_type]; the
    scheme's structured [adrs_sf] addresses enter via [encode_adrs],
    and [th_eval] decodes with the proven-cancelling [decode_tweak] —
    the junk branch on non-canonical tuples is dead code, see
    [th_evalE_*]):

    - [Tf]  (chain hash F):           th_M := N, th_N := N;
            samplers dN/dN (SM-PRE samples hidden inputs, SM-UD ideal
            samples outputs — both n-byte strings).
    - [Tpk] (pk compression Theta_l): th_M := 'list N (the l chain
            ends), th_N := N; only SM-TCR is assumed on Theta_l, which
            never samples th_M/th_N, so th_dM is a dummy (ret [::]).
    - [Tgr] (grinding hash Hgrind):   th_M := M × 'nat (message,
            counter — STCRP's [enc m c := (m, c)]), th_N := 'nat (the
            digest as a [nat], parsed base-w downstream, exactly as in
            wotsc.scheme); only S-TCR(Prop) is assumed on Hgrind,
            which never samples th_M/th_N, so both samplers are
            dummies (th_dM needs SOME inhabitant of M, whence the
            section parameter [dM] — data only, never used by the
            games; instantiations have a canonical 2n-bit-string
            sampler).

    ** Collections

    Each instance's collection exposes the OTHER members of the
    SHRINCS collection that the P5 reductions must evaluate under the
    still-hidden PKseed (preliminaries.tex notion:thl; the EasyCrypt
    `*C` game variants):
    - [Cf]: Theta_l and Hgrind.  The SM-UD/SM-TCR/SM-PRE reductions
      on F must compute the grinded digest BEFORE their first query
      (the digest determines the queried tweaks), hence Hgrind;
      Theta_l is included for uniformity (pk compression could also
      wait until after GETPP).
    - [Cpk]: F and Hgrind.  The SM-TCR(Theta_l) reduction must commit
      the honest chain ends as its target before GETPP, and those are
      F-chains over an Hgrind digest.
    - [Cgr]: F and Theta_l.  (STCRP's SQUERY does the grinding
      in-oracle and nothing forces queries after the digest, so the
      trivial collection would do; the symmetric choice is free.)
    Tweaks of collection members are also encoded addresses; inputs
    and outputs are tagged with the evident sums.

    ** The STCRP instantiation for Hgrind

    Mb := M, [grind_enc m c := (m, c)], [grind_prp] := the digit-sum
    predicate (decode base-w, check [valid_digest] — exactly
    [good_ctr]'s structure), cap := c_max.  [grind_search_find_ctr]
    proves that STCRP's in-oracle bounded search at the encoded
    grinding address IS the scheme's [find_ctr].

    ** G0w / G1w (the valid-commit game pair)

    [G0w] is the known-message game (Sec.lib.sig.kots) for the shrincs_fxmss_wots_scheme
    scheme, flattened into one self-contained package, in the
    VALID-COMMIT variant: COMMIT [#assert]s grinding success
    ([isSome (find_ctr ...)]) right after sampling PKseed, so a
    grinding failure aborts the experiment and COMMIT always signs.
    This is fixed_sum_scheme's G0v pattern (the proof architecture edge-case
    decision there): after a refusal nothing is revealed, and
    bounding refusal-branch forgeries needs targets at EVERY position
    with no consumer — in SHRINCS, shrincs_fxmss_scheme only ever signs grindable
    digests by construction.  Documented deviation from the plain
    [KOTS_game shrincs_fxmss_wots_scheme].

    Beyond G0v, COMMIT also stores the issued signature (chain
    values + counter) in [g0w_sig_loc]: KFORGE never reads it, but
    the later reduction hops need the signed data and sharing one
    location set keeps their invariants small (as Gmid did in
    wots.tcr_hop).

    [G1w] is the post-SM-UD-hybrid game: the grinding still happens
    (digest first — it determines the chain digits), then each
    chain's signature value is sampled RE-ROOTED at its digit
    position via fixed_sum_scheme's [sample_sig_roots] at [Fw] (digit 0:
    the value itself is a fresh uniform; digit d > 0: a hidden
    uniform sits one hash step below, [σ_i = F (chain_adrs i (d-1))
    u_i] — the SM-PRE oracle's distribution), and the public key is
    the Theta_l compression of the chain ends completed from the
    signature values ([complete_ends], the verifier's own
    completion).

    Location ids 900+ (moved off 300+: collided with Sec.wots.games). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From Sec.lib Require Import prelude math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme sig.kots games.thf games.smtcr games.smpre games.smud games.stcrp toolkit.sample_seq.
From Sec.lib Require Import chain.core wots.games.
From SHRINCS Require Import addressing wotsc.scheme.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Decoding tweaks (shared by all three thf instances)

    The native tweak space is exactly finite, so decoding is total and
    bijective.  There is no non-canonical tuple and no dummy branch. *)

Section DecodeTweak.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

Definition decode_tweak (t : adrs_sf_ch) : adrs_sf := decode_adrs t.

Lemma decode_tweakK : cancel encode_adrs decode_tweak.
Proof. exact: encode_adrsK. Qed.

End DecodeTweak.

Section WOTSCGames.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same section context as SHRINCS.wotsc.Scheme, plus the dummy
    message sampler [dM] (consumed ONLY by [Tgr]'s [th_dM] record
    field, see header). *)
Context (PP N M : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> M * nat -> nat).
Context (dPP : dist PP) (dN : dist N) (dM : dist M).
Context (S_wn c_max : nat).
Context (zstar istar : nat).

(** Shorthands for the section-instantiated scheme operations. *)
Local Notation gadrs := (grind_adrs zstar istar).
Local Notation cadrs := (chain_adrs zstar istar).
Local Notation padrs := (pk_adrs zstar istar).
Local Notation wdigest := (digest_of PP M Hgrind zstar istar).
Local Notation wgood := (good_ctr PP M Hgrind S_wn zstar istar).
Local Notation wfind_ctr :=
  (find_ctr PP M Hgrind S_wn c_max zstar istar).
Local Notation wpk_of := (shrincs_fxmss_wots_public_key PP N F Tl zstar istar).
Local Notation wsign := (sign_digits PP N F zstar istar).
Local Notation wcends := (complete_ends PP N F zstar istar).
Local Notation wverify :=
  (shrincs_fxmss_wots_verify PP N M F Tl Hgrind S_wn zstar istar).

(* ------------------------------------------------------------------ *)
(** ** The three thf instances (th_* choices in the header) *)

Definition Tf : thf :=
  {| th_PP := PP ; th_T := adrs_sf_ch ; th_M := N ; th_N := N ;
     th_eval := fun pp t x => F pp (decode_tweak t) x ;
     th_dPP := dPP ; th_dM := dN ; th_dN := dN |}.

Definition Tpk : thf :=
  {| th_PP := PP ; th_T := adrs_sf_ch ; th_M := 'list N ; th_N := N ;
     th_eval := fun pp t xs => Tl pp (decode_tweak t) xs ;
     th_dPP := dPP ; th_dM := {code ret ([::] : seq N) } ; th_dN := dN |}.

Definition Tgr : thf :=
  {| th_PP := PP ; th_T := adrs_sf_ch ; th_M := M × 'nat ; th_N := 'nat ;
     th_eval := fun pp t mc => Hgrind pp (decode_tweak t) mc ;
     th_dPP := dPP ;
     th_dM := {code m ← dM ;; ret (m, 0) } ;
     th_dN := {code ret 0 } |}.

(** Sanity: on encoded (canonical) tweaks the instances evaluate the
    scheme's functions — the consumers' interface to [th_eval]. *)
Lemma th_evalE_Tf pp (a : adrs_sf) (x : N) :
  th_eval Tf pp (encode_adrs a) x = F pp a x.
Proof. by rewrite /= decode_tweakK. Qed.

Lemma th_evalE_Tpk pp (a : adrs_sf) (xs : seq N) :
  th_eval Tpk pp (encode_adrs a) xs = Tl pp a xs.
Proof. by rewrite /= decode_tweakK. Qed.

Lemma th_evalE_Tgr pp (a : adrs_sf) (mc : M * nat) :
  th_eval Tgr pp (encode_adrs a) mc = Hgrind pp a mc.
Proof. by rewrite /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** ** Collections (header: each instance exposes the other two) *)

Definition Cf : thf_coll Tf :=
  Build_thf_coll Tf adrs_sf_ch (('list N) ∐ (M × 'nat)) (N ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl xs => inl (Tl pp (decode_tweak t) xs)
       | inr mc => inr (Hgrind pp (decode_tweak t) mc)
       end).

Definition Cpk : thf_coll Tpk :=
  Build_thf_coll Tpk adrs_sf_ch (N ∐ (M × 'nat)) (N ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr mc => inr (Hgrind pp (decode_tweak t) mc)
       end).

Definition Cgr : thf_coll Tgr :=
  Build_thf_coll Tgr adrs_sf_ch (N ∐ ('list N)) (N ∐ N)
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr xs => inr (Tl pp (decode_tweak t) xs)
       end).

(* ------------------------------------------------------------------ *)
(** ** The STCRP instantiation for Hgrind

    Sec.lib.games.stcrp is parameterized by (Mb, enc, prp, cap); the
    grinding instance is Mb := M, enc := pairing with the counter,
    prp := the digit-sum predicate on the decoded digest, cap :=
    c_max (the bounded-search deviation documented in STCRP.v matches
    the scheme's [find_ctr] exactly). *)

Definition grind_enc (m : M) (c : nat) : M * nat := (m, c).

Definition grind_prp (x : nat) : bool :=
  @valid_digest w S_wn (digits_w w l x).

(** STCRP's in-oracle search at the encoded grinding address is the
    scheme's grinding ([find_ctr]); in particular the counter stored
    with the SQUERY target is the signed counter, and SQUERY aborts
    exactly when COMMIT's grinding assert fails. *)
Lemma grind_search_find_ctr pp (m : M) :
  ohead [seq i <- iota 0 c_max
        | grind_prp (th_eval Tgr pp (encode_adrs gadrs) (grind_enc m i))]
  = wfind_ctr pp m.
Proof.
rewrite /find_ctr; congr ohead; apply: eq_filter => i.
rewrite /grind_prp /good_ctr /digest_of /= decode_tweakK.
by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The address-wrapped chain hash

    [Fw] is [F] at this instance's chain addresses, in the abstract
    (chain index, position) tweak shape of [Sec.lib.chain.core]. This bridge
    lets the generic chain analysis and [sample_sig_roots] re-rooting
    machinery be reused directly. *)

Definition Fw (pp : PP) (t : nat * nat) (x : N) : N :=
  F pp (cadrs t.1 t.2) x.

(** [Fw]'s chain steps are the scheme's ([chainf] of wotsc.scheme ==
    [chainf] of wots.scheme at [Fw]); stated once so consumers
    can rewrite instead of relying on conversion. *)
Lemma chainf_Fw pp i :
  Sec.lib.chain.core.chainf PP N Fw pp i
  = chainf PP N F zstar istar pp i.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** G0w: the flat valid-commit known-message game *)

Local Notation WC :=
  (shrincs_fxmss_wots_scheme PP N M F Tl Hgrind dPP dN S_wn c_max zstar istar).

(* ids 900+, not 300+: 300-302 collide with Sec.wots.games's
   [forge_pk/log/sig_loc] (see proof/LOCATIONS.md). *)
Definition g0w_pk_loc := mkloc 900 (None : option (Pk WC)).
Definition g0w_log_loc := mkloc 901 ([::] : seq (Msg WC)).
Definition g0w_sig_loc := mkloc 902 (None : option (Sig WC)).

Definition G0w (b : bool) : game (I_KOTS WC) :=
  [package [fmap g0w_pk_loc ; g0w_log_loc ; g0w_sig_loc ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get g0w_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      #assert (isSome (wfind_ctr pp m)) ;;
      let c := odflt 0 (wfind_ctr pp m) in
      xs ← sample_seq dN l ;;
      #put g0w_pk_loc := Some (pp, wpk_of pp xs) ;;
      #put g0w_log_loc := [:: m] ;;
      #put g0w_sig_loc := Some (wsign pp xs (wdigest pp m c), c) ;;
      ret ((pp, wpk_of pp xs), Some (wsign pp xs (wdigest pp m c), c))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0w_pk_loc ;;
        log ← get g0w_log_loc ;;
        ret (wverify pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(** Sanity (pure correctness through the assert + odflt plumbing):
    the signature G0w issues verifies under the pk it stores. *)
Lemma G0w_sign_verifies pp (xs : seq N) (m : M) :
  size xs = l -> isSome (wfind_ctr pp m) ->
  wverify pp (wpk_of pp xs) m
    (wsign pp xs (wdigest pp m (odflt 0 (wfind_ctr pp m))),
     odflt 0 (wfind_ctr pp m)).
Proof.
move=> hxs; case E: (wfind_ctr pp m) => [c|] // _ /=.
by rewrite (shrincs_fxmss_wots_verify_digits PP N M F Tl Hgrind S_wn c_max zstar istar
  pp xs m c hxs E).
Qed.

(* ------------------------------------------------------------------ *)
(** ** G1w: the post-UD-hybrid game (definition only; header) *)

Definition G1w (b : bool) : game (I_KOTS WC) :=
  [package [fmap g0w_pk_loc ; g0w_log_loc ; g0w_sig_loc ] ;
    [ COMMIT ] : { SParam WC × Msg WC ~> Pk WC × 'option (Sig WC) } '(sp, m) {
      pko ← get g0w_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      pp ← dPP ;;
      #assert (isSome (wfind_ctr pp m)) ;;
      let c := odflt 0 (wfind_ctr pp m) in
      sg ← sample_sig_roots PP N Fw dN pp 0 (wdigest pp m c) ;;
      #put g0w_pk_loc := Some (pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)) ;;
      #put g0w_log_loc := [:: m] ;;
      #put g0w_sig_loc := Some (sg, c) ;;
      ret ((pp, Tl pp padrs (wcends pp (wdigest pp m c) sg)), Some (sg, c))
    } ;
    [ KFORGE ] : { Msg WC × Sig WC ~> 'bool } '(m, s) {
      if b then
        pk ← getSome g0w_pk_loc ;;
        log ← get g0w_log_loc ;;
        ret (wverify pk.1 pk.2 m s && (m \notin log))
      else
        ret false
    }
  ].

(** The grinding assert in code form delivers exactly the pure fact
    the analysis layer consumes ([good_ctr] at the signed counter). *)
Lemma find_ctr_isSome_good pp (m : M) :
  isSome (wfind_ctr pp m) -> wgood pp m (odflt 0 (wfind_ctr pp m)).
Proof.
case E: (wfind_ctr pp m) => [c|] //= _.
exact: (find_ctr_good PP M Hgrind S_wn c_max zstar istar pp m c E).
Qed.

End WOTSCGames.
