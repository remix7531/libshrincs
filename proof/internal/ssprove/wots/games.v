(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.games

    The experiments use one hash instance over encoded messages.
    [thf_hash] samples hidden messages by encoding sampled nodes,
    which is the input distribution required by the chain games.
    [grind_enc] can change both the tweak and the message, and its
    class law makes the bounded search agree with [find_counter].

    [G_forge_sampledkey] and [G_forge_uniformchains] are intermediate
    known-message games. Both abort when grinding fails and store the
    issued signature for the reductions. The latter samples chain roots
    at the signing positions through [sample_sig_roots]. [Fw] connects
    these operations to the generic chain library. Location ids 300+. *)

From Shrincs.internal.ssprove.lib Require Import prelude
  toolkit.sample_seq.
From Shrincs.internal.ssprove.lib Require Import chain.core.
From Shrincs Require Import games.
From Shrincs.internal.ssprove.wots Require Import scheme.


Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section WOTSCGames.

(** The WOTS+C parameter record (see Shrincs.internal.ssprove.wots.params). *)
Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** ** The common hash instance *)

Definition d_hash_message : dist (wcp_HM P) :=
  {code x ← wcp_dN P ;; ret (wcp_encode_node P x)}.

Definition thf_hash : thf :=
  {| th_PP := wcp_PP P ; th_T := wc_adrs_ch P ; th_M := wcp_HM P ; th_N := wcp_N P ;
     th_eval := wcp_Th P ;
     th_dPP := wcp_dPP P ; th_dM := d_hash_message ; th_dN := wcp_dN P |}.

Definition grind_enc (t : wc_adrs_ch P) (m : wcp_M P) (c : nat)
    : wc_adrs_ch P * wcp_HM P :=
  wcp_encode_grind P t m c.

(** Sanity: on encoded tweaks the instances evaluate the scheme's
    functions — the consumers' interface to [th_eval]. *)
Lemma th_evalE_Tf pp (a : wc_adrs P) (x : wcp_N P) :
  th_eval thf_hash pp (encode_tweak P a) (wcp_encode_node P x) = wcp_F P pp a x.
Proof. by []. Qed.

Lemma th_evalE_Tpk pp (a : wc_adrs P) (xs : seq (wcp_N P)) :
  th_eval thf_hash pp (encode_tweak P a) (wcp_encode_ends P xs) = wcp_T_sf P pp a xs.
Proof. by []. Qed.

Lemma th_evalE_Tgr pp (a : wc_adrs P) (m : wcp_M P) (c : nat) :
  th_eval thf_hash pp (grind_enc (encode_tweak P a) m c).1
    (grind_enc (encode_tweak P a) m c).2 = wcp_H_grind P pp a (m, c).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** The STCRP instantiation for H_grind

    The grinding instance encodes the message digest and counter into
    a tweak and a hash message. Its search predicate is the digit-sum
    test, and its counter bound is [c_max]. *)

(** The digits of a grinding hash output sum to the target. *)
Definition grind_prp (g : wcp_G P) : bool :=
  sumn (wcp_digits P g) == wcp_constant_sum P.

(** [grind_prp] is [valid_digest] of the digits: the digit bound that
    [valid_digest] also checks holds for every hash output
    ([wcp_digits_wf]). *)
Lemma grind_prpE (g : wcp_G P) : grind_prp g = valid_digest P (wcp_digits P g).
Proof. by rewrite /valid_digest /wf_digits (wcp_digits_wf P). Qed.

(** STCRP's in-oracle search at the encoded grinding address is the
    scheme's grinding ([find_counter]); in particular the counter stored
    with the SQUERY target is the signed counter, and SQUERY aborts
    exactly when COMMIT's grinding assert fails. *)
Lemma grind_search_find_ctr pp (m : wcp_M P) :
  ohead [seq i <- iota 0 (wcp_c_max P)
        | let q := grind_enc (encode_tweak P (grind_adrs P)) m i in
          if wcp_grind_class P q.1 then grind_prp (th_eval thf_hash pp q.1 q.2) else false]
  = find_counter P pp m.
Proof.
rewrite /find_counter; congr ohead; apply: eq_filter => i.
rewrite /grind_enc (wcp_encode_grind_class P).
by rewrite grind_prpE /good_counter /digest_of /wcp_H_grind.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The address-wrapped chain hash

    [Fw] is [F] at this instance's chain addresses, in the abstract
    (chain index, position) tweak shape of the generic chain library —
    THE bridge that lets the chain library's analysis and its
    [sample_sig_roots] re-rooting machinery apply to WOTS+C. *)

Definition Fw (pp : wcp_PP P) (i : nat) (p : nat) (x : wcp_N P) : wcp_N P :=
  wcp_F P pp (chain_adrs P i p) x.

(* ------------------------------------------------------------------ *)
(** ** Shared reduction vocabulary (header): the chain library's
    query/decision combinators at this instance's [Fw]. *)

Definition wsigs := sigs_of (wcp_PP P) (wcp_N P) (wcp_w P) Fw.
Definition wends := ends_of (wcp_PP P) (wcp_N P) (wcp_w P) Fw.
Definition wcommitq := commit_queries (wcp_PP P) (wcp_N P) (wcp_w P) Fw.
Definition wpreq := pre_queries (wcp_N P).
Definition wtcr_dec := tcr_decision (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) Fw.
Definition wpre_dec := pre_decision (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) Fw.

(* ------------------------------------------------------------------ *)
(** ** G_forge_sampledkey: the flat valid-commit known-message game *)

Definition forge_pk_loc := mkloc 300 (None : option (Pk (shrincs_wots_scheme P))).
Definition forge_log_loc := mkloc 301 ([::] : seq (Msg (shrincs_wots_scheme P))).
Definition forge_sig_loc := mkloc 302 (None : option (wc_sig_parts P)).

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
      ret ((pp, shrincs_wots_pubkey P pp xs),
           Some (wcp_sig_encode P (sign_chains P pp xs (digest_of P pp m c), c)))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, s) {
      pk ← getSome forge_pk_loc ;;
      log ← get forge_log_loc ;;
      if b then
        ret (shrincs_wots_verify P pk.1 pk.2 m (wcp_sig_decode P s) && (m \notin log))
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
      sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) Fw (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put forge_pk_loc := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc := [:: m] ;;
      #put forge_sig_loc := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)),
           Some (wcp_sig_encode P (sg, c)))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(m, s) {
      pk ← getSome forge_pk_loc ;;
      log ← get forge_log_loc ;;
      if b then
        ret (shrincs_wots_verify P pk.1 pk.2 m (wcp_sig_decode P s) && (m \notin log))
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
