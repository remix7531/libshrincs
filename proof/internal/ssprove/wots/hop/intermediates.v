(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.hop.intermediates

    The shared substrate of the WOTS+C game hops, factored out so the
    five hop files type-check IN PARALLEL instead of through a
    grind -> compress -> chain_common serial [Require] chain.

    It collects exactly the pieces that more than one hop needs:

      - the three intermediate games [G_post_grind], [G_post_compress], [G_post_chain].  Each
        nulls one more KFORGE forgery case than the previous; the
        COMMIT body is identical to G_forge_uniformchains's throughout.  [G_post_grind] starts
        the Grind hop's target, [G_post_compress] the Compress hop's, [G_post_chain]
        the two chain hops';

      - the pure grinding-search picker [cp_pick] (+ [cp_zip_filter],
        [cp_pick_map]) and the two evaluation bridges [digestE],
        [wendsE], all used by both [Sec.hop.compress] and the chain
        hops.

    Everything here is pure (games and rewrite lemmas); the reductions
    and relational proofs stay in their per-hop files. *)

From mathcomp.experimental_reals Require Import distr.
From Shrincs.internal.ssprove.lib Require Import prelude sig.scheme sig.kots
  chain.core.
From Shrincs.internal.common Require Import math.chain math.encoding.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import scheme games analysis.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Intermediates.

Context (P : wc_params).

(* ------------------------------------------------------------------ *)
(** ** The grinding-search picker (pure)

    [cp_pick] returns the first (counter, digest value) the grinding
    predicate accepts; on the honest answer list it IS the scheme's
    grinding ([cp_pick_map]). *)

Definition cp_pick (hs : seq nat) : option (nat * nat) :=
  ohead [seq ch <- zip (iota 0 (wcp_c_max P)) hs | grind_prp P ch.2].

Lemma cp_zip_filter (f : nat -> nat) (p : nat -> bool) (cs : seq nat) :
  ohead [seq ch <- zip cs [seq f c | c <- cs] | p ch.2]
  = omap (fun c => (c, f c)) (ohead [seq c <- cs | p (f c)]).
Proof.
elim: cs => [|c cs IH] //=.
by case: (p (f c)) => /=; [|exact: IH].
Qed.

Lemma cp_pick_map (pp : wcp_PP P) (m : wcp_M P) :
  cp_pick [seq wcp_H_grind P pp (grind_adrs P) (m, c) | c <- iota 0 (wcp_c_max P)]
  = omap (fun c => (c, wcp_H_grind P pp (grind_adrs P) (m, c))) (find_counter P pp m).
Proof. by rewrite /cp_pick cp_zip_filter. Qed.

(* ------------------------------------------------------------------ *)
(** ** Evaluation bridges (pure)

    [digestE] reads a grinding-oracle answer as the scheme's
    [digest_of]; [wendsE] reads a length-chain_count walk's completed ends as
    the verifier's [complete_ends]. *)

Lemma digestE (pp : wcp_PP P) (m : wcp_M P) (c : nat) :
  rev (digits_w (wcp_w P) (wcp_chain_count P) (wcp_H_grind P pp (grind_adrs P) (m, c)))
  = digest_of P pp m c.
Proof. by []. Qed.

Lemma wendsE (pp : wcp_PP P) (ds : seq nat) (ys : seq (wcp_N P)) :
  size ds = wcp_chain_count P -> wends P pp 0 ds ys = complete_ends P pp ds ys.
Proof.
move=> h.
rewrite /wends.
by rewrite (ends_of_from_sig (wcp_PP P) (wcp_N P) (wcp_chain_count P) (wcp_w P) (Fw P) pp ds ys h)
   (wcendsE P pp ds ys).
Qed.

(* ------------------------------------------------------------------ *)
(** ** G_post_grind: G_forge_uniformchains-real with the GRIND case of KFORGE nulled *)

Definition G_post_grind : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap forge_pk_loc P ; forge_log_loc P ; forge_sig_loc P ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P)
                   ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get forge_pk_loc P ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put forge_pk_loc P := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc P := [:: m] ;;
      #put forge_sig_loc P := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome forge_pk_loc P ;;
      log ← get forge_log_loc P ;;
      sgo ← getSome forge_sig_loc P ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m sgo.2
            then ret false
            else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** G_post_compress: G_post_grind with ALSO the COMPRESS case nulled *)

Definition G_post_compress : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap forge_pk_loc P ; forge_log_loc P ; forge_sig_loc P ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P)
                   ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get forge_pk_loc P ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put forge_pk_loc P := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc P := [:: m] ;;
      #put forge_sig_loc P := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome forge_pk_loc P ;;
      log ← get forge_log_loc P ;;
      sgo ← getSome forge_sig_loc P ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m sgo.2
            then ret false
            else
              if complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                 != complete_ends P pk.1 (digest_of P pk.1 m sgo.2) sgo.1
              then ret false
              else ret true
          else ret false
      end
    }
  ].

(* ------------------------------------------------------------------ *)
(** ** G_post_chain: G_post_compress with ALSO the CHAIN-COLLISION case nulled *)

Definition G_post_chain : game (I_KOTS (shrincs_wots_scheme P)) :=
  [package [fmap forge_pk_loc P ; forge_log_loc P ; forge_sig_loc P ] ;
    [ COMMIT ] : { SParam (shrincs_wots_scheme P) × Msg (shrincs_wots_scheme P)
                   ~> Pk (shrincs_wots_scheme P) × 'option (Sig (shrincs_wots_scheme P)) } '(sp, m) {
      pko ← get forge_pk_loc P ;;
      #assert ~~ (isSome pko) ;;
      pp ← wcp_dPP P ;;
      #assert (isSome (find_counter P pp m)) ;;
      let c := odflt 0 (find_counter P pp m) in
      sg ← sample_sig_roots (wcp_PP P) (wcp_N P) (wcp_w P) (Fw P) (wcp_dN P) pp 0 (digest_of P pp m c) ;;
      #put forge_pk_loc P := Some (pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)) ;;
      #put forge_log_loc P := [:: m] ;;
      #put forge_sig_loc P := Some (sg, c) ;;
      ret ((pp, wcp_T_sf P pp (pk_adrs P) (complete_ends P pp (digest_of P pp m c) sg)), Some (sg, c))
    } ;
    [ KFORGE ] : { Msg (shrincs_wots_scheme P) × Sig (shrincs_wots_scheme P) ~> 'bool } '(mst, sgst) {
      pk ← getSome forge_pk_loc P ;;
      log ← get forge_log_loc P ;;
      sgo ← getSome forge_sig_loc P ;;
      match log with
      | [::] => ret false
      | m :: _ =>
          if shrincs_wots_verify P pk.1 pk.2 mst sgst && (mst \notin log)
          then
            if digest_of P pk.1 mst sgst.2 == digest_of P pk.1 m sgo.2
            then ret false
            else
              if complete_ends P pk.1 (digest_of P pk.1 mst sgst.2) sgst.1
                 != complete_ends P pk.1 (digest_of P pk.1 m sgo.2) sgo.1
              then ret false
              else
                match wtcr_dec P pk.1 (digest_of P pk.1 m sgo.2)
                        (digest_of P pk.1 mst sgst.2) sgo.1 sgst.1 with
                | Some _ => ret false
                | None => ret true
                end
          else ret false
      end
    }
  ].

End Intermediates.
