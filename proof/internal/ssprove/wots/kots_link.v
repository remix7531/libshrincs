(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.kots_link

    The KOTS linking theorem: the two WOTS+C valid-commit known-message
    games are, PERFECTLY and unconditionally, the generic valid-commit
    KOTS game [KOTS_vc_game] (Sec.lib.sig.kots) instantiated at the two
    WOTS+C schemes.

      [G_forge_keyed_KOTS_vc      : G_forge_keyed      ~  KOTS_vc_game (shrincs_wots_keyed ...)]
      [G_forge_sampledkey_KOTS_vc : G_forge_sampledkey ~  KOTS_vc_game (shrincs_wots_scheme P)]

    Both are [perfect (I_KOTS (shrincs_wots_scheme P))] — no [Hrange] /
    grinding-range side condition: the flat games are byte-for-byte the
    KOTS experiment (same key generation, same one-time sign, same
    forge check), the only reshaping being that they inline the
    scheme's [keygen]/[sign] and carry an extra signature location
    ([forge_sig_loc], unread by KFORGE) that [KOTS_vc_game] omits.

    ** Proof shape (template: Sec.wots.hop.ud's endpoint hops)

    A cross-identifier [heap_ignore ⋊ couple_cross] invariant relates
    the game's [forge_*] locations (ids 300/301/302) to the KOTS
    locations (ids 115/116); [forge_sig_loc] is ignored (no KOTS
    counterpart).  COMMIT syncs the freshness gate and couples the
    PKseed sample, then CASE-SPLITS on [find_counter pp m] — the sign
    refusal pivot (Sec.wots.scheme): on [Some] both sides commit the
    same (pk, log) and return the same signature (the game's [#assert]
    is the scheme's non-refusal); on [None] the game aborts outright
    while the KOTS side samples its key/chain starts and then fails on
    the refused sign — related by [r_fail_scheme_rhs].  KFORGE reads
    the mirrored (pk, log) and both verify functions are the same
    [shrincs_wots_verify]. *)

From mathcomp.experimental_reals Require Import distr.
From Shrincs.internal.ssprove.lib Require Import prelude sig.scheme sig.kots
  toolkit.sample_seq toolkit.relational_rules.
From Shrincs.internal.common Require Import math.chain math.encoding.
From Shrincs.internal.ssprove Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import addressing.
From Shrincs.internal.ssprove.wots Require Import scheme games hop.prf.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section kots_link.

(** The WOTS+C parameter record [P] (Sec.wots.params), plus the keyed
    derivation data (the SKseed space [K], the derivation [PRF] and the
    SKseed sampler [dK]) that the keyed lemma additionally binds, as in
    Sec.wots.hop.prf. *)
Context (P : wc_params).
Context (K : choice_type).
Context (PRF : wcp_PP P -> wc_adrs P -> K -> wcp_N P).
Context (dK : dist K).

(* Keep the scheme functions folded under [simpl] (the known
   simpl-unrolling trap; the block mirrors Sec.wots.hop.prf). *)
#[local] Arguments find_counter : simpl never.
#[local] Arguments shrincs_wots_verify : simpl never.
#[local] Arguments sign_chains : simpl never.
#[local] Arguments shrincs_wots_pubkey : simpl never.
#[local] Arguments shrincs_wots_sign : simpl never.
#[local] Arguments digest_of : simpl never.
#[local] Arguments derive_sk : simpl never.
#[local] Arguments shrincs_wots_pubkey_gen : simpl never.

(** The cross-identifier invariant: heaps agree outside the five
    private locations; the game's pk/log locations mirror the KOTS
    pk/log locations.  [forge_sig_loc] has no KOTS counterpart, so it
    is only [heap_ignore]d. *)
Local Abbreviation kinv S := (
  heap_ignore [fmap (forge_pk_loc P) ; (forge_log_loc P) ; (forge_sig_loc P) ; kots_pk_loc S ; kots_log_loc S]
  ⋊ couple_cross (forge_pk_loc P) (kots_pk_loc S) eq
  ⋊ couple_cross (forge_log_loc P) (kots_log_loc S) eq
).

(* ------------------------------------------------------------------ *)
(** ** The keyed link *)

Lemma G_forge_keyed_KOTS_vc b :
  perfect (I_KOTS (shrincs_wots_scheme P))
    (G_forge_keyed P K PRF dK b)
    (KOTS_vc_game (shrincs_wots_keyed P K PRF dK) b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (kinv (shrincs_wots_keyed P K PRF dK))).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  (* sync the freshness gate (the pk-couple is invariant index 1) *)
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  (* couple the PKseed sample *)
  eapply r_scheme_bind; [exact _|].
  move=> pp.
  (* the sign-refusal pivot (Sec.wots.scheme.find_counter) *)
  case E: (find_counter P pp m) => [c|].
  + (* Some c: both sides commit the same (pk, log) and issue the same signature *)
    simpl.
    eapply r_scheme_bind; [exact _|].
    move=> k.
    rewrite (shrincs_wots_sign_Some P pp (derive_sk P K PRF pp k) m c E).
    rewrite /shrincs_wots_pubkey_gen.
    simpl.
    apply r_put_vs_put.
    apply r_put_vs_put.
    (* [forge_sig_loc] has no KOTS counterpart: an lhs-only write *)
    apply r_put_lhs.
    ssprove_restore_mem.
    { ssprove_invariant. }
    by apply r_ret.
  + (* None: the game aborts, while the keyed side samples its key and then
       fails on the refused sign (the swap-and-collapse [r_fail_scheme_rhs]) *)
    simpl.
    eapply r_transR.
    * eapply r_scheme_bind; [exact _|].
      move=> k.
      rewrite (shrincs_wots_sign_None P pp (derive_sk P K PRF pp k) m E).
      simpl.
      exact: (rreflexivity_rule fail).
    * apply: r_fail_scheme_rhs; exact _.
- (* KFORGE: read the mirrored (pk, log); both sides verify the same
     [shrincs_wots_verify] (the log-couple is invariant index 0) *)
  destruct arg as [mst sgst].
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  eapply r_get_remember_lhs => log.
  eapply r_get_remember_rhs => log'.
  ssprove_rem_rel 0%N => e'. subst log'.
  ssprove_forget_all.
  case: b => /=; by apply r_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The sampled-key link *)

Lemma G_forge_sampledkey_KOTS_vc b :
  perfect (I_KOTS (shrincs_wots_scheme P))
    (G_forge_sampledkey P b)
    (KOTS_vc_game (shrincs_wots_scheme P) b).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (kinv (shrincs_wots_scheme P))).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- (* COMMIT *)
  destruct arg as [sp m].
  ssprove_code_simpl. simpl.
  (* sync the freshness gate (the pk-couple is invariant index 1) *)
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  (* couple the PKseed sample *)
  eapply r_scheme_bind; [exact _|].
  move=> pp.
  (* the sign-refusal pivot (Sec.wots.scheme.find_counter) *)
  case E: (find_counter P pp m) => [c|].
  + (* Some c: both sides commit the same (pk, log) and issue the same signature *)
    simpl.
    eapply r_scheme_bind; [exact _|].
    move=> xs.
    rewrite (shrincs_wots_sign_Some P pp xs m c E).
    simpl.
    apply r_put_vs_put.
    apply r_put_vs_put.
    (* [forge_sig_loc] has no KOTS counterpart: an lhs-only write *)
    apply r_put_lhs.
    ssprove_restore_mem.
    { ssprove_invariant. }
    by apply r_ret.
  + (* None: the game aborts, while the KOTS side samples its chain starts
       and then fails on the refused sign (the swap-and-collapse
       [r_fail_scheme_rhs]) *)
    simpl.
    eapply r_transR.
    * eapply r_scheme_bind; [exact _|].
      move=> xs.
      rewrite (shrincs_wots_sign_None P pp xs m E).
      simpl.
      exact: (rreflexivity_rule fail).
    * apply: r_fail_scheme_rhs; exact _.
- (* KFORGE: read the mirrored (pk, log); both sides verify the same
     [shrincs_wots_verify] (the log-couple is invariant index 0) *)
  destruct arg as [mst sgst].
  eapply r_get_remember_lhs => pko.
  eapply r_get_remember_rhs => pko'.
  ssprove_rem_rel 1%N => e. subst pko'.
  ssprove_sync => hpko.
  eapply r_get_remember_lhs => log.
  eapply r_get_remember_rhs => log'.
  ssprove_rem_rel 0%N => e'. subst log'.
  ssprove_forget_all.
  case: b => /=; by apply r_ret.
Qed.

End kots_link.
