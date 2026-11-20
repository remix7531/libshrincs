(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.guard.prepared

    Leaf protocol aborts are independent of the forgery hybrid. Every
    setup, schedule and consumed-slot check precedes the pure verdict. *)

From Shrincs.internal.ssprove.lib Require Import prelude guard.common.
From Shrincs Require Import games schemes spec.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games leaf.opening leaf.commitments leaf.known_message_game
    leaf.prepared.

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma prepared_leaf_gen_phase_abort r sp sd h :
  isSome (get_heap h prepared_leaf_st_loc) ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      leaf_opening_public)) (sp,
      sd)) h =
    Pr_code fail h.
Proof.
move=> hs.
rewrite resolve_prepared_leaf_gen /prepared_leaf_gen Pr_code_get.
by case he: (get_heap h prepared_leaf_st_loc) hs.
Qed.

Lemma prepared_leaf_gen_illegal r sp sd h :
  ~~ shrincs_fxmss_structure_legal sp.1 sp.2 ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      leaf_opening_public)) (sp,
      sd)) h =
    Pr_code fail h.
Proof.
move=> /negbTE hsp.
rewrite resolve_prepared_leaf_gen /prepared_leaf_gen Pr_code_get.
by case: (get_heap h prepared_leaf_st_loc) => /=; rewrite ?hsp.
Qed.

Lemma prepared_leaf_gen_missing_digest r sp sd h :
  ~~ leaf_digest_total (shrincs_fxmss_schedule sp) sd ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      leaf_opening_public)) (sp,
      sd)) h =
    Pr_code fail h.
Proof.
move=> /negbTE hsd.
rewrite resolve_prepared_leaf_gen /prepared_leaf_gen Pr_code_get.
case: (get_heap h prepared_leaf_st_loc) => [st|] //=.
by case: (shrincs_fxmss_structure_legal sp.1 sp.2) => /=; rewrite ?hsd.
Qed.

Lemma prepared_leaf_sign_no_setup r j h :
  get_heap h prepared_leaf_st_loc = None ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j) h = Pr_code fail h.
Proof.
move=> hs.
by rewrite resolve_prepared_leaf_sign /prepared_leaf_sign Pr_code_get hs /=.
Qed.

Lemma prepared_leaf_check_no_setup r q h :
  get_heap h prepared_leaf_st_loc = None ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h.
Proof.
move=> hs.
by rewrite resolve_prepared_leaf_check /prepared_leaf_check Pr_code_get hs /=.
Qed.

Lemma prepared_leaf_sign_consumed r j h :
  j \in get_heap h prepared_leaf_slog_loc ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j) h = Pr_code fail h.
Proof.
move=> hj.
rewrite resolve_prepared_leaf_sign /prepared_leaf_sign Pr_code_get.
case: (get_heap h prepared_leaf_st_loc) => [st|] //=.
case: (j < size (shrincs_fxmss_schedule st.2)) => //=.
by rewrite Pr_code_get hj /=.
Qed.

Lemma prepared_leaf_sign_outside_schedule r j h st :
  get_heap h prepared_leaf_st_loc = Some st ->
  ~~ (j < size (shrincs_fxmss_schedule st.2)) ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j) h = Pr_code fail h.
Proof.
move=> hs /negbTE hj.
by rewrite resolve_prepared_leaf_sign /prepared_leaf_sign Pr_code_get hs /= hj.
Qed.

Lemma prepared_leaf_check_outside_schedule r q h st :
  get_heap h prepared_leaf_st_loc = Some st ->
  ~~ (q.1 < size (shrincs_fxmss_schedule st.2)) ->
  Pr_code (resolve (G_prepared_leaf r)
    (known_message_check, (leaf_opening_opening, 'bool)) q) h = Pr_code fail h.
Proof.
move=> hs /negbTE hq.
by rewrite resolve_prepared_leaf_check /prepared_leaf_check Pr_code_get hs /= hq.
Qed.

Lemma prepared_leaf_sign_no_setup_adv r0 r1 answer :
  AdvOf (fun b => G_prepared_leaf (if b then r0 else r1))
    (guard_calls (known_message_sign, ('nat, 'option leaf_opening_signature)) 0 1
      answer) = 0%R.
Proof.
apply: guard_adv_eq.
cbn [guard_repeat code_link].
by rewrite !resolve_prepared_leaf_sign.
Qed.
