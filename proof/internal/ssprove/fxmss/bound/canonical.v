(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bound.canonical

    The terminal bit hop and canonical-forger semantics establish the zero-success
    endpoint. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.stateful_rom.
From Shrincs Require Import spec schemes games.
From Shrincs.internal.ssprove.fxmss Require Import
  params games digest.filtered instance bridge.adapter.
From mathcomp Require Import reals distr realsum.

(* ------------------------------------------------------------------ *)
(** ** Terminal bit hop *)

Import PackageNotation GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Section FinalHop.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Lemma forge_keep_none_const (preassigned b : bool) (cm : shrincs_fxmss_message)
    (sg : shrincs_fxmss_bytes) :
  ⊢ ⦃ λ '(h0, h1), h0 = h1 ⦄
    (v ← shrincs_fxmss_forge_body P preassigned keep_none cm sg ;; ret (b && v)) ≈
    (v ← shrincs_fxmss_forge_body P preassigned keep_none cm sg ;; ret false)
  ⦃ eq ⦄.

Proof.
rewrite /shrincs_fxmss_forge_body.
ssprove_code_simpl.
simpl.
eapply (rsame_head_cmd (cmd_get shrincs_fxmss_st_loc)) => sto.
ssprove_code_simpl.
simpl.
case: sto => [st|] /=.
2: {
  eapply r_transL; first exact: relational_rules.r_fail_bind_rhs.
  exact: relational_rules.r_fail_bind_rhs.
}
eapply (rsame_head_cmd (cmd_get shrincs_fxmss_done_loc)) => done.
case: done => /=.
- eapply r_transL; first exact: relational_rules.r_fail_bind_rhs.
  exact: relational_rules.r_fail_bind_rhs.
- ssprove_sync_eq.
  eapply (rsame_head_cmd (cmd_get shrincs_fxmss_log_loc)) => lg.
  eapply (rsame_head_cmd (cmd_get shrincs_fxmss_keys_loc)) => kt.
  eapply (rsame_head_cmd (cmd_get shrincs_fxmss_sd_loc)) => sd.
  eapply (rsame_head_cmd (cmd_get shrincs_fxmss_rt_loc)) => rt.
  case: (shrincs_fxmss_message_valid cm) => /=.
  2: by rewrite andbF; apply: rreflexivity_rule.
  case: (shrincs_sf_parse sg) => [[[[h r] i] fsig]|] /=.
  2: by rewrite andbF; apply: rreflexivity_rule.
  eapply (rsame_head_cmd (cmd_get shrincs_fxmss_rom_loc)) => mp.
  case: (getm mp _) => [md|] /=.
  + by rewrite /keep_none !andbF; apply: rreflexivity_rule.
  + rewrite !bind_assoc.
    eapply (rsame_head (shrincs_fxmss_digest_dist P)) => md.
    simpl.
    by rewrite /keep_none !andbF; apply: rreflexivity_rule.
Qed.

Lemma forge_reject_perfect : perfect I_forge (G_forge_reject P Q true) (G_forge_reject P
  Q false).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (fun '(h0, h1) => h0 = h1)).
{ ssprove_invariant. }
simplify_eq_rel arg.
- eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
- eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
- eapply rpost_weaken_rule; first exact: rreflexivity_rule.
  by move=> [x h0] [y h1] [= -> ->].
- case: arg => cm sg.
  eapply rpost_weaken_rule.
  + exact: (forge_keep_none_const true true cm sg).
  + by move=> [x h0] [y h1] [= -> ->].
Qed.

Lemma bind_true_zero (T : choice_type) (c : raw_code T)
    (k : T -> raw_code 'bool) (h : heap) :
  (forall x h', dfst (Pr_code (k x) h') true = 0) ->
  dfst (Pr_code (bind c k) h) true = 0.
Proof.
move=> hk.
rewrite Pr_code_bind dfst_dlet_commut dletE.
rewrite (eq_psum (F2 := fun _ => 0)) ?psum0 //.
by move=> [x h'] /=; rewrite hk mulr0.
Qed.

Lemma forge_keep_none_true_zero b cm sg h :
  dfst (Pr_code (resolve (G_forge_reject P Q b) shrincs_fxmss_forge_op (cm, sg)) h) true
    = 0.
Proof.
rewrite /G_forge_reject /G_forge_filtered resolve_forge.
case: b.
2: {
  apply: bind_true_zero => v h'.
  by rewrite Pr_code_ret (dmargin_dunit (false, _) fst) dunit1E.
}
change (dfst (Pr_code (bind (shrincs_fxmss_forge_body P true keep_none cm sg)
  (fun v => ret v)) h) true = 0).
rewrite bind_ret /shrincs_fxmss_forge_body Pr_code_get.
case: (get_heap h shrincs_fxmss_st_loc) => [st|] /=.
2: by rewrite Pr_code_fail /dmargin dlet_null_ext dnullE.
rewrite Pr_code_get.
case: (get_heap h shrincs_fxmss_done_loc) => /=.
1: by rewrite Pr_code_fail /dmargin dlet_null_ext dnullE.
rewrite Pr_code_put !Pr_code_get.
case: (shrincs_fxmss_message_valid cm) => /=.
2: by rewrite Pr_code_ret (dmargin_dunit (false, _) fst) dunit1E.
case: (shrincs_sf_parse sg) => [[[[ht r] i] fsig]|] /=.
2: by rewrite Pr_code_ret (dmargin_dunit (false, _) fst) dunit1E.
rewrite Pr_code_get.
case: (getm _ _) => [md|] /=.
- by rewrite /keep_none andbF Pr_code_ret
    (dmargin_dunit (false, _) fst) dunit1E.
- (* Uncached digest: sampling still returns false under keep_none. *)
  fold (@bind).
  rewrite bind_ret bind_assoc.
  apply: bind_true_zero => md h'.
  cbn [bind].
  by rewrite /keep_none andbF Pr_code_put Pr_code_ret
    (dmargin_dunit (false, _) fst) dunit1E.
Qed.

Definition terminal_forge (c : raw_code (shrincs_fxmss_message × shrincs_fxmss_bytes)) :
    raw_code 'bool :=
  ms ← c ;; opr shrincs_fxmss_forge_op ms (fun b => ret b).

Lemma keep_none_terminal_code_zero b c h :
  dfst (Pr_code (code_link (terminal_forge c) (G_forge_reject P Q b)) h) true = 0.
Proof.
rewrite /terminal_forge code_link_bind.
apply: bind_true_zero => -[cm sg] h'.
change (dfst (Pr_code
  (bind (resolve (G_forge_reject P Q b) shrincs_fxmss_forge_op (cm, sg))
    (fun v => ret v)) h') true = 0).
rewrite bind_ret.
exact: forge_keep_none_true_zero.
Qed.

Lemma keep_none_terminal_success (A : nom_package)
    (c : raw_code (shrincs_fxmss_message × shrincs_fxmss_bytes)) :
  resolve A RUN tt = terminal_forge c ->
  fseparate (loc A) (loc (G_forge_reject P Q true)) ->
  distr.mu (Pr' (A ∘ G_forge_reject P Q true)%sep) true = 0.
Proof.
move=> hrun hsep.
have hd : disj A (G_forge_reject P Q true : nom_package).
  move/fseparate_disj: hsep => hh.
  rewrite /disj.
  apply: (fdisjointSl
    (support_sub A _ (Share.nom_package_IsNominal_obligation_1 A))).
  apply: (fdisjointSr
    (support_sub (G_forge_reject P Q true : nom_package) _
      (Share.nom_package_IsNominal_obligation_1 (G_forge_reject P Q true :
        nom_package)))).
  exact: hh.
rewrite /Pr' -(link_sep_link hd) Pr_Pr_code resolve_link hrun.
exact: keep_none_terminal_code_zero.
Qed.

Lemma forge_reject_advantage (A : nom_package)
    (VA : ValidPackage (loc A) I_forge A_export A) :
  AdvOf (G_forge_reject P Q) A = 0.
Proof.
by rewrite (Adv_perfect_l forge_reject_perfect) Adv_same.
Qed.

End FinalHop.

(* ------------------------------------------------------------------ *)
(** ** Canonical forger *)

Import PackageNotation GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

Lemma shrincs_fxmss_canonical_zero (G : nom_package) LA c vc :
  (forall candidate h, dfst (Pr_code (resolve G
    (mkopsig stateful_rom.FORGE
      (stateful_rom.sf_Msg fxmss_sf_scheme × stateful_rom.sf_Sig fxmss_sf_scheme) 'bool)
    candidate) h) true = 0) ->
  Pr' (fxmss_forger LA c vc ∘ G)%sep true = 0.
Proof.
move=> hz.
pose A := (fxmss_forger LA c vc : nom_package).
pose pi := fresh G A.
have hd : disj (pi ∙ A) G by rewrite disjC; exact: fresh_disjoint.
change (Pr' (A ∘ G)%sep true = 0).
rewrite -{1}(@rename_alpha _ A pi).
rewrite /Pr' -(link_sep_link hd) Pr_Pr_code resolve_link.
rewrite -rename_resolve /A /fxmss_forger sf_forger_run sf_measure_rename.
rewrite /stateful_rom.measure code_link_bind.
apply: sf_bind_zero => candidate h'.
cbn [code_link].
rewrite bind_ret.
exact: hz.
Qed.

(* Keep the rejecting game folded while resolving the public adapter. *)
Local Opaque G_forge_reject.

Lemma shrincs_fxmss_canonical_reject_zero Q bit LA c vc :
  Pr' ((fxmss_forger LA c vc ∘ shrincs_fxmss_rom_adapter) ∘
    G_forge_reject shrincs_fxmss_sha256 Q bit)%sep true = 0.
Proof.
rewrite -sep_link_assoc.
have ha : disj (shrincs_fxmss_rom_adapter : nom_package)
    (G_forge_reject shrincs_fxmss_sha256 Q bit : nom_package) by ssprove_separate_solve.
rewrite -(share_link_sep_link ha).
apply: shrincs_fxmss_canonical_zero.
move=> [cm sg] h.
rewrite resolve_link.
rewrite /shrincs_fxmss_rom_adapter /resolve /= coerce_kleisliE.
cbn [code_link].
rewrite Pr_code_get.
rewrite bind_ret.
exact: forge_keep_none_true_zero.
Qed.
