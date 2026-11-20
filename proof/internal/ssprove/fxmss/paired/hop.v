(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.paired.hop

    SIGN and HASH preserve the committed tree state: they read the key and tree
    but write only counters, logs and random-oracle tables. Perfect simulations of
    the static paired-class reduction, followed by the exact single-leg advantage
    equality with 2L-1 committed targets. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.denotational_rules toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape scheme games tree.forgery paired.reduction tree.classify
  paired.generation model.nodes paired.routing tree.encoding tree.model paired.targets
  digest.filtered instance.
From Stdlib Require Import BinInt.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree merkle.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Paired preservation *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_paired_inv shrincs_fxmss_paired_rel.

Lemma shrincs_fxmss_paired_lookup_stable P x :
  code_stable (shrincs_fxmss_paired_inv P) (shrincs_fxmss_lookup P x).
Proof.
rewrite /shrincs_fxmss_lookup.
split.
- apply: shrincs_fxmss_paired_inv_get.
  by rewrite /shrincs_fxmss_paired_service_locs; fmap_solve.
- move=> mp.
  case: (getm mp x) => [md|]; first by [].
  apply: code_stable_bind.
  + apply: (code_stable_valid emptym).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + move=> md.
    split; last by [].
    apply: shrincs_fxmss_paired_inv_put.
    by [].
Qed.

Lemma shrincs_fxmss_paired_hash_stable P Q keep bit x :
  code_stable (shrincs_fxmss_paired_inv P) (resolve (G_forge_full_signature P Q keep
    bit)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x).
Proof.
rewrite /G_forge_full_signature /resolve /= coerce_kleisliE.
cbn [code_stable].
split.
- apply: shrincs_fxmss_paired_inv_get.
  by rewrite /shrincs_fxmss_paired_service_locs; fmap_solve.
- move=> done.
  case: done.
  + by [].
  + cbn [negb assert code_stable].
    split.
    * apply: shrincs_fxmss_paired_inv_get.
      by rewrite /shrincs_fxmss_paired_service_locs; fmap_solve.
    * move=> hc.
      case: (hc < shrincs_fxmss_hash_budget Q).
      -- cbn [assert code_stable].
         split.
         ++ apply: shrincs_fxmss_paired_inv_put.
            by [].
         ++ (* A valid hash input preserves the committed tree state. *)
            case: (Z.leb _ _) => //.
            change (code_stable (shrincs_fxmss_paired_inv P)
              (bind (shrincs_fxmss_lookup P x) (fun md => ret (Some md)))).
            apply: code_stable_bind; first exact: shrincs_fxmss_paired_lookup_stable.
            by move=> md.
      -- by [].
Qed.

Local Opaque shrincs_fxmss_sign shrincs_fxmss_select_leaf shrincs_fxmss_lookup_keys.

Local Ltac tree_access := first
  [ apply: shrincs_fxmss_paired_inv_get; rewrite /shrincs_fxmss_paired_service_locs;
    fmap_solve
  | apply: shrincs_fxmss_paired_inv_put; done ].

Lemma shrincs_fxmss_paired_sign_stable P Q keep bit cm :
  code_stable (shrincs_fxmss_paired_inv P) (resolve (G_forge_full_signature P Q keep
    bit)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm).
Proof.
rewrite /G_forge_full_signature /resolve /= coerce_kleisliE.
cbn [code_stable].
split; first tree_access.
move=> sto.
case: sto => [st|]; last by [].
simpl.
split; first tree_access.
move=> done.
case: done; first by [].
simpl.
split; first tree_access.
move=> sc.
case: (sc < shrincs_fxmss_sign_budget Q); last by [].
simpl.
split; first tree_access.
move=> lg.
split; first tree_access.
split; first tree_access.
case: (shrincs_fxmss_message_valid cm); last by [].
simpl.
split; first tree_access.
move=> q.
case: (shrincs_fxmss_select_leaf _ _ _) => [a|]; last by [].
simpl.
split; first tree_access.
split; first tree_access.
move=> kso.
case: kso => [ks|]; last by [].
simpl.
split; first tree_access.
move=> kpo.
case: kpo => [kp|]; last by [].
simpl.
split; first tree_access.
move=> kt.
split; first tree_access.
move=> rt.
apply: code_stable_bind.
- case: (rt _) => [r|]; first by [].
  apply: code_stable_bind.
  + apply: (code_stable_valid emptym).
    * by move=> l /fhas_empty.
    * by move=> l v /fhas_empty.
  + by move=> r.
- move=> ro.
  case: ro => [r|]; last by [].
  simpl.
  split; first tree_access.
  split; first tree_access.
  move=> sd.
  apply: code_stable_bind.
  + apply: code_stable_bind.
    * case: (sd a) => [md|]; first by [].
      apply: code_stable_bind.
      -- apply: (code_stable_valid emptym).
         ++ by move=> l /fhas_empty.
         ++ by move=> l v /fhas_empty.
      -- by move=> md.
    * (* The sampled digest is recorded outside the service locations. *)
      move=> md.
      simpl.
      split; first tree_access.
      move=> mp.
      split; first tree_access.
      by [].
  + move=> md.
    case: (shrincs_fxmss_sign _ _ _ _ _ _ _ _) => [sg|]; by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired simulation *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_paired_inv shrincs_fxmss_paired_rel tcrx.TCRX_game.

Lemma shrincs_fxmss_paired_sign_resolve P Q keep bit cm :
  resolve (R_paired P Q) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
    shrincs_fxmss_bytes)) cm =
  resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
    (shrincs_fxmss_message, 'option
    shrincs_fxmss_bytes)) cm.
Proof. reflexivity. Qed.

Lemma shrincs_fxmss_paired_hash_resolve P Q keep bit x :
  resolve (R_paired P Q) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option
    (bytes 32))) x =
  resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_hash,
    (shrincs_fxmss_hmsg_input,
    'option (bytes 32))) x.
Proof. reflexivity. Qed.

Lemma shrincs_fxmss_paired_sign_sim P Q keep bit (G : raw_package) cm :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_paired_inv P (s0,s1) ⦄
    resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message, 'option
      shrincs_fxmss_bytes)) cm
    ≈ code_link (resolve (R_paired P Q)
        (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes))
          cm) G
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_paired_inv P (s0,s1) ⦄.
Proof.
rewrite (shrincs_fxmss_paired_sign_resolve P Q keep bit).
have hv : ValidCode shrincs_fxmss_locs [interface]
    (resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message,
      'option shrincs_fxmss_bytes)) cm).
  eapply valid_resolve.
  exact (pack_valid (G_forge_full_signature P Q keep bit)).
  by rewrite /I_forge; fmap_solve.
rewrite (code_link_scheme _ _ _ _ hv).
apply: r_code_stable.
exact: shrincs_fxmss_paired_sign_stable.
Qed.

Lemma shrincs_fxmss_paired_hash_sim P Q keep bit (G : raw_package) x :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_paired_inv P (s0,s1) ⦄
    resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_hash,
      (shrincs_fxmss_hmsg_input,
      'option (bytes 32))) x
    ≈ code_link (resolve (R_paired P Q)
        (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x) G
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_paired_inv P (s0,s1) ⦄.
Proof.
rewrite (shrincs_fxmss_paired_hash_resolve P Q keep bit).
have hv : ValidCode shrincs_fxmss_locs [interface]
    (resolve (G_forge_full_signature P Q keep bit) (shrincs_fxmss_op_hash,
      (shrincs_fxmss_hmsg_input,
      'option (bytes 32))) x).
  eapply valid_resolve.
  exact (pack_valid (G_forge_full_signature P Q keep bit)).
  by rewrite /I_forge; fmap_solve.
rewrite (code_link_scheme _ _ _ _ hv).
apply: r_code_stable.
exact: shrincs_fxmss_paired_hash_stable.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired forge simulation *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_paired_inv shrincs_fxmss_paired_rel tcrx.TCRX_game.

Lemma shrincs_fxmss_paired_ready_put P st kt h (l : Location) (v : l) :
  l.1 \notin [:: 1010; 1011; 1012; 1013] ->
  shrincs_fxmss_paired_ready P st kt h -> shrincs_fxmss_paired_ready P st kt (set_heap h
    l v).
Proof.
rewrite !inE !negb_or.
move=> /andP[h1010 /andP[h1011 /andP[h1012 h1013]]].
rewrite /shrincs_fxmss_paired_ready.
rewrite get_set_heap_neq; first by change (1010 != l.1); rewrite eq_sym.
rewrite get_set_heap_neq; first by change (1011 != l.1); rewrite eq_sym.
rewrite get_set_heap_neq; first by change (1012 != l.1); rewrite eq_sym.
rewrite get_set_heap_neq; first by change (1013 != l.1); rewrite eq_sym.
by [].
Qed.

(* Keep the route and lookup bodies folded while simplifying the forge protocol. *)
Local Opaque shrincs_fxmss_paired_route shrincs_fxmss_lookup.

Lemma shrincs_fxmss_paired_forge_known P Q bit cm sg h :
  shrincs_fxmss_paired_inv P (h,h) ->
  Pr_code (code_link (shrincs_fxmss_paired_forge_body P cm sg)
    (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner (2
      * shrincs_fxmss_leaf_capacity Q - 1) bit)) h =
  Pr_code (shrincs_fxmss_full_forge_body P
    (fun st kt a md fsig => (keep_no_tree_collision P st kt a md fsig &&
      (bit || keep_no_paired_collision P st kt a md fsig))%bool)
    cm sg) h.
Proof.
move=> hi.
rewrite /shrincs_fxmss_paired_forge_body /shrincs_fxmss_full_forge_body.
cbn [code_link bind].
rewrite !Pr_code_get.
case hs: (get_heap h shrincs_fxmss_st_loc) => [st|]; last by [].
cbn [code_link bind].
rewrite !Pr_code_get.
case hd: (get_heap h shrincs_fxmss_done_loc); first by [].
cbn [negb assert bind code_link].
rewrite !Pr_code_put.
set h1 := set_heap h shrincs_fxmss_done_loc true.
have hr : shrincs_fxmss_paired_ready P st (get_heap h shrincs_fxmss_keys_loc) h1.
  apply: shrincs_fxmss_paired_ready_put; first by [].
  exact: shrincs_fxmss_paired_inv_ready hi hs.
rewrite !Pr_code_get.
rewrite get_set_heap_neq; first by [].
case hm: (shrincs_fxmss_message_valid cm); last by [].
case hp: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|]; last by [].
fold (@code_link 'bool).
rewrite code_link_bind.
rewrite (code_link_scheme _ _ _ _ (shrincs_fxmss_lookup_valid P [interface] _)).
rewrite bind_ret.
have hk : get_heap h1 shrincs_fxmss_keys_loc = get_heap h shrincs_fxmss_keys_loc.
  by rewrite /h1 get_set_heap_neq.
rewrite hk.
cbn [getSome].
match goal with
| |- Pr_code (bind _ ?kl) _ = Pr_code (bind _ ?kr) _ =>
  set leftk := kl; set rightk := kr
end.
have hend : forall md h2,
    shrincs_fxmss_paired_ready P st (get_heap h shrincs_fxmss_keys_loc) h2 ->
    Pr_code (leftk md) h2 = Pr_code (rightk md) h2.
  move=> md h2 hr2.
  rewrite /leftk /rightk andbA.
  case hc: (_ && _ && _ && _)%bool; last by [].
  have hv : shrincs_fxmss_verify P st.1.1.1 st.1.2 (a,i) fsig md.
    by move: hc => /andP[/andP[/andP[hv _] _] _].
  have he := shrincs_fxmss_paired_route_known P Q bit st (get_heap h
    shrincs_fxmss_keys_loc)
    (a,i) md fsig h2 'bool (fun b => ret b) hr2 hv.
  by rewrite bind_ret in he.
cbv delta [shrincs_fxmss_lookup].
cbn [bind].
rewrite !Pr_code_get.
case: (getm _ _) => [md|].
- exact: hend md h1 hr.
- (* A fresh digest preserves the revealed challenge state. *)
  rewrite !bind_assoc.
  apply: Pr_code_bind_stateless.
  move=> md.
  cbn [bind].
  rewrite !Pr_code_put.
  apply: hend.
  apply: shrincs_fxmss_paired_ready_put; first by [].
  exact hr.
Qed.

Local Ltac paired_access := first
  [ apply: shrincs_fxmss_paired_inv_get; rewrite /shrincs_fxmss_paired_service_locs;
    fmap_solve
  | apply: shrincs_fxmss_paired_inv_put; done ].

(* Keep lookup folded for the separate stability lemma. *)
Local Opaque shrincs_fxmss_lookup.

Lemma shrincs_fxmss_paired_full_forge_stable P keep cm sg :
  code_stable (shrincs_fxmss_paired_inv P) (shrincs_fxmss_full_forge_body P keep cm sg).
Proof.
rewrite /shrincs_fxmss_full_forge_body.
simpl.
split; first paired_access.
move=> sto.
case: sto => [st|]; last by [].
simpl.
split; first paired_access.
move=> done.
case: done; first by [].
simpl.
split; first paired_access.
split; first paired_access.
move=> lg.
split; first paired_access.
move=> kt.
split; first paired_access.
move=> sd.
split; first paired_access.
move=> rt.
case: (shrincs_fxmss_message_valid cm); last by [].
case: (shrincs_sf_parse sg) => [[[[a r] i] fsig]|]; last by [].
rewrite bind_ret.
apply: code_stable_bind; first exact: shrincs_fxmss_paired_lookup_stable.
by move=> md.
Qed.

Lemma shrincs_fxmss_paired_forge_body_sim P Q bit cm sg :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_paired_inv P (s0,s1) ⦄
    shrincs_fxmss_full_forge_body P
      (fun st kt a md fsig => (keep_no_tree_collision P st kt a md fsig &&
      (bit || keep_no_paired_collision P st kt a md fsig))%bool)
      cm sg
    ≈ code_link (shrincs_fxmss_paired_forge_body P cm sg)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        (2 * shrincs_fxmss_leaf_capacity Q - 1) bit)
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_paired_inv P (s0,s1) ⦄.
Proof.
eapply r_pr_code_rhs.
- (* The right-hand heap satisfies the revealed-state invariant. *)
  move=> h0 h1 hi.
  apply: shrincs_fxmss_paired_forge_known.
  have [_ hr] := shrincs_fxmss_paired_invE P h0 h1 hi.
  split; last exact hr.
  by move=> l hl.
- apply: r_code_stable.
  exact: shrincs_fxmss_paired_full_forge_stable.
Qed.

(* Keep the forge bodies folded while exposing the package operations. *)
Local Opaque shrincs_fxmss_full_forge_body shrincs_fxmss_paired_forge_body.

Lemma shrincs_fxmss_paired_forge_sim P Q bit cm sg :
  ⊢ ⦃ λ '(s0,s1), shrincs_fxmss_paired_inv P (s0,s1) ⦄
    resolve (G_forge_full_signature P Q
      (fun st kt a md fsig => (keep_no_tree_collision P st kt a md fsig &&
      (bit || keep_no_paired_collision P st kt a md fsig))%bool)
      true) shrincs_fxmss_forge_op (cm, sg)
    ≈ code_link (resolve (R_paired P Q) shrincs_fxmss_forge_op (cm, sg))
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        (2 * shrincs_fxmss_leaf_capacity Q - 1) bit)
  ⦃ λ '(x,s0) '(y,s1), x = y /\ shrincs_fxmss_paired_inv P (s0,s1) ⦄.
Proof.
rewrite /resolve /G_forge_full_signature /R_paired /= coerce_kleisliE !bind_ret.
rewrite coerce_kleisliE bind_ret.
exact: shrincs_fxmss_paired_forge_body_sim.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired init invariant *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_paired_rel shrincs_fxmss_paired_inv.

Lemma shrincs_fxmss_paired_commit_ignore P h0 h1 targets :
  heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1) ->
  heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,shrincs_fxmss_paired_heap P h1
    targets).
Proof.
elim: targets h1 => [|t ts ih] h1 hi; first exact hi.
change (heap_ignore (shrincs_fxmss_paired_service_locs P)
  (h0,shrincs_fxmss_paired_heap P (shrincs_fxmss_paired_step P h1 t) ts)).
apply: ih.
rewrite /shrincs_fxmss_paired_step.
apply: relational_rules.heap_ignore_set_r;
  first by rewrite /shrincs_fxmss_paired_service_locs mem_domm.
apply: relational_rules.heap_ignore_set_r;
  first by rewrite /shrincs_fxmss_paired_service_locs mem_domm.
exact hi.
Qed.

Definition shrincs_fxmss_paired_store (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) (h : heap) : heap
      :=
  set_heap (set_heap (set_heap (set_heap (set_heap h
    shrincs_fxmss_st_loc (Some st)) shrincs_fxmss_ks_loc (Some ks)) shrincs_fxmss_kp_loc
      (Some kp))
    shrincs_fxmss_keys_loc kt) shrincs_fxmss_sd_loc sd.

Lemma shrincs_fxmss_paired_store_ignore P st ks kp kt sd h0 h1 :
  heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1) ->
  heap_ignore (shrincs_fxmss_paired_service_locs P)
    (shrincs_fxmss_paired_store st ks kp kt sd h0, shrincs_fxmss_paired_store st ks kp
      kt sd h1).
Proof.
move=> hi.
rewrite /shrincs_fxmss_paired_store.
do 5 apply: put_pre_cond_heap_ignore.
exact hi.
Qed.

Lemma shrincs_fxmss_paired_store_ready P st ks kp kt sd h :
  shrincs_fxmss_paired_ready P st kt h ->
  shrincs_fxmss_paired_ready P st kt (shrincs_fxmss_paired_store st ks kp kt sd h).
Proof.
move=> hr.
rewrite /shrincs_fxmss_paired_store.
do 5 (apply: shrincs_fxmss_paired_ready_put; first by []).
exact hr.
Qed.

Lemma shrincs_fxmss_paired_store_state st ks kp kt sd h :
  get_heap (shrincs_fxmss_paired_store st ks kp kt sd h) shrincs_fxmss_st_loc = Some st.
Proof.
rewrite /shrincs_fxmss_paired_store.
do 4 (rewrite get_set_heap_neq; first by []).
exact: get_set_heap_eq.
Qed.

Lemma shrincs_fxmss_paired_store_keys st ks kp kt sd h :
  get_heap (shrincs_fxmss_paired_store st ks kp kt sd h) shrincs_fxmss_keys_loc = kt.
Proof.
rewrite /shrincs_fxmss_paired_store.
rewrite get_set_heap_neq; first by [].
exact: get_set_heap_eq.
Qed.

Lemma shrincs_fxmss_paired_store_inv P st ks kp kt sd h0 h1 :
  heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1) ->
  shrincs_fxmss_paired_ready P st kt h1 ->
  shrincs_fxmss_paired_inv P
    (shrincs_fxmss_paired_store st ks kp kt sd h0, shrincs_fxmss_paired_store st ks kp
      kt sd h1).
Proof.
move=> hi hr.
split; first exact: shrincs_fxmss_paired_store_ignore.
change (shrincs_fxmss_paired_rel P
  (get_heap (shrincs_fxmss_paired_store st ks kp kt sd h1) shrincs_fxmss_st_loc)
  (get_heap (shrincs_fxmss_paired_store st ks kp kt sd h1) shrincs_fxmss_keys_loc)
  (get_heap (shrincs_fxmss_paired_store st ks kp kt sd h1) (tcrx.tcrx_pp_loc
    (shrincs_fxmss_hash_function P)))
  (get_heap (shrincs_fxmss_paired_store st ks kp kt sd h1) (tcrx.tcrx_tgts_loc
    (shrincs_fxmss_hash_function P)))
  (get_heap (shrincs_fxmss_paired_store st ks kp kt sd h1) (tcrx.tcrx_tws_loc
    (shrincs_fxmss_hash_function P)))
  (get_heap (shrincs_fxmss_paired_store st ks kp kt sd h1) tcrx.tcrx_rev_loc)).
rewrite shrincs_fxmss_paired_store_state shrincs_fxmss_paired_store_keys.
change (shrincs_fxmss_paired_ready P st kt (shrincs_fxmss_paired_store st ks kp kt sd
  h1)).
exact: shrincs_fxmss_paired_store_ready.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired gen simulation *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_paired_gen_pre P (po : option (bytes 16)) : precond :=
  fun '(h0,h1) =>
    [/\ heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1),
        get_heap h1 (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) = po,
        get_heap h1 (tcrx.tcrx_tgts_loc (shrincs_fxmss_hash_function P)) = emptym,
        get_heap h1 (tcrx.tcrx_tws_loc (shrincs_fxmss_hash_function P)) = [::] &
        get_heap h1 tcrx.tcrx_rev_loc = false].

Arguments shrincs_fxmss_paired_gen_pre : simpl never.
Local Opaque shrincs_fxmss_paired_inv shrincs_fxmss_paired_rel tcrx.TCRX_game.

Lemma shrincs_fxmss_paired_gen_pre_seed P pp h0 h1 :
  shrincs_fxmss_paired_gen_pre P None (h0,h1) ->
  shrincs_fxmss_paired_gen_pre P (Some pp)
    (h0, set_heap h1 (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) (Some pp)).
Proof.
move=> [hi hp ht hw hr].
split.
- apply: heap_ignore_set_r hi.
  by rewrite /shrincs_fxmss_paired_service_locs mem_domm.
- exact: get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

Definition shrincs_fxmss_paired_finish (st : shrincs_fxmss_state) (ks kp : bytes 16)
    (kt : shrincs_fxmss_key_table) (sd : shrincs_fxmss_digest_table) : raw_code (bytes
      48) :=
  #put shrincs_fxmss_st_loc := Some st ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_keys_loc := kt ;;
  #put shrincs_fxmss_sd_loc := sd ;;
  ret [tuple of st.1.1.1 ++ st.1.1.2 ++ st.1.2].

Lemma shrincs_fxmss_paired_finish_sim P st ks kp kt sd :
  ⊢ ⦃ λ '(h0,h1),
      heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1) /\
      shrincs_fxmss_paired_ready P st kt h1 ⦄
    shrincs_fxmss_paired_finish st ks kp kt sd ≈ shrincs_fxmss_paired_finish st ks kp kt
      sd
  ⦃ λ '(x,h0) '(y,h1), x = y /\ shrincs_fxmss_paired_inv P (h0,h1) ⦄.
Proof.
rewrite /shrincs_fxmss_paired_finish.
eapply r_put_lhs with (pre := fun '(h0,h1) =>
  heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1) /\
    shrincs_fxmss_paired_ready P st kt h1).
do 4 eapply r_put_lhs.
do 5 eapply r_put_rhs.
apply: r_ret => h0 h1 hh.
split; first by [].
case: hh => h1e [hh ->].
case: hh => h1d [hh ->].
case: hh => h1c [hh ->].
case: hh => h1b [hh ->].
case: hh => h1a [hh ->].
case: hh => h0e [hh ->].
case: hh => h0d [hh ->].
case: hh => h0c [hh ->].
case: hh => h0b [hh ->].
case: hh => h0a [[hi hr] ->].
exact: shrincs_fxmss_paired_store_inv hi hr.
Qed.

Lemma shrincs_fxmss_paired_generate_sim P Q bit pp partner ks kp kt sd b d :
  shrincs_fxmss_spec_legal_shape b d ->
  shrincs_fxmss_keys_sized (shrincs_fxmss_schedule (b,d)) kt ->
  let keys := fun c => odflt [::] (getm kt c) in
  let root := val_bt (shrincs_fxmss_tree_node_hash P pp) [::]
    (shrincs_fxmss_value_tree P pp keys b d) in
  ⊢ ⦃ λ '(h0,h1), shrincs_fxmss_paired_gen_pre P (Some pp) (h0,h1) ⦄
    shrincs_fxmss_paired_finish ((pp,partner,root),(b,d)) ks kp kt sd
    ≈ (root ← code_link (shrincs_fxmss_paired_generate P keys b d)
          (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
            fxmss_partner (2 * shrincs_fxmss_leaf_capacity Q - 1) bit) ;;
        pp ← resolve
          (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
            fxmss_partner (2 * shrincs_fxmss_leaf_capacity Q - 1) bit)
          (shrincs_fxmss_paired_reveal_op P) tt ;;
        shrincs_fxmss_paired_finish ((pp,partner,root),(b,d)) ks kp kt sd)
  ⦃ λ '(x,h0) '(y,h1), x = y /\ shrincs_fxmss_paired_inv P (h0,h1) ⦄.
Proof.
move=> hd hk keys root.
eapply r_pr_code_rhs_state with
  (f := fun h => set_heap (shrincs_fxmss_paired_heap P h
    (shrincs_fxmss_paired_targets P pp keys b d)) tcrx.tcrx_rev_loc true)
  (pre' := fun '(h0,h1) => heap_ignore (shrincs_fxmss_paired_service_locs P) (h0,h1) /\
    shrincs_fxmss_paired_ready P ((pp,partner,root),(b,d)) kt h1).
- move=> h0 h1 [hi hp ht hw hr].
  rewrite (shrincs_fxmss_paired_generate_known P Q bit pp keys b d h1 _ _ hd hp hr hw).
  rewrite (shrincs_fxmss_paired_reveal_known P (2 * shrincs_fxmss_leaf_capacity Q - 1)
    bit _ pp).
  + by rewrite shrincs_fxmss_paired_heap_seed.
  + reflexivity.
- move=> h0 h1 [hi hp ht hw hr].
  split.
  + apply: heap_ignore_set_r;
      first by rewrite /shrincs_fxmss_paired_service_locs mem_domm.
    exact: shrincs_fxmss_paired_commit_ignore.
  + exact: shrincs_fxmss_paired_ready_generated hd hk hp ht hw.
- exact: shrincs_fxmss_paired_finish_sim.
Qed.

Local Opaque shrincs_fxmss_node shrincs_fxmss_sample_keys shrincs_fxmss_sample_digests
  shrincs_fxmss_paired_generate shrincs_fxmss_paired_finish shrincs_fxmss_lookup_keys.

Lemma shrincs_fxmss_paired_gen_sim P Q keep b0 bit setup :
  ⊢ ⦃ λ '(h0,h1), shrincs_fxmss_paired_inv P (h0,h1) ⦄
    resolve (G_forge_full_signature P Q keep b0) (shrincs_fxmss_op_gen,
      (shrincs_fxmss_setup, bytes 48))
      setup
    ≈ code_link (resolve (R_paired P Q) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup,
      bytes 48)) setup)
      (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        (2 * shrincs_fxmss_leaf_capacity Q - 1) bit)
  ⦃ λ '(x,h0) '(y,h1), x = y /\ shrincs_fxmss_paired_inv P (h0,h1) ⦄.
Proof.
have hsync : ProvenBy (syncs shrincs_fxmss_st_loc) (shrincs_fxmss_paired_inv P).
  move=> [h0 h1] hi.
  apply: (shrincs_fxmss_paired_inv_get P shrincs_fxmss_st_loc _ h0 h1 hi).
  by rewrite /shrincs_fxmss_paired_service_locs; fmap_solve.
rewrite /resolve /G_forge_full_signature /R_paired /= !coerce_kleisliE.
cbn [code_link].
eapply (@r_get_vs_get_remember_rhs _ _ _ _ _ _ _ hsync).
move=> sto.
case: sto => [st|].
- simpl.
  apply: r_fail.
- cbn [isSome negb assert bind code_link].
  have hd_sync : ProvenBy (syncs shrincs_fxmss_done_loc)
      (shrincs_fxmss_paired_inv P ⋊ rem_rhs shrincs_fxmss_st_loc None).
    move=> [h0 h1] [hi _].
    apply: (shrincs_fxmss_paired_inv_get P shrincs_fxmss_done_loc _ h0 h1 hi).
    by rewrite /shrincs_fxmss_paired_service_locs; fmap_solve.
  eapply (@r_get_vs_get_remember_rhs _ _ _ _ _ _ _ hd_sync).
  move=> done.
  case: done.
  + simpl.
    apply: r_fail.
  + cbn [negb assert bind code_link].
    case hlegal: (shrincs_fxmss_structure_legal setup.1.1 setup.1.2).
    * (* A legal setup initializes the committed targets. *)
      cbn [assert bind code_link].
      have hd : shrincs_fxmss_spec_legal_shape setup.1.1 setup.1.2.
        by apply/shrincs_fxmss_legal_shapeP; rewrite hlegal.
      eapply rpre_weaken_rule with
        (pre := fun '(h0,h1) => shrincs_fxmss_paired_gen_pre P None (h0,h1)); last
          first.
      -- (* Unused setup leaves the challenge seed and target table empty. *)
         move=> h0 h1 [[hi hs] _].
         have [he hr] := shrincs_fxmss_paired_invE P h0 h1 hi.
         change (get_heap h1 shrincs_fxmss_st_loc = None) in hs.
         rewrite hs in hr.
         cbv delta [shrincs_fxmss_paired_rel] in hr.
         case: hr => hp ht hw hv.
         by split.
      -- (* Generate keys and commit the paired targets under a shared seed. *)
         simpl.
         fold (@code_link (bytes 48)).
         have heval : resolve
             (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class
               fxmss_partner (2 * shrincs_fxmss_leaf_capacity Q - 1) bit)
             (shrincs_fxmss_paired_eval_op P) (shrincs_fxmss_grind_tweak (uint U8 0,
               uint U64 0), [::]) =
             (po ← get (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) ;;
              pp ← (match po with
                | Some pp => ret pp
                | None => pp ← shrincs_fxmss_public_seed_dist P ;;
                    #put (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P)) := Some pp
                      ;; ret pp
                end) ;;
              ret (th_eval (shrincs_fxmss_hash_function P) pp
                (shrincs_fxmss_grind_tweak (uint U8 0, uint U64 0)) [::])).
           cbv delta [tcrx.TCRX_game].
           by rewrite /resolve /shrincs_fxmss_paired_eval_op /=
             coerce_kleisliE.
         rewrite heval.
         eapply (r_get_bind_rhs (tcrx.tcrx_pp_loc (shrincs_fxmss_hash_function P))
           None).
           by move=> h0 h1 [_ hp _ _ _].
         cbn [bind].
         rewrite !bind_assoc.
         eapply (@r_scheme_bind (bytes 16) (bytes 48) (shrincs_fxmss_public_seed_dist
           P));
           first exact: prog_valid.
         move=> pp.
         cbn [bind].
         eapply r_put_rhs_weak with
           (pre' := fun '(h0,h1) => shrincs_fxmss_paired_gen_pre P (Some pp) (h0,h1));
           first exact: shrincs_fxmss_paired_gen_pre_seed.
         cbv delta [shrincs_fxmss_paired_finish].
         match goal with
         | |- @rel_jdg ?A ?B ?pre ?post ?c0 (?f ?T ?c ?g) =>
           change (@rel_jdg A B pre post c0 (@code_link T c g))
         end.
         rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid
           (shrincs_fxmss_secret_dist P))).
         eapply (@r_scheme_bind (bytes 16) (bytes 48) (shrincs_fxmss_secret_dist P));
           first exact: prog_valid.
         move=> ks.
         rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid
           (shrincs_fxmss_secret_dist P))).
         eapply (@r_scheme_bind (bytes 16) (bytes 48) (shrincs_fxmss_secret_dist P));
           first exact: prog_valid.
         move=> kp.
         rewrite code_link_bind (code_link_scheme _ _ _ _
           (shrincs_fxmss_sample_keys_valid P emptym [interface] (shrincs_fxmss_schedule
             setup.1))).
         eapply (shrincs_fxmss_sample_keys_sized P (shrincs_fxmss_schedule setup.1)).
         move=> kt hkt.
         rewrite code_link_bind (code_link_scheme _ _ _ _
           (shrincs_fxmss_sample_digests_valid P emptym [interface]
             (shrincs_fxmss_schedule setup.1))).
         eapply (@r_scheme_bind shrincs_fxmss_digest_table (bytes 48));
           first exact: shrincs_fxmss_sample_digests_valid.
         move=> sd.
         cbv delta [shrincs_fxmss_lookup_keys].
         rewrite (@shrincs_fxmss_root_materialized P _ _ _ _
           hd).
         simpl.
         fold (@code_link (bytes 48)).
         rewrite code_link_bind.
         cbn [code_link].
         have ht := shrincs_fxmss_paired_generate_sim P Q bit pp setup.2 ks kp kt sd
           setup.1.1 setup.1.2 hd.
         rewrite -surjective_pairing in ht.
         have {}ht := ht hkt.
         cbn zeta in ht.
         exact ht.
    * simpl.
      apply: r_fail.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Paired hop *)

Import Shrincs.internal.ssprove.fxmss.scheme.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Local Opaque shrincs_fxmss_paired_inv shrincs_fxmss_paired_rel tcrx.TCRX_game
  shrincs_fxmss_leaf_capacity.

Lemma R_paired_perfect P Q bit :
  perfect I_forge
    (G_forge_full_signature P Q
      (fun st kt a md sg => (keep_no_tree_collision P st kt a md sg &&
        (bit || keep_no_paired_collision P st kt a md sg))%bool)
      true)
    (R_paired P Q ∘
      tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner (2
        * shrincs_fxmss_leaf_capacity Q - 1) bit).
Proof.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ (shrincs_fxmss_paired_inv P)).
- cbv beta delta [shrincs_fxmss_paired_inv].
  ssprove_invariant.
  cbv beta delta [shrincs_fxmss_paired_rel].
  by [].
- move=> id S T arg has.
  fmap_invert has.
  + rewrite resolve_link.
    exact: shrincs_fxmss_paired_gen_sim.
  + rewrite resolve_link.
    exact: shrincs_fxmss_paired_sign_sim.
  + rewrite resolve_link.
    exact: shrincs_fxmss_paired_hash_sim.
  + case: arg=> cm sg.
    rewrite resolve_link.
    exact: shrincs_fxmss_paired_forge_sim.
Qed.

Lemma R_paired_real P Q :
  perfect I_forge (G_tree_free P Q true)
    (R_paired P Q ∘
      tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        (2 * shrincs_fxmss_leaf_capacity Q - 1) true).
Proof.
have hk : (fun st kt a md sg => (keep_no_tree_collision P st kt a md sg &&
    (true || keep_no_paired_collision P st kt a md sg))%bool) =
    keep_no_tree_collision P.
  apply boolp.funext=> st; apply boolp.funext=> kt.
  apply boolp.funext=> a; apply boolp.funext=> md; apply boolp.funext=> sg.
  by rewrite /= andbT.
rewrite /G_tree_free -hk.
exact: (R_paired_perfect P Q true).
Qed.

Lemma R_paired_ideal P Q :
  perfect I_forge (G_forge_full_signature P Q (keep_paired_free P) true)
    (R_paired P Q ∘
      tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
        (2 * shrincs_fxmss_leaf_capacity Q - 1) false).
Proof. exact: (R_paired_perfect P Q false). Qed.

Lemma paired_advantage P Q (A : adversary I_forge) :
  Adv (G_tree_free P Q true) (G_forge_full_signature P Q (keep_paired_free P) true) A =
  AdvOf (tcrx.TCRX_game (shrincs_fxmss_hash_function P) fxmss_paired_class fxmss_partner
    (2 * shrincs_fxmss_leaf_capacity Q - 1)) (A ∘ R_paired P Q).
Proof.
rewrite (Adv_perfect_l (R_paired_real P Q)).
rewrite (Adv_perfect_r (R_paired_ideal P Q)).
exact: Adv_reduction.
Qed.

Lemma paired_sha256_advantage Q (A : adversary I_forge) :
  Adv (G_tree_free shrincs_fxmss_sha256 Q true)
    (G_forge_full_signature shrincs_fxmss_sha256 Q (keep_paired_free
      shrincs_fxmss_sha256) true) A =
  AdvOf (fxmss_tcrx_game (2 * shrincs_fxmss_leaf_capacity Q - 1)) (A ∘ R_paired
    shrincs_fxmss_sha256 Q).
Proof.
have he b : tcrx.TCRX_game (shrincs_fxmss_hash_function shrincs_fxmss_sha256)
  fxmss_paired_class fxmss_partner
    (2 * shrincs_fxmss_leaf_capacity Q - 1) b = fxmss_tcrx_game (2 *
      shrincs_fxmss_leaf_capacity Q - 1) b.
  apply: package_ext=> x.
  reflexivity.
  cbv delta [tcrx.TCRX_game].
  reflexivity.
rewrite (paired_advantage shrincs_fxmss_sha256 Q A).
by rewrite !he.
Qed.
