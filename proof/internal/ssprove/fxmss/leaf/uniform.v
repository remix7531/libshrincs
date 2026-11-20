(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.uniform

    Shared-seed prepared-leaf hybrids. A legal shape and digest table are
    supplied at GEN; EVAL remains available before GEN. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.sample_seq toolkit.relational_rules toolkit.link_forward
  games.scheduled_batch.
From mathcomp Require Import reals.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.known_message leaf.batch
    leaf.prepare
  leaf.uniform_sampling.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Operation and location identifiers occupy 1500..1599. *)
Definition leaf_prepared_gen : nat := 1540.
Definition leaf_prepared_done_loc := mkloc 1540 false.

Definition I_leaf_prepared_ud :=
  [interface
    [ leaf_prepared_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      fixed_public };
    [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature };
    [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 }
  ].

Definition C_leaf_prepared_ud : package I_leaf_batch_ud I_leaf_prepared_ud.
Proof.
notypeclasses refine [package [fmap leaf_prepared_done_loc];
  [ leaf_prepared_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
    fixed_public } (q) {
    done ← get leaf_prepared_done_loc ;;
    #assert ~~ done ;;
    #assert shrincs_fxmss_structure_legal q.1.1 q.1.2 ;;
    _ ← call [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 }
      known_message_pin ;;
    leaves ← leaf_grind_batch q.1 q.2 ;;
    pk ← call [ leaf_batch_gen ] : { 'list fixed_leaf ~> fixed_public } leaves ;;
    #put leaf_prepared_done_loc := true ;;
    ret pk
  };
  [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature } (_) {
    call [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature } tt
  };
  [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } (q) {
    call [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } q
  }
].
ssprove_valid.
apply: leaf_grind_batch_valid.
by fmap_solve.
Defined.

Definition leaf_roots_seed : raw_code (bytes 16) :=
  ppo ← get (ud_pp_loc shrincs_thf) ;;
  match ppo with
  | Some pp => ret pp
  | None => pp ← dBytes 16 ;;
            #put (ud_pp_loc shrincs_thf) := Some pp ;; ret pp
  end.

Definition leaf_roots_locs :=
  [fmap leaf_prepared_done_loc; leaf_batch_cache_loc; leaf_batch_slot_loc;
    ud_pp_loc shrincs_thf].

#[export] Instance leaf_roots_seed_valid I :
  ValidCode leaf_roots_locs I leaf_roots_seed.
Proof. rewrite /leaf_roots_seed; ssprove_valid. Qed.

Definition G_leaf_roots (r : nat) : game I_leaf_prepared_ud :=
  [package leaf_roots_locs;
    [ leaf_prepared_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      fixed_public } (q) {
      done ← get leaf_prepared_done_loc ;;
      #assert ~~ done ;;
      #assert shrincs_fxmss_structure_legal q.1.1 q.1.2 ;;
      pp ← leaf_roots_seed ;;
      xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule q.1)) ;;
      let cache := leaf_ud_complete r (known_message_prepared shrincs_fxmss_sha256 q.1
        pp q.2) pp
        xs in
      #put leaf_batch_cache_loc := Some [seq entry.2 | entry <- cache] ;;
      #put leaf_prepared_done_loc := true ;;
      ret (pp, [seq entry.1 | entry <- cache])
    };
    [ leaf_batch_sign ] : { 'unit ~> 'option fixed_signature } (_) {
      cache ← getSome leaf_batch_cache_loc ;;
      i ← get leaf_batch_slot_loc ;;
      #put leaf_batch_slot_loc := i.+1 ;;
      ret (nth None cache i)
    };
    [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 } (q) {
      #assert ~~ wots_c_hash_class q.1 ;;
      pp ← leaf_roots_seed ;;
      ret (Th pp q.1 q.2)
    }
  ].

Lemma leaf_grind_batch_forward s sp sd :
  code_link (leaf_grind_batch sp sd) (C_leaf_batch_ud s) =
    leaf_grind_batch sp sd.
Proof.
eapply (code_link_forward emptym
  [interface [ EVAL ] : { tweak × 'list ('word U8) ~> bytes 16 } ]).
- apply: leaf_grind_batch_valid. by fmap_solve.
- (* Every evaluation call is forwarded unchanged. *)
  move=> o ho x.
  have he : o = (EVAL, (tweak × 'list ('word U8), bytes 16)).
  { move: ho; rewrite /fhas /=.
    case: o x => n [a z] x /=.
    rewrite setmE.
    case: eqP => hn; last by rewrite emptymE.
    by move=> [<- <-]; subst n. }
  subst o.
  by rewrite /C_leaf_batch_ud /resolve /= coerce_kleisliE.
Qed.

Lemma leaf_prepared_gen_link s sp sd :
  resolve (C_leaf_prepared_ud ∘ C_leaf_batch_ud s)%pack
    (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      fixed_public)) (sp, sd) =
  (done ← get leaf_prepared_done_loc ;;
   #assert ~~ done ;;
   #assert shrincs_fxmss_structure_legal sp.1 sp.2 ;;
   _ ← call [ EVAL ] : { th_T shrincs_thf × th_M shrincs_thf ~> bytes 16 }
     known_message_pin ;;
   r ← leaf_ud_public_setup s sp sd ;;
   #put leaf_batch_cache_loc := Some [seq entry.2 | entry <- r.2] ;;
   #put leaf_prepared_done_loc := true ;;
   ret (r.1, [seq entry.1 | entry <- r.2])).

Proof.
rewrite resolve_link.
rewrite /C_leaf_prepared_ud /resolve /= coerce_kleisliE.
cbn [code_link].
congr (getr _ _).
apply functional_extensionality => done.
rewrite !code_link_assertD.
apply f_equal; apply functional_extensionality => hd.
apply f_equal; apply functional_extensionality => hsp.
cbn [code_link resolve].
rewrite /leaf_ud_public_setup code_link_bind bind_assoc.
rewrite leaf_grind_batch_forward.
rewrite /resolve /= !coerce_kleisliE.
cbn [bind code_link].
congr (opr _ _ _).
apply functional_extensionality => y.
apply f_equal; apply functional_extensionality => leaves.
rewrite /resolve /= coerce_kleisliE.
cbn [bind code_link].
by [].
Qed.

Local Abbreviation leaf_roots_inv :=
  (heap_ignore leaf_ud_setup_locs
   ⋊ couple_rhs leaf_prepared_done_loc ud_rev_loc
       (fun done rev => done = false -> rev = false)
   ⋊ couple_rhs leaf_prepared_done_loc (ud_tws_loc shrincs_thf)
       (fun done tws => done = false -> tws = [::])
   ⋊ couple_rhs leaf_prepared_done_loc scheduled_done_loc
       (fun done sched => done = false -> sched = false)).

Local Opaque dBytes leaf_grind_batch Th.

Local Opaque G_scheduled_ud.

Definition leaf_roots_store (r : bytes 16 * seq fixed_cache_entry) :
    raw_code fixed_public :=
  #put leaf_batch_cache_loc := Some [seq entry.2 | entry <- r.2] ;;
  #put leaf_prepared_done_loc := true ;;
  ret (r.1, [seq entry.1 | entry <- r.2]).

Lemma leaf_roots_inv_done h0 h1 :
  heap_ignore leaf_ud_setup_locs (h0, h1) ->
  leaf_roots_inv
    (set_heap h0 leaf_prepared_done_loc true,
     set_heap h1 leaf_prepared_done_loc true).

Proof.
move=> hi.
split; first split; first split.
- exact: put_pre_cond_heap_ignore hi.
- by rewrite !rel_app_cons /= get_set_heap_eq.
- by rewrite !rel_app_cons /= get_set_heap_eq.
- by rewrite !rel_app_cons /= get_set_heap_eq.
Qed.

Lemma leaf_roots_finish b s sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> (s < 14)%nat ->
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame (leaf_ud_setup_frame pp) [::] (h0, h1) /\
      get_heap h1 scheduled_done_loc = false ⦄
    (r ← (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
          ret (pp, leaf_ud_complete (if b then s else s.+1)
            (known_message_prepared shrincs_fxmss_sha256 sp pp sd) pp xs)) ;;
     leaf_roots_store r) ≈
    (r ← code_link (leaf_ud_public_setup s sp sd)
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b) ;;
     leaf_roots_store r)
  ⦃ fun '(pk0, h0) '(pk1, h1) => pk0 = pk1 /\ leaf_roots_inv (h0, h1) ⦄.

Proof.
move=> hsp hs.
eapply r_bind.
- apply: leaf_ud_public_sampling hsp hs _ _ _ _.
  + exact: leaf_ud_setup_frame_targets.
  + exact: leaf_ud_setup_frame_reveal.
  + exact: leaf_ud_setup_frame_done.
  + by move=> h0 h1 [_ hp].
- (* Storing the coupled results establishes the leaf-root invariant. *)
  move=> r0 r1.
  eapply rpre_hypothesis_rule => h0 h1 [he [[hi hp] _]].
  subst r1.
  eapply (rpre_weaken_rule
    (fun '(h0, h1) => heap_ignore leaf_ud_setup_locs (h0, h1)));
    last by move=> h0' h1' /= [-> ->].
  rewrite /leaf_roots_store.
  ssprove_sync.
  apply r_put_vs_put.
  apply r_ret => h0' h1' [hh1 [[hh0 [hi' ->]] ->]].
  split; first by [].
  exact: leaf_roots_inv_done hi'.
Qed.

Lemma leaf_roots_inv_start pp h0 h1 :
  leaf_roots_inv (h0, h1) ->
  get_heap h1 leaf_prepared_done_loc = false ->
  get_heap h1 (ud_pp_loc shrincs_thf) = Some pp ->
  leaf_ud_frame (leaf_ud_setup_frame pp) [::] (h0, h1) /\
    get_heap h1 scheduled_done_loc = false.


Proof.
move=> [[[hi hr] ht] hd] hdone hp.
move: hr ht hd; rewrite !rel_app_cons /= => hr ht hd.
split.
- split; first by split.
  split; first exact: hr hdone.
  exact: ht hdone.
- exact: hd hdone.
Qed.

Lemma leaf_roots_gen_sim b s sp sd :
  (s < 14)%nat ->
  ⊢ ⦃ fun '(h0, h1) => leaf_roots_inv (h0, h1) ⦄
    resolve (G_leaf_roots (if b then s else s.+1))
      (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
        fixed_public)) (sp, sd) ≈
    resolve (C_leaf_prepared_ud ∘ (C_leaf_batch_ud s ∘
      G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b))%pack
      (leaf_prepared_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
        fixed_public)) (sp, sd)
  ⦃ fun '(pk0, h0) '(pk1, h1) => pk0 = pk1 /\ leaf_roots_inv (h0, h1) ⦄.

Proof.
move=> hs.
rewrite link_assoc resolve_link leaf_prepared_gen_link.
rewrite /G_leaf_roots /resolve /= coerce_kleisliE.
cbn [code_link].
refine (r_get_vs_get_remember_rhs (pre := leaf_roots_inv) _).
move=> done.
rewrite code_link_assertD.
ssprove_sync => hdone.
case: done hdone => //= _.
rewrite code_link_assertD.
ssprove_sync => hsp.
cbn [code_link].
rewrite resolve_leaf_ud_eval.
eapply (r_bind_assertD_rhs _
  (leaf_roots_inv ⋊ rem_rhs leaf_prepared_done_loc false)); first by [].
move=> _.
cbn [bind].
refine (r_get_vs_get_remember_rhs
  (pre := leaf_roots_inv ⋊ rem_rhs leaf_prepared_done_loc false) _).
move=> ppo.
case: ppo => [pp|].
- cbn [bind].
  rewrite code_link_bind.
  cbn [code_link].
  have hf := leaf_roots_finish b s sp sd pp hsp hs.
  rewrite bind_assoc /leaf_roots_store in hf.
  cbn [bind] in hf.
  eapply rpre_weaken_rule; first exact: hf.
  move=> h0 h1 [[hi hd] hp].
  apply: leaf_roots_inv_start hi _ _.
  + by move: hd; rewrite /rem_inv /=.
  + by move: hp; rewrite /rem_inv /=.
- change (th_dPP shrincs_thf) with (dBytes 16).
  remember (dBytes 16) as dn eqn:hdn.
  rewrite !bind_assoc.
  cbn [bind].
  eapply r_scheme_bind; first by rewrite hdn; exact: prog_valid.
  move=> pp.
  apply r_put_vs_put.
  rewrite code_link_bind.
  cbn [code_link].
  rewrite hdn.
  have hf := leaf_roots_finish b s sp sd pp hsp hs.
  rewrite bind_assoc /leaf_roots_store in hf.
  cbn [bind] in hf.
  rewrite /leaf_ud_public_setup code_link_bind
    (bind_assoc (code_link (leaf_grind_batch sp sd)
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b))) in
        hf.
  cbn [code_link bind] in hf.
  setoid_rewrite bind_assoc in hf.
  cbn [bind] in hf.
  eapply rpre_weaken_rule; first exact: hf.
  move=> h0 h1 [h1' [[h0' [[[hi hd] hp] ->]] ->]].
  apply: leaf_roots_inv_start.
  + have hpres : put_pre_cond (ud_pp_loc shrincs_thf) (Some pp)
      leaf_roots_inv by ssprove_invariant.
    exact: hpres hi.
  + by rewrite get_set_heap_neq.
  + exact: get_set_heap_eq.
Qed.


Lemma leaf_roots_perfect b s :
  (s < 14)%nat ->
  perfect I_leaf_prepared_ud (G_leaf_roots (if b then s else s.+1))
    (C_leaf_prepared_ud ∘ G_leaf_batch_ud s (2 ^ 69) b).
Proof.
move=> hs.
rewrite /G_leaf_batch_ud.
ssprove_share.
eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ leaf_roots_inv).
{ ssprove_invariant => //. }
simplify_eq_rel arg.
- (* GEN agrees with the scheduled batch reduction. *)
  case: arg => sp sd.
  have hg := leaf_roots_gen_sim b s sp sd hs.
  rewrite resolve_link /G_leaf_roots /C_leaf_prepared_ud /resolve /=
    !coerce_kleisliE in hg.
  cbn [code_link] in hg.
  exact: hg.
- (* Opening a cached leaf returns the same value. *)
  ssprove_code_simpl.
  simpl.
  ssprove_sync => cache.
  rewrite bind_ret.
  ssprove_sync => hc.
  ssprove_sync => i.
  ssprove_sync.
  by apply r_ret.
- case: arg => t m.
  ssprove_code_simpl.
  simpl.
  rewrite bind_ret.
  ssprove_sync => ht.
  ssprove_sync => ppo.
  case: ppo => [pp|].
  + by apply r_ret.
  + (* An absent public seed is sampled and stored on both sides. *)
    refine (r_scheme_bind (dBytes 16) _ _
      (fun '(h0, h1) => leaf_roots_inv (h0, h1)) _ _ _).
    move=> pp.
    ssprove_sync.
    by apply r_ret.
Qed.

Definition R_leaf_prepared_ud s := C_leaf_prepared_ud ∘ R_leaf_batch_ud s.

Lemma leaf_prepared_ud_perfect b s :
  (s < 14)%nat ->
  perfect I_leaf_prepared_ud (G_leaf_roots (if b then s else s.+1))
    (R_leaf_prepared_ud s ∘ SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69) b).
Proof.
move=> hs.
eapply perfect_trans; first exact: leaf_roots_perfect hs.
rewrite /R_leaf_prepared_ud -sep_link_assoc.
apply static_batch.batch_context_perfect.
exact: R_leaf_batch_ud_perfect.
Qed.

Lemma leaf_prepared_ud_advantage s (A : adversary I_leaf_prepared_ud) :
  (s < 14)%nat ->
  Adv (G_leaf_roots s) (G_leaf_roots s.+1) A =
  AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
    (A ∘ R_leaf_prepared_ud s).
Proof.
move=> hs.
rewrite (Adv_perfect_l (leaf_prepared_ud_perfect true s hs)).
rewrite (Adv_perfect_r (leaf_prepared_ud_perfect false s hs)).
exact: Adv_reduction.
Qed.

Lemma leaf_prepared_ud_telescope (A : adversary I_leaf_prepared_ud) :
  (Adv (G_leaf_roots 0) (G_leaf_roots 14) A <=
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (A ∘ R_leaf_prepared_ud s))%R.
Proof.
have h := Adv_hybrid_dep (IGame := I_leaf_prepared_ud) (n := 14)
  (Multi := fun b => as_nom (G_leaf_roots (if b then 0 else 14)))
  (Game := fun s b => as_nom (G_leaf_roots (if b then s else s.+1)))
  (A := A).
have ht : (Adv (G_leaf_roots 0) (G_leaf_roots 14) A <=
    \sum_(0 <= s < 14) Adv (G_leaf_roots s) (G_leaf_roots s.+1) A)%R.
{ apply: h; first exact: perfect_refl.
  - exact: perfect_refl.
  - by move=> i hi; apply: perfect_refl. }
have he : (\sum_(0 <= s < 14)
    Adv (G_leaf_roots s) (G_leaf_roots s.+1) A =
    \sum_(0 <= s < 14)
      AdvOf (SMUD_game shrincs_thf wots_c_hash_class (2 ^ 69))
        (A ∘ R_leaf_prepared_ud s))%R.
{ apply: eq_big_nat => s /andP[_ hs].
  exact: leaf_prepared_ud_advantage hs. }
by rewrite -he.
Qed.
