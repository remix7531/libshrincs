(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.uniform_sampling

    Couple one independent node per batch row to the guarded static UD query loop.
    Preserve a caller-supplied state invariant through static UD setup. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.sample_seq toolkit.relational_rules games.static_batch chain.core
  chain.ud games.scheduled_batch.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape games instance leaf.fixed_batch leaf.known_message leaf.prepare
    leaf.batch.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Leaf uniform guesses sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope nat_scope.

Local Opaque dBytes.

Fixpoint leaf_ud_answers (b : bool) (pp : bytes 16)
    (ts : seq (option tweak)) (xs : seq (bytes 16)) : seq (bytes 16) :=
  match ts, xs with
  | t :: ts', x :: xs' =>
      (if t is Some t then if b then Th pp t x else x else x) ::
        leaf_ud_answers b pp ts' xs'
  | _, _ => [::]
  end.

Definition leaf_ud_loop_pre (tws : seq tweak) : precond :=
  fun '(h0, h1) =>
    heap_ignore [fmap ud_tws_loc shrincs_thf] (h0, h1) /\
    get_heap h1 ud_rev_loc = false /\
    get_heap h1 (ud_tws_loc shrincs_thf) = tws.

Lemma leaf_ud_loop_pre_set tws tws' h0 h1 :
  leaf_ud_loop_pre tws (h0, h1) ->
  leaf_ud_loop_pre tws'
    (h0, set_heap h1 (ud_tws_loc shrincs_thf) tws').
Proof.
move=> [hi [hr ht]].
split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; fmap_solve.
- split.
  + by rewrite get_set_heap_neq.
  + exact: get_set_heap_eq.
Qed.

Lemma leaf_ud_answers_real_rows leaves s pp rows xs i :
  s < 16 ->
  (forall j, j < size rows ->
    nth (uint U8 0, uint U64 0, 0, 0) (fixed_rows leaves) (i + j) =
    nth (uint U8 0, uint U64 0, 0, 0) rows j) ->
  leaf_ud_answers true pp
    [seq if s.+2 <= row.2 then Some (fixed_tweak row s) else None
      | row <- rows] xs =
  uq_real_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp s i [seq row.2 | row <- rows] xs.
Proof.
move=> hs.
elim: rows xs i => [|row rows ih] [|x xs] i //= hrows.
have hhead := hrows 0 (ltn0Sn _).
rewrite addn0 /= in hhead.
congr (_ :: _).
- case: ifP => hq //=.
  by rewrite (fixed_query_hash leaves pp i s x hs) hhead.
- apply: ih => j hj.
  have he := hrows j.+1 hj.
  by rewrite addSn -addnS.
Qed.

Lemma leaf_ud_answers_real leaves s pp xs :
  s < 16 ->
  leaf_ud_answers true pp (fixed_ud_requests s leaves) xs =
  uq_real_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp s 0 (fixed_flat_digits leaves) xs.
Proof.
move=> hs.
apply: leaf_ud_answers_real_rows hs _.
by move=> j hj; rewrite add0n.
Qed.

Lemma leaf_ud_answers_ideal pp ts xs :
  size xs = size ts -> leaf_ud_answers false pp ts xs = xs.
Proof.
elim: ts xs => [|t ts ih] [|x xs] //= [he].
by case: t => [t|] /=; rewrite ih.
Qed.

Lemma leaf_ud_loop_sampling p b pp ts tws :
  all wots_c_hash_class (pmap id ts) ->
  uniq (tws ++ pmap id ts) ->
  size tws + count isSome ts <= p ->
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_loop_pre tws (h0, h1) ⦄
    sample_seq (dBytes 16) (size ts) ≈
    batch_loop shrincs_thf
      (batch_ud_local shrincs_thf wots_c_hash_class p b pp) ts
  ⦃ fun '(xs, h0) '(ys, h1) =>
      leaf_ud_loop_pre (tws ++ pmap id ts) (h0, h1) /\
      size xs = size ts /\ ys = leaf_ud_answers b pp ts xs ⦄.
Proof.
remember (dBytes 16) as dn eqn:hdn.
elim: ts tws => [|t ts ih] tws.
- move=> hcl hu hc.
  apply r_ret => h0 h1 hp.
  by rewrite cats0.
- cbn [size sample_seq batch_loop].
  case: t => [t|].
  + move=> /andP[hcl hcls] hu hc.
    have ht : t \notin tws.
    { move: hu; rewrite cat_uniq => /and3P[_ /hasPn hd _].
      exact: hd t (mem_head _ _). }
    have hc' : size tws < p.
    { apply: leq_trans hc.
      change (size tws < size tws + (1 + count isSome ts)).
      by rewrite addnS ltnS leq_addr. }
    rewrite /batch_ud_local bind_assoc.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_get_bind_rhs ud_rev_loc false);
      first by move=> h0 h1 [_ [hr _]].
    cbv beta iota.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_get_bind_rhs (ud_tws_loc shrincs_thf) tws);
      first by move=> h0 h1 [_ [_ htws]].
    cbv beta iota.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_put_bind_rhs (ud_tws_loc shrincs_thf) (rcons tws t) _
      (leaf_ud_loop_pre (rcons tws t))).
    { move=> h0 h1 hp. exact: leaf_ud_loop_pre_set hp. }
    have hsample : (if b then x ← th_dM shrincs_thf ;;
      ret (th_eval shrincs_thf pp t x) else th_dN shrincs_thf) =
      (x ← dn ;; ret (if b then Th pp t x else x)).
    { rewrite hdn.
      clear ih.
      case: b.
      - change ((x ← (n ← dBytes 16 ;; ret (tval n)) ;; ret (Th pp t x)) =
          (x ← dBytes 16 ;; ret (Th pp t x))).
        by rewrite bind_assoc.
      - by rewrite bind_ret. }
    rewrite hsample bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> x.
    cbn [bind].
    eapply r_bind.
    - apply: ih hcls _ _.
      + by rewrite -cats1 -catA.
      + by move: hc; rewrite /= size_rcons addSn addnS.
    - move=> xs ys.
      apply r_ret => h0 h1 [hp [hs hy]].
      split.
      + by move: hp; rewrite -cats1 -catA.
      + split; first by rewrite /= hs.
        by rewrite /= hy.
  + (* A request without a target samples a uniform head value. *)
    move=> hcl hu hc.
    change (th_dN shrincs_thf) with (dBytes 16).
    rewrite -hdn.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> x.
    eapply r_bind; first exact: ih hcl hu hc.
    move=> xs ys.
    apply r_ret => h0 h1 [hp [hs hy]].
    split; first exact: hp.
    split; first by rewrite /= hs.
    by rewrite /= hy.
Qed.

Definition leaf_ud_complete s leaves (pp : bytes 16) xs :=
  let sigs := roots_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp s 0 (fixed_flat_digits leaves) xs in
  let ends := ends_from_sig (bytes 16) (bytes 16)
    (size (fixed_rows leaves)) 16 (fixed_F leaves)
    pp (fixed_flat_digits leaves) sigs in
  fixed_cache pp leaves sigs ends.

Lemma leaf_ud_complete_real s leaves pp xs :
  s < 16 ->
  fixed_complete true s leaves
    (pp, leaf_ud_answers true pp (fixed_ud_requests s leaves) xs) =
  leaf_ud_complete s leaves pp xs.
Proof.
move=> hs.
rewrite /fixed_complete /leaf_ud_complete /=.
by rewrite (leaf_ud_answers_real leaves s pp xs hs) rud_sig_real.
Qed.

Lemma leaf_ud_complete_ideal s leaves pp xs :
  size xs = size (fixed_rows leaves) ->
  fixed_complete true s leaves
    (pp, leaf_ud_answers false pp (fixed_ud_requests s leaves) xs) =
  leaf_ud_complete s.+1 leaves pp xs.
Proof.
move=> hsize.
rewrite /fixed_complete /leaf_ud_complete /= leaf_ud_answers_ideal.
- by rewrite /fixed_ud_requests size_map.
- by rewrite rud_sig_ideal.
Qed.

Lemma leaf_ud_completion_sampling p b s leaves pp :
  s < 16 ->
  uniq (pmap id (fixed_ud_requests s leaves)) ->
  count isSome (fixed_ud_requests s leaves) <= p ->
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_loop_pre [::] (h0, h1) ⦄
    (xs ← sample_seq (dBytes 16) (size (fixed_rows leaves)) ;;
     ret (leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    (ys ← batch_loop shrincs_thf
      (batch_ud_local shrincs_thf wots_c_hash_class p b pp)
      (fixed_ud_requests s leaves) ;;
     ret (fixed_complete true s leaves (pp, ys)))
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\
      leaf_ud_loop_pre (pmap id (fixed_ud_requests s leaves)) (h0, h1) ⦄.
Proof.
move=> hs hu hc.
have hn : size (fixed_ud_requests s leaves) = size (fixed_rows leaves).
  by rewrite /fixed_ud_requests size_map.
rewrite -{1}hn.
eapply r_bind.
- apply: leaf_ud_loop_sampling.
  + exact: fixed_ud_targets_class.
  + exact: hu.
  + exact: hc.
- move=> xs ys.
  apply r_ret => h0 h1 [hp [hsize ->]].
  split; last exact: hp.
  case: b.
  + by rewrite leaf_ud_complete_real.
  + rewrite leaf_ud_complete_ideal // -hn.
    exact: hsize.
Qed.

Lemma leaf_ud_prepared_sampling b s sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  let leaves := known_message_prepared shrincs_fxmss_sha256 sp pp sd in
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_loop_pre [::] (h0, h1) ⦄
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     ret (leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    (ys ← batch_loop shrincs_thf
      (batch_ud_local shrincs_thf wots_c_hash_class (2 ^ 69) b pp)
      (fixed_ud_requests s leaves) ;;
     ret (fixed_complete true s leaves (pp, ys)))
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\
      leaf_ud_loop_pre (pmap id (fixed_ud_requests s leaves)) (h0, h1) ⦄.
Proof.
move=> hsp hs /=.
rewrite -(known_message_prepared_budget shrincs_fxmss_sha256 sp pp sd).
apply: leaf_ud_completion_sampling.
- apply: leq_trans hs _.
  by [].
- exact: leaf_ud_targets_uniq hsp (ltnW hs).
- have [_ _ hc] := leaf_ud_domain shrincs_fxmss_sha256 sp pp sd s hsp hs.
  exact: hc.
Qed.

Lemma fixed_flat_digits_wf leaves :
  all (fun leaf => all (fun d => d < 16) (fixed_digits leaf)) leaves ->
  wf_digits 16 (fixed_flat_digits leaves).
Proof.
move=> hd.
apply/allP=> d /mapP[row hr ->].
exact: fixed_rows_digit_bound leaves row hd hr.
Qed.

Lemma leaf_ud_complete_zero leaves pp xs :
  all (fun leaf => all (fun d => d < 16) (fixed_digits leaf)) leaves ->
  leaf_ud_complete 0 leaves pp xs =
  fixed_cache pp leaves
    (sign_digits (bytes 16) (bytes 16) (size (fixed_rows leaves))
      16 (fixed_F leaves) pp xs (fixed_flat_digits leaves))
    (chain_ends (bytes 16) (bytes 16) (size (fixed_rows leaves))
      16 (fixed_F leaves) pp xs).
Proof.
move=> hd.
rewrite /leaf_ud_complete ends_from_roots_map0.
- exact: size_map.
- exact: fixed_flat_digits_wf hd.
- (* Initial chain roots reproduce the signatures at the fixed digits. *)
  have hsize : size (fixed_flat_digits leaves) = size (fixed_rows leaves).
    exact: size_map.
  by rewrite (roots_map_sign (bytes 16) (bytes 16)
    (size (fixed_rows leaves)) 16 (fixed_F leaves) pp
    (fixed_flat_digits leaves) xs hsize).
Qed.

Lemma leaf_ud_complete_last leaves pp xs :
  all (fun leaf => all (fun d => d < 16) (fixed_digits leaf)) leaves ->
  let sigs := sig_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp 0 (fixed_flat_digits leaves) xs in
  leaf_ud_complete 14 leaves pp xs =
  fixed_cache pp leaves sigs
    (ends_from_sig (bytes 16) (bytes 16) (size (fixed_rows leaves))
      16 (fixed_F leaves) pp (fixed_flat_digits leaves) sigs).
Proof.
move=> hd /=.
rewrite /leaf_ud_complete.
by rewrite (sig_map_roots _ _ _ _ _ _ _ _ (fixed_flat_digits_wf leaves hd)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf uniform guesses setup *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope nat_scope.

Definition leaf_ud_frame (J : precond) (tws : seq tweak) : precond :=
  fun '(h0, h1) => J (h0, h1) /\
    get_heap h1 ud_rev_loc = false /\
    get_heap h1 (ud_tws_loc shrincs_thf) = tws.

Lemma leaf_ud_frame_set J tws tws' h0 h1 :
  (forall h0 h1 ts, J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts)) ->
  leaf_ud_frame J tws (h0, h1) ->
  leaf_ud_frame J tws' (h0, set_heap h1 (ud_tws_loc shrincs_thf) tws').
Proof.
move=> hstable [hj [hr ht]].
split; first exact: hstable hj.
split.
- by rewrite get_set_heap_neq.
- exact: get_set_heap_eq.
Qed.

Lemma leaf_ud_loop_framed p b pp ts tws (J : precond) :
  (forall h0 h1 ts', J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts')) ->
  all wots_c_hash_class (pmap id ts) ->
  uniq (tws ++ pmap id ts) ->
  size tws + count isSome ts <= p ->
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame J tws (h0, h1) ⦄
    sample_seq (dBytes 16) (size ts) ≈
    batch_loop shrincs_thf
      (batch_ud_local shrincs_thf wots_c_hash_class p b pp) ts
  ⦃ fun '(xs, h0) '(ys, h1) =>
      leaf_ud_frame J (tws ++ pmap id ts) (h0, h1) /\
      size xs = size ts /\ ys = leaf_ud_answers b pp ts xs ⦄.
Proof.
move=> hstable.
remember (dBytes 16) as dn eqn:hdn.
elim: ts tws => [|t ts ih] tws.
- move=> hcl hu hc.
  apply r_ret => h0 h1 hp.
  by rewrite cats0.
- cbn [size sample_seq batch_loop].
  case: t => [t|].
  + move=> /andP[hcl hcls] hu hc.
    have ht : t \notin tws.
    { move: hu; rewrite cat_uniq => /and3P[_ /hasPn hd _].
      exact: hd t (mem_head _ _). }
    have hc' : size tws < p.
    { apply: leq_trans hc.
      change (size tws < size tws + (1 + count isSome ts)).
      by rewrite addnS ltnS leq_addr. }
    rewrite /batch_ud_local bind_assoc.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_get_bind_rhs ud_rev_loc false);
      first by move=> h0 h1 [_ [hr _]].
    cbv beta iota.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_get_bind_rhs (ud_tws_loc shrincs_thf) tws);
      first by move=> h0 h1 [_ [_ htws]].
    cbv beta iota.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply r_bind_assertD_rhs; first by [].
    move=> _.
    eapply (r_put_bind_rhs (ud_tws_loc shrincs_thf) (rcons tws t) _
      (leaf_ud_frame J (rcons tws t))).
    { move=> h0 h1 hp. exact: leaf_ud_frame_set hstable hp. }
    have hsample : (if b then x ← th_dM shrincs_thf ;;
      ret (th_eval shrincs_thf pp t x) else th_dN shrincs_thf) =
      (x ← dn ;; ret (if b then Th pp t x else x)).
    { rewrite hdn.
      clear ih.
      case: b.
      - change ((x ← (n ← dBytes 16 ;; ret (tval n)) ;; ret (Th pp t x)) =
          (x ← dBytes 16 ;; ret (Th pp t x))).
        by rewrite bind_assoc.
      - by rewrite bind_ret. }
    rewrite hsample bind_assoc.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> x.
    cbn [bind].
    eapply r_bind.
    - apply: ih hcls _ _.
      + by rewrite -cats1 -catA.
      + by move: hc; rewrite /= size_rcons addSn addnS.
    - move=> xs ys.
      apply r_ret => h0 h1 [hp [hs hy]].
      split.
      + by move: hp; rewrite -cats1 -catA.
      + split; first by rewrite /= hs.
        by rewrite /= hy.
  + (* A request without a target samples a uniform head value. *)
    move=> hcl hu hc.
    change (th_dN shrincs_thf) with (dBytes 16).
    rewrite -hdn.
    eapply r_scheme_bind; first exact: prog_valid.
    move=> x.
    eapply r_bind; first exact: ih hcl hu hc.
    move=> xs ys.
    apply r_ret => h0 h1 [hp [hs hy]].
    split; first exact: hp.
    split; first by rewrite /= hs.
    by rewrite /= hy.
Qed.

Lemma leaf_ud_completion_framed p b s leaves pp (J : precond) :
  (forall h0 h1 ts, J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts)) ->
  s < 16 ->
  uniq (pmap id (fixed_ud_requests s leaves)) ->
  count isSome (fixed_ud_requests s leaves) <= p ->
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) ⦄
    (xs ← sample_seq (dBytes 16) (size (fixed_rows leaves)) ;;
     ret (leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    (ys ← batch_loop shrincs_thf
      (batch_ud_local shrincs_thf wots_c_hash_class p b pp)
      (fixed_ud_requests s leaves) ;;
     ret (fixed_complete true s leaves (pp, ys)))
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\
      leaf_ud_frame J (pmap id (fixed_ud_requests s leaves)) (h0, h1) ⦄.
Proof.
move=> hstable hs hu hc.
have hn : size (fixed_ud_requests s leaves) = size (fixed_rows leaves).
  by rewrite /fixed_ud_requests size_map.
rewrite -{1}hn.
eapply r_bind.
- apply: leaf_ud_loop_framed.
  + exact: hstable.
  + exact: fixed_ud_targets_class.
  + exact: hu.
  + exact: hc.
- move=> xs ys.
  apply r_ret => h0 h1 [hp [hsize ->]].
  split; last exact: hp.
  case: b.
  + by rewrite leaf_ud_complete_real.
  + rewrite leaf_ud_complete_ideal // -hn.
    exact: hsize.
Qed.

Definition leaf_ud_setup s sp sd : raw_code ('list fixed_cache_entry) :=
  leaves ← leaf_grind_batch sp sd ;;
  r ← call [ scheduled_gen ] :
    { 'list ('option tweak) ~> batch_output shrincs_thf }
    (fixed_ud_requests s leaves) ;;
  ret (fixed_complete true s leaves r).

Lemma leaf_ud_setup_valid L I s sp sd :
  fhas I (EVAL, (tweak × 'list ('word U8), bytes 16)) ->
  fhas I (scheduled_gen,
    ('list ('option tweak), batch_output shrincs_thf)) ->
  ValidCode L I (leaf_ud_setup s sp sd).
Proof.
move=> heval hgen.
rewrite /leaf_ud_setup.
eapply valid_bind; first exact: leaf_grind_batch_valid heval.
move=> leaves.
eapply valid_opr; first exact: hgen.
move=> r; exact: valid_ret.
Qed.

Lemma resolve_leaf_ud_gen p b ts :
  resolve (G_scheduled_ud shrincs_thf wots_c_hash_class p known_message_pin b)
    (scheduled_gen, ('list ('option tweak), batch_output shrincs_thf)) ts =
  (done ← get scheduled_done_loc ;;
   #assert ~~ done ;;
   #assert ~~ wots_c_hash_class known_message_pin.1 ;;
   ppo ← get (ud_pp_loc shrincs_thf) ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dBytes 16 ;;
                  #put (ud_pp_loc shrincs_thf) := Some pp ;; ret pp
        end ;;
   ys ← batch_loop shrincs_thf
     (batch_ud_local shrincs_thf wots_c_hash_class p b pp) ts ;;
   #put ud_rev_loc := true ;;
   #put scheduled_done_loc := true ;;
   ret (pp, ys)).
Proof. by rewrite /G_scheduled_ud /resolve /= coerce_kleisliE. Qed.

Lemma leaf_ud_scheduled_sampling b s sp sd pp (J : precond) :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  (forall h0 h1 ts, J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts)) ->
  (forall h0 h1, J (h0, h1) -> J (h0, set_heap h1 ud_rev_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    J (h0, set_heap h1 scheduled_done_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  let leaves := known_message_prepared shrincs_fxmss_sha256 sp pp sd in
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) /\
      get_heap h1 scheduled_done_loc = false ⦄
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     ret (leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    (r ← resolve
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b)
      (scheduled_gen, ('list ('option tweak), batch_output shrincs_thf))
      (fixed_ud_requests s leaves) ;;
     ret (fixed_complete true s leaves r))
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\ J (h0, h1) /\
      get_heap h1 ud_rev_loc = true /\
      get_heap h1 scheduled_done_loc = true /\
      get_heap h1 (ud_tws_loc shrincs_thf) =
        pmap id (fixed_ud_requests s leaves) ⦄.
Proof.
move=> hsp hs hts hrev hdone hpin /=.
rewrite resolve_leaf_ud_gen bind_assoc.
cbn [bind].
set pre0 : precond := fun '(h0, h1) =>
  leaf_ud_frame J [::] (h0, h1) /\
  get_heap h1 scheduled_done_loc = false.
eapply (r_get_rhs_pin scheduled_done_loc false pre0);
  first by move=> h0 h1 [_ hd].
eapply (r_bind_assertD_rhs _ pre0); first by [].
move=> _.
eapply (r_bind_assertD_rhs _ pre0); first by [].
move=> _.
eapply (r_get_bind_rhs (ud_pp_loc shrincs_thf) (Some pp) pre0);
  first by move=> h0 h1 [[hj _] _]; apply: hpin hj.
cbn [bind].
rewrite (bind_assoc (batch_loop shrincs_thf
  (batch_ud_local shrincs_thf wots_c_hash_class (2 ^ 69) b pp)
  (fixed_ud_requests s (known_message_prepared shrincs_fxmss_sha256 sp pp sd)))).
rewrite -(known_message_prepared_budget shrincs_fxmss_sha256 sp pp sd).
eapply r_bind.
- rewrite /fixed_budget
    -(size_map (fun row => if s.+2 <= row.2
      then Some (fixed_tweak row s) else None)
      (fixed_rows (known_message_prepared shrincs_fxmss_sha256 sp pp sd))).
  eapply rpre_weaken_rule.
  + apply: (leaf_ud_loop_framed _ _ _ _ [::] J hts).
    * exact: fixed_ud_targets_class.
    * exact: leaf_ud_targets_uniq hsp (ltnW hs).
    * have [_ _ hc] := leaf_ud_domain shrincs_fxmss_sha256 sp pp sd s hsp hs.
      exact: hc.
  + by move=> h0 h1 [hp _].
- move=> xs ys.
  cbn [bind].
  eapply rpre_hypothesis_rule => h0 h1 [[hj [hr ht]] [hsize hy]].
  eapply (rpre_weaken_rule (fun '(s0, s1) => s0 = h0 /\ s1 = h1));
    last by move=> s0 s1 [].
  eapply (r_put_rhs ud_rev_loc true _ _
    (fun '(s0, s1) => s0 = h0 /\ s1 = h1)).
  eapply r_put_rhs.
  apply r_ret.
  move=> s0 s1 [s1' [[s1'' [[-> ->] ->]] ->]].
  split.
  + rewrite hy; clear hy.
    case: b.
    * rewrite leaf_ud_complete_real //.
      apply: leq_trans hs _; by [].
    * rewrite leaf_ud_complete_ideal //.
      by move: hsize; rewrite size_map.
  + split.
    * apply: hdone. exact: hrev hj.
    * split; first by rewrite get_set_heap_neq // get_set_heap_eq.
      split; first by rewrite get_set_heap_eq.
      by rewrite !get_set_heap_neq.
Qed.

Lemma leaf_ud_setup_sampling b s sp sd pp (J : precond) :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  (forall h0 h1 ts, J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts)) ->
  (forall h0 h1, J (h0, h1) -> J (h0, set_heap h1 ud_rev_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    J (h0, set_heap h1 scheduled_done_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  let leaves := known_message_prepared shrincs_fxmss_sha256 sp pp sd in
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) /\
      get_heap h1 scheduled_done_loc = false ⦄
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     ret (leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    code_link (leaf_ud_setup s sp sd)
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b)
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\ J (h0, h1) /\
      get_heap h1 ud_rev_loc = true /\
      get_heap h1 scheduled_done_loc = true /\
      get_heap h1 (ud_tws_loc shrincs_thf) =
        pmap id (fixed_ud_requests s leaves) ⦄.
Proof.
move=> hsp hs hts hrev hdone hpin.
cbv zeta.
rewrite /leaf_ud_setup code_link_bind.
eapply (leaf_grind_batch_ud (2 ^ 69) b sp sd pp
  (fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) /\
    get_heap h1 scheduled_done_loc = false)).
- by move=> h0 h1 [[hj _] _]; apply: hpin hj.
- cbn [code_link].
  exact: leaf_ud_scheduled_sampling hsp hs hts hrev hdone hpin.
Qed.

Definition leaf_ud_setup_locs :=
  [fmap ud_tws_loc shrincs_thf; ud_rev_loc; scheduled_done_loc].

Definition leaf_ud_setup_frame (pp : bytes 16) : precond :=
  fun '(h0, h1) => heap_ignore leaf_ud_setup_locs (h0, h1) /\
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp.

Lemma leaf_ud_setup_frame_targets pp h0 h1 ts :
  leaf_ud_setup_frame pp (h0, h1) ->
  leaf_ud_setup_frame pp
    (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts).
Proof.
move=> [hi hp]; split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; fmap_solve.
- by rewrite get_set_heap_neq.
Qed.

Lemma leaf_ud_setup_frame_reveal pp h0 h1 :
  leaf_ud_setup_frame pp (h0, h1) ->
  leaf_ud_setup_frame pp (h0, set_heap h1 ud_rev_loc true).
Proof.
move=> [hi hp]; split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; fmap_solve.
- by rewrite get_set_heap_neq.
Qed.

Lemma leaf_ud_setup_frame_done pp h0 h1 :
  leaf_ud_setup_frame pp (h0, h1) ->
  leaf_ud_setup_frame pp (h0, set_heap h1 scheduled_done_loc true).
Proof.
move=> [hi hp]; split.
- apply: heap_ignore_set_r hi.
  by apply: fhas_in; fmap_solve.
- by rewrite get_set_heap_neq.
Qed.

Lemma leaf_ud_setup_ready b s sp sd pp :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  let leaves := known_message_prepared shrincs_fxmss_sha256 sp pp sd in
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame (leaf_ud_setup_frame pp) [::] (h0, h1) /\
      get_heap h1 scheduled_done_loc = false ⦄
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     ret (leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    code_link (leaf_ud_setup s sp sd)
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b)
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\ leaf_ud_setup_frame pp (h0, h1) /\
      get_heap h1 ud_rev_loc = true /\
      get_heap h1 scheduled_done_loc = true /\
      get_heap h1 (ud_tws_loc shrincs_thf) =
        pmap id (fixed_ud_requests s leaves) ⦄.
Proof.
move=> hsp hs.
apply: leaf_ud_setup_sampling hsp hs _ _ _ _.
- exact: leaf_ud_setup_frame_targets.
- exact: leaf_ud_setup_frame_reveal.
- exact: leaf_ud_setup_frame_done.
- by move=> h0 h1 [_ hp].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf uniform guesses public *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope nat_scope.

Lemma leaf_ud_scheduled_public b s sp sd pp (J : precond) :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  (forall h0 h1 ts, J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts)) ->
  (forall h0 h1, J (h0, h1) -> J (h0, set_heap h1 ud_rev_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    J (h0, set_heap h1 scheduled_done_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  let leaves := known_message_prepared shrincs_fxmss_sha256 sp pp sd in
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) /\
      get_heap h1 scheduled_done_loc = false ⦄
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     ret (pp, leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    (r ← resolve
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b)
      (scheduled_gen, ('list ('option tweak), batch_output shrincs_thf))
      (fixed_ud_requests s leaves) ;;
     ret (r.1, fixed_complete true s leaves r))
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\ J (h0, h1) /\
      get_heap h1 ud_rev_loc = true /\
      get_heap h1 scheduled_done_loc = true /\
      get_heap h1 (ud_tws_loc shrincs_thf) =
        pmap id (fixed_ud_requests s leaves) ⦄.
Proof.
move=> hsp hs hts hrev hdone hpin /=.
rewrite resolve_leaf_ud_gen bind_assoc.
cbn [bind].
set pre0 : precond := fun '(h0, h1) =>
  leaf_ud_frame J [::] (h0, h1) /\
  get_heap h1 scheduled_done_loc = false.
eapply (r_get_rhs_pin scheduled_done_loc false pre0);
  first by move=> h0 h1 [_ hd].
eapply (r_bind_assertD_rhs _ pre0); first by [].
move=> _.
eapply (r_bind_assertD_rhs _ pre0); first by [].
move=> _.
eapply (r_get_bind_rhs (ud_pp_loc shrincs_thf) (Some pp) pre0);
  first by move=> h0 h1 [[hj _] _]; apply: hpin hj.
cbn [bind].
rewrite (bind_assoc (batch_loop shrincs_thf
  (batch_ud_local shrincs_thf wots_c_hash_class (2 ^ 69) b pp)
  (fixed_ud_requests s (known_message_prepared shrincs_fxmss_sha256 sp pp sd)))).
rewrite -(known_message_prepared_budget shrincs_fxmss_sha256 sp pp sd).
eapply r_bind.
- rewrite /fixed_budget
    -(size_map (fun row => if s.+2 <= row.2
      then Some (fixed_tweak row s) else None)
      (fixed_rows (known_message_prepared shrincs_fxmss_sha256 sp pp sd))).
  eapply rpre_weaken_rule.
  + apply: (leaf_ud_loop_framed _ _ _ _ [::] J hts).
    * exact: fixed_ud_targets_class.
    * exact: leaf_ud_targets_uniq hsp (ltnW hs).
    * have [_ _ hc] := leaf_ud_domain shrincs_fxmss_sha256 sp pp sd s hsp hs.
      exact: hc.
  + by move=> h0 h1 [hp _].
- move=> xs ys.
  cbn [bind].
  eapply rpre_hypothesis_rule => h0 h1 [[hj [hr ht]] [hsize hy]].
  eapply (rpre_weaken_rule (fun '(s0, s1) => s0 = h0 /\ s1 = h1));
    last by move=> s0 s1 [].
  eapply (r_put_rhs ud_rev_loc true _ _
    (fun '(s0, s1) => s0 = h0 /\ s1 = h1)).
  eapply r_put_rhs.
  apply r_ret.
  move=> s0 s1 [s1' [[s1'' [[-> ->] ->]] ->]].
  split.
  + congr (_, _).
    rewrite hy; clear hy.
    case: b.
    * rewrite leaf_ud_complete_real //.
      apply: leq_trans hs _; by [].
    * rewrite leaf_ud_complete_ideal //.
      by move: hsize; rewrite size_map.
  + split.
    * apply: hdone. exact: hrev hj.
    * split; first by rewrite get_set_heap_neq // get_set_heap_eq.
      split; first by rewrite get_set_heap_eq.
      by rewrite !get_set_heap_neq.
Qed.

Definition leaf_ud_public_setup s sp sd :
    raw_code (bytes 16 × 'list fixed_cache_entry) :=
  leaves ← leaf_grind_batch sp sd ;;
  r ← call [ scheduled_gen ] :
    { 'list ('option tweak) ~> batch_output shrincs_thf }
    (fixed_ud_requests s leaves) ;;
  ret (r.1, fixed_complete true s leaves r).

Lemma leaf_ud_public_sampling b s sp sd pp (J : precond) :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> s < 14 ->
  (forall h0 h1 ts, J (h0, h1) ->
    J (h0, set_heap h1 (ud_tws_loc shrincs_thf) ts)) ->
  (forall h0 h1, J (h0, h1) -> J (h0, set_heap h1 ud_rev_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    J (h0, set_heap h1 scheduled_done_loc true)) ->
  (forall h0 h1, J (h0, h1) ->
    get_heap h1 (ud_pp_loc shrincs_thf) = Some pp) ->
  let leaves := known_message_prepared shrincs_fxmss_sha256 sp pp sd in
  ⊢ ⦃ fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) /\
      get_heap h1 scheduled_done_loc = false ⦄
    (xs ← sample_seq (dBytes 16) (32 * size (shrincs_fxmss_schedule sp)) ;;
     ret (pp, leaf_ud_complete (if b then s else s.+1) leaves pp xs)) ≈
    code_link (leaf_ud_public_setup s sp sd)
      (G_scheduled_ud shrincs_thf wots_c_hash_class (2 ^ 69) known_message_pin b)
  ⦃ fun '(cache0, h0) '(cache1, h1) => cache0 = cache1 /\ J (h0, h1) /\
      get_heap h1 ud_rev_loc = true /\
      get_heap h1 scheduled_done_loc = true /\
      get_heap h1 (ud_tws_loc shrincs_thf) =
        pmap id (fixed_ud_requests s leaves) ⦄.
Proof.
move=> hsp hs hts hrev hdone hpin.
cbv zeta.
rewrite /leaf_ud_public_setup code_link_bind.
eapply (leaf_grind_batch_ud (2 ^ 69) b sp sd pp
  (fun '(h0, h1) => leaf_ud_frame J [::] (h0, h1) /\
    get_heap h1 scheduled_done_loc = false)).
- by move=> h0 h1 [[hj _] _]; apply: hpin hj.
- cbn [code_link].
  exact: leaf_ud_scheduled_public hsp hs hts hrev hdone hpin.
Qed.
