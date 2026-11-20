(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.known_message

    Restrict external evaluation to canonical type-18 tree inputs: full bounded
    coordinates and two sixteen-byte children. Sampling and cache invariants for
    all committed leaves. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.sample_seq toolkit.sample_seq_facts.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params games leaf.opening leaf.known_message_game shape leaf.commitments
    leaf.fixed_batch leaf.paths.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs.internal.ssprove.wots Require Import params scheme.

(* ------------------------------------------------------------------ *)
(** ** Leaf km filter *)

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition known_message_coll_allowed (q : leaf_opening_eval_input) : bool :=
  (q.1 == shrincs_fxmss_tree_tweak q.1.1.1.1.1) && (size q.2 == 32).

Definition known_message_pin : leaf_opening_eval_input :=
  (shrincs_fxmss_tree_tweak (uint U8 255, uint U64 0), zeros 16 ++ zeros 16).

Definition known_message_filter_request (q : leaf_opening_eval_input) :=
  if known_message_coll_allowed q then q else known_message_pin.

Definition known_message_filter_eval (q : leaf_opening_eval_input) : raw_code (bytes 16)
  :=
  y ← call [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 }
    (known_message_filter_request q) ;;
  ret (if known_message_coll_allowed q then y else zeros 16).

#[export] Instance known_message_filter_eval_valid q :
  ValidCode emptym I_known_message (known_message_filter_eval q).
Proof. rewrite /known_message_filter_eval; ssprove_valid. Qed.

Definition known_message_coll_filter : package I_known_message I_known_message :=
  [package emptym;
    [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table ~>
      leaf_opening_public }
      (q) {
      call [ known_message_gen ] : { shrincs_fxmss_structure ×
        shrincs_fxmss_digest_table ~>
        leaf_opening_public } q
    };
    [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } (j) {
      call [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } j
    };
    [ known_message_check ] : { leaf_opening_opening ~> 'bool } (q) {
      call [ known_message_check ] : { leaf_opening_opening ~> 'bool } q
    };
    [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 } (q) {
      known_message_filter_eval q
    }
  ].

Lemma resolve_known_message_filter_gen sp sd :
  resolve known_message_coll_filter
    (known_message_gen, (shrincs_fxmss_structure × shrincs_fxmss_digest_table,
      leaf_opening_public)) (sp, sd) =
    (call [ known_message_gen ] : { shrincs_fxmss_structure × shrincs_fxmss_digest_table
      ~> leaf_opening_public } (sp, sd)).
Proof. by rewrite /known_message_coll_filter /resolve /= coerce_kleisliE. Qed.

Lemma resolve_known_message_filter_sign j :
  resolve known_message_coll_filter
    (known_message_sign, ('nat, 'option leaf_opening_signature)) j =
    (call [ known_message_sign ] : { 'nat ~> 'option leaf_opening_signature } j).
Proof. by rewrite /known_message_coll_filter /resolve /= coerce_kleisliE. Qed.

Lemma resolve_known_message_filter_check q :
  resolve known_message_coll_filter
    (known_message_check, (leaf_opening_opening, 'bool)) q =
    (call [ known_message_check ] : { leaf_opening_opening ~> 'bool } q).
Proof. by rewrite /known_message_coll_filter /resolve /= coerce_kleisliE. Qed.

Lemma resolve_known_message_filter_eval q :
  resolve known_message_coll_filter
    (known_message_eval, (leaf_opening_eval_input, bytes 16)) q =
    known_message_filter_eval q.
Proof. by rewrite /known_message_coll_filter /resolve /= coerce_kleisliE. Qed.

Lemma known_message_coll_allowed_tree a (l r : bytes 16) :
  known_message_coll_allowed (shrincs_fxmss_tree_tweak a, l ++ r).
Proof. by rewrite /known_message_coll_allowed /= eqxx size_cat !size_tuple. Qed.

Lemma known_message_pin_allowed : known_message_coll_allowed known_message_pin.
Proof. exact: known_message_coll_allowed_tree. Qed.

Lemma known_message_coll_allowed_class q :
  known_message_coll_allowed q -> shrincs_fxmss_tree_class q.1.
Proof.
move=> /andP[/eqP -> _].
exact: shrincs_fxmss_tree_tweak_class.
Qed.

Lemma known_message_filter_request_allowed q : known_message_coll_allowed
  (known_message_filter_request q).
Proof.
rewrite /known_message_filter_request.
by case: ifP.
Qed.

Lemma known_message_filter_request_outside q :
  [&& ~~ wots_c_hash_class (known_message_filter_request q).1,
      ~~ wots_c_pk_class (known_message_filter_request q).1 &
      ~~ wots_c_grind_class (known_message_filter_request q).1].
Proof.
have /andP[/eqP he _] := known_message_filter_request_allowed q.
rewrite he.
by [].
Qed.

Lemma known_message_filter_tree a (l r : bytes 16) :
  known_message_filter_eval (shrincs_fxmss_tree_tweak a, l ++ r) =
    (call [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 }
      (shrincs_fxmss_tree_tweak a, l ++
      r)).
Proof.
by rewrite /known_message_filter_eval /known_message_filter_request
  known_message_coll_allowed_tree bind_ret.
Qed.

Lemma known_message_filter_refused q :
  ~~ known_message_coll_allowed q ->
  known_message_filter_eval q =
    (_ ← call [ known_message_eval ] : { leaf_opening_eval_input ~> bytes 16 }
      known_message_pin ;;
     ret (zeros 16)).
Proof.
by move=> /negbTE hq; rewrite /known_message_filter_eval /known_message_filter_request
  hq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf km gate *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition known_message_digits P (sp : shrincs_fxmss_structure) pp a md : seq nat :=
  match known_message_find P sp pp a md with
  | Some c => digest_of (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) pp md c
  | None => nseq 32 15
  end.

Definition known_message_prepared_leaf P (sp : shrincs_fxmss_structure) pp a md :
  fixed_leaf :=
  (a, omap (fun c =>
    (c, digest_of (shrincs_fxmss_leaf_params P a sp.1 (uint U8 sp.2)) pp md c))
    (known_message_find P sp pp a md)).

Definition known_message_prepared P sp pp sd : seq fixed_leaf :=
  [seq known_message_prepared_leaf P sp pp a (leaf_committed_digest sd a)
    | a <- shrincs_fxmss_schedule sp].

Lemma known_message_gate_failed P sp pp a md dd :
  known_message_find P sp pp a md = None -> known_message_gate P sp pp a md dd.
Proof. by move=> hf; rewrite /known_message_gate hf. Qed.

Lemma known_message_gate_same_digest P sp pp a md c :
  known_message_find P sp pp a md = Some c -> known_message_gate P sp pp a md md =
    false.
Proof. by move=> hf; rewrite /known_message_gate hf /= eqxx. Qed.

Lemma known_message_gate_fresh_pair P sp pp a md dd c k :
  known_message_find P sp pp a md = Some c -> known_message_gate P sp pp a md dd ->
  (dd, k) != (md, c).
Proof.
move=> hf.
rewrite /known_message_gate hf /= => hne.
by apply/eqP=> -[he _]; move: hne; rewrite he eqxx.
Qed.

Lemma known_message_digest_in_codomain sd a :
  isSome (getm sd a) -> leaf_committed_digest sd a \in codomm sd.
Proof.
rewrite /leaf_committed_digest.
case he: (getm sd a) => [md|] // _.
apply/codommP.
by exists a.
Qed.

(** The experiment logs all attempts. A fresh message's recorded randomizer is absent;
    the preassigned-game veto then forces its digest out of the entire table. *)
Lemma known_message_gate_discharge P sp pp a sd
    (rt : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16)) bm r dd :
  isSome (getm sd a) -> getm rt (a, bm) != Some r ->
  ~~ ((dd \in codomm sd) && (getm rt (a, bm) != Some r)) ->
  known_message_gate P sp pp a (leaf_committed_digest sd a) dd.
Proof.
move=> hsd hrt.
rewrite hrt andbT => hdd.
have hne : dd != leaf_committed_digest sd a.
  apply/eqP=> he.
  by move: hdd; rewrite he (known_message_digest_in_codomain sd a hsd).
by rewrite /known_message_gate hne orbT.
Qed.

Lemma known_message_digits_length P sp pp a md : size (known_message_digits P sp pp a
  md) = 32.
Proof.
rewrite /known_message_digits.
case: known_message_find => [c|]; last by rewrite size_nseq.
exact: size_digest_of.
Qed.

Lemma known_message_prepared_digits P sp pp a md :
  fixed_digits (known_message_prepared_leaf P sp pp a md) = known_message_digits P sp pp
    a md.
Proof. by rewrite /fixed_digits /known_message_prepared_leaf /known_message_digits;
  case: known_message_find. Qed.

Lemma known_message_prepared_coordinates P sp pp sd :
  [seq leaf.1 | leaf <- known_message_prepared P sp pp sd] = shrincs_fxmss_schedule sp.
Proof. by rewrite /known_message_prepared -map_comp /= map_id. Qed.

Lemma known_message_prepared_budget P sp pp sd :
  fixed_budget (known_message_prepared P sp pp sd) = (32 * size (shrincs_fxmss_schedule
    sp))%nat.
Proof.
rewrite fixed_budget_length.
- apply/allP=> leaf /mapP[a ha ->].
  by rewrite known_message_prepared_digits known_message_digits_length.
- by rewrite /known_message_prepared size_map.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf km invariants *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition known_message_keys_total (as_ : seq shrincs_fxmss_coord) (kt :
  shrincs_fxmss_key_table)
  :=
  all (fun a =>
    if getm kt a is Some xs then size xs == wots_c_chain_count else false) as_.

Lemma known_message_keys_total_set as_ kt a xs :
  known_message_keys_total as_ kt -> size xs = wots_c_chain_count ->
  known_message_keys_total (a :: as_) (setm kt a xs).
Proof.
move=> hkt hxs.
rewrite /known_message_keys_total /= setmE eqxx hxs eqxx /=.
apply/allP=> a' ha'.
rewrite setmE.
case: ifP => _; first by rewrite hxs eqxx.
exact: (allP hkt a' ha').
Qed.

Lemma known_message_keys_total_lookup as_ kt a :
  known_message_keys_total as_ kt -> a \in as_ ->
  size (odflt [::] (getm kt a)) = wots_c_chain_count.
Proof.
move=> hkt ha.
have := allP hkt a ha.
case: getm => [xs|] //= /eqP.
by [].
Qed.

Lemma known_message_sample_keys_congr (P : shrincs_fxmss_params) (as_ : seq
  shrincs_fxmss_coord)
    (A : choice_type) (k0 k1 : shrincs_fxmss_key_table -> raw_code A) :
  (forall kt, known_message_keys_total as_ kt -> k0 kt = k1 kt) ->
  (kt ← shrincs_fxmss_sample_keys P as_ ;; k0 kt) =
  (kt ← shrincs_fxmss_sample_keys P as_ ;; k1 kt).
Proof.
elim: as_ k0 k1 => [|a as_ ih] k0 k1 hk.
- exact: hk isT.
- (* The head key block preserves totality for the full schedule. *)
  cbn [shrincs_fxmss_sample_keys].
  rewrite bind_assoc [RHS]bind_assoc.
  apply: sample_seq_congr => xs hxs.
  rewrite bind_assoc [RHS]bind_assoc.
  apply: ih => kt hkt.
  apply: hk.
  exact: known_message_keys_total_set hkt hxs.
Qed.

Lemma known_message_sample_keys_total P as_ :
  (kt ← shrincs_fxmss_sample_keys P as_ ;; ret (kt, known_message_keys_total as_ kt)) =
  (kt ← shrincs_fxmss_sample_keys P as_ ;; ret (kt, true)).
Proof.
apply: known_message_sample_keys_congr.
by move=> kt ->.
Qed.

Lemma known_message_sample_tables_total P as_ :
  (kt ← shrincs_fxmss_sample_keys P as_ ;;
   sd ← shrincs_fxmss_sample_digests P as_ ;;
   ret (kt, sd, known_message_keys_total as_ kt && leaf_digest_total as_ sd)) =
  (kt ← shrincs_fxmss_sample_keys P as_ ;;
   sd ← shrincs_fxmss_sample_digests P as_ ;;
   ret (kt, sd, true)).
Proof.
apply: known_message_sample_keys_congr => kt hkt.
apply: leaf_sample_digests_congr => sd hsd.
by rewrite hkt hsd.
Qed.

Lemma known_message_cache_lookup P sp pp sd kt a :
  shrincs_fxmss_structure_legal sp.1 sp.2 -> a \in shrincs_fxmss_schedule sp ->
  nth None (known_message_cache P sp pp sd kt) (leaf_slot sp a) =
    leaf_sign_at P sp pp a (odflt [::] (getm kt a))
      (leaf_committed_digest sd a).
Proof.
move=> hsp ha.
have [hq he] := leaf_schedule_slot sp a hsp ha.
by rewrite (known_message_cache_nth P sp pp sd kt _ hsp hq) he.
Qed.

Lemma known_message_cache_commitment P sp pp sd kt q a :
  leaf_digest_total (shrincs_fxmss_schedule sp) sd ->
  shrincs_fxmss_select_leaf sp.1 sp.2 q = Some a ->
  (md ← leaf_digest_lookup P sd a ;;
   ret (leaf_sign_at P sp pp a (odflt [::] (getm kt a)) md)) =
  ret (nth None (known_message_cache P sp pp sd kt) q).
Proof.
move=> hsd hs.
have [hsp hq] := shrincs_fxmss_select_leaf_some _ _ _ _ hs.
rewrite (leaf_digest_lookup_committed P sp sd q a hsd hs) /=.
rewrite (known_message_cache_nth P sp pp sd kt q hsp hq).
rewrite (leaf_select_eq sp q hsp hq) in hs.
by case: hs => ->.
Qed.

Lemma known_message_gen_digest_guard P sp (A : choice_type)
    (k : shrincs_fxmss_digest_table -> raw_code A) :
  (sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule sp) ;;
   #assert leaf_digest_total (shrincs_fxmss_schedule sp) sd ;; k sd) =
  (sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule sp) ;; k sd).
Proof.
apply: leaf_sample_digests_congr.
by move=> sd hsd; rewrite hsd.
Qed.

Lemma known_message_population_gate P sp pp a sd rt lg cm r dd :
  known_message_log_consistent rt lg -> shrincs_fxmss_message_valid cm -> cm \notin lg
    ->
  isSome (getm sd a) ->
  ~~ ((dd \in codomm sd) &&
       (getm rt (a, shrincs_fxmss_bound_message cm) != Some r)) ->
  known_message_gate P sp pp a (leaf_committed_digest sd a) dd.
Proof.
move=> hlog hcm hnot hsd hveto.
apply: (known_message_gate_discharge P sp pp a sd rt
  (shrincs_fxmss_bound_message cm) r dd hsd) => //.
exact: known_message_log_fresh hlog hcm hnot.
Qed.
