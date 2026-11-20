(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.fixed_batch

    Fixed-digit, arbitrary-list core of the FXMSS UD and PRE schedules.
    Leaves carry full byte-level anchors and optional counters/digits.
    Failed slots use virtual all-max digits and retain None in the signing
    cache. The static type-16 games supply all challenged chain nodes;
    chain completion and type-17 compression happen after the one reveal.
    This core exposes the list of leaf roots. Legal-shape Merkle assembly,
    grinding, Hmsg_sf and forgery classification belong to its callers. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core chain.ud games.static_batch games.static_pre_batch
  toolkit.batch_map.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove Require Import hash.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition fixed_leaf : choice_type :=
  ('word U8 × 'word U64) × 'option ('nat × 'list ('nat)).
Definition fixed_row : choice_type := (('word U8 × 'word U64) × 'nat) × 'nat.
Definition fixed_signature : choice_type := 'nat × 'list (bytes 16).
Definition fixed_cache_entry : choice_type := bytes 16 × 'option fixed_signature.
Definition fixed_public : choice_type := bytes 16 × 'list (bytes 16).

Definition fixed_digits (leaf : fixed_leaf) : seq nat :=
  if leaf.2 is Some cd then cd.2 else nseq 32 15.

Definition fixed_rows (leaves : seq fixed_leaf) : seq fixed_row :=
  flatten [seq [seq (leaf.1.1, leaf.1.2, jd.1, jd.2)
                | jd <- zip (iota 0 (size (fixed_digits leaf)))
                            (fixed_digits leaf)]
           | leaf <- leaves].

Definition fixed_tweak (row : fixed_row) (k : nat) : tweak :=
  tweak_of (WotsCHash row.1.1.1 row.1.1.2
    (uint U32 row.1.2) (uint U32 k)).

Definition fixed_F (leaves : seq fixed_leaf)
    (pp : bytes 16) (i k : nat) (x : bytes 16) : bytes 16 :=
  Th pp (fixed_tweak
    (nth (uint U8 0, uint U64 0, 0, 0) (fixed_rows leaves) i) k) x.

Definition fixed_ud_requests s leaves :=
  [seq if s.+2 <= row.2 then Some (fixed_tweak row s) else None
   | row <- fixed_rows leaves].
Definition fixed_pre_requests leaves :=
  [seq if row.2 is d.+1 then Some (fixed_tweak row d) else None
   | row <- fixed_rows leaves].

(** The initial EVAL pins the public seed outside type 16. *)
Definition fixed_pin : tweak * seq UInt8 :=
  (tweak_of (WotsCGrind (uint U8 0) (uint U64 0)), [::]).

Definition fixed_flat_digits leaves := [seq row.2 | row <- fixed_rows leaves].

Definition fixed_signatures ud s leaves pp ys : seq (bytes 16) :=
  if ud then
    rud_sig (bytes 16) (bytes 16) 16 (fixed_F leaves)
      pp s 0 (fixed_flat_digits leaves) ys
  else ys.

Fixpoint fixed_cache (pp : bytes 16) (leaves : seq fixed_leaf)
    (sigs ends : seq (bytes 16)) : seq fixed_cache_entry :=
  match leaves with
  | [::] => [::]
  | leaf :: leaves' =>
      let n := size (fixed_digits leaf) in
      let pk := Th pp (tweak_of (WotsCPk leaf.1.1 leaf.1.2))
        (flatten [seq tval x | x <- take n ends]) in
      let sg := omap (fun cd => (cd.1, take n sigs)) leaf.2 in
      (pk, sg) :: fixed_cache pp leaves' (drop n sigs) (drop n ends)
  end.

Definition fixed_complete ud s leaves (r : batch_output shrincs_thf) :=
  let sigs := fixed_signatures ud s leaves r.1 r.2 in
  let ends := ends_from_sig (bytes 16) (bytes 16)
    (size (fixed_rows leaves)) 16 (fixed_F leaves)
    r.1 (fixed_flat_digits leaves) sigs in
  fixed_cache r.1 leaves sigs ends.

Definition fixed_gen : nat := 1110.
Definition fixed_sign : nat := 1111.
Definition fixed_check : nat := 1112.
Definition fixed_cache_loc :=
  mkloc 1110 (None : option (seq (option fixed_signature))).
Definition fixed_slot_loc := mkloc 1111 0.

Definition I_fixed_ud :=
  [interface
    [ fixed_gen ] : { 'unit ~> fixed_public };
    [ fixed_sign ] : { 'unit ~> 'option fixed_signature }
  ].
Definition I_fixed_pre :=
  [interface
    [ fixed_gen ] : { 'unit ~> fixed_public };
    [ fixed_sign ] : { 'unit ~> 'option fixed_signature };
    [ fixed_check ] : { 'nat × 'list ('word U8) ~> 'bool }
  ].

Definition C_fixed_ud (s : nat) (leaves : seq fixed_leaf) :
    package (I_batch_ud shrincs_thf) I_fixed_ud :=
  [package [fmap fixed_cache_loc; fixed_slot_loc];
    [ fixed_gen ] : { 'unit ~> fixed_public } (_) {
      r ← call [ batch_gen ] : { 'unit ~> batch_output shrincs_thf } tt ;;
      let cache := fixed_complete true s leaves r in
      #put fixed_cache_loc := Some [seq entry.2 | entry <- cache] ;;
      ret (r.1, [seq entry.1 | entry <- cache])
    };
    [ fixed_sign ] : { 'unit ~> 'option fixed_signature } (_) {
      cache ← getSome fixed_cache_loc ;;
      i ← get fixed_slot_loc ;;
      #put fixed_slot_loc := i.+1 ;;
      ret (nth None cache i)
    }
  ].

Definition C_fixed_pre (leaves : seq fixed_leaf) :
    package (I_batch_pre shrincs_thf) I_fixed_pre :=
  [package [fmap fixed_cache_loc; fixed_slot_loc];
    [ fixed_gen ] : { 'unit ~> fixed_public } (_) {
      r ← call [ batch_gen ] : { 'unit ~> batch_output shrincs_thf } tt ;;
      let cache := fixed_complete false 0 leaves r in
      #put fixed_cache_loc := Some [seq entry.2 | entry <- cache] ;;
      ret (r.1, [seq entry.1 | entry <- cache])
    };
    [ fixed_sign ] : { 'unit ~> 'option fixed_signature } (_) {
      cache ← getSome fixed_cache_loc ;;
      i ← get fixed_slot_loc ;;
      #put fixed_slot_loc := i.+1 ;;
      ret (nth None cache i)
    };
    [ fixed_check ] : { 'nat × 'list ('word U8) ~> 'bool } (q) {
      call [ batch_check ] : { 'nat × 'list ('word U8) ~> 'bool } q
    }
  ].

Definition fixed_budget (leaves : seq fixed_leaf) := size (fixed_rows leaves).
Definition R_fixed_ud s leaves :=
  C_fixed_ud s leaves ∘ R_batch_ud shrincs_thf fixed_pin
    (fixed_ud_requests s leaves).
Definition G_fixed_ud s leaves b :=
  C_fixed_ud s leaves ∘ G_batch_ud shrincs_thf wots_c_hash_class
    (fixed_budget leaves) fixed_pin (fixed_ud_requests s leaves) b.
Definition R_fixed_pre leaves :=
  C_fixed_pre leaves ∘ R_batch_pre shrincs_thf fixed_pin
    (fixed_pre_requests leaves).
Definition G_fixed_pre leaves b :=
  C_fixed_pre leaves ∘ G_batch_pre shrincs_thf wots_c_hash_class
    (fixed_budget leaves) fixed_pin (fixed_pre_requests leaves) b.

Lemma R_fixed_ud_perfect s leaves b :
  perfect I_fixed_ud (G_fixed_ud s leaves b)
    (R_fixed_ud s leaves ∘
      SMUD_game shrincs_thf wots_c_hash_class (fixed_budget leaves) b).
Proof.
rewrite /G_fixed_ud /R_fixed_ud -sep_link_assoc.
apply batch_context_perfect.
exact: R_batch_ud_perfect.
Qed.

Lemma fixed_query_hash leaves pp i k x :
  k < 16 ->
  Fc (bytes 16) (bytes 16) 16 (fixed_F leaves) pp (i, k) x =
  Th pp (fixed_tweak
    (nth (uint U8 0, uint U64 0, 0, 0) (fixed_rows leaves) i) k) x.
Proof. exact: FcE. Qed.

Lemma fixed_budget_length leaves :
  all (fun leaf => size (fixed_digits leaf) == 32) leaves ->
  fixed_budget leaves = (32 * size leaves)%nat.
Proof.
rewrite /fixed_budget /fixed_rows.
elim: leaves => [|leaf leaves ih] //= /andP [/eqP hsize hall].
rewrite size_cat size_map size_zip size_iota minnn hsize (ih hall).
by rewrite mulnS.
Qed.

Lemma R_fixed_pre_perfect leaves b :
  perfect I_fixed_pre (G_fixed_pre leaves b)
    (R_fixed_pre leaves ∘
      SMPRE_game shrincs_thf wots_c_hash_class (fixed_budget leaves) b).
Proof.
rewrite /G_fixed_pre /R_fixed_pre -sep_link_assoc.
apply batch_context_perfect.
exact: R_batch_pre_perfect.
Qed.

Lemma R_fixed_ud_real s leaves :
  perfect I_fixed_ud (G_fixed_ud s leaves true)
    (R_fixed_ud s leaves ∘
      SMUD_game shrincs_thf wots_c_hash_class (fixed_budget leaves) true).
Proof. exact: R_fixed_ud_perfect. Qed.

Lemma R_fixed_ud_ideal s leaves :
  perfect I_fixed_ud (G_fixed_ud s leaves false)
    (R_fixed_ud s leaves ∘
      SMUD_game shrincs_thf wots_c_hash_class (fixed_budget leaves) false).
Proof. exact: R_fixed_ud_perfect. Qed.

Lemma fixed_ud_advantage s leaves (A : adversary I_fixed_ud) :
  Adv (G_fixed_ud s leaves true) (G_fixed_ud s leaves false) A =
  AdvOf (SMUD_game shrincs_thf wots_c_hash_class (fixed_budget leaves))
    (A ∘ R_fixed_ud s leaves).
Proof.
rewrite (Adv_perfect_l (R_fixed_ud_real s leaves)).
rewrite (Adv_perfect_r (R_fixed_ud_ideal s leaves)).
exact: Adv_reduction.
Qed.

Lemma R_fixed_pre_real leaves :
  perfect I_fixed_pre (G_fixed_pre leaves true)
    (R_fixed_pre leaves ∘
      SMPRE_game shrincs_thf wots_c_hash_class (fixed_budget leaves) true).
Proof. exact: R_fixed_pre_perfect. Qed.

Lemma R_fixed_pre_ideal leaves :
  perfect I_fixed_pre (G_fixed_pre leaves false)
    (R_fixed_pre leaves ∘
      SMPRE_game shrincs_thf wots_c_hash_class (fixed_budget leaves) false).
Proof. exact: R_fixed_pre_perfect. Qed.

Lemma fixed_pre_advantage leaves (A : adversary I_fixed_pre) :
  Adv (G_fixed_pre leaves true) (G_fixed_pre leaves false) A =
  AdvOf (SMPRE_game shrincs_thf wots_c_hash_class (fixed_budget leaves))
    (A ∘ R_fixed_pre leaves).
Proof.
rewrite (Adv_perfect_l (R_fixed_pre_real leaves)).
rewrite (Adv_perfect_r (R_fixed_pre_ideal leaves)).
exact: Adv_reduction.
Qed.

(** The real and ideal answer maps give adjacent root positions. *)
Lemma fixed_ud_real_roots s leaves pp xs :
  fixed_signatures true s leaves pp
    (uq_real_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
      pp s 0 (fixed_flat_digits leaves) xs) =
  roots_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp s 0 (fixed_flat_digits leaves) xs.
Proof. exact: rud_sig_real. Qed.

Lemma fixed_ud_ideal_roots s leaves pp xs :
  fixed_signatures true s leaves pp xs =
  roots_map (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp s.+1 0 (fixed_flat_digits leaves) xs.
Proof. exact: rud_sig_ideal. Qed.

Lemma fixed_tweak_class row k : wots_c_hash_class (fixed_tweak row k).
Proof. by []. Qed.

Lemma fixed_pin_outside : ~~ wots_c_hash_class fixed_pin.1.
Proof. by []. Qed.

Lemma fixed_cache_none pp h i leaves sigs ends :
  ohead [seq entry.2 | entry <-
    fixed_cache pp ((h, i, None) :: leaves) sigs ends] = Some None.
Proof. by []. Qed.

Lemma fixed_cache_length pp leaves sigs ends :
  size (fixed_cache pp leaves sigs ends) = size leaves.
Proof.
by elim: leaves sigs ends => [|leaf leaves ih] sigs ends //=; rewrite ih.
Qed.

Lemma fixed_ud_target_budget s leaves :
  count isSome (fixed_ud_requests s leaves) <= fixed_budget leaves.
Proof.
rewrite /fixed_budget -(size_map
  (fun row => if s.+2 <= row.2 then Some (fixed_tweak row s) else None)).
exact: count_size.
Qed.

Lemma fixed_pre_target_budget leaves :
  count isSome (fixed_pre_requests leaves) <= fixed_budget leaves.
Proof.
rewrite /fixed_budget -(size_map
  (fun row => if row.2 is d.+1 then Some (fixed_tweak row d) else None)).
exact: count_size.
Qed.

Definition fixed_example : seq fixed_leaf :=
  [:: (uint U8 0, uint U64 0, Some (3, nseq 16 15 ++ nseq 16 0));
      (uint U8 0, uint U64 1, None);
      (uint U8 0, uint U64 2, Some (7, nseq 16 14 ++ nseq 16 1))].

Lemma fixed_example_data :
  [&& fixed_budget fixed_example == 96,
      count isSome (fixed_ud_requests 2 fixed_example) == 64,
      count isSome (fixed_pre_requests fixed_example) == 80,
      uniq (pmap id (fixed_ud_requests 2 fixed_example)) &
      uniq (pmap id (fixed_pre_requests fixed_example))].
Proof. auto with real arith. Qed.

(** A list can include failed slots on either game bit. *)
Lemma fixed_example_simulations :
  (forall b, perfect I_fixed_ud (G_fixed_ud 2 fixed_example b)
    (R_fixed_ud 2 fixed_example ∘
      SMUD_game shrincs_thf wots_c_hash_class 96 b)) /\
  (forall b, perfect I_fixed_pre (G_fixed_pre fixed_example b)
    (R_fixed_pre fixed_example ∘
      SMPRE_game shrincs_thf wots_c_hash_class 96 b)).
Proof.
split=> b.
- exact: R_fixed_ud_perfect.
- exact: R_fixed_pre_perfect.
Qed.

(** Per-leaf chain completion and compression can be deferred across
    later query blocks when all leaf descriptors have already been fixed. *)
Lemma fixed_completion_batch ud s pp
    (query : fixed_leaf -> raw_code (chList (bytes 16))) leaves :
  eager_map query
    (fun leaf ys => fixed_complete ud s [:: leaf] (pp, ys)) leaves =
  (rs ← query_list query leaves ;;
   ret [seq fixed_complete ud s [:: lr.1] (pp, lr.2)
        | lr <- zip leaves rs]).
Proof. exact: eager_map_batch. Qed.

Lemma fixed_example_digits :
  all (fun leaf =>
    [&& size (fixed_digits leaf) == 32,
        all (fun d => d < 16) (fixed_digits leaf) &
        if leaf.2 is Some cd then sumn cd.2 == 240 else true])
    fixed_example.
Proof. auto with real arith. Qed.
