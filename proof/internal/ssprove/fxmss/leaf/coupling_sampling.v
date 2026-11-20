(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.leaf.coupling_sampling

    Single-leaf sampling, signature-cache rows and returned values support both
    prepared-leaf endpoint couplings. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude chain.core chain.ud chain.roots_sampling toolkit.sample_seq
  toolkit.sample_seq_facts toolkit.byte_sampling toolkit.batch_map
  toolkit.relational_rules.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.wots Require Import params scheme games.
From Shrincs.internal.ssprove.fxmss Require Import
  params instance leaf.fixed_batch leaf.known_message_game leaf.known_message
    leaf.uniform_sampling
  leaf.prepared leaf.opening scheme leaf.compress.pure leaf.compress.sampling games
  leaf.commitments leaf.batch leaf.uniform leaf.context leaf.paths shape.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

(* ------------------------------------------------------------------ *)
(** ** Leaf coupling rows *)

Definition leaf_rows_walk pp (row : fixed_row) x k n :=
  chainc (bytes 16) (bytes 16) 16
    (fun pp _ k x => Th pp (fixed_tweak row k) x) pp 0 x k n.

Fixpoint leaf_rows_sigs s pp (rows : seq fixed_row) (xs : seq (bytes 16)) :=
  match rows, xs with
  | row :: rows', x :: xs' =>
      leaf_rows_walk pp row x (minn s row.2.-1) (row.2 - minn s row.2.-1) ::
        leaf_rows_sigs s pp rows' xs'
  | _, _ => [::]
  end.

Fixpoint leaf_rows_ends pp (rows : seq fixed_row) (xs : seq (bytes 16)) :=
  match rows, xs with
  | row :: rows', x :: xs' =>
      leaf_rows_walk pp row x row.2 (15 - row.2) :: leaf_rows_ends pp rows' xs'
  | _, _ => [::]
  end.

Local Opaque Th wots_c_counter_max.

Lemma leaf_rows_walk_fixed leaves pp i row x k n :
  nth (uint U8 0, uint U64 0, 0, 0) (fixed_rows leaves) i = row ->
  chainc (bytes 16) (bytes 16) 16 (fixed_F leaves) pp i x k n =
    leaf_rows_walk pp row x k n.
Proof.
move=> hr.
rewrite /leaf_rows_walk.
elim: n x k => [|n ih] x k //=.
rewrite ih /Fc /fixed_F hr /=.
by case: (Bool.bool_dec (k < 16) true).
Qed.

Lemma leaf_rows_sigs_rows leaves pp s i rows xs :
  (forall j, j < size rows ->
    nth (uint U8 0, uint U64 0, 0, 0) (fixed_rows leaves) (i + j) =
    nth (uint U8 0, uint U64 0, 0, 0) rows j) ->
  roots_map (bytes 16) (bytes 16) 16 (fixed_F leaves) pp s i
    [seq row.2 | row <- rows] xs = leaf_rows_sigs s pp rows xs.
Proof.
elim: rows xs i => [|row rows ih] [|x xs] i //= hr.
congr (_ :: _).
- apply: leaf_rows_walk_fixed.
  by have := hr 0 (ltn0Sn _); rewrite addn0.
- apply: ih => j hj.
  have := hr j.+1 hj.
  by rewrite addSn -addnS.
Qed.

Lemma leaf_rows_ends_rows leaves pp i rows xs :
  (forall j, j < size rows ->
    nth (uint U8 0, uint U64 0, 0, 0) (fixed_rows leaves) (i + j) =
    nth (uint U8 0, uint U64 0, 0, 0) rows j) ->
  [seq chainc (bytes 16) (bytes 16) 16 (fixed_F leaves)
    pp q.1 q.2.2 q.2.1 (15 - q.2.1)
    | q <- zip (iota i (size rows)) (zip [seq row.2 | row <- rows] xs)] =
    leaf_rows_ends pp rows xs.
Proof.
elim: rows xs i => [|row rows ih] [|x xs] i //= hr.
congr (_ :: _).
- apply: leaf_rows_walk_fixed.
  by have := hr 0 (ltn0Sn _); rewrite addn0.
- apply: ih => j hj.
  have := hr j.+1 hj.
  by rewrite addSn -addnS.
Qed.

Lemma leaf_rows_complete_rows s leaves pp xs :
  leaf_ud_complete s leaves pp xs =
  let sigs := leaf_rows_sigs s pp (fixed_rows leaves) xs in
  fixed_cache pp leaves sigs (leaf_rows_ends pp (fixed_rows leaves) sigs).
Proof.
rewrite /leaf_ud_complete /fixed_flat_digits leaf_rows_sigs_rows.
- by move=> j hj; rewrite add0n.
- by rewrite /ends_from_sig leaf_rows_ends_rows.
Qed.

Lemma leaf_rows_sigs_size s pp rows xs :
  size xs = size rows -> size (leaf_rows_sigs s pp rows xs) = size rows.
Proof.
by elim: rows xs => [|r rows ih] [|x xs] //= [he]; rewrite ih.
Qed.

Lemma leaf_rows_ends_size pp rows xs :
  size xs = size rows -> size (leaf_rows_ends pp rows xs) = size rows.
Proof.
by elim: rows xs => [|r rows ih] [|x xs] //= [he]; rewrite ih.
Qed.

Lemma leaf_rows_sigs_cat s pp rows rows' xs ys :
  size xs = size rows ->
  leaf_rows_sigs s pp (rows ++ rows') (xs ++ ys) =
    leaf_rows_sigs s pp rows xs ++ leaf_rows_sigs s pp rows' ys.
Proof.
by elim: rows xs => [|r rows ih] [|x xs] //= [he]; rewrite ih.
Qed.

Lemma leaf_rows_ends_cat pp rows rows' xs ys :
  size xs = size rows ->
  leaf_rows_ends pp (rows ++ rows') (xs ++ ys) =
    leaf_rows_ends pp rows xs ++ leaf_rows_ends pp rows' ys.
Proof.
by elim: rows xs => [|r rows ih] [|x xs] //= [he]; rewrite ih.
Qed.

Lemma leaf_rows_rows_cat leaves leaves' :
  fixed_rows (leaves ++ leaves') = fixed_rows leaves ++ fixed_rows leaves'.
Proof. by rewrite /fixed_rows map_cat flatten_cat. Qed.

Lemma leaf_rows_rows_one_size leaf :
  size (fixed_rows [:: leaf]) = size (fixed_digits leaf).
Proof. by rewrite /fixed_rows /= cats0 size_map size_zip size_iota minnn. Qed.

Lemma leaf_rows_complete_cons s pp leaf leaves xs ys :
  size xs = size (fixed_digits leaf) ->
  leaf_ud_complete s (leaf :: leaves) pp (xs ++ ys) =
    leaf_ud_complete s [:: leaf] pp xs ++ leaf_ud_complete s leaves pp ys.
Proof.
move=> hx.
have hx' : size xs = size (fixed_rows [:: leaf]) by rewrite leaf_rows_rows_one_size.
have hs := leaf_rows_sigs_size s pp _ _ hx'.
have he := leaf_rows_ends_size pp _ _ hs.
rewrite !leaf_rows_complete_rows.
rewrite -[leaf :: leaves]/([:: leaf] ++ leaves) leaf_rows_rows_cat.
rewrite (leaf_rows_sigs_cat s pp _ _ _ _ hx').
cbv zeta.
rewrite (leaf_rows_ends_cat pp _ _ _ _ hs).
cbn [fixed_cache cat].
rewrite leaf_rows_rows_one_size in hs he.
rewrite !take_cat !drop_cat hs he !ltnn !subnn !take0 !drop0 !cats0.
rewrite -{1}he take_size -hs take_size.
by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf coupling single *)

Definition leaf_sampling_rows (a : shrincs_fxmss_coord) i ds : seq fixed_row :=
  [seq (a.1, a.2, jd.1, jd.2) | jd <- zip (iota i (size ds)) ds].

Local Opaque Th wots_c_counter_max known_message_find.

Lemma leaf_sampling_walk sp pp a i d x k n :
  leaf_rows_walk pp (a.1, a.2, i, d) x k n =
    chainc (bytes 16) (bytes 16) 16
      (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2))) pp i x
        k n.
Proof.
rewrite /leaf_rows_walk.
by elim: n x k => [|n ih] x k //=.
Qed.

Lemma leaf_sampling_sigs sp pp a s i ds xs :
  leaf_rows_sigs s pp (leaf_sampling_rows a i ds) xs =
    roots_map (bytes 16) (bytes 16) 16
      (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2))) pp s i
        ds xs.
Proof.
elim: ds xs i => [|d ds ih] [|x xs] i //=.
rewrite /leaf_sampling_rows /= -/leaf_sampling_rows /=.
by rewrite (leaf_sampling_walk sp) ih.
Qed.

Lemma leaf_sampling_ends sp pp a i ds xs :
  leaf_rows_ends pp (leaf_sampling_rows a i ds) xs =
    [seq chainc (bytes 16) (bytes 16) 16
      (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)))
      pp q.1 q.2.2 q.2.1 (15 - q.2.1)
      | q <- zip (iota i (size ds)) (zip ds xs)].
Proof.
elim: ds xs i => [|d ds ih] [|x xs] i //=.
rewrite /leaf_sampling_rows /= -/leaf_sampling_rows /=.
by rewrite (leaf_sampling_walk sp) ih.
Qed.

Lemma leaf_sampling_prepared_rows sp pp a md :
  fixed_rows [:: known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a md] =
    leaf_sampling_rows a 0 (known_message_digits shrincs_fxmss_sha256 sp pp a md).
Proof.
by rewrite /fixed_rows /= cats0 known_message_prepared_digits /leaf_sampling_rows.
Qed.

Definition leaf_sampling_entry s sp pp a md xs : fixed_cache_entry :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let ds := known_message_digits shrincs_fxmss_sha256 sp pp a md in
  let sg := roots_map (bytes 16) (bytes 16) 16 (Fw W) pp s 0 ds xs in
  (Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode (complete_ends W pp ds sg)),
    omap (fun c => (c, sg)) (known_message_find shrincs_fxmss_sha256 sp pp a md)).

Lemma leaf_sampling_complete_one s sp pp a md xs :
  size xs = 32 ->
  leaf_ud_complete s [:: known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a md] pp
    xs =
    [:: leaf_sampling_entry s sp pp a md xs].
Proof.
move=> hx.
have hr : size (fixed_rows [:: known_message_prepared_leaf shrincs_fxmss_sha256 sp pp
  a md]) =
  32.
{ by rewrite leaf_rows_rows_one_size known_message_prepared_digits
  known_message_digits_length. }
have hx' : size xs = size (fixed_rows [:: known_message_prepared_leaf
  shrincs_fxmss_sha256 sp pp
  a md])
  by rewrite hr.
have hs := leaf_rows_sigs_size s pp _ _ hx'.
have he := leaf_rows_ends_size pp _ _ hs.
rewrite hr in hs he.
rewrite leaf_rows_complete_rows.
cbv zeta.
cbn [fixed_cache].
rewrite known_message_prepared_digits known_message_digits_length -{1}he take_size -hs
  take_size.
rewrite leaf_sampling_prepared_rows (leaf_sampling_sigs sp) (leaf_sampling_ends sp).
rewrite known_message_digits_length.
rewrite /leaf_sampling_entry /r_compress_encode.
congr [:: (_, _)].
by rewrite /known_message_prepared_leaf; case: known_message_find.
Qed.

Definition leaf_sampling_encode sp a (sg : option fixed_signature) : option
  leaf_opening_signature :=
  omap (fun cs => wcp_sig_encode
    (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) (cs.2, cs.1))
      sg.

Lemma leaf_sampling_encodeE sp a sg :
  leaf_sampling_encode sp a sg =
    omap (fun cs => wcp_sig_encode
      (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2))
      (cs.2, cs.1)) sg.
Proof. by []. Qed.

(* Keep bounded counter search out of signature conversion. *)
Local Opaque find_counter.
(* Unfold the wrapper while keeping bounded counter search sealed for conversion. *)
Local Transparent known_message_find.

Lemma leaf_sampling_zero sp pp a md xs :
  (leaf_sampling_entry 0 sp pp a md xs).1 = leaf_pk shrincs_fxmss_sha256 sp pp a xs /\
  leaf_sampling_encode sp a (leaf_sampling_entry 0 sp pp a md xs).2 =
    leaf_sign_at shrincs_fxmss_sha256 sp pp a xs md.
Proof.
rewrite /leaf_sampling_entry.
cbv zeta.
split.
- change (Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode
    (ends_from_sig (bytes 16) (bytes 16) 32 16
      (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2))) pp
      (known_message_digits shrincs_fxmss_sha256 sp pp a md)
      (roots_map (bytes 16) (bytes 16) 16
        (Fw (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2))) pp
          0 0
        (known_message_digits shrincs_fxmss_sha256 sp pp a md) xs))) = leaf_pk
          shrincs_fxmss_sha256 sp pp a xs).
  rewrite ends_from_roots_map0.
  + exact: known_message_digits_length.
  + exact: r_compress_digits_wf.
  + by [].
- rewrite /leaf_sampling_encode /= (roots_map_sign (bytes 16) (bytes 16) 32 16
    _ _ _ _ (known_message_digits_length shrincs_fxmss_sha256 sp pp a md)).
  rewrite /leaf_sign_at /shrincs_fxmss_leaf_sign /shrincs_wots_sign
    /known_message_digits.
  case hf: (known_message_find shrincs_fxmss_sha256 sp pp a md) => [c|].
  + rewrite /known_message_find in hf.
    by rewrite hf.
  + rewrite /known_message_find in hf.
    by rewrite hf.
Qed.

Definition leaf_sampling_last_entry sp pp a md xs : prepared_leaf_entry :=
  let W := shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2) in
  let ds := known_message_digits shrincs_fxmss_sha256 sp pp a md in
  let sg := sig_map (bytes 16) (bytes 16) 16 (Fw W) pp 0 ds xs in
  ((sg, complete_ends W pp ds sg), known_message_find shrincs_fxmss_sha256 sp pp a md).

Lemma leaf_sampling_last_counter sp pp a md xs :
  (leaf_sampling_last_entry sp pp a md xs).2 =
    known_message_find shrincs_fxmss_sha256 sp pp a md.
Proof. by []. Qed.

Lemma leaf_sampling_last sp pp a md xs :
  leaf_sampling_entry 14 sp pp a md xs =
    let e := leaf_sampling_last_entry sp pp a md xs in
    (Th pp (shrincs_fxmss_pk_tweak a) (r_compress_encode e.1.2),
      omap (fun c => (c, e.1.1)) e.2).
Proof.
rewrite /leaf_sampling_entry /leaf_sampling_last_entry.
by rewrite (sig_map_roots _ _ _ _ _ _ _ _ (r_compress_digits_wf sp pp a md)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf coupling sampling *)

Import PackageNotation.
#[local] Open Scope package_scope.

Definition leaf_blocks_blocks (ats : seq shrincs_fxmss_coord) :=
  query_list (fun _ : shrincs_fxmss_coord => sample_seq (dBytes 16) 32) ats.
Definition leaf_blocks_cache s sp pp sd (ats : seq shrincs_fxmss_coord) (blocks : seq
  (seq
  (bytes 16))) :=
  [seq leaf_sampling_entry s sp pp ax.1 (leaf_committed_digest sd ax.1) ax.2
    | ax <- zip ats blocks].
Fixpoint leaf_blocks_keys (ats : seq shrincs_fxmss_coord) (blocks : seq (seq (bytes
  16))) :
  shrincs_fxmss_key_table :=
  match ats, blocks with
  | a :: ats', xs :: blocks' => setm (leaf_blocks_keys ats' blocks') a xs
  | _, _ => emptym
  end.
Definition leaf_blocks_wf (ats : seq shrincs_fxmss_coord) (blocks : seq (seq (bytes
  16))) :=
  size blocks = size ats /\ all (fun xs => size xs == 32) blocks.

Local Opaque bind sample_seq dBytes Th wots_c_counter_max known_message_find
  known_message_digits leaf_sampling_entry.

Lemma leaf_blocks_blocks_congr ats {B : choice_type}
    (k0 k1 : seq (seq (bytes 16)) -> raw_code B) :
  (forall blocks, leaf_blocks_wf ats blocks -> k0 blocks = k1 blocks) ->
  (blocks ← leaf_blocks_blocks ats ;; k0 blocks) =
    (blocks ← leaf_blocks_blocks ats ;; k1 blocks).
Proof.
elim: ats k0 k1 => [|a ats ih] k0 k1 hk.
- change (k0 [::] = k1 [::]).
  apply: hk. by split.
- (* The head block has 32 samples; the tail satisfies the same bounds. *)
  rewrite /leaf_blocks_blocks /query_list.
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  apply: sample_seq_congr => xs hxs.
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  apply: ih => blocks [hlen hwf].
  apply: hk.
  split; first by rewrite /= hlen.
  by rewrite /= hxs eqxx hwf.
Qed.

Lemma leaf_blocks_flat_congr s sp pp sd ats {B : choice_type}
    (k : seq fixed_cache_entry -> raw_code B) :
  (xs ← sample_seq (dBytes 16) (32 * size ats) ;;
   k (leaf_ud_complete s
     [seq known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a
       (leaf_committed_digest sd a)
       | a <- ats] pp xs)) =
  (blocks ← leaf_blocks_blocks ats ;; k (leaf_blocks_cache s sp pp sd ats blocks)).
Proof.
elim: ats k => [|a ats ih] k.
- by [].
- rewrite [size (_ :: _)]/= mulnS sample_seq_cat.
  rewrite /leaf_blocks_blocks /query_list [LHS]bind_assoc [RHS]bind_assoc.
  apply: sample_seq_congr => xs hx.
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  cbn [bind].
  have he ys : leaf_ud_complete s
    [seq known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a
      (leaf_committed_digest sd a)
      | a <- a :: ats] pp (xs ++ ys) =
    leaf_sampling_entry s sp pp a (leaf_committed_digest sd a) xs ::
    leaf_ud_complete s
      [seq known_message_prepared_leaf shrincs_fxmss_sha256 sp pp a
        (leaf_committed_digest sd a)
        | a <- ats] pp ys.
  { rewrite map_cons leaf_rows_complete_cons.
    - by rewrite known_message_prepared_digits known_message_digits_length.
    - by rewrite leaf_sampling_complete_one.
  }
  setoid_rewrite he.
  rewrite (ih (fun cache =>
    k (leaf_sampling_entry s sp pp a (leaf_committed_digest sd a) xs :: cache))).
  apply: leaf_blocks_blocks_congr => blocks hwf.
  by [].
Qed.

Lemma leaf_blocks_keys_congr ats {B : choice_type}
    (k : shrincs_fxmss_key_table -> raw_code B) :
  (kt ← shrincs_fxmss_sample_keys shrincs_fxmss_sha256 ats ;; k kt) =
  (blocks ← leaf_blocks_blocks ats ;; k (leaf_blocks_keys ats blocks)).
Proof.
elim: ats k => [|a ats ih] k.
- by [].
- (* The head key block agrees with the sampled block table. *)
  rewrite /shrincs_fxmss_sample_keys /leaf_blocks_blocks /query_list
    [LHS]bind_assoc [RHS]bind_assoc.
  apply: sample_seq_congr => xs hx.
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  cbn [bind].
  rewrite (ih (fun kt => k (setm kt a xs))).
  by [].
Qed.

Definition leaf_blocks_last sp pp sd (ats : seq shrincs_fxmss_coord) (blocks : seq (seq
  (bytes
  16))) :=
  [seq leaf_sampling_last_entry sp pp ax.1 (leaf_committed_digest sd ax.1) ax.2
    | ax <- zip ats blocks].

Lemma leaf_blocks_leaf_congr sp pp a md {B : choice_type} (k : prepared_leaf_entry ->
  raw_code B) :
  (e ← prepared_leaf_sample sp pp a md ;; k e) =
  (xs ← sample_seq (dBytes 16) 32 ;; k (leaf_sampling_last_entry sp pp a md xs)).
Proof.
rewrite /prepared_leaf_sample bind_assoc sample_sig_roots_code
  known_message_digits_length.
by [].
Qed.

Lemma leaf_blocks_last_congr sp pp sd ats {B : choice_type}
    (k : seq prepared_leaf_entry -> raw_code B) :
  (es ← query_list (fun a => prepared_leaf_sample sp pp a (leaf_committed_digest sd a))
    ats ;;
   k es) =
  (blocks ← leaf_blocks_blocks ats ;; k (leaf_blocks_last sp pp sd ats blocks)).
Proof.
elim: ats k => [|a ats ih] k.
- by [].
- (* The last hybrid prepares the head leaf and then the tail. *)
  rewrite /leaf_blocks_blocks /query_list [LHS]bind_assoc [RHS]bind_assoc.
  rewrite leaf_blocks_leaf_congr.
  apply: sample_seq_congr => xs hx.
  rewrite [LHS]bind_assoc [RHS]bind_assoc.
  cbn [bind].
  rewrite (ih (fun es =>
    k (leaf_sampling_last_entry sp pp a (leaf_committed_digest sd a) xs :: es))).
  by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf coupling blocks *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque bind sample_seq dBytes Th wots_c_counter_max.

Lemma leaf_blocks_blocks_valid ats : ValidCode emptym emptym (leaf_blocks_blocks ats).
Proof.
elim: ats => [|a ats ih].
- exact: valid_ret.
- (* Sampling a head block and the remaining blocks is valid. *)
  cbn [leaf_blocks_blocks query_list].
  eapply valid_bind; first exact: sample_seq_valid.
  move=> xs.
  eapply valid_bind; first exact: ih.
  move=> blocks.
  exact: valid_ret.
Qed.

Lemma leaf_blocks_blocks_spec ats {B : choice_type}
    (pre : precond) (post : postcond B B)
    (k0 k1 : seq (seq (bytes 16)) -> raw_code B) :
  (forall blocks, leaf_blocks_wf ats blocks ->
    ⊢ ⦃ pre ⦄ k0 blocks ≈ k1 blocks ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄ (blocks ← leaf_blocks_blocks ats ;; k0 blocks) ≈
    (blocks ← leaf_blocks_blocks ats ;; k1 blocks) ⦃ post ⦄.
Proof.
move=> hk.
pose good blocks := (size blocks == size ats) &&
  all (fun xs : seq (bytes 16) => size xs == 32) blocks.
have hguard (k : seq (seq (bytes 16)) -> raw_code B) :
  (blocks ← leaf_blocks_blocks ats ;; k blocks) =
  (blocks ← leaf_blocks_blocks ats ;; if good blocks then k blocks else fail).
{ apply: leaf_blocks_blocks_congr => blocks [hlen hall].
  by rewrite /good hlen eqxx hall.
}
rewrite (hguard k0) (hguard k1).
apply: r_scheme_bind; first exact: leaf_blocks_blocks_valid.
move=> blocks.
case hg: (good blocks); last exact: r_fail.
apply: hk.
move: hg => /andP[/eqP hlen hall].
by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf coupling cache *)

Import PackageNotation.
#[local] Open Scope package_scope.

Local Opaque wots_c_counter_max Th dBytes leaf_sampling_encode.

Definition leaf_context_sampling_results sp (ats : seq shrincs_fxmss_coord)
    (cache : seq (option fixed_signature)) i : seq (option leaf_opening_signature) :=
  [seq leaf_sampling_encode sp ai.1 (nth None cache ai.2)
    | ai <- zip ats (iota i (size ats))].

Lemma leaf_context_sampling_one r sp a :
  code_link (leaf_ctx_ud_one sp a) (G_leaf_roots r) =
  (sg ← (cache ← getSome leaf_batch_cache_loc ;;
         i ← get leaf_batch_slot_loc ;;
         #put leaf_batch_slot_loc := i.+1 ;;
         ret (nth None cache i)) ;;
   ret (leaf_sampling_encode sp a sg)).
Proof.
rewrite /leaf_ctx_ud_one code_link_bind.
cbn [code_link].
rewrite /G_leaf_roots /resolve /= coerce_kleisliE.
by rewrite bind_ret.
Qed.

Local Opaque leaf_sampling_encode bind code_link.
Lemma leaf_context_sampling_drain (r : nat) (sp : shrincs_fxmss_structure) (ats : seq
  shrincs_fxmss_coord)
    (cache : seq (option fixed_signature)) (i : nat) {B : choiceType}
    (pre : nat -> precond) (post : postcond B B)
    (c0 : seq (option leaf_opening_signature) -> raw_code B)
    (c1 : seq (option leaf_opening_signature) -> raw_code B) :
  (forall j h0 h1, pre j (h0,h1) ->
    get_heap h1 leaf_batch_cache_loc = Some cache /\
    get_heap h1 leaf_batch_slot_loc = j) ->
  (forall j h0 h1, pre j (h0,h1) ->
    pre j.+1 (h0, set_heap h1 leaf_batch_slot_loc j.+1)) ->
  (forall ys, ys = leaf_context_sampling_results sp ats cache i ->
    ⊢ ⦃ fun '(h0, h1) => pre (i + size ats)%nat (h0, h1) ⦄ c0 ys ≈ c1 ys ⦃ post ⦄) ->
  ⊢ ⦃ fun '(h0, h1) => pre i (h0, h1) ⦄ c0 (leaf_context_sampling_results sp ats cache
    i) ≈
    (ys ← code_link (query_list (leaf_ctx_ud_one sp) ats) (G_leaf_roots r) ;;
     c1 ys) ⦃ post ⦄.
Proof.
move=> hget hput.
elim: ats i c0 c1 => [|a ats ih] i c0 c1 hk.
- cbn [query_list code_link bind].
  rewrite addn0 in hk.
  apply: hk. by [].
- (* A cached head value advances the slot before draining the tail. *)
  rewrite /query_list code_link_bind leaf_context_sampling_one bind_assoc bind_assoc.
  cbn [bind].
  eapply (r_get_rhs_known leaf_batch_cache_loc (Some cache));
    first by move=> h0 h1 hp; have [] := hget i h0 h1 hp.
  cbv beta iota.
  cbn [assertD isSome getSome bind].
  eapply (r_get_rhs_known leaf_batch_slot_loc i);
    first by move=> h0 h1 hp; have [] := hget i h0 h1 hp.
  cbv beta iota.
  eapply (r_put_rhs_weak _ _ _ (pre i.+1)); first exact: hput.
  rewrite code_link_bind.
  cbn [code_link].
  rewrite bind_assoc.
  cbn [bind].
  change (leaf_context_sampling_results sp (a :: ats) cache i) with
    (leaf_sampling_encode sp a (nth None cache i) :: leaf_context_sampling_results sp
      ats cache i.+1).
  apply: (ih i.+1 (fun ys => c0 (leaf_sampling_encode sp a (nth None cache i) ::
    ys))).
  move=> ys ->.
  rewrite addSn -addnS.
  apply: hk. by [].
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf coupling values *)

Definition leaf_values_encoded sp (ats : seq shrincs_fxmss_coord) (cache : seq
  fixed_cache_entry) :=
  [seq leaf_sampling_encode sp ac.1 ac.2.2 | ac <- zip ats cache].
Definition leaf_values_signature sp (a : shrincs_fxmss_coord) (e : prepared_leaf_entry)
  : option
  leaf_opening_signature :=
  omap (fun c => wots.params.wcp_sig_encode
    (shrincs_fxmss_leaf_params shrincs_fxmss_sha256 a sp.1 (uint U8 sp.2)) (e.1.1, c))
      e.2.
Definition leaf_values_last_signatures sp (ats : seq shrincs_fxmss_coord) (es : seq
  prepared_leaf_entry)
  :=
  [seq leaf_values_signature sp ae.1 ae.2 | ae <- zip ats es].

Local Opaque Th wots_c_counter_max known_message_find leaf_sampling_entry
  leaf_sampling_last_entry leaf_sampling_encode.

Lemma leaf_values_drain_shift sp ats cache x i :
  leaf_context_sampling_results sp ats (x :: cache) i.+1 = leaf_context_sampling_results
    sp ats cache i.
Proof.
elim: ats i => [|a ats ih] i //=.
rewrite /leaf_context_sampling_results /=.
congr (_ :: _).
exact: ih.
Qed.

Lemma leaf_values_drain_full sp ats cache :
  size cache = size ats ->
  leaf_context_sampling_results sp ats [seq e.2 | e <- cache] 0 = leaf_values_encoded sp
    ats cache.
Proof.
elim: ats cache => [|a ats ih] [|e cache] //= [hlen].
change (leaf_sampling_encode sp a e.2 :: leaf_context_sampling_results sp ats (e.2 ::
  [seq e.2 | e <- cache]) 1 =
  leaf_sampling_encode sp a e.2 :: leaf_values_encoded sp ats cache).
by rewrite leaf_values_drain_shift ih.
Qed.

Lemma leaf_values_cache_size s sp pp sd ats blocks :
  size blocks = size ats -> size (leaf_blocks_cache s sp pp sd ats blocks) = size ats.
Proof. by move=> hb; rewrite /leaf_blocks_cache size_map size_zip hb minnn. Qed.

Lemma leaf_values_keys_nth ats blocks i :
  uniq ats -> size blocks = size ats -> i < size ats ->
  getm (leaf_blocks_keys ats blocks) (nth (uint U8 0, uint U64 0) ats i) =
    Some (nth [::] blocks i).
Proof.
elim: ats blocks i => [|a ats ih] [|xs blocks] i //= /andP[ha hu] [hlen].
case: i => [|i] hi.
- by rewrite setmE eqxx.
- (* A tail coordinate is distinct from the head coordinate. *)
  rewrite setmE.
  have hn : nth (uint U8 0, uint U64 0) ats i != a.
  { apply/eqP=> he.
    move: ha => /negP ha.
    apply: ha.
    rewrite -he.
    exact: mem_nth hi.
  }
  rewrite /= (negbTE hn).
  exact: ih hu hlen hi.
Qed.

Lemma leaf_values_cache_nth s sp pp sd ats blocks i :
  size blocks = size ats -> i < size ats ->
  nth (zeros 16, None) (leaf_blocks_cache s sp pp sd ats blocks) i =
    leaf_sampling_entry s sp pp (nth (uint U8 0, uint U64 0) ats i)
      (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i))
      (nth [::] blocks i).
Proof.
elim: ats blocks i => [|a ats ih] [|xs blocks] [|i] //= [hlen] hi.
exact: ih hlen hi.
Qed.

Lemma leaf_values_encoded_nth sp ats cache i :
  size cache = size ats -> i < size ats ->
  nth None (leaf_values_encoded sp ats cache) i =
    leaf_sampling_encode sp (nth (uint U8 0, uint U64 0) ats i)
      (nth (zeros 16, None) cache i).2.
Proof.
elim: ats cache i => [|a ats ih] [|e cache] [|i] //= [hlen] hi.
exact: ih hlen hi.
Qed.

Lemma leaf_values_zero_roots sp pp sd ats blocks :
  uniq ats -> size blocks = size ats ->
  [seq e.1 | e <- leaf_blocks_cache 0 sp pp sd ats blocks] =
    [seq leaf_pk shrincs_fxmss_sha256 sp pp a (odflt [::] (getm (leaf_blocks_keys ats
      blocks)
      a))
      | a <- ats].
Proof.
move=> hu hb.
apply: (@eq_from_nth _ (zeros 16)).
- by rewrite !size_map size_zip hb minnn.
- (* Each initial root equals the root from the sampled key table. *)
  move=> i hi.
  have hc := leaf_values_cache_size 0 sp pp sd ats blocks hb.
  rewrite size_map hc in hi.
  rewrite (nth_map (zeros 16, None)) ?hc //.
  rewrite (leaf_values_cache_nth _ _ _ _ _ _ _ hb hi).
  rewrite (nth_map (uint U8 0, uint U64 0)) //.
  rewrite (leaf_values_keys_nth _ _ _ hu hb hi) /=.
  exact: (proj1 (leaf_sampling_zero _ _ _ _ _)).
Qed.

Lemma leaf_values_zero_signatures sp pp sd ats blocks :
  uniq ats -> size blocks = size ats ->
  leaf_values_encoded sp ats (leaf_blocks_cache 0 sp pp sd ats blocks) =
    [seq leaf_sign_at shrincs_fxmss_sha256 sp pp a (odflt [::] (getm (leaf_blocks_keys
      ats
      blocks) a))
      (leaf_committed_digest sd a) | a <- ats].
Proof.
move=> hu hb.
have hc := leaf_values_cache_size 0 sp pp sd ats blocks hb.
have hs : size (leaf_values_encoded sp ats (leaf_blocks_cache 0 sp pp sd ats blocks))
  = size ats.
{ by rewrite /leaf_values_encoded size_map size_zip hc minnn. }
apply: (@eq_from_nth _ None).
- by rewrite hs size_map.
- (* Each initial signature equals the signature from the sampled keys. *)
  move=> i hi.
  rewrite hs in hi.
  rewrite (leaf_values_encoded_nth _ _ _ _ hc hi) (leaf_values_cache_nth _ _ _ _ _ _ _
    hb hi).
  rewrite (nth_map (uint U8 0, uint U64 0)) //.
  rewrite (leaf_values_keys_nth _ _ _ hu hb hi) /=.
  exact: (proj2 (leaf_sampling_zero _ _ _ _ _)).
Qed.

Lemma leaf_values_last_roots sp pp sd ats blocks :
  [seq e.1 | e <- leaf_blocks_cache 14 sp pp sd ats blocks] =
    [seq Th pp (shrincs_fxmss_pk_tweak ae.1) (r_compress_encode ae.2.1.2)
      | ae <- zip ats (leaf_blocks_last sp pp sd ats blocks)].
Proof.
elim: ats blocks => [|a ats ih] [|xs blocks] //=.
rewrite /leaf_blocks_cache /leaf_blocks_last /= leaf_sampling_last /=.
congr (_ :: _).
exact: ih.
Qed.

Lemma leaf_values_last_encode sp a (e : prepared_leaf_entry) :
  leaf_sampling_encode sp a (omap (fun c => (c, e.1.1)) e.2) = leaf_values_signature sp
    a e.
Proof.
by rewrite leaf_sampling_encodeE /leaf_values_signature; case: e.2.
Qed.

Lemma leaf_values_last_encoded sp pp sd ats blocks :
  leaf_values_encoded sp ats (leaf_blocks_cache 14 sp pp sd ats blocks) =
    leaf_values_last_signatures sp ats (leaf_blocks_last sp pp sd ats blocks).
Proof.
elim: ats blocks => [|a ats ih] [|xs blocks] //=.
rewrite /leaf_values_encoded /leaf_values_last_signatures /leaf_blocks_cache
  /leaf_blocks_last /= leaf_sampling_last /=.
rewrite leaf_values_last_encode.
congr (_ :: _).
exact: ih.
Qed.

Lemma leaf_values_last_size sp pp sd ats blocks :
  size blocks = size ats -> size (leaf_blocks_last sp pp sd ats blocks) = size ats.
Proof. by move=> hb; rewrite /leaf_blocks_last size_map size_zip hb minnn. Qed.

Lemma leaf_values_last_nth sp pp sd ats blocks i :
  size blocks = size ats -> i < size ats ->
  nth prepared_leaf_default (leaf_blocks_last sp pp sd ats blocks) i =
    leaf_sampling_last_entry sp pp (nth (uint U8 0, uint U64 0) ats i)
      (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i))
      (nth [::] blocks i).
Proof.
elim: ats blocks i => [|a ats ih] [|xs blocks] [|i] //= [hlen] hi.
exact: ih hlen hi.
Qed.

Lemma leaf_values_last_counter sp pp sd ats blocks i :
  size blocks = size ats -> i < size ats ->
  (nth prepared_leaf_default (leaf_blocks_last sp pp sd ats blocks) i).2 =
    known_message_find shrincs_fxmss_sha256 sp pp (nth (uint U8 0, uint U64 0) ats i)
      (leaf_committed_digest sd (nth (uint U8 0, uint U64 0) ats i)).
Proof.
move=> hb hi.
rewrite (leaf_values_last_nth _ _ _ _ _ _ hb hi).
by rewrite leaf_sampling_last_counter.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Prepared-root coupling values *)

Local Opaque Th known_message_find wots_c_counter_max.

Lemma prepared_leaf_coupling_signatures_nth sp ats entries j :
  size entries = size ats -> j < size ats ->
  nth None (leaf_values_last_signatures sp ats entries) j =
    leaf_values_signature sp (nth (uint U8 0, uint U64 0) ats j)
      (nth prepared_leaf_default entries j).
Proof.
elim: ats entries j => [|a ats ih] [|e entries] [|j] //= [hlen] hj.
exact: ih hlen hj.
Qed.

Lemma prepared_leaf_coupling_roots_nth sp pp entries j :
  shrincs_fxmss_structure_legal sp.1 sp.2 ->
  size entries = size (shrincs_fxmss_schedule sp) -> j < size (shrincs_fxmss_schedule
    sp) ->
  nth (zeros 16) (prepared_leaf_roots sp pp entries) j =
    Th pp (shrincs_fxmss_pk_tweak (leaf_coord_at sp j))
      (Shrincs.internal.ssprove.fxmss.leaf.compress.pure.r_compress_encode (nth
        prepared_leaf_default entries j).1.2).
Proof.
move=> hsp hlen hj.
rewrite /prepared_leaf_roots (nth_map ((uint U8 0, uint U64 0),
  prepared_leaf_default)).
- by rewrite size_zip hlen minnn.
- rewrite nth_zip; first by rewrite hlen.
  cbn [fst snd].
  rewrite (leaf_schedule_nth sp j hsp) //.
  by rewrite -(leaf_schedule_length sp hsp).
Qed.

Lemma prepared_leaf_coupling_verdict sp pp a md entry mw :
  entry.2 = known_message_find shrincs_fxmss_sha256 sp pp a md ->
  prepared_leaf_verdict 0 sp pp a md entry mw =
    (leaf_recover shrincs_fxmss_sha256 sp pp a mw.1 mw.2 ==
      Some (Th pp (shrincs_fxmss_pk_tweak a)
        (Shrincs.internal.ssprove.fxmss.leaf.compress.pure.r_compress_encode
          entry.1.2))) &&
    known_message_gate shrincs_fxmss_sha256 sp pp a md mw.1.
Proof.
move=> he.
rewrite prepared_leaf_verdict_before_chain // /= !andbT /leaf_recover
  Shrincs.internal.ssprove.fxmss.scheme.shrincs_fxmss_leaf_recover_verify
    /known_message_gate he.
by [].
Qed.
