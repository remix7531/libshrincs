(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.addressing

    THE address facade over [Model.address]: the single, scheme-neutral
    layer every SHRINCS scheme in this repository builds its addresses
    and tweaks through.  [Model.address] itself stays Stdlib-only, so
    this file is where the reachable-states ADRS gets equipped with the
    SSProve/MathComp structure (a [Finite] instance, a [choice_type]
    tweak space) AND with the [nat]-boundary smart constructors.

    ** One facade, all twelve arms

    [Model.address.adrs] has twelve constructors -- five stateful
    ([Wc_hash], [Wc_prf], [Wc_pk], [Wc_grind], [Fxmss], along the FXMSS
    leaf) and seven stateless ([Tw_hash], [Tw_prf], [Tw_pk],
    [Fors_roots], [Xmss_tree], [Fors_tree], [Fors_prf], along the
    SPHINCS+ hypertree).  ALL twelve get the same four pieces here, in
    the same shape, whether or not this repository's current proofs use
    them: a smart constructor from bare [nat] components, the
    [field_bounded]-style range predicate its components must satisfy to
    be placed exactly, an injectivity lemma on exactly those inputs, and
    membership in the [Finite] / [encode_adrs] / [decode_adrs] encoding
    (automatic -- the encoding is the full 12-arm coproduct).  The seven
    stateless arms have no consumer yet, deliberately: the future
    FORS/hypertree driver extends THIS facade instead of minting a
    second one.

    ** Exact-or-zero placement

    The reachable-states model is EXACT: every [fin] field carries its
    range proof, and there is no saturating clamp anywhere
    ([Model.fin]).  A [nat] arriving at this boundary (game code, a
    [nat * nat] tweak, a copied [nat]-shaped development) has no bound
    in scope, so the facade totalizes it EXACT-OR-ZERO
    ([fin_of_nat_or_zero]): a representable component is placed exactly,
    an unrepresentable one is represented by zero in the SAME address
    class.  No component is ever truncated or reduced modulo its field
    bound, and every injectivity lemma below states the range hypotheses
    under which the placement is exact.  The two arms whose field bounds
    are PARAMETRIC ([Wc_hash], [Wc_prf], over [chain_count] and
    [w.-1]) additionally guard the bound's positivity, falling back to
    the pk address when the parameter is degenerate; with a positive
    parameter -- which every in-range component argument already
    witnesses -- that branch is unreachable.

    Because placement needs no proof ARGUMENT, no caller has to thread a
    range proof, and no definition anywhere has to stay transparent for
    two rebuilds of the same address to be definitionally equal.

    ** The EXACT tweak space (Rank 1)

    [adrs_sf] is equipped with a mathcomp [Finite] instance by
    transporting the finite structure of the flat 12-arm coproduct
    [adrs_sum] along the constructor bijection [adrs_p]/[adrs_u]
    ([can_type adrs_pK]).  The FinFin shim makes each [fin b] summand a
    [finType] with the bound [b] kept SYMBOLIC (in particular
    [fin (2^64)] never materializes [Z.to_nat (2^64)]).

    The tweak space is then the single canonical ordinal
    [adrs_sf_ch := 'fin #|adrs_sf|], with encode/decode the canonical
    bijection [fto]/[otf] (enum_rank/enum_val).  Both cancels
    ([encode_adrsK]) are TOTAL (no range side conditions) and decode is a
    genuine two-sided inverse, so every address round-trips.

    Scheme-SPECIFIC tweak layers sit on top: [Sec.wots.addressing] adds
    the WOTS+C per-hash-call tweaks ([chain_tweak], [prf_tweak]);
    [SHRINCS.addressing] re-exports this facade under the FXMSS
    development's own names. *)

From HB Require Import structures.
From Sec.lib Require Import prelude fin_fin.
From Model Require address.
From Model Require Import byte fin.
From Stdlib Require Import ZArith Lia.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ------------------------------------------------------------------ *)
(** ** Field-range predicates

    One predicate shape for every ADRS field: [field_bounded bound n]
    says the [nat] component [n] is representable in a [fin bound]
    field.  [component_bounded] is the [nat]-bound convenience (the
    parametric [chain_count] / [w.-1] fields); [anchor_bounded] and
    [hypertree_bounded] bundle the two-slot anchor of the stateful and
    stateless families.  They wrap the [Z] arithmetic so the
    mathcomp-heavy games can state and carry field bounds WITHOUT
    importing [ZArith] (which would shadow ssrnat's [^]/[<] in
    [nat_scope]). *)

Definition field_bounded (bound : Z) (n : nat) : Prop := (Z.of_nat n < bound)%Z.

Definition component_bounded (bound n : nat) : Prop := field_bounded (Z.of_nat bound) n.

Lemma component_bounded_lt bound n :
  (n < bound)%nat -> component_bounded bound n.
Proof.
move=> Hn; rewrite /component_bounded /field_bounded.
apply Nat2Z.inj_lt.
exact/ltP.
Qed.

(** The stateful anchor: a 1-byte node height and an 8-byte node index. *)
Definition anchor_bounded (zi : nat * nat) : Prop :=
  field_bounded 256 zi.1 /\ field_bounded (2 ^ 64) zi.2.

(** The stateless anchor: a hypertree layer and an 8-byte tree address. *)
Definition hypertree_bounded (lt : nat * nat) : Prop :=
  field_bounded address.hypertree_layers lt.1 /\ field_bounded (2 ^ 64) lt.2.

(* ------------------------------------------------------------------ *)
(** ** Exact-or-zero placement

    [fin_of_nat_or_zero bound _ n] is [n] itself when [n] is
    representable and the field's zero otherwise -- a [Z_lt_dec] guard,
    NOT a clamp.  [fin_of_nat_or_zeroE] is the exactness bridge every
    caller with a range proof in hand rewrites with. *)

Definition fin_zero (bound : Z) (Hbound : (0 < bound)%Z) : fin bound :=
  fin_of_nat bound 0 Hbound.

Definition fin_of_nat_or_zero (bound : Z) (Hbound : (0 < bound)%Z)
    (n : nat) : fin bound :=
  match Z_lt_dec (Z.of_nat n) bound with
  | left Hn => fin_of_nat bound n Hn
  | right _ => fin_zero bound Hbound
  end.

Lemma fin_of_nat_or_zeroE bound Hbound n
    (Hn : (Z.of_nat n < bound)%Z) :
  fin_of_nat_or_zero bound Hbound n = fin_of_nat bound n Hn.
Proof.
rewrite /fin_of_nat_or_zero; case: Z_lt_dec => [Hn'|Hn']; last by lia.
by apply: fin_val_inj; rewrite !fin_val_of_nat.
Qed.

Lemma fin_of_nat_or_zero_val bound Hbound n :
  field_bounded bound n ->
  fin_val (fin_of_nat_or_zero bound Hbound n) = Z.of_nat n.
Proof. by move=> Hn; rewrite (fin_of_nat_or_zeroE _ _ _ Hn) fin_val_of_nat. Qed.

(** Exact-or-zero placement is injective on representable components:
    the ONE fact every per-arm injectivity lemma below is assembled
    from. *)
Lemma fin_of_nat_or_zero_inj bound Hbound n m :
  field_bounded bound n -> field_bounded bound m ->
  fin_of_nat_or_zero bound Hbound n = fin_of_nat_or_zero bound Hbound m ->
  n = m.
Proof.
move=> Hn Hm.
rewrite (fin_of_nat_or_zeroE _ _ _ Hn) (fin_of_nat_or_zeroE _ _ _ Hm).
exact: fin_of_nat_inj.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The per-field placers

    One placer per ADRS field bound, each the exact-or-zero totalizer at
    that bound.  The five spec-constant bounds of the stateless family
    ([Model.address]'s [hypertree_layers], [sub_leaves], [len_tw],
    [w_tw_pred], [h_xmss], [h_fors], [fors_idx]) are concrete, so their
    positivity is a [lia]; the two WOTS+C bounds are parametric and are
    guarded at the constructor instead. *)

Lemma byte_bound_pos : (0 < 256)%Z.
Proof. lia. Qed.

Lemma index_bound_pos : (0 < 2 ^ 64)%Z.
Proof. by apply: Z.pow_pos_nonneg; lia. Qed.

Lemma hypertree_layers_pos : (0 < address.hypertree_layers)%Z.
Proof. rewrite /address.hypertree_layers; lia. Qed.

Lemma sub_leaves_pos : (0 < address.sub_leaves)%Z.
Proof. rewrite /address.sub_leaves; lia. Qed.

Lemma len_tw_pos : (0 < address.len_tw)%Z.
Proof. rewrite /address.len_tw; lia. Qed.

Lemma w_tw_pred_pos : (0 < address.w_tw_pred)%Z.
Proof. rewrite /address.w_tw_pred; lia. Qed.

Lemma h_xmss_pos : (0 < address.h_xmss)%Z.
Proof. rewrite /address.h_xmss; lia. Qed.

Lemma h_fors_pos : (0 < address.h_fors)%Z.
Proof. rewrite /address.h_fors; lia. Qed.

Lemma fors_idx_pos : (0 < address.fors_idx)%Z.
Proof. rewrite /address.fors_idx; lia. Qed.

Definition anchor_height (z : nat) : fin 256 :=
  fin_of_nat_or_zero 256 byte_bound_pos z.

Definition anchor_index (i : nat) : fin (2 ^ 64) :=
  fin_of_nat_or_zero (2 ^ 64) index_bound_pos i.

Definition anchor_layer (l : nat) : fin address.hypertree_layers :=
  fin_of_nat_or_zero address.hypertree_layers hypertree_layers_pos l.

Definition sub_leaf (kp : nat) : fin address.sub_leaves :=
  fin_of_nat_or_zero address.sub_leaves sub_leaves_pos kp.

Definition tw_chain (c : nat) : fin address.len_tw :=
  fin_of_nat_or_zero address.len_tw len_tw_pos c.

Definition tw_pos (p : nat) : fin address.w_tw_pred :=
  fin_of_nat_or_zero address.w_tw_pred w_tw_pred_pos p.

Definition xmss_height (h : nat) : fin address.h_xmss :=
  fin_of_nat_or_zero address.h_xmss h_xmss_pos h.

Definition fors_height (h : nat) : fin address.h_fors :=
  fin_of_nat_or_zero address.h_fors h_fors_pos h.

Definition fors_leaf (i : nat) : fin address.fors_idx :=
  fin_of_nat_or_zero address.fors_idx fors_idx_pos i.

Lemma anchor_heightE z (Hz : (Z.of_nat z < 256)%Z) :
  anchor_height z = fin_of_nat 256 z Hz.
Proof. exact: fin_of_nat_or_zeroE. Qed.

Lemma anchor_indexE i (Hi : (Z.of_nat i < 2 ^ 64)%Z) :
  anchor_index i = fin_of_nat (2 ^ 64) i Hi.
Proof. exact: fin_of_nat_or_zeroE. Qed.

Lemma anchor_height_inj z z' :
  field_bounded 256 z -> field_bounded 256 z' ->
  anchor_height z = anchor_height z' -> z = z'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma anchor_index_inj i i' :
  field_bounded (2 ^ 64) i -> field_bounded (2 ^ 64) i' ->
  anchor_index i = anchor_index i' -> i = i'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma anchor_layer_inj l l' :
  field_bounded address.hypertree_layers l ->
  field_bounded address.hypertree_layers l' ->
  anchor_layer l = anchor_layer l' -> l = l'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma sub_leaf_inj kp kp' :
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  sub_leaf kp = sub_leaf kp' -> kp = kp'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma tw_chain_inj c c' :
  field_bounded address.len_tw c -> field_bounded address.len_tw c' ->
  tw_chain c = tw_chain c' -> c = c'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma tw_pos_inj p p' :
  field_bounded address.w_tw_pred p -> field_bounded address.w_tw_pred p' ->
  tw_pos p = tw_pos p' -> p = p'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma xmss_height_inj h h' :
  field_bounded address.h_xmss h -> field_bounded address.h_xmss h' ->
  xmss_height h = xmss_height h' -> h = h'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma fors_height_inj h h' :
  field_bounded address.h_fors h -> field_bounded address.h_fors h' ->
  fors_height h = fors_height h' -> h = h'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

Lemma fors_leaf_inj i i' :
  field_bounded address.fors_idx i -> field_bounded address.fors_idx i' ->
  fors_leaf i = fors_leaf i' -> i = i'.
Proof. exact: fin_of_nat_or_zero_inj. Qed.

(* ================================================================== *)
(* [Finite.copy] through [adrs_pK] re-registers the lower structures HB
   already knows, tripping [redundant-canonical-projection] at the
   instance and at [End AdrsFacade] -- inherent to the idiom (mathcomp
   itself builds with this warning off).  Scoped off, restored after. *)
Set Warnings "-redundant-canonical-projection".

Section AdrsFacade.

(** The WOTS+C chain count and Winternitz parameter: the ONLY two
    parametric field bounds of the whole 12-arm union ([pos_bound :=
    w.-1] is the chain-position bound).  Every other field bound is a
    [Model.address] spec constant. *)
Context (chain_count w : nat).
Local Notation pos_bound := (w.-1).

Local Notation adrs_sf := (address.adrs chain_count pos_bound).

(* ------------------------------------------------------------------ *)
(** ** The mathcomp [Finite] instance on [adrs_sf]

    Transport the finite structure of the flat 12-arm coproduct
    [adrs_sum] along the constructor bijection.  Each [fin b] summand is
    a [finType] via [Sec.lib.fin_fin] with [b] kept symbolic. *)

Definition adrs_sum := ( fin 256 * fin (2^64) * fin (Z.of_nat chain_count) * fin (Z.of_nat pos_bound)
  + ( fin 256 * fin (2^64) * fin (Z.of_nat chain_count)
  + ( fin 256 * fin (2^64)
  + ( fin 256 * fin (2^64)
  + ( fin 256 * fin (2^64)
  + ( fin address.hypertree_layers * fin (2^64) * fin address.sub_leaves * fin address.len_tw * fin address.w_tw_pred
  + ( fin address.hypertree_layers * fin (2^64) * fin address.sub_leaves * fin address.len_tw
  + ( fin address.hypertree_layers * fin (2^64) * fin address.sub_leaves
  + ( fin address.hypertree_layers * fin (2^64) * fin address.sub_leaves
  + ( fin address.hypertree_layers * fin (2^64) * fin address.h_xmss * fin address.sub_leaves
  + ( fin address.hypertree_layers * fin (2^64) * fin address.sub_leaves * fin address.h_fors * fin address.fors_idx
  +   fin address.hypertree_layers * fin (2^64) * fin address.sub_leaves * fin address.fors_idx )))))))))))%type.

Definition adrs_p (a : adrs_sf) : adrs_sum :=
  match a with
  | address.Wc_hash nh ni c p => inl (nh,ni,c,p)
  | address.Wc_prf nh ni c => inr (inl (nh,ni,c))
  | address.Wc_pk nh ni => inr (inr (inl (nh,ni)))
  | address.Wc_grind nh ni => inr (inr (inr (inl (nh,ni))))
  | address.Fxmss nh ni => inr (inr (inr (inr (inl (nh,ni)))))
  | address.Tw_hash ly tr kp c h => inr (inr (inr (inr (inr (inl (ly,tr,kp,c,h))))))
  | address.Tw_prf ly tr kp c => inr(inr(inr(inr(inr(inr(inl (ly,tr,kp,c)))))))
  | address.Tw_pk ly tr kp => inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,kp))))))))
  | address.Fors_roots ly tr kp => inr(inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,kp)))))))))
  | address.Xmss_tree ly tr h idx => inr(inr(inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,h,idx))))))))))
  | address.Fors_tree ly tr kp h idx => inr(inr(inr(inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,kp,h,idx)))))))))))
  | address.Fors_prf ly tr kp idx => inr(inr(inr(inr(inr(inr(inr(inr(inr(inr(inr (ly,tr,kp,idx)))))))))))
  end.

Definition adrs_u (s : adrs_sum) : adrs_sf :=
  match s with
  | inl (nh,ni,c,p) => address.Wc_hash nh ni c p
  | inr (inl (nh,ni,c)) => address.Wc_prf nh ni c
  | inr (inr (inl (nh,ni))) => address.Wc_pk nh ni
  | inr (inr (inr (inl (nh,ni)))) => address.Wc_grind nh ni
  | inr (inr (inr (inr (inl (nh,ni))))) => address.Fxmss nh ni
  | inr (inr (inr (inr (inr (inl (ly,tr,kp,c,h)))))) => address.Tw_hash ly tr kp c h
  | inr(inr(inr(inr(inr(inr(inl (ly,tr,kp,c))))))) => address.Tw_prf ly tr kp c
  | inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,kp)))))))) => address.Tw_pk ly tr kp
  | inr(inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,kp))))))))) => address.Fors_roots ly tr kp
  | inr(inr(inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,h,idx)))))))))) => address.Xmss_tree ly tr h idx
  | inr(inr(inr(inr(inr(inr(inr(inr(inr(inr(inl (ly,tr,kp,h,idx))))))))))) => address.Fors_tree ly tr kp h idx
  | inr(inr(inr(inr(inr(inr(inr(inr(inr(inr(inr (ly,tr,kp,idx))))))))))) => address.Fors_prf ly tr kp idx
  end.

Lemma adrs_pK : cancel adrs_p adrs_u.
Proof. by case. Qed.

HB.instance Definition _ := Finite.copy adrs_sf (can_type adrs_pK).

(* ------------------------------------------------------------------ *)
(** ** The exact tweak space and its encode/decode bijection *)

Definition adrs_sf_ch : choice_type := 'fin #|{: adrs_sf}|.
Definition encode_adrs (a : adrs_sf) : adrs_sf_ch := fto a.
Definition decode_adrs (x : adrs_sf_ch) : adrs_sf := otf x.

Lemma encode_adrsK : cancel encode_adrs decode_adrs.
Proof. exact: otf_fto. Qed.

Lemma encode_adrs_inj : injective encode_adrs.
Proof. exact: can_inj encode_adrsK. Qed.

(* ------------------------------------------------------------------ *)
(** ** The flat [nat] view

    [Model.address]'s six [Z] wire projections, read back as [nat]s --
    the shape a [nat]-indexed development compares against, and the
    per-field selector the injectivity proofs below read.  Each field
    lands in exactly one projection, on every arm. *)

Definition adrs_type (a : adrs_sf) : nat := Z.to_nat (address.adrs_type a).

Definition adrs_height (a : adrs_sf) : nat := Z.to_nat (address.adrs_anchor_tag_z a).

Definition adrs_index (a : adrs_sf) : nat := Z.to_nat (address.adrs_anchor_idx_z a).

(** Payload word 0: the keypair / leaf index of the stateless arms. *)
Definition adrs_kp (a : adrs_sf) : nat := Z.to_nat (address.payload_a_z a).

(** Payload word 1: chain index or tree height. *)
Definition adrs_chain (a : adrs_sf) : nat := Z.to_nat (address.payload_b_z a).

(** Payload word 2: hash position or tree index. *)
Definition adrs_hash (a : adrs_sf) : nat := Z.to_nat (address.payload_c_z a).

Definition adrs_keypair (a : adrs_sf) : nat * nat := (adrs_height a, adrs_index a).

(** The stateful / stateless type bytes, as [nat]s. *)
Definition TY_WOTS_HASH_SF : nat := Z.to_nat address.SF_SHRINCS_WOTS_HASH.
Definition TY_WOTS_PK_SF : nat := Z.to_nat address.SF_SHRINCS_WOTS_PK.
Definition TY_TREE_SF : nat := Z.to_nat address.SF_FXMSS_TREE.
Definition TY_WOTS_PRF_SF : nat := Z.to_nat address.SF_SHRINCS_WOTS_PRF.
Definition TY_WOTS_GRIND_SF : nat := Z.to_nat address.SF_SHRINCS_WOTS_GRIND.

(* ------------------------------------------------------------------ *)
(** ** The five stateful smart constructors, SF_ rows

    The anchor [(z, i)] is the (node height, node index) pair of the
    FXMSS leaf this instance lives at.  [wc_pk_adrs] doubles as the
    degenerate-parameter fallback of the two guarded arms: with
    [chain_count = 0] (resp. [w.-1 = 0]) the chain-index (resp.
    position) field type is EMPTY, so no [Wc_prf] / [Wc_hash] address
    exists at all. *)

Definition wc_pk_adrs (zi : nat * nat) : adrs_sf :=
  address.Wc_pk (anchor_height zi.1) (anchor_index zi.2).

Definition wc_grind_adrs (zi : nat * nat) : adrs_sf :=
  address.Wc_grind (anchor_height zi.1) (anchor_index zi.2).

Definition fxmss_tree_adrs (z i : nat) : adrs_sf :=
  address.Fxmss (anchor_height z) (anchor_index i).

Definition wc_prf_adrs (zi : nat * nat) (chain : nat) : adrs_sf :=
  match Z_lt_dec 0 (Z.of_nat chain_count) with
  | left Hcount =>
      address.Wc_prf (anchor_height zi.1) (anchor_index zi.2)
        (fin_of_nat_or_zero (Z.of_nat chain_count) Hcount chain)
  | right _ => wc_pk_adrs zi
  end.

Definition wc_hash_adrs (zi : nat * nat) (chain pos : nat) : adrs_sf :=
  match Z_lt_dec 0 (Z.of_nat chain_count),
        Z_lt_dec 0 (Z.of_nat pos_bound) with
  | left Hcount, left Hpos =>
      address.Wc_hash (anchor_height zi.1) (anchor_index zi.2)
        (fin_of_nat_or_zero (Z.of_nat chain_count) Hcount chain)
        (fin_of_nat_or_zero (Z.of_nat pos_bound) Hpos pos)
  | _, _ => wc_pk_adrs zi
  end.

(* ------------------------------------------------------------------ *)
(** ** The seven stateless smart constructors, SL_ rows

    The hypertree anchor [(layer, tree_address)] replaces the stateful
    [(node_height, node_index)]; every remaining field bound is a
    [Model.address] spec constant, so none of these needs a positivity
    guard.  No consumer yet -- the hypertree driver extends this facade
    rather than minting a second one. *)

Definition tw_hash_adrs (lt : nat * nat) (kp chain pos : nat) : adrs_sf :=
  address.Tw_hash (anchor_layer lt.1) (anchor_index lt.2)
    (sub_leaf kp) (tw_chain chain) (tw_pos pos).

Definition tw_prf_adrs (lt : nat * nat) (kp chain : nat) : adrs_sf :=
  address.Tw_prf (anchor_layer lt.1) (anchor_index lt.2)
    (sub_leaf kp) (tw_chain chain).

Definition tw_pk_adrs (lt : nat * nat) (kp : nat) : adrs_sf :=
  address.Tw_pk (anchor_layer lt.1) (anchor_index lt.2) (sub_leaf kp).

Definition fors_roots_adrs (lt : nat * nat) (kp : nat) : adrs_sf :=
  address.Fors_roots (anchor_layer lt.1) (anchor_index lt.2) (sub_leaf kp).

Definition xmss_tree_adrs (lt : nat * nat) (h idx : nat) : adrs_sf :=
  address.Xmss_tree (anchor_layer lt.1) (anchor_index lt.2)
    (xmss_height h) (sub_leaf idx).

Definition fors_tree_adrs (lt : nat * nat) (kp h idx : nat) : adrs_sf :=
  address.Fors_tree (anchor_layer lt.1) (anchor_index lt.2)
    (sub_leaf kp) (fors_height h) (fors_leaf idx).

Definition fors_prf_adrs (lt : nat * nat) (kp idx : nat) : adrs_sf :=
  address.Fors_prf (anchor_layer lt.1) (anchor_index lt.2)
    (sub_leaf kp) (fors_leaf idx).

(* ------------------------------------------------------------------ *)
(** ** Exactness of the stateful placements *)

Lemma wc_pk_adrs_keypair zi :
  anchor_bounded zi -> adrs_keypair (wc_pk_adrs zi) = zi.
Proof.
case: zi => z i [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /wc_pk_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma wc_grind_adrs_keypair zi :
  anchor_bounded zi -> adrs_keypair (wc_grind_adrs zi) = zi.
Proof.
case: zi => z i [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /wc_grind_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma fxmss_tree_adrs_keypair z i :
  anchor_bounded (z, i) -> adrs_keypair (fxmss_tree_adrs z i) = (z, i).
Proof.
move=> [Hz Hi].
rewrite /adrs_keypair /adrs_height /adrs_index /fxmss_tree_adrs /=.
rewrite /anchor_height /anchor_index
  (fin_of_nat_or_zeroE _ _ _ Hz) (fin_of_nat_or_zeroE _ _ _ Hi).
by rewrite !fin_val_of_nat !Nat2Z.id.
Qed.

Lemma wc_prf_adrs_chain zi chain :
  component_bounded chain_count chain ->
  adrs_chain (wc_prf_adrs zi chain) = chain.
Proof.
move=> Hchain.
have Hchain' := Hchain.
rewrite /component_bounded /field_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /adrs_chain /wc_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain) /=.
exact: Nat2Z.id.
Qed.

Lemma wc_hash_adrs_chain zi chain pos :
  component_bounded chain_count chain -> component_bounded pos_bound pos ->
  adrs_chain (wc_hash_adrs zi chain pos) = chain.
Proof.
move=> Hchain Hpos.
have Hchain' := Hchain.
have Hpos' := Hpos.
rewrite /component_bounded /field_bounded in Hchain' Hpos'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
have Hpos0 : (0 < Z.of_nat pos_bound)%Z.
  have := Nat2Z.is_nonneg pos; lia.
rewrite /adrs_chain /wc_hash_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
case: Z_lt_dec => [Hpos0'|Hpos0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain) /=.
exact: Nat2Z.id.
Qed.

Lemma wc_hash_adrs_pos zi chain pos :
  component_bounded chain_count chain -> component_bounded pos_bound pos ->
  adrs_hash (wc_hash_adrs zi chain pos) = pos.
Proof.
move=> Hchain Hpos.
have Hchain' := Hchain.
have Hpos' := Hpos.
rewrite /component_bounded /field_bounded in Hchain' Hpos'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
have Hpos0 : (0 < Z.of_nat pos_bound)%Z.
  have := Nat2Z.is_nonneg pos; lia.
rewrite /adrs_hash /wc_hash_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
case: Z_lt_dec => [Hpos0'|Hpos0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hpos) /=.
exact: Nat2Z.id.
Qed.

Lemma wc_prf_adrsE zi chain
    (Hzi : anchor_bounded zi)
    (Hchain : component_bounded chain_count chain) :
  wc_prf_adrs zi chain =
    address.Wc_prf
      (fin_of_nat 256 zi.1 Hzi.1)
      (fin_of_nat (2 ^ 64) zi.2 Hzi.2)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain).
Proof.
have Hchain' := Hchain.
rewrite /component_bounded /field_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /wc_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (anchor_heightE _ Hzi.1) (anchor_indexE _ Hzi.2).
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain).
congr (address.Wc_prf _ _ _); apply: fin_val_inj;
  by rewrite !fin_val_of_nat.
Qed.

Lemma wc_hash_adrsE zi chain pos
    (Hzi : anchor_bounded zi)
    (Hchain : component_bounded chain_count chain)
    (Hpos : component_bounded pos_bound pos) :
  wc_hash_adrs zi chain pos =
    address.Wc_hash
      (fin_of_nat 256 zi.1 Hzi.1)
      (fin_of_nat (2 ^ 64) zi.2 Hzi.2)
      (fin_of_nat (Z.of_nat chain_count) chain Hchain)
      (fin_of_nat (Z.of_nat pos_bound) pos Hpos).
Proof.
have Hchain' := Hchain.
have Hpos' := Hpos.
rewrite /component_bounded /field_bounded in Hchain' Hpos'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
have Hpos0 : (0 < Z.of_nat pos_bound)%Z.
  have := Nat2Z.is_nonneg pos; lia.
rewrite /wc_hash_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
case: Z_lt_dec => [Hpos0'|Hpos0']; last by lia.
rewrite (anchor_heightE _ Hzi.1) (anchor_indexE _ Hzi.2).
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain)
  (fin_of_nat_or_zeroE _ _ _ Hpos).
congr (address.Wc_hash _ _ _ _); apply: fin_val_inj;
  by rewrite !fin_val_of_nat.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Injectivity, arm by arm

    Each lemma is exactly "the components that were placed exactly are
    recoverable": the range hypotheses are the ones under which
    [fin_of_nat_or_zero] is exact, and nothing more. *)

Lemma wc_pk_adrs_inj z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  wc_pk_adrs (z, i) = wc_pk_adrs (z', i') -> z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 adrs_keypair H).
rewrite (wc_pk_adrs_keypair (z, i) Hz) (wc_pk_adrs_keypair (z', i') Hz').
by case.
Qed.

Lemma wc_grind_adrs_inj z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  wc_grind_adrs (z, i) = wc_grind_adrs (z', i') -> z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 adrs_keypair H).
rewrite (wc_grind_adrs_keypair (z, i) Hz) (wc_grind_adrs_keypair (z', i') Hz').
by case.
Qed.

Lemma fxmss_tree_adrs_inj z i z' i' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  fxmss_tree_adrs z i = fxmss_tree_adrs z' i' -> z = z' /\ i = i'.
Proof.
move=> Hz Hz' H.
move: (congr1 adrs_keypair H).
rewrite (fxmss_tree_adrs_keypair z i Hz) (fxmss_tree_adrs_keypair z' i' Hz').
by case.
Qed.

Lemma wc_prf_adrs_inj z i c z' i' c' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  component_bounded chain_count c ->
  component_bounded chain_count c' ->
  wc_prf_adrs (z, i) c = wc_prf_adrs (z', i') c' ->
  [/\ z = z', i = i' & c = c'].
Proof.
move=> Hz Hz' Hc Hc' H.
rewrite (wc_prf_adrsE (z, i) c Hz Hc)
  (wc_prf_adrsE (z', i') c' Hz' Hc') in H.
injection H => Hcf Hif Hzf.
by split; apply: Nat2Z.inj.
Qed.

Lemma wc_hash_adrs_inj z i c p z' i' c' p' :
  anchor_bounded (z, i) -> anchor_bounded (z', i') ->
  component_bounded chain_count c ->
  component_bounded pos_bound p ->
  component_bounded chain_count c' ->
  component_bounded pos_bound p' ->
  wc_hash_adrs (z, i) c p = wc_hash_adrs (z', i') c' p' ->
  [/\ z = z', i = i', c = c' & p = p'].
Proof.
move=> Hz Hz' Hc Hp Hc' Hp' H.
rewrite (wc_hash_adrsE (z, i) c p Hz Hc Hp)
  (wc_hash_adrsE (z', i') c' p' Hz' Hc' Hp') in H.
injection H => Hpf Hcf Hif Hzf.
by split; apply: Nat2Z.inj.
Qed.

(** The two guarded arms against an ARBITRARY [fin] field pinned only by
    its value -- the shape a [Model]-side fold hands over, where the
    field was built from whichever range proof that fold had.  (The
    anchor slots stay in placer form: they are the same term on both
    sides of every use.) *)
Lemma wc_prf_adrs_finE zi chain (ci : fin (Z.of_nat chain_count)) :
  component_bounded chain_count chain -> fin_val ci = Z.of_nat chain ->
  wc_prf_adrs zi chain
  = address.Wc_prf (anchor_height zi.1) (anchor_index zi.2) ci.
Proof.
move=> Hchain Hci.
have Hchain' := Hchain.
rewrite /component_bounded /field_bounded in Hchain'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
rewrite /wc_prf_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain).
congr (address.Wc_prf _ _ _).
by apply: fin_val_inj; rewrite fin_val_of_nat Hci.
Qed.

Lemma wc_hash_adrs_finE zi chain pos
    (ci : fin (Z.of_nat chain_count)) (cp : fin (Z.of_nat pos_bound)) :
  component_bounded chain_count chain -> component_bounded pos_bound pos ->
  fin_val ci = Z.of_nat chain -> fin_val cp = Z.of_nat pos ->
  wc_hash_adrs zi chain pos
  = address.Wc_hash (anchor_height zi.1) (anchor_index zi.2) ci cp.
Proof.
move=> Hchain Hpos Hci Hcp.
have Hchain' := Hchain.
have Hpos' := Hpos.
rewrite /component_bounded /field_bounded in Hchain' Hpos'.
have Hcount0 : (0 < Z.of_nat chain_count)%Z.
  have := Nat2Z.is_nonneg chain; lia.
have Hpos0 : (0 < Z.of_nat pos_bound)%Z.
  have := Nat2Z.is_nonneg pos; lia.
rewrite /wc_hash_adrs.
case: Z_lt_dec => [Hcount0'|Hcount0']; last by lia.
case: Z_lt_dec => [Hpos0'|Hpos0']; last by lia.
rewrite (fin_of_nat_or_zeroE _ _ _ Hchain) (fin_of_nat_or_zeroE _ _ _ Hpos).
congr (address.Wc_hash _ _ _ _); apply: fin_val_inj;
  by rewrite fin_val_of_nat ?Hci ?Hcp.
Qed.

(** Same-anchor component injectivity of the two guarded arms: with the
    anchor held FIXED (the shape every per-hash-call tweak of one WOTS+C
    instance has), the chain index and position are recoverable with no
    hypothesis on the anchor at all. *)
Lemma wc_hash_adrs_component_inj zi c p c' p' :
  component_bounded chain_count c -> component_bounded pos_bound p ->
  component_bounded chain_count c' -> component_bounded pos_bound p' ->
  wc_hash_adrs zi c p = wc_hash_adrs zi c' p' -> c = c' /\ p = p'.
Proof.
move=> Hc Hp Hc' Hp' H.
split.
- by rewrite -(wc_hash_adrs_chain zi c p Hc Hp)
             -(wc_hash_adrs_chain zi c' p' Hc' Hp') H.
- by rewrite -(wc_hash_adrs_pos zi c p Hc Hp)
             -(wc_hash_adrs_pos zi c' p' Hc' Hp') H.
Qed.

Lemma wc_prf_adrs_component_inj zi c c' :
  component_bounded chain_count c -> component_bounded chain_count c' ->
  wc_prf_adrs zi c = wc_prf_adrs zi c' -> c = c'.
Proof.
move=> Hc Hc' H.
by rewrite -(wc_prf_adrs_chain zi c Hc) -(wc_prf_adrs_chain zi c' Hc') H.
Qed.

Lemma tw_hash_adrs_inj l t kp c p l' t' kp' c' p' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  field_bounded address.len_tw c -> field_bounded address.len_tw c' ->
  field_bounded address.w_tw_pred p -> field_bounded address.w_tw_pred p' ->
  tw_hash_adrs (l, t) kp c p = tw_hash_adrs (l', t') kp' c' p' ->
  [/\ l = l', t = t', kp = kp', c = c' & p = p'].
Proof.
move=> [hl ht] [hl' ht'] hkp hkp' hc hc' hp hp' hE.
rewrite /tw_hash_adrs in hE.
injection hE => ep ec ekp et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: sub_leaf_inj hkp hkp' ekp.
- exact: tw_chain_inj hc hc' ec.
- exact: tw_pos_inj hp hp' ep.
Qed.

Lemma tw_prf_adrs_inj l t kp c l' t' kp' c' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  field_bounded address.len_tw c -> field_bounded address.len_tw c' ->
  tw_prf_adrs (l, t) kp c = tw_prf_adrs (l', t') kp' c' ->
  [/\ l = l', t = t', kp = kp' & c = c'].
Proof.
move=> [hl ht] [hl' ht'] hkp hkp' hc hc' hE.
rewrite /tw_prf_adrs in hE.
injection hE => ec ekp et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: sub_leaf_inj hkp hkp' ekp.
- exact: tw_chain_inj hc hc' ec.
Qed.

Lemma tw_pk_adrs_inj l t kp l' t' kp' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  tw_pk_adrs (l, t) kp = tw_pk_adrs (l', t') kp' ->
  [/\ l = l', t = t' & kp = kp'].
Proof.
move=> [hl ht] [hl' ht'] hkp hkp' hE.
rewrite /tw_pk_adrs in hE.
injection hE => ekp et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: sub_leaf_inj hkp hkp' ekp.
Qed.

Lemma fors_roots_adrs_inj l t kp l' t' kp' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  fors_roots_adrs (l, t) kp = fors_roots_adrs (l', t') kp' ->
  [/\ l = l', t = t' & kp = kp'].
Proof.
move=> [hl ht] [hl' ht'] hkp hkp' hE.
rewrite /fors_roots_adrs in hE.
injection hE => ekp et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: sub_leaf_inj hkp hkp' ekp.
Qed.

Lemma xmss_tree_adrs_inj l t h idx l' t' h' idx' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.h_xmss h -> field_bounded address.h_xmss h' ->
  field_bounded address.sub_leaves idx -> field_bounded address.sub_leaves idx' ->
  xmss_tree_adrs (l, t) h idx = xmss_tree_adrs (l', t') h' idx' ->
  [/\ l = l', t = t', h = h' & idx = idx'].
Proof.
move=> [hl ht] [hl' ht'] hh hh' hi hi' hE.
rewrite /xmss_tree_adrs in hE.
injection hE => eidx eh et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: xmss_height_inj hh hh' eh.
- exact: sub_leaf_inj hi hi' eidx.
Qed.

Lemma fors_tree_adrs_inj l t kp h idx l' t' kp' h' idx' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  field_bounded address.h_fors h -> field_bounded address.h_fors h' ->
  field_bounded address.fors_idx idx -> field_bounded address.fors_idx idx' ->
  fors_tree_adrs (l, t) kp h idx = fors_tree_adrs (l', t') kp' h' idx' ->
  [/\ l = l', t = t', kp = kp', h = h' & idx = idx'].
Proof.
move=> [hl ht] [hl' ht'] hkp hkp' hh hh' hi hi' hE.
rewrite /fors_tree_adrs in hE.
injection hE => eidx eh ekp et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: sub_leaf_inj hkp hkp' ekp.
- exact: fors_height_inj hh hh' eh.
- exact: fors_leaf_inj hi hi' eidx.
Qed.

Lemma fors_prf_adrs_inj l t kp idx l' t' kp' idx' :
  hypertree_bounded (l, t) -> hypertree_bounded (l', t') ->
  field_bounded address.sub_leaves kp -> field_bounded address.sub_leaves kp' ->
  field_bounded address.fors_idx idx -> field_bounded address.fors_idx idx' ->
  fors_prf_adrs (l, t) kp idx = fors_prf_adrs (l', t') kp' idx' ->
  [/\ l = l', t = t', kp = kp' & idx = idx'].
Proof.
move=> [hl ht] [hl' ht'] hkp hkp' hi hi' hE.
rewrite /fors_prf_adrs in hE.
injection hE => eidx ekp et el.
split.
- exact: anchor_layer_inj hl hl' el.
- exact: anchor_index_inj ht ht' et.
- exact: sub_leaf_inj hkp hkp' ekp.
- exact: fors_leaf_inj hi hi' eidx.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pairwise-disjoint address classes

    Distinct constructors are distinct addresses UNCONDITIONALLY (no
    range hypotheses): the type tag alone separates the arms. *)

Lemma wc_grind_adrs_neq_fxmss_tree zi z i :
  wc_grind_adrs zi <> fxmss_tree_adrs z i.
Proof. by []. Qed.

Lemma wc_grind_adrs_neq_wc_pk zi zi' :
  wc_grind_adrs zi <> wc_pk_adrs zi'.
Proof. by []. Qed.

Lemma fxmss_tree_adrs_neq_wc_pk z i zi :
  fxmss_tree_adrs z i <> wc_pk_adrs zi.
Proof. by []. Qed.

End AdrsFacade.

Set Warnings "redundant-canonical-projection".

(** The two field bounds are recovered from the address type at every
    call site, so they are implicit everywhere below the facade. *)
Arguments adrs_type {chain_count w} _.
Arguments adrs_height {chain_count w} _.
Arguments adrs_index {chain_count w} _.
Arguments adrs_kp {chain_count w} _.
Arguments adrs_chain {chain_count w} _.
Arguments adrs_hash {chain_count w} _.
Arguments adrs_keypair {chain_count w} _.
Arguments wc_pk_adrs {chain_count w} _.
Arguments wc_grind_adrs {chain_count w} _.
Arguments fxmss_tree_adrs {chain_count w} _ _.
Arguments wc_prf_adrs {chain_count w} _ _.
Arguments wc_hash_adrs {chain_count w} _ _ _.
Arguments tw_hash_adrs {chain_count w} _ _ _ _.
Arguments tw_prf_adrs {chain_count w} _ _ _.
Arguments tw_pk_adrs {chain_count w} _ _.
Arguments fors_roots_adrs {chain_count w} _ _.
Arguments xmss_tree_adrs {chain_count w} _ _ _.
Arguments fors_tree_adrs {chain_count w} _ _ _ _.
Arguments fors_prf_adrs {chain_count w} _ _ _.

Arguments encode_adrs : simpl never.
Arguments decode_adrs : simpl never.
Arguments adrs_sf_ch : simpl never.
