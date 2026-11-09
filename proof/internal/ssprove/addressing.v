(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.addressing

    SSProve-specific structure layered on [Shrincs.internal.common.address]'s dependent
    ADRS: a mathcomp [Finite] instance (needed by mathcomp/SSProve
    machinery) and the encode/decode bridge into a [choice_type] tweak
    space ([th_T]).  [Shrincs.internal.common.address] itself stays Stdlib-only, so this
    file is where the "generic model gets equipped with SSProve-specific
    structure" step happens.

    ** Scheme-neutral core

    This file is the SCHEME-NEUTRAL address core: the flat coproduct
    [adrs_sum] transporting [Finite] onto [adrs_sf], the exact tweak
    space [adrs_sf_ch] with its [encode_adrs]/[decode_adrs] bijection,
    and the anchor smart constructor [anchor_adrs].  None of it mentions
    WOTS+C chains or grinding, so a future scheme (the FXMSS hypertree,
    the stateless SL_* arms already present in [Shrincs.internal.common.address.adrs]) can
    build its own tweaks on top of THIS file without pulling in the
    WOTS+C-specific machinery.  That machinery -- [chain_tweak],
    [prf_tweak], the [shrincs_wots_*_adrs] smart constructors, and their
    conditional index-injectivity lemmas -- lives in
    [Shrincs.internal.ssprove.wots.addressing], which imports this file.

    The WOTS+C address is parametric in [chain_count] (= [len]) and
    [pos_bound] (= [w-1]); this file's own [Section WcTweak] still
    carries those two parameters (with positivity hypotheses [Hcc]/[Hw]
    in scope, even though nothing defined here needs the positivity
    facts) purely because [adrs_sf := address.adrs chain_count (w.-1)]
    is the single shared dependent-union type every scheme's addresses
    live in -- [adrs_sf]'s bounds happen to equal the WOTS+C games'
    [chain_count] and [w.-1] EXACTLY (no decode clamp, no "<= 32"
    bridge), but that is a fact about [adrs_sf]'s TYPE, not about any
    definition below depending on chain/position VALUES.

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
    genuine two-sided inverse, so every address round-trips and the
    junk-decode branch of the old flat tuple is gone entirely.

    [anchor_adrs] builds the [(zstar, istar)]-anchored [Wc_pk] carrier
    EXACTLY via [fin_of_nat]; a scheme's own smart constructors read the
    anchor back off it (see [Shrincs.internal.ssprove.wots.addressing.shrincs_wots_chain_adrs]
    for the WOTS+C ones) to derive their sibling addresses. *)

From HB Require Import structures.
From Shrincs.internal.ssprove.lib Require Import prelude fin_fin.
From Shrincs.internal.common Require address.
From Shrincs.internal.common Require Import byte fin.
From Stdlib Require Import ZArith Lia.

Import PackageNotation.
#[local] Open Scope package_scope.

(* ------------------------------------------------------------------ *)
(** ** Type constants (stateful rows, shrincs-bip values) *)

Definition SF_SHRINCS_WOTS_HASH  : nat := 16.
Definition SF_SHRINCS_WOTS_PK    : nat := 17.
Definition SF_FXMSS_TREE         : nat := 18.
Definition SF_SHRINCS_WOTS_PRF   : nat := 21.
Definition SF_SHRINCS_WOTS_GRIND : nat := 22.

(** A small bridge: a mathcomp [ltn] fact lifts to a [Z] one. *)
Lemma natZ_lt (a b : nat) : (a < b)%nat -> (Z.of_nat a < Z.of_nat b)%Z.
Proof. move/ltP => h; lia. Qed.

(** ** Anchor-field range predicates.

    The two ADRS-anchor slots are a 1-byte height ([< 256]) and an
    8-byte node index ([< 2^64]); [anchor_adrs] needs a [Z]-side bound
    proof for each to build its [fin] fields EXACTLY (no clamp).  These
    named predicates are the interface the games thread down: because
    they wrap the [Z] arithmetic, the mathcomp-heavy games can state /
    carry the anchor bounds WITHOUT importing [ZArith] (which would
    shadow ssrnat's [^]/[<] in [nat_scope]). *)
Definition anchor_tag_bound (n : nat) : Prop := (Z.of_nat n < 256)%Z.
Definition anchor_idx_bound (n : nat) : Prop := (Z.of_nat n < 2 ^ 64)%Z.

Lemma anchor_tag_bound_lt (n : nat) : (n < 256)%nat -> anchor_tag_bound n.
Proof. exact: natZ_lt. Qed.

(* ================================================================== *)
(* [Finite.copy] through [adrs_pK] re-registers the lower structures HB
   already knows, tripping [redundant-canonical-projection] at the
   instance and at [End WcTweak] -- inherent to the idiom (mathcomp
   itself builds with this warning off).  Scoped off, restored after. *)
Set Warnings "-redundant-canonical-projection".

Section WcTweak.

(** The WOTS+C chain count and Winternitz parameter, with their
    positivity hypotheses (mathcomp [ltn]).  [pos_bound := w.-1] is the
    position field bound.  (Kept in scope for [adrs_sf]'s parametrization
    -- see the file header; [Hcc]/[Hw] are unused below.) *)
Context (chain_count w : nat).
Context (Hcc : (0 < chain_count)%nat) (Hw : (1 < w)%nat).
Local Abbreviation pos_bound := (w.-1).

Local Abbreviation adrs_sf := (address.adrs chain_count pos_bound).

(* ------------------------------------------------------------------ *)
(** ** The mathcomp [Finite] instance on [adrs_sf]

    Transport the finite structure of the flat 12-arm coproduct
    [adrs_sum] along the constructor bijection.  Each [fin b] summand is
    a [finType] via [Shrincs.internal.ssprove.lib.fin_fin] with [b] kept symbolic. *)

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
(** ** Smart constructor from an anchor tuple

    From a global ADRS anchored at the key pair [(zstar, istar)],
    scheme-specific sibling addresses are derived by typing the anchor.
    [anchor_adrs t] is any carrier holding just that anchor; a scheme's
    own smart constructors (e.g.
    [Shrincs.internal.ssprove.wots.addressing.shrincs_wots_chain_adrs]) read it back via
    [adrs_nh]/[adrs_ni] and set their own payload fields. *)

Definition anchor_adrs (t : nat * nat)
    (Htag : (Z.of_nat t.1 < 256)%Z) (Hidx : (Z.of_nat t.2 < 2 ^ 64)%Z) : adrs_sf :=
  address.Wc_pk (fin_of_nat 256 t.1 Htag)
                (fin_of_nat (2 ^ 64) t.2 Hidx).

End WcTweak.

Set Warnings "redundant-canonical-projection".

Arguments encode_adrs : simpl never.
Arguments decode_adrs : simpl never.
Arguments adrs_sf_ch : simpl never.
