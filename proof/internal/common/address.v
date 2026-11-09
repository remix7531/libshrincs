(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * model.address: the SHRINCS 22-byte ADRS, as a reachable-states type.

    SHRINCS uses one 22-byte address format for every tweakable-hash
    call, shared across every scheme in the family (WOTS+C, WOTS-TW,
    XMSS, FXMSS, FORS, the SPHINCS+ hypertree). Two families of type
    tag select the anchor's meaning:

      stateless (SL_*, along the SPHINCS+ hypertree):
        layer(1) || tree_address(8, BE) || type(1) || payload(12)
      stateful (SF_*, along the FXMSS leaf):
        node_height(1) || node_index(8, BE) || type(1) || payload(12)

    Both layouts are byte-for-byte identical -- {1-byte anchor tag,
    8-byte BE anchor index, 1-byte type, 12-byte payload}.

    Unlike the earlier flat record of truncating machine ints, [adrs]
    is now a **dependent tagged union**: one constructor per ADRS type,
    each field a Z-bounded ordinal ([model.fin]) at its spec-tight
    bound.  Illegal states (a chain index past [chain_count], a payload
    slot set on a type whose row leaves it zero, an out-of-family type
    tag) are unrepresentable, and field / tweak injectivity is
    intrinsic -- discharged once at the type boundary rather than
    re-proved downstream.

    Two views coexist:
    - the CONSTRUCTORS (typed, reachable-states) are how the model and
      the security proof build and reason about addresses;
    - the flat 6-field [Z] projections ([adrs_anchor_tag_z] ...
      [payload_c_z]) recover the wire layout, so [adrs_bytes] keeps its
      byte-for-byte serialize shape and the C-refinement's byte-splice
      reasoning re-derives against the same concatenation.

    Consumers that only need the WOTS+C anchor read it back with the
    [adrs_nh]/[adrs_ni] fin-projections; the smart
    constructors ([shrincs_wots_*_adrs]) take an [adrs] anchor carrier
    (matching the C's "prefill the anchor, then type it" convention)
    and rebuild the typed sibling from those projections.

    Definitions only -- no lemmas. Facts live in [model.theory.address]. *)

From Stdlib Require Import List ZArith Lia.
From Shrincs.internal.common Require Export byte fin.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** ADRS type tags (shrincs.py "ADRS type flags").

    The stateless (SL_) and stateful (SF_) type ranges are disjoint, so
    the type byte alone disambiguates the anchor interpretation. Kept as
    [byte] (they are the on-wire type byte) -- [adrs_type] returns one
    per constructor. *)

(** Stateless tags: along the SPHINCS+ hypertree. *)
Definition SL_WOTS_TW_HASH : byte := byte_of 0 ltac:(lia).
Definition SL_WOTS_TW_PK   : byte := byte_of 1 ltac:(lia).
Definition SL_XMSS_TREE    : byte := byte_of 2 ltac:(lia).
Definition SL_FORS_TREE    : byte := byte_of 3 ltac:(lia).
Definition SL_FORS_ROOTS   : byte := byte_of 4 ltac:(lia).
Definition SL_WOTS_TW_PRF  : byte := byte_of 5 ltac:(lia).
Definition SL_FORS_PRF     : byte := byte_of 6 ltac:(lia).

(** Stateful tags: along the FXMSS leaf. *)
Definition SF_SHRINCS_WOTS_HASH  : byte := byte_of 16 ltac:(lia).
Definition SF_SHRINCS_WOTS_PK    : byte := byte_of 17 ltac:(lia).
Definition SF_FXMSS_TREE         : byte := byte_of 18 ltac:(lia).
Definition SF_SHRINCS_WOTS_PRF   : byte := byte_of 21 ltac:(lia).
Definition SF_SHRINCS_WOTS_GRIND : byte := byte_of 22 ltac:(lia).

(* ================================================================= *)
(** ** Stateless (hypertree) field-bound constants.

    The stateless ADRS arms below encode the SPHINCS+-style hypertree of
    SHRINCS (WOTS-TW leaves, XMSS subtrees, a FORS forest). Each names
    the EXCLUSIVE [fin] bound of one field (the field's value is [<] the
    constant), documenting every magic number at one site and turning
    the eventual parameterization (with the hypertree driver) into a
    find-replace.  Beware the two shapes: for count-shaped fields the
    bound IS the spec parameter (a chain index is [< chain count]); for
    height-shaped fields it is the parameter PLUS ONE (a node height
    ranges [0 .. height] inclusive).  Spec values (shrincs.py):
    SPHX_LAYER_COUNT = 5, SPHX_XMSS_HEIGHT = 9, SPHX_FORS_HEIGHT = 13,
    SPHX_FORS_COUNT = 10, WOTS_TW_CHAIN_COUNT = 35, w = 16.
    The constants are plain [Z] (the [fin] bound type) and transparent,
    so [fin] fields over them stay definitionally equal to the raw
    literals -- [lia], however, does not unfold them, so range proofs
    [unfold] first. *)
Definition hypertree_layers : Z := 6.       (* layer bound [= SPHX_LAYER_COUNT + 1 = 6];
                                          "the topmost layer is at layer
                                          SPHX_LAYER_COUNT" (../shrincs-bip/SHRINCS.md:159),
                                          and SPHX_LAYER_COUNT = 5 (shrincs.py), so
                                          layer ranges 0..5 inclusive = 6 values -- a
                                          documented deviation from SPHINCS+/FIPS-205,
                                          which bounds layer strictly below d *)
Definition sub_leaves  : Z := 512.     (* leaf-index bound   [= 2^(h/d) = 2^9]     *)
Definition len_tw      : Z := 35.      (* chain-index bound  [= chain count len]   *)
Definition w_tw_pred   : Z := 15.      (* hash-pos bound     [= w - 1]             *)
Definition h_xmss      : Z := 10.      (* node-height bound  [= h/d + 1 = 9 + 1]   *)
Definition h_fors      : Z := 14.      (* node-height bound  [= a + 1 = 13 + 1]    *)
Definition fors_idx    : Z := 81920.   (* leaf-index bound   [= k * 2^a = 10*2^13] *)

(* ================================================================= *)
(** ** [ly_nh]: widen a stateless [layer] ([< 6]) to the anchor-tag
    ordinal ([< 256]).  Defined BEFORE [Section AddrParams] so its [lia]
    proof cannot capture the section's positivity hypotheses (which would
    otherwise pollute every [adrs_nh]-using accessor with spurious
    [0 < chain_count] / [0 < pos_bound] arguments). It mentions neither
    [adrs] nor the section parameters. *)
Lemma fin6_lt_256 (ly : fin hypertree_layers) : 0 <= fin_val ly < 256.
Proof. pose proof (fin_range ly); unfold hypertree_layers in *; lia. Qed.
Definition ly_nh (ly : fin hypertree_layers) : fin 256 := fin_of_Z 256 (fin_val ly) (fin6_lt_256 ly).

(* ================================================================= *)
(** ** The ADRS, as a dependent union over [fin].

    Field bounds are spec-tight (from shrincs-bip): stateful anchor =
    [node_height < 256], [node_index < 2^64]; stateless anchor =
    [layer < hypertree_layers], [tree_address < 2^64]; the WOTS+C chain index
    and position bounds are the section parameters [chain_count] and
    [pos_bound] (instantiated to [len = 32] and [w-1 = 15] downstream in
    [model.wots]); the stateless field bounds are the named constants
    above ([sub_leaves], [len_tw], [w_tw_pred], [h_xmss], [h_fors],
    [fors_idx]).

    The WOTS+C chain/position bounds are kept PARAMETRIC (a section over
    [chain_count] / [pos_bound]; [pos_bound] carries a positivity
    hypothesis so [shrincs_wots_hash_adrs]'s zero-position default is
    well-typed); every other field bound stays a concrete literal. *)

Section AddrParams.
Variables chain_count pos_bound : nat.
Hypothesis Hpb : (0 < pos_bound)%nat.

Inductive adrs :=
  (* stateful WOTS+C -- the arms this repo's proofs exercise *)
  | Wc_hash  (nh : fin 256) (ni : fin (2^64)) (chain : fin (Z.of_nat chain_count)) (pos : fin (Z.of_nat pos_bound))
  | Wc_prf   (nh : fin 256) (ni : fin (2^64)) (chain : fin (Z.of_nat chain_count))
  | Wc_pk    (nh : fin 256) (ni : fin (2^64))
  | Wc_grind (nh : fin 256) (ni : fin (2^64))
  | Fxmss    (nh : fin 256) (ni : fin (2^64))
  (* stateless -- spec-tight bounds, defined for completeness (no
     consumers until the hypertree driver lands) *)
  | Tw_hash    (ly : fin hypertree_layers) (tr : fin (2^64)) (kp : fin sub_leaves) (chain : fin len_tw) (hash : fin w_tw_pred)
  | Tw_prf     (ly : fin hypertree_layers) (tr : fin (2^64)) (kp : fin sub_leaves) (chain : fin len_tw)
  | Tw_pk      (ly : fin hypertree_layers) (tr : fin (2^64)) (kp : fin sub_leaves)
  | Fors_roots (ly : fin hypertree_layers) (tr : fin (2^64)) (kp : fin sub_leaves)
  | Xmss_tree  (ly : fin hypertree_layers) (tr : fin (2^64)) (h : fin h_xmss) (idx : fin sub_leaves)
  | Fors_tree  (ly : fin hypertree_layers) (tr : fin (2^64)) (kp : fin sub_leaves) (h : fin h_fors) (idx : fin fors_idx)
  | Fors_prf   (ly : fin hypertree_layers) (tr : fin (2^64)) (kp : fin sub_leaves) (idx : fin fors_idx).

(** Decidable equality: [decide equality] over the constructors, each
    field discharged by [fin_eq_dec]. Constructor injectivity is free
    ([injection]). *)
Definition adrs_eq_dec (a b : adrs) : {a = b} + {a <> b}.
Proof. decide equality; apply fin_eq_dec. Defined.

(* ================================================================= *)
(** ** The flat 6-field [Z] view (recovers the wire layout).

    [adrs_type] is the type byte; the other five are the [Z] value of
    each wire field (anchor tag / index, then payload words w0/w1/w2),
    zero where the type's row leaves the slot unused.  Named [adrs_type]
    (rather than e.g. [tag]) because that is the name the C-refinement
    compares against the type-tag constants. *)

Definition adrs_type (a : adrs) : byte :=
  match a with
  | Wc_hash _ _ _ _   => SF_SHRINCS_WOTS_HASH
  | Wc_prf _ _ _      => SF_SHRINCS_WOTS_PRF
  | Wc_pk _ _         => SF_SHRINCS_WOTS_PK
  | Wc_grind _ _      => SF_SHRINCS_WOTS_GRIND
  | Fxmss _ _         => SF_FXMSS_TREE
  | Tw_hash _ _ _ _ _ => SL_WOTS_TW_HASH
  | Tw_prf _ _ _ _    => SL_WOTS_TW_PRF
  | Tw_pk _ _ _       => SL_WOTS_TW_PK
  | Fors_roots _ _ _  => SL_FORS_ROOTS
  | Xmss_tree _ _ _ _ => SL_XMSS_TREE
  | Fors_tree _ _ _ _ _ => SL_FORS_TREE
  | Fors_prf _ _ _ _  => SL_FORS_PRF
  end.

Definition adrs_anchor_tag_z (a : adrs) : Z :=
  match a with
  | Wc_hash nh _ _ _ | Wc_prf nh _ _ | Wc_pk nh _ | Wc_grind nh _ | Fxmss nh _ => fin_val nh
  | Tw_hash ly _ _ _ _ | Tw_prf ly _ _ _ | Tw_pk ly _ _ | Fors_roots ly _ _
  | Xmss_tree ly _ _ _ | Fors_tree ly _ _ _ _ | Fors_prf ly _ _ _ => fin_val ly
  end.

Definition adrs_anchor_idx_z (a : adrs) : Z :=
  match a with
  | Wc_hash _ ni _ _ | Wc_prf _ ni _ | Wc_pk _ ni | Wc_grind _ ni | Fxmss _ ni => fin_val ni
  | Tw_hash _ tr _ _ _ | Tw_prf _ tr _ _ | Tw_pk _ tr _ | Fors_roots _ tr _
  | Xmss_tree _ tr _ _ | Fors_tree _ tr _ _ _ | Fors_prf _ tr _ _ => fin_val tr
  end.

(** Payload word 0 (bytes 10-13): keypair index where a row uses one,
    else zero. *)
Definition payload_a_z (a : adrs) : Z :=
  match a with
  | Tw_hash _ _ kp _ _ | Tw_prf _ _ kp _ | Tw_pk _ _ kp | Fors_roots _ _ kp
  | Fors_tree _ _ kp _ _ | Fors_prf _ _ kp _ => fin_val kp
  | _ => 0
  end.

(** Payload word 1 (bytes 14-17): chain index / tree height. *)
Definition payload_b_z (a : adrs) : Z :=
  match a with
  | Wc_hash _ _ chain _ | Wc_prf _ _ chain => fin_val chain
  | Tw_hash _ _ _ chain _ | Tw_prf _ _ _ chain => fin_val chain
  | Xmss_tree _ _ h _ | Fors_tree _ _ _ h _ => fin_val h
  | _ => 0
  end.

(** Payload word 2 (bytes 18-21): hash position / tree index. *)
Definition payload_c_z (a : adrs) : Z :=
  match a with
  | Wc_hash _ _ _ pos => fin_val pos
  | Tw_hash _ _ _ _ hash => fin_val hash
  | Xmss_tree _ _ _ idx | Fors_tree _ _ _ _ idx | Fors_prf _ _ _ idx => fin_val idx
  | _ => 0
  end.

(* ================================================================= *)
(** ** [to_byte(x, y)]: big-endian [y]-byte encoding of [x]. *)

Fixpoint to_byte (x : Z) (y : nat) : list byte :=
  match y with
  | O    => []
  | S y' => to_byte (x / 256) y' ++ [byte_mod256 x]
  end.

(** Serialize an ADRS to its 22-byte wire form -- same concatenation
    shape as the old flat record, now driven by the [Z] projections. *)
Definition adrs_bytes (a : adrs) : list byte :=
  to_byte (adrs_anchor_tag_z a) 1 ++
  to_byte (adrs_anchor_idx_z a) 8 ++
  to_byte (adrs_type a)         1 ++
  to_byte (payload_a_z a)       4 ++
  to_byte (payload_b_z a)       4 ++
  to_byte (payload_c_z a)       4.

(* ================================================================= *)
(** ** WOTS+C anchor / field projections (fin-valued).

    The WOTS+C algorithms read the anchor back off a carrier [adrs] to
    build the typed siblings. On the five stateful WOTS+C arms these are
    exact; on any other arm they return a zero default (never reached on
    the WOTS+C path). *)

(** Widen the stateless [layer] field ([< 6]) into the anchor-tag
    ordinal ([< 256]), so [adrs_nh] is FAITHFUL on every arm: its
    [fin_val] is always exactly [adrs_anchor_tag_z] (see
    [model.theory.address.adrs_nh_tag_z]).  [adrs_ni] is faithful already
    -- the stateless [tree_address] and stateful [node_index] share the
    [fin (2^64)] type.  [ly_nh] / [fin6_lt_256] are defined BEFORE the
    section (they mention neither [adrs] nor the parameters). *)
Definition adrs_nh (a : adrs) : fin 256 :=
  match a with
  | Wc_hash nh _ _ _ | Wc_prf nh _ _ | Wc_pk nh _ | Wc_grind nh _ | Fxmss nh _ => nh
  | Tw_hash ly _ _ _ _ | Tw_prf ly _ _ _ | Tw_pk ly _ _ | Fors_roots ly _ _
  | Xmss_tree ly _ _ _ | Fors_tree ly _ _ _ _ | Fors_prf ly _ _ _ => ly_nh ly
  end.

Definition adrs_ni (a : adrs) : fin (2^64) :=
  match a with
  | Wc_hash _ ni _ _ | Wc_prf _ ni _ | Wc_pk _ ni | Wc_grind _ ni | Fxmss _ ni => ni
  | Tw_hash _ tr _ _ _ | Tw_prf _ tr _ _ | Tw_pk _ tr _ | Fors_roots _ tr _
  | Xmss_tree _ tr _ _ | Fors_tree _ tr _ _ _ | Fors_prf _ tr _ _ => tr
  end.

(* ================================================================= *)
(** ** WOTS+C smart constructors.

    Each takes an [adrs] anchor carrier (the WOTS+C keypair location,
    prefilled by the caller as in shrincs.py) and rebuilds the typed
    sibling from its [adrs_nh]/[adrs_ni] anchor, per that type's row.

    The chain index / position are now taken as bound-carrying [fin]
    fields directly (no [nat -> fin] clamp): every caller has the bound
    in hand -- the VST funspecs (chain index [< chain_count = 32],
    position [< w-1 = 15]), the model's own [chain_iter] (dependent
    Fixpoint), and the SSProve fold via its boundary totalizer
    ([Sec.addressing.chain_of_nat] / [pos_of_nat]).  So the model is
    exactly reachable-states: an illegal (out-of-range) chain/position
    is unrepresentable, not merely never built. *)

(** SF_SHRINCS_WOTS_HASH: chain index [chain], position 0 (chaining sets it). *)
Definition shrincs_wots_hash_adrs (a : adrs) (chain : fin (Z.of_nat chain_count)) : adrs :=
  Wc_hash (adrs_nh a) (adrs_ni a) chain (fin_of_Z (Z.of_nat pos_bound) 0 ltac:(lia)).

(** SF_SHRINCS_WOTS_PK. *)
Definition shrincs_wots_pk_adrs (a : adrs) : adrs :=
  Wc_pk (adrs_nh a) (adrs_ni a).

(** SF_SHRINCS_WOTS_PRF: chain index [chain]. *)
Definition shrincs_wots_prf_adrs (a : adrs) (chain : fin (Z.of_nat chain_count)) : adrs :=
  Wc_prf (adrs_nh a) (adrs_ni a) chain.

(** SF_SHRINCS_WOTS_GRIND. *)
Definition shrincs_wots_grind_adrs (a : adrs) : adrs :=
  Wc_grind (adrs_nh a) (adrs_ni a).

(** Set the WOTS+C chain position (the only field the chain iteration
    varies); identity on any non-hash arm. *)
Definition set_hash_pos (a : adrs) (pos : fin (Z.of_nat pos_bound)) : adrs :=
  match a with
  | Wc_hash nh ni chain _ => Wc_hash nh ni chain pos
  | _ => a
  end.

End AddrParams.

(** Make the two section parameters ([chain_count]/[pos_bound]) IMPLICIT
    on every discharged constructor and accessor, so downstream [match]
    patterns and accessor calls resolve them from the [adrs] argument and
    stay textually unchanged.  The type constructor [adrs] itself keeps
    its parameters EXPLICIT (so [adrs len w_pred] is writable). *)
Arguments Wc_hash {chain_count pos_bound}.
Arguments Wc_prf {chain_count pos_bound}.
Arguments Wc_pk {chain_count pos_bound}.
Arguments Wc_grind {chain_count pos_bound}.
Arguments Fxmss {chain_count pos_bound}.
Arguments Tw_hash {chain_count pos_bound}.
Arguments Tw_prf {chain_count pos_bound}.
Arguments Tw_pk {chain_count pos_bound}.
Arguments Fors_roots {chain_count pos_bound}.
Arguments Xmss_tree {chain_count pos_bound}.
Arguments Fors_tree {chain_count pos_bound}.
Arguments Fors_prf {chain_count pos_bound}.
Arguments adrs_eq_dec {chain_count pos_bound}.
Arguments adrs_type {chain_count pos_bound}.
Arguments adrs_anchor_tag_z {chain_count pos_bound}.
Arguments adrs_anchor_idx_z {chain_count pos_bound}.
Arguments payload_a_z {chain_count pos_bound}.
Arguments payload_b_z {chain_count pos_bound}.
Arguments payload_c_z {chain_count pos_bound}.
Arguments adrs_bytes {chain_count pos_bound}.
Arguments adrs_nh {chain_count pos_bound}.
Arguments adrs_ni {chain_count pos_bound}.
Arguments shrincs_wots_hash_adrs {chain_count pos_bound}.
Arguments shrincs_wots_pk_adrs {chain_count pos_bound}.
Arguments shrincs_wots_prf_adrs {chain_count pos_bound}.
Arguments shrincs_wots_grind_adrs {chain_count pos_bound}.
Arguments set_hash_pos {chain_count pos_bound}.
