(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.lemmas.cancel_hints: fast-fail swap for the cancel db.

    [cancel]'s per-pair attempt is [eauto with nocore cancel] (VST
    floyd/seplog_tactics.v).  The [cancel] hint database carries
    transparency state "none" (all constants opaque), and under that
    state its [Hint Resolve] entries [data_at_cancel] /
    [field_at_cancel] and the four data_at<->field_at bridge lemmas
    head-match a MISmatched pair of conjuncts, bind the array arguments,
    and fail only after expensive unification backtracking.
    The same [simple apply] issued from
    a [Hint Extern] body runs under DEFAULT transparency and fails
    before that backtracking, while the Extern pattern is matched under the
    db's opaque state, so no spurious firing is introduced.

    Do NOT simply remove the six hints: [forward_if] fails without
    [data_at_field_at_cancel], and the loose [_ |-- data_at_] /
    [_ |-- field_at_] Extern patterns are needed for stackframe
    pairs such as
    [data_at_ Tsh (tarray tuchar pk_bytes) p |--
     data_at_ Tsh (tarray tuchar 2048) p]
    (a tight [field_at_ ...] pattern never matches a [data_at_]
    LHS under the opaque db transparency).

    All hints use [export] locality: they take effect in any file
    that [Require Import]s this module; [contract.lemmas]
    re-exports it, so every verif body gets the swap. *)

From VST Require Import floyd.proofauto.

(* ================================================================= *)
(** ** The six diseased Resolve entries, re-added as guarded Externs. *)
(* ================================================================= *)

#[export] Remove Hints data_at_cancel field_at_cancel
  data_at_field_at_cancel field_at_data_at_cancel : cancel.
#[export] Hint Extern 1 (data_at _ _ _ _ |-- data_at _ _ _ _) =>
  simple apply data_at_cancel : cancel.
#[export] Hint Extern 1 (field_at _ _ _ _ _ |-- field_at _ _ _ _ _) =>
  simple apply field_at_cancel : cancel.
#[export] Hint Extern 1 (data_at _ _ _ _ |-- field_at _ _ _ _ _) =>
  simple apply data_at_field_at_cancel : cancel.
#[export] Hint Extern 1 (field_at _ _ _ _ _ |-- data_at _ _ _ _) =>
  simple apply field_at_data_at_cancel : cancel.
#[export] Remove Hints field_at__data_at__cancel data_at__field_at__cancel : cancel.
#[export] Hint Extern 1 (_ |-- data_at_ _ _ _) =>
  simple apply field_at__data_at__cancel : cancel.
#[export] Hint Extern 1 (_ |-- field_at_ _ _ _ _) =>
  simple apply data_at__field_at__cancel : cancel.

(* ================================================================= *)
(** ** Bridge Extern: the conversion path the removal took away. *)
(* ================================================================= *)

(** The removed [Hint Resolve] entries also (accidentally) served as
    the only full-conversion path for pairs that are convertible but
    not syntactic, e.g. a loop-entry
    [data_at_ sh (tarray tuchar pk_bytes) p |--
     data_at sh (tarray tuchar 2048) (prefix-[] ++ Zrepeat Vundef 2048) p]
    whose RHS [++] hides an [@app (@reptype CompSpecs tuchar)] vs
    [@app val] type-argument mismatch; VST's own conversion-based
    [derives_refl] Extern is commented out upstream as too slow, and
    the remaining [constr_eq]-guarded one cannot see through it.
    Restore that single shape with a pattern-guarded bridge: the
    default-transparency body unifies the types and [reflexivity]
    closes the [_ = default_val _] premise by (cheap, weak-head
    fail-fast) kernel conversion.  If a future proof hits the same
    cliff on a [field_at_]/[field_at] pair, add the analogous Extern
    via [field_at__field_at] / [data_at__field_at] /
    [field_at__data_at] here. *)
#[export] Hint Extern 2 (data_at_ _ _ _ |-- data_at _ _ _ _) =>
  (simple apply data_at__data_at; reflexivity) : cancel.
