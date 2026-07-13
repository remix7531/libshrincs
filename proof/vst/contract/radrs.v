(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.radrs: the flat "under-construction" ADRS for the C refinement.

    [Model.address.adrs] is a dependent union: illegal field/type
    combinations are unrepresentable.  That is exactly right for the
    model and the security proof, but the C builds an ADRS by MUTATING a
    22-byte buffer in place -- prefill the anchor, write the type byte,
    then splice each 4-byte payload word -- and its intermediate states
    (type set but payload not yet zeroed, etc.) are byte-faithful yet do
    NOT correspond to any union constructor.

    [radrs] is the flat six-field-of-[Z] view the C mutates: one field
    per wire slot, no bounds, so every partial byte state is
    representable.  It is used ONLY inside the VST body proofs, as the
    intermediate under-construction value; the funspec pre/post
    conditions still speak the union ([Model.address.adrs]) via
    [adrs_bytes].  The two are bridged by:

    - [adrs_to_raw] : the wire-field view of a union address, and
    - [radrs_bytes_to_raw] : [radrs_bytes (adrs_to_raw a) = adrs_bytes a]
      (by [reflexivity] -- both are the same [to_byte] concatenation),

    plus, where a body needs one, a "stores" lemma folding a
    setter composition back into [adrs_to_raw (shrincs_wots_*_adrs a ...)]
    (the shared ones, e.g. [prf_raw_stores], live in
    [contract.lemmas.chain_blocks]).

    Because the fields are [Z] (not truncating machine ints), the setters
    are plain field replacements and the [shrincs_adrs_put32] splice
    lemmas need no [repr]-truncation bridge. *)

From Stdlib Require Import List ZArith Lia.
From Model Require Import byte fin address wots.
Import ListNotations.
Open Scope Z_scope.

(** WOTS+C instantiates [Model.address]'s parametric ADRS at
    [chain_count = len] and [pos_bound = w_pred]; this notation keeps
    every bare [adrs] type mention resolving to the fully-applied
    [address.adrs len w_pred]. *)
Local Notation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** The flat wire view. *)

Record radrs : Type := mk_radrs {
  rtag  : Z;   (* byte 0     : anchor tag (node height / layer) *)
  ridx  : Z;   (* bytes 1-8  : anchor index (node index / tree address) *)
  rtype : Z;   (* byte 9     : ADRS type *)
  rpa   : Z;   (* bytes 10-13: payload word 0 *)
  rpb   : Z;   (* bytes 14-17: payload word 1 *)
  rpc   : Z;   (* bytes 18-21: payload word 2 *)
}.

Definition rset_type (r : radrs) (v : Z) : radrs :=
  mk_radrs (rtag r) (ridx r) v (rpa r) (rpb r) (rpc r).
Definition rset_payload_a (r : radrs) (v : Z) : radrs :=
  mk_radrs (rtag r) (ridx r) (rtype r) v (rpb r) (rpc r).
Definition rset_payload_b (r : radrs) (v : Z) : radrs :=
  mk_radrs (rtag r) (ridx r) (rtype r) (rpa r) v (rpc r).
Definition rset_payload_c (r : radrs) (v : Z) : radrs :=
  mk_radrs (rtag r) (ridx r) (rtype r) (rpa r) (rpb r) v.

(** Serialize a wire view to its 22 bytes (same concatenation shape as
    [Model.address.adrs_bytes]). *)
Definition radrs_bytes (r : radrs) : list byte :=
  to_byte (rtag r)  1 ++
  to_byte (ridx r)  8 ++
  to_byte (rtype r) 1 ++
  to_byte (rpa r)   4 ++
  to_byte (rpb r)   4 ++
  to_byte (rpc r)   4.

(* ================================================================= *)
(** ** Bridge to the model union. *)

(** The wire-field view of a union address. *)
Definition adrs_to_raw (a : adrs) : radrs :=
  mk_radrs (adrs_anchor_tag_z a) (adrs_anchor_idx_z a) (byte_val (adrs_type a))
           (payload_a_z a) (payload_b_z a) (payload_c_z a).

(** Serializing the wire view of [a] gives exactly [adrs_bytes a] -- both
    are the same [to_byte] concatenation of the same six [Z]s. *)
Lemma radrs_bytes_to_raw (a : adrs) : radrs_bytes (adrs_to_raw a) = adrs_bytes a.
Proof. reflexivity. Qed.

(** The C leaves the anchor (tag + index) untouched; every setter/store
    keeps [rtag]/[ridx], so the under-construction value stays anchored
    where the caller prefilled it. *)
Definition radrs_struct_eq (r s : radrs) : Prop :=
  rtag r = rtag s /\ ridx r = ridx s.
