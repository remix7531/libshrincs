(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.lib.sig.scheme

    Signature schemes as data, extended with two features:

    - [SParam]: an adversary-chosen structure parameter consumed by
      key generation (lets the adversary pick a structure such as a
      Merkle tree shape; use ['unit] for ordinary schemes);
    - STATEFUL SIGNING as key update: [sign sk m] returns
      [Some (sig, sk')] with the evolved secret key, or [None] when
      the scheme refuses (stateful keys exhausted, grinding failure).
      Stateless schemes return the key unchanged.  Keeping all state
      inside [Sk] means the EU-CMA game (Shrincs.internal.ssprove.lib.sig.eucma) stores ONE
      location, so game-hop invariants have a uniform shape. *)

From Shrincs.internal.ssprove.lib Require Import prelude.

Import PackageNotation.
#[local] Open Scope package_scope.

Record sig_scheme := {
  Pk : choice_type ;
  Sk : choice_type ;
  Msg : choice_type ;
  Sig : choice_type ;
  SParam : choice_type ;
  keygen : SParam -> dist (Sk × Pk) ;
  sign : Sk -> Msg -> dist ('option (Sig × Sk)) ;
  verify : Pk -> Msg -> Sig -> bool
}.
