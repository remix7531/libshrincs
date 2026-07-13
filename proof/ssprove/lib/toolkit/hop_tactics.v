(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.toolkit.hop_tactics

    Small proof-shaping tactics shared by the WOTS+C relational hop
    proofs (Grind / Compress / ChainTCR / ChainPRE).  They only
    ABBREVIATE a recurring SSProve tactic sequence — no new reasoning,
    so a reader can expand [sync_eq] mentally to the three [eapply]s
    below. *)

From Sec.lib Require Import prelude toolkit.relational_rules.

(** [sync_eq x x']: read a location on both sides, remembering the two
    values as [x] (lhs) and [x'] (rhs), and reduce to proving they
    agree.  Leaves TWO goals in order:
      1. the equality [x' = x] — discharge it from the relational
         invariant (typically a [{ ... }] block);
      2. the continuation, with the reads remembered — finish with
         [move=> e; subst x'].
    It expands exactly to
      eapply r_get_remember_lhs => x.
      eapply r_get_remember_rhs => x'.
      eapply (r_fact (x' = x)).  *)
Tactic Notation "sync_eq" ident(x) ident(x') :=
  eapply r_get_remember_lhs; intro x;
  eapply r_get_remember_rhs; intro x';
  eapply (r_fact (x' = x)).
