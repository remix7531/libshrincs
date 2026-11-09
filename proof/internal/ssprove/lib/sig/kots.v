(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.sig.kots

    One-time, KNOWN-MESSAGE unforgeability game pair for a
    [sig_scheme]: the adversary submits the (single) message to be
    signed TOGETHER with the request that creates the key, then must
    forge on a different message.

    This is the right notion for the chain layer of hash-based
    signatures: a bare OTS cannot be proved adaptively EU-CMA from
    SM-* assumptions because the reductions must know the signed
    digits while building the public key.  Adaptivity is broken
    earlier by the message-digest hops, after which the WOTS+C layer
    faces exactly this known-message experiment.

    Real/ideal convention as in Sec.lib.games.thf: ideal FORGE returns
    false; the known-message OTS success of A is
    [AdvOf (KOTS_game S) A]. *)

From Shrincs.internal.ssprove.lib Require Import prelude sig.scheme.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section KOTSGame.

Context (S : sig_scheme).

Definition COMMIT : nat := 110.
Definition KFORGE : nat := 111.

Definition kots_pk_loc := mkloc 115 (None : option (Pk S)).
Definition kots_log_loc := mkloc 116 ([::] : seq (Msg S)).

Definition I_KOTS :=
  [interface
    [ COMMIT ] : { SParam S × Msg S ~> Pk S × 'option (Sig S) } ;
    [ KFORGE ] : { Msg S × Sig S ~> 'bool }
  ].

Definition KOTS_game (b : bool) : game I_KOTS :=
  [package [fmap kots_pk_loc ; kots_log_loc ] ;
    [ COMMIT ] : { SParam S × Msg S ~> Pk S × 'option (Sig S) } '(sp, m) {
      pko ← get kots_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      '(sk, pk) ← keygen S sp ;;
      #put kots_pk_loc := Some pk ;;
      r ← sign S sk m ;;
      match r with
      | Some (s, _) =>
          #put kots_log_loc := [:: m] ;;
          ret (pk, Some s)
      | None => ret (pk, None)
      end
    } ;
    [ KFORGE ] : { Msg S × Sig S ~> 'bool } '(m, s) {
      (* Both games enforce the same call order: KFORGE before COMMIT
         aborts because no public key has been stored. *)
      pk ← getSome kots_pk_loc ;;
      log ← get kots_log_loc ;;
      if b then
        (* win  <=>  the signature verifies AND the forged message was
           never signed (the one-time forgery condition). *)
        ret (verify S pk m s && (m \notin log))
      else
        ret false
    }
  ].

(** [KOTS_vc_game] is the VALID-COMMIT variant of [KOTS_game]: it
    differs from [KOTS_game] on EXACTLY the sign-refusal event.  Where
    [KOTS_game] commits the key first and then returns [(pk, None)] on
    a refused ([None]) sign, [KOTS_vc_game] commits NOTHING and lets
    COMMIT [fail] — so BOTH puts happen only after a successful sign
    (the [match]-not-[getSome] shape keeps the two continuations
    proof-free).  The refusal probability is deliberately UNBOUNDED
    here: a valid-commit experiment is the right notion for the WOTS+C
    chain layer, whose tree consumer only ever signs grindable digests
    by construction (see Sec.wots.games).  This game is machine-linked
    to the WOTS+C valid-commit games [G_forge_keyed] /
    [G_forge_sampledkey] in Sec.wots.kots_link. *)
Definition KOTS_vc_game (b : bool) : game I_KOTS.
Proof.
  notypeclasses refine [package [fmap kots_pk_loc ; kots_log_loc ] ;
    [ COMMIT ] : { SParam S × Msg S ~> Pk S × 'option (Sig S) } '(sp, m) {
      pko ← get kots_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      '(sk, pk) ← keygen S sp ;;
      r ← sign S sk m ;;
      match r with
      | Some (s, _) =>
          #put kots_pk_loc := Some pk ;;
          #put kots_log_loc := [:: m] ;;
          ret (pk, Some s)
      | None => @fail (Pk S × 'option (Sig S))
      end
    } ;
    [ KFORGE ] : { Msg S × Sig S ~> 'bool } '(m, s) {
      (* Keep the protocol-state checks outside the game-bit branch. *)
      pk ← getSome kots_pk_loc ;;
      log ← get kots_log_loc ;;
      if b then
        ret (verify S pk m s && (m \notin log))
      else
        ret false
    }
  ].
  (* [ssprove_valid] discharges everything but the sign-refusal [fail];
     its [valid_fail] Hint Extern uses non-ssreflect [eapply], which
     trips on the [chProd] reverse-coercion here, so close it by hand. *)
  ssprove_valid.
  exact: valid_fail.
Defined.

End KOTSGame.
