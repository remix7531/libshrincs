(** * HBS.Sig.KOTS

    One-time, KNOWN-MESSAGE unforgeability game pair for a
    [sig_scheme]: the adversary submits the (single) message to be
    signed TOGETHER with the request that creates the key, then must
    forge on a different message.

    This is the right notion for the chain layer of hash-based
    signatures (EasyCrypt's EUF-GCMA flavour, WOTS_TW_ES.ec): a bare
    OTS cannot be proved adaptively EU-CMA from SM-* assumptions
    because the reductions must know the signed digits while building
    the public key.  In SHRINCS, adaptivity is broken earlier by the
    message-digest hops (rkTCR + reprogramming, security.tex F.0-F.3),
    after which the WOTS+C layer faces exactly this known-message
    experiment.

    Real/ideal convention as in HBS.Games.THF: ideal FORGE returns
    false; the known-message OTS success of A is
    [AdvOf (KOTS_game S) A]. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Sig.Scheme.
Set Warnings "notation-overridden,ambiguous-paths".

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
      if b then
        pk ← getSome kots_pk_loc ;;
        log ← get kots_log_loc ;;
        ret (verify S pk m s && (m \notin log))
      else
        ret false
    }
  ].

End KOTSGame.
