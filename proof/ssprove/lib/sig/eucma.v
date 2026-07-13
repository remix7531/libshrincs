(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.sig.eucma

    Adaptive existential-unforgeability-under-chosen-message-attack
    (EU-CMA) game pair for a [sig_scheme]: the adversary is handed a
    signing ORACLE it may query on messages of its choice -- each query
    evolving the single stateful secret key, per [Sec.lib.sig.scheme]'s
    key-update signing -- then must FORGE a valid signature on a message
    it never submitted.

    Contrast [Sec.lib.sig.kots] (one-time, known-message), where the
    single signed message is fixed at key creation.  This is the general
    adaptive notion the SHRINCS tower's tree layers consume; the WOTS+C
    leaf itself is proved in the weaker KOTS experiment.

    Real/ideal convention as in [Sec.lib.games.thf] and KOTS: ideal
    FORGE returns false; the EU-CMA success of A is
    [AdvOf (EUCMA_game S) A]. *)

From Sec.lib Require Import prelude sig.scheme.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section EUCMAGame.

Context (S : sig_scheme).

Definition SETUP : nat := 120.
Definition SIGN  : nat := 121.
Definition FORGE : nat := 122.

Definition eucma_sk_loc  := mkloc 125 (None : option (Sk S)).
Definition eucma_pk_loc  := mkloc 126 (None : option (Pk S)).
Definition eucma_log_loc := mkloc 127 ([::] : seq (Msg S)).

Definition I_EUCMA :=
  [interface
    [ SETUP ] : { SParam S ~> Pk S } ;
    [ SIGN  ] : { Msg S ~> 'option (Sig S) } ;
    [ FORGE ] : { Msg S × Sig S ~> 'bool }
  ].

Definition EUCMA_game (b : bool) : game I_EUCMA :=
  [package [fmap eucma_sk_loc ; eucma_pk_loc ; eucma_log_loc ] ;
    [ SETUP ] : { SParam S ~> Pk S } (sp) {
      pko ← get eucma_pk_loc ;;
      #assert ~~ (isSome pko) ;;
      '(sk, pk) ← keygen S sp ;;
      #put eucma_sk_loc := Some sk ;;
      #put eucma_pk_loc := Some pk ;;
      ret pk
    } ;
    [ SIGN ] : { Msg S ~> 'option (Sig S) } (m) {
      sk ← getSome eucma_sk_loc ;;
      r ← sign S sk m ;;
      match r with
      | Some (s, sk') =>
          #put eucma_sk_loc := Some sk' ;;
          log ← get eucma_log_loc ;;
          #put eucma_log_loc := m :: log ;;
          ret (Some s)
      | None => ret None
      end
    } ;
    [ FORGE ] : { Msg S × Sig S ~> 'bool } '(m, s) {
      if b then
        pk ← getSome eucma_pk_loc ;;
        log ← get eucma_log_loc ;;
        ret (verify S pk m s && (m \notin log))
      else
        ret false
    }
  ].

End EUCMAGame.
