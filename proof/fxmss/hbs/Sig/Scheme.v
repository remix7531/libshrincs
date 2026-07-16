(** * HBS.Sig.Scheme

    Signature schemes as data, in the style of
    resources/ssprove/theories/Crypt/examples/PKE/Scheme.v.

    Counterpart: preliminaries.tex def:dss, extended with the two
    SHRINCS-specific features (def:shrincs-eu-cma):

    - [SParam]: an adversary-chosen structure parameter consumed by
      key generation (FXMSS lets the adversary pick the Merkle tree
      shape; use ['unit] for ordinary schemes);
    - STATEFUL SIGNING as key update: [sign sk m] returns
      [Some (sig, sk')] with the evolved secret key, or [None] when
      the scheme refuses (stateful keys exhausted, grinding failure).
      Stateless schemes return the key unchanged.  Keeping all state
      inside [Sk] means the EU-CMA game (HBS.Sig.EUCMA) stores ONE
      location, so game-hop invariants have a uniform shape. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude.
Set Warnings "notation-overridden,ambiguous-paths".

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
