(** * HBS.Games.THF

    Abstract (tweakable) hash functions as data, and the conventions
    shared by all assumption games in HBS.Games.*.

    Counterparts: preliminaries.tex Defs. "Keyed hash functions" /
    "Tweakable hash function" (def:tweakableHF) and the collection
    notion (notion:thl); EasyCrypt `TweakableHashFunctions.eca` /
    `KeyedHashFunctions.eca` in resources/FV-SPHINCSPLUS-EC.

    ** Real/ideal convention for search games

    The paper states hash assumptions as success probabilities
    [Succ^X(A)] of search experiments.  Here every such notion is a
    GAME PAIR [G : bool -> game I]: the [true] (real) game implements
    the experiment's final check; the [false] (ideal) game differs
    exactly in that the check oracle always returns [false].  The
    assumption advantage is [AdvOf G A = Adv (G true) (G false) A],
    and all bounds in this development are stated with such terms on
    the right-hand side.  This is the state-separating-proofs
    treatment of search/forgery games; it keeps the whole development
    inside SSProve's [Adv] calculus (triangle, reduction, perfect).
    For an adversary that simply forwards the check oracle's reply,
    [AdvOf G A] equals the paper's success probability, and in
    general [AdvOf G A] is bounded by the probability that some check
    query succeeds in the real game, so paper-level assumptions
    translate soundly.

    ** Collections

    SHRINCS uses several tweakable hash functions sharing one public
    parameter (the collection Th_lambda).  Games therefore expose, in
    addition to the member under attack, a COLLECTION oracle giving
    the adversary the other members evaluated at the shared (still
    hidden) public parameter — the `*C` variants of the EasyCrypt
    development.  The collection is abstracted as a single function
    [th_coll : PP -> CollT -> CollM -> CollN]; instantiate the types
    with sums to bundle several functions, or with ['unit] (and any
    constant) when no collection access is needed. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

(** A tweakable hash function with the samplers its games need.
    [th_eval] is a pure abstract function: assumptions about it are
    exactly the game pairs of HBS.Games.*, nothing else. *)
Record thf := {
  th_PP : choice_type ;            (* public parameter (PKseed)      *)
  th_T  : choice_type ;            (* tweak (encoded address)        *)
  th_M  : choice_type ;            (* input                          *)
  th_N  : choice_type ;            (* output                         *)
  th_eval : th_PP -> th_T -> th_M -> th_N ;
  th_dPP : dist th_PP ;            (* parameter sampler              *)
  th_dM  : dist th_M ;             (* input sampler (SM-PRE, SM-UD)  *)
  th_dN  : dist th_N               (* output sampler (SM-UD ideal)   *)
}.

(** A keyed hash function (PRF assumption). *)
Record khf := {
  kh_K : choice_type ;
  kh_M : choice_type ;
  kh_N : choice_type ;
  kh_eval : kh_K -> kh_M -> kh_N ;
  kh_dK : dist kh_K ;
  kh_dN : dist kh_N
}.

(** Collection access bundled with a [thf]; trivial instance below. *)
Record thf_coll (T : thf) := {
  tc_T : choice_type ;
  tc_M : choice_type ;
  tc_N : choice_type ;
  tc_eval : th_PP T -> tc_T -> tc_M -> tc_N
}.

Arguments tc_T {T} _.
Arguments tc_M {T} _.
Arguments tc_N {T} _.
Arguments tc_eval {T} _.

Definition trivial_coll (T : thf) : thf_coll T :=
  {| tc_T := 'unit ; tc_M := 'unit ; tc_N := 'unit ;
     tc_eval := fun _ _ _ => Datatypes.tt |}.
