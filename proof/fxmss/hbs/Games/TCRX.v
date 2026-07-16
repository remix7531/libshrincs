(** * HBS.Games.TCRX

    Single-function Multi-target Target-Collision Resistance with
    EXCLUSIVE tweaks, as a real/ideal game pair (see HBS.Games.THF
    for the convention).

    Counterpart: stcr-exclusive.tex, Definition "Single-Function,
    Multi-Target Target Collision Resistance with Exclusive Tweaks
    (TCR-exclusive)", experiment $TCR-X_{Th,p}(A)$
    (\TCRexclusivebf_{\TweakHash, p} in the tex).  This is the
    paper's novel notion used for the F.9 -> F.10 structure-mismatch
    hop in the \fxmss proof: "There is a subset of tweak space which
    can be partitioned into two halves. You can set a challenge for a
    tweak from one of the halves, but you can not use the
    corresponding tweak from the other half. However, the solution
    (i.e.) the collision can use either of the paired tweaks."

    Experiment structure (paper): the tweak space splits as
    T = T_1 u T_2 u T_3 (pairwise disjoint, |T_2| = |T_3|) with a
    bijection omega : T_2 -> T_3.  A first stage commits up to [p]
    targets (tweak, message) through an oracle for Th(P,.,.) without
    seeing P; the oracle rejects a tweak if it, or its omega-partner,
    was already used ("If T in T_2 and there is an M' in M with
    (omega(T),M') in Q return bot", and symmetrically for T_3 via
    omega^{-1}).  The second stage receives P and must output
    (j, T∗, M∗) such that Th(P,T∗,M∗) = Th(P,T_j,M_j) and M∗ <> M_j,
    where T∗ is T_j itself or — exactly when T_j lies in the paired
    halves — its partner: "If T_j in T_2 and (T∗ <> T_j and
    T∗ <> g(T_j)): Output 0" (and the omega^{-1} mirror for T_3).

    Modeling choices (documented readings of the tex):
    - Partition/bijection: the experiment is symmetric in T_2 / T_3
      (the oracle applies omega on T_2 and omega^{-1} on T_3, and the
      win condition likewise), so the game never needs to tell the
      two halves apart.  We therefore take a predicate
      [paired : th_T T -> bool] (membership in T_2 u T_3; T_1 is its
      complement) and a total map [omega : th_T T -> th_T T] whose
      restriction to paired tweaks is meant to be the fixed-point-free
      involution swapping T_2 and T_3 (omega on T_2, omega^{-1} on
      T_3).  No properties of [paired]/[omega] are needed to STATE
      the game; intended instantiations satisfy them by construction
      (in SHRINCS: internal-node tweak (z,i) <-> WOTS-compression
      tweak (z,i)).
    - "g(T_j)" in the win condition (tex lines 29-30) is read as
      omega(T_j): omega is the only bijection T_2 -> T_3 in scope at
      that point, and g is only introduced later (proof section) as a
      random function.
    - The oracle accepts targets under tweaks from ALL three classes
      ("takes T in T and M in M as inputs", tex line 17); exclusivity
      is enforced per omega-pair only.
    - The oracle's bot answers (cap [p], tweak reuse, partner reuse)
      are encoded as #assert, like SMTCR's DIST condition; a rejected
      query records nothing.
    - The tex samples P up front (step 2) but only uses it in oracle
      replies and the final check; we sample it lazily at first use
      (same convention as SMTCR.v), which is equivalent.
    - "without the oracle access" / "A_2 ... with input P" (tex steps
      4-5): GETPP-style oracle XGETPP reveals P and disables XQUERY.
    - "M∗ <> M_j" is required verbatim even when T∗ is the partner
      tweak (tex line 31 imposes it unconditionally).
    - The side condition p in [|T_1 u T_2|] (tex line 12) is a
      constraint on the parameter, not on the experiment; here
      [p : nat] is unconstrained.
    - As in SMTCR.v we add the collection oracle XCOLLQ (EasyCrypt
      `*_C` convention): the other members of the SHRINCS collection
      evaluated under the same hidden P.  It is not part of the tex
      definition.
    - Invalid index j (no j-th entry in Q) cannot win: CHECK returns
      false ("Denote the j-th entry in Q by (T_j, M_j)", j in [|Q|]).

    Game encoding:
    - [XQUERY (t, m)]: commit a target; allowed only before [XGETPP]
      was called, caps at [p] targets, enforces freshness of the
      tweak AND of its omega-partner (when [t] is paired), returns
      Th(P,t,m).
    - [XCOLLQ]: evaluate the other collection members under the same
      (hidden) P; available in both phases.
    - [XGETPP]: reveal P; afterwards XQUERY is disabled.
    - [XCHECK (j, t, m)]: real game returns the win predicate
      (tweak-validity /\ m <> m_j /\ Th(P,t_j,m_j) = Th(P,t,m));
      ideal game returns false.

    TCR-exclusive advantage of A:
    [AdvOf (TCRX_game T C paired omega p) A]. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Games.THF.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section TCRXGame.

Context (T : thf) (C : thf_coll T).
(* [paired t] = t in T_2 u T_3; [omega] = the pairing involution on
   the paired tweaks (omega : T_2 -> T_3 of the tex, extended by its
   inverse on T_3; arbitrary elsewhere). *)
Context (paired : th_T T -> bool) (omega : th_T T -> th_T T).
Context (p : nat).

Definition XQUERY : nat := 90.
Definition XGETPP : nat := 91.
Definition XCHECK : nat := 92.
Definition XCOLLQ : nat := 93.

Definition tcrx_pp_loc := mkloc 95 (None : option (th_PP T)).
Definition tcrx_tgts_loc :=
  mkloc 96 (emptym : {fmap nat → (th_T T × th_M T)}).
Definition tcrx_tws_loc := mkloc 97 ([::] : seq (th_T T)).
Definition tcrx_rev_loc := mkloc 98 (false : bool).

Definition I_TCRX :=
  [interface
    [ XQUERY ] : { th_T T × th_M T ~> th_N T } ;
    [ XGETPP ] : { 'unit ~> th_PP T } ;
    [ XCHECK ] : { ('nat × th_T T) × th_M T ~> 'bool } ;
    [ XCOLLQ ] : { tc_T C × tc_M C ~> tc_N C }
  ].

Definition TCRX_game (b : bool) : game I_TCRX :=
  [package [fmap tcrx_pp_loc ; tcrx_tgts_loc ; tcrx_tws_loc ; tcrx_rev_loc ] ;
    [ XQUERY ] : { th_T T × th_M T ~> th_N T } '(t, m) {
      revealed ← get tcrx_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get tcrx_tws_loc ;;
      (* "If |Q| >= p return bot." *)
      #assert (size tws < p)%N ;;
      (* "If T in T and there is an M' in M with (T,M') in Q return
         bot." *)
      #assert (t \notin tws) ;;
      (* "If T in T_2 and there is an M' in M with (omega(T),M') in Q
         return bot." — and the omega^{-1} mirror for T_3; both are
         [omega t] under the involution reading. *)
      #assert (~~ (paired t && (omega t \in tws))) ;;
      tgts ← get tcrx_tgts_loc ;;
      #put tcrx_tgts_loc := setm tgts (size tws) (t, m) ;;
      #put tcrx_tws_loc := rcons tws t ;;
      ppo ← get tcrx_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcrx_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t m)
    } ;
    [ XGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get tcrx_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcrx_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put tcrx_rev_loc := true ;;
      ret pp
    } ;
    [ XCHECK ] : { ('nat × th_T T) × th_M T ~> 'bool } '(j, t, m) {
      if b then
        revealed ← get tcrx_rev_loc ;;
        #assert revealed ;;
        tgts ← get tcrx_tgts_loc ;;
        match getm tgts j with
        | Some (t0, m0) =>
            ppo ← get tcrx_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcrx_pp_loc := Some pp ;;
               ret pp
           end ;;
            (* Tweak validity: T∗ = T_j always wins the case split;
               the partner omega(T_j) is admitted exactly when T_j is
               paired (T_j in T_2 u T_3).  Win: "Output 1 if
               Th(P,T_j,M_j) = Th(P,T∗,M∗) and M∗ <> M_j." *)
            ret (((t == t0) || (paired t0 && (t == omega t0)))
                 && (m != m0)
                 && (th_eval T pp t0 m0 == th_eval T pp t m))
        | None => ret false
        end
      else
        ret false
    } ;
    [ XCOLLQ ] : { tc_T C × tc_M C ~> tc_N C } '(t, m) {
      ppo ← get tcrx_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcrx_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (tc_eval C pp t m)
    }
  ].

End TCRXGame.
