(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.games: security experiments and the concrete WOTS+C scheme

    The search experiments compare their success test with an always-false test. Their public seed is sampled lazily once and shared by every oracle of the experiment. Target selection closes when the seed is revealed. The PRF experiment keeps its key hidden. The KOTS experiment commits the message before generating a key and aborts if signing fails. *)

From mathcomp Require Export boot order algebra.
From Stdlib Require Export Utf8.
From extructures Require Export ord fset fmap.
From Equations Require Export Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From SSProve.Crypt Require Export NominalPrelude TotalProbability HybridArgument.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* Signing may refuse or return a signature and an updated secret key. SParam is chosen by the adversary before key generation. *)
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

(* The hash and its samplers are data. Each experiment below states the access it gives to them. *)
Record thf := {
  th_PP : choice_type ;
  th_T  : choice_type ;
  th_M  : choice_type ;
  th_N  : choice_type ;
  th_eval : th_PP -> th_T -> th_M -> th_N ;
  th_dPP : dist th_PP ;
  th_dM  : dist th_M ;
  th_dN  : dist th_N
}.

Record khf := {
  kh_K : choice_type ;
  kh_M : choice_type ;
  kh_N : choice_type ;
  kh_eval : kh_K -> kh_M -> kh_N ;
  kh_dK : dist kh_K ;
  kh_dN : dist kh_N
}.

(* Evaluation is available outside the static target class, under the same lazily sampled public seed. *)
Definition EVAL : nat := 43.

(* T is the challenged hash. Target selection is restricted by target_class and budget p. For collision and preimage games, b selects the real success test or an always-false test. *)
Module smtcr.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SMTCRGame.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition TQUERY : nat := 40.
Definition GETPP : nat := 41.
Definition CHECK : nat := 42.

Definition tcr_pp_loc := mkloc 44 (None : option (th_PP T)).
Definition tcr_tgts_loc :=
  mkloc 45 (emptym : {fmap nat → (th_T T × th_M T)}).
Definition tcr_tws_loc := mkloc 46 ([::] : seq (th_T T)).
Definition tcr_rev_loc := mkloc 47 (false : bool).

Definition I_SMTCR :=
  [interface
    [ TQUERY ] : { th_T T × th_M T ~> th_N T } ;
    [ GETPP ] : { 'unit ~> th_PP T } ;
    [ CHECK ] : { 'nat × th_M T ~> 'bool } ;
    [ EVAL ] : { th_T T × th_M T ~> th_N T }
  ].

(* Choose at most p target messages at distinct tweaks before the seed is revealed. CHECK wins by supplying a different message with the same hash at one recorded tweak. *)
Definition SMTCR_game (b : bool) : game I_SMTCR :=
  [package [fmap tcr_pp_loc ; tcr_tgts_loc ; tcr_tws_loc ; tcr_rev_loc ] ;
    [ TQUERY ] : { th_T T × th_M T ~> th_N T } '(t, m) {
      #assert (target_class t) ;;
      revealed ← get tcr_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get tcr_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      tgts ← get tcr_tgts_loc ;;
      #put tcr_tgts_loc := setm tgts (size tws) (t, m) ;;
      #put tcr_tws_loc := rcons tws t ;;
      ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t m)
    } ;
    [ GETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put tcr_rev_loc := true ;;
      ret pp
    } ;
    [ CHECK ] : { 'nat × th_M T ~> 'bool } '(j, m) {
      revealed ← get tcr_rev_loc ;;
      #assert revealed ;;
      if b then
        tgts ← get tcr_tgts_loc ;;
        match getm tgts j with
        | Some (t0, m0) =>
            ppo ← get tcr_pp_loc ;;
            pp ← match ppo with
                 | Some pp => ret pp
                 | None =>
                     pp ← th_dPP T ;;
                     #put tcr_pp_loc := Some pp ;;
                     ret pp
                 end ;;
            ret ((m != m0) && (th_eval T pp t0 m == th_eval T pp t0 m0))
        | None => ret false
        end
      else
        ret false
    } ;
    [ EVAL ] : { th_T T × th_M T ~> th_N T } '(t, m) {
      #assert ~~ (target_class t) ;;
      ppo ← get tcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put tcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t m)
    }
  ].

End SMTCRGame.
End smtcr.

Module smpre.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SMPREGame.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition PQUERY : nat := 50.
Definition PGETPP : nat := 51.
Definition PCHECK : nat := 52.

Definition pre_pp_loc := mkloc 54 (None : option (th_PP T)).
Definition pre_tgts_loc :=
  mkloc 55 (emptym : {fmap nat → (th_T T × th_M T)}).
Definition pre_tws_loc := mkloc 56 ([::] : seq (th_T T)).
Definition pre_rev_loc := mkloc 57 (false : bool).

Definition I_SMPRE :=
  [interface
    [ PQUERY ] : { th_T T ~> th_N T } ;
    [ PGETPP ] : { 'unit ~> th_PP T } ;
    [ PCHECK ] : { 'nat × th_M T ~> 'bool } ;
    [ EVAL ] : { th_T T × th_M T ~> th_N T }
  ].

(* At each chosen tweak, return the hash of a fresh hidden message. After seed revelation, CHECK accepts any preimage of a recorded output, including the original hidden message. *)
Definition SMPRE_game (b : bool) : game I_SMPRE :=
  [package [fmap pre_pp_loc ; pre_tgts_loc ; pre_tws_loc ; pre_rev_loc ] ;
    [ PQUERY ] : { th_T T ~> th_N T } (t) {
      #assert (target_class t) ;;
      revealed ← get pre_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get pre_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      x ← th_dM T ;;
      tgts ← get pre_tgts_loc ;;
      #put pre_tgts_loc := setm tgts (size tws) (t, x) ;;
      #put pre_tws_loc := rcons tws t ;;
      ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t x)
    } ;
    [ PGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put pre_rev_loc := true ;;
      ret pp
    } ;
    [ PCHECK ] : { 'nat × th_M T ~> 'bool } '(j, m) {
      revealed ← get pre_rev_loc ;;
      #assert revealed ;;
      if b then
        tgts ← get pre_tgts_loc ;;
        match getm tgts j with
        | Some (t0, x0) =>
            ppo ← get pre_pp_loc ;;
            pp ← match ppo with
                 | Some pp => ret pp
                 | None =>
                     pp ← th_dPP T ;;
                     #put pre_pp_loc := Some pp ;;
                     ret pp
                 end ;;
            ret (th_eval T pp t0 m == th_eval T pp t0 x0)%B
        | None => ret false
        end
      else
        ret false
    } ;
    [ EVAL ] : { th_T T × th_M T ~> th_N T } '(t, m) {
      #assert ~~ (target_class t) ;;
      ppo ← get pre_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put pre_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t m)
    }
  ].

End SMPREGame.
End smpre.

Module smud.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section SMUDGame.
Context (T : thf) (target_class : th_T T -> bool) (p : nat).

Definition UQUERY : nat := 60.
Definition UGETPP : nat := 61.

Definition ud_pp_loc := mkloc 64 (None : option (th_PP T)).
Definition ud_tws_loc := mkloc 65 ([::] : seq (th_T T)).
Definition ud_rev_loc := mkloc 66 (false : bool).

Definition I_SMUD :=
  [interface
    [ UQUERY ] : { th_T T ~> th_N T } ;
    [ UGETPP ] : { 'unit ~> th_PP T } ;
    [ EVAL ] : { th_T T × th_M T ~> th_N T }
  ].

(* Before seed revelation, answer distinct-tweak target queries with hashes of hidden random messages when b is true, or independent random outputs otherwise. Evaluation queries use the shared seed outside the target class. *)
Definition SMUD_game (b : bool) : game I_SMUD :=
  [package [fmap ud_pp_loc ; ud_tws_loc ; ud_rev_loc ] ;
    [ UQUERY ] : { th_T T ~> th_N T } (t) {
      #assert (target_class t) ;;
      revealed ← get ud_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get ud_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      (* Both game bits enforce the same query budget and distinctness. *)
      #put ud_tws_loc := rcons tws t ;;
      if b then
        ppo ← get ud_pp_loc ;;
        pp ← match ppo with
             | Some pp => ret pp
             | None =>
                 pp ← th_dPP T ;;
                 #put ud_pp_loc := Some pp ;;
                 ret pp
             end ;;
        x ← th_dM T ;;
        ret (th_eval T pp t x)
      else
        y ← th_dN T ;;
        ret y
    } ;
    [ UGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get ud_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put ud_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put ud_rev_loc := true ;;
      ret pp
    } ;
    [ EVAL ] : { th_T T × th_M T ~> th_N T } '(t, m) {
      #assert ~~ (target_class t) ;;
      ppo ← get ud_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put ud_pp_loc := Some pp ;;
               ret pp
           end ;;
      ret (th_eval T pp t m)
    }
  ].

End SMUDGame.
End smud.

Module stcrp.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section STCRPGame.
Context (T : thf) (target_class : th_T T -> bool).
Context (Mb : choice_type) (enc : th_T T -> Mb -> nat -> th_T T * th_M T)
        (prp : th_N T -> bool) (cap : nat) (p : nat).

Definition SQUERY : nat := 70.
Definition SGETPP : nat := 71.
Definition SCHECK : nat := 72.

Definition stcr_pp_loc := mkloc 74 (None : option (th_PP T)).
Definition stcr_tgts_loc :=
  mkloc 75 (emptym : {fmap nat → (th_T T × (Mb × 'nat))}).
Definition stcr_tws_loc := mkloc 76 ([::] : seq (th_T T)).
Definition stcr_rev_loc := mkloc 77 (false : bool).

Definition I_STCRP :=
  [interface
    [ SQUERY ] : { th_T T × Mb ~> th_N T × 'nat } ;
    [ SGETPP ] : { 'unit ~> th_PP T } ;
    [ SCHECK ] : { 'nat × (Mb × 'nat) ~> 'bool }
  ].

(* A target query searches counters below cap and returns the first encoded hash satisfying the target class and prp, aborting on exhaustion. After seed revelation, CHECK requires a collision from a different base message. Both encoded tweaks must lie in the target class. The candidate counter need not be bounded or first acceptable. There is no evaluation oracle. *)
Definition STCRP_game (b : bool) : game I_STCRP :=
  [package [fmap stcr_pp_loc ; stcr_tgts_loc ; stcr_tws_loc ; stcr_rev_loc ] ;
    [ SQUERY ] : { th_T T × Mb ~> th_N T × 'nat } '(t, m) {
      #assert (target_class t) ;;
      revealed ← get stcr_rev_loc ;;
      #assert ~~ revealed ;;
      tws ← get stcr_tws_loc ;;
      #assert (size tws < p)%N ;;
      #assert (t \notin tws) ;;
      ppo ← get stcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put stcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      let found := [seq i <- iota 0 cap |
        let q := enc t m i in
        if target_class q.1 then prp (th_eval T pp q.1 q.2) else false] in
      match found with
      | i :: _ =>
          tgts ← get stcr_tgts_loc ;;
          #put stcr_tgts_loc := setm tgts (size tws) (t, (m, i)) ;;
          #put stcr_tws_loc := rcons tws t ;;
          ret (th_eval T pp (enc t m i).1 (enc t m i).2, i)
      | [::] =>
          (* Counter search is bounded, so exhaustion aborts this query. *)
          #assert false ;;
          ret (th_eval T pp (enc t m 0).1 (enc t m 0).2, 0)
      end
    } ;
    [ SGETPP ] : { 'unit ~> th_PP T } (_) {
      ppo ← get stcr_pp_loc ;;
      pp ← match ppo with
           | Some pp => ret pp
           | None =>
               pp ← th_dPP T ;;
               #put stcr_pp_loc := Some pp ;;
               ret pp
           end ;;
      #put stcr_rev_loc := true ;;
      ret pp
    } ;
    [ SCHECK ] : { 'nat × (Mb × 'nat) ~> 'bool } '(j, (m, ctr)) {
      revealed ← get stcr_rev_loc ;;
      #assert revealed ;;
      if b then
        tgts ← get stcr_tgts_loc ;;
        match getm tgts j with
        | Some (t0, (m0, i0)) =>
            ppo ← get stcr_pp_loc ;;
            pp ← match ppo with
                 | Some pp => ret pp
                 | None =>
                     pp ← th_dPP T ;;
                     #put stcr_pp_loc := Some pp ;;
                     ret pp
                 end ;;
            let target := enc t0 m0 i0 in
            let candidate := enc t0 m ctr in
            ret (if target_class target.1 && target_class candidate.1 then
                   (m != m0) &&
                   (th_eval T pp target.1 target.2 == th_eval T pp candidate.1 candidate.2)
                 else false)
        | None => ret false
        end
      else
        ret false
    }
  ].

End STCRPGame.
End stcrp.

Module prf.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section PRFGame.
Context (K : khf) (q : nat).

Definition FQUERY : nat := 80.

Definition prf_k_loc := mkloc 84 (None : option (kh_K K)).
Definition prf_qs_loc := mkloc 85 ([::] : seq (kh_M K)).

Definition I_PRF :=
  [interface
    [ FQUERY ] : { kh_M K ~> kh_N K }
  ].

(* Answer at most q distinct inputs using one hidden key when b is true, or independent random outputs otherwise. Unlike the tweakable-hash games, this game never reveals the key. *)
Definition PRF_game (b : bool) : game I_PRF :=
  [package [fmap prf_k_loc ; prf_qs_loc ] ;
    [ FQUERY ] : { kh_M K ~> kh_N K } (m) {
      ms ← get prf_qs_loc ;;
      #assert (size ms < q)%N ;;
      #assert (m \notin ms) ;;
      (* Distinct queries let the ideal branch sample without memoization. *)
      #put prf_qs_loc := rcons ms m ;;
      if b then
        ko ← get prf_k_loc ;;
        k ← match ko with
            | Some k => ret k
            | None =>
                k ← kh_dK K ;;
                #put prf_k_loc := Some k ;;
                ret k
            end ;;
        ret (kh_eval K k m)
      else
        y ← kh_dN K ;;
        ret y
    }
  ].

End PRFGame.
End prf.

Module kots.

Import PackageNotation.
#[local] Close Scope Z_scope.
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

(* The adversary commits a message before key generation and receives its signature and public key only if signing succeeds. KFORGE accepts a valid signature on a different message when b is true, and always rejects otherwise. A failed commit aborts the experiment. *)
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
      pk ← getSome kots_pk_loc ;;
      log ← get kots_log_loc ;;
      if b then
        ret (verify S pk m s && (m \notin log))
      else
        ret false
    }
  ].
  ssprove_valid.
  exact: valid_fail.
Defined.

End KOTSGame.
End kots.

Export smtcr smpre smud stcrp prf kots.

Definition tcr_budget (chain_count w : nat) : nat :=
  chain_count + chain_count * w.

From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs Require Import spec.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* The games below instantiate the experiments at the functions and byte strings of Shrincs.spec. *)

Definition bytes (n : nat) : choice_type := chTuple (chWord U8) n.

(* Every seed, hash value and message digest the games sample consists of independent uniform bytes. *)
Definition dByte : dist ('word U8) :=
  {code x ← sample uniform 256 ;; ret (uint U8 x)}.

Fixpoint sample_bytes (n : nat) : raw_code (bytes n) :=
  match n with
  | 0 => ret (nil_tuple _)
  | n'.+1 => b ← dByte ;; bs ← sample_bytes n' ;; ret (cons_tuple b bs)
  end.

Lemma sample_bytes_valid (n : nat) : ValidCode emptym emptym (sample_bytes n).
Proof.
elim: n => [|n IH] /=.
- apply valid_ret.
- apply valid_sampler => a.
  eapply valid_bind; [exact: IH | move=> bs; apply valid_ret].
Qed.

Definition dBytes (n : nat) : dist (bytes n) :=
  {code sample_bytes n #with sample_bytes_valid n}.

(* A tweak carries the six fields that Address.pack serialises: height, index, address type and three words. *)
Definition tweak : choice_type :=
  'word U8 × 'word U64 × 'word U8 × 'word U32 × 'word U32 × 'word U32.

(* The address type fixes each target class before the public seed is sampled. *)
Definition wots_c_hash_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_HASH.

Definition wots_c_pk_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_PK.

Definition wots_c_grind_class (t : tweak) : bool :=
  t.1.1.1.2 == SF_WOTS_C_GRIND.

(* Grinding puts the first twelve digest bytes in the tweak payload and the remaining bytes in the message. The anchor and address type stay fixed. *)
Definition grinding_tweak (t : tweak) (digest : Bytes 32) : tweak :=
  let: (height, index, address_type, word1, word2, word3) := t in
  (height, index, address_type,
   int_from_bytes U32 (slice digest 0 4),
   int_from_bytes U32 (slice digest 4 4),
   int_from_bytes U32 (slice digest 8 4)).

Definition grinding_message (digest : Bytes 32) (counter : UInt16) : seq UInt8 :=
  slice digest 12 20 ++ zeros 4 ++ int_to_bytes counter 2.

(* F, PRF and T_sf use this hash at their address fields. Grinding uses the encoded tweak and message. Every result has sixteen bytes. *)
Definition Th (pk_seed : Bytes 16) (t : tweak) (M : seq UInt8) : Bytes 16 :=
  let: (height, index, address_type, word1, word2, word3) := t in
  slice (sha256 (pk_seed ++ zeros 48 ++ pack height index address_type word1 word2 word3 ++ M)) 0 16.

(* The PRF key is the secret seed. Its input contains the public seed and the tweak. *)
Definition shrincs_prf (pk_seed : bytes 16) (t : tweak) (sk_seed : bytes 16) : bytes 16 :=
  Th pk_seed t sk_seed.

Definition wots_c_w : nat := 2 ^ WOTS_C_CHAIN_BITS.
Definition wots_c_chain_count : nat := WOTS_C_CHAIN_COUNT.
Definition wots_c_counter_max : nat := 2 ^ 16.

(* The chain games sample hidden sixteen-byte inputs and encode them as byte sequences. Compression and grinding choose their target messages. *)
Definition shrincs_thf : thf := {|
  th_PP := bytes 16; th_T := tweak; th_M := 'list ('word U8); th_N := bytes 16;
  th_eval := Th;
  th_dPP := dBytes 16;
  th_dM := {code x ← dBytes 16 ;; ret (tval x)};
  th_dN := dBytes 16 |}.

Definition shrincs_khf_prf : khf := {|
  kh_K := bytes 16; kh_M := bytes 16 × tweak; kh_N := bytes 16;
  kh_eval := fun k pt => shrincs_prf pt.1 pt.2 k;
  kh_dK := dBytes 16; kh_dN := dBytes 16 |}.

Definition wots_c_grind_enc (t : tweak) (m : bytes 32) (c : nat)
    : tweak * seq UInt8 :=
  (grinding_tweak t m, grinding_message m (uint U16 c)).

(* This is the digit-sum test used by grinding and recovery in the specification. *)
Definition wots_c_grind_prp (g : bytes 16) : bool :=
  sumn (base_2b g WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT) == WOTS_C_CONSTANT_SUM.

Section AtTheAnchor.

(* The node height and index locate the WOTS+C key. Its anchor and tree shape are fixed within the experiment and universally quantified in the theorem. *)
Context (node_height : UInt8) (node_index : UInt64) (tree_balanced : bool) (tree_depth : UInt8).

(* The three operations are the specification entry points. Both keys carry the public seed, and signing leaves the secret key unchanged. *)
Definition wots_c_scheme : sig_scheme := {|
  Pk := bytes 16 × bytes 16;
  Sk := bytes 16 × bytes 16;
  Msg := bytes 32;
  Sig := bytes (2 + WOTS_C_CHAINS_SIZE);
  SParam := 'unit;
  keygen := fun _ => {code
    pk_seed ← dBytes 16 ;;
    sk_seed ← dBytes 16 ;;
    ret ((pk_seed, sk_seed),
         (pk_seed, wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth))};
  sign := fun sk message_digest => {code
    ret (omap (fun signature => (signature, sk))
           (wots_c_sign message_digest sk.2 sk.1 node_height node_index tree_balanced tree_depth))};
  verify := fun pk message_digest signature =>
    wots_c_pubkey_from_sig signature message_digest pk.1 node_height node_index == Some pk.2
|}.

Definition wots_c_kots_game := KOTS_vc_game wots_c_scheme.

End AtTheAnchor.
