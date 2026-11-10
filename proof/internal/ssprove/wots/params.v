(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.ssprove.wots.params

    The WOTS+C parameter record [wc_params]: one value carrying every
    section parameter the scheme, games, hops and bounds used to thread
    individually (types, Winternitz data, tweaks, the hash function,
    samplers and grinding data).  Downstream files take a single
    [Context (P : wc_params)] instead of a 19-line Context block, and
    every scheme/game constant is a plain definition applied to [P] --
    no [Local Notation] preamble.

    The record is deliberately abstract.  The hop proofs run [simpl]
    over game code that contains the grinding search and the chain
    folds; at a concrete instance those would unfold.

    ** Hash roles

    - [wcp_F]       the chain hash F, called at [wcp_tw_chain];
    - [wcp_T_sf]    the pk compression T_sf, called at [wcp_tw_pk];
    - [wcp_H_grind] evaluates grinding at its encoded tweak and message.
                    Its output is read as [chain_count] digits by
                    [wcp_digits], which is injective.

    Each role is derived from [wcp_Th]. The encoders place nodes, chain
    ends and grinding inputs in its common message space [wcp_HM].

    ** Tweaks

    A hash call is separated from every other by its tweak, a value of
    [wcp_Tw].  The record names the four families of tweaks one
    instance uses and states the two injectivity facts the proofs need:
    distinct chain steps and distinct chain starts have distinct
    tweaks.  Whatever locates the instance (its anchor in a tree) is
    inside the four fields; the model never looks at it.

    The second half of this file keeps the address vocabulary the hop
    files were written against ([grind_adrs], [encode_tweak],
    [chain_tweak], ...).  Each name is now a plain renaming of a record
    field, and encoding is the identity. *)

From Shrincs.internal.ssprove.lib Require Import prelude.

(* ================================================================== *)
(** ** The parameter record *)

Record wc_params := {
  (* Public seed, nodes, message digests, tweaks and hash messages. *)
  wcp_PP : choice_type ;
  wcp_N  : choice_type ;
  wcp_M  : choice_type ;
  wcp_Tw : choice_type ;
  wcp_HM : choice_type ;

  (* Winternitz parameter and chain count, with positivity. *)
  wcp_w           : nat ;
  wcp_chain_count : nat ;
  wcp_Hcc : (0 < wcp_chain_count)%nat ;
  wcp_Hw  : (1 < wcp_w)%nat ;

  (* The tweaks of this instance: step [pos] of chain [i], the start of
     chain [i], public key compression, grinding.  The first two are
     total on [nat]; they need only be injective on the indices the
     scheme reaches. *)
  wcp_tw_chain : nat -> nat -> wcp_Tw ;
  wcp_tw_prf   : nat -> wcp_Tw ;
  wcp_tw_pk    : wcp_Tw ;
  wcp_tw_grind : wcp_Tw ;
  wcp_tw_chain_inj : forall i pos i' pos' : nat,
    (i < wcp_chain_count)%nat -> (i' < wcp_chain_count)%nat ->
    (pos < wcp_w.-1)%nat -> (pos' < wcp_w.-1)%nat ->
    wcp_tw_chain i pos = wcp_tw_chain i' pos' -> i = i' /\ pos = pos' ;
  wcp_tw_prf_inj : forall i i' : nat,
    (i < wcp_chain_count)%nat -> (i' < wcp_chain_count)%nat ->
    wcp_tw_prf i = wcp_tw_prf i' -> i = i' ;

  wcp_Th : wcp_PP -> wcp_Tw -> wcp_HM -> wcp_N ;
  wcp_encode_node : wcp_N -> wcp_HM ;
  wcp_encode_node_inj : injective wcp_encode_node ;
  wcp_encode_ends : seq wcp_N -> wcp_HM ;
  wcp_encode_ends_inj : injective wcp_encode_ends ;
  wcp_encode_grind : wcp_Tw -> wcp_M -> nat -> wcp_Tw * wcp_HM ;

  (* Target classes are static. The grinding encoder changes payload
     words while retaining a grinding tweak outside the other classes. *)
  wcp_chain_class : pred wcp_Tw ;
  wcp_pk_class : pred wcp_Tw ;
  wcp_grind_class : pred wcp_Tw ;
  wcp_tw_chain_class : forall i pos, wcp_chain_class (wcp_tw_chain i pos) ;
  wcp_tw_pk_class : wcp_pk_class wcp_tw_pk ;
  wcp_tw_grind_class : wcp_grind_class wcp_tw_grind ;
  wcp_tw_chain_not_pk : forall i pos, ~~ wcp_pk_class (wcp_tw_chain i pos) ;
  wcp_encode_grind_class : forall m c,
    wcp_grind_class (wcp_encode_grind wcp_tw_grind m c).1 ;
  wcp_encode_grind_not_chain : forall m c,
    ~~ wcp_chain_class (wcp_encode_grind wcp_tw_grind m c).1 ;
  wcp_encode_grind_not_pk : forall m c,
    ~~ wcp_pk_class (wcp_encode_grind wcp_tw_grind m c).1 ;

  (* The digits of a grinding hash output, one per chain, each below
     [w].  The GRIND hop turns equal digit vectors into a collision on
     H_grind, which needs [wcp_digits_inj].  [wcp_G0] is an arbitrary
     inhabitant, read only on code paths the proofs show to be dead. *)
  wcp_digits : wcp_N -> seq nat ;
  wcp_digits_size : forall g : wcp_N, size (wcp_digits g) = wcp_chain_count ;
  wcp_digits_wf : forall g : wcp_N, all (fun d => (d < wcp_w)%nat) (wcp_digits g) ;
  wcp_digits_inj : injective wcp_digits ;
  wcp_G0 : wcp_N ;

  (* The signature as the adversary handles it.  The model works on
     its two parts, the chain values and the grinding counter:
     [wcp_sig_decode] splits a signature into them and
     [wcp_sig_encode] builds one.  The security proof needs no law
     relating the two: a forged signature is only ever decoded, an
     issued one only ever encoded. *)
  wcp_Sig : choice_type ;
  wcp_sig_encode : seq wcp_N * nat -> wcp_Sig ;
  wcp_sig_decode : wcp_Sig -> seq wcp_N * nat ;

  (* Key generation samples the public seed and the nodes. *)
  wcp_dPP : dist wcp_PP ;
  wcp_dN  : dist wcp_N ;

  (* Target chain-sum and grinding-counter bound (c_max = 2^{8c}). *)
  wcp_constant_sum : nat ;
  wcp_c_max        : nat ;
}.

Abbreviation wcp_G := wcp_N.

Definition wcp_F (P : wc_params) (pp : wcp_PP P) (t : wcp_Tw P) (x : wcp_N P)
    : wcp_N P :=
  wcp_Th P pp t (wcp_encode_node P x).

Definition wcp_T_sf (P : wc_params) (pp : wcp_PP P) (t : wcp_Tw P)
    (xs : seq (wcp_N P)) : wcp_N P :=
  wcp_Th P pp t (wcp_encode_ends P xs).

Definition wcp_H_grind (P : wc_params) (pp : wcp_PP P) (t : wcp_Tw P)
    (mc : wcp_M P * nat) : wcp_N P :=
  wcp_Th P pp (wcp_encode_grind P t mc.1 mc.2).1 (wcp_encode_grind P t mc.1 mc.2).2.

#[global] Arguments wcp_F : simpl never.
#[global] Arguments wcp_T_sf : simpl never.
#[global] Arguments wcp_H_grind : simpl never.

(** The two parts of a signature as a choice type: what the games
    store, as opposed to the encoded [wcp_Sig] their oracles exchange. *)
Definition wc_sig_parts (P : wc_params) : choice_type :=
  chProd (chList (wcp_N P)) chNat.

(* ================================================================== *)
(** ** Address vocabulary

    An address of the instance and its tweak are the same value. *)

Definition wc_adrs (P : wc_params) : Type := wcp_Tw P.

Definition wc_adrs_ch (P : wc_params) : choice_type := wcp_Tw P.

(** ADRS^g, the grinding address. *)
Definition grind_adrs (P : wc_params) : wc_adrs P := wcp_tw_grind P.

(** ADRS^pk, the pk-compression address. *)
Definition pk_adrs (P : wc_params) : wc_adrs P := wcp_tw_pk P.

(** ADRS^h, the address of step [pos] of chain [i]. *)
Definition chain_adrs (P : wc_params) (i pos : nat) : wc_adrs P := wcp_tw_chain P i pos.

(** ADRS^prf, the address of the start of chain [i]. *)
Definition prf_adrs (P : wc_params) (i : nat) : wc_adrs P := wcp_tw_prf P i.

(* ================================================================== *)
(** ** Tweak encoding

    [encode_tweak] and [decode_tweak] are the identity.  They stay as
    names because the hop proofs rewrite with the lemmas below; no
    [simpl] unfolds them, since neither reduces a [match]. *)

Definition encode_tweak (P : wc_params) (a : wc_adrs P) : wc_adrs_ch P := a.

Definition decode_tweak (P : wc_params) (t : wc_adrs_ch P) : wc_adrs P := t.

Lemma encode_tweakK (P : wc_params) : cancel (encode_tweak P) (decode_tweak P).
Proof. by []. Qed.

Lemma encode_tweak_inj (P : wc_params) : injective (encode_tweak P).
Proof. by []. Qed.

(** The per-hash-call chain tweak. *)
Definition chain_tweak (P : wc_params) (i pos : nat) : wc_adrs_ch P :=
  encode_tweak P (chain_adrs P i pos).

Definition prf_tweak (P : wc_params) (i : nat) : wc_adrs_ch P :=
  encode_tweak P (prf_adrs P i).

Lemma decode_chain_tweak (P : wc_params) (i pos : nat) :
  decode_tweak P (chain_tweak P i pos) = chain_adrs P i pos.
Proof. by []. Qed.

Lemma decode_prf_tweak (P : wc_params) (i : nat) :
  decode_tweak P (prf_tweak P i) = prf_adrs P i.
Proof. by []. Qed.

Lemma chain_tweak_inj (P : wc_params) (i pos i' pos' : nat) :
  (i < wcp_chain_count P)%nat -> (i' < wcp_chain_count P)%nat ->
  (pos < (wcp_w P).-1)%nat -> (pos' < (wcp_w P).-1)%nat ->
  chain_tweak P i pos = chain_tweak P i' pos' -> i = i' /\ pos = pos'.
Proof. exact: wcp_tw_chain_inj. Qed.

Lemma prf_tweak_inj (P : wc_params) (i i' : nat) :
  (i < wcp_chain_count P)%nat -> (i' < wcp_chain_count P)%nat ->
  prf_tweak P i = prf_tweak P i' -> i = i'.
Proof. exact: wcp_tw_prf_inj. Qed.
