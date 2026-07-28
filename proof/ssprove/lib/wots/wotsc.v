(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.lib.wots.wotsc

    THE generic WOTS+C (Compressed WOTS+) one-time signature scheme:
    the fixed-sum Winternitz chain layer of [Sec.lib.chain.core] plus
    grinding and public-key compression, over an ABSTRACT address type.

    Both anchored instances are definitional wrappers around it:
    - [Sec.wots.scheme]        (native, one [wc_params] record, MSB-first
                                digits: [dig_msb := true]);
    - [SHRINCS.wotsc.scheme]   (FXMSS, section-variable parameters,
                                LSB-first digits: [dig_msb := false]).

    Every name here carries the [wotsc_] prefix so that neither wrapper's
    unqualified printed name ([scheme.shrincs_wots_scheme],
    [scheme.find_ctr]) becomes ambiguous. *)

From Sec.lib Require Import prelude sig.scheme toolkit.sample_seq math.chain.
From Model Require Import math.encoding.

Import PackageNotation.
#[local] Open Scope package_scope.

Section WotsC.

(** Winternitz parameter, number of chains. *)
Context (w l : nat).

(** Public parameter (PKseed), hash domain, message space. *)
Context (PP N M : choice_type).

(** The instance's address/tweak type, kept abstract: the native tree
    passes [address.adrs chain_count w.-1], FXMSS passes [adrs_sf l w]. *)
Context (A : Type).

(** Chain hash, public-key compression, grinding hash. *)
Context (F : PP -> A -> N -> N).
Context (Tl : PP -> A -> seq N -> N).
Context (Hgrind : PP -> A -> M * nat -> nat).

(** Samplers for key generation. *)
Context (dPP : dist PP) (dN : dist N).

(** Target chain-sum, grinding-counter bound. *)
Context (tsum c_max : nat).

(** The instance's three addresses. *)
Context (grind_adrs pk_adrs : A) (chain_adrs : nat -> nat -> A).

(** Digit order: the native tree reads the digest MOST-significant digit
    first (matching shrincs.py's base-w parse and [Model.wots.base_2b]),
    FXMSS reads it least-significant first.  Both are self-consistent;
    only the chain-index-to-digit assignment differs. *)
Context (dig_msb : bool).

Definition wotsc_order (ds : seq nat) : seq nat := if dig_msb then rev ds else ds.

Lemma wotsc_order_size ds : size (wotsc_order ds) = size ds.
Proof. by rewrite /wotsc_order; case: dig_msb => //; rewrite size_rev. Qed.

Lemma wotsc_order_wf ds : wf_digits w (wotsc_order ds) = wf_digits w ds.
Proof. by rewrite /wotsc_order /wf_digits; case: dig_msb => //; rewrite all_rev. Qed.

Lemma wotsc_order_sumn ds : sumn (wotsc_order ds) = sumn ds.
Proof. by rewrite /wotsc_order; case: dig_msb => //; rewrite sumn_rev. Qed.

(* ------------------------------------------------------------------ *)
(** ** Grinding *)

Definition wotsc_digest_of (pp : PP) (m : M) (c : nat) : seq nat :=
  wotsc_order (digits_w w l (Hgrind pp grind_adrs (m, c))).

Definition wotsc_valid_digest (ds : seq nat) : bool :=
  wf_digits w ds && (sumn ds == tsum).

Definition wotsc_good_ctr (pp : PP) (m : M) (c : nat) : bool :=
  wotsc_valid_digest (wotsc_digest_of pp m c).

Definition wotsc_find_ctr (pp : PP) (m : M) : option nat :=
  ohead [seq c <- iota 0 c_max | wotsc_good_ctr pp m c].

Lemma wotsc_size_digest_of pp m c : size (wotsc_digest_of pp m c) = l.
Proof. by rewrite /wotsc_digest_of wotsc_order_size size_digits_w. Qed.

Lemma wotsc_find_ctrP pp m c :
  wotsc_find_ctr pp m = Some c -> wotsc_good_ctr pp m c && (c < c_max).
Proof.
rewrite /wotsc_find_ctr.
case E: [seq c0 <- iota 0 c_max | wotsc_good_ctr pp m c0] => [|c0 cs] //= [<-].
move: (mem_head c0 cs).
by rewrite -E mem_filter mem_iota add0n => /andP[-> /andP[_ ->]].
Qed.

Lemma wotsc_find_ctr_good pp m c : wotsc_find_ctr pp m = Some c -> wotsc_good_ctr pp m c.
Proof. by move=> /wotsc_find_ctrP /andP[h _]. Qed.

Lemma wotsc_find_ctr_lt pp m c : wotsc_find_ctr pp m = Some c -> c < c_max.
Proof. by move=> /wotsc_find_ctrP /andP[_ h]. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure scheme functions *)

Definition wotsc_chainf (pp : PP) (i : nat) : nat -> N -> N :=
  fun pos x => F pp (chain_adrs i pos) x.

Definition wotsc_chain_ends (pp : PP) (xs : seq N) : seq N :=
  [seq chain (wotsc_chainf pp ix.1) ix.2 0 w.-1 | ix <- zip (iota 0 l) xs].

Definition wotsc_pubkey (pp : PP) (xs : seq N) : N :=
  Tl pp pk_adrs (wotsc_chain_ends pp xs).

Definition wotsc_sign_chains (pp : PP) (xs : seq N) (ds : seq nat) : seq N :=
  [seq chain (wotsc_chainf pp ixd.1.1) ixd.1.2 0 ixd.2
  | ixd <- zip (zip (iota 0 l) xs) ds].

Definition wotsc_complete_ends (pp : PP) (ds : seq nat) (ys : seq N) : seq N :=
  [seq chain (wotsc_chainf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota 0 l) (zip ds ys)].

Definition wotsc_verify (pp : PP) (root : N) (m : M) (sg : seq N * nat) : bool :=
  [&& wotsc_valid_digest (wotsc_digest_of pp m sg.2), size sg.1 == l
    & Tl pp pk_adrs (wotsc_complete_ends pp (wotsc_digest_of pp m sg.2) sg.1) == root].

Definition wotsc_sign (pp : PP) (xs : seq N) (m : M) : option (seq N * nat) :=
  omap (fun c => (wotsc_sign_chains pp xs (wotsc_digest_of pp m c), c))
       (wotsc_find_ctr pp m).

(* ------------------------------------------------------------------ *)
(** ** Size sanity lemmas *)

Lemma wotsc_size_chain_ends pp xs : size (wotsc_chain_ends pp xs) = minn l (size xs).
Proof. by rewrite size_map size_zip size_iota. Qed.

Lemma wotsc_size_sign_chains pp xs ds :
  size (wotsc_sign_chains pp xs ds) = minn (minn l (size xs)) (size ds).
Proof. by rewrite size_map !size_zip size_iota. Qed.

Lemma wotsc_size_complete_ends pp ds ys :
  size (wotsc_complete_ends pp ds ys) = minn l (minn (size ds) (size ys)).
Proof. by rewrite size_map !size_zip size_iota. Qed.

(* ------------------------------------------------------------------ *)
(** ** Correctness *)

Lemma wotsc_complete_sign_chain pp st (xs : seq N) (ds : seq nat) :
  size ds = size xs -> wf_digits w ds ->
  [seq chain (wotsc_chainf pp q.1) q.2.2 q.2.1 (w.-1 - q.2.1)
  | q <- zip (iota st (size xs))
             (zip ds
                  [seq chain (wotsc_chainf pp ixd.1.1) ixd.1.2 0 ixd.2
                  | ixd <- zip (zip (iota st (size xs)) xs) ds])]
  = [seq chain (wotsc_chainf pp ix.1) ix.2 0 w.-1 | ix <- zip (iota st (size xs)) xs].
Proof.
elim: xs st ds => [|x xs IH] st [|d ds] //= [hsz] /andP[hd hds].
have hdw : d <= w.-1 by rewrite -ltnS (ltn_predK hd).
have hsp := chain_split (wotsc_chainf pp st) x (leq0n d) hdw.
rewrite !subn0 in hsp.
by rewrite -hsp; congr (_ :: _); apply: IH.
Qed.

Lemma wotsc_verify_sign_digits pp xs m c :
  size xs = l -> wotsc_find_ctr pp m = Some c ->
  wotsc_verify pp (wotsc_pubkey pp xs) m
    (wotsc_sign_chains pp xs (wotsc_digest_of pp m c), c) = true.
Proof.
move=> hxs hc.
have hgood : wotsc_good_ctr pp m c := wotsc_find_ctr_good _ _ _ hc.
have /andP[hwf _] := hgood.
have hszd : size (wotsc_digest_of pp m c) = l by rewrite wotsc_size_digest_of.
rewrite /wotsc_verify /=.
apply/and3P; split.
- exact: hgood.
- by rewrite wotsc_size_sign_chains hxs hszd !minnn eqxx.
- apply/eqP; rewrite /wotsc_pubkey; congr (Tl _ _ _).
  rewrite /wotsc_complete_ends /wotsc_chain_ends /wotsc_sign_chains -hxs.
  apply: wotsc_complete_sign_chain; last exact: hwf.
  by rewrite hszd hxs.
Qed.

Lemma wotsc_verify_sign pp xs m sg :
  size xs = l -> wotsc_sign pp xs m = Some sg ->
  wotsc_verify pp (wotsc_pubkey pp xs) m sg = true.
Proof.
move=> hxs; rewrite /wotsc_sign.
case E: (wotsc_find_ctr pp m) => [c|] //= [<-].
by apply: wotsc_verify_sign_digits.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The scheme *)

Definition wotsc_scheme : sig_scheme := {|
  Pk := PP × N ;
  Sk := PP × ('list N) ;
  Msg := M ;
  Sig := ('list N) × 'nat ;
  SParam := 'unit ;
  keygen := fun _ => {code
    pp ← dPP ;;
    xs ← sample_seq dN l ;;
    ret ((pp, xs), (pp, wotsc_pubkey pp xs)) } ;
  sign := fun sk m => {code
    ret (omap (fun sg => (sg, sk)) (wotsc_sign sk.1 sk.2 m)) } ;
  verify := fun pk m sg => wotsc_verify pk.1 pk.2 m sg
|}.

End WotsC.
