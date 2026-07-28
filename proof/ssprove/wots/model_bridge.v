(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.wots.model_bridge

    The games <-> model correspondence: the machine link between the
    SSProve games layer ([Sec.wots.scheme], nat/ordinal-valued,
    MSB-first digits) and the shared canonical model ([Model.wots],
    Stdlib/Z-valued) at the CONCRETE truncated-SHA256 instantiation
    ([Sec.axioms]'s [wc_sha256] record).  This is the
    claim the README used to make WITHOUT a machine proof: "the games
    scheme computes the same thing as the ground-truth model."

    ** Dictionary direction

    The games-layer values are ordinals ([N_shrincs = 'fin (2^128)] for
    hash values, [M_shrincs = 'fin (2^256)] for the message digest) and
    plain [nat]s (the grinding counter); the model side is byte strings
    and [Z].  Every statement here QUANTIFIES the games-side value and
    DECODES it to the model ([decode16 pp], [decode32 m], [Z.of_nat c])
    -- never the reverse (no model->games encoding appears in a
    statement's shape).  So the model's chain bounds ([fin (Z.of_nat
    len)]) never have to be materialized; the correspondence rides on
    [Sec.bridge]'s already-proved [digest_of_bridge] /
    [good_counter_bridge] and [Model.math.encoding]'s [be_num]/[digits_w]
    machinery.

    ** The 6.1 stratum (DIGITS + COUNTER)

    - [digest_of_modelE] (T1): the games digest equals the model digest
      (both [seq nat = list nat], plain equality);
    - [good_counter_modelE] (T2): the games grinding predicate equals
      the model's;
    - [find_from_seq] / [find_counter_modelE]: the games' ohead-filter
      search equals the model's fuel recursion (up to [Z.of_nat]).

    The counter orientation is [wots.find_counter ... = omap Z.of_nat
    (scheme.find_counter ...)] -- the model side (partial, [option Z])
    reads as [Z.of_nat] applied to the games side (partial, [option
    nat]); chosen so the search skeleton ([iota]/[ohead]) stays on the
    games side and only the found counter is transported.

    Later sub-phases (the fold adapter, pubkey / sign / verify
    correspondences) build on this file; the section markers below are
    the extension points.  The anchor-independent glue and round-trips
    live BEFORE the anchor section so a future scheme can reuse them.

    NOTE (omitted): [encode16_eqE] (an [==]-equivalence of [encode16] on
    16-byte strings) is NOT provided: the bare [==] on [sha256.block] /
    [N_shrincs] resolves, under this file's SSProve package imports, to a
    [Setoid] equivalence rather than mathcomp's [eq_op], so the statement
    does not elaborate as written.  The injective content it would carry
    is already available through [decode16_encode16] (decode is a left
    inverse of encode on 16-byte blocks); a downstream consumer that
    needs the boolean form can restate it with an explicit [eqtype.eq_op].

    IMPORT DISCIPLINE (see Sec.bridge / HashAssumptions headers,
    load-bearing): [BinInt] stays a plain [Import] and [Znat] a plain
    [Require] (qualified [Znat.Nat2Z.foo] access) -- `Require Import
    ZArith`/`Require Import Znat` both silently shadow mathcomp's nat
    "^" ([expn] -> [Nat.pow]).  Numeric comparisons take an explicit
    [%nat] annotation.  (Consequences seen here: the Z-scope "^"
    notation is absent, so [Zofnat_expn] spells [Z.pow]/[expn]
    explicitly; [Zle_0_nat] is unqualified-unavailable, discharged by
    [lia].) *)

From mathcomp Require Import all_boot all_order.
From Sec.lib Require Import prelude games.thf games.smtcr games.smpre games.smud
  games.stcrp games.prf sig.scheme sig.kots.
From Sec.lib Require Import chain.core.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Sec Require Import addressing.
From Sec.lib Require Import wots.wotsc.
From Sec.wots Require Import scheme games
  hop.grind hop.compress hop.chain_tcr hop.chain_pre hop.ud hop.prf.
Require Import Sec.wots.theorem.
From mathcomp Require Import reals.
Require Import Sec.wots.instantiation.
From Sec Require Import bridge.
Require Import Sec.axioms.
From Model Require wots byte address.
Require Model.theory.wots.
(* See header IMPORT DISCIPLINE. *)
From Stdlib Require Import BinInt Lia.
From Stdlib Require Znat.

Import PackageNotation.
Import GRing.Theory Num.Theory Order.POrderTheory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* [chain] is a Fixpoint over the step count; at the concrete numbers
   (w = 16) a bare [simpl] would unroll all 15 steps into nested [F]s
   and destroy every [chain]-headed rewrite below.  Blocked here; the
   fold is only ever peeled through [chain0]/[chain_rcons]. *)
#[local] Arguments chain : simpl never.

(* ------------------------------------------------------------------ *)
(** ** GLUE: mathcomp seq <-> Stdlib List frictions

    Minimal and local: the mathcomp/Stdlib primitives that print the
    same but are distinct constants.  [size]/[length] and [nth] arg
    order are the ones this stratum needs; [concat]/[flatten] is here
    for the pubkey/verify sub-phases (they [concat] the chain tips). *)

Lemma size_lengthE (T : Type) (s : seq T) : size s = length s.
Proof. by elim: s => [|a s IH] //=; rewrite IH. Qed.

Lemma nth_listE (T : Type) (x0 : T) (s : seq T) (n : nat) :
  nth x0 s n = List.nth n s x0.
Proof. by elim: s n => [|a s IH] [|n] //=. Qed.

Lemma concat_flatten (T : Type) (s : seq (seq T)) : List.concat s = flatten s.
Proof. by elim: s => [|a s IH] //=; rewrite IH. Qed.

(* ------------------------------------------------------------------ *)
(** ** ROUND-TRIPS: the encode/decode dictionary is lossless

    Anchor-independent facts about [digit_byte] / [decode_block] /
    [encode16] (the HashAssumptions encoding).  [decode16_encode16] is
    the reverse companion of HashAssumptions' [encode16_decode16]:
    together they make the 16-byte-block <-> [N_shrincs] correspondence
    a genuine bijection on 16-byte blocks. *)

(** Byte-level round trip (nat -> byte -> nat). *)
Lemma digit_byteK (d : nat) : (d < 256)%nat -> Z.to_nat (byte.byte_val (digit_byte d)) = d.
Proof. by move=> hd; rewrite digit_byte_val // Znat.Nat2Z.id. Qed.

(** Byte-level round trip (byte -> nat -> byte): [digit_byte] recovers
    the byte from its [Z.to_nat]-projected value. *)
Lemma digit_byte_bytevalK (b : byte.byte) : digit_byte (Z.to_nat (byte.byte_val b)) = b.
Proof.
rewrite /digit_byte.
have [h0 h256] := byte.byte_val_range b.
rewrite Znat.Z2Nat.id; last lia.
rewrite (byte.byte_mod256_small (byte.byte_val b) (byte.byte_val_range b)).
by apply: byte.byte_eq; rewrite byte.byte_val_of.
Qed.

(** Block-level round trip: decoding the big-endian value of a byte
    string's [size]-many bytes recovers the string.  ([decode16_encode16]
    below is this at [size = 16].) *)
Lemma decode_block_nat_bytesK (X : sha256.block) :
  decode_block (size X) (be_num (nat_bytes X)) = X.
Proof.
have hwf : wf_digits 256 (rev (nat_bytes X)).
  rewrite /wf_digits all_rev; apply/allP => v hv.
  case/mapP: hv => b hb ->.
  have [h0 h256] := byte.byte_val_range b; apply/ltP; lia.
have hd : digits_w 256 (size X) (be_num (nat_bytes X)) = rev (nat_bytes X).
  have hsz : size (rev (nat_bytes X)) = size X by rewrite size_rev size_map.
  have hbe : be_num (nat_bytes X) = num_of_digits 256 (rev (nat_bytes X)).
    by rewrite -{1}(revK (nat_bytes X)) be_num_rev.
  rewrite hbe -{1}hsz num_of_digitsK //.
rewrite /decode_block hd map_rev revK /nat_bytes -map_comp -[RHS]map_id.
by apply/eq_in_map => b hb /=; exact: digit_byte_bytevalK.
Qed.

(** The soundness reverse of HashAssumptions' [encode16_decode16]:
    encode-then-decode is the identity on every 16-byte block (the size
    hypothesis is real -- [encode16] normalizes shorter/longer blocks
    through [block16_norm]). *)
Lemma decode16_encode16 (Y : sha256.block) : size Y = 16 -> decode16 (encode16 Y) = Y.
Proof.
move=> hY.
rewrite /decode16 val_encode16 (block16_norm_id Y hY).
have h := decode_block_nat_bytesK Y.
by rewrite hY in h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** COUNTER: generic search-skeleton glue (anchor-independent)

    [find_fromS] is the one-step unfold of the model's fuel recursion
    (kept as a lemma so the [find_from_seq] induction never has to make
    the kernel WHNF the [Fixpoint]); [Zofnat_expn] / [c_max_natE] bridge
    the two spellings of [2^16] WITHOUT computing it (the model and games
    both keep [c_max] symbolic -- reducing it would force the [2^16]-fuel
    [find_from] recursion). *)

Lemma find_fromS (pk : sha256.block) (A : address.adrs wots.len wots.w_pred)
    (M : sha256.block) (f : nat) (c : Z) :
  wots.find_from pk A M f.+1 c
  = if wots.good_counter pk A M c then Some c else wots.find_from pk A M f (c + 1)%Z.
Proof. by []. Qed.

(** [Z.of_nat] of a nat [expn] is the [Z.pow] of the [Z.of_nat]s --
    stated with [expn]/[Z.pow] SPELLED (the "^" notations are
    scope-ambiguous here; see header). *)
Lemma Zofnat_expn (a b : nat) : Z.of_nat (expn a b) = Z.pow (Z.of_nat a) (Z.of_nat b).
Proof.
elim: b => [|b IH]; first by rewrite expn0.
rewrite expnS Znat.Nat2Z.inj_mul IH Znat.Nat2Z.inj_succ.
rewrite Z.pow_succ_r; last by lia.
by [].
Qed.

(** The two [2^16]s agree: [Z.to_nat] of the model's Z-valued [c_max]
    is the games' nat-valued [c_max_shrincs].  Kept symbolic. *)
Lemma c_max_natE : Z.to_nat wots.c_max = c_max_shrincs.
Proof.
have h : Z.of_nat c_max_shrincs = wots.c_max.
  by rewrite /c_max_shrincs /wots.c_max Zofnat_expn.
by rewrite -h Znat.Nat2Z.id.
Qed.

(* ------------------------------------------------------------------ *)
(** ** LENGTHS: every model hash output is a 16-byte block

    ([decode16_encode16]'s size side condition is discharged by these
    at every fold step.) *)

Lemma thash_length (pk : sha256.block) (A : address.adrs wots.len wots.w_pred)
    (M : sha256.block) : length (wots.thash pk A M) = 16%nat.
Proof. by rewrite /wots.thash /wots.trunc16 List.length_firstn wots.length_sha256'. Qed.

(** The chain fold preserves 16-byte-ness: position count [n] steps of
    [F] (each a [thash]) from a 16-byte start. *)
Lemma chain_iter_length (X : sha256.block) (st n : nat) (pk : sha256.block)
    (A : address.adrs wots.len wots.w_pred) (H : ((st + n)%coq_nat <= wots.w_pred)%coq_nat) :
  length X = 16%nat ->
  length (wots.shrincs_wots_chain_iter X st n pk A H) = 16%nat.
Proof.
by elim: n H => [|k IH] H hX //=; rewrite thash_length.
Qed.

(** The chain fold from a DECODED 16-byte block stays 16 bytes: the
    recurring [decode16_encode16] size side-condition at every fold step
    (the start [decode16 x] is 16 bytes by [size_decode_block]). *)
Lemma chain_iter_decode16_length (x : N_shrincs) (st n : nat) (pk : sha256.block)
    (A : address.adrs wots.len wots.w_pred) (Hb : ((st + n)%coq_nat <= wots.w_pred)%coq_nat) :
  length (wots.shrincs_wots_chain_iter (decode16 x) st n pk A Hb) = 16%nat.
Proof. by apply: chain_iter_length; rewrite -size_lengthE /decode16 size_decode_block. Qed.

(* ================================================================== *)
(** ** The anchored correspondence

    Everything below is anchored at a fixed leaf position [(zstar,
    istar)] -- the instance anchor threaded through [wc_sha256] and,
    on the model side, through [A0]. *)

Section model_bridge.

(** The instance anchor (any leaf position; see Sec.wots.scheme).  No
    range hypothesis: [Sec.addressing] places both anchor components
    exact-or-zero. *)
Context (zstar istar : nat).

(** The games parameter record at the SHA-256 hashes and this anchor.
    A section-local [Let] (transparent; substituted inline into every
    statement at section close, so the compiled lemmas read
    [wc_sha256 zstar istar] -- no notation pin). *)
Let P := wc_sha256 zstar istar.

(** The model-side anchor address: the facade's [wc_pk_adrs] carrier at
    [(zstar, istar)].  Its type [address.adrs chain_count_shrincs
    w_shrincs.-1] is CONVERTIBLE to [Model.wots]'s [adrs = address.adrs
    wots.len wots.w_pred] ([chain_count_shrincs = wots.len = 32],
    [w_shrincs.-1 = wots.w_pred = 15]), so [A0] passes directly wherever
    a [Model.wots] address is expected. *)
Definition A0 : address.adrs chain_count_shrincs w_shrincs.-1 :=
  addressing.wc_pk_adrs (wc_anchor P).

(** The games' grind address IS the model's grind-typing of [A0]. *)
Lemma grind_adrsE : grind_adrs P = address.shrincs_wots_grind_adrs A0.
Proof. by rewrite /grind_adrs /A0. Qed.

(** The crux: the games' nat-valued grinding hash reads the concrete
    SHA-256 [H_grind] output (at [A0]) as a big-endian number. *)
Lemma Hgrind_natE (pp : PP_shrincs) (m : M_shrincs) (c : nat) :
  wcp_H_grind P pp (grind_adrs P) (m, c)
  = be_num (nat_bytes (wots.H_grind (decode16 pp) (address.shrincs_wots_grind_adrs A0) (decode32 m) (Z.of_nat c))).
Proof.
rewrite grind_adrsE.
have hE : wcp_H_grind P pp (address.shrincs_wots_grind_adrs A0) (m, c)
        = nat_of_ord (H_grind0_sha256 pp (address.shrincs_wots_grind_adrs A0) (m, c)) by [].
rewrite hE /H_grind0_sha256 val_encode16.
rewrite block16_norm_id; last by rewrite size_lengthE wots.H_grind_length.
by [].
Qed.

(** T1: the games digest equals the model digest (both [seq nat = list
    nat]).  The digit order already matches ([scheme.digest_of] is
    MSB-first, [rev (digits_w ...)], as is [Model.wots] via
    [digest_of_bridge]), so this is a plain equality. *)
Lemma digest_of_modelE (pp : PP_shrincs) (m : M_shrincs) (c : nat) :
  Sec.wots.scheme.digest_of P pp m c
  = wots.digest_of (decode16 pp) A0 (decode32 m) (Z.of_nat c).
Proof.
by rewrite Sec.wots.scheme.digest_of_def digest_of_bridge Hgrind_natE.
Qed.

(** T2: the games grinding predicate equals the model's.  ([wf_digits]
    and [sumn] are [rev]-invariant, which absorbs the MSB/LSB [rev]
    difference between [scheme.digest_of] and [good_counter_bridge]'s
    un-[rev]'d [digits_w].) *)
Lemma good_counter_modelE (pp : PP_shrincs) (m : M_shrincs) (c : nat) :
  Sec.wots.scheme.good_counter P pp m c
  = wots.good_counter (decode16 pp) A0 (decode32 m) (Z.of_nat c).
Proof.
rewrite good_counter_bridge Sec.wots.scheme.good_counter_def Sec.wots.scheme.valid_digest_def.
by rewrite !digest_of_modelE !digest_of_bridge /wf_digits all_rev sumn_rev.
Qed.

(** The counter search connects the model's fuel recursion
    ([find_from], List.find-shaped) to the games' [ohead]-filter over
    [iota], one induction on the fuel, transporting the found counter by
    [Z.of_nat] and casing the head predicate through [good_counter_modelE]. *)
Lemma find_from_seq (pp : PP_shrincs) (m : M_shrincs) (fuel start : nat) :
  wots.find_from (decode16 pp) A0 (decode32 m) fuel (Z.of_nat start)
  = omap Z.of_nat (ohead [seq c <- iota start fuel | Sec.wots.scheme.good_counter P pp m c]).
Proof.
elim: fuel start => [|f IH] start; first by [].
rewrite find_fromS.
have -> : (Z.of_nat start + 1)%Z = Z.of_nat start.+1 by rewrite Znat.Nat2Z.inj_succ; lia.
rewrite IH.
have -> : [seq c <- iota start f.+1 | Sec.wots.scheme.good_counter P pp m c]
        = if Sec.wots.scheme.good_counter P pp m start
          then start :: [seq c <- iota start.+1 f | Sec.wots.scheme.good_counter P pp m c]
          else [seq c <- iota start.+1 f | Sec.wots.scheme.good_counter P pp m c]
  by [].
rewrite -(good_counter_modelE pp m start).
by case: (Sec.wots.scheme.good_counter P pp m start).
Qed.

(** The whole grinding search corresponds: the model's [find_counter]
    (fuel [Z.to_nat c_max], start 0) is the games' [find_counter]
    (bounded [ohead]-filter over [iota 0 c_max_shrincs]) transported by
    [omap Z.of_nat]. *)
Lemma find_counter_modelE (pp : PP_shrincs) (m : M_shrincs) :
  wots.find_counter (decode16 pp) A0 (decode32 m)
  = omap Z.of_nat (Sec.wots.scheme.find_counter P pp m).
Proof.
rewrite /wots.find_counter -[0%Z]/(Z.of_nat 0%nat) find_from_seq.
by rewrite /Sec.wots.scheme.find_counter c_max_natE.
Qed.

(* ---------------------------------------------------------------- *)
(** ** Address agreement (the 6.2 stratum, part D)

    The games' P-applied instance addresses ARE the model's smart
    constructors on [A0].  The chain-carrying ones are stated for
    ARBITRARY [fin] fields pinned only by their values, so they rewrite
    against whichever Z-side range proof the model fold supplies. *)

(** The games' pk address IS the model's pk-typing of [A0]. *)
Lemma pk_adrsE : pk_adrs P = address.shrincs_wots_pk_adrs A0.
Proof. by []. Qed.

(** The games' prf address of chain [i] IS the model's, at ANY [fin]
    chain field valued [Z.of_nat i].  Both anchor slots are the SAME
    exact-or-zero placer term on either side ([A0] is the pk-typed
    carrier of the very same anchor), so only the chain field needs a
    bridge. *)
Lemma prf_adrs_modelE (i : nat) (Hi : (i < chain_count_shrincs)%nat)
    (ci : fin.fin (Z.of_nat wots.len)) (Hci : fin.fin_val ci = Z.of_nat i) :
  prf_adrs P i = address.shrincs_wots_prf_adrs A0 ci.
Proof.
rewrite /prf_adrs (addressing.wc_prf_adrs_finE chain_count_shrincs w_shrincs
  (wc_anchor P) i ci (addressing.component_bounded_lt _ _ Hi) Hci).
by [].
Qed.

(** The games' (total) chain address at in-range [(i, pos)] IS the
    model fold's per-step address [set_hash_pos (hash_adrs _ A0 ci) cp]
    -- for ANY positivity proof [hp] and ANY [fin] fields valued
    [Z.of_nat i] / [Z.of_nat pos] ([set_hash_pos] overwrites the
    position slot, so [hp]'s initial-position proof term is inert). *)
Lemma chain_adrs_modelE (i pos : nat)
    (Hi : (i < chain_count_shrincs)%nat) (Hpos : (pos < w_shrincs.-1)%nat)
    (hp : (0 < wots.w_pred)%coq_nat)
    (ci : fin.fin (Z.of_nat wots.len)) (cp : fin.fin (Z.of_nat wots.w_pred)) :
  fin.fin_val ci = Z.of_nat i -> fin.fin_val cp = Z.of_nat pos ->
  chain_adrs P i pos
  = address.set_hash_pos (address.shrincs_wots_hash_adrs hp A0 ci) cp.
Proof.
move=> Hvi Hvp.
rewrite /chain_adrs (addressing.wc_hash_adrs_finE chain_count_shrincs w_shrincs
  (wc_anchor P) i pos ci cp (addressing.component_bounded_lt _ _ Hi)
  (addressing.component_bounded_lt _ _ Hpos) Hvi Hvp).
by [].
Qed.

(* ---------------------------------------------------------------- *)
(** ** T3: the fold adapter (the games' total fold IS the model's
    dependent fold)

    Both folds apply positions [st, ..., st + n - 1] in ascending
    order; the induction end-peels BOTH sides ([chain_rcons] against
    the model Fixpoint's native peel), with the model's bound proof
    universally quantified so the IH instantiates it with the
    recursive occurrence's own proof -- no proof irrelevance needed. *)

Lemma chain_chain_iterE (pp : PP_shrincs) (x : N_shrincs) (i st n : nat)
    (Hi : (i < chain_count_shrincs)%nat)
    (hp : (0 < wots.w_pred)%coq_nat)
    (ci : fin.fin (Z.of_nat wots.len)) (Hci : fin.fin_val ci = Z.of_nat i)
    (Hb : ((st + n)%coq_nat <= wots.w_pred)%coq_nat) :
  chain (Sec.wots.scheme.chainf P pp i) x st n
  = encode16 (wots.shrincs_wots_chain_iter (decode16 x) st n (decode16 pp)
                (address.shrincs_wots_hash_adrs hp A0 ci) Hb).
Proof.
elim: n Hb => [|n IH] Hb.
- (* 0 steps: both folds are the identity; close the dictionary. *)
  by rewrite chain0 /= encode16_decode16.
- (* end-peel both sides; the model's outermost step is at [st + n]. *)
  rewrite (chain_rcons (Sec.wots.scheme.chainf P pp i) x st n) /=.
  (* the peeled position is in range: [st + n < w_pred < w] *)
  have Hb' : ((st + n).+1 <= wots.w_pred)%nat by rewrite -addnS; apply/leP.
  have Hlt : ((st + n)%nat < w_shrincs)%nat
    := ltn_trans Hb' (isT : (wots.w_pred < w_shrincs)%nat).
  rewrite (IH (wots.chain_iter_rec_le st n Hb)) /Sec.wots.scheme.chainf.
  have hlen : length (wots.shrincs_wots_chain_iter (decode16 x) st n (decode16 pp)
                        (address.shrincs_wots_hash_adrs hp A0 ci)
                        (wots.chain_iter_rec_le st n Hb)) = 16%nat
    by apply: chain_iter_decode16_length.
  rewrite /F_sha256 decode16_encode16; last by rewrite size_lengthE.
  have Hposn : ((st + n)%nat < w_shrincs.-1)%nat := Hb'.
  rewrite (chain_adrs_modelE i (st + n)%nat Hi Hposn hp ci
             (fin.fin_of_nat (Z.of_nat wots.w_pred) ((st + n)%coq_nat)
                (wots.chain_iter_pos_lt st n Hb)) Hci
             (fin.fin_val_of_nat _ _ _)).
  by [].
Qed.

(* ---------------------------------------------------------------- *)
(** ** T4: key derivation, chain tips, and THE pubkey correspondence *)

(** The games' PRF-derived chain start of chain [i] decodes to the
    model's [shrincs_wots_derive_sk] at the same chain. *)
Lemma derive_sk_modelE (pp : PP_shrincs) (k : K_shrincs) (i : nat)
    (Hi : (i < chain_count_shrincs)%nat)
    (ci : fin.fin (Z.of_nat wots.len)) (Hci : fin.fin_val ci = Z.of_nat i) :
  decode16 (PRF_sha256 pp (prf_adrs P i) k)
  = wots.shrincs_wots_derive_sk ci (decode16 k) (decode16 pp) A0.
Proof.
rewrite /PRF_sha256 (prf_adrs_modelE i Hi ci Hci) decode16_encode16 //.
by rewrite size_lengthE /wots.PRF thash_length.
Qed.

(** The games' chain ends over the PRF-derived key decode elementwise
    to the model's [chain_tips]. *)
Lemma chain_ends_tipsE (pp : PP_shrincs) (k : K_shrincs) :
  map decode16 (chain_ends P pp (derive_sk P K_shrincs PRF_sha256 pp k))
  = wots.chain_tips (decode16 k) (decode16 pp) A0.
Proof.
set xs := derive_sk P K_shrincs PRF_sha256 pp k.
have hxs : size xs = chain_count_shrincs by rewrite /xs size_derive_sk.
have hsz : size (chain_ends P pp xs) = chain_count_shrincs
  := size_chain_ends_l P pp xs hxs.
have hszt : size (wots.chain_tips (decode16 k) (decode16 pp) A0) = chain_count_shrincs.
  by rewrite size_lengthE /wots.chain_tips iteration.length_for_idx_dep.
apply: (@eq_from_nth _ (decode16 n0_shrincs)).
  by rewrite size_map hsz hszt.
move=> j; rewrite size_map hsz => Hj.
have HjP : (j < wots.len)%coq_nat by apply/ltP.
rewrite (nth_map n0_shrincs); last by rewrite hsz.
rewrite /chain_ends (nth_map (0%nat, n0_shrincs)); last
  by rewrite size_zip size_iota hxs minnn.
rewrite nth_zip ?size_iota ?hxs // nth_iota //= add0n.
rewrite (nth_listE _ (decode16 n0_shrincs)
           (wots.chain_tips (decode16 k) (decode16 pp) A0) j)
        /wots.chain_tips (iteration.nth_for_idx_dep wots.len _ _ j HjP).
have hnth : nth n0_shrincs xs j = PRF_sha256 pp (prf_adrs P j) k.
  rewrite /xs /derive_sk (nth_map 0%nat) ?size_iota //.
  by rewrite nth_iota // add0n.
rewrite hnth.
rewrite (chain_chain_iterE pp (PRF_sha256 pp (prf_adrs P j) k) j 0 w_shrincs.-1
           Hj wots.w_pred_pos
           (fin.fin_of_nat (Z.of_nat wots.len) j (wots.chain_idx_lt j HjP)))
  ?fin.fin_val_of_nat //.
rewrite decode16_encode16; last first.
  by rewrite size_lengthE; apply: chain_iter_decode16_length.
by rewrite (derive_sk_modelE pp k j Hj
              (fin.fin_of_nat (Z.of_nat wots.len) j (wots.chain_idx_lt j HjP))
              (fin.fin_val_of_nat _ _ _)).
Qed.

(** T4 HEADLINE: the keyed games public key IS the model's
    [shrincs_wots_pubkey_gen] (the spec's wots_c_pubkey_gen), through
    the dictionary. *)
Lemma pubkey_gen_modelE (pp : PP_shrincs) (k : K_shrincs) :
  shrincs_wots_pubkey P pp (derive_sk P K_shrincs PRF_sha256 pp k)
  = encode16 (wots.shrincs_wots_pubkey_gen (decode16 k) (decode16 pp) A0).
Proof.
rewrite Sec.wots.scheme.shrincs_wots_pubkey_def /wots.shrincs_wots_pubkey_gen.
have -> : wcp_T_sf P = T_sf_sha256 by [].
by rewrite /T_sf_sha256 pk_adrsE concat_flatten chain_ends_tipsE.
Qed.

(* ---------------------------------------------------------------- *)
(** ** T5: signing, chain completion, verification, and the signing
    correspondence (the FINAL stratum)

    The signature-side companions of T4.  [sign_chains_modelE] and
    [complete_ends_modelE] are the fold adapter [chain_chain_iterE]
    applied elementwise (per chain [j]) at a message digit rather than
    at [w-1]: the step count / start position is now the digest digit
    [ds[j]], whose in-range bound is exactly the model's own
    [sign_chain_bound] / [complete_chain_bound] -- supplied as the
    fold's [Hb] so both sides carry the SAME bound proof (no
    proof-irrelevance step).  The digit vectors [ds] are aligned by T1
    ([digest_of_modelE]) up front, so the games' [nth] step counts land
    on the model's [ds[j]] on the nose. *)

(** The games' signature chains over the PRF-derived key, at the digest
    the games supply, decode elementwise to the model's [sign_chains]
    (which recomputes the SAME digest internally -- aligned via T1). *)
Lemma sign_chains_modelE (pp : PP_shrincs) (k : K_shrincs) (m : M_shrincs) (c : nat) :
  map decode16 (Sec.wots.scheme.sign_chains P pp (derive_sk P K_shrincs PRF_sha256 pp k)
                  (Sec.wots.scheme.digest_of P pp m c))
  = wots.sign_chains (decode32 m) (decode16 k) (decode16 pp) A0 (Z.of_nat c).
Proof.
rewrite digest_of_modelE.
set D := wots.digest_of (decode16 pp) A0 (decode32 m) (Z.of_nat c).
set xs := derive_sk P K_shrincs PRF_sha256 pp k.
have hxs : size xs = chain_count_shrincs by rewrite /xs size_derive_sk.
have hdD : size D = chain_count_shrincs.
  by rewrite /D -digest_of_modelE size_digest_of.
have hsz : size (Sec.wots.scheme.sign_chains P pp xs D) = chain_count_shrincs
  := size_sign_chains_l P pp xs D hxs hdD.
have hszm : size (wots.sign_chains (decode32 m) (decode16 k) (decode16 pp) A0 (Z.of_nat c)) = chain_count_shrincs.
  by rewrite size_lengthE /wots.sign_chains iteration.length_for_idx_dep.
apply: (@eq_from_nth _ (decode16 n0_shrincs)).
  by rewrite size_map hsz hszm.
move=> j; rewrite size_map hsz => Hj.
have HjP : (j < wots.len)%coq_nat by apply/ltP.
rewrite (nth_map n0_shrincs); last by rewrite hsz.
rewrite /Sec.wots.scheme.sign_chains (nth_map ((0%nat, n0_shrincs), 0%nat)); last first.
  by rewrite !size_zip size_iota hxs hdD !minnn.
rewrite nth_zip; last by rewrite size_zip size_iota hxs hdD minnn.
rewrite nth_zip; last by rewrite size_iota hxs.
rewrite nth_iota // add0n /=.
rewrite (nth_listE _ (decode16 n0_shrincs)
           (wots.sign_chains (decode32 m) (decode16 k) (decode16 pp) A0 (Z.of_nat c)) j).
rewrite /wots.sign_chains.
rewrite (iteration.nth_for_idx_dep wots.len _ (decode16 n0_shrincs) j HjP).
have hnth : nth n0_shrincs xs j = PRF_sha256 pp (prf_adrs P j) k.
  rewrite /xs /derive_sk (nth_map 0%nat) ?size_iota //.
  by rewrite nth_iota // add0n.
rewrite hnth (nth_listE _ 0%N D j).
rewrite (chain_chain_iterE pp (PRF_sha256 pp (prf_adrs P j) k) j 0 (List.nth j D 0%nat)
           Hj wots.w_pred_pos
           (fin.fin_of_nat (Z.of_nat wots.len) j (wots.chain_idx_lt j HjP))
           (fin.fin_val_of_nat _ _ _)
           (wots.sign_chain_bound (decode16 pp) A0 (decode32 m) (Z.of_nat c) j)).
rewrite decode16_encode16; last first.
  by rewrite size_lengthE; apply: chain_iter_decode16_length.
by rewrite (derive_sk_modelE pp k j Hj
              (fin.fin_of_nat (Z.of_nat wots.len) j (wots.chain_idx_lt j HjP))
              (fin.fin_val_of_nat _ _ _)).
Qed.

(** The games' verifier-side chain completion, over ARBITRARY start
    values [ys] (the received signature values), decodes elementwise to
    the model's [complete_ends] on [map decode16 ys].  The size gate
    [size ys = chain_count] aligns the [zip]s; the digest is again
    supplied at the games' [digest_of] and aligned by T1. *)
Lemma complete_ends_modelE (pp : PP_shrincs) (m : M_shrincs) (c : nat) (ys : seq N_shrincs) :
  size ys = chain_count_shrincs ->
  map decode16 (Sec.wots.scheme.complete_ends P pp (Sec.wots.scheme.digest_of P pp m c) ys)
  = wots.complete_ends (decode32 m) (map decode16 ys) (Z.of_nat c) (decode16 pp) A0.
Proof.
move=> hys.
rewrite digest_of_modelE.
set D := wots.digest_of (decode16 pp) A0 (decode32 m) (Z.of_nat c).
have hdD : size D = chain_count_shrincs by rewrite /D -digest_of_modelE size_digest_of.
have hsz : size (Sec.wots.scheme.complete_ends P pp D ys) = chain_count_shrincs.
  by rewrite size_complete_ends hdD hys !minnn.
have hszm : size (wots.complete_ends (decode32 m) (map decode16 ys) (Z.of_nat c) (decode16 pp) A0) = chain_count_shrincs.
  by rewrite size_lengthE /wots.complete_ends iteration.length_for_idx_dep.
apply: (@eq_from_nth _ (decode16 n0_shrincs)).
  by rewrite size_map hsz hszm.
move=> j; rewrite size_map hsz => Hj.
have HjP : (j < wots.len)%coq_nat by apply/ltP.
rewrite (nth_map n0_shrincs); last by rewrite hsz.
rewrite /Sec.wots.scheme.complete_ends (nth_map (0%nat, (0%nat, n0_shrincs))); last first.
  by rewrite size_zip size_iota size_zip hdD hys !minnn.
rewrite nth_zip; last by rewrite size_iota size_zip hdD hys minnn.
rewrite nth_zip; last by rewrite hdD hys.
rewrite nth_iota // add0n /=.
rewrite (nth_listE _ (decode16 n0_shrincs)
           (wots.complete_ends (decode32 m) [seq decode16 i | i <- ys] (Z.of_nat c) (decode16 pp) A0) j).
rewrite /wots.complete_ends.
rewrite (iteration.nth_for_idx_dep wots.len _ (decode16 n0_shrincs) j HjP).
rewrite (nth_listE _ 0%N D j).
rewrite (chain_chain_iterE pp (nth n0_shrincs ys j) j (List.nth j D 0%nat)
           _ Hj wots.w_pred_pos
           (fin.fin_of_nat (Z.of_nat wots.len) j (wots.chain_idx_lt j HjP))
           (fin.fin_val_of_nat _ _ _)
           (wots.complete_chain_bound (decode16 pp) A0 (decode32 m) (Z.of_nat c) j)).
rewrite decode16_encode16; last first.
  by rewrite size_lengthE; apply: chain_iter_decode16_length.
rewrite -(nth_listE _ iteration.default (map decode16 ys) j) (nth_map n0_shrincs); last by rewrite hys.
by [].
Qed.

(** T5 HEADLINE: the games' boolean verifier IS the model's, through the
    dictionary.  Under the size gate [size sig = chain_count] (which
    makes the games' [size sg == chain_count] conjunct [true], absorbing
    it), the two agree: the valid-digest conjunct is T2 (as
    [good_counter_modelE]); the recompress-and-compare conjunct bridges
    the games' [T_sf == root] (an [eq_op] on [N_shrincs]) to the model's
    [list_eq_dec]-on-blocks via the [encode16]/[decode16] bijection --
    [encode16 X == root] iff [X = decode16 root] for the 16-byte pubkey
    [X] (a boolean EQUALITY, both directions cased). *)
Lemma verify_modelE (pp : PP_shrincs) (root : N_shrincs) (m : M_shrincs)
    (sig : seq N_shrincs) (c : nat) :
  size sig = chain_count_shrincs ->
  Sec.wots.scheme.shrincs_wots_verify P pp root m (sig, c)
  = wots.shrincs_wots_verify (decode16 root) (map decode16 sig) (decode32 m) (Z.of_nat c) (decode16 pp) A0.
Proof.
move=> hsig.
rewrite Sec.wots.scheme.shrincs_wots_verify_def.
cbn [fst snd].
rewrite /wots.shrincs_wots_verify.
have hcc : wcp_chain_count P = chain_count_shrincs by [].
rewrite hcc hsig eqxx andTb.
congr andb.
  exact: (good_counter_modelE pp m c).
have hTsf : wcp_T_sf P pp (pk_adrs P) (Sec.wots.scheme.complete_ends P pp (Sec.wots.scheme.digest_of P pp m c) sig)
          = encode16 (wots.shrincs_wots_pubkey_from_sig (decode32 m) (map decode16 sig) (Z.of_nat c) (decode16 pp) A0).
  have -> : wcp_T_sf P = T_sf_sha256 by [].
  rewrite /T_sf_sha256 /wots.shrincs_wots_pubkey_from_sig pk_adrsE.
  by rewrite (complete_ends_modelE pp m c sig hsig) concat_flatten.
rewrite hTsf.
set X := wots.shrincs_wots_pubkey_from_sig (decode32 m) (map decode16 sig) (Z.of_nat c) (decode16 pp) A0.
have hX16 : size X = 16%nat.
  by rewrite /X size_lengthE /wots.shrincs_wots_pubkey_from_sig /wots.T_sf thash_length.
case: (List.list_eq_dec byte.byte_eq_dec X (decode16 root)) => [Heq | Hneq].
- by rewrite Heq encode16_decode16 eqxx.
- case: eqP => [Habs | //].
  exfalso; apply: Hneq.
  have hd := decode16_encode16 X hX16.
  by rewrite Habs in hd; rewrite -hd.
Qed.

(** T5 HEADLINE: the games' partial signer IS the model's, through the
    dictionary.  Orientation matches [find_counter_modelE] (model = the
    games transported): the model signature (option [list block * Z]) is
    the [omap] of the games one (option [seq N * nat]) under
    "decode each chain value, [Z.of_nat] the counter".  The winning
    counter is transported by T2's [find_counter_modelE]; the signature
    payload by [sign_chains_modelE]. *)
Lemma sign_modelE (pp : PP_shrincs) (k : K_shrincs) (m : M_shrincs) :
  wots.shrincs_wots_sign (decode32 m) (decode16 k) (decode16 pp) A0
  = omap (fun sgc => (map decode16 sgc.1, Z.of_nat sgc.2))
         (Sec.wots.scheme.shrincs_wots_sign P pp (derive_sk P K_shrincs PRF_sha256 pp k) m).
Proof.
rewrite /wots.shrincs_wots_sign Sec.wots.scheme.shrincs_wots_sign_def find_counter_modelE.
case E: (Sec.wots.scheme.find_counter P pp m) => [c|]; last by [].
cbn [Option.map].
congr Some; congr pair.
by rewrite (sign_chains_modelE pp k m c).
Qed.

(** Grinding-failure corollary: when the games' bounded search finds no
    good counter, both signers refuse. *)
Lemma sign_None_modelE (pp : PP_shrincs) (k : K_shrincs) (m : M_shrincs) :
  Sec.wots.scheme.shrincs_wots_sign P pp (derive_sk P K_shrincs PRF_sha256 pp k) m = None ->
  wots.shrincs_wots_sign (decode32 m) (decode16 k) (decode16 pp) A0 = None.
Proof. by move=> hN; rewrite sign_modelE hN. Qed.

End model_bridge.
