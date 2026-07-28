(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.bridge

    Pure equivalences between the shared canonical model
    (Model.wots/Model.address/Model.byte, Stdlib vocabulary, Z-valued,
    MSB-first digits) and this repo's math layer (Model.math.chain /
    Model.math.encoding, mathcomp vocabulary, LSB-first digits).
    MathComp-only; no SSProve (the Model.math audit boundary).

    Contents:
    - Stdlib <-> mathcomp glue (take/sum/eqb);
    - a [byte]-as-[eqType] instance (needed for [Model.math.chain.chain],
      and reusable groundwork for the byte-level instantiation:
      [Model.wots]'s [block] needs an eqType before it can be given
      the richer choice_type/Countable/Finite structure that step
      needs);
    - [nibbles_bridge]/[base_2b_cons]/[base_2b_digits_w]: [Model.wots]'s
      nibble-splitting [base_2b] (fixed at 4-bit groups, MSB-first)
      equals the REVERSED base-16 decomposition of the big-endian byte
      value read off the same bytes -- the [rev] is the
      MSB-first/LSB-first flip;
    - [digest_of_bridge]/[good_counter_bridge]: [Model.wots]'s
      [digest_of]/[good_counter] (over the concrete byte-valued
      [H_grind]) equal the [digits_w]/[wf_digits]/[sumn] shapes a
      games-layer nat-digest [H_grind] Context would need to match.

    IMPORT DISCIPLINE (load-bearing, do not "simplify"): [BinInt] (not
    the full [ZArith]) gives Z literals/infix notation without pulling
    in [PeanoNat]'s [nat] "^" notation, which shadows mathcomp's
    [expn] the moment it is [Import]ed (confirmed empirically: `From
    Stdlib Require Import ZArith` alone makes `256 ^ 3 : nat` print as
    [Nat.pow], breaking every [expn]/[edivn]/[digits_w] lemma in this
    file). [Znat] (the [Z2Nat]/[Nat2Z] conversion lemmas) is the same
    story, so it stays a plain [Require] with qualified
    [Znat.Z2Nat.foo] / [Znat.Nat2Z.foo] access below rather than
    [Require Import].

    DIGIT ORDER: the model assigns its MSB-first digit i to chain i;
    the games layer's [scheme.digest_of] reads MSB-first
    ([rev (digits_w ...)]), so digit i pairs with chain i on both
    sides -- no relabeling.
    [Sec.wots.model_bridge.digest_of_modelE] proves the games digest
    EQUALS the model digest ([digest_of_bridge] below is exactly the
    lemma it consumes for this), rather than up to a flip.

    THE BYTE-LEVEL INSTANTIATION (done in axioms.v): that
    file picks concrete choice_types for [Model.wots.block] (16-byte
    strings) and the message digest ([instantiation.v]'s ['fin
    (2^128)]/['fin (2^256)] ordinals), encodes/decodes between them
    and [Model.wots]'s byte blocks using the [be_num]/[digits_w]
    machinery in [Model.math.encoding], and instantiates
    [games.v]/[Hop/prf.v]'s abstract
    [F]/[T_sf]/[H_grind]/[PRF] Contexts with [Model.wots.F]/[T_sf]/
    [H_grind]/[PRF] composed with that encoding -- composed with 6
    named hash-hardness axioms, this yields the unconditional
    [shrincs_wots_secure_sha256]. No separate address serialization
    step is needed: [Model.wots]'s hash functions already take an
    [adrs] value directly and serialize it internally (see
    [Model.wots.H_grind]'s use of [Model.address.adrs_bytes]). *)

From mathcomp Require Import all_boot all_order.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Model Require wots byte address.
Require Model.theory.wots.
From HB Require Import structures.
From Stdlib Require Import BinInt Lia.
From Stdlib Require Znat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------ *)
(** ** Stdlib <-> mathcomp glue *)

Lemma firstn_take (T : Type) (n : nat) (s : seq T) :
  List.firstn n s = take n s.
Proof. by elim: n s => [|n IH] [|a s] //=; rewrite IH. Qed.

Lemma list_sum_sumn (s : seq nat) : List.list_sum s = sumn s.
Proof. by elim: s => [|a s IH] //=; rewrite IH. Qed.

Lemma eqb_eqn (a b : nat) : Nat.eqb a b = (a == b).
Proof. by elim: a b => [|a IH] [|b] //=. Qed.

(* ------------------------------------------------------------------ *)
(** ** [byte] as an [eqType]

    Needed for [Model.math.chain.chain] (its step function's domain,
    here [Model.sha256.block = list byte], must be an [eqType]); also
    reusable groundwork for axioms.v's choice_type encoding
    (an eqType is a prerequisite of the richer structures that step
    needs).  Load-bearing HERE too: [mapP] in [base_2b_digits_w] below
    reflects membership in a [seq byte], so it needs this instance. *)

Definition eq_byte (b b' : byte.byte) : bool :=
  (byte.byte_val b =? byte.byte_val b')%Z.

Lemma eq_byteP : Equality.axiom eq_byte.
Proof.
move=> b b'; apply: (iffP idP); rewrite /eq_byte.
- by move=> /Z.eqb_eq; exact: byte.byte_eq.
- by move=> ->; rewrite Z.eqb_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build byte.byte eq_byteP.

(* ------------------------------------------------------------------ *)
(** ** Byte lists as nat lists (the [Z] <-> [nat] boundary) *)

Definition nat_bytes (X : seq byte.byte) : seq nat :=
  [seq Z.to_nat (byte.byte_val b) | b <- X].

(* ------------------------------------------------------------------ *)
(** ** The single-byte nibble extraction

    [Model.wots.base_2b]'s per-byte nibble computation
    ([Z.to_nat (b / 16)], [Z.to_nat (b mod 16)]) equals plain nat
    division/modulo on the [Z.to_nat]-projected byte -- direct from
    [byte]'s [[0, 256)] bound, no bit-level detour needed. *)

Lemma nibbles_bridge (b : byte.byte) :
  [:: Z.to_nat (byte.byte_val b / 16); Z.to_nat (byte.byte_val b mod 16)]
  = [:: Z.to_nat (byte.byte_val b) %/ 16; Z.to_nat (byte.byte_val b) %% 16].
Proof.
have [h0 h256] := byte.byte_val_range b.
set v := byte.byte_val b.
have hdm : v = (v / 16 * 16 + v mod 16)%Z by rewrite {1}(Z.div_mod v 16); lia.
have hr : (0 <= v mod 16 < 16)%Z by apply Z.mod_pos_bound; lia.
have hq : (0 <= v / 16)%Z by apply Z.div_pos; lia.
have e : Z.to_nat v = Z.to_nat (v / 16) * 16 + Z.to_nat (v mod 16).
  apply: Znat.Nat2Z.inj.
  rewrite -plusE -multE Znat.Nat2Z.inj_add Znat.Nat2Z.inj_mul !Znat.Z2Nat.id; try lia.
have hlt : Z.to_nat (v mod 16) < 16 by apply/ltP; lia.
have hed := edivn_eq (Z.to_nat (v / 16)) hlt.
rewrite -e edivn_def in hed.
by case: hed => -> ->.
Qed.

Lemma base_2b_singleton (b : byte.byte) :
  wots.base_2b [:: b] 2 = [:: Z.to_nat (byte.byte_val b) %/ 16; Z.to_nat (byte.byte_val b) %% 16].
Proof. rewrite /wots.base_2b /=. exact: nibbles_bridge. Qed.

(* ------------------------------------------------------------------ *)
(** ** Byte-boundary structure of the extraction *)

Lemma base_2b_cons (b : byte.byte) (X : seq byte.byte) (m : nat) :
  wots.base_2b (b :: X) (2 + m) = wots.base_2b [:: b] 2 ++ wots.base_2b X m.
Proof. by rewrite /wots.base_2b -plusE /=. Qed.

(* ------------------------------------------------------------------ *)
(** ** THE digit bridge: [Model.wots]'s nibble-split bytes = the
       reversed base-16 decomposition of their big-endian value *)

Lemma base_2b_digits_w (X : seq byte.byte) :
  wots.base_2b X (2 * size X) = rev (digits_w 16 (2 * size X) (be_num (nat_bytes X))).
Proof.
elim: X => [|b X IH].
- by rewrite /wots.base_2b.
- rewrite [size (b :: X)]/= mulnS.
  rewrite base_2b_cons base_2b_singleton IH.
  rewrite [nat_bytes (b :: X)]/= be_num_cons.
  have hsz : size (nat_bytes X) = size X by rewrite size_map.
  rewrite hsz.
  have e16 : (256 ^ size X = 16 ^ (2 * size X))%N by rewrite expnM.
  rewrite [(2 + 2 * size X)%N]addnC e16.
  have hallb1 : all (fun v => v < 256) (nat_bytes X).
    apply/allP => v hv.
    case/mapP: hv => c hc ->.
    have [h0 h256] := byte.byte_val_range c.
    apply/ltP; lia.
  have hbound : be_num (nat_bytes X) < 16 ^ (2 * size X).
    rewrite -e16 -hsz; exact: be_num_lt.
  rewrite (digits_w_split (W:=16) (k:=2 * size X) 2 (Z.to_nat (byte.byte_val b)) isT hbound).
  rewrite rev_cat.
  congr (_ ++ _).
  rewrite /=.
  have [h0 h256] := byte.byte_val_range b.
  have hlt16 : Z.to_nat (byte.byte_val b) %/ 16 < 16.
    rewrite ltn_divLR //.
    have -> : (16 * 16 = 256)%N by [].
    apply/ltP; lia.
  by rewrite (modn_small hlt16).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The digest bridge: [Model.wots.digest_of]/[good_counter] at the
       [digits_w]/[wf_digits]/[sumn] shapes *)

Lemma digest_of_bridge (pk_seed : sha256.block) (ADRS : address.adrs wots.len wots.w_pred) (M : sha256.block) (c : Z) :
  wots.digest_of pk_seed ADRS M c
  = rev (digits_w 16 32
      (be_num (nat_bytes (wots.H_grind pk_seed (address.shrincs_wots_grind_adrs ADRS) M c)))).
Proof.
rewrite /wots.digest_of.
have hlen : size (wots.H_grind pk_seed (address.shrincs_wots_grind_adrs ADRS) M c) = 16%N
  := wots.H_grind_length pk_seed (address.shrincs_wots_grind_adrs ADRS) M c.
(* [ADRS]'s type now mentions [wots.len], so rewrite [wots.len] ONLY at
   the [base_2b] digit-count slot (a plain [rewrite] would try to rewrite
   the dependent [chain_count] index of [shrincs_wots_grind_adrs ADRS]). *)
have E : wots.len = (2 * size (wots.H_grind pk_seed (address.shrincs_wots_grind_adrs ADRS) M c))%N
  by rewrite hlen.
rewrite [X in wots.base_2b _ X]E.
have -> : 32 = (2 * size (wots.H_grind pk_seed (address.shrincs_wots_grind_adrs ADRS) M c))%N.
  by rewrite hlen.
exact: base_2b_digits_w.
Qed.

Lemma good_counter_bridge (pk_seed : sha256.block) (ADRS : address.adrs wots.len wots.w_pred) (M : sha256.block) (c : Z) :
  wots.good_counter pk_seed ADRS M c
  = (wf_digits 16
       (digits_w 16 32 (be_num (nat_bytes (wots.H_grind pk_seed (address.shrincs_wots_grind_adrs ADRS) M c))))
     && (sumn
       (digits_w 16 32 (be_num (nat_bytes (wots.H_grind pk_seed (address.shrincs_wots_grind_adrs ADRS) M c))))
       == 240)).
Proof.
rewrite /wots.good_counter /wots.valid_digest digest_of_bridge.
rewrite list_sum_sumn sumn_rev eqb_eqn.
by rewrite wf_digits_w.
Qed.
