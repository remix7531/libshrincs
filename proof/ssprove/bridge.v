(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Sec.bridge

    Pure equivalences between the MODEL OF RECORD -- [Model.shrincs],
    the definition-for-definition port of the normative Python spec,
    with its derived views in [Model.theory.shrincs] (Stdlib
    vocabulary, [Z]-valued, MSB-first digits) -- and this repo's math
    layer ([Model.math.encoding] / [Sec.lib.math.chain], mathcomp
    vocabulary, LSB-first digits).  MathComp-only; no SSProve (the
    Model.math audit boundary).

    Contents:
    - Stdlib <-> mathcomp glue (take/sum/eqb);
    - a [byte]-as-[eqType] instance (needed for [Sec.lib.math.chain.chain],
      and reusable groundwork for the byte-level instantiation:
      a 16-byte hash block needs an eqType before it can be given
      the richer choice_type/Countable/Finite structure that step
      needs);
    - [nibbles]/[nibbles_digits_w]: the byte-wise nibble split (fixed at
      4-bit groups, MSB-first) of a byte string equals the REVERSED
      base-16 decomposition of the big-endian value read off the same
      bytes -- the [rev] is the MSB-first/LSB-first flip;
    - [nib_flat_nat]: THE ONE [Z] <-> [nat] transport.  The port's
      digit vector is [Z]-valued and reads its nibbles through
      [Model.theory.shrincs.nib]; that [flat_map] over the spec's own
      [range] is the [Z.of_nat] image of the [nat]-valued [nibbles].
      Everything below it stays in one number world;
    - [base_2b_digits_w]: the two composed -- the port's generic
      bit-packing loop [Model.shrincs.base_2b] at [b = 4] IS that
      reversed base-16 decomposition, transported by [Z.of_nat];
    - [digest_of_bridge]/[good_counter_bridge]: the port's
      [Model.theory.shrincs.digest_of]/[good_counter] (over the
      concrete byte-valued [H_grind]) equal the
      [digits_w]/[wf_digits]/[sumn] shapes a games-layer nat-digest
      [H_grind] Context would need to match.

    IMPORT DISCIPLINE (load-bearing, do not "simplify"): [BinInt] (not
    the full [ZArith]) gives Z literals/infix notation without pulling
    in [PeanoNat]'s [nat] "^" notation, which shadows mathcomp's
    [expn] the moment it is [Import]ed (confirmed empirically: `From
    Stdlib Require Import ZArith` alone makes `256 ^ 3 : nat` print as
    [Nat.pow], breaking every [expn]/[edivn]/[digits_w] lemma in this
    file). [Znat] (the [Z2Nat]/[Nat2Z] conversion lemmas) is the same
    story, so it stays a plain [Require] with qualified
    [Znat.Z2Nat.foo] / [Znat.Nat2Z.foo] access below rather than
    [Require Import].  [Model.shrincs] is reached QUALIFIED for the
    same reason: the port's [len] is Python's [len] builtin and would
    shadow mathcomp's list length notation on [Import].

    DIGIT ORDER: the port assigns its MSB-first digit i to chain i;
    the games layer's [scheme.digest_of] reads MSB-first
    ([rev (digits_w ...)]), so digit i pairs with chain i on both
    sides -- no relabeling.
    [Sec.wots.model_bridge.digest_of_modelE] proves the games digest
    EQUALS the port's digest ([digest_of_bridge] below is exactly the
    lemma it consumes for this), rather than up to a flip.

    THE BYTE-LEVEL INSTANTIATION (done in axioms.v): that
    file picks concrete choice_types for the port's 16-byte hash
    blocks and the message digest ([instantiation.v]'s ['fin
    (2^128)]/['fin (2^256)] ordinals), encodes/decodes between them
    and the port's byte strings using the [be_num]/[digits_w]
    machinery in [Model.math.encoding], and instantiates
    [games.v]/[Hop/prf.v]'s abstract
    [F]/[T_sf]/[H_grind]/[PRF] Contexts with [Model.shrincs.F]/[T_sf]/
    [H_grind]/[PRF] applied to the 22-byte WIRE address
    ([Model.address.adrs_bytes]) -- composed with 6 named
    hash-hardness axioms, this yields the unconditional
    [shrincs_wots_secure_sha256]. *)

From mathcomp Require Import all_boot all_order.
From Model Require Import math.encoding.
From Sec.lib Require Import math.chain.
From Model Require byte sha256 shrincs.
Require Model.theory.shrincs.
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

(** The port's [Z]-valued [sum] builtin, at a [Z.of_nat]-image list. *)
Lemma sum_list_map_of_nat (s : seq nat) :
  shrincs.sum_list (List.map Z.of_nat s) = Z.of_nat (sumn s).
Proof. by elim: s => [|a s IH] //=; rewrite IH -plusE Znat.Nat2Z.inj_add. Qed.

(* ------------------------------------------------------------------ *)
(** ** [byte] as an [eqType]

    Needed for [Sec.lib.math.chain.chain] (its step function's domain,
    here [Model.sha256.block = list byte], must be an [eqType]); also
    reusable groundwork for axioms.v's choice_type encoding
    (an eqType is a prerequisite of the richer structures that step
    needs).  Load-bearing HERE too: [mapP] in [nibbles_digits_w] below
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
(** ** The byte-wise nibble split, in [nat] vocabulary

    [nib_nat] is the port's [Model.theory.shrincs.nib] read as a pair
    of [nat] digits: plain nat division/modulo on the
    [Z.to_nat]-projected byte -- direct from [byte]'s [[0, 256)] bound,
    no bit-level detour needed. *)

Definition nib_nat (b : byte.byte) : seq nat :=
  [:: Z.to_nat (byte.byte_val b) %/ 16; Z.to_nat (byte.byte_val b) %% 16].

Definition nibbles (X : seq byte.byte) : seq nat := flatten [seq nib_nat b | b <- X].

Lemma nibbles_cons (b : byte.byte) (X : seq byte.byte) :
  nibbles (b :: X) = nib_nat b ++ nibbles X.
Proof. by []. Qed.

(** The port's [Z] division/modulo of a byte value is plain nat
    division/modulo on its [Z.to_nat] projection.  Stated as ONE pair
    equality so both halves come out of the single [edivn]
    computation; [nib_hi]/[nib_lo] are its projections. *)
Lemma nibbles_bridge (b : byte.byte) :
  (Z.to_nat (byte.byte_val b) %/ 16, Z.to_nat (byte.byte_val b) %% 16)
  = (Z.to_nat (byte.byte_val b / 16), Z.to_nat (byte.byte_val b mod 16)).
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
by rewrite -e edivn_def in hed.
Qed.

Lemma nib_hi (b : byte.byte) :
  Z.to_nat (byte.byte_val b) %/ 16 = Z.to_nat (byte.byte_val b / 16).
Proof. by case: (nibbles_bridge b). Qed.

Lemma nib_lo (b : byte.byte) :
  Z.to_nat (byte.byte_val b) %% 16 = Z.to_nat (byte.byte_val b mod 16).
Proof. by case: (nibbles_bridge b). Qed.

(* ------------------------------------------------------------------ *)
(** ** THE digit bridge: the nibble-split bytes = the reversed base-16
       decomposition of their big-endian value *)

Lemma nibbles_digits_w (X : seq byte.byte) :
  nibbles X = rev (digits_w 16 (2 * size X) (be_num (nat_bytes X))).
Proof.
elim: X => [|b X IH] //.
rewrite nibbles_cons IH [size (b :: X)]/= mulnS.
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
rewrite /nib_nat /=.
have [h0 h256] := byte.byte_val_range b.
have hlt16 : Z.to_nat (byte.byte_val b) %/ 16 < 16.
  rewrite ltn_divLR //.
  have -> : (16 * 16 = 256)%N by [].
  apply/ltP; lia.
by rewrite (modn_small hlt16).
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE number-world transport

    The port's nibble reader [Model.theory.shrincs.nib] is [Z]-valued
    and indexes INTO the byte string (rather than walking it), so the
    port's whole digit vector is a [flat_map] over the spec's own
    [range].  These two lemmas are the ONE place where the [Z] and
    [nat] worlds meet: everything above is mathcomp [nat], everything
    the port states is [Z], and the transport is a single
    [List.map Z.of_nat]. *)

(** One byte, both ways. *)
Lemma nib_val_bridge (b : byte.byte) (X : seq byte.byte) :
  shrincs.nib (b :: X) 0 = List.map Z.of_nat (nib_nat b).
Proof.
have [h0 h256] := byte.byte_val_range b.
have hq : (0 <= byte.byte_val b / 16)%Z by apply Z.div_pos; lia.
have hr : (0 <= byte.byte_val b mod 16 < 16)%Z by apply Z.mod_pos_bound; lia.
rewrite /shrincs.nib /nib_nat.
cbn [List.map].
have -> : shrincs.index (b :: X) 0 = byte.byte_val b by [].
rewrite Z.shiftr_div_pow2; last lia.
have -> : (2 ^ 4 = 16)%Z by [].
by rewrite nib_hi nib_lo !Znat.Z2Nat.id; try lia.
Qed.

(** Reading past a prepended byte, at the port's own [index]. *)
Lemma nib_bytes_cons (b : byte.byte) (X : seq byte.byte) (j : Z) :
  (0 <= j)%Z -> shrincs.nib (b :: X) (j + 1) = shrincs.nib X j.
Proof.
move=> hj.
by rewrite /shrincs.nib (shrincs.index_cons b X j hj).
Qed.

(** The whole vector: the port's [flat_map]-over-[range] nibble split
    IS the [Z.of_nat] image of [nibbles]. *)
Lemma nib_flat_nat (X : seq byte.byte) :
  List.flat_map (shrincs.nib X) (shrincs.range 0 (Z.of_nat (size X)))
  = List.map Z.of_nat (nibbles X).
Proof.
elim: X => [|b X IH] //.
have Hext : forall a, List.In a (shrincs.range 0 (Z.of_nat (size X))) ->
    shrincs.nib (b :: X) (a + 1) = shrincs.nib X a.
  move=> a ha; apply: nib_bytes_cons.
  by have [h _] := shrincs.in_range _ _ _ ha.
rewrite [size (b :: X)]/= shrincs.range0_cons.
cbn [List.flat_map].
rewrite shrincs.flat_map_map (shrincs.flat_map_ext_in _ (shrincs.nib X) _ Hext) IH.
by rewrite (nib_val_bridge b X) nibbles_cons /nib_nat.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE public digit bridge

    The port's generic bit-packing loop at [b = 4], over a byte string,
    IS the reversed base-16 decomposition of that string's big-endian
    value -- the port's own [base_2b_4] (the loop is the byte-wise
    nibble split) composed with the two lemmas above. *)

Lemma base_2b_digits_w (X : seq byte.byte) :
  shrincs.base_2b X 4 (Z.of_nat (2 * size X))
  = List.map Z.of_nat (rev (digits_w 16 (2 * size X) (be_num (nat_bytes X)))).
Proof. by rewrite shrincs.base_2b_4 nib_flat_nat nibbles_digits_w. Qed.

(* ------------------------------------------------------------------ *)
(** ** The digest bridge: the port's [digest_of]/[good_counter] at the
       [digits_w]/[wf_digits]/[sumn] shapes *)

Lemma digest_of_bridge (pk_seed : sha256.block) (nh ni : Z)
    (M : sha256.block) (c : Z) :
  shrincs.digest_of pk_seed nh ni M c
  = List.map Z.of_nat
      (rev (digits_w 16 32
         (be_num (nat_bytes
            (shrincs.H_grind pk_seed (shrincs.wc_grind_adrs nh ni) M c))))).
Proof.
rewrite /shrincs.digest_of.
have hsz : size (shrincs.H_grind pk_seed (shrincs.wc_grind_adrs nh ni) M c) = 16%nat
  := shrincs.length_H_grind _ _ _ _.
have -> : shrincs.WOTS_C_CHAIN_BITS = 4%Z by [].
have <- : Z.of_nat
            (2 * size (shrincs.H_grind pk_seed (shrincs.wc_grind_adrs nh ni) M c))
        = shrincs.WOTS_C_CHAIN_COUNT by rewrite hsz.
by rewrite base_2b_digits_w hsz.
Qed.

Lemma good_counter_bridge (pk_seed : sha256.block) (nh ni : Z)
    (M : sha256.block) (c : Z) :
  shrincs.good_counter pk_seed nh ni M c
  = (wf_digits 16
       (digits_w 16 32 (be_num (nat_bytes
          (shrincs.H_grind pk_seed (shrincs.wc_grind_adrs nh ni) M c))))
     && (sumn
       (digits_w 16 32 (be_num (nat_bytes
          (shrincs.H_grind pk_seed (shrincs.wc_grind_adrs nh ni) M c))))
       == 240)).
Proof.
rewrite /shrincs.good_counter /shrincs.valid_digest digest_of_bridge.
rewrite sum_list_map_of_nat sumn_rev wf_digits_w //.
change shrincs.WOTS_C_CONSTANT_SUM with 240%Z.
case: eqP => [->|hne] //.
by apply/Z.eqb_neq => habs; apply: hne; lia.
Qed.
