(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.common.bytes: the representation atlas

    One library mapping between the machine-word representations the
    two proof stacks speak, generic over the word size [ws : wsize]
    (U8 .. U256). The word is the hub; every other representation has
    a cast to/from it:

      'I_(2 ^ wbits ws)  --word_of_ord-->  word ws   (SSProve sampling)
      word ws            --ord_of_word-->  'I_(2 ^ wbits ws)
      word ws            --wunsigned---->  Z         (mathcomp-word's own)
      Z                  --wrepr-------->  word ws
      word ws            --bytes_of_word-> seq Z     (big-endian wire bytes)
      seq Z              --word_of_bytes-> word ws

    The VST side continues from [seq Z]: Shrincs.internal.vst.support.base maps it to
    CompCert's [list byte] / [list val] (that last hop is floyd-typed
    and lives there, keeping this file floyd-free).

    IMPORT DISCIPLINE: this file imports the word LIBRARY only
    (mathcomp, mathcomp-word, SSProve's jasmin word shim); no SSProve
    package/game machinery, no floyd, no compcert. Both proof sides
    depend on it.

    In particular Z arrives via [BinInt] and NOT via [ZArith], and nat
    annotations are spelled [%nat] and NEVER [%N]. Two independent
    traps, both silent:

    - [Require Import ZArith] re-declares "_ ^ _" inside nat_scope as
      [Nat.pow], shadowing mathcomp's [expn]. [BinInt] does not.
    - the "%N" delimiter key is owned by stdlib's N_scope, not by
      mathcomp's nat_scope: [BinNums] is loaded transitively by
      mathcomp-word, and its [Delimit Scope N_scope with N] wins over
      ssrnat's [Delimit Scope nat_scope with N]. Under
      [Open Scope Z_scope] a literal written [32%N] therefore falls
      through N_scope to Z_scope and comes out a [Z]; with ZArith
      imported [(2 ^ 256)%N] comes out [nat_of_bin (N.pow 2 256)].

    Either way the ordinal bound would stop being mathcomp's
    [expn 2 256] -- which is exactly the term SSProve builds for
    [sample uniform (2 ^ 256)] in the games. The two are equal but not
    feasibly convertible (2^256 in unary), so the mismatch makes the
    games file spin in conversion rather than fail.

    Byte order is BIG-ENDIAN throughout: [bytes_of_word ws w] renders
    [wunsigned w] most-significant byte first, matching both the SHA-256
    wire convention and how sha256sum prints digests, so a 32-byte hex
    literal reads identically as a [wrepr U256 0x...] numeral and as a
    C byte array. *)

From HB Require Import structures.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.
(* Require WITHOUT Import: loading activates no notations, so stdlib's
   nat_scope "_ ^ _" (the expn-shadowing trap above) stays dormant;
   the two lemmas below are referenced by qualified name. *)
From Stdlib Require Zpower Znat.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope Z_scope.

(** ** Size bookkeeping

    [wbits] is the bit width as a mathcomp nat ([expn]-compatible, see
    the discipline note), [wnbytes] the byte width; every jasmin wsize
    is a whole number of bytes. At U256 they convert to 256 and 32. *)

Definition wbits (ws : wsize) : nat := (wsize_size_minus_1 ws).+1.

Definition wnbytes (ws : wsize) : nat := (wbits ws %/ 8)%nat.

(** [expn] and Stdlib's [Nat.pow] compute the same function; this is
    the single bridge every bound below funnels through, so the
    library's ordinals stay [expn]-spelled (what SSProve builds) while
    the Z side uses Stdlib arithmetic. *)

Lemma expn_Nat_pow (a b : nat) : (a ^ b)%nat = Nat.pow a b.
Proof. by elim: b => //= b IH; rewrite expnS IH multE. Qed.

Lemma wbaseE (ws : wsize) : wbase ws = Z.of_nat (2 ^ wbits ws)%nat.
Proof.
rewrite /wbase /modulus Zpower.two_power_nat_equiv expn_Nat_pow
        Znat.Nat2Z.inj_pow //.
Qed.

Section Codec.

Variable ws : wsize.

(** ** Ordinal casts (the SSProve sampling representation)

    SSProve samples land in ['fin n]; the games cast them to words.
    [2 ^ wbits ws] ordinals and [word ws] have the same cardinality,
    so the casts are mutually inverse ([word_of_ordK], [ord_of_wordK]).
    The exponent is mathcomp's [expn] -- the SAME term SSProve builds
    for [sample uniform (2 ^ wbits ws)] -- hence the [%nat] annotation
    (see the import-discipline note above). *)

Definition word_of_ord (i : 'I_(2 ^ wbits ws)%nat) : word ws :=
  wrepr ws (Z.of_nat (val i)).

Lemma wunsigned_lt_exp (w : word ws) :
  (Z.to_nat (wunsigned w) < 2 ^ wbits ws)%nat.
Proof.
have [H0 Hlt] := wunsigned_range w.
rewrite wbaseE in Hlt.
apply/ltP.
have Hc := proj1 (Znat.Z2Nat.inj_lt _ _ H0 (Znat.Nat2Z.is_nonneg _)) Hlt.
by rewrite Znat.Nat2Z.id in Hc.
Qed.

Definition ord_of_word (w : word ws) : 'I_(2 ^ wbits ws)%nat :=
  Ordinal (wunsigned_lt_exp w).

Lemma ord_of_wordK : cancel ord_of_word word_of_ord.
Proof.
move=> w.
rewrite /word_of_ord /ord_of_word /=.
rewrite (Znat.Z2Nat.id _ (proj1 (wunsigned_range w))).
exact: wrepr_unsigned.
Qed.

Lemma word_of_ordK : cancel word_of_ord ord_of_word.
Proof.
move=> i.
apply: val_inj.
change (Z.to_nat (wunsigned (wrepr ws (Z.of_nat (val i)))) = val i).
have Hi : (val i < 2 ^ wbits ws)%nat by case: i.
have ordinal_integer_bound : 0 <= Z.of_nat (val i) < wbase ws.
{ split; first exact: Znat.Nat2Z.is_nonneg.
  rewrite wbaseE.
  apply: Znat.inj_lt.
  exact/ltP. }
by rewrite (wunsigned_repr_small ordinal_integer_bound) Znat.Nat2Z.id.
Qed.

(** ** Byte rendering (big-endian wire representation) *)

Definition byte_of_word (w : word ws) (i : nat) : Z :=
  Z.land (Z.shiftr (wunsigned w) (Z.of_nat (8 * (wnbytes ws - 1 - i)))) 255.

Definition bytes_of_word (w : word ws) : seq Z :=
  [seq byte_of_word w i | i <- iota 0 (wnbytes ws)].

Definition word_of_bytes (bs : seq Z) : word ws :=
  wrepr ws (foldl (fun acc b => Z.lor (Z.shiftl acc 8) b) 0 bs).

Lemma bytes_of_word_size (w : word ws) :
  size (bytes_of_word w) = wnbytes ws.
Proof. by rewrite size_map size_iota. Qed.

Lemma byte_of_word_range (w : word ws) (i : nat) :
  0 <= byte_of_word w i < 256.
Proof.
rewrite /byte_of_word.
have -> : 255 = Z.ones 8 by [].
rewrite (Z.land_ones _ 8 ltac:(by [])).
by apply: Z.mod_pos_bound.
Qed.

(* Round-trips between the byte and word views (word_of_bytes o
   bytes_of_word = id and the masked converse) are PROVED, but not
   here: they live in Shrincs.internal.vst.sha256.bridge as
   [word_of_bytes_of_word] and [bytes_of_word_of_bytes], next to the
   only proofs that need them (the C's load_be32 / store_be32 and the
   two digest stores). They are stated size-generically over [ws], so
   moving them down here is a refactor away if a second consumer
   appears; until then they sit with their consumer. *)

End Codec.
