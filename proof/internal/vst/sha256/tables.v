(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.internal.vst.sha256.tables: the two SHA-256 constant tables as VALUES

    K (FIPS 180-4 SS 4.2.2) and H^(0) (SS 5.3.3) are function locals in
    src/sha256.c, not file-scope arrays, so they are NOT Clight globals
    and there is no resource here to own. This file is what is left of
    that: the facts a proof needs about the two tables as [list val],
    and the bridge from the C's numerals to the model's words.

    WHY THEY ARE NOT GLOBALS. A [static const] array is a Clight
    global; separation logic makes a caller own whatever the callee
    reads; and VST has no persistent read-only assertion, so ownership
    cannot be duplicated away. A global table would therefore appear in
    the PRE and the POST of every funspec from [sha256_compress_words]
    outwards, including public key generation and verification
    contracts, which have no business mentioning the
    round constants of a hash. As locals, the two exported contracts
    are functions of their bytes and nothing else, and the sha256
    component's init predicate is [emp].

    Hoisting K to the callers of [sha256_compress_words] initializes it
    once per call rather than once per block.

    THE ONE SECOND TRANSCRIPTION IN THE DEVELOPMENT lives at the foot
    of this file: [K_C] and [H0_C], the two tables as clightgen renders
    them. A proof that steps through a local array initialiser holds
    the C's own numerals, and something has to say those are FIPS's.
    [K_C_is_K] and [H0_C_is_H0] are that something, and they are
    checked by [vm_compute], so a divergence between the C's table and
    the specification's is a build failure naming the table that
    drifted. No other file may mention those numerals. *)

From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.sha256 Require Import bridge.
From Shrincs.internal.vst.sha256 Require Import clone.

(* Imported for the AST's identifiers. This shadows Shrincs.clight.wots's
   [prog], which Shrincs.internal.vst.support.base exports. The identifiers agree because
   clightgen 3.17 derives every identifier from its NAME, so a symbol
   shared by the translation units is the same positive in all of
   them. *)
From Shrincs.clight Require Import sha256.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Local Open Scope Z_scope.
Local Open Scope logic.

(* ================================================================= *)
(** ** Shapes

    The lengths the two [tarray tuint _] assert, as the [Zlength] every
    loop invariant over a copy of a table carries. The [size]-side
    facts are [clone.K_size] and [clone.H0_size]. *)

Lemma words_to_vals_H0_Zlength : Zlength (words_to_vals H0) = 8.
Proof.
rewrite words_to_vals_Zlength.
rewrite H0_size.
reflexivity.
Qed.

Lemma words_to_vals_K_Zlength : Zlength (words_to_vals K) = 64.
Proof.
rewrite words_to_vals_Zlength.
rewrite K_size.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The C's numerals ARE the model's words

    Both tables are written in the C as a braced list of literals, and
    clightgen turns each into an [Econst_int (Int.repr n)] stored into
    the local array. Proving such a run of stores builds [words_to_vals
    K] means matching those numerals against [wrepr U32] of FIPS's
    hexadecimal, and ONE MISMATCH HAS TO BE CROSSED -- a printing
    convention, not a disagreement.

    clightgen renders a table entry above 2^31 as a NEGATIVE literal
    ([Int.repr (-1245643825)] for K_2 = 0xb5c0fbcf), while the model
    builds [wrepr U32 0xb5c0fbcf]. The two are the same [Int.int], but
    NOT by [reflexivity] and not by [vm_compute; reflexivity] either:
    [Int.repr] is [mkint (Z_mod_modulus n) (Z_mod_modulus_range' n)]
    and [Z_mod_modulus_range'] is closed by [Qed], so the two values
    agree in their [intval] field and differ in the opaque proof term
    beside it, which conversion cannot see through.

    [Int.mkint_eq] is CompCert's own way past that -- constructive, via
    [eq_proofs_unicity] on comparisons, so no axiom is involved. The
    three lemmas below wrap it so that a whole table is ONE closed
    computation on residues rather than sixty-four separate steps. *)

(** Two [Int.int] are equal as soon as their residues are. *)
Lemma repr_eq_unsigned (z : Z) (i : Int.int) :
  Int.Z_mod_modulus z = Int.unsigned i -> Int.repr z = i.
Proof.
intros Hz.
rewrite <- (Int.repr_unsigned i).
rewrite <- Hz.
apply Int.mkint_eq.
rewrite Int.Z_mod_modulus_eq.
rewrite Int.Z_mod_modulus_eq.
rewrite Zmod_mod.
reflexivity.
Qed.

(** The model's word view of a [Z] is its CompCert residue. *)
Lemma wunsigned_wrepr_mod (z : Z) : wunsigned (wrepr U32 z) = Int.Z_mod_modulus z.
Proof.
rewrite Int.Z_mod_modulus_eq.
rewrite <- wbase_U32.
rewrite wunsigned_repr.
reflexivity.
Qed.

(** A table the model writes as words over [zs] is the C's array of
    [Int.int] as soon as the two agree residue by residue. Both uses
    ([K] over [K_Z], [H0] over [H0_Z]) discharge the hypothesis by a
    single [vm_compute; reflexivity]. *)
Lemma words_to_vals_table (zs : seq Z) (js : list Int.int) :
  List.map Int.Z_mod_modulus zs = List.map Int.unsigned js ->
  words_to_vals [seq wrepr U32 z | z <- zs] = List.map Vint js.
Proof.
revert js.
induction zs as [| z zs IH]; intros js Hmod.
- (* both lists empty, or the lengths disagree *)
  destruct js as [| j js]; [ reflexivity | discriminate ].
- destruct js as [| j js]; [ discriminate | ].
  simpl in Hmod.
  injection Hmod as Hhd Htl.
  simpl.
  f_equal.
  + f_equal.
    unfold int_of_w32.
    apply repr_eq_unsigned.
    rewrite wunsigned_wrepr_mod.
    rewrite Int.Z_mod_modulus_eq in Hhd.
    rewrite Int.Z_mod_modulus_eq.
    rewrite Int.Z_mod_modulus_eq.
    rewrite Zmod_mod.
    exact Hhd.
  + exact (IH js Htl).
Qed.

(* ================================================================= *)
(** ** The tables as the C writes them

    A local array initialiser becomes one [Sassign] of an [Econst_int]
    per entry, so a proof that steps through the initialisation ends up
    holding the C's own numerals. These two lists are those numerals,
    in clightgen's rendering -- which is why entries above 2^31 appear
    NEGATIVE.

    THEY ARE A SECOND TRANSCRIPTION, and the two lemmas beside them are
    what makes that safe: each says the list is [words_to_vals] of the
    corresponding table of Shrincs.sha256, checked by [vm_compute] through
    [words_to_vals_table]. Change either the C or the specification
    alone and this file stops compiling, naming the table that drifted.
    Nothing else in the development may mention these numerals. *)

Definition K_C : list Int.int :=
  List.map Int.repr
    [ 1116352408; 1899447441; -1245643825; -373957723; 961987163; 1508970993;
      -1841331548; -1424204075; -670586216; 310598401; 607225278; 1426881987;
      1925078388; -2132889090; -1680079193; -1046744716; -459576895; -272742522;
      264347078; 604807628; 770255983; 1249150122; 1555081692; 1996064986;
      -1740746414; -1473132947; -1341970488; -1084653625; -958395405; -710438585;
      113926993; 338241895; 666307205; 773529912; 1294757372; 1396182291;
      1695183700; 1986661051; -2117940946; -1838011259; -1564481375; -1474664885;
      -1035236496; -949202525; -778901479; -694614492; -200395387; 275423344;
      430227734; 506948616; 659060556; 883997877; 958139571; 1322822218;
      1537002063; 1747873779; 1955562222; 2024104815; -2067236844; -1933114872;
      -1866530822; -1538233109; -1090935817; -965641998].

Definition H0_C : list Int.int :=
  List.map Int.repr
    [ 1779033703; -1150833019; 1013904242; -1521486534;
      1359893119; -1694144372; 528734635; 1541459225].

(** The C's sixty-four constants are FIPS's K, and its eight are H^(0).
    These are the only place the two transcriptions meet. *)
Lemma K_C_is_K : words_to_vals K = List.map Vint K_C.
Proof.
unfold K, K_C.
apply words_to_vals_table.
vm_compute.
reflexivity.
Qed.

Lemma H0_C_is_H0 : words_to_vals H0 = List.map Vint H0_C.
Proof.
unfold H0, H0_C.
apply words_to_vals_table.
vm_compute.
reflexivity.
Qed.
