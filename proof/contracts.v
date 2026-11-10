(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Shrincs.contracts: the public C contracts

    One VST function specification per exported function of src/wots.c. Each postcondition names the function of Shrincs.spec that the C function is called after, applied to the values the caller passed, so what the C is claimed to compute is the transcription of the reference and not a second description of it.

    How to read a specification:

    - [WITH] lists what the caller chooses: the pointers, the values behind them, and one share per buffer. Buffers are tuples of the specification, so a length is part of a type and no premise restates it.
    - [PARAMS] gives the C arguments in the order of the C prototype. [rep_val x] is the C value that carries [x].
    - [SEP] lists the memory the function needs. [at_ sh x p] says that [x] sits at [p] in its C representation with permission [sh], and [space_for A sh p] says that [p] has room for a value of type [A] and says nothing about its content. The clauses of one [SEP] are separated, so the buffers of a call do not overlap, which is what [restrict] says in the C prototype.

    That the C satisfies these specifications is the second conjunct of Shrincs.theorem. *)

From VST Require Import floyd.proofauto.
From Shrincs.clight Require Export wots.
Require Shrincs.clight.sha256.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs Require Import spec.

Local Open Scope Z_scope.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(* The input bound makes the message length in bits fit the SHA-256 length field. *)
Definition spec_sha256 : AST.ident * funspec :=
  DECLARE Shrincs.clight.sha256._shrincs_sha256
  WITH msg : list byte, out_ptr : Values.val, in_ptr : Values.val,
       sh_in : share, sh_out : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (readable_share sh_in; writable_share sh_out;
          0 <= Zlength msg < two_p 61)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr (Zlength msg)))
    SEP (data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
         data_at_ sh_out (tarray tuchar 32) out_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_in (tarray tuchar (Zlength msg)) (List.map Vubyte msg) in_ptr;
         data_at sh_out (tarray tuchar 32)
           (List.map (fun z : Z => Vubyte (Byte.repr z))
             (Shrincs.sha256.bytes_of_word U256
               (Shrincs.sha256.sha256 (List.map Byte.unsigned msg)))) out_ptr).

(*  Representation  *)

(* How a value of the specification sits in C: the C type that holds it and the C value that carries it. *)
Class Rep (A : Type) := { rep_type : Ctypes.type ; rep_val : A -> reptype rep_type }.

(* An unsigned integer is the C integer of its value. *)
#[export] Instance rep_u8 : Rep UInt8 :=
  {| rep_type := tuchar ; rep_val := fun x : UInt8 => Vint (Int.repr (wunsigned x)) |}.

#[export] Instance rep_u64 : Rep UInt64 :=
  {| rep_type := tulong ; rep_val := fun x : UInt64 => Vlong (Int64.repr (wunsigned x)) |}.

(* A boolean is the C [bool] that is 1 for true and 0 for false. *)
#[export] Instance rep_bool : Rep bool :=
  {| rep_type := tbool ; rep_val := fun b : bool => Vint (Int.repr (Z.b2z b)) |}.

(* A byte string of no fixed length, as the content of an array of [unsigned char]. *)
Definition vals (x : seq UInt8) : list Values.val := List.map rep_val x.

(* [n] bytes are an array of [n] [unsigned char], in order. *)
#[export] Instance rep_bytes (n : nat) : Rep (Bytes n) :=
  {| rep_type := tarray tuchar (Z.of_nat n) ; rep_val := fun x : Bytes n => vals x |}.

(* An absent output leaves the buffer contents unspecified. *)
#[export] Instance rep_option (A : Type) {representation : Rep A} : Rep (option A) :=
  {| rep_type := @rep_type A representation ;
     rep_val := fun output =>
       match output with
       | Some value => @rep_val A representation value
       | None => default_val (@rep_type A representation)
       end |}.

Definition at_ {A : Type} {R : Rep A} (sh : share) (x : A) (p : Values.val) : mpred :=
  data_at sh rep_type (rep_val x) p.

Definition space_for (A : Type) {R : Rep A} (sh : share) (p : Values.val) : mpred :=
  data_at_ sh rep_type p.

(*  The three entry points  *)

(* shrincs_wots_c_pubkey_gen writes the public key of the leaf to [pk]. *)
Definition shrincs_wots_c_pubkey_gen_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_pubkey_gen
  WITH pk_ptr : Values.val, sk_seed_ptr : Values.val, pk_seed_ptr : Values.val,
       sk_seed : Bytes 16, pk_seed : Bytes 16, node_height : UInt8, node_index : UInt64,
       tree_balanced : bool, tree_depth : UInt8,
       sh_pk : share, sh_sk_seed : share, sh_pk_seed : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tuchar, tulong, tbool, tuchar ]
    PROP (writable_share sh_pk; readable_share sh_sk_seed; readable_share sh_pk_seed)
    PARAMS (pk_ptr; sk_seed_ptr; pk_seed_ptr;
            rep_val node_height; rep_val node_index; rep_val tree_balanced; rep_val tree_depth)
    SEP (space_for (Bytes 16) sh_pk pk_ptr;
         at_ sh_sk_seed sk_seed sk_seed_ptr;
         at_ sh_pk_seed pk_seed pk_seed_ptr)
  POST [ tvoid ]
    EX public_key : Bytes 16,
    PROP (public_key =
            wots_c_pubkey_gen sk_seed pk_seed node_height node_index tree_balanced tree_depth)
    RETURN ()
    SEP (at_ sh_pk public_key pk_ptr;
         at_ sh_sk_seed sk_seed sk_seed_ptr;
         at_ sh_pk_seed pk_seed pk_seed_ptr).

(* shrincs_wots_c_sign returns SHRINCS_WOTS_OK (0) and writes the signature when the reference returns one. It returns SHRINCS_WOTS_SIGN_FAILED (-2) when the reference returns None, and then the content of [signature] is not specified. *)
Definition shrincs_wots_c_sign_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_sign
  WITH signature_ptr : Values.val, message_digest_ptr : Values.val,
       sk_seed_ptr : Values.val, pk_seed_ptr : Values.val,
       message_digest : Bytes 32, sk_seed : Bytes 16, pk_seed : Bytes 16,
       node_height : UInt8, node_index : UInt64, tree_balanced : bool, tree_depth : UInt8,
       sh_signature : share, sh_message_digest : share, sh_sk_seed : share, sh_pk_seed : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tuchar, tulong, tbool, tuchar ]
    PROP (writable_share sh_signature; readable_share sh_message_digest;
          readable_share sh_sk_seed; readable_share sh_pk_seed)
    PARAMS (signature_ptr; message_digest_ptr; sk_seed_ptr; pk_seed_ptr;
            rep_val node_height; rep_val node_index; rep_val tree_balanced; rep_val tree_depth)
    SEP (space_for (Bytes (2 + WOTS_C_CHAINS_SIZE)) sh_signature signature_ptr;
         at_ sh_message_digest message_digest message_digest_ptr;
         at_ sh_sk_seed sk_seed sk_seed_ptr;
         at_ sh_pk_seed pk_seed pk_seed_ptr)
  POST [ tint ]
    EX signature_result : option (Bytes (2 + WOTS_C_CHAINS_SIZE)), EX return_value : Z,
    PROP (signature_result =
            wots_c_sign message_digest sk_seed pk_seed node_height node_index tree_balanced tree_depth;
          return_value = match signature_result with Some _ => 0 | None => -2 end)
    RETURN (Vint (Int.repr return_value))
    SEP (at_ sh_signature signature_result signature_ptr;
         at_ sh_message_digest message_digest message_digest_ptr;
         at_ sh_sk_seed sk_seed sk_seed_ptr;
         at_ sh_pk_seed pk_seed pk_seed_ptr).

(* shrincs_wots_c_pubkey_from_sig returns SHRINCS_WOTS_OK (0) and writes the recovered public key when the reference returns one. It returns SHRINCS_WOTS_VERIFY_FAILED (-1) when the reference returns None, and then the content of [pk] is not specified. *)
Definition shrincs_wots_c_pubkey_from_sig_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_pubkey_from_sig
  WITH pk_ptr : Values.val, signature_ptr : Values.val, message_digest_ptr : Values.val,
       pk_seed_ptr : Values.val,
       signature : Bytes (2 + WOTS_C_CHAINS_SIZE), message_digest : Bytes 32, pk_seed : Bytes 16,
       node_height : UInt8, node_index : UInt64,
       sh_pk : share, sh_signature : share, sh_message_digest : share, sh_pk_seed : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tuchar, tulong ]
    PROP (writable_share sh_pk; readable_share sh_signature;
          readable_share sh_message_digest; readable_share sh_pk_seed)
    PARAMS (pk_ptr; signature_ptr; message_digest_ptr; pk_seed_ptr;
            rep_val node_height; rep_val node_index)
    SEP (space_for (Bytes 16) sh_pk pk_ptr;
         at_ sh_signature signature signature_ptr;
         at_ sh_message_digest message_digest message_digest_ptr;
         at_ sh_pk_seed pk_seed pk_seed_ptr)
  POST [ tint ]
    EX public_key_result : option (Bytes 16), EX return_value : Z,
    PROP (public_key_result =
            wots_c_pubkey_from_sig signature message_digest pk_seed node_height node_index;
          return_value = match public_key_result with Some _ => 0 | None => -1 end)
    RETURN (Vint (Int.repr return_value))
    SEP (at_ sh_pk public_key_result pk_ptr;
         at_ sh_signature signature signature_ptr;
         at_ sh_message_digest message_digest message_digest_ptr;
         at_ sh_pk_seed pk_seed pk_seed_ptr).
