(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.buffer: a byte buffer being filled from the left

    Every buffer [src/thash.c] and [src/wots.c] build is written front to back: a hash preimage one field after the other, a signature one chain after the other, the chain tips one tip after the other. [filled sh md f p] is such a buffer of [md] bytes at [p] in the middle of that: its first bytes are the byte string [f] of the specification and the rest is not written yet.

    The file has the three things a body proof does with one. It cuts the next window off as its own array, for a callee that writes it, and puts the written window back ([filled_split], [filled_join]). It appends through [shrincs_memcpy] and [shrincs_memset] ([memcpy_fill_spec], [memset_fill_spec]). And it hashes what is written so far ([sha256_fill_spec]).

    The three contracts are not new assumptions. Each is proved here from the contract of the same function that [contract.gprog] hands to the callers, as a [funspec_sub], and a body proof applies it at the call with [forward_call]. The pointer surgery a call into the middle of a buffer needs is therefore done once, in those three proofs. *)

From Shrincs.internal.vst.support Require Import base settings.
From Shrincs.internal.vst.support.repr Require Import words.
From Shrincs.internal.vst.support Require Import contract.helpers contract.trusted theory.values.
Require Shrincs.sha256.
Require Shrincs.clight.sha256.
From Shrincs.internal.vst.sha256 Require sync.
(* MathComp last and file by file, as in [theory.values]. *)
From mathcomp Require Import ssrnat seq tuple ssralg.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Open Scope Z_scope.

(* ================================================================= *)
(** ** The predicate *)

Definition filled (sh : share) (md : Z) (f : seq UInt8) (p : Values.val) : mpred :=
  data_at sh (tarray tuchar md) (app (vals f) (Zrepeat Vundef (md - Zlength f))) p.

Lemma data_at__filled (sh : share) (md : Z) (p : Values.val) :
  data_at_ sh (tarray tuchar md) p = filled sh md nil p.
Proof.
unfold filled.
rewrite data_at__tarray.
change (Zlength (@nil UInt8)) with 0.
rewrite Z.sub_0_r.
reflexivity.
Qed.

Lemma filled_full (sh : share) (md : Z) (f : seq UInt8) (p : Values.val) :
  Zlength f = md -> filled sh md f p = data_at sh (tarray tuchar md) (vals f) p.
Proof.
intros Hf.
unfold filled.
rewrite Hf.
rewrite Z.sub_diag.
rewrite Zrepeat_0.
rewrite app_nil_r.
reflexivity.
Qed.

Lemma filled_data_at_ (sh : share) (md : Z) (f : seq UInt8) (p : Values.val) :
  filled sh md f p |-- data_at_ sh (tarray tuchar md) p.
Proof.
unfold filled.
apply data_at_data_at_.
Qed.

(** An array of bytes, whatever it holds, is that many writable bytes. *)
Lemma data_at_tuchar_memory_block (sh : share) (n : Z) (v : list Values.val) (p : Values.val) :
  0 <= n -> data_at sh (tarray tuchar n) v p |-- memory_block sh n p.
Proof.
intros Hn.
sep_apply (data_at_data_at_ sh (tarray tuchar n) v p).
sep_apply (data_at__memory_block_cancel sh (tarray tuchar n) p).
simpl sizeof.
rewrite Z.max_r by lia.
rewrite Z.mul_1_l.
apply derives_refl.
Qed.

(* ================================================================= *)
(** ** Cutting the next window off, and putting it back *)

(** The next [n] bytes after the written part, as an array of their own. *)
Lemma filled_split (sh : share) (md : Z) (f : seq UInt8) (p : Values.val) (k n : Z) :
  Zlength f = k -> 0 <= n -> k + n <= md ->
  field_compatible (tarray tuchar md) [] p ->
  filled sh md f p =
  (data_at sh (tarray tuchar k) (vals f) p *
   data_at_ sh (tarray tuchar n) (offset_val k p) *
   data_at_ sh (tarray tuchar (md - (k + n))) (offset_val (k + n) p))%logic.
Proof.
intros Hf Hn Hkn Hfc.
assert (Hk : 0 <= k) by (rewrite <- Hf; apply Zlength_nonneg).
assert (Hvf : Zlength (vals f) = k) by (rewrite Zlength_vals; exact Hf).
unfold filled.
rewrite Hf.
rewrite (tuchar_split3 sh p (app (vals f) (Zrepeat Vundef (md - k))) md n k)
  by (try assumption; rewrite Zlength_app, Hvf, Zlength_Zrepeat by lia; lia).
rewrite !data_at__tarray.
change (default_val tuchar) with Vundef.
f_equal.
- f_equal.
  + f_equal.
    list_solve.
  + f_equal.
    list_solve.
- f_equal.
  list_solve.
Qed.

(** The same three pieces once the window holds [x]. *)
Lemma filled_join (sh : share) (md : Z) (f x : seq UInt8) (p : Values.val) (k n : Z) :
  Zlength f = k -> Zlength x = n -> k + n <= md ->
  field_compatible (tarray tuchar md) [] p ->
  (data_at sh (tarray tuchar k) (vals f) p *
   data_at sh (tarray tuchar n) (vals x) (offset_val k p) *
   data_at_ sh (tarray tuchar (md - (k + n))) (offset_val (k + n) p))%logic
  = filled sh md (cat f x) p.
Proof.
intros Hf Hx Hkn Hfc.
assert (Hk : 0 <= k) by (rewrite <- Hf; apply Zlength_nonneg).
assert (Hn : 0 <= n) by (rewrite <- Hx; apply Zlength_nonneg).
assert (Hvf : Zlength (vals f) = k) by (rewrite Zlength_vals; exact Hf).
assert (Hvx : Zlength (vals x) = n) by (rewrite Zlength_vals; exact Hx).
assert (Hfx : Zlength (cat f x) = k + n).
{ rewrite <- catE.
  rewrite Zlength_app.
  lia. }
unfold filled.
rewrite Hfx.
rewrite vals_cat.
rewrite (tuchar_split3 sh p
           (app (app (vals f) (vals x)) (Zrepeat Vundef (md - (k + n)))) md n k)
  by (try assumption; rewrite !Zlength_app, Hvf, Hvx, Zlength_Zrepeat by lia; lia).
rewrite !data_at__tarray.
change (default_val tuchar) with Vundef.
f_equal.
- f_equal.
  + f_equal.
    list_solve.
  + f_equal.
    list_solve.
- f_equal.
  list_solve.
Qed.

(** A byte stored just past the written part extends it by that byte. The index is the number the C stores at, tied to the written part by a premise. *)
Lemma filled_upd (md : Z) (f : seq UInt8) (b : UInt8) (k : Z) :
  Zlength f = k -> k < md ->
  upd_Znth k (app (vals f) (Zrepeat Vundef (md - Zlength f)))
    (Vint (Int.repr (wunsigned b)))
  = app (vals (rcons f b)) (Zrepeat Vundef (md - Zlength (rcons f b))).
Proof.
intros Hfk Hlt.
subst k.
pose proof (Zlength_nonneg f) as Hk.
assert (Hvf : Zlength (vals f) = Zlength f) by apply Zlength_vals.
rewrite <- (cats1 f b).
rewrite vals_cat.
rewrite <- (catE f (b :: nil)).
rewrite Zlength_app.
change (Zlength (b :: nil)) with 1.
change (vals (b :: nil)) with (Vint (Int.repr (wunsigned b)) :: nil).
list_solve.
Qed.

(** The pointer [base + (size_t)i * 16] the C computes for block [i], from an array and from a pointer. *)
Lemma block_index_long (i : Z) :
  0 <= i <= Int.max_unsigned ->
  eval_binop Omul tulong tint (eval_cast tuint tulong (Vint (Int.repr i))) (Vint (Int.repr 16))
  = Vlong (Int64.repr (i * 16)).
Proof.
intros Hi.
simpl.
rewrite Int.unsigned_repr by lia.
rewrite Int.signed_repr by rep_lia.
rewrite mul64_repr.
reflexivity.
Qed.

Lemma block_pointer_array (p : Values.val) (n i : Z) :
  isptr p -> 0 <= i <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tarray tuchar n) tulong p
               (eval_binop Omul tulong tint (eval_cast tuint tulong (Vint (Int.repr i)))
                  (Vint (Int.repr 16))))
  = offset_val (16 * i) p.
Proof.
intros Hp Hi.
rewrite (block_index_long i Hi).
unfold sem_binary_operation'.
simpl.
rewrite sem_add_pl_ptr_special by (first [reflexivity | exact Hp]).
simpl force_val.
f_equal.
change (sizeof tuchar) with 1.
lia.
Qed.

Lemma block_pointer_ptr (p : Values.val) (i : Z) :
  isptr p -> 0 <= i <= Int.max_unsigned ->
  force_val (sem_binary_operation' Oadd (tptr tuchar) tulong p
               (eval_binop Omul tulong tint (eval_cast tuint tulong (Vint (Int.repr i)))
                  (Vint (Int.repr 16))))
  = offset_val (16 * i) p.
Proof.
intros Hp Hi.
rewrite (block_index_long i Hi).
unfold sem_binary_operation'.
simpl.
rewrite sem_add_pl_ptr_special by (first [reflexivity | exact Hp]).
simpl force_val.
f_equal.
change (sizeof tuchar) with 1.
lia.
Qed.

(* ================================================================= *)
(** ** The digest as bytes of the specification *)

(** The thirty-two bytes [shrincs_sha256] stores are [int_to_bytes] of the digest word. *)
Lemma word_to_vals_int_to_bytes (w : word U256) : word_to_vals w = vals (int_to_bytes w 32).
Proof.
unfold word_to_vals, bytes_of_word, vals.
change (tval (int_to_bytes w 32))
  with (map (fun i : nat => wrepr U8 (wunsigned w / 256 ^ Z.of_nat (32 - 1 - i)))
          (iota 0 32)).
change (wnbytes U256) with 32%nat.
rewrite <- (map_seq_list (fun i : nat => byte_of_word U256 w i) (iota 0 32)).
rewrite <- (map_seq_list
              (fun i : nat => wrepr U8 (wunsigned w / 256 ^ Z.of_nat (32 - 1 - i)))
              (iota 0 32)).
rewrite !List.map_map.
apply List.map_ext.
intros i.
unfold Vubyte.
cbn [rep_val rep_u8].
do 2 f_equal.
pose proof (byte_of_word_range U256 w i) as Hrange.
rewrite Byte.unsigned_repr by rep_lia.
rewrite wunsigned_wrepr_u8.
unfold byte_of_word.
change (wnbytes U256) with 32%nat.
set (m := (32 - 1 - i)%nat).
change 255 with (Z.ones 8).
rewrite Z.land_ones by lia.
rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 8) with 256.
rewrite <- multE.
rewrite Nat2Z.inj_mul.
rewrite Z.pow_mul_r by lia.
reflexivity.
Qed.

(** The bytes the contract of [src/sha256.c] quantifies over, read back as the numbers the hash is defined on. *)
Lemma map_unsigned_bytes (x : seq UInt8) :
  List.map Byte.unsigned (List.map (fun b : UInt8 => Byte.repr (wunsigned b)) x)
  = map (fun b : UInt8 => wunsigned b) x.
Proof.
rewrite <- (map_seq_list (fun b : UInt8 => wunsigned b) x).
rewrite List.map_map.
apply List.map_ext.
intros b.
pose proof (wunsigned_u8_range b) as Hb.
apply Byte.unsigned_repr.
rep_lia.
Qed.

(* ================================================================= *)
(** ** The three contracts on a buffer being filled *)

(** [shrincs_memcpy] appending the window [ks, ks + n) of a byte string to the buffer.

    The two pointers the C passes are quantified as they are, [q_d] and [q_s], and tied to the buffers by a premise each. A call that starts at the head of a buffer passes the buffer's own pointer, which is [offset_val 0] of itself only once it is known to be a pointer, so the tie is a proof obligation and not a syntactic match. The bytes copied are a witness too, [x], so the caller names them in the vocabulary of the specification. *)
Definition memcpy_fill_spec : ident * funspec :=
  DECLARE util._shrincs_memcpy
  WITH sh_d : share, sh_s : share, p_d : Values.val, p_s : Values.val,
       q_d : Values.val, q_s : Values.val,
       md : Z, ms : Z, k : Z, ks : Z, n : Z,
       f : seq UInt8, src : seq UInt8, x : seq UInt8
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (writable_share sh_d; readable_share sh_s;
          q_d = offset_val k p_d; q_s = offset_val ks p_s;
          Zlength f = k; Zlength src = ms; sublist ks (ks + n) src = x;
          0 <= ks; 0 <= n; ks + n <= ms; k + n <= md; md <= Int64.max_unsigned)
    PARAMS (q_d; q_s; Vlong (Int64.repr n))
    SEP (filled sh_d md f p_d; data_at sh_s (tarray tuchar ms) (vals src) p_s)
  POST [ tptr tvoid ]
    PROP () RETURN (q_d)
    SEP (filled sh_d md (cat f x) p_d; data_at sh_s (tarray tuchar ms) (vals src) p_s).

Lemma memcpy_fill_sub : funspec_sub (snd shrincs_memcpy_spec) (snd memcpy_fill_spec).
Proof.
do_funspec_sub.
destruct w as [[[[[[[[[[[[[sh_d sh_s] p_d] p_s] q_d] q_s] md] ms] k] ks] n] f] src] x].
clear H.
simpl.
Intros.
subst q_d q_s args.
rename H3 into Hf.
rename H4 into Hsrc.
rename H5 into Hx.
assert (Hk : 0 <= k) by (rewrite <- Hf; apply Zlength_nonneg).
assert (Hlx : Zlength x = n) by (rewrite <- Hx; rewrite Zlength_sublist by lia; lia).
assert (Hvs : Zlength (vals src) = ms) by (rewrite Zlength_vals; exact Hsrc).
assert_PROP (field_compatible (tarray tuchar md) [] p_d) as FCd
  by (unfold filled; entailer!).
assert_PROP (field_compatible (tarray tuchar ms) [] p_s) as FCs by entailer!.
(* the buffer: written part, the window, the rest *)
rewrite (filled_split sh_d md f p_d k n Hf H7 H9 FCd).
(* the source: before the window, the window, after it *)
rewrite (tuchar_split3 sh_s p_s (vals src) ms n ks Hvs H7 H6 H8 FCs).
rewrite (sublist_vals ks (ks + n) src).
rewrite Hx.
rewrite (vals_ints x).
Exists (sh_s, sh_d, offset_val k p_d, offset_val ks p_s, n,
        List.map (fun b : UInt8 => Int.repr (wunsigned b)) x)
       (data_at sh_d (tarray tuchar k) (vals f) p_d *
        data_at_ sh_d (tarray tuchar (md - (k + n))) (offset_val (k + n) p_d) *
        data_at sh_s (tarray tuchar ks) (sublist 0 ks (vals src)) p_s *
        data_at sh_s (tarray tuchar (ms - (ks + n))) (sublist (ks + n) ms (vals src))
          (offset_val (ks + n) p_s))%logic.
apply andp_right.
- (* the precondition of [shrincs_memcpy], with the pieces around the two windows as frame *)
  rewrite <- (memory_block_data_at__tarray_tuchar_eq sh_d (offset_val k p_d) n) by rep_lia.
  apply andp_left2.
  entailer!.
- (* its postcondition puts the buffer back with the window written *)
  apply prop_right.
  intros rho'.
  rewrite <- (filled_join sh_d md f x p_d k n Hf Hlx H9 FCd).
  rewrite (vals_ints x).
  entailer!.
Qed.

(** [shrincs_memset] appending [n] zero bytes. *)
Definition memset_fill_spec : ident * funspec :=
  DECLARE util._shrincs_memset
  WITH sh : share, p : Values.val, q : Values.val, md : Z, k : Z, n : Z,
       f : seq UInt8, x : seq UInt8
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; q = offset_val k p;
          Zlength f = k; nseq (Z.to_nat n) (uint U8 0) = x;
          0 <= n; k + n <= md; md <= Int64.max_unsigned)
    PARAMS (q; Vint (Int.repr 0); Vlong (Int64.repr n))
    SEP (filled sh md f p)
  POST [ tptr tvoid ]
    PROP () RETURN (q)
    SEP (filled sh md (cat f x) p).

Lemma vals_zeros (m : nat) :
  List.repeat (Vint (Int.repr 0)) m = vals (nseq m (uint U8 0)).
Proof.
unfold vals.
rewrite <- repeatE.
rewrite map_repeat.
reflexivity.
Qed.

Lemma memset_fill_sub : funspec_sub (snd shrincs_memset_spec) (snd memset_fill_spec).
Proof.
do_funspec_sub.
destruct w as [[[[[[[sh p] q] md] k] n] f] x].
clear H.
simpl.
Intros.
subst q args.
rename H1 into Hf.
rename H2 into Hx.
assert (Hk : 0 <= k) by (rewrite <- Hf; apply Zlength_nonneg).
assert (Hlx : Zlength x = n).
{ rewrite <- Hx.
  rewrite <- repeatE.
  rewrite Zlength_repeat by lia.
  reflexivity. }
assert_PROP (field_compatible (tarray tuchar md) [] p) as FC
  by (unfold filled; entailer!).
rewrite (filled_split sh md f p k n Hf H3 H4 FC).
Exists (sh, offset_val k p, n, Int.repr 0)
       (data_at sh (tarray tuchar k) (vals f) p *
        data_at_ sh (tarray tuchar (md - (k + n))) (offset_val (k + n) p))%logic.
apply andp_right.
- rewrite <- (memory_block_data_at__tarray_tuchar_eq sh (offset_val k p) n) by rep_lia.
  apply andp_left2.
  entailer!.
- apply prop_right.
  intros rho'.
  rewrite <- (filled_join sh md f x p k n Hf Hlx H4 FC).
  rewrite <- Hx.
  rewrite <- vals_zeros.
  entailer!.
Qed.

(** [shrincs_sha256] over the written part of a buffer, with the digest as the bytes [Shrincs.spec]'s [sha256] returns. The bound is SHA-256's own, far above any buffer here. *)
Definition sha256_fill_spec : ident * funspec :=
  DECLARE Shrincs.clight.sha256._shrincs_sha256
  WITH out_ptr : Values.val, in_ptr : Values.val, md : Z, n : Z, f : seq UInt8,
       sh_o : share, sh_i : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_i;
          Zlength f = n; n <= md; md < 2305843009213693952)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr n))
    SEP (data_at_ sh_o (tarray tuchar 32) out_ptr; filled sh_i md f in_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 32) (vals (sha256 f)) out_ptr;
         filled sh_i md f in_ptr).

Lemma sha256_fill_sub : funspec_sub (snd sha256_spec) (snd sha256_fill_spec).
Proof.
do_funspec_sub.
destruct w as [[[[[[out_ptr in_ptr] md] n] f] sh_o] sh_i].
clear H.
simpl.
Intros.
subst args.
rename H1 into Hf.
assert (Hn : 0 <= n) by (rewrite <- Hf; apply Zlength_nonneg).
assert_PROP (field_compatible (tarray tuchar md) [] in_ptr) as FC
  by (unfold filled; entailer!).
rewrite (filled_split sh_i md f in_ptr n 0 Hf ltac:(lia) ltac:(lia) FC).
set (msg := List.map (fun b : UInt8 => Byte.repr (wunsigned b)) f).
assert (Hmsg : Zlength msg = n) by (unfold msg; rewrite Zlength_map; exact Hf).
Exists (msg, out_ptr, in_ptr, sh_i, sh_o)
       (data_at_ sh_i (tarray tuchar 0) (offset_val n in_ptr) *
        data_at_ sh_i (tarray tuchar (md - (n + 0))) (offset_val (n + 0) in_ptr))%logic.
rewrite Hmsg.
rewrite (vals_bytes f).
fold msg.
apply andp_right.
- apply andp_left2.
  entailer!.
  change (two_power_pos 61) with 2305843009213693952.
  lia.
- apply prop_right.
  intros rho'.
  rewrite Shrincs.internal.vst.sha256.sync.sync_sha256.
  unfold msg.
  rewrite map_unsigned_bytes.
  rewrite word_to_vals_int_to_bytes.
  rewrite Shrincs.spec.sha256.unlock.
  entailer!.
Qed.
