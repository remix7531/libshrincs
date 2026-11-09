(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * body_shrincs_ct_memcmp: VST body proof for [shrincs_ct_memcmp].

    Proves that the in-tree constant-time byte-compare returns
    [Int.zero] iff the two byte-arrays agree element-wise.  The loop
    OR-accumulates [a[i] ^ b[i]] into [_diff]; since [_diff] is a
    [uint8_t] its zero-extension is the identity throughout, and the
    invariant carries the byte bound on the accumulator together with
    the biconditional [diff = 0 <-> the length-i prefixes agree]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.gprog contract.lemmas.
From Shrincs.clight Require Import util.

Open Scope Z_scope.

Lemma body_shrincs_ct_memcmp :
  semax_body Vprog Gprog_util f_shrincs_ct_memcmp shrincs_ct_memcmp_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.
  match goal with
  | H : Forall _ p_contents |- _ => rename H into Hpb
  end.
  match goal with
  | H : Forall _ q_contents |- _ => rename H into Hqb
  end.

  (* ===== Initialise [diff = 0] ===== *)

  forward.

  (* ===== Loop: invariant carries byte-bound + biconditional ===== *)

  forward_for_simple_bound n
    (EX i : Z, EX diff_v : int,
      PROP (0 <= Int.unsigned diff_v < 256;
            diff_v = Int.zero <->
              sublist 0 i p_contents = sublist 0 i q_contents)
      LOCAL (temp _diff (Vint diff_v); temp _a p; temp _b q;
             temp _n (Vlong (Int64.repr n)))
      SEP (data_at psh (tarray tuchar n) (map Vint p_contents) p;
           data_at qsh (tarray tuchar n) (map Vint q_contents) q)).

  (* ----- Loop entry: i = 0, diff = 0 ----- *)

  - Exists Int.zero.
    entailer!!.
    rewrite !sublist_nil_gen by lia.
    easy.

  (* ----- Loop body ----- *)

  - Intros.
    rename H3 into Hdb.
    rename H4 into Hbi.

    assert (Hai : 0 <= Int.unsigned (Znth i p_contents) < 256)
      by (apply Forall_Znth; auto; lia).
    assert (Hbj : 0 <= Int.unsigned (Znth i q_contents) < 256)
      by (apply Forall_Znth; auto; lia).

    (* Load a[i] *)
    forward.

    (* Load b[i] *)
    forward.

    (* diff = diff | (uint8_t)(a[i] ^ b[i]) *)
    forward.

    set (xv := Int.xor (Znth i p_contents) (Znth i q_contents)).
    assert (Hxb : 0 <= Int.unsigned xv < 256)
      by (subst xv; apply int_xor_byte_bound; auto).
    assert (Hxz : Int.zero_ext 8 xv = xv) by (apply zero_ext_8_byte; auto).
    set (nv := Int.or diff_v xv).
    assert (Hnb : 0 <= Int.unsigned nv < 256)
      by (subst nv; apply int_or_byte_bound; auto).
    assert (Hnz : Int.zero_ext 8 nv = nv) by (apply zero_ext_8_byte; auto).

    (* re-establish the invariant at i + 1 for the new accumulator *)
    Exists nv.
    entailer!!.
    split.
    + (* ->: nv = 0 forces diff = 0 and xor = 0; extend the equal prefix by byte i *)
      intro Hnv0.
      apply int_or_eq_zero_iff in Hnv0 as [Hd0 Hx0].
      apply (proj1 (int_xor_eq_zero_iff _ _)) in Hx0.
      rewrite !(sublist_split 0 i (i + 1)) by lia.
      rewrite !(sublist_one i (i + 1)) by lia.
      rewrite Hx0, (proj1 Hbi Hd0).
      reflexivity.
    + (* <-: prefix equality at i + 1 gives the old prefix equality (so diff = 0)
         and equal bytes at i (so the xor is 0) *)
      intro Heq.
      rewrite !(sublist_split 0 i (i + 1)) in Heq by lia.
      rewrite !(sublist_one i (i + 1)) in Heq by lia.
      apply app_inj_tail in Heq as [Hpre Hknth].
      rewrite (proj2 Hbi Hpre).
      rewrite Int.or_zero_l.
      apply int_xor_eq_zero_iff.
      exact Hknth.

  (* ----- Loop exit: return _diff ----- *)

  - Intros diff_v.
    rename H2 into Hdb.
    rename H3 into Hbi.

    forward.

    Exists diff_v.
    entailer!!.
    (* at i = n the prefixes are the whole arrays: the invariant's
       biconditional is exactly the POST's *)
    rewrite !sublist_same in Hbi by auto.
    exact Hbi.
Qed.
