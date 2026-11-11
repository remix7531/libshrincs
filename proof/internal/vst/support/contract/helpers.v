(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.helpers: the contracts of the functions a client cannot call

    One funspec per function of [src/util.c], [src/thash.c] and [src/wots.c] that [include/shrincs.h] does not declare. The three it does declare and SHA-256 have their public contracts in [Shrincs.contracts].

    Every WOTS+C helper is named after a function of the reference, and its postcondition names that function of [Shrincs.spec] on the values the caller passed. A buffer is quantified as a tuple, so its length is in its type. A machine integer is quantified as a word and passed as the C integer of its value.

    THE SPECIFICATION IS FOLDED HERE AND STAYS FOLDED. The [Arguments] block below stops [simpl] at every function of [Shrincs.spec], and it travels with the Import of this file. Floyd calls [simpl] inside nearly every tactic, and on a goal that mentions [slice], [pack] or [int_to_bytes] at a concrete length it would spell the bytes out one by one. The body proofs move between the C and the specification by the lemmas of [Shrincs.internal.vst.shape] alone. *)

From Shrincs.internal.vst.support Require Export base.
From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Shrincs Require Export spec contracts.
From Shrincs.internal.vst Require Export shape.
From Shrincs.clight Require util thash.

Local Open Scope Z_scope.

#[global] Arguments uint : simpl never.
#[global] Arguments int_to_bytes : simpl never.
#[global] Arguments int_from_bytes : simpl never.
#[global] Arguments slice : simpl never.
#[global] Arguments range : simpl never.
#[global] Arguments replicate : simpl never.
#[global] Arguments zeros : simpl never.
#[global] Arguments concat : simpl never.
#[global] Arguments base_2b : simpl never.
#[global] Arguments pack : simpl never.
#[global] Arguments to_bytes : simpl never.
#[global] Arguments T_sf : simpl never.
#[global] Arguments F : simpl never.
#[global] Arguments H_grind : simpl never.
#[global] Arguments PRF : simpl never.
#[global] Arguments wots_c_chain_iter : simpl never.
#[global] Arguments wots_c_grind_to_constant_sum : simpl never.
#[global] Arguments wots_c_map_digest : simpl never.
#[global] Arguments wots_c_pubkey_gen : simpl never.
#[global] Arguments wots_c_sign : simpl never.
#[global] Arguments wots_c_pubkey_from_sig : simpl never.
#[global] Arguments blocks : simpl never.
#[global] Arguments digest_indexes : simpl never.
#[global] Arguments chain_from_seed : simpl never.
#[global] Arguments chain_from_sig : simpl never.
#[global] Arguments pubkey_gen_tips : simpl never.
#[global] Arguments signature_of : simpl never.
#[global] Arguments recovered_tips : simpl never.
#[global] Arguments WOTS_C_CHAIN_COUNT : simpl never.
#[global] Arguments WOTS_C_CHAINS_SIZE : simpl never.
#[global] Arguments WOTS_C_CONSTANT_SUM : simpl never.

(* ================================================================= *)
(** ** Values the helpers pass that the entry points do not *)

(** A 32-bit and a 16-bit unsigned integer, each passed as an [unsigned int]. The C widens every counter to 32 bits. Abbreviations and not definitions, so a body proof sees the [Vint] floyd computes with. *)
Abbreviation u32_val x := (Vint (Int.repr (wunsigned (x : UInt32)))) (only parsing).
Abbreviation u16_val x := (Vint (Int.repr (wunsigned (x : UInt16)))) (only parsing).

(** Chain indexes, one per [unsigned char]. *)
Definition index_vals (indexes : seq nat) : list Values.val :=
  List.map (fun d : nat => Vint (Int.repr (Z.of_nat d))) indexes.

#[global] Arguments th : simpl never.

(* ================================================================= *)
(** ** [src/util.c] *)

Module helpers_libc.

Import util.

Definition shrincs_memset_spec : ident * funspec :=
  DECLARE _shrincs_memset
  WITH sh : share, p : Values.val, n : Z, c : Int.int
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned;
          0 <= Int.unsigned c < 256)
    PARAMS (p; Vint c; Vlong (Int64.repr n))
    SEP (memory_block sh n p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at sh (tarray tuchar n) (List.repeat (Vint c) (Z.to_nat n)) p).

Definition shrincs_memcpy_spec : ident * funspec :=
  DECLARE _shrincs_memcpy
  WITH qsh : share, psh : share, p : Values.val, q : Values.val,
       n : Z, contents : list Int.int
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share qsh; writable_share psh; 0 <= n <= Int64.max_unsigned)
    PARAMS (p; q; Vlong (Int64.repr n))
    SEP (data_at qsh (tarray tuchar n) (List.map Vint contents) q; memory_block psh n p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at qsh (tarray tuchar n) (List.map Vint contents) q;
         data_at psh (tarray tuchar n) (List.map Vint contents) p).

Definition shrincs_panic_spec : ident * funspec :=
  DECLARE _shrincs_panic
  WITH u : unit
  PRE [ ] PROP (False) PARAMS () SEP ()
  POST [ tvoid ] PROP () RETURN () SEP ().

End helpers_libc.

(* ================================================================= *)
(** ** [src/thash.c] *)

Module helpers_thash.

Import thash.

(** [Address.pack]. *)
Definition shrincs_adrs_pack_spec : ident * funspec :=
  DECLARE _shrincs_adrs_pack
  WITH a_ptr : Values.val, height : UInt8, index : UInt64, address_type : UInt8,
       word1 : UInt32, word2 : UInt32, word3 : UInt32, sh : share
  PRE [ tptr tuchar, tuchar, tulong, tuchar, tuint, tuint, tuint ]
    PROP (writable_share sh)
    PARAMS (a_ptr; rep_val height; rep_val index; rep_val address_type;
            u32_val word1; u32_val word2; u32_val word3)
    SEP (data_at_ sh (tarray tuchar 22) a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh (tarray tuchar 22)
           (vals (pack height index address_type word1 word2 word3)) a_ptr).

(** The message has no fixed length, so it is a [seq] and its length is a premise. The bound is the size of the C's buffer. *)
Definition shrincs_thash_spec : ident * funspec :=
  DECLARE _shrincs_thash
  WITH out_ptr : Values.val, ps_ptr : Values.val, a_ptr : Values.val,
       m_ptr : Values.val, msglen : Z,
       pk_seed : Bytes 16, adrs : Bytes 22, msg : seq UInt8,
       sh_o : share, sh_ps : share, sh_a : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_ps; readable_share sh_a; readable_share sh_m;
          Zlength msg = msglen; msglen <= 512)
    PARAMS (out_ptr; ps_ptr; a_ptr; m_ptr; Vlong (Int64.repr msglen))
    SEP (data_at_ sh_o (tarray tuchar 16) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_a (tarray tuchar 22) (vals adrs) a_ptr;
         data_at sh_m (tarray tuchar msglen) (vals msg) m_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 16) (vals (th pk_seed adrs msg)) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_a (tarray tuchar 22) (vals adrs) a_ptr;
         data_at sh_m (tarray tuchar msglen) (vals msg) m_ptr).

End helpers_thash.

(* ================================================================= *)
(** ** [src/wots.c], the static functions *)

Module helpers_wots.

Definition shrincs_wots_c_t_sf_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_t_sf
  WITH out_ptr : Values.val, ps_ptr : Values.val, m_ptr : Values.val,
       pk_seed : Bytes 16, node_height : UInt8, node_index : UInt64,
       M_l : Bytes WOTS_C_CHAINS_SIZE,
       sh_o : share, sh_ps : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar, tuchar, tulong, tptr tuchar ]
    PROP (writable_share sh_o; readable_share sh_ps; readable_share sh_m)
    PARAMS (out_ptr; ps_ptr; rep_val node_height; rep_val node_index; m_ptr)
    SEP (data_at_ sh_o (tarray tuchar 16) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 512) (vals M_l) m_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 16)
           (vals (T_sf pk_seed (WotsCPk node_height node_index) M_l)) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 512) (vals M_l) m_ptr).

Definition shrincs_wots_c_f_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_f
  WITH out_ptr : Values.val, ps_ptr : Values.val, m_ptr : Values.val,
       pk_seed : Bytes 16, node_height : UInt8, node_index : UInt64,
       chain_index : UInt32, hash_index : UInt32, M_1 : Bytes 16,
       sh_o : share, sh_ps : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar, tuchar, tulong, tuint, tuint, tptr tuchar ]
    PROP (writable_share sh_o; readable_share sh_ps; readable_share sh_m)
    PARAMS (out_ptr; ps_ptr; rep_val node_height; rep_val node_index;
            u32_val chain_index; u32_val hash_index; m_ptr)
    SEP (data_at_ sh_o (tarray tuchar 16) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 16) (vals M_1) m_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 16)
           (vals (F pk_seed (WotsCHash node_height node_index chain_index hash_index) M_1))
           out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 16) (vals M_1) m_ptr).

Definition shrincs_wots_c_h_grind_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_h_grind
  WITH out_ptr : Values.val, ps_ptr : Values.val, d_ptr : Values.val,
       pk_seed : Bytes 16, node_height : UInt8, node_index : UInt64,
       digest : Bytes 32, counter : UInt16,
       sh_o : share, sh_ps : share, sh_d : share
  PRE [ tptr tuchar, tptr tuchar, tuchar, tulong, tptr tuchar, tuint ]
    PROP (writable_share sh_o; readable_share sh_ps; readable_share sh_d)
    PARAMS (out_ptr; ps_ptr; rep_val node_height; rep_val node_index; d_ptr; u16_val counter)
    SEP (data_at_ sh_o (tarray tuchar 16) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_d (tarray tuchar 32) (vals digest) d_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 16)
           (vals (H_grind pk_seed (WotsCGrind node_height node_index) digest counter)) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_d (tarray tuchar 32) (vals digest) d_ptr).

Definition shrincs_wots_c_prf_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_prf
  WITH out_ptr : Values.val, ps_ptr : Values.val, ss_ptr : Values.val,
       pk_seed : Bytes 16, sk_seed : Bytes 16, node_height : UInt8, node_index : UInt64,
       tree_balanced : bool, tree_depth : UInt8, chain_index : UInt32,
       sh_o : share, sh_ps : share, sh_ss : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tuchar, tulong, tbool, tuchar, tuint ]
    PROP (writable_share sh_o; readable_share sh_ps; readable_share sh_ss)
    PARAMS (out_ptr; ps_ptr; ss_ptr; rep_val node_height; rep_val node_index;
            rep_val tree_balanced; rep_val tree_depth; u32_val chain_index)
    SEP (data_at_ sh_o (tarray tuchar 16) out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_ss (tarray tuchar 16) (vals sk_seed) ss_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 16)
           (vals (PRF pk_seed sk_seed
                    (WotsCPrf node_height node_index tree_balanced tree_depth chain_index)))
           out_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_ss (tarray tuchar 16) (vals sk_seed) ss_ptr).

(** The chain positions are counted in [Z], as the C passes them. The premise is the reference's [assert]. *)
Definition shrincs_wots_c_chain_iter_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_chain_iter
  WITH node_ptr : Values.val, ps_ptr : Values.val,
       node : Bytes 16, start : Z, stop : Z, pk_seed : Bytes 16,
       node_height : UInt8, node_index : UInt64, chain_index : UInt32,
       sh_n : share, sh_ps : share
  PRE [ tptr tuchar, tuint, tuint, tptr tuchar, tuchar, tulong, tuint ]
    PROP (writable_share sh_n; readable_share sh_ps; 0 <= start <= stop; stop <= 15)
    PARAMS (node_ptr; Vint (Int.repr start); Vint (Int.repr stop); ps_ptr;
            rep_val node_height; rep_val node_index; u32_val chain_index)
    SEP (data_at sh_n (tarray tuchar 16) (vals node) node_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_n (tarray tuchar 16)
           (vals (wots_c_chain_iter node (Z.to_nat start) (Z.to_nat stop) pk_seed
                    node_height node_index chain_index)) node_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr).

(** [base_2b] at the one instance the C has. *)
Definition shrincs_wots_c_base_2b_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_base_2b
  WITH i_ptr : Values.val, x_ptr : Values.val, x : Bytes 16,
       sh_i : share, sh_x : share
  PRE [ tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_i; readable_share sh_x)
    PARAMS (i_ptr; x_ptr)
    SEP (data_at_ sh_i (tarray tuchar 32) i_ptr;
         data_at sh_x (tarray tuchar 16) (vals x) x_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_i (tarray tuchar 32)
           (index_vals (base_2b x WOTS_C_CHAIN_BITS WOTS_C_CHAIN_COUNT)) i_ptr;
         data_at sh_x (tarray tuchar 16) (vals x) x_ptr).

(** Returns 1 and leaves the indexes written where the reference returns them, and returns 0 where the reference returns None. *)
Definition shrincs_wots_c_map_digest_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_map_digest
  WITH i_ptr : Values.val, ps_ptr : Values.val, m_ptr : Values.val,
       pk_seed : Bytes 16, message_digest : Bytes 32,
       node_height : UInt8, node_index : UInt64, counter : UInt16,
       sh_i : share, sh_ps : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tuchar, tulong, tuint ]
    PROP (writable_share sh_i; readable_share sh_ps; readable_share sh_m)
    PARAMS (i_ptr; ps_ptr; m_ptr; rep_val node_height; rep_val node_index; u16_val counter)
    SEP (data_at_ sh_i (tarray tuchar 32) i_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 32) (vals message_digest) m_ptr)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr
              (match wots_c_map_digest pk_seed message_digest node_height node_index counter with
               | Some _ => 1
               | None => 0
               end)))
    SEP (match wots_c_map_digest pk_seed message_digest node_height node_index counter with
         | Some indexes => data_at sh_i (tarray tuchar 32) (index_vals indexes) i_ptr
         | None => data_at_ sh_i (tarray tuchar 32) i_ptr
         end;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 32) (vals message_digest) m_ptr).

(** Returns the counter and leaves its indexes written where the reference returns both, and returns -1 where the reference returns None. *)
Definition shrincs_wots_c_grind_to_constant_sum_spec : ident * funspec :=
  DECLARE _shrincs_wots_c_grind_to_constant_sum
  WITH i_ptr : Values.val, ps_ptr : Values.val, m_ptr : Values.val,
       pk_seed : Bytes 16, message_digest : Bytes 32,
       node_height : UInt8, node_index : UInt64,
       sh_i : share, sh_ps : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tuchar, tulong ]
    PROP (writable_share sh_i; readable_share sh_ps; readable_share sh_m)
    PARAMS (i_ptr; ps_ptr; m_ptr; rep_val node_height; rep_val node_index)
    SEP (data_at_ sh_i (tarray tuchar 32) i_ptr;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 32) (vals message_digest) m_ptr)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr
              (match wots_c_grind_to_constant_sum pk_seed message_digest node_height
                       node_index with
               | Some (counter, _) => wunsigned counter
               | None => -1
               end)))
    SEP (match wots_c_grind_to_constant_sum pk_seed message_digest node_height
                 node_index with
         | Some (_, indexes) => data_at sh_i (tarray tuchar 32) (index_vals indexes) i_ptr
         | None => data_at_ sh_i (tarray tuchar 32) i_ptr
         end;
         data_at sh_ps (tarray tuchar 16) (vals pk_seed) ps_ptr;
         data_at sh_m (tarray tuchar 32) (vals message_digest) m_ptr).

End helpers_wots.

Export helpers_libc helpers_thash helpers_wots.
