(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * contract.helpers_wots: VST funspecs for the WOTS+C step functions in [src/wots.c].

    Each funspec relates a C step function to its pure counterpart in
    [model.wots]: [_t_sf], [_h_grind], [_derive_sk], [_chain_iter],
    [_chain_from_seed], [_map_digest], [_grind_to_constant_sum].  Bodies
    are proved in [verif/*].  The shared tweakable-hash specs
    ([shrincs_adrs_put32], [shrincs_thash]) live in [contract.helpers_thash]
    (they back [src/thash.c], not [src/wots.c]).  Bundled with the libc
    funspecs ([contract.helpers_libc]) and the tweakable-hash funspecs
    ([contract.helpers_thash]) as [Gprog_wots] in [contract.gprog]. *)

From VST Require Import floyd.proofauto.
From Shrincs.internal.vst.support Require Import contract.public.

Open Scope Z_scope.
Open Scope logic.

Local Abbreviation adrs := (address.adrs len w_pred).

(* ================================================================= *)
(** ** [shrincs_wots_t_sf(out, pk_seed, addr, ends)] -- the tweakable hash over the
    [len] concatenated chain tips ([len * n = 512] bytes):
    [T_sf pk_seed A ends = SHA256(pk_seed || zeros(48) || ADRS || ends)[:16]].
    Reads [addr]; does not mutate it. *)

Definition shrincs_wots_t_sf_spec : ident * funspec :=
  DECLARE _shrincs_wots_t_sf
  WITH out_ptr : val, ps_ptr : val, a_ptr : val, e_ptr : val,
       A : adrs, pk_seed : block, ends : block,
       sh_o : share, sh_ps : share, sh_a : share, sh_e : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_o;
          readable_share sh_ps; readable_share sh_a; readable_share sh_e;
          Zlength pk_seed = n_bytes; Zlength ends = Z.of_nat (len * n))
    PARAMS (out_ptr; ps_ptr; a_ptr; e_ptr)
    SEP (data_at_ sh_o (tarray tuchar n_bytes) out_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals A)         a_ptr;
         data_at sh_e  (tarray tuchar (Z.of_nat (len * n))) (block_to_vals ends) e_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes) (block_to_vals (T_sf pk_seed A ends)) out_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals A)         a_ptr;
         data_at sh_e  (tarray tuchar (Z.of_nat (len * n))) (block_to_vals ends) e_ptr).

(* ================================================================= *)
(** ** [shrincs_wots_h_grind(out, msg, counter, pk_seed, addr)] -- grinding hash
    [H_grind(pk_seed, addr, msg, counter)].  Reads the first 10 bytes of
    [addr] (caller has set the grind type byte); does not mutate [addr].
    [msg] is the 32-byte message digest. *)

Definition shrincs_wots_h_grind_spec : ident * funspec :=
  DECLARE _shrincs_wots_h_grind
  WITH out_ptr : val, m_ptr : val, counter : Z, ps_ptr : val, a_ptr : val,
       msg : block, pk_seed : block, a : adrs,
       sh_o : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tuint, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_o;
          readable_share sh_m; readable_share sh_ps; readable_share sh_a;
          0 <= counter < 2 ^ 16;
          Zlength msg = msg_bytes; Zlength pk_seed = n_bytes)
    PARAMS (out_ptr; m_ptr; Vint (Int.repr counter); ps_ptr; a_ptr)
    SEP (data_at_ sh_o (tarray tuchar n_bytes) out_ptr;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      m_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes)
           (block_to_vals (H_grind pk_seed a msg counter)) out_ptr;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      m_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr).

(* ================================================================= *)
(** ** [shrincs_wots_derive_sk(out, chain_i, sk_seed, pk_seed, addr)].

    Implements [shrincs_wots_derive_sk chain_i sk_seed pk_seed a].  Mutates [addr] to
    the PRF-typed address [shrincs_wots_prf_adrs a chain_i]. *)

Definition shrincs_wots_derive_sk_spec : ident * funspec :=
  DECLARE _shrincs_wots_derive_sk
  WITH out_ptr : val, ss_ptr : val, ps_ptr : val, a_ptr : val,
       chain_i : Z,
       sk_seed : block, pk_seed : block, a : adrs,
       sh_o : share, sh_ss : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tuint, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_o; writable_share sh_a;
          readable_share sh_ss; readable_share sh_ps;
          0 <= chain_i < Z.of_nat len;
          Zlength sk_seed = n_bytes; Zlength pk_seed = n_bytes)
    PARAMS (out_ptr; Vint (Int.repr chain_i); ss_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_o  (tarray tuchar n_bytes) out_ptr;
         data_at sh_ss (tarray tuchar n_bytes) (block_to_vals sk_seed)  ss_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes)
           (block_to_vals (shrincs_wots_derive_sk (to_chain32 (Z.to_nat chain_i)) sk_seed pk_seed a))
           out_ptr;
         data_at sh_ss (tarray tuchar n_bytes) (block_to_vals sk_seed)  ss_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals (shrincs_wots_prf_adrs a (to_chain32 (Z.to_nat chain_i)))) a_ptr).

(* ================================================================= *)
(** ** [shrincs_wots_chain_iter(node, start, steps, pk_seed, addr)] -- iterates
    [F] [steps] times in place on [node].  The caller sets the type +
    chain address before calling; this only writes the hash address.
    [chain_addr_post] is [set_payload_c a (start+steps-1)] when
    [steps > 0], else [a] untouched. *)

Definition chain_addr_post (a : adrs) (start steps : nat) : adrs :=
  match steps with
  | O   => a
  | S k => set_hash_pos a (to_pos15 (start + k))
  end.

(** [chain_addr_post] only touches the hash word, so it preserves the
    caller-prefilled prefix ([adrs_struct_eq]).  Shared by the sign /
    from_sig chain loops that thread the residual address. *)
Lemma chain_addr_post_struct_eq : forall a start steps,
  adrs_struct_eq (chain_addr_post a start steps) a.
Proof.
  intros a start steps. unfold chain_addr_post.
  destruct steps.
  - apply adrs_struct_eq_refl.
  - apply set_hash_pos_struct_eq.
Qed.

(** [chain_addr_post] only touches the position word, so on a hash-typed
    address it stays hash-typed and keeps a zero reserved word. *)
Lemma chain_addr_post_hash_type : forall b start steps,
  adrs_type b = SF_SHRINCS_WOTS_HASH ->
  adrs_type (chain_addr_post b start steps) = SF_SHRINCS_WOTS_HASH.
Proof.
  intros b start steps Ht. unfold chain_addr_post.
  destruct steps as [|k].
  - exact Ht.
  - destruct b as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht.
    reflexivity.
Qed.

Lemma chain_addr_post_pa0 : forall b start steps,
  adrs_type b = SF_SHRINCS_WOTS_HASH ->
  payload_a_z (chain_addr_post b start steps) = 0.
Proof.
  intros b start steps Ht. unfold chain_addr_post.
  destruct b as [nh ni ch pos| | | | | | | | | | | ]; try discriminate Ht;
    destruct steps; reflexivity.
Qed.

Definition shrincs_wots_chain_iter_spec : ident * funspec :=
  DECLARE _shrincs_wots_chain_iter
  WITH buf_ptr : val, ps_ptr : val, a_ptr : val,
       start : Z, steps : Z,
       in_buf : block, pk_seed : block, a : adrs,
       sh_b : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tuint, tuint, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_b; writable_share sh_a;
          readable_share sh_ps;
          0 <= start; 0 <= steps; start + steps <= Z.of_nat w_pred;
          Zlength in_buf = n_bytes; Zlength pk_seed = n_bytes;
          (* The ADRS must already carry the WOTS+C chain type / index; the
             loop only varies the position field ([set_hash_pos] is the
             identity on any non-hash arm, so the C's unconditional position
             store would otherwise diverge from the model). *)
          exists nh ni chain pos, a = Wc_hash nh ni chain pos)
    PARAMS (buf_ptr; Vint (Int.repr start); Vint (Int.repr steps);
            ps_ptr; a_ptr)
    SEP (data_at sh_b (tarray tuchar n_bytes) (block_to_vals in_buf)   buf_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_b (tarray tuchar n_bytes)
           (block_to_vals
              (chain_iter_c in_buf (Z.to_nat start) (Z.to_nat steps) pk_seed a))
           buf_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals
                    (chain_addr_post a (Z.to_nat start) (Z.to_nat steps)))
                 a_ptr).

(* ================================================================= *)
(** ** [shrincs_wots_chain_from_seed(node, chain_i, steps, sk_seed, pk_seed, addr)] --
    the per-chain kernel shared by [shrincs_wots_pubkey_gen] and [shrincs_wots_sign]:
    [shrincs_wots_derive_sk] the chain secret (PRF-typed ADRS), re-type the ADRS to the
    WOTS+C hash, then [shrincs_wots_chain_iter] [steps] steps from index 0.  Leaves
    [node] holding the chain result and [addr] the post-chain hash address.
    ([node] is fully overwritten by [shrincs_wots_derive_sk], so its input is [data_at_].) *)

Definition shrincs_wots_chain_from_seed_spec : ident * funspec :=
  DECLARE _shrincs_wots_chain_from_seed
  WITH node_ptr : val, ss_ptr : val, ps_ptr : val, a_ptr : val,
       chain_i : Z, steps : Z,
       sk_seed : block, pk_seed : block, a : adrs,
       sh_n : share, sh_ss : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tuint, tuint, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_n; writable_share sh_a;
          readable_share sh_ss; readable_share sh_ps;
          0 <= chain_i < Z.of_nat len;
          0 <= steps <= Z.of_nat w_pred;
          Zlength sk_seed = n_bytes; Zlength pk_seed = n_bytes)
    PARAMS (node_ptr; Vint (Int.repr chain_i); Vint (Int.repr steps);
            ss_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_n  (tarray tuchar n_bytes) node_ptr;
         data_at sh_ss (tarray tuchar n_bytes) (block_to_vals sk_seed)  ss_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_n (tarray tuchar n_bytes)
           (block_to_vals
              (chain_iter_c (shrincs_wots_derive_sk (to_chain32 (Z.to_nat chain_i)) sk_seed pk_seed a)
                 0 (Z.to_nat steps) pk_seed
                 (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 (Z.to_nat chain_i))))) node_ptr;
         data_at sh_ss (tarray tuchar n_bytes) (block_to_vals sk_seed)  ss_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals
                    (chain_addr_post (shrincs_wots_hash_adrs w_pred_pos a (to_chain32 (Z.to_nat chain_i)))
                       0 (Z.to_nat steps))) a_ptr).

(* ================================================================= *)
(** ** [shrincs_wots_map_digest(digits, msg, counter, pk_seed, addr)] -- write
    the [len] base-16 digits of [H_grind(...,counter)] and return their
    sum.  Sets [addr] to the grind-typed [shrincs_wots_grind_adrs a]. *)

Definition shrincs_wots_map_digest_spec : ident * funspec :=
  DECLARE _shrincs_wots_map_digest
  WITH d_ptr : val, m_ptr : val, counter : Z, ps_ptr : val, a_ptr : val,
       msg : block, pk_seed : block, a : adrs,
       sh_d : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tuint, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_d; writable_share sh_a;
          readable_share sh_m; readable_share sh_ps;
          0 <= counter < 2 ^ 16;
          Zlength msg = msg_bytes; Zlength pk_seed = n_bytes;
          (* Grind-typing zeroes the payload (the reachable-states grind
             address carries none), but the C leaves it; so the anchor must
             enter clean.  [H_grind] reads only ADRS[:10], so the digest is
             unaffected either way.  Preserved by the caller's re-entry with
             [shrincs_wots_grind_adrs a] (which is clean). *)
          clean_anchor a)
    PARAMS (d_ptr; m_ptr; Vint (Int.repr counter); ps_ptr; a_ptr)
    SEP (data_at_ sh_d (tarray tuchar (Z.of_nat len)) d_ptr;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      m_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (Z.of_nat (list_sum (digest_of pk_seed a msg counter)))))
    SEP (data_at sh_d (tarray tuchar (Z.of_nat len))
           (digits_to_vals (digest_of pk_seed a msg counter)) d_ptr;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      m_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr             (adrs_to_vals (shrincs_wots_grind_adrs a)) a_ptr).

(* ================================================================= *)
(** ** [shrincs_wots_grind_to_constant_sum(digits, counter_out, msg, pk_seed, addr)]
    -- least good counter.  Post keyed on the model [find_counter]; sets
    [addr] to [shrincs_wots_grind_adrs a]. *)

Definition shrincs_wots_grind_to_constant_sum_spec : ident * funspec :=
  DECLARE _shrincs_wots_grind_to_constant_sum
  WITH d_ptr : val, c_ptr : val, m_ptr : val, ps_ptr : val, a_ptr : val,
       msg : block, pk_seed : block, a : adrs,
       sh_d : share, sh_c : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuint, tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_d; writable_share sh_c; writable_share sh_a;
          readable_share sh_m; readable_share sh_ps;
          Zlength msg = msg_bytes; Zlength pk_seed = n_bytes;
          (* clean anchor (see [shrincs_wots_map_digest_spec]); this passes
             it straight to [shrincs_wots_map_digest], and its re-entry with
             [shrincs_wots_grind_adrs a] preserves it. *)
          clean_anchor a)
    PARAMS (d_ptr; c_ptr; m_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_d (tarray tuchar (Z.of_nat len)) d_ptr;
         data_at_ sh_c tuint c_ptr;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      m_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr
             (match find_counter pk_seed a msg with Some _ => 0 | None => 1 end)))
    SEP (match find_counter pk_seed a msg with
         | Some c => data_at sh_d (tarray tuchar (Z.of_nat len))
                       (digits_to_vals (digest_of pk_seed a msg c)) d_ptr *
                     data_at sh_c tuint (Vint (Int.repr c)) c_ptr
         | None   => data_at_ sh_d (tarray tuchar (Z.of_nat len)) d_ptr *
                     data_at_ sh_c tuint c_ptr
         end;
         data_at sh_m  (tarray tuchar msg_bytes) (block_to_vals msg)      m_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pk_seed) ps_ptr;
         data_at sh_a  t_addr             (adrs_to_vals (shrincs_wots_grind_adrs a)) a_ptr).
