(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.scheme

    The WOTS+C leaf operations and shared hash instance define the operational
    FXMSS tree, signing and authentication-path recovery. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec schemes games.
From Shrincs.internal.ssprove.wots Require Import scheme hop.prf games.
From Shrincs.internal.ssprove.fxmss Require Import params shape.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From mathcomp.experimental_reals Require Import distr.
From Stdlib Require Import BinInt.

(* ------------------------------------------------------------------ *)
(** ** WOTS+C leaf operations *)

Section Leaves.
Context (P : shrincs_fxmss_params) (a : shrincs_fxmss_coord) (b : bool) (d : UInt8).

Definition shrincs_fxmss_leaf_keys (pp k : bytes 16) : seq (bytes 16) :=
  derive_sk (shrincs_fxmss_leaf_params P a b d) (bytes 16) (shrincs_fxmss_prf_key P) pp
    k.
Definition shrincs_fxmss_leaf_pubkey (pp : bytes 16) (xs : seq (bytes 16)) : bytes 16 :=
  shrincs_wots_pubkey (shrincs_fxmss_leaf_params P a b d) pp xs.
Definition shrincs_fxmss_leaf_sign (pp : bytes 16) (xs : seq (bytes 16)) (m : bytes 32)
    : option (bytes (2 + WOTS_C_CHAINS_SIZE)) :=
  omap (wcp_sig_encode (shrincs_fxmss_leaf_params P a b d))
    (shrincs_wots_sign (shrincs_fxmss_leaf_params P a b d) pp xs m).
Definition shrincs_fxmss_leaf_recover (pp : bytes 16) (m : bytes 32)
    (sg : bytes (2 + WOTS_C_CHAINS_SIZE)) : option (bytes 16) :=
  let W := shrincs_fxmss_leaf_params P a b d in
  let parts := wcp_sig_decode W sg in
  if valid_digest W (digest_of W pp m parts.2) &&
       (size parts.1 == wcp_chain_count W) then
    Some (wcp_T_sf W pp (pk_adrs W)
      (complete_ends W pp (digest_of W pp m parts.2) parts.1))
  else None.

Lemma shrincs_fxmss_leaf_keys_size pp k : size (shrincs_fxmss_leaf_keys pp k) =
  wots_c_chain_count.
Proof. by rewrite /shrincs_fxmss_leaf_keys /derive_sk size_map size_iota. Qed.

Lemma shrincs_fxmss_leaf_recover_verify pp m sg root :
  (shrincs_fxmss_leaf_recover pp m sg == Some root) =
  shrincs_wots_verify (shrincs_fxmss_leaf_params P a b d) pp root m
    (wcp_sig_decode (shrincs_fxmss_leaf_params P a b d) sg).
Proof.
rewrite /shrincs_fxmss_leaf_recover /shrincs_wots_verify.
by case: (valid_digest _ _) => //=.
Qed.

Lemma shrincs_fxmss_leaf_sign_none pp xs m :
  find_counter (shrincs_fxmss_leaf_params P a b d) pp m = None ->
  shrincs_fxmss_leaf_sign pp xs m = None.
Proof. by rewrite /shrincs_fxmss_leaf_sign /shrincs_wots_sign => ->. Qed.

End Leaves.

(* ------------------------------------------------------------------ *)
(** ** Hash instance and leaf targets *)

Import PackageNotation.
#[local] Open Scope package_scope.

Lemma shrincs_fxmss_hash_message_lossless (P : shrincs_fxmss_params) :
  LosslessCode (x ← shrincs_fxmss_secret_dist P ;; ret (tval x)).
Proof.
rewrite /LosslessCode (Pr_fst_bind (prog_valid (shrincs_fxmss_secret_dist P))).
under eq_dlet do rewrite Pr_fst_ret.
rewrite -pr_predT pr_dlet.
under eq_exp do rewrite pr_dunit /=.
by rewrite exp_cst pr_predT (shrincs_fxmss_secret_lossless P) GRing.mulr1.
Qed.

Definition shrincs_fxmss_hash_message (P : shrincs_fxmss_params) : dist ('list ('word
  U8)) :=
  {code x ← shrincs_fxmss_secret_dist P ;; ret (tval x)}.

Definition shrincs_fxmss_hash_function (P : shrincs_fxmss_params) : thf.
Proof.
refine {|
th_PP := bytes 16; th_T := tweak; th_M := 'list ('word U8);
th_N := bytes 16; th_eval := shrincs_fxmss_hash_eval P;
th_dPP := shrincs_fxmss_public_seed_dist P;
th_dM := shrincs_fxmss_hash_message P;
th_dN := shrincs_fxmss_secret_dist P
|}.
Defined.

Lemma shrincs_fxmss_leaf_hash_eq P a b d :
  thf_hash (shrincs_fxmss_leaf_params P a b d) = shrincs_fxmss_hash_function P.
Proof.
rewrite /thf_hash /shrincs_fxmss_hash_function.
f_equal; apply: boolp.Prop_irrelevance.
Qed.

Definition shrincs_fxmss_leaf_commit_queries P a b d :=
  wcommitq (shrincs_fxmss_leaf_params P a b d).
Definition shrincs_fxmss_leaf_pre_queries P a b d :=
  wpreq (shrincs_fxmss_leaf_params P a b d).
Definition shrincs_fxmss_leaf_tcr_decision P a b d :=
  wtcr_dec (shrincs_fxmss_leaf_params P a b d).
Definition shrincs_fxmss_leaf_pre_decision P a b d :=
  wpre_dec (shrincs_fxmss_leaf_params P a b d).

(* ------------------------------------------------------------------ *)
(** ** Operational tree model *)

#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.

Section Scheme.
Context (P : shrincs_fxmss_params).

Fixpoint shrincs_fxmss_node_at (fuel : nat) (keys : shrincs_fxmss_coord -> seq (bytes
  16)) (node_index : UInt64)
    (node_height : UInt8) (pk_seed : Bytes 16) (tree_balanced : bool)
    (tree_depth : UInt8) : option (Bytes 16) :=
  if fuel is fuel'.+1 then
    let height := Z.to_nat (wunsigned node_height) in
    let node_depth := FXMSS_HEIGHT - height in
    if (node_depth == Z.to_nat (wunsigned tree_depth)) ||
       (~~ tree_balanced && (node_index == uint U64 1)) then
      Some (shrincs_fxmss_leaf_pubkey P (node_height, node_index) tree_balanced
        tree_depth
        pk_seed (keys (node_height, node_index)))
    else if (if tree_balanced then node_depth < Z.to_nat (wunsigned tree_depth)
             else node_index == uint U64 0) then
      let lchild_index := Z.mul 2 (wunsigned node_index) in
      if (0 < height) && Z.ltb (Z.add lchild_index 1) (Z.pow 2 64) then
        let child_height := uint U8 (height - 1) in
        if shrincs_fxmss_node_at fuel' keys (wrepr U64 lchild_index) child_height
             pk_seed tree_balanced tree_depth is Some lchild then
          if shrincs_fxmss_node_at fuel' keys (wrepr U64 (Z.add lchild_index 1)) child_height
               pk_seed tree_balanced tree_depth is Some rchild then
            Some (shrincs_fxmss_hash_node P pk_seed (node_height, node_index) lchild
              rchild)
          else None
        else None
      else None
    else None
  else None.

Definition shrincs_fxmss_node (keys : shrincs_fxmss_coord -> seq (bytes 16)) (node_index
  : UInt64) (node_height : UInt8)
    (pk_seed : Bytes 16) (tree_balanced : bool) (tree_depth : UInt8) : option (Bytes 16) :=
  shrincs_fxmss_node_at (Z.to_nat (wunsigned node_height)).+1
    keys node_index node_height pk_seed tree_balanced tree_depth.

(* Authentication siblings are appended bottom-up. *)
Definition shrincs_fxmss_sign (message_digest : Bytes 32) (keys : shrincs_fxmss_coord ->
  seq (bytes 16))
    (leaf_index : UInt64) (leaf_height : UInt8) (pk_seed : Bytes 16)
    (tree_balanced : bool) (tree_depth : UInt8) : option (seq UInt8) :=
  let height := Z.to_nat (wunsigned leaf_height) in
  let leaf_depth := FXMSS_HEIGHT - height in
  if (if tree_balanced then leaf_depth == Z.to_nat (wunsigned tree_depth)
      else (leaf_index == uint U64 1) || (leaf_depth == Z.to_nat (wunsigned tree_depth))) then
    if shrincs_fxmss_leaf_sign P (leaf_height, leaf_index) tree_balanced tree_depth
         pk_seed (keys (leaf_height, leaf_index)) message_digest is Some sig then
      foldl (fun sig j =>
        if sig is Some sig then
          let sibling_index := Z.lxor (Z.div (wunsigned leaf_index) (Z.pow 2 (Z.of_nat j))) 1 in
          let sibling_height := height + j in
          if Z.ltb sibling_index (Z.pow 2 64) && (sibling_height < 256) then
            if shrincs_fxmss_node keys (wrepr U64 sibling_index) (uint U8 sibling_height)
                 pk_seed tree_balanced tree_depth is Some sibling then
              Some (sig ++ sibling)
            else None
          else None
        else None) (Some (tval sig)) (range 0 leaf_depth)
    else None
  else None.

(* The exact length check precedes every padded slice. *)
Definition shrincs_fxmss_recover (leaf_index : UInt64) (leaf_height : UInt8)
    (signature : seq UInt8) (message_digest : Bytes 32) (pk_seed : Bytes 16)
    : option (Bytes 16) :=
  let height := Z.to_nat (wunsigned leaf_height) in
  let leaf_depth := FXMSS_HEIGHT - height in
  if (size signature == 2 + WOTS_C_CHAINS_SIZE + leaf_depth * 16) &&
     Z.ltb (wunsigned leaf_index) (Z.pow 2 (Z.of_nat (minn 64 leaf_depth))) then
    let wots_sig := slice signature 0 (2 + WOTS_C_CHAINS_SIZE) in
    let xmss_auth := drop (2 + WOTS_C_CHAINS_SIZE) signature in
    if shrincs_fxmss_leaf_recover P (leaf_height, leaf_index) false (uint U8 0)
         pk_seed message_digest wots_sig
      is Some node then
      Some (foldl (fun (node : Bytes 16) k =>
        let parent := (uint U8 (height + k + 1),
          wrepr U64 (Z.div (wunsigned leaf_index) (Z.pow 2 (Z.of_nat (k + 1))))) in
        let sibling := slice xmss_auth (k * 16) 16 in
        if Z.eqb (Z.modulo (Z.div (wunsigned leaf_index) (Z.pow 2 (Z.of_nat k))) 2) 1 then
          shrincs_fxmss_hash_node P pk_seed parent sibling node
        else shrincs_fxmss_hash_node P pk_seed parent node sibling) node (range 0
          leaf_depth))
    else None
  else None.

Definition shrincs_fxmss_verify (pp root : bytes 16) (a : shrincs_fxmss_coord)
    (signature : seq UInt8) (m : bytes 32) : bool :=
  shrincs_fxmss_recover a.2 a.1 signature m pp == Some root.

Definition shrincs_fxmss_derived_keys pp k b d :
    shrincs_fxmss_coord -> seq (bytes 16) :=
  fun a => shrincs_fxmss_leaf_keys P a b d pp k.

End Scheme.
