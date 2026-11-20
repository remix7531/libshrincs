(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.prf.reduction

    The chain-start and message-randomizer reduction packages expose the PRF
    queries and their oracle resolutions. *)

From Shrincs.internal.ssprove.lib Require Import prelude games.prf_memo.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape scheme games instance prf.inputs.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import ZArith.

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF reductions *)

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint shrincs_fxmss_prf_derive_leaf pp a b d (j n : nat) :
    raw_code ('list (bytes 16)) :=
  match n with
  | 0 => ret [::]
  | n'.+1 =>
      x ← (call [ MQUERY ] : { kh_M shrincs_khf_prf ~> bytes 16 }
        (shrincs_fxmss_prf_input pp a b d j)) ;;
      xs ← shrincs_fxmss_prf_derive_leaf pp a b d j.+1 n' ;;
      ret (x :: xs)
  end.

Lemma shrincs_fxmss_prf_derive_leaf_valid L pp a b d j n :
  ValidCode L (I_PRF_memo shrincs_khf_prf)
    (shrincs_fxmss_prf_derive_leaf pp a b d j n).
Proof.
elim: n j => [|n ih] j; first apply valid_ret.
cbn [shrincs_fxmss_prf_derive_leaf].
eapply valid_opr; first by fmap_solve.
move=> x.
eapply valid_bind; first exact: ih.
move=> xs; apply valid_ret.
Qed.
#[export] Existing Instance shrincs_fxmss_prf_derive_leaf_valid.

Fixpoint shrincs_fxmss_prf_derive_table pp b d (as_ : seq shrincs_fxmss_coord) :
    raw_code shrincs_fxmss_key_table :=
  match as_ with
  | [::] => ret emptym
  | a :: rest =>
      xs ← shrincs_fxmss_prf_derive_leaf pp a b d 0 wots_c_chain_count ;;
      kt ← shrincs_fxmss_prf_derive_table pp b d rest ;;
      ret (setm kt a xs)
  end.

Lemma shrincs_fxmss_prf_derive_table_valid L pp b d as_ :
  ValidCode L (I_PRF_memo shrincs_khf_prf)
    (shrincs_fxmss_prf_derive_table pp b d as_).
Proof.
elim: as_ => [|a rest ih]; first apply valid_ret.
cbn [shrincs_fxmss_prf_derive_table].
eapply valid_bind; first exact: shrincs_fxmss_prf_derive_leaf_valid.
move=> xs.
eapply valid_bind; first exact: ih.
move=> kt; apply valid_ret.
Qed.
#[export] Existing Instance shrincs_fxmss_prf_derive_table_valid.

Lemma shrincs_fxmss_prf_local_valid Q rr bit I op x
    (hop : fhas I_forge op) :
  ValidCode shrincs_fxmss_locs I
    (resolve (G_forge shrincs_fxmss_sha256 Q true rr false (fun _ _ _ _ _ => true) bit)
      op
      x).
Proof.
eapply (valid_injectMap (I1 := emptym)); first by fmap_solve.
eapply valid_resolve.
- exact (pack_valid
    (G_forge shrincs_fxmss_sha256 Q true rr false (fun _ _ _ _ _ => true) bit)).
- exact: hop.
Qed.
#[export] Existing Instance shrincs_fxmss_prf_local_valid.

Definition shrincs_fxmss_prf_gen (setup : shrincs_fxmss_setup) : raw_code (bytes 48) :=
  sto ← get shrincs_fxmss_st_loc ;;
  #assert ~~ isSome sto ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
  pp ← dBytes 16 ;;
  _ ← (call [ MQUERY ] : { kh_M shrincs_khf_prf ~> bytes 16 } (shrincs_fxmss_prf_pin
    pp)) ;;
  kp ← dBytes 16 ;;
  kt ← shrincs_fxmss_prf_derive_table pp setup.1.1 (uint U8 setup.1.2)
    (shrincs_fxmss_schedule setup.1) ;;
  let st0 := ((pp, setup.2, zeros 16), setup.1) in
  let keys := shrincs_fxmss_lookup_keys shrincs_fxmss_sha256 true st0 (zeros 16) kt in
  let ro := shrincs_fxmss_node shrincs_fxmss_sha256 keys (uint U64 0) (uint U8 255)
    pp setup.1.1 (uint U8 setup.1.2) in
  #assert isSome ro ;;
  let root := odflt (zeros 16) ro in
  #put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
  #put shrincs_fxmss_ks_loc := Some (zeros 16) ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_keys_loc := kt ;;
  #put shrincs_fxmss_sd_loc := emptym ;;
  ret [tuple of pp ++ setup.2 ++ root].

Lemma shrincs_fxmss_prf_gen_valid setup :
  ValidCode shrincs_fxmss_locs (I_PRF_memo shrincs_khf_prf) (shrincs_fxmss_prf_gen
    setup).
Proof.
rewrite /shrincs_fxmss_prf_gen.
ssprove_valid.
exact: shrincs_fxmss_prf_derive_table_valid.
Qed.
#[export] Existing Instance shrincs_fxmss_prf_gen_valid.

Definition R_prf_memo (Q : shrincs_fxmss_resources) (bit : bool) :
    package (I_PRF_memo shrincs_khf_prf) I_forge.
Proof.
notypeclasses refine [package shrincs_fxmss_locs;
  [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
    shrincs_fxmss_prf_gen setup };
  [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
    (cm) {
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_sign,
      (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm
  };
  [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit)
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x
  };
  [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
    } (x) {
    resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) shrincs_fxmss_forge_op x
  }
].
ssprove_valid.
- exact (shrincs_fxmss_prf_local_valid Q false bit (I_PRF_memo shrincs_khf_prf)
    shrincs_fxmss_forge_op x (ltac:(fmap_solve))).
- exact (shrincs_fxmss_prf_local_valid Q false bit (I_PRF_memo shrincs_khf_prf)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x
      (ltac:(fmap_solve))).
- exact (shrincs_fxmss_prf_local_valid Q false bit (I_PRF_memo shrincs_khf_prf)
    (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) x
      (ltac:(fmap_solve))).
- exact: shrincs_fxmss_prf_gen_valid.
Defined.

Definition R_prf Q bit : nom_package :=
  R_prf_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf (shrincs_fxmss_prf_budget Q).

Definition shrincs_fxmss_prf_msg_gen (setup : shrincs_fxmss_setup) : raw_code (bytes 48)
  :=
  sto ← get shrincs_fxmss_st_loc ;;
  #assert ~~ isSome sto ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
  pp ← dBytes 16 ;;
  ks ← dBytes 16 ;;
  _ ← (call [ MQUERY ] : { kh_M shrincs_khf_prf_msg ~> bytes 16 }
    shrincs_fxmss_prf_msg_pin) ;;
  kt ← shrincs_fxmss_sample_keys shrincs_fxmss_sha256 (shrincs_fxmss_schedule setup.1)
    ;;
  let st0 := ((pp, setup.2, zeros 16), setup.1) in
  let keys := shrincs_fxmss_lookup_keys shrincs_fxmss_sha256 true st0 ks kt in
  let ro := shrincs_fxmss_node shrincs_fxmss_sha256 keys (uint U64 0) (uint U8 255)
    pp setup.1.1 (uint U8 setup.1.2) in
  #assert isSome ro ;;
  let root := odflt (zeros 16) ro in
  #put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some (zeros 16) ;;
  #put shrincs_fxmss_keys_loc := kt ;;
  #put shrincs_fxmss_sd_loc := emptym ;;
  ret [tuple of pp ++ setup.2 ++ root].

Lemma shrincs_fxmss_prf_msg_gen_valid setup :
  ValidCode shrincs_fxmss_locs (I_PRF_memo shrincs_khf_prf_msg)
    (shrincs_fxmss_prf_msg_gen
    setup).
Proof.
rewrite /shrincs_fxmss_prf_msg_gen.
ssprove_valid.
exact: shrincs_fxmss_sample_keys_valid.
Qed.
#[export] Existing Instance shrincs_fxmss_prf_msg_gen_valid.

Definition shrincs_fxmss_prf_msg_sign Q (cm : shrincs_fxmss_message) : raw_code ('option
  shrincs_fxmss_bytes) :=
  st ← getSome shrincs_fxmss_st_loc ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  sc ← get shrincs_fxmss_scnt_loc ;;
  #assert sc < shrincs_fxmss_sign_budget Q ;;
  lg ← get shrincs_fxmss_log_loc ;;
  #put shrincs_fxmss_scnt_loc := sc.+1 ;;
  #put shrincs_fxmss_log_loc := cm :: lg ;;
  if shrincs_fxmss_message_valid cm then
    q ← get shrincs_fxmss_next_loc ;;
    match shrincs_fxmss_select_leaf st.2.1 st.2.2 q with
    | None => ret None
    | Some a =>
        #put shrincs_fxmss_next_loc := q.+1 ;;
        ks ← getSome shrincs_fxmss_ks_loc ;;
        _ ← getSome shrincs_fxmss_kp_loc ;;
        kt ← get shrincs_fxmss_keys_loc ;;
        let pp := st.1.1.1 in
        let bm := shrincs_fxmss_bound_message cm in
        rt ← get shrincs_fxmss_rt_loc ;;
        r ← (call [ MQUERY ] : { kh_M shrincs_khf_prf_msg ~> bytes 16 }
          (shrincs_fxmss_prf_msg_input pp a bm)) ;;
        #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
        let x := (r, ((pp, st.1.2), (a, bm))) in
        md ← shrincs_fxmss_lookup shrincs_fxmss_sha256 x ;;
        let keys := shrincs_fxmss_lookup_keys shrincs_fxmss_sha256 true st ks kt in
        match shrincs_fxmss_sign shrincs_fxmss_sha256 md keys a.2 a.1 pp
                st.2.1 (uint U8 st.2.2) with
        | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
        | None => ret None
        end
    end
  else ret None.

Lemma shrincs_fxmss_prf_msg_sign_valid Q cm :
  ValidCode shrincs_fxmss_locs (I_PRF_memo shrincs_khf_prf_msg)
    (shrincs_fxmss_prf_msg_sign
    Q cm).
Proof.
rewrite /shrincs_fxmss_prf_msg_sign.
ssprove_valid.
exact: shrincs_fxmss_lookup_valid.
Qed.
#[export] Existing Instance shrincs_fxmss_prf_msg_sign_valid.

Definition R_prf_msg_memo (Q : shrincs_fxmss_resources) (bit : bool) :
    package (I_PRF_memo shrincs_khf_prf_msg) I_forge.
Proof.
notypeclasses refine [package shrincs_fxmss_locs;
  [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
    shrincs_fxmss_prf_msg_gen setup };
  [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
    (cm) { shrincs_fxmss_prf_msg_sign Q cm };
  [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
    resolve (G_forge_randomized shrincs_fxmss_sha256 Q bit)
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x
  };
  [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
    } (x) {
    resolve (G_forge_randomized shrincs_fxmss_sha256 Q bit) shrincs_fxmss_forge_op x
  }
].
ssprove_valid.
- exact (shrincs_fxmss_prf_local_valid Q true bit (I_PRF_memo shrincs_khf_prf_msg)
    shrincs_fxmss_forge_op x (ltac:(fmap_solve))).
- exact (shrincs_fxmss_prf_local_valid Q true bit (I_PRF_memo shrincs_khf_prf_msg)
    (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x
      (ltac:(fmap_solve))).
- exact: shrincs_fxmss_prf_msg_sign_valid.
- exact: shrincs_fxmss_prf_msg_gen_valid.
Defined.

Definition R_prf_msg Q bit : nom_package :=
  R_prf_msg_memo Q bit ∘ prf_memo.R_prf_memo shrincs_khf_prf_msg
    (shrincs_fxmss_q_prf_msg Q).

(* ------------------------------------------------------------------ *)
(** ** Chain-start PRF resolve *)

Import Shrincs.internal.ssprove.fxmss.games.
Import PackageNotation.
#[local] Open Scope package_scope.

Lemma resolve_R_prf_gen Q bit arg :
  resolve (R_prf_memo Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) arg
    = shrincs_fxmss_prf_gen arg.
Proof.
by rewrite /R_prf_memo /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_forge_gen P Q random_keys random_r preassigned keep bit setup :
  resolve (G_forge P Q random_keys random_r preassigned keep bit)
    (shrincs_fxmss_op_gen, (shrincs_fxmss_setup, bytes 48)) setup =
  (sto ← get shrincs_fxmss_st_loc ;;
      #assert ~~ isSome sto ;;
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
      pp ← shrincs_fxmss_public_seed_dist P ;;
      ks ← shrincs_fxmss_secret_dist P ;;
      kp ← shrincs_fxmss_secret_dist P ;;
      kt ← (if random_keys then shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule
        setup.1)
             else ret emptym) ;;
      sd ← (if preassigned then shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule
        setup.1)
             else ret emptym) ;;
      let st0 := ((pp, setup.2, zeros 16), setup.1) in
      let keys := shrincs_fxmss_lookup_keys P random_keys st0 ks kt in
      let ro := shrincs_fxmss_node P keys (uint U64 0) (uint U8 255)
          pp setup.1.1 (uint U8 setup.1.2) in
      #assert isSome ro ;;
      let root := odflt (zeros 16) ro in
      #put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
      #put shrincs_fxmss_ks_loc := Some ks ;;
      #put shrincs_fxmss_kp_loc := Some kp ;;
      #put shrincs_fxmss_keys_loc := kt ;;
      #put shrincs_fxmss_sd_loc := sd ;;
      ret [tuple of pp ++ setup.2 ++ root]).
Proof. by rewrite /G_forge /resolve /= coerce_kleisliE. Qed.

Lemma resolve_forge_hash P Q rk rr preassigned keep bit x :
 resolve (G_forge P Q rk rr preassigned keep bit) (shrincs_fxmss_op_hash,
   (shrincs_fxmss_hmsg_input,
   'option (bytes 32))) x =
 (done ← get shrincs_fxmss_done_loc ;;
 #assert ~~ done ;;
 hc ← get shrincs_fxmss_hcnt_loc ;;
 #assert hc < shrincs_fxmss_hash_budget Q ;;
 #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
 if Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111) then
 md ← shrincs_fxmss_lookup P x ;; ret (Some md) else ret None).
Proof.
by rewrite /G_forge /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_R_prf_hash Q bit x :
 resolve (R_prf_memo Q bit) (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option
   (bytes 32))) x =
 resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_hash,
   (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x.
Proof.
by rewrite /R_prf_memo /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_R_prf_forge Q bit x :
 resolve (R_prf_memo Q bit) shrincs_fxmss_forge_op x =
 resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) shrincs_fxmss_forge_op x.
Proof.
by rewrite /R_prf_memo /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_R_prf_sign Q bit x :
 resolve (R_prf_memo Q bit) (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option
   shrincs_fxmss_bytes)) x =
 resolve (G_forge_sampledkey shrincs_fxmss_sha256 Q bit) (shrincs_fxmss_op_sign,
   (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) x.
Proof.
by rewrite /R_prf_memo /resolve /= coerce_kleisliE.
Qed.

Lemma resolve_forge_sign P Q random_keys random_r preassigned keep bit cm :
 resolve (G_forge P Q random_keys random_r preassigned keep bit)
   (shrincs_fxmss_op_sign, (shrincs_fxmss_message, 'option shrincs_fxmss_bytes)) cm =
 (st ← getSome shrincs_fxmss_st_loc ;;
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      sc ← get shrincs_fxmss_scnt_loc ;;
      #assert sc < shrincs_fxmss_sign_budget Q ;;
      lg ← get shrincs_fxmss_log_loc ;;
      #put shrincs_fxmss_scnt_loc := sc.+1 ;;
      #put shrincs_fxmss_log_loc := cm :: lg ;;
      if shrincs_fxmss_message_valid cm then
        q ← get shrincs_fxmss_next_loc ;;
        match shrincs_fxmss_select_leaf st.2.1 st.2.2 q with
        | None => ret None
        | Some a =>
            #put shrincs_fxmss_next_loc := q.+1 ;;
            ks ← getSome shrincs_fxmss_ks_loc ;;
            kp ← getSome shrincs_fxmss_kp_loc ;;
            kt ← get shrincs_fxmss_keys_loc ;;
            let pp := st.1.1.1 in
            let bm := shrincs_fxmss_bound_message cm in
            rt ← get shrincs_fxmss_rt_loc ;;
            ro ← (if random_r then
                    match getm rt (a, bm) with
                    | Some r => ret (Some r)
                    | None => r ← shrincs_fxmss_secret_dist P ;; ret (Some r)
                    end
                  else ret (shrincs_fxmss_prf_msg_eval P kp pp a bm)) ;;
            match ro with
            | None => ret None
            | Some r =>
                #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
                let x := (r, ((pp, st.1.2), (a, bm))) in
                md ← (if preassigned then
                        sd ← get shrincs_fxmss_sd_loc ;;
                        md ← (match getm sd a with
                              | Some md => ret md
                              | None => md ← shrincs_fxmss_digest_dist P ;; ret md
                              end) ;;
                        mp ← get shrincs_fxmss_rom_loc ;;
                        #put shrincs_fxmss_rom_loc := setm mp x md ;;
                        ret md
                      else shrincs_fxmss_lookup P x) ;;
                let keys := shrincs_fxmss_lookup_keys P random_keys st ks kt in
                match shrincs_fxmss_sign P md keys a.2 a.1 pp
                        st.2.1 (uint U8 st.2.2) with
                | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
                | None => ret None
                end
            end
        end
      else ret None).
Proof.
by rewrite /G_forge /resolve /= coerce_kleisliE.
Qed.
