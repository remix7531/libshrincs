(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.repro.games

    Sequential reprogramming interfaces. The simulator consumes the next
    full leaf coordinate before REPRO and reads its digest back with QUERY.
    Invalid messages and exhausted schedules return None after logging the
    attempt. HASH is independent of GEN. The experiment bit is used only
    after the complete forgery computation, including its oracle query. *)

From Shrincs.internal.ssprove.lib Require Import
  prelude toolkit.ro_plus toolkit.reprogram_sep.
From Shrincs Require Import spec schemes.
From Shrincs.internal.ssprove.fxmss Require Import
  params shape scheme games bound.reprogramming.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section Reprogramming.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Definition repro_gen_body (setup : shrincs_fxmss_setup) : raw_code (bytes 48) :=
  sto ← get shrincs_fxmss_st_loc ;;
  #assert ~~ isSome sto ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
  pp ← shrincs_fxmss_public_seed_dist P ;;
  ks ← shrincs_fxmss_secret_dist P ;;
  kp ← shrincs_fxmss_secret_dist P ;;
  kt ← shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1) ;;
  sd ← ret (emptym : shrincs_fxmss_digest_table) ;;
  let st0 := ((pp, setup.2, zeros 16), setup.1) in
  let keys := shrincs_fxmss_lookup_keys P true st0 ks kt in
  let ro := shrincs_fxmss_node P keys (uint U64 0) (uint U8 255)
      pp setup.1.1 (uint U8 setup.1.2) in
  #assert isSome ro ;;
  let root := odflt (zeros 16) ro in
  #put shrincs_fxmss_st_loc := Some ((pp, setup.2, root), setup.1) ;;
  #put shrincs_fxmss_ks_loc := Some ks ;;
  #put shrincs_fxmss_kp_loc := Some kp ;;
  #put shrincs_fxmss_keys_loc := kt ;;
  #put shrincs_fxmss_sd_loc := sd ;;
  ret [tuple of pp ++ setup.2 ++ root].

Definition repro_sign_body
    (draw : repro_suffix -> raw_code (bytes 16 × bytes 32))
    (cm : shrincs_fxmss_message) : raw_code ('option shrincs_fxmss_bytes) :=
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
        kp ← getSome shrincs_fxmss_kp_loc ;;
        kt ← get shrincs_fxmss_keys_loc ;;
        let pp := st.1.1.1 in
        let bm := shrincs_fxmss_bound_message cm in
        rt ← get shrincs_fxmss_rt_loc ;;
        rm ← draw ((pp, st.1.2), (a, bm)) ;;
        let r := rm.1 in
        let md := rm.2 in
        #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
        let keys := shrincs_fxmss_lookup_keys P true st ks kt in
        match shrincs_fxmss_sign P md keys a.2 a.1 pp
            st.2.1 (uint U8 st.2.2) with
        | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
        | None => ret None
        end
    end
  else ret None.

Definition repro_sample (x : repro_suffix) : raw_code (bytes 16 × bytes 32) :=
  r ← shrincs_fxmss_secret_dist P ;;
  md ← shrincs_fxmss_digest_dist P ;;
  mp ← get shrincs_fxmss_rom_loc ;;
  #put shrincs_fxmss_rom_loc := setm mp (r, x) md ;;
  ret (r, md).

Definition repro_sample_call (x : repro_suffix) :
    raw_code (bytes 16 × bytes 32) :=
  r ← call [ REPRO ] : { repro_suffix ~> bytes 16 } x ;;
  md ← call [ QUERY ] : { shrincs_fxmss_hmsg_input ~> bytes 32 } (r, x) ;;
  ret (r, md).

Definition repro_query (x : shrincs_fxmss_hmsg_input) : raw_code (bytes 32) :=
  call [ QUERY ] : { shrincs_fxmss_hmsg_input ~> bytes 32 } x.

Definition repro_hash_body (query : shrincs_fxmss_hmsg_input -> raw_code (bytes 32))
    (x : shrincs_fxmss_hmsg_input) : raw_code ('option (bytes 32)) :=
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  hc ← get shrincs_fxmss_hcnt_loc ;;
  #assert hc < shrincs_fxmss_hash_budget Q ;;
  #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
  if Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111) then
    md ← query x ;; ret (Some md)
  else ret None.

Definition repro_forge_body (query : shrincs_fxmss_hmsg_input -> raw_code (bytes 32))
    (cm : shrincs_fxmss_message) (sg : shrincs_fxmss_bytes) : raw_code 'bool :=
  st ← getSome shrincs_fxmss_st_loc ;;
  done ← get shrincs_fxmss_done_loc ;;
  #assert ~~ done ;;
  #put shrincs_fxmss_done_loc := true ;;
  lg ← get shrincs_fxmss_log_loc ;;
  kt ← get shrincs_fxmss_keys_loc ;;
  sd ← get shrincs_fxmss_sd_loc ;;
  rt ← get shrincs_fxmss_rt_loc ;;
  verdict ← (if shrincs_fxmss_message_valid cm then
      match shrincs_sf_parse sg with
      | Some (h, r, i, fsig) =>
          let a := (h, i) in
          let pp := st.1.1.1 in
          let bm := shrincs_fxmss_bound_message cm in
          md ← query (r, ((pp, st.1.2), (a, bm))) ;;
          ret (shrincs_fxmss_verify P pp st.1.2 a fsig md &&
            (cm \notin lg) &&
            true &&
            true)
      | None => ret false
      end
    else ret false) ;;
  ret verdict.

#[export] Instance repro_gen_valid (I : Interface) setup :
  ValidCode shrincs_fxmss_locs I (repro_gen_body setup).
Proof.
rewrite /repro_gen_body.
ssprove_valid.
exact: shrincs_fxmss_sample_keys_valid.
Qed.

#[export] Instance repro_sign_valid (I : Interface) draw
    (vs : forall x, ValidCode shrincs_fxmss_locs I (draw x)) cm :
  ValidCode shrincs_fxmss_locs I (repro_sign_body draw cm).
Proof.
rewrite /repro_sign_body.
ssprove_valid.
Qed.

#[export] Instance repro_sample_valid (I : Interface) x :
  ValidCode shrincs_fxmss_locs I (repro_sample x).
Proof. rewrite /repro_sample. ssprove_valid. Qed.

#[export] Instance repro_sample_call_valid x :
  ValidCode shrincs_fxmss_locs repro_interface (repro_sample_call x).
Proof. rewrite /repro_sample_call /repro_interface /I_RO. ssprove_valid. Qed.

#[export] Instance repro_query_valid x :
  ValidCode shrincs_fxmss_locs repro_interface (repro_query x).
Proof. rewrite /repro_query /repro_interface /I_RO. ssprove_valid. Qed.

#[export] Instance repro_hash_valid (I : Interface) query
    (vq : forall x, ValidCode shrincs_fxmss_locs I (query x)) x :
  ValidCode shrincs_fxmss_locs I (repro_hash_body query x).
Proof. rewrite /repro_hash_body. ssprove_valid. Qed.

#[export] Instance repro_forge_valid (I : Interface) query
    (vq : forall x, ValidCode shrincs_fxmss_locs I (query x)) cm sg :
  ValidCode shrincs_fxmss_locs I (repro_forge_body query cm sg).
Proof. rewrite /repro_forge_body. ssprove_valid. Qed.

Definition G_forge_reprogrammed (bit : bool) : game I_forge :=
  [package shrincs_fxmss_locs;
    [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
      repro_gen_body setup
    };
    [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
      (cm) {
      repro_sign_body repro_sample cm
    };
    [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
      repro_hash_body (shrincs_fxmss_lookup P) x
    };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      } '(cm, sg) {
      verdict ← repro_forge_body (shrincs_fxmss_lookup P) cm sg ;;
      ret (bit && verdict)
    }
  ].

Definition R_reprogram (bit : bool) : package repro_interface I_forge :=
  [package shrincs_fxmss_locs;
    [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
      repro_gen_body setup
    };
    [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
      (cm) {
      repro_sign_body repro_sample_call cm
    };
    [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
      repro_hash_body repro_query x
    };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      } '(cm, sg) {
      verdict ← repro_forge_body repro_query cm sg ;;
      ret (bit && verdict)
    }
  ].

Lemma repro_gen_eq bit setup :
  repro_gen_body setup =
    resolve (G_forge_randomized P Q bit) (shrincs_fxmss_op_gen, (shrincs_fxmss_setup,
      bytes 48)) setup.
Proof. by rewrite /G_forge_randomized /G_forge /resolve /= coerce_kleisliE. Qed.

Lemma repro_hash_eq bit x :
  repro_hash_body (shrincs_fxmss_lookup P) x =
    resolve (G_forge_randomized P Q bit)
      (shrincs_fxmss_op_hash, (shrincs_fxmss_hmsg_input, 'option (bytes 32))) x.
Proof. by rewrite /G_forge_randomized /G_forge /resolve /= coerce_kleisliE. Qed.

Lemma repro_forge_eq cm sg :
  repro_forge_body (shrincs_fxmss_lookup P) cm sg =
    shrincs_fxmss_forge_body P false (fun _ _ _ _ _ => true) cm sg.
Proof. by []. Qed.

End Reprogramming.
