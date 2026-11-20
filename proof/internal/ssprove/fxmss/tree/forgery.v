(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.tree.forgery

    Digest-filtered experiments whose pure filter receives the complete parsed
    signature, including its authentication path. Setup, signing and HASH
    are the preassigned experiment's oracles. All protocol reads and digest
    sampling precede the security bit. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import params shape scheme games
  digest.filtered.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_full_keep :=
  shrincs_fxmss_state -> shrincs_fxmss_key_table -> shrincs_fxmss_coord -> bytes 32 ->
    shrincs_fxmss_bytes -> bool.

Definition shrincs_fxmss_lift_keep (keep : shrincs_fxmss_keep) : shrincs_fxmss_full_keep
  :=
  fun st kt a md sg => keep st kt a md
    (slice sg 0 (2 + WOTS_C_CHAINS_SIZE)).

Section Games.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Definition shrincs_fxmss_full_forge_body (keep : shrincs_fxmss_full_keep)
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
          md ← shrincs_fxmss_lookup P (r, ((pp, st.1.2), (a, bm))) ;;
          ret (shrincs_fxmss_verify P pp st.1.2 a fsig md &&
            (cm \notin lg) &&
            (~~ ((md \in codomm sd) &&
               (getm rt (a, bm) != Some r))) &&
            keep st kt a md fsig)
      | None => ret false
      end
    else ret false) ;;
  ret verdict.

#[export] Instance shrincs_fxmss_full_forge_body_valid (I : Interface) keep cm sg :
  ValidCode shrincs_fxmss_locs I (shrincs_fxmss_full_forge_body keep cm sg).
Proof.
rewrite /shrincs_fxmss_full_forge_body.
ssprove_valid.
exact: shrincs_fxmss_lookup_valid.
Qed.

(** The full-signature filter runs on the pure verdict before [bit]. *)
Definition G_forge_full_signature (keep : shrincs_fxmss_full_keep)
    (bit : bool) : game I_forge :=
  [package shrincs_fxmss_locs;
    [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 } (setup) {
      sto ← get shrincs_fxmss_st_loc ;;
      #assert ~~ isSome sto ;;
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      #assert shrincs_fxmss_structure_legal setup.1.1 setup.1.2 ;;
      pp ← shrincs_fxmss_public_seed_dist P ;;
      ks ← shrincs_fxmss_secret_dist P ;;
      kp ← shrincs_fxmss_secret_dist P ;;
      kt ← shrincs_fxmss_sample_keys P (shrincs_fxmss_schedule setup.1) ;;
      sd ← shrincs_fxmss_sample_digests P (shrincs_fxmss_schedule setup.1) ;;
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
      ret [tuple of pp ++ setup.2 ++ root]
    };
    [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes }
      (cm) {
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
            ro ← (match getm rt (a, bm) with
                  | Some r => ret (Some r)
                  | None => r ← shrincs_fxmss_secret_dist P ;; ret (Some r)
                  end) ;;
            match ro with
            | None => ret None
            | Some r =>
                #put shrincs_fxmss_rt_loc := setm rt (a, bm) r ;;
                let x := (r, ((pp, st.1.2), (a, bm))) in
                md ← (sd ← get shrincs_fxmss_sd_loc ;;
                      md ← (match getm sd a with
                            | Some md => ret md
                            | None => md ← shrincs_fxmss_digest_dist P ;; ret md
                            end) ;;
                      mp ← get shrincs_fxmss_rom_loc ;;
                      #put shrincs_fxmss_rom_loc := setm mp x md ;;
                      ret md) ;;
                let keys := shrincs_fxmss_lookup_keys P true st ks kt in
                match shrincs_fxmss_sign P md keys a.2 a.1 pp
                        st.2.1 (uint U8 st.2.2) with
                | Some sg => ret (shrincs_sf_encode a.1 r a.2 sg)
                | None => ret None
                end
            end
        end
      else ret None
    };
    [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) } (x) {
      done ← get shrincs_fxmss_done_loc ;;
      #assert ~~ done ;;
      hc ← get shrincs_fxmss_hcnt_loc ;;
      #assert hc < shrincs_fxmss_hash_budget Q ;;
      #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
      if Z.leb (Z.of_nat (size x.2.2.2)) (Z.sub (Z.pow 2 61) 111) then
        md ← shrincs_fxmss_lookup P x ;; ret (Some md)
      else ret None
    };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      } '(cm, sg) {
      verdict ← shrincs_fxmss_full_forge_body keep cm sg ;;
      ret (bit && verdict)
    }
  ].

Lemma forge_full_signature_lift_eq (keep : shrincs_fxmss_keep) bit :
  G_forge_full_signature (shrincs_fxmss_lift_keep keep) bit = G_forge_filtered P Q keep
    bit.
Proof.
apply: package_ext => x; reflexivity.
Qed.

Lemma forge_full_signature_digest_filtered_eq bit :
  G_forge_full_signature (fun _ _ _ _ _ => true) bit = G_forge_digest_filtered P Q bit.
Proof. exact: forge_full_signature_lift_eq. Qed.

End Games.
