(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.games

    Internal hybrids: one adversarial structure and partner, sequential
    signing with an all-attempt log, and one shared Hmsg table. G_forge_keyed derives
    chain starts; G_forge_sampledkey samples them; G_forge_randomized also samples
      message randomizers.
    All protocol reads, assertions and digest sampling precede the final bit.
    Operations and locations occupy 1300..1399. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.sample_seq.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import params shape scheme.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope nat_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_op_gen : nat := 1300.
Definition shrincs_fxmss_op_sign : nat := 1301.
Definition shrincs_fxmss_op_hash : nat := 1302.
Definition shrincs_fxmss_op_forge : nat := 1303.

Definition I_forge :=
  [interface
    [ shrincs_fxmss_op_gen ] : { shrincs_fxmss_setup ~> bytes 48 };
    [ shrincs_fxmss_op_sign ] : { shrincs_fxmss_message ~> 'option shrincs_fxmss_bytes
      };
    [ shrincs_fxmss_op_hash ] : { shrincs_fxmss_hmsg_input ~> 'option (bytes 32) };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      }
  ].

Definition shrincs_fxmss_key_table : choice_type := chMap shrincs_fxmss_coord ('list
  (bytes 16)).
Definition shrincs_fxmss_digest_table : choice_type := chMap shrincs_fxmss_coord (bytes
  32).
Definition shrincs_fxmss_state : choice_type :=
  ((bytes 16 × bytes 16) × bytes 16) × shrincs_fxmss_structure.
Definition shrincs_fxmss_st_loc := mkloc 1300 (None : option shrincs_fxmss_state).
Definition shrincs_fxmss_ks_loc := mkloc 1301 (None : option (bytes 16)).
Definition shrincs_fxmss_kp_loc := mkloc 1302 (None : option (bytes 16)).
Definition shrincs_fxmss_keys_loc := mkloc 1303 (emptym : shrincs_fxmss_key_table).
Definition shrincs_fxmss_log_loc := mkloc 1304 ([::] : seq shrincs_fxmss_message).
Definition shrincs_fxmss_scnt_loc := mkloc 1305 0.
Definition shrincs_fxmss_hcnt_loc := mkloc 1306 0.
Definition shrincs_fxmss_next_loc := mkloc 1307 0.
Definition shrincs_fxmss_done_loc := mkloc 1308 false.
Definition shrincs_fxmss_rom_loc := mkloc 1309
  (emptym : chMap shrincs_fxmss_hmsg_input (bytes 32)).
Definition shrincs_fxmss_sd_loc := mkloc 1310 (emptym : shrincs_fxmss_digest_table).
Definition shrincs_fxmss_rt_loc := mkloc 1311
  (emptym : chMap (shrincs_fxmss_coord × shrincs_fxmss_bytes) (bytes 16)).

Definition shrincs_fxmss_locs : Locations :=
  [fmap shrincs_fxmss_st_loc; shrincs_fxmss_ks_loc; shrincs_fxmss_kp_loc;
    shrincs_fxmss_keys_loc; shrincs_fxmss_log_loc;
        shrincs_fxmss_scnt_loc; shrincs_fxmss_hcnt_loc; shrincs_fxmss_next_loc;
          shrincs_fxmss_done_loc;
        shrincs_fxmss_rom_loc; shrincs_fxmss_sd_loc; shrincs_fxmss_rt_loc].

Definition shrincs_fxmss_schedule (sp : shrincs_fxmss_structure) : seq
  shrincs_fxmss_coord :=
  pmap (shrincs_fxmss_select_leaf sp.1 sp.2)
    (iota 0 (shrincs_fxmss_leaf_count sp.1 sp.2)).

Definition shrincs_fxmss_lookup_keys (P : shrincs_fxmss_params) (random : bool) (st :
  shrincs_fxmss_state)
    (k : bytes 16) (kt : shrincs_fxmss_key_table) : shrincs_fxmss_coord -> seq (bytes
      16) :=
  if random then fun a => odflt [::] (getm kt a)
  else shrincs_fxmss_derived_keys P st.1.1.1 k st.2.1 (uint U8 st.2.2).

Definition shrincs_fxmss_keep :=
  shrincs_fxmss_state -> shrincs_fxmss_key_table -> shrincs_fxmss_coord -> bytes 32 ->
    bytes (2 + WOTS_C_CHAINS_SIZE) -> bool.

Section Games.
Context (P : shrincs_fxmss_params) (Q : shrincs_fxmss_resources).

Fixpoint shrincs_fxmss_sample_keys (as_ : seq shrincs_fxmss_coord) : raw_code
  shrincs_fxmss_key_table :=
  match as_ with
  | [::] => ret emptym
  | a :: rest =>
      xs ← sample_seq (shrincs_fxmss_secret_dist P) wots_c_chain_count ;;
      kt ← shrincs_fxmss_sample_keys rest ;;
      ret (setm kt a xs)
  end.

#[export] Instance shrincs_fxmss_sample_keys_valid (L : Locations) (I : Interface) as_ :
  ValidCode L I (shrincs_fxmss_sample_keys as_).
Proof.
elim: as_ => [|a rest ih].
- apply valid_ret.
- eapply valid_bind; first exact: sample_seq_valid.
  move=> xs.
  eapply valid_bind; first exact: ih.
  move=> kt; apply valid_ret.
Qed.

Fixpoint shrincs_fxmss_sample_digests (as_ : seq shrincs_fxmss_coord) : raw_code
  shrincs_fxmss_digest_table :=
  match as_ with
  | [::] => ret emptym
  | a :: rest =>
      md ← shrincs_fxmss_digest_dist P ;;
      sd ← shrincs_fxmss_sample_digests rest ;;
      ret (setm sd a md)
  end.

#[export] Instance shrincs_fxmss_sample_digests_valid (L : Locations) (I : Interface)
  as_ :
  ValidCode L I (shrincs_fxmss_sample_digests as_).
Proof.
elim: as_ => [|a rest ih].
- apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid.
  move=> md.
  eapply valid_bind; first exact: ih.
  move=> sd; apply valid_ret.
Qed.

Definition shrincs_fxmss_lookup (x : shrincs_fxmss_hmsg_input) : raw_code (bytes 32) :=
  mp ← get shrincs_fxmss_rom_loc ;;
  match getm mp x with
  | Some md => ret md
  | None =>
      md ← shrincs_fxmss_digest_dist P ;;
      #put shrincs_fxmss_rom_loc := setm mp x md ;;
      ret md
  end.

#[export] Instance shrincs_fxmss_lookup_valid (I : Interface) x :
  ValidCode shrincs_fxmss_locs I (shrincs_fxmss_lookup x).
Proof.
rewrite /shrincs_fxmss_lookup.
eapply valid_getr; first by fmap_solve.
move=> mp.
case: (getm mp x) => [md|]; first apply valid_ret.
eapply valid_bind; first by eapply valid_scheme, prog_valid.
move=> md.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

Definition shrincs_fxmss_forge_body (preassigned : bool) (keep : shrincs_fxmss_keep)
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
          md ← shrincs_fxmss_lookup (r, ((pp, st.1.2), (a, bm))) ;;
          ret (shrincs_fxmss_verify P pp st.1.2 a fsig md &&
            (cm \notin lg) &&
            (if preassigned then ~~ ((md \in codomm sd) &&
               (getm rt (a, bm) != Some r)) else true) &&
            keep st kt a md (slice fsig 0 (2 + WOTS_C_CHAINS_SIZE)))
      | None => ret false
      end
    else ret false) ;;
  ret verdict.

#[export] Instance shrincs_fxmss_forge_body_valid (I : Interface) preassigned keep cm sg
  :
  ValidCode shrincs_fxmss_locs I (shrincs_fxmss_forge_body preassigned keep cm sg).
Proof.
rewrite /shrincs_fxmss_forge_body.
ssprove_valid.
exact: shrincs_fxmss_lookup_valid.
Qed.

(** [random_keys] and [random_r] select hybrids, independently of [bit].
    [preassigned] preassigns one digest per leaf and reprograms signing queries.
    The keep predicate only filters a pure, already-computed verdict. *)
Definition G_forge (random_keys random_r preassigned : bool) (keep : shrincs_fxmss_keep)
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
      kt ← (if random_keys then shrincs_fxmss_sample_keys (shrincs_fxmss_schedule
        setup.1)
             else ret emptym) ;;
      sd ← (if preassigned then shrincs_fxmss_sample_digests (shrincs_fxmss_schedule
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
                      else shrincs_fxmss_lookup x) ;;
                let keys := shrincs_fxmss_lookup_keys P random_keys st ks kt in
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
        md ← shrincs_fxmss_lookup x ;; ret (Some md)
      else ret None
    };
    [ shrincs_fxmss_op_forge ] : { shrincs_fxmss_message × shrincs_fxmss_bytes ~> 'bool
      } '(cm, sg) {
      verdict ← shrincs_fxmss_forge_body preassigned keep cm sg ;;
      ret (bit && verdict)
    }
  ].

Definition shrincs_fxmss_forge_op : opsig :=
  (shrincs_fxmss_op_forge, (shrincs_fxmss_message × shrincs_fxmss_bytes, 'bool)).

Lemma resolve_forge random_keys random_r preassigned keep bit cm sg :
  resolve (G_forge random_keys random_r preassigned keep bit) shrincs_fxmss_forge_op
    (cm, sg) =
    (verdict ← shrincs_fxmss_forge_body preassigned keep cm sg ;; ret (bit && verdict)).
Proof. by rewrite /G_forge /resolve /= coerce_kleisliE. Qed.

Definition G_forge_keyed := G_forge false false false (fun _ _ _ _ _ => true).
Definition G_forge_sampledkey := G_forge true false false (fun _ _ _ _ _ => true).
Definition G_forge_randomized := G_forge true true false (fun _ _ _ _ _ => true).

End Games.
