(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.games.stateful_rom

    Generic facts for the public stateful ROM experiment: the canonical
    ideal success is zero, every admitted signing attempt is logged, and
    state is consumed before the digest is read. *)

From Shrincs.internal.ssprove.lib Require Import prelude toolkit.probability.
From Shrincs Require Import games.
From mathcomp Require Import reals.
From mathcomp.experimental_reals Require Import distr realsum.

Import PackageNotation Shrincs.games.stateful_rom GRing.Theory Num.Theory.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.
#[local] Open Scope ring_scope.

(* ------------------------------------------------------------------ *)
(** ** Canonical success probability *)

Lemma sf_bind_zero (T : choice_type) (c : raw_code T)
    (k : T -> raw_code 'bool) h :
  (forall x h', dfst (Pr_code (k x) h') true = 0) ->
  dfst (Pr_code (bind c k) h) true = 0.
Proof.
move=> hk.
rewrite Pr_code_bind dfst_dlet_commut dletE.
rewrite (eq_psum (F2 := fun _ => 0)) ?psum0 //.
by move=> [x h'] /=; rewrite hk mulr0.
Qed.

Lemma sf_forge_false S candidate h :
  dfst (Pr_code (forge_body S false candidate) h) true = 0.
Proof.
unfold forge_body.
apply: sf_bind_zero => verdict h'.
by rewrite dPr_ret dunit1E.
Qed.

Lemma sf_forger_run S LA c vc :
  resolve (val (canonical_forger S LA c vc)) RUN tt = measure S c.
Proof. by rewrite /canonical_forger /resolve /= coerce_kleisliE. Qed.

Lemma sf_resolve_forge S q_s q_h b candidate :
  resolve (val (EUCMA_game S q_s q_h b))
    (mkopsig FORGE (sf_Msg S × sf_Sig S) 'bool) candidate =
  forge_body S b candidate.
Proof. by simplify_linking. Qed.

Lemma sf_measure_false S q_s q_h c h :
  dfst (Pr_code (code_link (measure S c)
    (val (EUCMA_game S q_s q_h false))) h) true = 0.
Proof.
rewrite /measure code_link_bind.
apply: sf_bind_zero => candidate h'.
cbn [code_link].
rewrite bind_ret sf_resolve_forge.
exact: sf_forge_false.
Qed.

Lemma sf_measure_rename S pi c :
  pi ∙ measure S c = measure S (pi ∙ c).
Proof. by rewrite /measure mcode_bind. Qed.

Lemma sf_ideal_zero S q_s q_h LA c vc :
  Pr' (canonical_forger S LA c vc ∘ EUCMA_game S q_s q_h false)%sep true = 0.
Proof.
pose A := (canonical_forger S LA c vc : nom_package).
pose G := (EUCMA_game S q_s q_h false : nom_package).
pose pi := fresh G A.
have hd : disj (pi ∙ A) G by rewrite disjC; exact: fresh_disjoint.
change (Pr' (A ∘ G)%sep true = 0).
rewrite -{1}(@rename_alpha _ A pi).
rewrite /Pr' -(link_sep_link hd) Pr_Pr_code resolve_link.
rewrite -rename_resolve /A sf_forger_run sf_measure_rename.
exact: sf_measure_false.
Qed.

Lemma sf_advantage_success S q_s q_h LA c vc :
  AdvOf (EUCMA_game S q_s q_h) (canonical_forger S LA c vc) =
  Pr' (canonical_forger S LA c vc ∘ EUCMA_game S q_s q_h true)%sep true.
Proof.
by rewrite AdvE (sf_ideal_zero S q_s q_h LA c vc)
subr0 ger0_norm.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Signing state and replay refusal *)

(** Every returning attempt, including None, has logged the external pair. *)
Lemma sf_return_logged (T : choice_type) (v w : T) S cm h h' :
  cm \in get_heap h (sf_log_loc S) ->
  cm \notin get_heap h' (sf_log_loc S) ->
  Pr_code (ret v) h (w,h') = 0.
Proof.
move=> hin hout.
rewrite Pr_code_ret dunit1E.
case: eqP => [he|he] //.
case: he => _ hh.
subst h'.
by move: hout; rewrite hin.
Qed.

Lemma sf_sign_log S q_s cm h response h' :
  cm \notin get_heap h' (sf_log_loc S) ->
  Pr_code (sign_body S q_s cm) h (response,h') = 0.
Proof.
move=> hout.
rewrite /sign_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|];
last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_done_loc);
first by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_scnt_loc < q_s)%N;
last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_put Pr_code_get Pr_code_put.
set h0 := set_heap _ (sf_log_loc S) _.
have hin : cm \in get_heap h0 (sf_log_loc S).
{ by rewrite /h0 get_set_heap_eq inE eqxx. }
case: (sf_message_valid S cm);
last exact: sf_return_logged hin hout.
rewrite Pr_code_put.
set h1 := set_heap h0 (sf_st_loc S) _.
have hin1 : cm \in get_heap h1 (sf_log_loc S).
{ by rewrite /h1 get_set_heap_neq. }
case: (sf_sign_query S _ _) => [x|];
last exact: sf_return_logged hin1 hout.
rewrite /shared_lookup Pr_code_get.
case: (getm (get_heap h1 (sf_rom_loc S)) x) => [md|].
- exact: sf_return_logged hin1 hout.
- fold (@bind).
rewrite bind_assoc.
rewrite (Pr_code_fst (prog_valid (sf_digest S))).
apply: dlet_at0 => md.
rewrite Pr_code_put.
apply: sf_return_logged hout.
by rewrite get_set_heap_neq.
Qed.

Lemma sf_sign_log_support S q_s cm h response h' :
  Pr_code (sign_body S q_s cm) h (response,h') != 0 ->
  cm \in get_heap h' (sf_log_loc S).
Proof.
apply: contraR => hout.
by rewrite (sf_sign_log S q_s cm h response h' hout).
Qed.

Lemma sf_check_replay S cm sig h :
  cm \in get_heap h (sf_log_loc S) ->
  dfst (Pr_code (check_body S (cm,sig)) h) true = 0.
Proof.
move=> hin.
rewrite /check_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|];
last by rewrite Pr_code_fail /dmargin dlet_null_ext dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_done_loc);
first by rewrite Pr_code_fail /dmargin dlet_null_ext dnullE.
rewrite Pr_code_put Pr_code_get get_set_heap_neq //=.
case: (sf_message_valid S cm); last by rewrite dPr_ret dunit1E.
case: (sf_verify_query S st.2 cm sig) => [sg|];
last by rewrite dPr_ret dunit1E.
rewrite hin /=.
fold (@bind).
rewrite Pr_code_get.
case: (getm _ _) => [md|]; first by rewrite /= andbF dPr_ret dunit1E.
fold (@bind).
rewrite bind_assoc.
rewrite (Pr_code_fst (prog_valid (sf_digest S))) dfst_dlet_commut.
apply: dlet_at0 => md.
by rewrite Pr_code_put /= andbF dPr_ret dunit1E.
Qed.

Lemma sf_forge_replay S cm sig h :
  cm \in get_heap h (sf_log_loc S) ->
  dfst (Pr_code (forge_body S true (cm,sig)) h) true = 0.
Proof.
rewrite /forge_body bind_ret.
exact: sf_check_replay.
Qed.

Lemma sf_attempt_replay S q_s cm h response h' sig :
  Pr_code (sign_body S q_s cm) h (response,h') != 0 ->
  dfst (Pr_code (forge_body S true (cm,sig)) h') true = 0.
Proof.
move=> hs.
apply: sf_forge_replay.
exact: (sf_sign_log_support S q_s cm h response h' hs).
Qed.

(** The heap already holds the logged attempt and successor when hashing
    and grinding start. Invalid messages log and count but consume no leaf. *)
Lemma sf_sign_transition S q_s cm h st :
  get_heap h (sf_st_loc S) = Some st ->
  get_heap h sf_done_loc = false ->
  (get_heap h sf_scnt_loc < q_s)%N ->
  sf_message_valid S cm ->
  Pr_code (sign_body S q_s cm) h =
  Pr_code
    (match sf_sign_query S st.1 cm with
     | None => ret None
     | Some x => md ← shared_lookup S x ;; ret (sf_sign_finish S st.1 cm md)
     end)
    (set_heap
      (set_heap (set_heap h sf_scnt_loc (get_heap h sf_scnt_loc).+1)
        (sf_log_loc S) (cm :: get_heap h (sf_log_loc S)))
      (sf_st_loc S) (Some (sf_sign_next S st.1 cm, st.2))).
Proof.
move=> hst hd hq hm.
by rewrite /sign_body Pr_code_get hst Pr_code_get hd Pr_code_get hq
  Pr_code_put Pr_code_get get_set_heap_neq // Pr_code_put hm Pr_code_put.
Qed.

Lemma sf_sign_domain_refusal S q_s cm h st :
  get_heap h (sf_st_loc S) = Some st ->
  get_heap h sf_done_loc = false ->
  (get_heap h sf_scnt_loc < q_s)%N ->
  ~~ sf_message_valid S cm ->
  Pr_code (sign_body S q_s cm) h =
    Pr_code (ret None)
      (set_heap (set_heap h sf_scnt_loc (get_heap h sf_scnt_loc).+1)
        (sf_log_loc S) (cm :: get_heap h (sf_log_loc S))).
Proof.
move=> hst hd hq hm.
by rewrite /sign_body Pr_code_get hst Pr_code_get hd Pr_code_get hq
  Pr_code_put Pr_code_get get_set_heap_neq // Pr_code_put (negbTE hm).
Qed.

Lemma sf_hash_transition S q_h x h st :
  get_heap h (sf_st_loc S) = Some st ->
  get_heap h sf_done_loc = false ->
  (get_heap h sf_hcnt_loc < q_h)%N ->
  Pr_code (hash_body S q_h x) h =
    Pr_code
      (if sf_hash_valid S x then md ← shared_lookup S x ;; ret (Some md)
       else ret None)
      (set_heap h sf_hcnt_loc (get_heap h sf_hcnt_loc).+1).
Proof.
move=> hst hd hq.
by rewrite /hash_body Pr_code_get hd Pr_code_get hq Pr_code_put.
Qed.

Lemma sf_game_valid S q_s q_h b :
  ValidPackage (sf_locations S) emptym (I_EUCMA S)
    (EUCMA_game S q_s q_h b).
Proof. exact (pack_valid (EUCMA_game S q_s q_h b)). Qed.

Lemma sf_forger_valid S LA c vc :
  ValidPackage LA (I_EUCMA S) A_export (canonical_forger S LA c vc).
Proof. exact (pack_valid (canonical_forger S LA c vc)). Qed.

(* ------------------------------------------------------------------ *)
(** ** Counters and exact execution support *)

Lemma sf_return_location (T : choice_type) (v w : T)
    (l : Location) (expected : l) h h' :
  get_heap h l = expected ->
  get_heap h' l != expected ->
  Pr_code (ret v) h (w, h') = 0.
Proof.
move=> hin hout.
rewrite Pr_code_ret dunit1E.
case: eqP => [he|he] //.
case: he => _ hh.
subst h'.
by move: hout; rewrite hin eqxx.
Qed.

(** Counters count every admitted call, including None and repeated inputs. *)
Lemma sf_sign_count S q_s cm h response h' :
  get_heap h' sf_scnt_loc != (get_heap h sf_scnt_loc).+1 ->
  Pr_code (sign_body S q_s cm) h (response, h') = 0.
Proof.
move=> hout.
rewrite /sign_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|];
  last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_done_loc);
  first by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_scnt_loc < q_s)%N;
  last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_put Pr_code_get Pr_code_put.
set h0 := set_heap _ (sf_log_loc S) _.
have hin : get_heap h0 sf_scnt_loc = (get_heap h sf_scnt_loc).+1.
{ by rewrite /h0 get_set_heap_neq // get_set_heap_eq. }
case: (sf_message_valid S cm);
  last exact: sf_return_location hin hout.
rewrite Pr_code_put.
set h1 := set_heap h0 (sf_st_loc S) _.
have hin1 : get_heap h1 sf_scnt_loc = (get_heap h sf_scnt_loc).+1.
{ by rewrite /h1 get_set_heap_neq. }
case: (sf_sign_query S _ _) => [x|];
  last exact: sf_return_location hin1 hout.
rewrite /shared_lookup Pr_code_get.
case: (getm (get_heap h1 (sf_rom_loc S)) x) => [md|].
- exact: sf_return_location hin1 hout.
- (* A fresh hash sample preserves the signing counter. *)
  fold (@bind).
  rewrite bind_assoc (Pr_code_fst (prog_valid (sf_digest S))).
  apply: dlet_at0 => md.
  rewrite Pr_code_put.
  apply: sf_return_location hout.
  by rewrite get_set_heap_neq.
Qed.

Lemma sf_sign_count_support S q_s cm h response h' :
  Pr_code (sign_body S q_s cm) h (response, h') != 0 ->
  get_heap h' sf_scnt_loc = (get_heap h sf_scnt_loc).+1.
Proof.
move=> hs.
apply/eqP.
apply/negPn/negP => hn.
by move: hs; rewrite (sf_sign_count S q_s cm h response h' hn) eqxx.
Qed.

Lemma sf_hash_count S q_h x h response h' :
  get_heap h' sf_hcnt_loc != (get_heap h sf_hcnt_loc).+1 ->
  Pr_code (hash_body S q_h x) h (response, h') = 0.
Proof.
move=> hout.
rewrite /hash_body Pr_code_get.
case: (get_heap h sf_done_loc);
  first by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_hcnt_loc < q_h)%N;
  last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_put.
set h0 := set_heap h sf_hcnt_loc _.
have hin : get_heap h0 sf_hcnt_loc = (get_heap h sf_hcnt_loc).+1.
{ by rewrite /h0 get_set_heap_eq. }
case: (sf_hash_valid S x);
  last exact: sf_return_location hin hout.
rewrite /shared_lookup Pr_code_get.
case: (getm (get_heap h0 (sf_rom_loc S)) x) => [md|].
- exact: sf_return_location hin hout.
- (* A fresh hash sample preserves the hash counter. *)
  fold (@bind).
  rewrite bind_assoc (Pr_code_fst (prog_valid (sf_digest S))).
  apply: dlet_at0 => md.
  rewrite Pr_code_put.
  apply: sf_return_location hout.
  by rewrite get_set_heap_neq.
Qed.

Lemma sf_hash_count_support S q_h x h response h' :
  Pr_code (hash_body S q_h x) h (response, h') != 0 ->
  get_heap h' sf_hcnt_loc = (get_heap h sf_hcnt_loc).+1.
Proof.
move=> hs.
apply/eqP.
apply/negPn/negP => hn.
by move: hs; rewrite (sf_hash_count S q_h x h response h' hn) eqxx.
Qed.

Lemma sf_sign_log_exact S q_s cm h response h' :
  get_heap h' (sf_log_loc S) != cm :: get_heap h (sf_log_loc S) ->
  Pr_code (sign_body S q_s cm) h (response, h') = 0.
Proof.
move=> hout.
rewrite /sign_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|];
  last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_done_loc);
  first by rewrite Pr_code_fail dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_scnt_loc < q_s)%N;
  last by rewrite Pr_code_fail dnullE.
rewrite Pr_code_put Pr_code_get Pr_code_put.
set h0 := set_heap _ (sf_log_loc S) _.
have hin : get_heap h0 (sf_log_loc S) = cm :: get_heap h (sf_log_loc S).
{ by rewrite /h0 get_set_heap_eq get_set_heap_neq. }
case: (sf_message_valid S cm);
  last exact: sf_return_location hin hout.
rewrite Pr_code_put.
set h1 := set_heap h0 (sf_st_loc S) _.
have hin1 : get_heap h1 (sf_log_loc S) = cm :: get_heap h (sf_log_loc S).
{ by rewrite /h1 get_set_heap_neq. }
case: (sf_sign_query S _ _) => [x|];
  last exact: sf_return_location hin1 hout.
rewrite /shared_lookup Pr_code_get.
case: (getm (get_heap h1 (sf_rom_loc S)) x) => [md|].
- exact: sf_return_location hin1 hout.
- (* A fresh hash sample preserves the signing log. *)
  fold (@bind).
  rewrite bind_assoc (Pr_code_fst (prog_valid (sf_digest S))).
  apply: dlet_at0 => md.
  rewrite Pr_code_put.
  apply: sf_return_location hout.
  by rewrite get_set_heap_neq.
Qed.

Lemma sf_sign_log_exact_support S q_s cm h response h' :
  Pr_code (sign_body S q_s cm) h (response, h') != 0 ->
  get_heap h' (sf_log_loc S) = cm :: get_heap h (sf_log_loc S).
Proof.
move=> hs.
apply/eqP.
apply/negPn/negP => hn.
by move: hs; rewrite (sf_sign_log_exact S q_s cm h response h' hn) eqxx.
Qed.

Lemma sf_forge_done S b candidate h response h' :
  get_heap h' sf_done_loc != true ->
  Pr_code (forge_body S b candidate) h (response, h') = 0.
Proof.
move=> hout.
rewrite /forge_body /check_body Pr_code_get.
case: (get_heap h (sf_st_loc S)) => [st|];
  last by rewrite Pr_code_sample dlet_null_ext dnullE.
rewrite Pr_code_get.
case: (get_heap h sf_done_loc);
  first by rewrite Pr_code_sample dlet_null_ext dnullE.
rewrite Pr_code_put Pr_code_get.
set h0 := set_heap h sf_done_loc true.
have hin : get_heap h0 sf_done_loc = true.
{ by rewrite /h0 get_set_heap_eq. }
case: (sf_message_valid S candidate.1);
  last exact: sf_return_location hin hout.
case: (sf_verify_query S _ _ _) => [x|];
  last exact: sf_return_location hin hout.
rewrite /shared_lookup Pr_code_get.
case: (getm (get_heap h0 (sf_rom_loc S)) x) => [md|].
- exact: sf_return_location hin hout.
- (* A fresh hash sample preserves the completed-forgery flag. *)
  fold (@bind).
  rewrite !bind_assoc (Pr_code_fst (prog_valid (sf_digest S))).
  apply: dlet_at0 => md.
  rewrite Pr_code_put.
  apply: sf_return_location hout.
  by rewrite get_set_heap_neq.
Qed.

Lemma sf_forge_done_support S b candidate h response h' :
  Pr_code (forge_body S b candidate) h (response, h') != 0 ->
  get_heap h' sf_done_loc = true.
Proof.
move=> hs.
apply/eqP.
apply/negPn/negP => hn.
by move: hs; rewrite (sf_forge_done S b candidate h response h' hn) eqxx.
Qed.

Lemma sf_sign_budget_support S q_s cm h response h' :
  Pr_code (sign_body S q_s cm) h (response, h') != 0 ->
  (get_heap h' sf_scnt_loc <= q_s)%N.
Proof.
move=> hs.
rewrite (sf_sign_count_support S q_s cm h response h' hs).
rewrite /sign_body Pr_code_get in hs.
case: (get_heap h (sf_st_loc S)) hs => [st|] hs;
  last by rewrite Pr_code_fail dnullE eqxx in hs.
rewrite Pr_code_get in hs.
case: (get_heap h sf_done_loc) hs => hs;
  first by rewrite Pr_code_fail dnullE eqxx in hs.
rewrite Pr_code_get in hs.
case hq: (get_heap h sf_scnt_loc < q_s)%N in hs; first exact: hq.
by rewrite Pr_code_fail dnullE eqxx in hs.
Qed.

Lemma sf_hash_budget_support S q_h x h response h' :
  Pr_code (hash_body S q_h x) h (response, h') != 0 ->
  (get_heap h' sf_hcnt_loc <= q_h)%N.
Proof.
move=> hs.
rewrite (sf_hash_count_support S q_h x h response h' hs).
rewrite /hash_body Pr_code_get in hs.
case: (get_heap h sf_done_loc) hs => hs;
  first by rewrite Pr_code_fail dnullE eqxx in hs.
rewrite Pr_code_get in hs.
case hq: (get_heap h sf_hcnt_loc < q_h)%N in hs; first exact: hq.
by rewrite Pr_code_fail dnullE eqxx in hs.
Qed.
