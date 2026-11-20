(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.chain.pre_terminal

    Equal chain ends and a decreasing digit yield a preimage witness when
    the collision classifier declines. Honest digits need only be in
    range, so the statement also covers virtual all-max refusal slots. *)

From Shrincs.internal.ssprove.lib Require Import prelude chain.core.
#[local] Open Scope nat_scope.

Lemma valid_msg_not_allmax l w S (ds : seq nat) :
  S != (l * w.-1)%N -> valid_msg l w S ds ->
  has (fun d => (d < w.-1)%N) ds.
Proof.
move=> hdeg /and3P[/eqP hsz hwf /eqP hsum].
apply/negbNE/negP => /hasPn hall.
have hall1 : all (pred1 w.-1) ds.
  apply/allP => d hd.
  have h1 : (d < w)%N := allP hwf d hd.
  have h2 : (w.-1 <= d)%N by rewrite leqNgt; exact: hall.
  by rewrite /= eqn_leq h2 andbT -ltnS (ltn_predK h1).
move/eqP: hdeg; apply.
by rewrite -hsum (all_pred1P _ _ hall1) sumn_nseq hsz mulnC.
Qed.

Lemma size_pre_queries (N : choice_type) st ds (us : seq N) :
  size us = size ds ->
  size (pre_queries N st ds us) = preimage_query_count ds.
Proof.
elim: ds st us => [|d ds ih] st [|u us] //= [hlen].
rewrite pre_queries_cons size_cat (ih _ _ hlen).
by case: d.
Qed.

Section Terminal.
Context (PP N : choice_type) (l w S_wn : nat).
Context (F : PP -> nat -> nat -> N -> N).

Lemma pre_terminal (pp : PP) (dds : seq nat)
    (us sgstar : seq N) (mstar : seq nat) :
  size dds = l -> all (fun d => (d < w)%N) dds -> size us = l ->
  valid_msg l w S_wn mstar ->
  (size sgstar == l)%B ->
  has (fun i => (nth 0 mstar i < nth 0 dds i)%N) (iota 0 l) ->
  ends_from_sig PP N l w F pp mstar sgstar = ends_from_sig PP N l w F pp dds (sigs_of PP N w F pp 0 dds us) ->
  tcr_decision PP N l w F pp dds mstar (sigs_of PP N w F pp 0 dds us) sgstar = None ->
  exists jc x t u,
    [/\ pre_decision PP N l w F pp dds mstar (sigs_of PP N w F pp 0 dds us) sgstar
        = Some (jc, x),
        qnth (pre_queries N 0 dds us) jc = Some (t, u)
      & Fc PP N w F pp t x = Fc PP N w F pp t u].
Proof.
move=> hddsz hddw hus hvmf hsgsz hhas hends hnone.
have hmsz : size mstar = l by case/and3P: hvmf => /eqP.
have hussz : size us = size dds by rewrite hus hddsz.
have hsgs : size (sigs_of PP N w F pp 0 dds us) = l.
by rewrite (size_sigs_of PP N w F pp 0 dds us hussz) hddsz.
(* forged completion = honest completion -> the same ends_from_sig public key *)
have hEE : ends_from_sig PP N l w F pp dds (sigs_of PP N w F pp 0 dds us)
         = ends_from_sig PP N l w F pp mstar sgstar.
exact: esym hends.
have hAC : forall (n st : nat) (ds0 : seq nat) (ys : seq N),
  all (fun q => chain_check PP N w F pp q.1 q.2.1 q.2.2.1 q.2.2.2)
      (zip (iota st n)
           (zip ds0 (zip ys
              [seq chainc PP N w F pp q.1 q.2.2 q.2.1 (w.-1 - q.2.1)
              | q <- zip (iota st n) (zip ds0 ys)]))).
elim=> [|n IH] st ds0 ys; first by case: ds0 => [|d ds0]; case: ys => [|y ys].
case: ds0 => [|d ds0]; case: ys => [|y ys] => //=.
apply/andP; split; last exact: IH.
by rewrite /core.chain_check eqxx.
have hverify : core.verify_sig PP N l w S_wn F pp
    (ends_from_sig PP N l w F pp dds (sigs_of PP N w F pp 0 dds us)) mstar sgstar.
rewrite hEE /core.verify_sig hvmf hsgsz /= /ends_from_sig.
exact: (hAC l 0 mstar sgstar).
(* now the shared ohead coordinate drives both totality and the win *)
rewrite /pre_decision; move: hnone; rewrite /tcr_decision.
case E1: (ohead _) => [i|]; last first.
by move=> _; move: hhas E1; rewrite has_filter; case: (filter _ _) => [|a s].
have hifacts : i \in [seq i0 <- iota 0 l | (nth 0 mstar i0 < nth 0 dds i0)%N].
by move: E1; case: (filter _ _) => //= a s [<-]; rewrite in_cons eqxx.
move: hifacts; rewrite mem_filter mem_iota /= add0n => /andP[hlt hil].
have [si E2] : exists si, qnth (sigs_of PP N w F pp 0 dds us) i = Some si.
by apply: qnth_some; rewrite hsgs.
have [si' E3] : exists si', qnth sgstar i = Some si'.
by apply: qnth_some; rewrite (eqP hsgsz).
rewrite E2 E3.
have hdw : (nth 0 dds i < w)%N by apply: (allP hddw); rewrite mem_nth // hddsz.
have hszends := size_ends_from_sig PP N l w F pp dds
                  (sigs_of PP N w F pp 0 dds us) hddsz hsgs.
have h1 := verify_sig_nth PP N l w S_wn F pp _ mstar sgstar si' i
             hverify hszends hil.
rewrite (ends_from_sig_nth PP N l w F pp dds (sigs_of PP N w F pp 0 dds us)
           si' i hddsz hsgs hil) in h1.
rewrite (qnth_nth si' _ _ _ E3) (qnth_nth si' _ _ _ E2) in h1.
have hfc := forgery_cases PP N w F pp i (nth 0 dds i) si (nth 0 mstar i) si'
              hlt hdw h1.
move: hfc; case E4: (chain_extractc PP N w F pp i si'
                       (nth 0 mstar i) si (nth 0 dds i) w.-1) => [k u v|] hfc.
by [].
move=> _.
have hpim := forgery_pre_preimage PP N w F pp i (nth 0 dds i) si si'
               (nth 0 mstar i) hlt hfc.
have hilm : (i < size dds)%N by rewrite hddsz.
have [ui hui] : exists ui, qnth us i = Some ui.
by apply: qnth_some; rewrite hus.
have hsig0 := qnth_sigs_of PP N w F pp 0 dds us i ui hussz hilm hui.
rewrite add0n E2 in hsig0.
case: hsig0 => hsig.
have hd0 : (0 < nth 0 dds i)%N := leq_ltn_trans (leq0n _) hlt.
have hsr : sig_of_root PP N w F pp i (nth 0 dds i) ui
         = Fc PP N w F pp (i, (nth 0 dds i).-1) ui by case: (nth 0 dds i) hd0.
exists (pre_index dds i),
       (chainc PP N w F pp i si' (nth 0 mstar i)
              ((nth 0 dds i).-1 - nth 0 mstar i)),
       (i, (nth 0 dds i).-1), ui; split.
- (* The classifier returns the selected preimage witness. *)
  by [].
- (* The selected target is present in the query list. *)
  by rewrite (qnth_pre_queries N 0 dds us i ui hussz hilm hui hd0).
- (* The forged prefix hashes to the target image. *)
  by rewrite hpim hsig hsr.
Qed.

End Terminal.
