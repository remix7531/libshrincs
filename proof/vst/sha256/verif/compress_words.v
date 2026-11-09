(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 * Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
 *)

(** * Verif_compress_words: proof of body_sha256_compress_words

    SS 6.2.2, all four steps -- RustCrypto sha2's [compress_u32]. THE
    LONG POLE of this development: VST's own SHA-256 compression proof
    is around 950 lines even with the schedule fully unrolled, and
    src/sha256.c keeps a SLIDING WINDOW, which is the harder of the two
    schedules to reason about.

    Three loops, and the middle one is the reason step 3 is split in
    the C rather than guarded by a branch: with the split, only the
    third loop carries the window relation.

    LOOP 1, [for (t = 0; t < 16; t++) W[t] = M[t]] -- the usual partial
    copy:

      EX t : Z, ... SEP (data_at Tsh (tarray tuint 16)
        (sublist 0 t (words_to_vals Ms) ++ Zrepeat Vundef (16 - t)) v_W; ...)

    LOOP 2, rounds 0 to 15. W is untouched here, so the schedule side
    of the invariant is just "the array still holds the block", and
    the working variables carry the fold:

      EX t : Z, EX wa .. wh : w32c,
        PROP (rounds_upto Hs Ms (Z.to_nat t) = (wa, wb, wc, wd, we, wf, wg, wh))
        LOCAL (temp _a (Vint (int_of_w32 wa)); ... )
        SEP (data_at Tsh (tarray tuint 16) (words_to_vals Ms) v_W; ...)

    LOOP 3, rounds 16 to 63. THE WINDOW. The array no longer holds a
    prefix of the schedule; it holds the sixteen most recent words,
    each at its own index modulo 16:

      EX t : Z, EX Wv : list val, EX wa .. wh : w32c,
        PROP (Zlength Wv = 16;
              forall u : Z, t - 16 <= u < t ->
                Znth (u mod 16) Wv
                  = Vint (int_of_w32 (nth w32_0 (schedule Ms) (Z.to_nat u)));
              rounds_upto Hs Ms (Z.to_nat t) = (wa, wb, wc, wd, we, wf, wg, wh))
        LOCAL (temp _a (Vint (int_of_w32 wa)); ... )
        SEP (data_at Tsh (tarray tuint 16) Wv v_W; ...)

    The window is stated over Z rather than over nat, which is what
    makes it cheap: the C reads [W[(t - j) % 16]] and floyd hands the
    proof the index [(i - j) mod 16] already in Z, so the invariant
    applies at [u := i - j] with no conversion at all. At t = 16 the
    range is [0, 16), exactly what loop 2 leaves behind, so entry is
    free and the asymmetry the sliding window is famous for never
    appears -- it was spent by splitting the loop.

    THE STEP is where the two model lemmas earn their place.
    [nth_schedule_upto_last] says the word produced at index t is
    [sigma1] of the word at [t-2], plus [t-7], plus [sigma0] of
    [t-15], plus [t-16] -- the four offsets the C reads, literally.
    [nth_schedule_prefix] moves between [schedule Ms] (what the
    invariant above names) and [schedule_upto Ms n] (what that lemma
    produces); [nth_schedule_rec] is the two of them composed into the
    recurrence stated entirely over [schedule Ms]. Writing
    [W[t %% 16]] retires [u = t-16] and admits [u = t], which is the
    window sliding by one; the only arithmetic obligation is
    [mod16_neq], that two indices less than sixteen apart differ
    modulo sixteen.

    STEP 4 is eight straight-line load/store pairs against
    [compress_words]'s [zip ... H] and needs nothing new.

    SCOPE TRAP, and the reason loop 1's invariant carries an explicit
    [%list]. With mathcomp's seq_scope on top of the stack a bare
    [++] is mathcomp's [cat], not [List.app] -- different constants --
    and floyd's [list_solve] only knows [app]. The symptom is
    "list_solve cannot solve this goal" on a goal that is manifestly
    true, with nothing pointing at the notation. *)

From Vst.repr Require Import words.
From Vst.sha256 Require Import bridge.
From Vst.sha256 Require Import contract.
From Vst Require Import settings.
From Vst.sha256 Require Import clone.
From Vst.clight Require Import sha256.

From mathcomp Require Import boot order algebra word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.

Set Bullet Behavior "Strict Subproofs".

(* IMPORT DISCIPLINE, and what it costs the proof scripts. The wide
   mathcomp surface stays because this file's own STATEMENTS are typed
   in it: [seq (word U32)], [size Hs = 8%nat] and the [[:: ... ]] list
   literal of [compress_words_vals], plus the boolean [nat] bounds the
   model lemmas ([roundsS], [nth_schedule_rec]) take. Narrowing the
   import to [ssralg word.word] would change those statements.

   So mathcomp's [rewrite] is the one in scope, and it differs from
   Stdlib's in two places a reader will notice below: a list of
   rewrites is NOT comma-separated -- each rule gets its own line,
   which is what this repo's STYLE.md asks for anyway -- and the
   Stdlib form [rewrite H by tac] does not parse (nothing below needs
   it). Right-to-left [rewrite <- H] does parse, and is spelled that
   way throughout.

   The reflection view that turns mathcomp's BOOLEAN [_ < _] on [nat]
   -- which is what the model lemmas ask for -- into the [Prop] one
   [lia] reads is spelled [apply (introT ltP)], per STYLE.md: the
   view operator [apply/ltP] is compact ssreflect and does not belong
   in this tier. *)

Local Open Scope Z_scope.

(* ================================================================= *)
(** ** The array shapes this proof needs

    Every array in this function is a [words_to_vals] of a [seq w32].
    The three shapes the proof meets a read in -- a symbolic [Z]
    index, a [nat] literal, and the whole eight-element array written
    out -- are [Znth_words_to_vals], [Znth_words_to_vals_nat] and
    [words_to_vals_8] of Vst.sha256.bridge. What is left
    here is the one shape that is about the C loop and not about the
    translation. *)

(** One iteration of loop 1: filling the first still-undefined slot
    extends the copied prefix by one. Generic in the array length, so
    it is a hoist candidate for a shared VST list theory. *)
Lemma upd_step (l : list Values.val) (i n : Z) :
  0 <= i < n -> Zlength l = n ->
  upd_Znth i (sublist 0 i l ++ Zrepeat Vundef (n - i))%list (Znth i l)
  = (sublist 0 (i + 1) l ++ Zrepeat Vundef (n - (i + 1)))%list.
Proof.
intros Hi Hl.
list_solve.
Qed.

(* ================================================================= *)
(** ** The sliding sixteen-word window

    Loop 3 keeps only W[t mod 16], so the recurrence
    [nth_schedule_rec] of Vst.sha256.clone states has to be
    read off a window rather than off the whole schedule. *)

(** The whole arithmetic content of the sliding window: the slot the
    round about to be computed overwrites is the one no later round
    reads, because two indices less than sixteen apart cannot agree
    modulo sixteen. *)
Lemma mod16_neq (u t : Z) : 0 < t - u < 16 -> u mod 16 <> t mod 16.
Proof.
intros Hd Heq.
assert (Hz : (t - u) mod 16 = 0).
{ rewrite Zminus_mod.
  rewrite Heq.
  rewrite Z.sub_diag.
  apply Zmod_0_l. }
assert (Hdv : (16 | t - u)) by exact (proj1 (Z.mod_divide (t - u) 16 ltac:(lia)) Hz).
assert (Hle : 16 <= t - u) by exact (Z.divide_pos_le 16 (t - u) ltac:(lia) Hdv).
lia.
Qed.

(* ================================================================= *)
(** ** SS 6.2.2 step 4, in the shape the POSTcondition states it

    [nth_compress_words] of Vst.sha256.clone gives one
    entry; step 4 stores all eight, so the array is written out. *)

(** The POSTcondition's array, written out against the eight working
    variables the sixty-four rounds left behind. *)
Lemma compress_words_vals (Hs Ms : seq (word U32))
      (wa wb wc wd we wf wg wh : word U32) :
  size Hs = 8%nat ->
  rounds Hs Ms = (wa, wb, wc, wd, we, wf, wg, wh) ->
  words_to_vals (compress_words Hs Ms) =
  [:: Vint (int_of_w32 (wa + nth w32_0 Hs 0)%R);
      Vint (int_of_w32 (wb + nth w32_0 Hs 1)%R);
      Vint (int_of_w32 (wc + nth w32_0 Hs 2)%R);
      Vint (int_of_w32 (wd + nth w32_0 Hs 3)%R);
      Vint (int_of_w32 (we + nth w32_0 Hs 4)%R);
      Vint (int_of_w32 (wf + nth w32_0 Hs 5)%R);
      Vint (int_of_w32 (wg + nth w32_0 Hs 6)%R);
      Vint (int_of_w32 (wh + nth w32_0 Hs 7)%R)].
Proof.
intros H8 Hr.
rewrite (words_to_vals_8 _ (compress_words_size Hs Ms H8)).
(* [erefl] is mathcomp's [eq_refl]; it discharges the literal bound
   [(k < 8)%nat] by computation. The Stdlib name cannot be used here:
   under this import [eq_refl] is ssrbool's BOOLEAN [x == x]. *)
rewrite (nth_compress_words Hs Ms 0 erefl H8).
rewrite (nth_compress_words Hs Ms 1 erefl H8).
rewrite (nth_compress_words Hs Ms 2 erefl H8).
rewrite (nth_compress_words Hs Ms 3 erefl H8).
rewrite (nth_compress_words Hs Ms 4 erefl H8).
rewrite (nth_compress_words Hs Ms 5 erefl H8).
rewrite (nth_compress_words Hs Ms 6 erefl H8).
rewrite (nth_compress_words Hs Ms 7 erefl H8).
rewrite Hr.
reflexivity.
Qed.

(* ================================================================= *)
(** ** The body proof *)

Lemma body_sha256_compress_words :
  semax_body Vprog_sha Gprog_sha f_sha256_compress_words spec_sha256_compress_words.
Proof.
start_function.
rename H into HHn.                    (* size Hs = 8 *)
rename H0 into HMn.                   (* size Ms = 16 *)

(* ===== Setup: name the array facts ===== *)

(* K arrives as the third pointer PARAMETER, so its [data_at] is
   already a top-level SEP conjunct: there is nothing to unfold, and
   the array is read exactly the way [M] is. *)

(* The four indexed facts every [forward] over an array needs. *)
assert (HMz : Zlength (words_to_vals Ms) = 16).
{ rewrite words_to_vals_Zlength.
  rewrite HMn.
  reflexivity. }
assert (HMv : forall j : Z, 0 <= j < 16 ->
          Znth j (words_to_vals Ms) = Vint (int_of_w32 (nth w32_0 Ms (Z.to_nat j)))).
{ intros j Hj.
  apply Znth_words_to_vals.
  rewrite HMn.
  lia. }
assert (HKv : forall j : Z, 0 <= j < 64 ->
          Znth j (words_to_vals K) = Vint (int_of_w32 (nth w32_0 K (Z.to_nat j)))).
{ intros j Hj.
  apply Znth_words_to_vals.
  rewrite K_size.
  lia. }
assert (HHv : forall (k : nat) (j : Z), (k < 8)%nat -> j = Z.of_nat k ->
          Znth j (words_to_vals Hs) = Vint (int_of_w32 (nth w32_0 Hs k))).
{ intros k j Hk Hj.
  apply Znth_words_to_vals_nat.
  - (* the index is in range *)
    rewrite HHn.
    exact Hk.
  - exact Hj. }
(* SS 6.2.2 step 1, first line: the first sixteen schedule words ARE
   the block. This is [nth_schedule_prefix] at n = 0, and it is what
   lets loop 2 speak of [Ms] where the funspec speaks of the
   schedule. *)
assert (Hpre : forall u : Z, 0 <= u < 16 ->
          nth w32_0 (schedule Ms) (Z.to_nat u) = nth w32_0 Ms (Z.to_nat u)).
{ intros u Hu.
  rewrite (nth_schedule_prefix Ms 0 (Z.to_nat u) HMn).
  - (* zero extension steps is at most forty-eight, by computation *)
    reflexivity.
  - rewrite addn0.
    apply (introT ltP).
    lia.
  - reflexivity. }

(* ===== SS 6.2.2 step 1, the t < 16 half -- C loop 1 =====
   for (t = 0; t < 16; t++) W[t] = M[t];
   Step 1's other half, t >= 16, is NOT here: the C fuses it into loop
   3 below, and that fusion is what keeps the window out of loop 2. *)
forward_for_simple_bound 16
  (EX t : Z,
   PROP ()
   LOCAL (lvar _W (tarray tuint 16) v_W; temp _H hp; temp _M mp;
          temp _sha256_K kp)
   SEP (data_at Tsh (tarray tuint 16)
          (sublist 0 t (words_to_vals Ms) ++ Zrepeat Vundef (16 - t))%list v_W;
        data_at shh (tarray tuint 8) (words_to_vals Hs) hp;
        data_at shm (tarray tuint 16) (words_to_vals Ms) mp;
        data_at shk (tarray tuint 64) (words_to_vals K) kp)).
- (* entry: nothing copied yet, all sixteen slots undefined *)
  entailer!.
- (* one iteration *)
  forward.                      (* t'26 = M[t] *)
  + (* the block holds machine words *)
    rewrite (HMv i ltac:(lia)).
    entailer!.
  + forward.                    (* W[t] = t'26 *)
    entailer!.
    apply derives_refl'.
    f_equal.
    apply upd_step.
    * lia.
    * exact HMz.
- (* exit: W holds the block *)
  assert (Hfull : (sublist 0 16 (words_to_vals Ms) ++ Zrepeat Vundef (16 - 16))%list
                  = words_to_vals Ms) by list_solve.
  rewrite Hfull.
  clear Hfull.

  (* ===== SS 6.2.2 step 2 -- straight line ===== *)
  (* a = H[0]; b = H[1]; ... h = H[7]: the working variables start at
     the incoming chaining value. *)
  rewrite (words_to_vals_8 Hs HHn).
  forward.                      (* a = H[0] *)
  forward.                      (* b = H[1] *)
  forward.                      (* c = H[2] *)
  forward.                      (* d = H[3] *)
  forward.                      (* e = H[4] *)
  forward.                      (* f = H[5] *)
  forward.                      (* g = H[6] *)
  forward.                      (* h = H[7] *)
  rewrite <- (words_to_vals_8 Hs HHn).
  rewrite (HHv 0%nat 0 erefl erefl).
  rewrite (HHv 1%nat 1 erefl erefl).
  rewrite (HHv 2%nat 2 erefl erefl).
  rewrite (HHv 3%nat 3 erefl erefl).
  rewrite (HHv 4%nat 4 erefl erefl).
  rewrite (HHv 5%nat 5 erefl erefl).
  rewrite (HHv 6%nat 6 erefl erefl).
  rewrite (HHv 7%nat 7 erefl erefl).
  (* Step 2 was [HHv]'s only consumer: nothing below indexes H again
     until step 4, which reads all eight at once through
     [words_to_vals_8]. *)
  clear HHv.

  (* ===== SS 6.2.2 step 3, rounds 0 to 15 -- C loop 2 =====
     No round in this range writes W, so the schedule side of the
     invariant is just "the array still holds the block" and there is
     no window relation to carry. Buying that is the whole reason the
     C splits step 3 into two loops instead of guarding one loop with
     [if (t < 16)]. *)
  forward_for_simple_bound 16
    (EX t : Z, EX wa : w32c, EX wb : w32c, EX wc : w32c, EX wd : w32c,
     EX we : w32c, EX wf : w32c, EX wg : w32c, EX wh : w32c,
     PROP (rounds_upto Hs Ms (Z.to_nat t) = (wa, wb, wc, wd, we, wf, wg, wh))
     LOCAL (temp _a (Vint (int_of_w32 wa)); temp _b (Vint (int_of_w32 wb));
            temp _c (Vint (int_of_w32 wc)); temp _d (Vint (int_of_w32 wd));
            temp _e (Vint (int_of_w32 we)); temp _f (Vint (int_of_w32 wf));
            temp _g (Vint (int_of_w32 wg)); temp _h (Vint (int_of_w32 wh));
            lvar _W (tarray tuint 16) v_W; temp _H hp; temp _M mp;
            temp _sha256_K kp)
     SEP (data_at Tsh (tarray tuint 16) (words_to_vals Ms) v_W;
          data_at shh (tarray tuint 8) (words_to_vals Hs) hp;
          data_at shm (tarray tuint 16) (words_to_vals Ms) mp;
          data_at shk (tarray tuint 64) (words_to_vals K) kp)).
  + (* entry: no rounds run, so the state is still H^(i-1) *)
    Exists (nth w32_0 Hs 0) (nth w32_0 Hs 1) (nth w32_0 Hs 2) (nth w32_0 Hs 3)
           (nth w32_0 Hs 4) (nth w32_0 Hs 5) (nth w32_0 Hs 6) (nth w32_0 Hs 7).
    entailer!.
    assert (Hz0 : Z.to_nat 0 = 0%nat) by reflexivity.
    rewrite Hz0.
    rewrite rounds_upto0.
    reflexivity.
  + (* one round *)
    rename H into Hi.
    Intros.
    rename H into Hst.
    assert (Hi64 : 0 <= i < 64) by lia.
    assert (Hlt64 : (Z.to_nat i < 64)%nat) by (apply (introT ltP); lia).
    pose proof (Hpre i Hi) as Hsch.
    forward_call (int_of_w32 we).                                (* t'1 = Sigma1(e) *)
    rewrite !int_of_w32K.
    forward_call (int_of_w32 we, int_of_w32 wf, int_of_w32 wg).  (* t'2 = Ch(e, f, g) *)
    rewrite !int_of_w32K.
    forward.                                                     (* t'24 = sha256_K[t] *)
    { (* the round-constant table holds machine words *)
      rewrite (HKv i Hi64).
      entailer!. }
    forward.                                                     (* t'25 = W[t] *)
    { (* so does the schedule array *)
      rewrite (HMv i Hi).
      entailer!. }
    rewrite (HKv i Hi64).
    rewrite (HMv i Hi).
    forward.                              (* T1 = h + t'1 + t'2 + t'24 + t'25 *)
    forward_call (int_of_w32 wa).                                (* t'3 = Sigma0(a) *)
    rewrite !int_of_w32K.
    forward_call (int_of_w32 wa, int_of_w32 wb, int_of_w32 wc).  (* t'4 = Maj(a, b, c) *)
    rewrite !int_of_w32K.
    forward.                              (* T2 = t'3 + t'4 *)
    forward.                              (* h = g *)
    forward.                              (* g = f *)
    forward.                              (* f = e *)
    forward.                              (* e = d + T1 *)
    forward.                              (* d = c *)
    forward.                              (* c = b *)
    forward.                              (* b = a *)
    forward.                              (* a = T1 + T2 *)
    (* the C's [Int.add] tower IS the standard's T1 and T2 *)
    rewrite !int_add_of_w32.
    (* SS 6.2.2 step 3's rotation, in the invariant's binder order:
         a := T1 + T2    b := a    c := b    d := c
         e := d + T1     f := e    g := f    h := g
       with T1 = h + Sigma1 e + Ch e f g + K[t] + W[t] and
       T2 = Sigma0 a + Maj a b c. Only a and e are new; the other six
       shift down, which is why six of the eight witnesses below are
       bare variables. W[t] appears as [nth Ms t] because for t < 16
       the schedule IS the block -- that is what [Hsch] records. *)
    Exists ((wh + Sigma1 we + Ch we wf wg + nth w32_0 K (Z.to_nat i)
             + nth w32_0 Ms (Z.to_nat i)) + (Sigma0 wa + Maj wa wb wc))%R
           wa wb wc
           (wd + (wh + Sigma1 we + Ch we wf wg + nth w32_0 K (Z.to_nat i)
                  + nth w32_0 Ms (Z.to_nat i)))%R
           we wf wg.
    entailer!.
    assert (Hn1 : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
    rewrite Hn1.
    rewrite (roundsS Hs Ms (Z.to_nat i) Hlt64 HMn).
    rewrite Hst.
    rewrite Hsch.
    reflexivity.

  (* ===== SS 6.2.2 steps 1 (t >= 16) and 3 (rounds 16 to 63), FUSED
     -- C loop 3. THE SLIDING WINDOW ===== *)
  + Intros xa xb xc xd xe xf xg xh.
    (* [Hst16] is never named again, but it is what this loop's entry
       [entailer!] closes its [rounds_upto] conjunct with. *)
    rename H into Hst16.
    (* THE WINDOW, restated here because the header is three hundred
       lines up. At loop index t the array is NOT a prefix of the
       schedule and never becomes one again: entry [u mod 16] holds
       schedule word u for the sixteen most RECENT u, that is for
       every u in [t - 16, t).

       Sixteen consecutive indices hit sixteen distinct residues, so
       those sixteen entries are the whole array -- which is why the
       invariant needs no separate clause saying the rest is junk, and
       why the store W[t % 16] can retire u = t - 16 and admit u = t
       in one move. The header argues the rest: why the index is a Z,
       and why entry at t = 16 is free. *)
    forward_for_simple_bound 64
      (EX t : Z, EX Wv : list Values.val,
       EX wa : w32c, EX wb : w32c, EX wc : w32c, EX wd : w32c,
       EX we : w32c, EX wf : w32c, EX wg : w32c, EX wh : w32c,
       PROP (Zlength Wv = 16;
             forall u : Z, t - 16 <= u < t ->
               Znth (u mod 16) Wv
               = Vint (int_of_w32 (nth w32_0 (schedule Ms) (Z.to_nat u)));
             rounds_upto Hs Ms (Z.to_nat t) = (wa, wb, wc, wd, we, wf, wg, wh))
       LOCAL (temp _a (Vint (int_of_w32 wa)); temp _b (Vint (int_of_w32 wb));
              temp _c (Vint (int_of_w32 wc)); temp _d (Vint (int_of_w32 wd));
              temp _e (Vint (int_of_w32 we)); temp _f (Vint (int_of_w32 wf));
              temp _g (Vint (int_of_w32 wg)); temp _h (Vint (int_of_w32 wh));
              lvar _W (tarray tuint 16) v_W; temp _H hp; temp _M mp;
              temp _sha256_K kp)
       SEP (data_at Tsh (tarray tuint 16) Wv v_W;
            data_at shh (tarray tuint 8) (words_to_vals Hs) hp;
            data_at shm (tarray tuint 16) (words_to_vals Ms) mp;
            data_at shk (tarray tuint 64) (words_to_vals K) kp)).
    * (* entry at t = 16: the window is [0, 16), which is the block *)
      Exists (words_to_vals Ms) xa xb xc xd xe xf xg xh.
      entailer!.
      intros u Hu.
      rewrite (Z.mod_small u 16 ltac:(lia)).
      rewrite (HMv u ltac:(lia)).
      rewrite (Hpre u ltac:(lia)).
      reflexivity.
    * (* one round, preceded by its own schedule word *)
      rename H into Hi.
      Intros.
      rename H into HWz.
      rename H0 into HWin.
      rename H1 into Hst.
      (* [Hpre] and [HMv] belong to the loops that spoke of [Ms]; this
         one speaks of [schedule Ms] throughout. Dropping them keeps
         two universally quantified hypotheses out of the thirty-odd
         [forward]s below. [HWz] looks equally unused and is not: the
         [upd_Znth] bullets close their bounds with [lia], which reads
         it from the context. *)
      clear Hpre HMv.
      (* floyd's load rule asks for each subscript in [0, 16); [rep_lia]
         does not know [Z.mod_pos_bound], so the five bounds are named. *)
      assert (Hm2 : 0 <= (i - 2) mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      assert (Hm7 : 0 <= (i - 7) mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      assert (Hm15 : 0 <= (i - 15) mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      assert (Hm16 : 0 <= (i - 16) mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      assert (Hm0 : 0 <= i mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      forward.                                    (* t'23 = W[(t - 2) % 16] *)
      { rewrite (HWin (i - 2) ltac:(lia)).
        entailer!. }
      rewrite (HWin (i - 2) ltac:(lia)).
      forward_call (int_of_w32 (nth w32_0 (schedule Ms) (Z.to_nat (i - 2)))).
                                                  (* t'5 = sigma1(t'23) *)
      rewrite !int_of_w32K.
      forward.                                    (* t'22 = W[(t - 15) % 16] *)
      { rewrite (HWin (i - 15) ltac:(lia)).
        entailer!. }
      rewrite (HWin (i - 15) ltac:(lia)).
      forward_call (int_of_w32 (nth w32_0 (schedule Ms) (Z.to_nat (i - 15)))).
                                                  (* t'6 = sigma0(t'22) *)
      rewrite !int_of_w32K.
      forward.                                    (* t'20 = W[(t - 7) % 16] *)
      { rewrite (HWin (i - 7) ltac:(lia)).
        entailer!. }
      forward.                                    (* t'21 = W[(t - 16) % 16] *)
      { rewrite (HWin (i - 16) ltac:(lia)).
        entailer!. }
      rewrite (HWin (i - 7) ltac:(lia)).
      rewrite (HWin (i - 16) ltac:(lia)).
      forward.                          (* w = t'5 + t'20 + t'6 + t'21 *)
      rewrite !int_add_of_w32.
      assert (Hlt64 : (Z.to_nat i < 64)%nat) by (apply (introT ltP); lia).
      (* SS 6.2.2 step 1's recurrence at t: what the C just built IS
         the t-th schedule word. *)
      assert (Hw : nth w32_0 (schedule Ms) (Z.to_nat i)
                 = (sigma1 (nth w32_0 (schedule Ms) (Z.to_nat (i - 2)))
                    + nth w32_0 (schedule Ms) (Z.to_nat (i - 7))
                    + sigma0 (nth w32_0 (schedule Ms) (Z.to_nat (i - 15)))
                    + nth w32_0 (schedule Ms) (Z.to_nat (i - 16)))%R).
      { (* the four offsets, as [nth_schedule_rec] indexes them: all
           four counted up from [i - 16]. [rewrite <- plusE] turns
           mathcomp's [addn] into Stdlib's [Nat.add], which is the one
           [lia]'s preprocessing has instances for. *)
        assert (E0 : Z.to_nat i = (16 + Z.to_nat (i - 16))%nat) by (rewrite <- plusE; lia).
        assert (E2 : Z.to_nat (i - 2) = (14 + Z.to_nat (i - 16))%nat) by (rewrite <- plusE; lia).
        assert (E7 : Z.to_nat (i - 7) = (9 + Z.to_nat (i - 16))%nat) by (rewrite <- plusE; lia).
        assert (E15 : Z.to_nat (i - 15) = (1 + Z.to_nat (i - 16))%nat) by (rewrite <- plusE; lia).
        rewrite E0.
        rewrite E2.
        rewrite E7.
        rewrite E15.
        apply nth_schedule_rec.
        - exact HMn.
        - apply (introT ltP).
          lia. }
      rewrite <- Hw.
      (* [Hw] is spent, and so are the four load bounds: everything
         below indexes W only to store, at [i mod 16]. [Hw] mentions
         [schedule Ms] four times, so leaving it in scope would make
         each of the twenty-five [forward]s that follow carry it. *)
      clear Hw Hm2 Hm7 Hm15 Hm16.
      forward.                                    (* W[t % 16] = w *)
      assert (Hi64 : 0 <= i < 64) by lia.
      forward_call (int_of_w32 we).                                (* t'7 = Sigma1(e) *)
      rewrite !int_of_w32K.
      forward_call (int_of_w32 we, int_of_w32 wf, int_of_w32 wg).  (* t'8 = Ch(e, f, g) *)
      rewrite !int_of_w32K.
      forward.                                                     (* t'19 = sha256_K[t] *)
      { rewrite (HKv i Hi64).
        entailer!. }
      rewrite (HKv i Hi64).
      forward.                            (* T1 = h + t'7 + t'8 + t'19 + w *)
      forward_call (int_of_w32 wa).                                (* t'9 = Sigma0(a) *)
      rewrite !int_of_w32K.
      forward_call (int_of_w32 wa, int_of_w32 wb, int_of_w32 wc).  (* t'10 = Maj(a, b, c) *)
      rewrite !int_of_w32K.
      forward.                            (* T2 = t'9 + t'10 *)
      forward.                            (* h = g *)
      forward.                            (* g = f *)
      forward.                            (* f = e *)
      forward.                            (* e = d + T1 *)
      forward.                            (* d = c *)
      forward.                            (* c = b *)
      forward.                            (* b = a *)
      forward.                            (* a = T1 + T2 *)
      rewrite !int_add_of_w32.
      (* The same rotation as loop 2 (a := T1 + T2, e := d + T1, the
         other six shift down), plus a ninth witness the earlier loop
         did not need: W with slot [i mod 16] overwritten by the
         schedule word this iteration just built. W[t] is
         [nth (schedule Ms) t] here, not [nth Ms t] -- past t = 16 the
         two part company. *)
      Exists (upd_Znth (i mod 16) Wv
                (Vint (int_of_w32 (nth w32_0 (schedule Ms) (Z.to_nat i)))))
             ((wh + Sigma1 we + Ch we wf wg + nth w32_0 K (Z.to_nat i)
               + nth w32_0 (schedule Ms) (Z.to_nat i))
              + (Sigma0 wa + Maj wa wb wc))%R
             wa wb wc
             (wd + (wh + Sigma1 we + Ch we wf wg + nth w32_0 K (Z.to_nat i)
                    + nth w32_0 (schedule Ms) (Z.to_nat i)))%R
             we wf wg.
      entailer!.
      split.
      { (* the window slid by one: u = t was admitted, u = t-16 retired *)
        intros u Hu.
        assert (Hmu : 0 <= u mod 16 < 16) by (apply Z.mod_pos_bound; lia).
        destruct (Z.eq_dec u i) as [Heq|Hne].
        - (* the slot just written *)
          rewrite Heq.
          rewrite upd_Znth_same.
          + lia.
          + reflexivity.
        - (* every other slot is untouched, by [mod16_neq] *)
          rewrite upd_Znth_diff.
          + lia.
          + lia.
          + apply mod16_neq.
            lia.
          + apply HWin.
            lia. }
      (* and one more round of the fold *)
      assert (Hn1 : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
      rewrite Hn1.
      rewrite (roundsS Hs Ms (Z.to_nat i) Hlt64 HMn).
      rewrite Hst.
      reflexivity.

    (* ===== SS 6.2.2 step 4 -- straight line ===== *)
    (* H[k] = <working variable k> + H[k] for k = 0..7: the sixty-four
       rounds' output added into the incoming chaining value. *)
    * Intros Wv wa wb wc wd we wf wg wh.
      rename H into HWz.
      rename H0 into HWin.
      rename H1 into Hst64.
      (* The window has done its job, since step 4 never reads W. With
         [HWin] gone, [schedule Ms] is absent from the sixteen
         [forward]s below. [HWz] stays: floyd wants the length to
         retire the local array at function exit. *)
      clear HWin Hpre HMv HKv.
      rewrite (words_to_vals_8 Hs HHn).
      forward.                            (* t'18 = H[0] *)
      forward.                            (* H[0] = a + t'18 *)
      forward.                            (* t'17 = H[1] *)
      forward.                            (* H[1] = b + t'17 *)
      forward.                            (* t'16 = H[2] *)
      forward.                            (* H[2] = c + t'16 *)
      forward.                            (* t'15 = H[3] *)
      forward.                            (* H[3] = d + t'15 *)
      forward.                            (* t'14 = H[4] *)
      forward.                            (* H[4] = e + t'14 *)
      forward.                            (* t'13 = H[5] *)
      forward.                            (* H[5] = f + t'13 *)
      forward.                            (* t'12 = H[6] *)
      forward.                            (* H[6] = g + t'12 *)
      forward.                            (* t'11 = H[7] *)
      forward.                            (* H[7] = h + t'11 *)
      (* sixty-four rounds have run, so the loop's fold IS [rounds] *)
      assert (Hrounds : rounds Hs Ms = (wa, wb, wc, wd, we, wf, wg, wh)).
      { rewrite (rounds_uptoE Hs Ms HMn).
        exact Hst64. }
      rewrite !int_add_of_w32.
      rewrite (compress_words_vals Hs Ms wa wb wc wd we wf wg wh HHn Hrounds).
      entailer!.
Qed.
