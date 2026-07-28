(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.repro_hop

    Hop 3 of the FXMSS EU-CMA chain: the digest-reprogramming hop,
    consuming HBS.toolkit.ROPlus's
    [RO_repro] game pair through HBS.toolkit.Reprogram's
    [Repro_bound].

    ** The FORGE-oracle bound

    An unbounded FORGE oracle would perform an unbounded number of lazy
    random-oracle reads and make any finite reprogramming bound false:

    - Reduction-side: every shared-RO read of the game must be
      forwarded to [RO_repro]'s QUERY (serving any read from local
      state desynchronizes exactly on the reprogramming-detection
      events the hop is supposed to bound), and QUERY is capped at
      [qh]; unboundedly many FORGE calls exceed every cap.
    - Game-side (the real attack): an adversary calling FORGE K
      times on one message [m] with K distinct randomness values
      r_1..r_K plants K rom entries (r_i, (pk, (zi, m))) whose
      values correlate with the K returned verdict bits.  A
      subsequent SIGN(m) at leaf zi hits a planted prefix with
      probability K/|R|, and the planted-vs-fresh digest is then
      detectable through the verdict bit correlation.  With K
      unbounded the distinguishing advantage between "SIGN reads
      the shared rom" and "SIGN's digest is fresh" approaches a
      constant — no bound of the form qp*qh'/|R| with finite qh'
      can hold.

    The EU-CMA security game bounds FORGE by [q_f]; [q_f := 1] recovers
    the paper experiment's single forgery output. Its verification
    random-oracle read is counted in the reprogramming query budget.

    The hop therefore uses the FORGE-budgeted pair

      [G2c] := G2f + FORGE budget [q_f] (counter [shrincs_fxmss_fcnt_loc],
               location 408; q_f := 1 recovers the tex experiment),
      [G3c] := the reprogrammed game (below),

    where [G2c] is the budgeted [G2f]. All
    later hops (4-9) inherit the budgeted FORGE; the digest-collision
    bound of hop 4 NEEDS the same budget (its abort event is
    per-FORGE-call), so the budget is not an artifact of this hop.

    ** The games and the reduction

    - [G2c] (real side): SIGN's randomness comes from the lazy table
      [shrincs_fxmss_rt_loc] at key (leaf id, message); the digest is the
      shared lazy rom at ((r, (pk, (leaf id, m)))).
    - [G3c] (ideal side): on a TABLE MISS, SIGN samples a fresh
      [r ← dR] and a fresh digest [md ← dD] and OVERWRITES the rom
      at (r, x) — the digest is decoupled from the adversary's
      prior HASH queries (the reprogramming).  On a table hit
      (repeated (leaf id, m), only reachable by re-asking a refused
      query) the cached (r, digest) is reused via the rom exactly
      as in G2c, which is what keeps refusal semantics
      deterministic (the proof architecture hop-2 discussion).
    - [R_rep b : package (I_RO R XSuf D) I_G0f]: HASH forwards to
      QUERY; SIGN's table miss calls REPRO (fresh r; the true game
      reprograms (r, x)) and then QUERY to read the digest; the
      table hit calls QUERY only; FORGE's single digest
      recomputation is a QUERY.  Budgets: [qp := q_s] REPRO calls
      (one per table miss <= one per SIGN call),
      [qh' := q_h + q_s + q_f] QUERY calls (HASH + SIGN + FORGE,
      each gated by its own counter).

    ** Statements

    - [R_rep_real  b : perfect IG (G2c b) (R_rep b ∘ ROG false)]
    - [R_rep_ideal b : perfect IG (G3c b) (R_rep b ∘ ROG true)]
      (both for ARBITRARY samplers dR/dD — the perfect halves are
      sampler-agnostic)
    - [Repro_hop_Adv b A : Adv (G2c b) (G3c b) A
                           = AdvOf (ROG) (A ∘ R_rep b)]
    - [Repro_hop b A : Adv (G2c b) (G3c b) A
         <= q_s%:R * ((q_h + q_s + q_f + q_s.-1)%:R / r.+1%:R)]
      at [Repro_bound]'s documented scope: R := 'fin r.+1 with the
      uniform sampler [rp_dPfx r], and [LosslessCode dD] (the
      side-condition parameters of the hop; the proof architecture "Side
      conditions").

    Locations: G2c/G3c reuse Games.v's 400-407 plus [shrincs_fxmss_fcnt_loc]
    408; the reduction mirrors at 480-486.

    Style: prf_hop.v (block preconditions, one-sided bind-spine
    rules, manual put-chain restorations). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import reals.
From HBS Require Import prelude math.bin_tree math.merkle sig.scheme
  games.thf toolkit.sample_seq toolkit.ro_plus toolkit.reprogram.
From HBS Require Import wots.games wots.ud_hop
  wots.tcr_hop wots.pre_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.prf_hop.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic helpers *)

(** Re-storing a present binding is the identity (the lazy-rom
    "re-store on hit" of the games versus QUERY's "no write on hit"
    of the oracle). *)
Lemma setm_same {T : ordType} {S : Type} {m : {fmap T -> S}} {k : T}
    {v : S} :
  getm m k = Some v -> setm m k v = m.
Proof.
by move=> e; apply/eq_fmap => k'; rewrite setmE; case: eqP => [-> | //];
  rewrite e.
Qed.

(** Non-dependent instance of [code_link_assertD] ([#assert b ;; c]
    hides the unused binder, which vanilla [rewrite] cannot match
    higher-order). *)
Lemma code_link_assert {A : choice_type} (b : bool) (c : raw_code A) p :
  code_link (#assert b ;; c) p = (#assert b ;; code_link c p).
Proof. exact: (code_link_assertD A b (λ _, c) p). Qed.

(** Budget arithmetic: a sum of three gated counters stays below the
    sum of the three budgets when one is strictly below its budget. *)
Lemma leq_add3_ltn_l (a b c qa qb qc : nat) :
  (a < qa)%N -> (b <= qb)%N -> (c <= qc)%N ->
  (a + b + c < qa + qb + qc)%N.
Proof.
move=> ha hb hc; have h := leq_add (leq_add ha hb) hc.
by rewrite !addSn in h.
Qed.

Lemma leq_add3_ltn_m (a b c qa qb qc : nat) :
  (a <= qa)%N -> (b < qb)%N -> (c <= qc)%N ->
  (a + b + c < qa + qb + qc)%N.
Proof.
move=> ha hb hc; have h := leq_add (leq_add ha hb) hc.
by rewrite addnS addSn in h.
Qed.

Lemma leq_add3_ltn_r (a b c qa qb qc : nat) :
  (a <= qa)%N -> (b <= qb)%N -> (c < qc)%N ->
  (a + b + c < qa + qb + qc)%N.
Proof.
move=> ha hb hc; have h := leq_add (leq_add ha hb) hc.
by rewrite addnS in h.
Qed.

Section FXMSSReproHop.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same section context as fxmss.games minus the PRFs and their key
    spaces (gone after hops 1-2), plus the FORGE budget [q_f]
    (header).  The samplers are arbitrary here; the bound section
    below instantiates [R]/[dR] to [Repro_bound]'s scope. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(* ------------------------------------------------------------------ *)
(** ** Shorthands *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).
Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation FXST := (shrincs_fxmss_game_state PP N).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).
Local Notation fxsignx :=
  (shrincs_fxmss_sign_x PP N D R F Tl Hgrind Htree S_wn c_max h_sf).
Local Notation fxvermd :=
  (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation skeys := (@sample_keys l N dN).

Local Notation Lst := (shrincs_fxmss_st_loc PP N).
Local Notation Llog := (shrincs_fxmss_log_loc M).
Local Notation Lrom := (shrincs_fxmss_rom_loc PP N D M R).
Local Notation Lrt := (shrincs_fxmss_rt_loc M R).

(** The RO suffix space (REPRO's argument): the full Hmsg^sf input
    minus the randomness prefix; [ROIN = R × XSuf]. *)
Definition XSuf : choice_type := (PP × N) × (('nat × 'nat) × M).

(** QUERY budget of the repro instance: every shared-rom read of the
    game is one QUERY — [q_h] HASH reads + [q_s] SIGN reads + [q_f]
    FORGE reads, each gated by its own counter (header). *)
Definition qh' : nat := q_h + q_s + q_f.

Local Notation Lmap := (ro_map_loc R XSuf D).
Local Notation Lqc := ro_qcnt_loc.
Local Notation Lrc := ro_rcnt_loc.
Local Notation ROG b' := (RO_repro R XSuf D dR dD qh' q_s b').
Local Notation IRO := (I_RO R XSuf D).

(** The FORGE budget counter (the +1 over Games.v's 400-407) is
    [shrincs_fxmss_fcnt_loc] (408), imported from [fxmss.games] (no local
    redefinition: this file already [Require Import]s it, see
    proof/LOCATIONS.md). *)

(* ------------------------------------------------------------------ *)
(** ** G2c / G3c: named oracle bodies + DIRECTED assembly

    The lifted used-set SIGN body defeats the plain [package] TC search
    (>30-min wall; the kernel-cost analysis).  Each oracle is a named definition
    with a hand-proved [ValidCode] instance, assembled by the directed
    [valid_package_cons] idiom (peel FORGE->HASH->SIGN->GEN), exactly as
    Games.v and prf_hop.v do.  GEN/HASH/FORGE are shared between G2c/G3c
    ([gc_*]); the SIGN bodies differ ([g2c_sign_body] table-lazy vs
    [g3c_sign_body] reprogrammed). *)

Definition Gc_locs : Locations :=
  [fmap Lst ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ;
        shrincs_fxmss_hcnt_loc ; Lrt ; shrincs_fxmss_fcnt_loc ].

Definition gc_gen_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   #put Lst := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   ret (pp, fxroot pp sp xss)).

Definition g2c_sign_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     r ← (match getm tb (mz.2, mz.1) with
          | Some r => ret r
          | None => r ← dR ;; ret r
          end) ;;
     #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
     #put Lrt := setm tb (mz.2, mz.1) r ;;
     md ← (match getm mp (r, (st.1, (mz.2, mz.1))) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
     match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
     | Some sg =>
         #put Llog := rcons lg mz.1 ;;
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret (Some sg)
     | None =>
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

Definition g3c_sign_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     match getm tb (mz.2, mz.1) with
     | Some r =>
         #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
         #put Lrt := setm tb (mz.2, mz.1) r ;;
         md ← (match getm mp (r, (st.1, (mz.2, mz.1))) with
               | Some d => ret d
               | None => d ← dD ;; ret d
               end) ;;
         #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put Llog := rcons lg mz.1 ;;
             #put shrincs_fxmss_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put shrincs_fxmss_scnt_loc := sc.+1 ;;
             ret None
         end
     | None =>
         r ← dR ;;
         md ← dD ;;
         #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
         #put Lrt := setm tb (mz.2, mz.1) r ;;
         #put Lrom := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put Llog := rcons lg mz.1 ;;
             #put shrincs_fxmss_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put shrincs_fxmss_scnt_loc := sc.+1 ;;
             ret None
         end
     end
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

Definition gc_hash_body (x : ROIN) : raw_code D :=
  (hc ← get shrincs_fxmss_hcnt_loc ;;
   #assert (hc < q_h)%N ;;
   mp ← get Lrom ;;
   md ← (match getm mp x with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp x md ;;
   #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
   ret md).

Definition gc_forge_body (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get shrincs_fxmss_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put shrincs_fxmss_fcnt_loc := fc.+1 ;;
   ret (if b then
          fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
          && (m \notin lg)
        else false)).

#[export] Instance gc_gen_body_valid (I : Interface) (sp : 'list 'bool) :
  ValidCode Gc_locs I (gc_gen_body sp).
Proof.
rewrite /gc_gen_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance gc_hash_body_valid (I : Interface) (x : ROIN) :
  ValidCode Gc_locs I (gc_hash_body x).
Proof.
rewrite /gc_hash_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance gc_forge_body_valid (I : Interface) (b : bool)
    (m : M) (sg : FXSIG) :
  ValidCode Gc_locs I (gc_forge_body b m sg).
Proof.
rewrite /gc_forge_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance g2c_sign_body_valid (I : Interface)
    (mz : M × ('nat × 'nat)) :
  ValidCode Gc_locs I (g2c_sign_body mz).
Proof.
rewrite /g2c_sign_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_bind.
  case: (getm tb _) => [r|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> r; apply valid_ret.
move=> r.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
case: (fxsignx _ _ _ _ _ _) => [sg|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  apply valid_ret.
- eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance g3c_sign_body_valid (I : Interface)
    (mz : M × ('nat × 'nat)) :
  ValidCode Gc_locs I (g3c_sign_body mz).
Proof.
rewrite /g3c_sign_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
case: (getm tb _) => [r|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_bind.
    case: (getm mp _) => [d|]; first by apply valid_ret.
    by eapply valid_bind; first eapply valid_scheme, prog_valid;
       move=> d; apply valid_ret.
  move=> md.
  eapply valid_putr; first by fmap_solve.
  case: (fxsignx _ _ _ _ _ _) => [sg|].
  + eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve.
    apply valid_ret.
  + eapply valid_putr; first by fmap_solve. apply valid_ret.
- eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> r.
  eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> md.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  case: (fxsignx _ _ _ _ _ _) => [sg|].
  + eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve.
    apply valid_ret.
  + eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

Definition G2c (b : bool) : game IG.
Proof.
notypeclasses refine [package Gc_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { gc_gen_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      g2c_sign_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { gc_hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { gc_forge_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: gc_forge_body_valid. } }
    { intros x; exact: gc_hash_body_valid. } }
  { intro mz; exact: g2c_sign_body_valid. } }
{ intro sp; exact: gc_gen_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** G3c: digests reprogrammed (the post-hop game)

    Only SIGN differs from G2c: on a table miss the digest is a
    FRESH uniform stored over (rather than read from) the rom at
    the fresh point (r, x) (header). *)

Definition G3c (b : bool) : game IG.
Proof.
notypeclasses refine [package Gc_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { gc_gen_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      g3c_sign_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { gc_hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { gc_forge_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: gc_forge_body_valid. } }
    { intros x; exact: gc_hash_body_valid. } }
  { intro mz; exact: g3c_sign_body_valid. } }
{ intro sp; exact: gc_gen_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** The reduction *)

Definition rr_st_loc := mkloc 480 (None : option FXST).
Definition rr_used_loc := mkloc 481 (emptym : chMap ('nat × 'nat) 'unit).
Definition rr_scnt_loc := mkloc 482 (0 : 'nat).
Definition rr_log_loc := mkloc 483 ([::] : seq M).
Definition rr_hcnt_loc := mkloc 484 (0 : 'nat).
Definition rr_rt_loc := mkloc 485 (emptym : chMap (('nat × 'nat) × M) R).
Definition rr_fcnt_loc := mkloc 486 (0 : 'nat).

Definition Rr_locs : Locations :=
  [fmap rr_st_loc ; rr_used_loc ; rr_scnt_loc ; rr_log_loc ;
        rr_hcnt_loc ; rr_rt_loc ; rr_fcnt_loc ].

Definition rr_gen_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get rr_st_loc ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   #put rr_st_loc := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   ret (pp, fxroot pp sp xss)).

Definition rr_sign_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get rr_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome rr_st_loc ;;
   us ← get rr_used_loc ;;
   lg ← get rr_log_loc ;;
   tb ← get rr_rt_loc ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     match getm tb (mz.2, mz.1) with
     | Some r =>
         #put rr_used_loc := setm us mz.2 Datatypes.tt ;;
         #put rr_rt_loc := setm tb (mz.2, mz.1) r ;;
         md ← (call [ QUERY ] : { R × XSuf ~> D }
                 (r, (st.1, (mz.2, mz.1)))) ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put rr_log_loc := rcons lg mz.1 ;;
             #put rr_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put rr_scnt_loc := sc.+1 ;;
             ret None
         end
     | None =>
         r ← (call [ REPRO ] : { XSuf ~> R }
                (st.1, (mz.2, mz.1))) ;;
         #put rr_used_loc := setm us mz.2 Datatypes.tt ;;
         #put rr_rt_loc := setm tb (mz.2, mz.1) r ;;
         md ← (call [ QUERY ] : { R × XSuf ~> D }
                 (r, (st.1, (mz.2, mz.1)))) ;;
         match fxsignx st.1.1 st.2.1 st.2.2 (flidx st.2.1 mz.2) r md with
         | Some sg =>
             #put rr_log_loc := rcons lg mz.1 ;;
             #put rr_scnt_loc := sc.+1 ;;
             ret (Some sg)
         | None =>
             #put rr_scnt_loc := sc.+1 ;;
             ret None
         end
     end
   else
     #put rr_scnt_loc := sc.+1 ;;
     ret None).

Definition rr_hash_body (x : ROIN) : raw_code D :=
  (hc ← get rr_hcnt_loc ;;
   #assert (hc < q_h)%N ;;
   md ← (call [ QUERY ] : { R × XSuf ~> D } x) ;;
   #put rr_hcnt_loc := hc.+1 ;;
   ret md).

Definition rr_forge_body (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get rr_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome rr_st_loc ;;
   lg ← get rr_log_loc ;;
   md ← (call [ QUERY ] : { R × XSuf ~> D }
           (sg.1.2, (st.1, (sg.1.1, m)))) ;;
   #put rr_fcnt_loc := fc.+1 ;;
   ret (if b then
          fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
          && (m \notin lg)
        else false)).

#[export] Instance rr_gen_body_valid (sp : 'list 'bool) :
  ValidCode Rr_locs IRO (rr_gen_body sp).
Proof.
rewrite /rr_gen_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rr_hash_body_valid (x : ROIN) :
  ValidCode Rr_locs IRO (rr_hash_body x).
Proof.
rewrite /rr_hash_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_opr; first by fmap_solve. move=> md.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rr_forge_body_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode Rr_locs IRO (rr_forge_body b m sg).
Proof.
rewrite /rr_forge_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_opr; first by fmap_solve. move=> md.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance rr_sign_body_valid (mz : M × ('nat × 'nat)) :
  ValidCode Rr_locs IRO (rr_sign_body mz).
Proof.
rewrite /rr_sign_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> tb.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
case: (getm tb _) => [r|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_opr; first by fmap_solve. move=> md.
  case: (fxsignx _ _ _ _ _ _) => [sg|].
  + eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve.
    apply valid_ret.
  + eapply valid_putr; first by fmap_solve. apply valid_ret.
- eapply valid_opr; first by fmap_solve. move=> r.
  eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  eapply valid_opr; first by fmap_solve. move=> md.
  case: (fxsignx _ _ _ _ _ _) => [sg|].
  + eapply valid_putr; first by fmap_solve.
    eapply valid_putr; first by fmap_solve.
    apply valid_ret.
  + eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

Definition R_rep (b : bool) : package IRO IG.
Proof.
notypeclasses refine [package Rr_locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) { rr_gen_body sp } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      rr_sign_body mz } ;
    [ FXHASH ] : { ROIN ~> D } (x) { rr_hash_body x } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) { rr_forge_body b m sg }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: rr_forge_body_valid. } }
    { intros x; exact: rr_hash_body_valid. } }
  { intro mz; exact: rr_sign_body_valid. } }
{ intro sp; exact: rr_gen_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Resolved oracle bodies (computed once; Reprogram.v pattern) *)

Definition qo : opsig := (QUERY, (R × XSuf, D)).
Definition rpo : opsig := (REPRO, (XSuf, R)).

Lemma resolve_Q (b' : bool) (p : R × XSuf) :
  resolve (ROG b') qo p =
  (qc ← get Lqc ;;
   #assert (qc < qh')%N ;;
   #put Lqc := qc.+1 ;;
   m ← get Lmap ;;
   match getm m p with
   | Some y => ret y
   | None =>
       y ← dD ;;
       #put Lmap := setm m p y ;;
       ret y
   end).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

Lemma resolve_R_f (x : XSuf) :
  resolve (ROG false) rpo x =
  (rc ← get Lrc ;;
   #assert (rc < q_s)%N ;;
   #put Lrc := rc.+1 ;;
   r ← dR ;;
   ret r).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

Lemma resolve_R_t (x : XSuf) :
  resolve (ROG true) rpo x =
  (rc ← get Lrc ;;
   #assert (rc < q_s)%N ;;
   #put Lrc := rc.+1 ;;
   r ← dR ;;
   m ← get Lmap ;;
   y ← dD ;;
   #put Lmap := setm m (r, x) y ;;
   ret r).
Proof. by rewrite /RO_repro /resolve /= coerce_kleisliE. Qed.

(* Keep the packages and the pure layer folded under [simpl] from
   here on (PRFHop discipline). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments RO_repro : simpl never.
#[local] Arguments shrincs_fxmss_sign_x : simpl never.
#[local] Arguments shrincs_fxmss_verify_md : simpl never.
#[local] Arguments shrincs_fxmss_root_x : simpl never.
#[local] Arguments shrincs_fxmss_shape : simpl never.
#[local] Arguments shrincs_fxmss_sign_path : simpl never.
#[local] Arguments shrincs_fxmss_pos_id : simpl never.
#[local] Arguments leaf_paths : simpl never.
#[local] Arguments setm : simpl never.
#[local] Arguments getm : simpl never.
#[local] Arguments emptym : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The invariant (shared by BOTH perfect lemmas)

    Mirrors: every lhs game location against its reduction twin; the
    lhs rom against the repro game's map (EXACT map equality — the
    games re-store on a hit where QUERY does not write, bridged by
    [setm_same]).  Numerics: the repro game's counters against the
    reduction's gated counters —

      qc <= hc + sc + fc   (one QUERY per HASH/SIGN/FORGE entry),
      rc <= sc             (one REPRO per SIGN table miss),

    which together with the budget caps hc <= q_h, sc <= q_s,
    fc <= q_f discharge QUERY's [qc < qh'] and REPRO's [rc < q_s]
    asserts (the budget lemmas above). *)

Definition RTKey : choice_type := ('nat × 'nat) × M.

Definition R3 (sto : option FXST) (usv : chMap ('nat × 'nat) 'unit)
    (sc : nat) (lg : seq M)
    (rm : {fmap ROIN -> D}) (hc : nat) (tb : {fmap RTKey -> R}) (fc : nat)
    (sto' : option FXST) (usv' : chMap ('nat × 'nat) 'unit) (sc' : nat)
    (lg' : seq M) (hc' : nat)
    (tb' : {fmap RTKey -> R}) (fc' : nat)
    (Mv : {fmap ROIN -> D}) (qc rc : nat) : Prop :=
  [/\ [/\ sto' = sto, usv' = usv, sc' = sc, lg' = lg & hc' = hc],
      [/\ tb' = tb, fc' = fc & Mv = rm],
      [/\ (qc <= hc + sc + fc)%N & (rc <= sc)%N]
    & [/\ (hc <= q_h)%N, (sc <= q_s)%N & (fc <= q_f)%N]].

Definition L3 : Locations :=
  [fmap Lst ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ; shrincs_fxmss_hcnt_loc ; Lrt ;
        shrincs_fxmss_fcnt_loc ;
        rr_st_loc ; rr_used_loc ; rr_scnt_loc ; rr_log_loc ; rr_hcnt_loc ;
        rr_rt_loc ; rr_fcnt_loc ; Lmap ; Lqc ; Lrc ].

Definition inv3 : precond :=
  heap_ignore L3
  ⋊ rel_app [:: (lhs, Lst) ; (lhs, shrincs_fxmss_used_loc) ; (lhs, shrincs_fxmss_scnt_loc) ;
                (lhs, Llog) ; (lhs, Lrom) ; (lhs, shrincs_fxmss_hcnt_loc) ;
                (lhs, Lrt) ; (lhs, shrincs_fxmss_fcnt_loc) ;
                (rhs, rr_st_loc) ; (rhs, rr_used_loc) ; (rhs, rr_scnt_loc) ;
                (rhs, rr_log_loc) ; (rhs, rr_hcnt_loc) ; (rhs, rr_rt_loc) ;
                (rhs, rr_fcnt_loc) ; (rhs, Lmap) ; (rhs, Lqc) ;
                (rhs, Lrc) ] R3.

Arguments inv3 : simpl never.

Lemma inv3E s0 s1 :
  inv3 (s0, s1) ->
  heap_ignore L3 (s0, s1) /\
  R3 (get_heap s0 Lst) (get_heap s0 shrincs_fxmss_used_loc) (get_heap s0 shrincs_fxmss_scnt_loc)
     (get_heap s0 Llog) (get_heap s0 Lrom) (get_heap s0 shrincs_fxmss_hcnt_loc)
     (get_heap s0 Lrt) (get_heap s0 shrincs_fxmss_fcnt_loc)
     (get_heap s1 rr_st_loc) (get_heap s1 rr_used_loc)
     (get_heap s1 rr_scnt_loc) (get_heap s1 rr_log_loc)
     (get_heap s1 rr_hcnt_loc) (get_heap s1 rr_rt_loc)
     (get_heap s1 rr_fcnt_loc)
     (get_heap s1 Lmap) (get_heap s1 Lqc) (get_heap s1 Lrc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma inv3I s0 s1 :
  heap_ignore L3 (s0, s1) ->
  R3 (get_heap s0 Lst) (get_heap s0 shrincs_fxmss_used_loc) (get_heap s0 shrincs_fxmss_scnt_loc)
     (get_heap s0 Llog) (get_heap s0 Lrom) (get_heap s0 shrincs_fxmss_hcnt_loc)
     (get_heap s0 Lrt) (get_heap s0 shrincs_fxmss_fcnt_loc)
     (get_heap s1 rr_st_loc) (get_heap s1 rr_used_loc)
     (get_heap s1 rr_scnt_loc) (get_heap s1 rr_log_loc)
     (get_heap s1 rr_hcnt_loc) (get_heap s1 rr_rt_loc)
     (get_heap s1 rr_fcnt_loc)
     (get_heap s1 Lmap) (get_heap s1 Lqc) (get_heap s1 Lrc) ->
  inv3 (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** Block preconditions

    Explicit Prop preconditions for the segments after each oracle's
    get/assert preamble (PRFHop architecture: [rpre_weaken_rule]
    drops the rem-machinery, the leaves restore [inv3] manually).
    [cq]/[cr] are the mid-block slacks of the QUERY/REPRO counter
    bumps (restored by the final scnt/hcnt/fcnt increment). *)

(** GEN: nothing pinned (everything mirrored is untouched). *)
Definition B3G : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L3 (s0, s1),
          get_heap s1 rr_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rr_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc,
          get_heap s1 rr_log_loc = get_heap s0 Llog &
          get_heap s1 rr_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc],
      [/\ get_heap s1 rr_rt_loc = get_heap s0 Lrt,
          get_heap s1 rr_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc &
          get_heap s1 Lmap = get_heap s0 Lrom],
      [/\ (get_heap s1 Lqc
             <= get_heap s0 shrincs_fxmss_hcnt_loc + get_heap s0 shrincs_fxmss_scnt_loc
                + get_heap s0 shrincs_fxmss_fcnt_loc)%N
        & (get_heap s1 Lrc <= get_heap s0 shrincs_fxmss_scnt_loc)%N]
    & [/\ (get_heap s0 shrincs_fxmss_hcnt_loc <= q_h)%N,
          (get_heap s0 shrincs_fxmss_scnt_loc <= q_s)%N &
          (get_heap s0 shrincs_fxmss_fcnt_loc <= q_f)%N]].

Arguments B3G : simpl never.

(** SIGN: st/q/sc/log pinned both sides; lhs rom/rt and rhs map/rt
    pinned SEPARATELY (they diverge mid-block). *)
Definition S3 (stv : FXST) (usL usR : chMap ('nat × 'nat) 'unit)
    (sc : nat) (lg : seq M)
    (mpL mpR : {fmap ROIN -> D}) (tbL tbR : {fmap RTKey -> R})
    (cq cr : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L3 (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rr_st_loc = Some stv,
          get_heap s0 shrincs_fxmss_used_loc = usL &
          get_heap s1 rr_used_loc = usR],
      [/\ get_heap s0 shrincs_fxmss_scnt_loc = sc,
          get_heap s1 rr_scnt_loc = sc,
          get_heap s0 Llog = lg,
          get_heap s1 rr_log_loc = lg &
          get_heap s1 rr_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc],
      [/\ get_heap s0 Lrom = mpL,
          get_heap s1 Lmap = mpR,
          get_heap s0 Lrt = tbL,
          get_heap s1 rr_rt_loc = tbR &
          get_heap s1 rr_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      [/\ (get_heap s1 Lqc
             <= get_heap s0 shrincs_fxmss_hcnt_loc + sc + get_heap s0 shrincs_fxmss_fcnt_loc
                + cq)%N
        & (get_heap s1 Lrc <= sc + cr)%N]
    & [/\ (get_heap s0 shrincs_fxmss_hcnt_loc <= q_h)%N
        & (get_heap s0 shrincs_fxmss_fcnt_loc <= q_f)%N]].

Arguments S3 : simpl never.

(** HASH: budget counter and the two map views pinned. *)
Definition H3 (hcv : nat) (mpL mpR : {fmap ROIN -> D}) (cq : nat) :
    precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L3 (s0, s1),
          get_heap s1 rr_st_loc = get_heap s0 Lst,
          get_heap s1 rr_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rr_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc &
          get_heap s1 rr_log_loc = get_heap s0 Llog],
      [/\ get_heap s0 shrincs_fxmss_hcnt_loc = hcv,
          get_heap s1 rr_hcnt_loc = hcv,
          get_heap s0 Lrom = mpL &
          get_heap s1 Lmap = mpR],
      [/\ get_heap s1 rr_rt_loc = get_heap s0 Lrt &
          get_heap s1 rr_fcnt_loc = get_heap s0 shrincs_fxmss_fcnt_loc],
      [/\ (get_heap s1 Lqc
             <= hcv + get_heap s0 shrincs_fxmss_scnt_loc + get_heap s0 shrincs_fxmss_fcnt_loc
                + cq)%N
        & (get_heap s1 Lrc <= get_heap s0 shrincs_fxmss_scnt_loc)%N]
    & [/\ (get_heap s0 shrincs_fxmss_scnt_loc <= q_s)%N
        & (get_heap s0 shrincs_fxmss_fcnt_loc <= q_f)%N]].

Arguments H3 : simpl never.

(** FORGE (real branch): st/log and the FORGE counter pinned. *)
Definition F3 (stv : FXST) (lg : seq M) (mpL mpR : {fmap ROIN -> D})
    (fcv cq : nat) : precond :=
  λ '(s0, s1),
  [/\ [/\ heap_ignore L3 (s0, s1),
          get_heap s0 Lst = Some stv,
          get_heap s1 rr_st_loc = Some stv,
          get_heap s0 Llog = lg &
          get_heap s1 rr_log_loc = lg],
      [/\ get_heap s0 Lrom = mpL,
          get_heap s1 Lmap = mpR,
          get_heap s0 shrincs_fxmss_fcnt_loc = fcv &
          get_heap s1 rr_fcnt_loc = fcv],
      [/\ get_heap s1 rr_used_loc = get_heap s0 shrincs_fxmss_used_loc,
          get_heap s1 rr_scnt_loc = get_heap s0 shrincs_fxmss_scnt_loc,
          get_heap s1 rr_hcnt_loc = get_heap s0 shrincs_fxmss_hcnt_loc &
          get_heap s1 rr_rt_loc = get_heap s0 Lrt],
      [/\ (get_heap s1 Lqc
             <= get_heap s0 shrincs_fxmss_hcnt_loc + get_heap s0 shrincs_fxmss_scnt_loc + fcv
                + cq)%N
        & (get_heap s1 Lrc <= get_heap s0 shrincs_fxmss_scnt_loc)%N]
    & [/\ (get_heap s0 shrincs_fxmss_hcnt_loc <= q_h)%N
        & (get_heap s0 shrincs_fxmss_scnt_loc <= q_s)%N]].

Arguments F3 : simpl never.

(* ------------------------------------------------------------------ *)
(** ** Precondition transformers (one per mid-block heap write) *)

Lemma S3_set_qc stv usL usR sc lg mpL mpR tbL tbR cq cr (v : nat) s0 s1 :
  get_heap s1 Lqc = v ->
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL usR sc lg mpL mpR tbL tbR cq.+1 cr (s0, set_heap s1 Lqc v.+1).
Proof.
move=> hv [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
           [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split; last by rewrite get_set_heap_neq.
  by rewrite get_set_heap_eq addnS ltnS -hv.
- by split.
Qed.

Lemma S3_set_rc stv usL usR sc lg mpL mpR tbL tbR cq cr (v : nat) s0 s1 :
  get_heap s1 Lrc = v ->
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr.+1 (s0, set_heap s1 Lrc v.+1).
Proof.
move=> hv [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
           [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split; first by rewrite get_set_heap_neq.
  by rewrite get_set_heap_eq addnS ltnS -hv.
- by split.
Qed.

Lemma S3_set_M stv usL usR sc lg mpL mpR tbL tbR cq cr
    (mv : {fmap ROIN -> D}) s0 s1 :
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL usR sc lg mpL mv tbL tbR cq cr (s0, set_heap s1 Lmap mv).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
        [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split=> //.
  + by rewrite get_set_heap_eq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by split.
Qed.

Lemma S3_set_rtR stv usL usR sc lg mpL mpR tbL tbR cq cr
    (tv : {fmap RTKey -> R}) s0 s1 :
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL usR sc lg mpL mpR tbL tv cq cr (s0, set_heap s1 rr_rt_loc tv).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
        [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split=> //.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq.
  + by rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by split.
Qed.

Lemma S3_set_rtL stv usL usR sc lg mpL mpR tbL tbR cq cr
    (tv : {fmap RTKey -> R}) s0 s1 :
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL usR sc lg mpL mpR tv tbR cq cr (set_heap s0 Lrt tv, s1).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
        [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_lhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split=> //.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite !get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
Qed.

Lemma S3_set_romL stv usL usR sc lg mpL mpR tbL tbR cq cr
    (mv : {fmap ROIN -> D}) s0 s1 :
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL usR sc lg mv mpR tbL tbR cq cr (set_heap s0 Lrom mv, s1).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
        [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_lhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split=> //.
  + by rewrite get_set_heap_eq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite !get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
Qed.

(** The used-set writes (lhs game, rhs reduction).  Both sides write
    [setm us mz.2 tt] before the randomness table update; the pins for
    every other tracked location survive by [get_set_heap_neq]. *)
Lemma S3_set_usedL stv usL usR sc lg mpL mpR tbL tbR cq cr
    (v : chMap ('nat × 'nat) 'unit) s0 s1 :
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv v usR sc lg mpL mpR tbL tbR cq cr (set_heap s0 shrincs_fxmss_used_loc v, s1).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
        [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_lhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite !get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
Qed.

Lemma S3_set_usedR stv usL usR sc lg mpL mpR tbL tbR cq cr
    (v : chMap ('nat × 'nat) 'unit) s0 s1 :
  S3 stv usL usR sc lg mpL mpR tbL tbR cq cr (s0, s1) ->
  S3 stv usL v sc lg mpL mpR tbL tbR cq cr (s0, set_heap s1 rr_used_loc v).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
        [p15 p16] [p17 p18]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split.
Qed.

Lemma H3_set_qc hcv mpL mpR cq (v : nat) s0 s1 :
  get_heap s1 Lqc = v ->
  H3 hcv mpL mpR cq (s0, s1) ->
  H3 hcv mpL mpR cq.+1 (s0, set_heap s1 Lqc v.+1).
Proof.
move=> hv [[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10] [p11 p12] [p13 p14]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- split; last by rewrite get_set_heap_neq.
  by rewrite get_set_heap_eq addnS ltnS -hv.
- by split.
Qed.

Lemma H3_set_M hcv mpL mpR cq (mv : {fmap ROIN -> D}) s0 s1 :
  H3 hcv mpL mpR cq (s0, s1) ->
  H3 hcv mpL mv cq (s0, set_heap s1 Lmap mv).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10] [p11 p12] [p13 p14]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- split=> //.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_eq.
- by split; rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by split.
Qed.

Lemma F3_set_qc stv lg mpL mpR fcv cq (v : nat) s0 s1 :
  get_heap s1 Lqc = v ->
  F3 stv lg mpL mpR fcv cq (s0, s1) ->
  F3 stv lg mpL mpR fcv cq.+1 (s0, set_heap s1 Lqc v.+1).
Proof.
move=> hv [[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10 p11 p12] [p13 p14]
           [p15 p16]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- split; last by rewrite get_set_heap_neq.
  by rewrite get_set_heap_eq addnS ltnS -hv.
- by split.
Qed.

Lemma F3_set_M stv lg mpL mpR fcv cq (mv : {fmap ROIN -> D}) s0 s1 :
  F3 stv lg mpL mpR fcv cq (s0, s1) ->
  F3 stv lg mpL mv fcv cq (s0, set_heap s1 Lmap mv).
Proof.
move=> [[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10 p11 p12] [p13 p14]
        [p15 p16]].
split.
- split=> //.
  + by apply: heap_ignore_set_rhs hig; apply: fhas_in; fmap_solve.
  + by rewrite get_set_heap_neq.
  + by rewrite get_set_heap_neq.
- split=> //.
  + by rewrite get_set_heap_eq.
  + by rewrite get_set_heap_neq.
- by split=> //; rewrite get_set_heap_neq.
- by split; rewrite get_set_heap_neq.
- by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The shared SIGN tail

    After the randomness/digest are settled and all table/rom/map
    writes are done — with the two map views EQUAL again ([mp']) —
    the per-branch signing tails coincide. *)

Lemma r_sign_tail (stv : FXST) (usv : chMap ('nat × 'nat) 'unit)
    (idx sc : nat) (lg : seq M)
    (mp' : {fmap ROIN -> D}) (tb' : {fmap RTKey -> R}) (cr : nat)
    (m : M) (rv : R) (md : D) :
  (sc < q_s)%N ->
  (cr <= 1)%N ->
  ⊢ ⦃ λ '(s0, s1), S3 stv usv usv sc lg mp' mp' tb' tb' 1 cr (s0, s1) ⦄
     (match fxsignx stv.1.1 stv.2.1 stv.2.2 idx rv md with
      | Some sg =>
          #put Llog := rcons lg m ;;
          #put shrincs_fxmss_scnt_loc := sc.+1 ;;
          ret (Some sg)
      | None =>
          #put shrincs_fxmss_scnt_loc := sc.+1 ;;
          ret None
      end)
   ≈ (match fxsignx stv.1.1 stv.2.1 stv.2.2 idx rv md with
      | Some sg =>
          #put rr_log_loc := rcons lg m ;;
          #put rr_scnt_loc := sc.+1 ;;
          ret (Some sg)
      | None =>
          #put rr_scnt_loc := sc.+1 ;;
          ret None
      end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ inv3 (s0, s1) ⦄.
Proof.
move=> hsc hcr.
case Esig: (fxsignx stv.1.1 stv.2.1 stv.2.2 idx rv md) => [sg|].
- eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hp1 g1].
  case: hp1 => s1b [hp2 g2].
  case: hp2 => s0a [hp3 g3].
  case: hp3 => s0b [hblk g4].
  subst.
  split; first by [].
  case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
                [p15 p16] [p17 p18].
  apply: inv3I.
  + do 2 (apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve).
    do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
    exact: hig.
  + get_heap_simpl.
    rewrite ?p1 ?p2 ?p3 ?p4 ?p9 ?p10 ?p11 ?p12 ?p13 ?p14.
    split.
    * by split.
    * by split.
    * split.
      -- apply: (leq_trans p15).
         by rewrite addn1 addnS addSn leqnn.
      -- apply: (leq_trans p16).
         by rewrite -addn1 leq_add2l.
    * by split.
- eapply r_put_lhs.
  eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hp1 g1].
  case: hp1 => s0a [hblk g2].
  subst.
  split; first by [].
  case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
                [p15 p16] [p17 p18].
  apply: inv3I.
  + apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  + get_heap_simpl.
    rewrite ?p1 ?p2 ?p3 ?p4 ?p7 ?p8 ?p9 ?p10 ?p11 ?p12 ?p13 ?p14.
    split.
    * by split.
    * by split.
    * split.
      -- apply: (leq_trans p15).
         by rewrite addn1 addnS addSn leqnn.
      -- apply: (leq_trans p16).
         by rewrite -addn1 leq_add2l.
    * by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE real-side equivalence *)

Lemma R_rep_real (b : bool) :
  perfect IG (G2c b) (R_rep b ∘ ROG false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv3).
{ rewrite /inv3; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* FXGEN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 _.
  eapply r_assertD; first by [].
  move=> hcap _.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), B3G (s0, s1)); last first.
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv
      => hig [[e1 e2 e3 e4 e5] [e6 e7 e8] [e9 e10] [e11 e12 e13]].
    split.
    - by split.
    - by split.
    - by split.
    - by split. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dPP)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_scheme_bind (skeys (size (leaf_paths (tshape arg)))));
    first exact: sample_keys_valid.
  move=> xss; cbv beta.
  eapply r_put_lhs. eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hpre1 g1].
  case: hpre1 => s0a [hblk g2].
  subst.
  split; first by [].
  case: hblk => -[hig m1 m2 m3 m4] [m5 m6 m7] [m8 m9] [m10 m11 m12].
  apply: inv3I.
  + apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  + get_heap_simpl.
    split.
    * by split.
    * by split.
    * by split.
    * by split.
- (* FXSIGN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sc.
  eapply r_get_remember_rhs => sc'.
  eapply (r_fact (sc' = sc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [[_ _ e3 _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sc'.
  eapply r_assertD; first by [].
  move=> hsc _.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv3E: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => us'.
  eapply (r_fact (us' = us)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv3E: hinv => _ [[_ e2 _ _ _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst us'.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv3E: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_lhs => tb.
  eapply r_get_remember_rhs => tb'.
  eapply (r_fact (tb' = tb)).
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv3E: hinv => _ [_ [e6 _ _] _ _].
    rewrite /rem_inv /= in h9 h10.
    by rewrite -h9 -h10. }
  move=> e; subst tb'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), S3 stv us us sc lg mp mp tb tb 0 0 (s0, s1));
    last first.
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv3E: hinv
      => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] [f11 f12 f13]].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
    split.
    - by split.
    - by split.
    - split=> //.
      by rewrite f8 h8.
    - split.
      + by rewrite addn0 -h0.
      + by rewrite addn0 -h0.
    - by split. }
  case E: ([&& flok stv.2.1 arg.2 & arg.2 \notin domm us]); last first.
  + (* leaf schedule exhausted: burn the budget on both sides *)
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hpre1 g1].
    case: hpre1 => s0a [hblk g2].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
                  [p15 p16] [p17 p18].
    apply: inv3I.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p7 ?p8 ?p9 ?p10 ?p11 ?p12 ?p13 ?p14.
      split.
      -- by split.
      -- by split.
      -- split.
         ++ apply: (leq_trans p15).
            by rewrite addn0 addnS addSn leqnSn.
         ++ apply: (leq_trans p16).
            by rewrite addn0 leqnSn.
      -- by split.
  + (* leaf available *)
    case Etb: (getm tb (arg.2, arg.1)) => [r0|].
    * (* randomness table hit: QUERY only *)
      simpl.
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt) us sc lg mp mp
                     tb tb 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedL h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     tb tb 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedR h. }
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r0) tb 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtL h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r0)
                     (setm tb (arg.2, arg.1) r0) 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtR h. }
      eapply r_get_remember_rhs => qc.
      eapply (r_fact ((qc < qh')%N)).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        case: hblk => _ _ _ [b1 _] [b2 b3].
        rewrite hrem addn0 in b1.
        apply: leq_ltn_trans b1 _.
        exact: leq_add3_ltn_m b2 hsc b3. }
      move=> hqc.
      eapply r_bind_assertD_rhs.
      { by move=> ? ? _. }
      move=> _.
      eapply (r_put_bind_rhs Lqc qc.+1 _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r0)
                     (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        exact: S3_set_qc hrem hblk. }
      eapply (r_get_bind_rhs Lmap mp).
      { by move=> s0 s1 [_ _ [_ h _ _ _] _ _]. }
      cbv beta iota.
      simpl.
      case Emd: (getm mp (r0, (stv.1, (arg.2, arg.1))))
        => [d|].
      -- (* rom hit: QUERY answers from the map, the game re-stores *)
         simpl.
         rewrite (setm_same Emd).
         eapply (r_put_lhs_weak _ _ _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg mp mp
                        (setm tb (arg.2, arg.1) r0)
                        (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_romL h. }
         by apply: r_sign_tail.
      -- (* rom miss: the two lazy samples couple *)
         rewrite ?bind_assoc.
         simpl.
         eapply (r_scheme_bind dD); first exact: prog_valid.
         move=> d; cbv beta.
         eapply (r_put_rhs_weak Lmap
                   (setm mp (r0, (stv.1, (arg.2, arg.1))) d) _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg mp
                        (setm mp (r0, (stv.1, (arg.2, arg.1))) d)
                        (setm tb (arg.2, arg.1) r0)
                        (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_M h. }
         simpl.
         eapply (r_put_lhs_weak _ _ _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg
                        (setm mp (r0, (stv.1, (arg.2, arg.1))) d)
                        (setm mp (r0, (stv.1, (arg.2, arg.1))) d)
                        (setm tb (arg.2, arg.1) r0)
                        (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_romL h. }
         by apply: r_sign_tail.
    * (* randomness table miss: REPRO then QUERY *)
      simpl.
      eapply r_get_remember_rhs => rc.
      eapply (r_fact ((rc < q_s)%N)).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        case: hblk => _ _ _ [_ b1] _.
        rewrite hrem addn0 in b1.
        exact: leq_ltn_trans b1 hsc. }
      move=> hrc.
      eapply r_bind_assertD_rhs.
      { by move=> ? ? _. }
      move=> _.
      eapply (r_put_bind_rhs Lrc rc.+1 _
                (λ '(s0, s1), S3 stv us us sc lg mp mp tb tb 0 1 (s0, s1))).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        exact: S3_set_rc hrem hblk. }
      rewrite ?bind_assoc.
      simpl.
      eapply (r_scheme_bind dR); first exact: prog_valid.
      move=> r; cbv beta.
      simpl.
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt) us sc lg mp mp
                     tb tb 0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedL h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     tb tb 0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedR h. }
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r) tb 0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtL h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r)
                     (setm tb (arg.2, arg.1) r) 0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtR h. }
      eapply r_get_remember_rhs => qc.
      eapply (r_fact ((qc < qh')%N)).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        case: hblk => _ _ _ [b1 _] [b2 b3].
        rewrite hrem addn0 in b1.
        apply: leq_ltn_trans b1 _.
        exact: leq_add3_ltn_m b2 hsc b3. }
      move=> hqc.
      eapply r_bind_assertD_rhs.
      { by move=> ? ? _. }
      move=> _.
      eapply (r_put_bind_rhs Lqc qc.+1 _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r)
                     (setm tb (arg.2, arg.1) r) 1 1 (s0, s1))).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        exact: S3_set_qc hrem hblk. }
      eapply (r_get_bind_rhs Lmap mp).
      { by move=> s0 s1 [_ _ [_ h _ _ _] _ _]. }
      cbv beta iota.
      simpl.
      case Emd: (getm mp (r, (stv.1, (arg.2, arg.1))))
        => [d|].
      -- simpl.
         rewrite (setm_same Emd).
         eapply (r_put_lhs_weak _ _ _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg mp mp
                        (setm tb (arg.2, arg.1) r)
                        (setm tb (arg.2, arg.1) r) 1 1 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_romL h. }
         by apply: r_sign_tail.
      -- rewrite ?bind_assoc.
         simpl.
         eapply (r_scheme_bind dD); first exact: prog_valid.
         move=> d; cbv beta.
         eapply (r_put_rhs_weak Lmap
                   (setm mp (r, (stv.1, (arg.2, arg.1))) d) _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg mp
                        (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                        (setm tb (arg.2, arg.1) r)
                        (setm tb (arg.2, arg.1) r) 1 1 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_M h. }
         simpl.
         eapply (r_put_lhs_weak _ _ _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg
                        (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                        (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                        (setm tb (arg.2, arg.1) r)
                        (setm tb (arg.2, arg.1) r) 1 1 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_romL h. }
         by apply: r_sign_tail.
- (* FXHASH *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => hc.
  eapply r_get_remember_rhs => hc'.
  eapply (r_fact (hc' = hc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [[_ _ _ _ e5] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst hc'.
  eapply r_assertD; first by [].
  move=> hhc _.
  eapply r_get_remember_lhs => mp.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), H3 hc mp mp 0 (s0, s1)); last first.
  { move=> s0 s1 [[[hinv h0] h1] h2].
    case/inv3E: hinv
      => hig [[e1 e2 e3 e4 e5] [e6 e7 e8] [e9 e10] [e11 e12 e13]].
    rewrite /rem_inv /= in h0 h1 h2.
    split.
    - by split.
    - split=> //.
      by rewrite e8.
    - by split.
    - split=> //.
      by rewrite addn0 -h0.
    - by split. }
  eapply r_get_remember_rhs => qc.
  eapply (r_fact ((qc < qh')%N)).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    case: hblk => _ _ _ [b1 _] [b2 b3].
    rewrite hrem addn0 in b1.
    apply: leq_ltn_trans b1 _.
    exact: leq_add3_ltn_l hhc b2 b3. }
  move=> hqc.
  eapply r_bind_assertD_rhs.
  { by move=> ? ? _. }
  move=> _.
  eapply (r_put_bind_rhs Lqc qc.+1 _
            (λ '(s0, s1), H3 hc mp mp 1 (s0, s1))).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    exact: H3_set_qc hrem hblk. }
  eapply (r_get_bind_rhs Lmap mp).
  { by move=> s0 s1 [_ [_ _ _ h] _ _ _]. }
  cbv beta iota.
  simpl.
  case Emd: (getm mp arg) => [d|].
  + simpl.
    rewrite (setm_same Emd).
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10] [p11 p12]
                  [p13 p14].
    apply: inv3I.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p8 ?p9 ?p10.
      split.
      -- by split.
      -- by split.
      -- split.
         ++ apply: (leq_trans p11).
            by rewrite addn1 !addSn leqnn.
         ++ exact: p12.
      -- by split.
  + rewrite ?bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply (r_put_rhs_weak Lmap (setm mp arg d) _
              (λ '(s0, s1), H3 hc mp (setm mp arg d) 1 (s0, s1))).
    { move=> s0 s1 h; exact: H3_set_M h. }
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10] [p11 p12]
                  [p13 p14].
    apply: inv3I.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p8 ?p9 ?p10.
      split.
      -- by split.
      -- by split.
      -- split.
         ++ apply: (leq_trans p11).
            by rewrite addn1 !addSn leqnn.
         ++ exact: p12.
      -- by split.
- (* FXFORGE: bookkeeping is now b-unconditional (incl. the RHS QUERY
     counter machinery); the [if b] rides on the returned verdict,
     identical on both sides — a pure sync. *)
  case: arg => [m sg].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => fc.
  eapply r_get_remember_rhs => fc'.
  eapply (r_fact (fc' = fc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [_ [_ e7 _] _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst fc'.
  rewrite code_link_assert.
  eapply r_assertD; first by [].
  move=> hfc _.
  simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv3E: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  ssprove_code_simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv3E: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), F3 stv lg mp mp fc 0 (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[hinv h0] h1] h2] h3] h4] h5] h6].
    case/inv3E: hinv
      => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] [f11 f12 f13]].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6.
    split.
    - by split.
    - split=> //.
      by rewrite f8.
    - by split.
    - split=> //.
      by rewrite addn0 -h0.
    - by split. }
  eapply r_get_remember_rhs => qc.
  eapply (r_fact ((qc < qh')%N)).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    case: hblk => _ _ _ [b1 _] [b2 b3].
    rewrite hrem addn0 in b1.
    apply: leq_ltn_trans b1 _.
    exact: leq_add3_ltn_r b2 b3 hfc. }
  move=> hqc.
  eapply r_bind_assertD_rhs.
  { by move=> ? ? _. }
  move=> _.
  eapply (r_put_bind_rhs Lqc qc.+1 _
            (λ '(s0, s1), F3 stv lg mp mp fc 1 (s0, s1))).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    exact: F3_set_qc hrem hblk. }
  eapply (r_get_bind_rhs Lmap mp).
  { by move=> s0 s1 [_ [_ h _ _] _ _ _]. }
  cbv beta iota.
  simpl.
  case Emd: (getm mp (sg.1.2, (stv.1, (sg.1.1, m)))) => [d|].
  * simpl.
    rewrite (setm_same Emd).
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10 p11 p12]
                  [p13 p14] [p15 p16].
    apply: inv3I.
    -- apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
       do 2 (apply: heap_ignore_set_lhs;
             first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?p1 ?p2 ?p3 ?p4 ?p6 ?p9 ?p10 ?p11 ?p12.
       split.
       ++ by split.
       ++ by split.
       ++ split.
          ** apply: (leq_trans p13).
             by rewrite addn1 addnS leqnn.
          ** exact: p14.
       ++ by split.
  * rewrite ?bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply (r_put_rhs_weak Lmap (setm mp (sg.1.2, (stv.1, (sg.1.1, m))) d) _
              (λ '(s0, s1),
                 F3 stv lg mp (setm mp (sg.1.2, (stv.1, (sg.1.1, m))) d)
                   fc 1 (s0, s1))).
    { move=> s0 s1 h; exact: F3_set_M h. }
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10 p11 p12]
                  [p13 p14] [p15 p16].
    apply: inv3I.
    -- apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
       do 2 (apply: heap_ignore_set_lhs;
             first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?p1 ?p2 ?p3 ?p4 ?p6 ?p9 ?p10 ?p11 ?p12.
       split.
       ++ by split.
       ++ by split.
       ++ split.
          ** apply: (leq_trans p13).
             by rewrite addn1 addnS leqnn.
          ** exact: p14.
       ++ by split.
Qed.

(* ------------------------------------------------------------------ *)
(** ** THE ideal-side equivalence *)

Lemma R_rep_ideal (b : bool) :
  perfect IG (G3c b) (R_rep b ∘ ROG true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ inv3).
{ rewrite /inv3; ssprove_invariant => //. }
simplify_eq_rel arg.
- (* FXGEN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 _.
  eapply r_assertD; first by [].
  move=> hcap _.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), B3G (s0, s1)); last first.
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv
      => hig [[e1 e2 e3 e4 e5] [e6 e7 e8] [e9 e10] [e11 e12 e13]].
    split.
    - by split.
    - by split.
    - by split.
    - by split. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dPP)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_scheme_bind (skeys (size (leaf_paths (tshape arg)))));
    first exact: sample_keys_valid.
  move=> xss; cbv beta.
  eapply r_put_lhs. eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1a [hpre1 g1].
  case: hpre1 => s0a [hblk g2].
  subst.
  split; first by [].
  case: hblk => -[hig m1 m2 m3 m4] [m5 m6 m7] [m8 m9] [m10 m11 m12].
  apply: inv3I.
  + apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
    apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
    exact: hig.
  + get_heap_simpl.
    split.
    * by split.
    * by split.
    * by split.
    * by split.
- (* FXSIGN *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => sc.
  eapply r_get_remember_rhs => sc'.
  eapply (r_fact (sc' = sc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [[_ _ e3 _ _] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst sc'.
  eapply r_assertD; first by [].
  move=> hsc _.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv3E: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  eapply r_assertD; first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  eapply r_get_remember_lhs => us.
  eapply r_get_remember_rhs => us'.
  eapply (r_fact (us' = us)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv3E: hinv => _ [[_ e2 _ _ _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst us'.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7].
    case/inv3E: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h6 h7.
    by rewrite -h6 -h7. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply r_get_remember_lhs => tb.
  eapply r_get_remember_rhs => tb'.
  eapply (r_fact (tb' = tb)).
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv3E: hinv => _ [_ [e6 _ _] _ _].
    rewrite /rem_inv /= in h9 h10.
    by rewrite -h9 -h10. }
  move=> e; subst tb'.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), S3 stv us us sc lg mp mp tb tb 0 0 (s0, s1));
    last first.
  { move=> s0 s1 [[[[[[[[[[[hinv h0] h1] h2] h3] h4] h5] h6] h7] h8] h9] h10].
    case/inv3E: hinv
      => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] [f11 f12 f13]].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
    split.
    - by split.
    - by split.
    - split=> //.
      by rewrite f8 h8.
    - split.
      + by rewrite addn0 -h0.
      + by rewrite addn0 -h0.
    - by split. }
  case E: ([&& flok stv.2.1 arg.2 & arg.2 \notin domm us]); last first.
  + (* leaf schedule exhausted: burn the budget on both sides *)
    eapply r_put_lhs; eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hpre1 g1].
    case: hpre1 => s0a [hblk g2].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8 p9] [p10 p11 p12 p13 p14]
                  [p15 p16] [p17 p18].
    apply: inv3I.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve.
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p7 ?p8 ?p9 ?p10 ?p11 ?p12 ?p13 ?p14.
      split.
      -- by split.
      -- by split.
      -- split.
         ++ apply: (leq_trans p15).
            by rewrite addn0 addnS addSn leqnSn.
         ++ apply: (leq_trans p16).
            by rewrite addn0 leqnSn.
      -- by split.
  + (* leaf available *)
    case Etb: (getm tb (arg.2, arg.1)) => [r0|].
    * (* randomness table hit: QUERY only *)
      simpl.
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt) us sc lg mp mp
                     tb tb 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedL h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     tb tb 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedR h. }
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r0) tb 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtL h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r0)
                     (setm tb (arg.2, arg.1) r0) 0 0 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtR h. }
      eapply r_get_remember_rhs => qc.
      eapply (r_fact ((qc < qh')%N)).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        case: hblk => _ _ _ [b1 _] [b2 b3].
        rewrite hrem addn0 in b1.
        apply: leq_ltn_trans b1 _.
        exact: leq_add3_ltn_m b2 hsc b3. }
      move=> hqc.
      eapply r_bind_assertD_rhs.
      { by move=> ? ? _. }
      move=> _.
      eapply (r_put_bind_rhs Lqc qc.+1 _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp mp
                     (setm tb (arg.2, arg.1) r0)
                     (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        exact: S3_set_qc hrem hblk. }
      eapply (r_get_bind_rhs Lmap mp).
      { by move=> s0 s1 [_ _ [_ h _ _ _] _ _]. }
      cbv beta iota.
      simpl.
      case Emd: (getm mp (r0, (stv.1, (arg.2, arg.1))))
        => [d|].
      -- (* rom hit: QUERY answers from the map, the game re-stores *)
         simpl.
         rewrite (setm_same Emd).
         eapply (r_put_lhs_weak _ _ _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg mp mp
                        (setm tb (arg.2, arg.1) r0)
                        (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_romL h. }
         by apply: r_sign_tail.
      -- (* rom miss: the two lazy samples couple *)
         rewrite ?bind_assoc.
         simpl.
         eapply (r_scheme_bind dD); first exact: prog_valid.
         move=> d; cbv beta.
         eapply (r_put_rhs_weak Lmap
                   (setm mp (r0, (stv.1, (arg.2, arg.1))) d) _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg mp
                        (setm mp (r0, (stv.1, (arg.2, arg.1))) d)
                        (setm tb (arg.2, arg.1) r0)
                        (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_M h. }
         simpl.
         eapply (r_put_lhs_weak _ _ _
                   (λ '(s0, s1),
                      S3 stv (setm us arg.2 Datatypes.tt)
                        (setm us arg.2 Datatypes.tt) sc lg
                        (setm mp (r0, (stv.1, (arg.2, arg.1))) d)
                        (setm mp (r0, (stv.1, (arg.2, arg.1))) d)
                        (setm tb (arg.2, arg.1) r0)
                        (setm tb (arg.2, arg.1) r0) 1 0 (s0, s1))).
         { move=> s0 s1 h; exact: S3_set_romL h. }
         by apply: r_sign_tail.
    * (* randomness table miss: REPRO reprograms, QUERY reads it *)
      simpl.
      eapply r_get_remember_rhs => rc.
      eapply (r_fact ((rc < q_s)%N)).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        case: hblk => _ _ _ [_ b1] _.
        rewrite hrem addn0 in b1.
        exact: leq_ltn_trans b1 hsc. }
      move=> hrc.
      eapply r_bind_assertD_rhs.
      { by move=> ? ? _. }
      move=> _.
      eapply (r_put_bind_rhs Lrc rc.+1 _
                (λ '(s0, s1), S3 stv us us sc lg mp mp tb tb 0 1 (s0, s1))).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        exact: S3_set_rc hrem hblk. }
      rewrite ?bind_assoc.
      simpl.
      eapply (r_scheme_bind dR); first exact: prog_valid.
      move=> r; cbv beta.
      simpl.
      eapply (r_get_bind_rhs Lmap mp).
      { by move=> s0 s1 [_ _ [_ h _ _ _] _ _]. }
      rewrite ?bind_assoc.
      simpl.
      eapply (r_scheme_bind dD); first exact: prog_valid.
      move=> d; cbv beta.
      simpl.
      eapply (r_put_rhs_weak Lmap
                (setm mp (r, (stv.1, (arg.2, arg.1))) d) _
                (λ '(s0, s1),
                   S3 stv us us sc lg mp
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     tb tb 0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_M h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv us (setm us arg.2 Datatypes.tt) sc lg mp
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     tb tb 0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedR h. }
      eapply (r_put_rhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv us (setm us arg.2 Datatypes.tt) sc lg mp
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     tb (setm tb (arg.2, arg.1) r)
                     0 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtR h. }
      eapply r_get_remember_rhs => qc.
      eapply (r_fact ((qc < qh')%N)).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        case: hblk => _ _ _ [b1 _] [b2 b3].
        rewrite hrem addn0 in b1.
        apply: leq_ltn_trans b1 _.
        exact: leq_add3_ltn_m b2 hsc b3. }
      move=> hqc.
      eapply r_bind_assertD_rhs.
      { by move=> ? ? _. }
      move=> _.
      eapply (r_put_bind_rhs Lqc qc.+1 _
                (λ '(s0, s1),
                   S3 stv us (setm us arg.2 Datatypes.tt) sc lg mp
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     tb (setm tb (arg.2, arg.1) r)
                     1 1 (s0, s1))).
      { move=> s0 s1 [hblk hrem].
        rewrite /rem_inv /= in hrem.
        exact: S3_set_qc hrem hblk. }
      eapply (r_get_bind_rhs Lmap
                (setm mp (r, (stv.1, (arg.2, arg.1))) d)).
      { by move=> s0 s1 [_ _ [_ h _ _ _] _ _]. }
      cbv beta iota.
      rewrite setmE eqxx.
      simpl.
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     tb (setm tb (arg.2, arg.1) r)
                     1 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_usedL h. }
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg mp
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     (setm tb (arg.2, arg.1) r)
                     (setm tb (arg.2, arg.1) r)
                     1 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_rtL h. }
      eapply (r_put_lhs_weak _ _ _
                (λ '(s0, s1),
                   S3 stv (setm us arg.2 Datatypes.tt)
                     (setm us arg.2 Datatypes.tt) sc lg
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     (setm mp (r, (stv.1, (arg.2, arg.1))) d)
                     (setm tb (arg.2, arg.1) r)
                     (setm tb (arg.2, arg.1) r)
                     1 1 (s0, s1))).
      { move=> s0 s1 h; exact: S3_set_romL h. }
      by apply: r_sign_tail.
- (* FXHASH *)
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => hc.
  eapply r_get_remember_rhs => hc'.
  eapply (r_fact (hc' = hc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [[_ _ _ _ e5] _ _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst hc'.
  eapply r_assertD; first by [].
  move=> hhc _.
  eapply r_get_remember_lhs => mp.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), H3 hc mp mp 0 (s0, s1)); last first.
  { move=> s0 s1 [[[hinv h0] h1] h2].
    case/inv3E: hinv
      => hig [[e1 e2 e3 e4 e5] [e6 e7 e8] [e9 e10] [e11 e12 e13]].
    rewrite /rem_inv /= in h0 h1 h2.
    split.
    - by split.
    - split=> //.
      by rewrite e8.
    - by split.
    - split=> //.
      by rewrite addn0 -h0.
    - by split. }
  eapply r_get_remember_rhs => qc.
  eapply (r_fact ((qc < qh')%N)).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    case: hblk => _ _ _ [b1 _] [b2 b3].
    rewrite hrem addn0 in b1.
    apply: leq_ltn_trans b1 _.
    exact: leq_add3_ltn_l hhc b2 b3. }
  move=> hqc.
  eapply r_bind_assertD_rhs.
  { by move=> ? ? _. }
  move=> _.
  eapply (r_put_bind_rhs Lqc qc.+1 _
            (λ '(s0, s1), H3 hc mp mp 1 (s0, s1))).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    exact: H3_set_qc hrem hblk. }
  eapply (r_get_bind_rhs Lmap mp).
  { by move=> s0 s1 [_ [_ _ _ h] _ _ _]. }
  cbv beta iota.
  simpl.
  case Emd: (getm mp arg) => [d|].
  + simpl.
    rewrite (setm_same Emd).
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10] [p11 p12]
                  [p13 p14].
    apply: inv3I.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p8 ?p9 ?p10.
      split.
      -- by split.
      -- by split.
      -- split.
         ++ apply: (leq_trans p11).
            by rewrite addn1 !addSn leqnn.
         ++ exact: p12.
      -- by split.
  + rewrite ?bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply (r_put_rhs_weak Lmap (setm mp arg d) _
              (λ '(s0, s1), H3 hc mp (setm mp arg d) 1 (s0, s1))).
    { move=> s0 s1 h; exact: H3_set_M h. }
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10] [p11 p12]
                  [p13 p14].
    apply: inv3I.
    * apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
      do 2 (apply: heap_ignore_set_lhs; first by apply: fhas_in; fmap_solve).
      exact: hig.
    * get_heap_simpl.
      rewrite ?p1 ?p2 ?p3 ?p4 ?p8 ?p9 ?p10.
      split.
      -- by split.
      -- by split.
      -- split.
         ++ apply: (leq_trans p11).
            by rewrite addn1 !addSn leqnn.
         ++ exact: p12.
      -- by split.
- (* FXFORGE: bookkeeping is now b-unconditional (incl. the RHS QUERY
     counter machinery); the [if b] rides on the returned verdict,
     identical on both sides — a pure sync. *)
  case: arg => [m sg].
  ssprove_code_simpl. simpl.
  eapply r_get_remember_lhs => fc.
  eapply r_get_remember_rhs => fc'.
  eapply (r_fact (fc' = fc)).
  { move=> s0 s1 [[hinv h0] h1].
    case/inv3E: hinv => _ [_ [_ e7 _] _ _].
    rewrite /rem_inv /= in h0 h1.
    by rewrite -h0 -h1. }
  move=> e; subst fc'.
  rewrite code_link_assert.
  eapply r_assertD; first by [].
  move=> hfc _.
  simpl.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
  { move=> s0 s1 [[[[hinv h0] h1] h2] h3].
    case/inv3E: hinv => _ [[e1 _ _ _ _] _ _ _].
    rewrite /rem_inv /= in h2 h3.
    by rewrite -h2 -h3. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  refine (r_assertD _ _ _ _ _ _ _ _); first by [].
  move=> e0 e1.
  case: sto e0 e1 => [stv|] e0 e1; last by discriminate e0.
  simpl.
  ssprove_code_simpl.
  eapply r_get_remember_lhs => lg.
  eapply r_get_remember_rhs => lg'.
  eapply (r_fact (lg' = lg)).
  { move=> s0 s1 [[[[[[hinv h0] h1] h2] h3] h4] h5].
    case/inv3E: hinv => _ [[_ _ _ e4 _] _ _ _].
    rewrite /rem_inv /= in h4 h5.
    by rewrite -h4 -h5. }
  move=> e; subst lg'.
  eapply r_get_remember_lhs => mp.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), F3 stv lg mp mp fc 0 (s0, s1)); last first.
  { move=> s0 s1 [[[[[[[hinv h0] h1] h2] h3] h4] h5] h6].
    case/inv3E: hinv
      => hig [[f1 f2 f3 f4 f5] [f6 f7 f8] [f9 f10] [f11 f12 f13]].
    rewrite /rem_inv /= in h0 h1 h2 h3 h4 h5 h6.
    split.
    - by split.
    - split=> //.
      by rewrite f8.
    - by split.
    - split=> //.
      by rewrite addn0 -h0.
    - by split. }
  eapply r_get_remember_rhs => qc.
  eapply (r_fact ((qc < qh')%N)).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    case: hblk => _ _ _ [b1 _] [b2 b3].
    rewrite hrem addn0 in b1.
    apply: leq_ltn_trans b1 _.
    exact: leq_add3_ltn_r b2 b3 hfc. }
  move=> hqc.
  eapply r_bind_assertD_rhs.
  { by move=> ? ? _. }
  move=> _.
  eapply (r_put_bind_rhs Lqc qc.+1 _
            (λ '(s0, s1), F3 stv lg mp mp fc 1 (s0, s1))).
  { move=> s0 s1 [hblk hrem].
    rewrite /rem_inv /= in hrem.
    exact: F3_set_qc hrem hblk. }
  eapply (r_get_bind_rhs Lmap mp).
  { by move=> s0 s1 [_ [_ h _ _] _ _ _]. }
  cbv beta iota.
  simpl.
  case Emd: (getm mp (sg.1.2, (stv.1, (sg.1.1, m)))) => [d|].
  * simpl.
    rewrite (setm_same Emd).
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10 p11 p12]
                  [p13 p14] [p15 p16].
    apply: inv3I.
    -- apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
       do 2 (apply: heap_ignore_set_lhs;
             first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?p1 ?p2 ?p3 ?p4 ?p6 ?p9 ?p10 ?p11 ?p12.
       split.
       ++ by split.
       ++ by split.
       ++ split.
          ** apply: (leq_trans p13).
             by rewrite addn1 addnS leqnn.
          ** exact: p14.
       ++ by split.
  * rewrite ?bind_assoc.
    simpl.
    eapply (r_scheme_bind dD); first exact: prog_valid.
    move=> d; cbv beta.
    eapply (r_put_rhs_weak Lmap (setm mp (sg.1.2, (stv.1, (sg.1.1, m))) d) _
              (λ '(s0, s1),
                 F3 stv lg mp (setm mp (sg.1.2, (stv.1, (sg.1.1, m))) d)
                   fc 1 (s0, s1))).
    { move=> s0 s1 h; exact: F3_set_M h. }
    simpl.
    eapply r_put_lhs; eapply r_put_lhs.
    eapply r_put_rhs.
    apply r_ret => s0 s1 hpre.
    case: hpre => s1a [hp1 g1].
    case: hp1 => s0a [hp2 g2].
    case: hp2 => s0b [hblk g3].
    subst.
    split; first by [].
    case: hblk => -[hig p1 p2 p3 p4] [p5 p6 p7 p8] [p9 p10 p11 p12]
                  [p13 p14] [p15 p16].
    apply: inv3I.
    -- apply: heap_ignore_set_rhs; first by apply: fhas_in; fmap_solve.
       do 2 (apply: heap_ignore_set_lhs;
             first by apply: fhas_in; fmap_solve).
       exact: hig.
    -- get_heap_simpl.
       rewrite ?p1 ?p2 ?p3 ?p4 ?p6 ?p9 ?p10 ?p11 ?p12.
       split.
       ++ by split.
       ++ by split.
       ++ split.
          ** apply: (leq_trans p13).
             by rewrite addn1 addnS leqnn.
          ** exact: p14.
       ++ by split.
Qed.


(* ------------------------------------------------------------------ *)
(** ** The hop, reduced (sampler-agnostic part) *)

Lemma Repro_hop_Adv (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G2c b) (G3c b) A
  = AdvOf (RO_repro R XSuf D dR dD qh' q_s) (A ∘ R_rep b).
Proof.
rewrite (Adv_perfect_l (R_rep_real b)) (Adv_perfect_r (R_rep_ideal b)).
by rewrite Adv_reduction Adv_sym.
Qed.

End FXMSSReproHop.

(* ------------------------------------------------------------------ *)
(** ** The hop bound at [Repro_bound]'s scope

    Side-condition parameters of the hop (the proof architecture "Side
    conditions" / Toolkit/Reprogram.v header): the randomness space
    is [R := 'fin r_n.+1] with the UNIFORM sampler [rp_dPfx r_n]
    (so |R| = r_n.+1), and the digest sampler [dD] is lossless. *)

Section FXMSSReproBound.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

Context (PP N D M : choice_type).
Context (r_n : nat).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dD : dist D).
Context (dD_ll : LosslessCode dD).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

Local Notation Rfin := (chFin r_n.+1).
Local Notation dRu := (rp_dPfx r_n).
Local Notation IG := (I_G0fL PP N D M Rfin).
Local Notation G2C b :=
  (G2c PP N D M Rfin F Tl Hgrind Htree dPP dN dRu dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation G3C b :=
  (G3c PP N D M Rfin F Tl Hgrind Htree dPP dN dRu dD
     S_wn c_max h_sf q_s q_h n_max q_f b).
Local Notation R_REP b :=
  (R_rep PP N D M Rfin F Tl Hgrind Htree dPP dN dRu
     S_wn c_max h_sf q_s q_h n_max q_f b).

(** Hop 3 of the shrincs_fxmss_scheme chain (tex F.2 -> F.3, claim:fxmss-repro),
    with [Repro_bound]'s documented [qp > 1] slack [q_s.-1]. *)
Theorem Repro_hop (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  (Adv (G2C b) (G3C b) A
   <= q_s%:R * ((q_h + q_s + q_f + q_s.-1)%:R / r_n.+1%:R)
   :> Axioms.R)%R.
Proof.
rewrite (Repro_hop_Adv PP N D M Rfin F Tl Hgrind Htree dPP dN dRu dD
           S_wn c_max h_sf q_s q_h n_max q_f b A VA).
have VA' : ValidPackage (loc (A ∘ R_REP b)%sep)
             (I_RO Rfin (XSuf PP N M) D) A_export (A ∘ R_REP b)%sep.
{ exact _. }
exact: (Repro_bound r_n (XSuf PP N M) D dD dD_ll (q_h + q_s + q_f) q_s
          _ VA').
Qed.

End FXMSSReproBound.
