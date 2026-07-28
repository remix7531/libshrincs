(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.late_games

    The late games in the FXMSS EU-CMA chain (hops 5--9). They extend
    [G4c] from [fxmss.digest_hop] on the FORGE side: every game here shares
    GEN / SIGN / HASH and differs ONLY in the FORGE verdict, which is
    progressively nulled along the classification of a verifying
    forgery by [merkle.extract] against the honest value tree.

    ** The forgery classifier

    [shrincs_fxmss_forgery_case pp sp xss zi md ws ap] applies
    [merkle.extract] from [Sec.lib.math.merkle] with:
      - node hash [h := shrincs_fxmss_node_hash pp]  (the [Htree]-at-shrincs_fxmss_adr_tree map),
      - honest tree [t := value_tree_x pp sp xss]  (the stored keys),
      - forged path [path_of_idx (h_sf - zi.1) zi.2],
      - auth path [ap], recovered anchor [shrincs_fxmss_recover_anchor pp zi md ws].
    On a verifying forgery (the 4th conjunct of [shrincs_fxmss_verify_md]) the
    Merkle invariant [val_ap h [::] p ap a = Some (val_bt h [::] t)]
    holds, so [extractP] classifies it into one of FColl / FEscape /
    FShort / FAnchor.

    ** The four games

      [G5f b] — G4c with REFUSALS REMOVED (the proof architecture "Grind-
                validity hop"): GEN additionally asserts that ALL q_s
                presampled digests are grindable under pp (mirroring
                G0w's COMMIT-time grindability assert), so query q
                signs anchor q deterministically and never refuses.
      [G6f b] — G5f with the FAnchor forgery verdict nulled
                (returns false on an FAnchor forgery).
      [G7f b] — G6f with FColl ALSO nulled.
      [G8f b] — G7f with FEscape/FShort ALSO nulled.  Then EVERY case
                is nulled, so the [b = true] FORGE verdict is the
                constant [false] — G8f is perfect to [G0f false]
                (the proof architecture "Final step (9)"; [G8f_forge_false]).

    The tree hop is in [fxmss.tree_hop]; the structural hop and final
    exhaustion consume [G8f_forge_false] and the structural cases. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From Sec.lib Require Import prelude math.bin_tree math.merkle sig.scheme games.thf toolkit.sample_seq.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games.
(* [Export], not [Import]: files that [Require Import fxmss.late_games]
   without requiring [fxmss.digest_hop] themselves (tree_hop_proof.v,
   tcrx_hop_proof.v, leaf_km.v, leaf_reduction.v, ...) need
   [shrincs_fxmss_sd_loc] transitively, and plain [Import] does not
   propagate through a further [Require] — see proof/LOCATIONS.md. *)
From SHRINCS Require Export fxmss.digest_hop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.

Section FXMSSLateGames.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same section context as [fxmss.digest_hop]. *)
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
(** ** Shorthands (DigestHop's) *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation IG := (I_G0fL PP N D M R).
Local Notation flok sp zi := (leaf_okP h_sf sp zi).
Local Notation flidx sp zi := (lidx h_sf sp zi).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation FXST := (shrincs_fxmss_game_state PP N).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).
Local Notation valtree := (value_tree_x PP N F Tl h_sf).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).
Local Notation fxsignx :=
  (shrincs_fxmss_sign_x PP N D R F Tl Hgrind Htree S_wn c_max h_sf).
Local Notation fxvermd :=
  (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation frecover := (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind).
Local Notation skeys := (@sample_keys l N dN).

Local Notation Lst := (shrincs_fxmss_st_loc PP N).
Local Notation Llog := (shrincs_fxmss_log_loc M).
Local Notation Lrom := (shrincs_fxmss_rom_loc PP N D M R).
Local Notation Lrt := (shrincs_fxmss_rt_loc M R).

(** The signing-table key space and the presampled-digest map (= the
    DigestHop locations; [shrincs_fxmss_sd_loc] (409) is imported from
    [fxmss.digest_hop], not redefined here — see proof/LOCATIONS.md). *)
Local Notation RTK := (('nat × 'nat) × M).
Local Notation Lsd := (shrincs_fxmss_sd_loc D).

(** The shared location set of every late game (= DigestHop's). *)
Definition LateLocs : Locations :=
  [fmap Lst ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; Llog ; Lrom ;
        shrincs_fxmss_hcnt_loc ; Lrt ; shrincs_fxmss_fcnt_loc ; Lsd ].

(* ------------------------------------------------------------------ *)
(** ** The presampled-digest sampler [fill_code] (DigestHop's) *)

Fixpoint fill_code (js : seq nat) (m0 : chMap 'nat D) :
    raw_code (chMap 'nat D) :=
  match js with
  | [::] => ret m0
  | j :: js' => y ← dD ;; fill_code js' (setm m0 j y)
  end.

#[export] Instance fill_code_valid (L : Locations) (I : Interface)
    (js : seq nat) (m0 : chMap 'nat D) :
  ValidCode L I (fill_code js m0).
Proof.
elim: js m0 => [|j js IH] m0 /=.
- apply valid_ret.
- eapply valid_bind.
  + eapply valid_scheme, prog_valid.
  + move=> y. exact: IH.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Grindability of a digest (the G0w-style assert)

    A presampled digest [d] is signable at anchor identifier [zi]
    under [pp] exactly when [find_ctr] succeeds, i.e. [shrincs_fxmss_wots_sign] (and
    hence [shrincs_fxmss_sign_x]) returns [Some].  [sd_grindable pp sp xss sd]
    asserts this for EVERY presampled slot at the anchor it will be
    signed under (slot j is signed under anchor [posid (spath sp j)]),
    so after the GEN assert SIGN never refuses (the proof architecture "Grind-
    validity hop"). *)

Definition slot_grindable (pp : PP) (sp : seq bool) (j : nat) (d : D) :
    bool :=
  isSome (find_ctr PP D Hgrind S_wn c_max (posid (spath sp j)).1
            (posid (spath sp j)).2 pp d).

Definition sd_grindable (pp : PP) (sp : seq bool) (sd : chMap 'nat D) :
    bool :=
  all (fun j => match getm sd j with
                | Some d => slot_grindable pp sp j d
                | None => true
                end) (iota 0 (size (leaf_paths (tshape sp)))).

(* ------------------------------------------------------------------ *)
(** ** The forgery classifier

    The [fcase] of a verifying forgery against the honest value tree;
    consumed by the verdict-nulling predicates below and by the
    reductions of tree_hop.v / StructHop.v. *)

Definition shrincs_fxmss_forgery_case (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (zi : nat * nat) (md : D) (ws : seq N * nat) (ap : seq N) :=
  extract (nhash pp) [::] (valtree pp sp xss)
    (path_of_idx (h_sf - zi.1) zi.2) ap (frecover pp zi md ws).

(** The verdict modifiers: [keep_*] returns [true] exactly on the
    cases NOT YET nulled, so the FORGE verdict of each game is the
    [G4c]-style verdict AND-ed with the modifier.  [keepAnchor] keeps
    everything but FAnchor (G6f); [keepColl] additionally drops FColl
    (G7f); [keepNone] keeps nothing (G8f → constant false). *)
Definition keepAnchor (fc : fcase (A:=N)) : bool :=
  match fc with FAnchor => false | _ => true end.
Definition keepColl (fc : fcase (A:=N)) : bool :=
  match fc with FAnchor => false | FColl _ _ _ => false | _ => true end.
Definition keepNone (fc : fcase (A:=N)) : bool := false.

(** The classified verdict of a forgery: the verifier verdict, message
    freshness, the digest-collision-abort (DigestHop's [coll_ev]) and
    the case modifier [keep]. *)
Definition coll_ev (sd : chMap 'nat D) (tb : chMap RTK R)
    (zim : ('nat × 'nat) × M) (r : R) (md : D) : bool :=
  (md \in codomm sd) && (getm tb zim != Some r).

Definition fverd (keep : fcase (A:=N) -> bool) (st : FXST) (xss : seq (seq N))
    (sp : seq bool) (lg : seq M) (sd : chMap 'nat D) (tb : chMap RTK R)
    (m : M) (sg : FXSIG) (md : D) : bool :=
  ((fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2 && (m \notin lg))
   && ~~ coll_ev sd tb (sg.1.1, m) sg.1.2 md)
  && keep (shrincs_fxmss_forgery_case st.1.1 sp xss sg.1.1 md sg.2.1 sg.2.2).

(* ------------------------------------------------------------------ *)
(** ** The shared GEN / SIGN / HASH bodies (refusals removed)

    GEN = G4c's GEN plus the grindability assert.  SIGN signs the
    presampled digest [sd[sc]] at anchor [q] (= slot order, since
    after G5f every query advances the counter), records it in the
    PRFmsg table and the RO map (so HASH/FORGE see a consistent view),
    and — by the GEN assert — always succeeds for [q < n_a]. *)

Definition gen5_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   sd ← fill_code (iota 0 n_max) emptym ;;
   #assert sd_grindable pp sp sd ;;
   #put Lst := Some ((pp, fxroot pp sp xss), (sp, xss)) ;;
   #put Lsd := sd ;;
   ret (pp, fxroot pp sp xss)).

Definition sign5_body (mz : M × ('nat × 'nat)) : raw_code ('option FXSIG) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome Lst ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   if [&& flok st.2.1 mz.2 & mz.2 \notin domm us] then
     r ← dR ;;
     md ← (match getm sd (flidx st.2.1 mz.2) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
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
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

Definition hash5_body (x : ROIN) : raw_code D :=
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

(** [ssprove_valid] chokes on the [sample_keys]/[fill_code] binds and
    the [getSome]/[#assert as] forms; the bodies are validated by hand
    (the [valid_*] combinators), which also keeps the instances cheap. *)

#[export] Instance gen5_body_valid (I : Interface) (sp : 'list 'bool) :
  ValidCode LateLocs I (gen5_body sp).
Proof.
rewrite /gen5_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_bind; first by apply fill_code_valid. move=> sd.
eapply valid_assertD => _.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance sign5_body_valid (I : Interface) (mz : M × ('nat × 'nat)) :
  ValidCode LateLocs I (sign5_body mz).
Proof.
rewrite /sign5_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> r.
eapply valid_bind.
  case: (getm sd _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
    move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: (fxsignx _ _ _ _ _ _) => [sg|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  apply valid_ret.
- eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance hash5_body_valid (I : Interface) (x : ROIN) :
  ValidCode LateLocs I (hash5_body x).
Proof.
rewrite /hash5_body.
eapply valid_getr; first by fmap_solve. move=> hc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_bind.
  case: (getm mp x) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

(** The shared FORGE body, parameterized by the case modifier [keep].
    [keep := fun _ => true] is the G5f verdict; [keepAnchor] the G6f
    one; [keepColl] the G7f one; [keepNone] the G8f one. *)
Definition forge_keep_body (keep : fcase (A:=N) -> bool) (b : bool)
    (m : M) (sg : FXSIG) : raw_code 'bool :=
  (fc ← get shrincs_fxmss_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome Lst ;;
   lg ← get Llog ;;
   mp ← get Lrom ;;
   tb ← get Lrt ;;
   sd ← get Lsd ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put Lrom := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put shrincs_fxmss_fcnt_loc := fc.+1 ;;
   ret (if b then fverd keep st st.2.2 st.2.1 lg sd tb m sg md else false)).

#[export] Instance forge_keep_body_valid (I : Interface) (keep : fcase (A:=N) -> bool)
    (b : bool) (m : M) (sg : FXSIG) :
  ValidCode LateLocs I (forge_keep_body keep b m sg).
Proof.
rewrite /forge_keep_body.
eapply valid_getr; first by fmap_solve. move=> fc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSome.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
eapply valid_getr; first by fmap_solve. move=> tb.
eapply valid_getr; first by fmap_solve. move=> sd.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid; move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

(** The FORGE branch as it appears in the package (the [b] guard is now
    threaded INTO [forge_keep_body], so the bookkeeping runs on both
    [b]-sides and only the returned verdict depends on [b]). *)
#[export] Instance forge_if_valid (I : Interface) (keep : fcase (A:=N) -> bool)
    (b : bool) (m : M) (sg : FXSIG) :
  ValidCode LateLocs I (forge_keep_body keep b m sg).
Proof. by apply forge_keep_body_valid. Qed.

(* ------------------------------------------------------------------ *)
(** ** The late games (only FORGE differs; the modifier is [keep]) *)

(** The game family, indexed by the FORGE case modifier. *)
Definition Gkeep (keep : fcase (A:=N) -> bool) (b : bool) : game IG.
Proof.
notypeclasses refine [package LateLocs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen5_body sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (mz) {
      sign5_body mz
    } ;
    [ FXHASH ] : { ROIN ~> D } (x) {
      hash5_body x
    } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) {
      forge_keep_body keep b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge_keep_body_valid. } }
    { intros x; exact: hash5_body_valid. } }
  { intro mz; exact: sign5_body_valid. } }
{ intro sp; exact: gen5_body_valid. }
Defined.

Definition G5f (b : bool) : game IG := Gkeep (fun _ => true) b.
Definition G6f (b : bool) : game IG := Gkeep keepAnchor b.
Definition G7f (b : bool) : game IG := Gkeep keepColl b.
Definition G8f (b : bool) : game IG := Gkeep keepNone b.

(* ------------------------------------------------------------------ *)
(** ** Resolve equations (TCRXRom/DigestHop pattern) *)

Definition geno : opsig := (FXGEN, ('list 'bool, PP × N)).
Definition sgo : opsig := (FXSIGN, (M × ('nat × 'nat), 'option FXSIG)).
Definition hho : opsig := (FXHASH, (ROIN, D)).
Definition fgo : opsig := (FXFORGE, (M × FXSIG, 'bool)).

Lemma resolve_gen (keep : fcase (A:=N) -> bool) (b : bool) (sp : 'list 'bool) :
  resolve (Gkeep keep b) geno sp = gen5_body sp.
Proof. by rewrite /Gkeep /resolve /= coerce_kleisliE. Qed.

Lemma resolve_sign (keep : fcase (A:=N) -> bool) (b : bool) (mz : M × ('nat × 'nat)) :
  resolve (Gkeep keep b) sgo mz = sign5_body mz.
Proof. by rewrite /Gkeep /resolve /= coerce_kleisliE. Qed.

Lemma resolve_hash (keep : fcase (A:=N) -> bool) (b : bool) (x : ROIN) :
  resolve (Gkeep keep b) hho x = hash5_body x.
Proof. by rewrite /Gkeep /resolve /= coerce_kleisliE. Qed.

Lemma resolve_forge (keep : fcase (A:=N) -> bool) (b : bool) (m : M) (sg : FXSIG) :
  resolve (Gkeep keep b) fgo (m, sg)
  = forge_keep_body keep b m sg.
Proof. by rewrite /Gkeep /resolve /= coerce_kleisliE. Qed.

(* ------------------------------------------------------------------ *)
(** ** Composition sanity toward G8f = false

    [keepNone] nulls every case, so the G8f FORGE verdict is the
    constant [false] for both [b]: the [b = true] body's returned
    boolean is [_ && keepNone _ = false].  This is the "Final step (9)"
    bridge consumer ([fverd] collapses to [false]). *)

Lemma fverd_keepNone (st : FXST) (xss : seq (seq N)) (sp : seq bool)
    (lg : seq M) (sd : chMap 'nat D) (tb : chMap RTK R)
    (m : M) (sg : FXSIG) (md : D) :
  fverd keepNone st xss sp lg sd tb m sg md = false.
Proof. by rewrite /fverd /keepNone andbF. Qed.

(** The G7f → G8f modifier difference is EXACTLY the FColl/FEscape/
    FShort cases (FAnchor already nulled in both); confirms the chain
    G6f → G7f → G8f telescopes onto the three structure cases. *)
Lemma keepColl_keepNone_diff (fc : fcase (A:=N)) :
  keepColl fc && ~~ keepNone fc = keepColl fc.
Proof. by rewrite /keepNone andbT. Qed.

(** The G6f → G7f modifier difference is EXACTLY the FColl case
    (everything FAnchor/escape/short agrees): on a non-FColl, non-
    FAnchor case both keep; on FColl, G6f keeps and G7f drops.  This
    is what the TREE hop's reduction discriminates on. *)
Lemma keepAnchor_keepColl_eq (fc : fcase (A:=N)) :
  (forall q x y, fc <> FColl q x y) -> keepAnchor fc = keepColl fc.
Proof. by case: fc => //= q x y /(_ q x y). Qed.

End FXMSSLateGames.
