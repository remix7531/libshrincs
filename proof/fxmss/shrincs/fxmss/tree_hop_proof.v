(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.tree_hop_proof

    Hop 7 (G6f -> G7f, [claim:fxmss-tree-tcr]): the [R_tree] reduction
    package and its real and ideal [perfect] simulations, which assemble
    [Tree_hop]. This module consumes the pure collision and target
    bookkeeping from [fxmss.tree_hop] and the [Gkeep keep b] game family
    from [fxmss.late_games].

    The reduction builds the honest value tree through the SM-TCR
    oracles: leaf anchors through COLLQ and internal nodes bottom-up
    through TQUERY, under the COLLQ [pp] pin. SIGN and HASH are identical
    to the G6f bodies. FORGE runs [shrincs_fxmss_forgery_case] and submits the colliding
    internal node at its committed index. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From HBS Require Import prelude math.bin_tree math.merkle math.chain math.encoding
  sig.scheme games.thf games.smtcr toolkit.sample_seq.
From HBS Require Import wots.games wots.tcr_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section FXMSSTreeHopProof.

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

(** Same section context as [fxmss.tree_hop] and [fxmss.late_games]. *)
Context (PP N D M R : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (dPP : dist PP) (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (Hh : (h_sf <= 64)%N).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(** Hash-domain inhabitant for the dead [inr] branch of the leaf
    [Tl]-compression COLLQ (the reduction must compress the anchor
    ends BEFORE GETPP, so it cannot wait for the revealed pp; the
    branch is never taken — the answer is always [inl] — but a closed
    [N] term is needed for it).  Data-only side condition, exactly
    the WOTS+C chain-hop [n0]; trivially discharged where [N] is an
    n-byte-string type. *)
Context (n0 : N).

(* ------------------------------------------------------------------ *)
(** ** Shorthands (TreeHop's / LateGames') *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation valtree := (value_tree_x PP N F Tl h_sf).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).

(** The thf [Th] and collection [Cth] under attack (tree_hop.v). *)
Local Notation TH := (Th PP N Htree dPP dN).
Local Notation CTH := (Cth PP N D F Tl Hgrind Htree dPP dN).
Local Notation SMT b := (SMTCR_game TH CTH (n_max - 1) b).

(** Internal-node tweak (tree_hop.v's [tnode_tw]). *)
Local Notation tnode := (@tnode_tw w l h_sf).

(* ------------------------------------------------------------------ *)
(** ** The late-game family (LateGames') and the two endpoints *)

Local Notation G6 b :=
  (G6f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).
Local Notation G7 b :=
  (G7f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).

Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation FXST := (shrincs_fxmss_game_state PP N).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).

(** LateGames locations / bodies. *)
Local Notation Lst := (shrincs_fxmss_st_loc PP N).
Local Notation Llog := (shrincs_fxmss_log_loc M).
Local Notation Lrom := (shrincs_fxmss_rom_loc PP N D M R).
Local Notation Lrt := (shrincs_fxmss_rt_loc M R).
Local Notation Lsd := (shrincs_fxmss_sd_loc D).
Local Notation LateLocs0 := (LateLocs PP N D M R).
Local Notation gen5 :=
  (gen5_body PP N D R F Tl Hgrind Htree dPP dN dR dD S_wn c_max
     h_sf n_max).
Local Notation sign5 :=
  (sign5_body PP N D M R F Tl Hgrind Htree dR dD S_wn c_max h_sf q_s).
Local Notation hash5 := (hash5_body PP N D M R dD q_h).
Local Notation forge_keep :=
  (forge_keep_body PP N D M R F Tl Hgrind Htree dD S_wn h_sf q_f).
Local Notation fillc := (fill_code D dD).
Local Notation sdgrind := (sd_grindable PP D Hgrind S_wn c_max h_sf).
Local Notation skeys := (@sample_keys l N dN).
Local Notation shrincs_fxmss_forgery_case_at_N :=
  (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf).
Local Notation fxvermd :=
  (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation frecover := (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind).
Local Notation keepA := (keepAnchor N).
Local Notation keepC := (keepColl N).
Local Notation fverdN :=
  (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf).

(** Keep the M5 leaf-id selectors folded under [simpl] so the SIGN-bullet
    [case:] scrutinees ([leaf_okP …], [lidx …]) match the goal verbatim. *)
Arguments leaf_okP : simpl never.
Arguments lidx : simpl never.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the anchor value of the value tree at a leaf

    [value_tree_x pp sp xss = bt_posmap (anchor_val ...) [::] (tshape
    sp)]; the reduction builds the leaf values through COLLQ. *)

Local Notation fpk_of zi := (shrincs_fxmss_wots_public_key PP N F Tl zi.1 zi.2).
Local Notation fchain_ends zi := (chain_ends PP N F zi.1 zi.2).

(** The leaf function of [value_tree_x] at a leaf position [p]. *)
Definition anchor_val (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (p : seq bool) : N :=
  fpk_of (posid p) pp (nth [::] xss (index p (leaf_paths (tshape sp)))).

(* ------------------------------------------------------------------ *)
(** ** Pure layer: bottom-up evaluation of a [bt unit] sub-shape

    [tval pp sp xss pos t] is [val_bt (nhash pp) pos] of the value
    sub-tree at the shape-subtree [t] sitting at absolute position
    [pos] (the value tree decorated from [t]).  Internal nodes hash
    children with [nhash pp pos]; leaves carry [anchor_val] at their
    absolute path.  [tval] at the whole shape / root is [fxroot]
    ([tval_root]). *)

Fixpoint tval (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : N :=
  match t with
  | BLeaf _ => anchor_val pp sp xss pos
  | BNode tl tr =>
      nhash pp pos (tval pp sp xss (rcons pos false) tl)
                   (tval pp sp xss (rcons pos true) tr)
  end.

(** [tval] computes [val_bt] of the decorated sub-tree. *)
Lemma tval_valbt (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  tval pp sp xss pos t
  = val_bt (nhash pp) pos
      (bt_posmap (fun p => anchor_val pp sp xss p) pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
by rewrite IHl IHr.
Qed.

(** The whole tree's [tval] at the root is the game's root [fxroot]. *)
Lemma tval_root (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  tval pp sp xss [::] (tshape sp) = fxroot pp sp xss.
Proof. by rewrite tval_valbt. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: internal positions of a sub-shape under [pos]

    [int_under pos t]: the absolute positions of the internal nodes of
    the sub-shape [t] sitting at [pos], bottom-up (children before
    parent) — the TQUERY commit order of the loop below.  At the root
    it is a permutation of [internal_paths (tshape sp)] (only the
    multiset / membership matters for distinctness + budget). *)

Fixpoint int_under (pos : seq bool) (t : bt unit) : seq (seq bool) :=
  match t with
  | BLeaf _ => [::]
  | BNode tl tr =>
      int_under (rcons pos false) tl ++ int_under (rcons pos true) tr
        ++ [:: pos]
  end.

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed loops (CompressHop/ChainHop pattern)

    The reduction builds the value tree through the SM-TCR oracles:
    F-chains and Tl-compression for leaf anchors via COLLQ (the [Cth]
    members), Hgrind for the grindability assert via COLLQ, and the
    internal nodes bottom-up via TQUERY. *)

(** Opsigs as committed to [I_SMTCR Th Cth]. *)
Definition tr_cqo : opsig := (COLLQ, (tc_T CTH × tc_M CTH, tc_N CTH)).
Definition tr_tqo : opsig := (TQUERY, (th_T TH × th_M TH, th_N TH)).
Definition tr_gpo : opsig := (GETPP, ('unit, th_PP TH)).
Definition tr_cko : opsig := (CHECK, ('nat × th_M TH, 'bool)).

(** Chain-step address of the anchor at [zi], chain [i], position
    [pos]. *)
Local Notation cadrs zi i pos := (shrincs_fxmss_wots_chain_adrs zi i pos).
Local Notation padrs zi := (shrincs_fxmss_wots_pk_adrs zi).
Local Notation gadrs zi := (shrincs_fxmss_wots_grind_adrs zi).

(** Walk chain [i] of anchor [zi] upward from value [x] at position
    [k] for [n] steps, one COLLQ (F member, [inl]) per step. *)
Fixpoint tr_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr tr_cqo (encode_adrs (cadrs zi i k), inl x)
         (λ r, tr_walk zi i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance tr_walk_valid (L : Locations) zi i k n (x : N) :
  ValidCode L (I_SMTCR TH CTH) (tr_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; exact: IH.
Qed.

(** Chain-ends of anchor [zi] from key list [xs]: per chain, walk up
    w-1 steps from the secret. *)
Fixpoint tr_cends (zi : nat * nat) (i : nat) (xs : seq N) :
    raw_code (chList N) :=
  match xs with
  | [::] => ret [::]
  | x :: xs' =>
      e ← tr_walk zi i 0 w.-1 x ;;
      es ← tr_cends zi i.+1 xs' ;;
      ret (e :: es)
  end.

#[local] Instance tr_cends_valid (L : Locations) zi i xs :
  ValidCode L (I_SMTCR TH CTH) (tr_cends zi i xs).
Proof.
elim: xs i => [|x xs IH] i /=.
- apply valid_ret.
- eapply valid_bind; first exact: tr_walk_valid.
  move=> e; eapply valid_bind; first exact: IH.
  move=> es; apply valid_ret.
Qed.

(** Anchor value: compute the ends, then compress with [Tl] via COLLQ
    (the [inr (inl ends)] member of [Cth]). *)
Definition tr_anchor (zi : nat * nat) (xs : seq N) : raw_code N :=
  ends ← tr_cends zi 0 xs ;;
  opr tr_cqo (encode_adrs (padrs zi), inr (inl ends))
    (λ r, ret (if r is inl y then y else n0)).

#[local] Instance tr_anchor_valid (L : Locations) zi xs :
  ValidCode L (I_SMTCR TH CTH) (tr_anchor zi xs).
Proof.
rewrite /tr_anchor; eapply valid_bind; first exact: tr_cends_valid.
move=> ends; eapply valid_opr; first by fmap_solve.
move=> r; apply valid_ret.
Qed.

(** Bottom-up tree commit over a shape sub-tree [t] at absolute
    position [pos]: leaves build the anchor value via COLLQ; internal
    nodes commit via TQUERY (the answer = honest node value).  The
    leaf key list for the leaf at position [p] is [nth [::] xss (index
    p (leaf_paths (tshape sp)))] = the game's value-tree leaf key. *)
Fixpoint tr_tree (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : raw_code N :=
  match t with
  | BLeaf _ =>
      tr_anchor (posid pos)
        (nth [::] xss (index pos (leaf_paths (tshape sp))))
  | BNode tl tr =>
      lv ← tr_tree sp xss (rcons pos false) tl ;;
      rv ← tr_tree sp xss (rcons pos true) tr ;;
      opr tr_tqo (tnode pos, (lv, rv)) (λ y, ret y)
  end.

#[local] Instance tr_tree_valid (L : Locations) sp xss pos t :
  ValidCode L (I_SMTCR TH CTH) (tr_tree sp xss pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- exact: tr_anchor_valid.
- eapply valid_bind; first exact: IHl.
  move=> lv; eapply valid_bind; first exact: IHr.
  move=> rv; eapply valid_opr; first by fmap_solve.
  move=> y; apply valid_ret.
Qed.

(** Grind one anchor's q_s-slot: route Hgrind through COLLQ (the
    [inr (inr (d, c))] member of [Cth]), at every counter below
    [c_max], returning the answer list. *)
Fixpoint tr_grind (zi : nat * nat) (d : D) (cs : seq nat) :
    raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr tr_cqo (encode_adrs (gadrs zi), inr (inr (d, c)))
        (λ r, hs ← tr_grind zi d cs' ;;
              ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance tr_grind_valid (L : Locations) zi d cs :
  ValidCode L (I_SMTCR TH CTH) (tr_grind zi d cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

(** Grindability of all q_s presampled slots through COLLQ: for slot
    [j] holding digest [d], grind anchor [posid (spath sp j)] and test
    [isSome (find_ctr ...)] on the answer list ([cp_pick]-style); the
    conjunction over slots is [sd_grindable] ([tr_gcheck_E]). *)
Definition tr_slot_grind (sp : seq bool) (sd : chMap 'nat D) (j : nat) :
    raw_code 'bool :=
  match getm sd j with
  | Some d =>
      hs ← tr_grind (posid (spath sp j)) d (iota 0 c_max) ;;
      ret (has (@grind_prp w l S_wn) hs)
  | None => ret true
  end.

#[local] Instance tr_slot_grind_valid (L : Locations) sp sd j :
  ValidCode L (I_SMTCR TH CTH) (tr_slot_grind sp sd j).
Proof.
rewrite /tr_slot_grind; case: (getm sd j) => [d|]; last by apply valid_ret.
eapply valid_bind; first exact: tr_grind_valid.
move=> hs; apply valid_ret.
Qed.

Fixpoint tr_gcheck (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) :
    raw_code 'bool :=
  match js with
  | [::] => ret true
  | j :: js' =>
      b ← tr_slot_grind sp sd j ;;
      bs ← tr_gcheck sp sd js' ;;
      ret (b && bs)
  end.

#[local] Instance tr_gcheck_valid (L : Locations) sp sd js :
  ValidCode L (I_SMTCR TH CTH) (tr_gcheck sp sd js).
Proof.
elim: js => [|j js IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: tr_slot_grind_valid.
  move=> b; eapply valid_bind; first exact: IH.
  move=> bs; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The committed-target index for an internal node

    Targets are committed via TQUERY in [int_under [::] (tshape sp)]
    order; the CHECK index of internal node [q] is its position. *)

Definition tnode_index (sp : seq bool) (q : seq bool) : nat :=
  index q (int_under [::] (tshape sp)).

(* ------------------------------------------------------------------ *)
(** ** The reduction package [R_tree]

    Uses the SAME locations as LateGames (shrincs_fxmss_*_loc 400-409), so
    SIGN/HASH are identical to [sign5_body]/[hash5_body], and their
    relational cases are pure syncs.  GEN routes the pp-dependent
    computation (grindability + root) through the SM-TCR oracles, under
    the COLLQ pp-pin; FORGE classifies the forgery and on FColl submits
    CHECK at the committed-target index. *)

(** GEN: pin pp via one COLLQ (Tl member on [::], answer discarded);
    sample the dead [dN]/[dR] and the keys/digests as G6f does; assert
    grindability through COLLQ; build the root bottom-up through
    TQUERY/COLLQ; GETPP; store state and return (pp, root). *)
Definition gen_red (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   _ ← opr tr_cqo (encode_adrs (gadrs (0, 0)), inr (inl [::])) (λ r, ret r) ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   sd ← fillc (iota 0 n_max) emptym ;;
   gok ← tr_gcheck sp sd (iota 0 (size (leaf_paths (tshape sp)))) ;;
   #assert gok ;;
   root ← tr_tree sp xss [::] (tshape sp) ;;
   pp ← opr tr_gpo Datatypes.tt (λ p, ret p) ;;
   #put Lst := Some ((pp, root), (sp, xss)) ;;
   #put Lsd := sd ;;
   ret (pp, root)).

(** FORGE: G6f's body up to the verdict, then classify; on FColl submit
    CHECK at the committed index of the colliding node, else answer as
    G6f ([keepA]).  The verdict prefix [P] (verify && fresh && ~~coll)
    matches [fverd]'s first three conjuncts. *)
Definition forge_red (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
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
   if b then
     let P := (fxvermd st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
               && (m \notin lg))
              && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 md in
     match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 md sg.2.1 sg.2.2 with
     | FColl q x _ =>
         ans ← opr tr_cko (tnode_index st.2.1 q, x) (λ a, ret a) ;;
         ret (P && ans)
     | fc' => ret (P && keepA fc')
     end
   else ret false).

#[export] Instance gen_red_valid (sp : 'list 'bool) :
  ValidCode LateLocs0 (I_SMTCR TH CTH) (gen_red sp).
Proof.
rewrite /gen_red.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> r; apply valid_ret.
move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_bind; first by apply fill_code_valid. move=> sd.
eapply valid_bind; first exact: tr_gcheck_valid. move=> gok.
eapply valid_assertD => _.
eapply valid_bind; first exact: tr_tree_valid. move=> root.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> p; apply valid_ret.
move=> pp.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance forge_red_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode LateLocs0 (I_SMTCR TH CTH) (forge_red b m sg).
Proof.
rewrite /forge_red.
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
case: b; last by apply valid_ret.
case: (shrincs_fxmss_forgery_case_at_N _ _ _ _ _ _ _) => [q x y|q x a0|q a|].
- eapply valid_bind.
    eapply valid_opr; first by fmap_solve. move=> a; apply valid_ret.
  move=> ans; apply valid_ret.
- apply valid_ret.
- apply valid_ret.
- apply valid_ret.
Qed.

(** The reduction is parameterized by the FORGE guard [b] (the outer
    game's FORGE bit): at [b = false] FORGE returns [false] (CHECK never
    invoked), matching [G6f false]/[G7f false]'s null verdict; at
    [b = true] it classifies and submits CHECK.  This [b]-threading is
    needed for [Tree_hop]'s [b = false] direction (both sides have a
    null FORGE, so the SM-TCR advantage is [0] too). *)
(** DIRECTED package validity (M5): the lifted SIGN body makes the
    default [package] typeclass elaboration a >30-min wall, so we
    [notypeclasses refine] the raw package and discharge the
    [ValidPackage] obligation by hand — [valid_package_cons] peeled
    FORGE→HASH→SIGN→GEN over the four hand-proved [ValidCode]
    instances, exactly as [late_games.Gkeep]. *)
Definition R_tree (b : bool) : package (I_SMTCR TH CTH) IG.
Proof.
notypeclasses refine [package LateLocs0 ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen_red sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (m) {
      sign5 m
    } ;
    [ FXHASH ] : { ROIN ~> D } (x) {
      hash5 x
    } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) {
      forge_red b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge_red_valid. } }
    { intros x; exact: hash5_body_valid. } }
  { intros m; exact: sign5_body_valid. } }
{ intros sp; exact: gen_red_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Linked SM-TCR oracle bodies (resolve equations, computed once) *)

Local Notation tpp := (tcr_pp_loc TH).
Local Notation ttgts := (tcr_tgts_loc TH).
Local Notation ttws := (tcr_tws_loc TH).
Local Notation trev := tcr_rev_loc.

Lemma resolve_cq (b : bool) (t : tc_T CTH) (x : tc_M CTH) :
  resolve (SMT b) tr_cqo (t, x) =
  (ppo ← get tpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put tpp := Some pp ;; ret pp
        end ;;
   ret (tc_eval CTH pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_tq (b : bool) (t : th_T TH) (x : th_M TH) :
  resolve (SMT b) tr_tqo (t, x) =
  (revealed ← get trev ;;
   #assert ~~ revealed ;;
   tws ← get ttws ;;
   #assert (size tws < n_max - 1)%N ;;
   #assert (t \notin tws) ;;
   tgts ← get ttgts ;;
   #put ttgts := setm tgts (size tws) (t, x) ;;
   #put ttws := rcons tws t ;;
   ppo ← get tpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put tpp := Some pp ;; ret pp
        end ;;
   ret (th_eval TH pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_gp (b : bool) (u : unit) :
  resolve (SMT b) tr_gpo u =
  (ppo ← get tpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put tpp := Some pp ;; ret pp
        end ;;
   #put trev := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_ck (j : nat) (x : th_M TH) :
  resolve (SMT true) tr_cko (j, x) =
  (revealed ← get trev ;;
   #assert revealed ;;
   tgts ← get ttgts ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get tpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put tpp := Some pp ;; ret pp
            end ;;
       ret ((x != m0) && (th_eval TH pp t0 x == th_eval TH pp t0 m0))
   | None => ret false
   end).
Proof. simplify_linking. reflexivity. Qed.

Lemma resolve_ck_false (j : nat) (x : th_M TH) :
  resolve (SMT false) tr_cko (j, x) = ret false.
Proof. simplify_linking. reflexivity. Qed.

(* Keep packages / oracle bodies / pure layer folded under [simpl]
   from here on (ChainHop/CompressHop lesson). *)
#[local] Arguments resolve : simpl never.
#[local] Arguments SMTCR_game : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments shrincs_fxmss_forgery_case : simpl never.
#[local] Arguments shrincs_fxmss_verify_md : simpl never.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: [int_under] is the shape's internal positions

    [int_under [::] t] is a permutation of the relative-internal-paths
    decorated as absolute positions; membership and uniqueness are all
    the budget/freshness side conditions need. *)

(** [int_under] is a re-based [internal_paths] (membership, size,
    uniqueness — all the budget/freshness side conditions need). *)
Lemma orb_rot3 (a b c : bool) : (a || (b || c) = c || (a || b))%B.
Proof. by case: a; case: b; case: c. Qed.

Lemma map_cons_cat (b : bool) (pos : seq bool) (s : seq (seq bool)) :
  [seq pos ++ q | q <- [seq b :: q0 | q0 <- s]]
  = [seq rcons pos b ++ q | q <- s].
Proof. by rewrite -map_comp; apply/eq_map => q /=; rewrite cat_rcons. Qed.

Lemma int_under_internal_pos (t : bt unit) (pos q : seq bool) :
  (q \in int_under pos t)
  = (q \in [seq pos ++ q' | q' <- internal_paths t]).
Proof.
elim: t pos q => [[]|tl IHl tr IHr] pos q /=; first by rewrite in_nil.
rewrite !mem_cat !inE map_cat mem_cat !map_cons_cat IHl IHr.
by rewrite cats0 orb_rot3.
Qed.

Lemma int_under_internal (t : bt unit) :
  int_under [::] t =i internal_paths t.
Proof.
move=> q; rewrite int_under_internal_pos.
apply/mapP/idP => [[q' hq' eq]|hq].
- by rewrite eq cat0s.
- exists q; first exact: hq.
  by rewrite cat0s.
Qed.

Lemma int_under_size (t : bt unit) :
  size (int_under [::] t) = size (internal_paths t).
Proof.
suff H : forall pos, size (int_under pos t) = size (internal_paths t) by [].
elim: t => [[]|tl IHl tr IHr] pos //=.
rewrite !size_cat !size_map IHl IHr /=.
by rewrite addn1 addnS.
Qed.

(** Every committed position under [pos] is [pos] followed by an
    internal path of [t]. *)
Lemma int_under_mem_pfx (t : bt unit) (pos x : seq bool) :
  x \in int_under pos t -> exists2 q, x = pos ++ q & q \in internal_paths t.
Proof. by rewrite int_under_internal_pos => /mapP[q hq ->]; exists q. Qed.

(** A [rcons pos false]-prefixed path and a [rcons pos true]-prefixed
    one disagree at index [size pos]. *)
Lemma rcons_ft_neq (pos s s' : seq bool) :
  rcons pos false ++ s = rcons pos true ++ s' -> False.
Proof.
move=> /(congr1 (nth true ^~ (size pos))).
by rewrite !cat_rcons !nth_cat ltnn subnn /=.
Qed.

(** A [rcons pos b]-prefixed path is longer than [pos]. *)
Lemma rcons_self_neq (b : bool) (pos s : seq bool) :
  pos = rcons pos b ++ s -> False.
Proof.
move=> /(congr1 size); rewrite size_cat size_rcons addSn.
by rewrite -[in LHS](addn0 (size pos)) -addnS => /addnI.
Qed.

Lemma int_under_uniqP (t : bt unit) (pos : seq bool) :
  uniq (int_under pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
rewrite !cat_uniq IHl IHr /= !andbT.
apply/andP; split.
- apply/hasPn => x; rewrite mem_cat inE => /orP[hx|/eqP ->].
  + apply/negP => /int_under_mem_pfx[q hq _].
    move/int_under_mem_pfx: hx => [q' hq' _].
    by apply: (rcons_ft_neq pos q q'); rewrite -hq -hq'.
  + apply/negP => /int_under_mem_pfx[q hq _].
    exact: (rcons_self_neq false pos q).
- rewrite orbF.
  apply/negP => /int_under_mem_pfx[q hq _].
  exact: (rcons_self_neq true pos q).
Qed.

Lemma int_under_uniq (t : bt unit) : uniq (int_under [::] t).
Proof. exact: int_under_uniqP. Qed.

(* ------------------------------------------------------------------ *)
(** ** The committed-target list (the SM-TCR bookkeeping)

    At internal node [q] the reduction commits target [(tnode q,
    node_children q)] where [node_children q] are the honest children
    VALUES — exactly the [y] of [shrincs_fxmss_forgery_case_FColl].  The committed list is
    in [int_under] order. *)

Definition node_children (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : seq bool) : N * N :=
  match subtree_at (valtree pp sp xss) q with
  | Some (BNode LT RT) =>
      (val_bt (nhash pp) (rcons q false) LT,
       val_bt (nhash pp) (rcons q true) RT)
  | _ => (n0, n0)
  end.

Definition commitq (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
    seq (adrs_sf_ch * (N × N)) :=
  [seq (tnode q, node_children pp sp xss q) | q <- int_under [::] (tshape sp)].

Definition commit_tws (sp : seq bool) : seq adrs_sf_ch :=
  [seq tnode q | q <- int_under [::] (tshape sp)].

(** Bottom-up [tr_tree] message at node [q] = [node_children q]:
    [tval] of the children equals [val_bt] of the value-tree children
    subtrees ([tval_valbt]). *)
Lemma tval_children (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : seq bool) (tl tr : bt unit) :
  subtree_at (tshape sp) q = Some (BNode tl tr) ->
  (tval pp sp xss (rcons q false) tl, tval pp sp xss (rcons q true) tr)
  = node_children pp sp xss q.
Proof.
move=> hsub.
rewrite /node_children /value_tree_x subtree_at_posmap hsub /=.
by rewrite !tval_valbt.
Qed.

(** [qnth] through a map (ChainHop's, local copy). *)
Lemma qnth_map {X Y : Type} (f : X -> Y) (s : seq X) (i : nat) :
  qnth [seq f x | x <- s] i = omap f (qnth s i).
Proof. by rewrite /qnth -map_drop; case: (drop i s). Qed.

(** CHECK-index lookup: the committed map at the index of an internal
    position [q] returns [q]'s target. *)
Lemma getm_commitq (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : seq bool) :
  q \in int_under [::] (tshape sp) ->
  getm (qmap_from 0 (commitq pp sp xss)) (tnode_index sp q)
  = Some (tnode q, node_children pp sp xss q).
Proof.
move=> hq.
rewrite /tnode_index.
have := qmap_from_get 0 (commitq pp sp xss) (index q (int_under [::] (tshape sp))).
rewrite add0n => ->.
rewrite /commitq qnth_map /qnth.
rewrite (drop_nth [::]); last by rewrite index_mem.
by rewrite nth_index.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The invariant

    [heap_ignore IGN] over the FOUR SM-TCR private locations (so the
    9 shrincs_fxmss_*_loc — shared by G6f and R_tree — are forced EQUAL on both
    sides, the SIGN/HASH mirror, FOR FREE), joined with a [rel_app]
    that keys the SM-TCR state on [shrincs_fxmss_st_loc]: None ⇒ initial,
    Some((pp,_),(sp,xss)) ⇒ pp pinned, phase revealed, the committed
    map = [qmap_from 0 (commitq pp sp xss)], the tweaks = [commit_tws
    sp]. *)

Definition IGN : Locations :=
  [fmap (tcr_pp_loc TH) ; (tcr_tgts_loc TH) ; (tcr_tws_loc TH) ; tcr_rev_loc ].

Definition RTr (sto : option FXST)
    (po : option PP) (tg : {fmap nat -> (th_T TH × th_M TH)})
    (tw : seq (th_T TH)) (rv : bool) : Prop :=
  match sto with
  | None => [/\ po = None, tg = emptym, tw = [::] & rv = false]
  | Some st =>
      [/\ po = Some st.1.1, rv = true,
          tg = qmap_from 0 (commitq st.1.1 st.2.1 st.2.2),
          tw = commit_tws st.2.1
        & st.1.2 = fxroot st.1.1 st.2.1 st.2.2]
  end.

Definition tr_inv : precond :=
  heap_ignore IGN
  ⋊ rel_app [:: (rhs, shrincs_fxmss_st_loc PP N) ; (rhs, tcr_pp_loc TH) ;
                (rhs, tcr_tgts_loc TH) ; (rhs, tcr_tws_loc TH) ;
                (rhs, tcr_rev_loc) ] RTr.

Arguments tr_inv : simpl never.

Lemma tr_invE s0 s1 :
  tr_inv (s0, s1) ->
  heap_ignore IGN (s0, s1) /\
  RTr (get_heap s1 (shrincs_fxmss_st_loc PP N)) (get_heap s1 (tcr_pp_loc TH))
      (get_heap s1 (tcr_tgts_loc TH)) (get_heap s1 (tcr_tws_loc TH))
      (get_heap s1 tcr_rev_loc).
Proof. by move=> [h1 h2]; split. Qed.

Lemma tr_invI s0 s1 :
  heap_ignore IGN (s0, s1) ->
  RTr (get_heap s1 (shrincs_fxmss_st_loc PP N)) (get_heap s1 (tcr_pp_loc TH))
      (get_heap s1 (tcr_tgts_loc TH)) (get_heap s1 (tcr_tws_loc TH))
      (get_heap s1 tcr_rev_loc) ->
  tr_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(* ------------------------------------------------------------------ *)
(** ** Conversion bridges: the COLLQ/TQUERY post-processed answers ARE
    the pure scheme values at the decoded address (decode_tweakK). *)

Lemma collq_F_E pp (zi : nat * nat) (i k : nat) (x : N) :
  (if tc_eval CTH pp (encode_adrs (cadrs zi i k)) (inl x) is inl y then y else x)
  = F pp (cadrs zi i k) x.
Proof. by rewrite {1}/tc_eval /= decode_tweakK. Qed.

Lemma collq_Tl_E pp (zi : nat * nat) (ends : seq N) :
  (if tc_eval CTH pp (encode_adrs (padrs zi)) (inr (inl ends)) is inl y
   then y else n0)
  = Tl pp (padrs zi) ends.
Proof. by rewrite {1}/tc_eval /= decode_tweakK. Qed.

Lemma collq_H_E pp (zi : nat * nat) (d : D) (c : nat) :
  (if tc_eval CTH pp (encode_adrs (gadrs zi)) (inr (inr (d, c))) is inr h
   then h else 0%N)
  = Hgrind pp (gadrs zi) (d, c).
Proof. by rewrite {1}/tc_eval /= decode_tweakK. Qed.

(** TQUERY's th_eval answer at a tnode tweak is the honest node hash. *)
Lemma th_eval_tnode pp (q : seq bool) (x y : N) :
  th_eval TH pp (tnode q) (x, y) = nhash pp q x y.
Proof. by rewrite {1}/th_eval /tnode /tnode_tw /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** ** The GEN block precondition (heap_ignore + the 4 SMTCR rhs locs)

    Inside GEN, the lhs (G6f) and rhs (R_tree) heaps agree off [IGN]
    (the 9 shrincs_fxmss_*_loc stay synced for free), and the rhs SMTCR state is
    explicitly tracked.  The pp-pin COLLQ samples pp lazily; the
    bottom-up loops then run with pp pinned, leaving the SMTCR
    machinery untouched (COLLQ) or growing the committed queue
    (TQUERY).  This mirrors CompressHop's [cblk] / ChainHop's [tblk]. *)

Definition trblk (po : option PP) (rv : bool)
    (tw : seq (th_T TH)) (tg : {fmap nat -> (th_T TH × th_M TH)}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGN (s0, s1),
      get_heap s1 tpp = po,
      get_heap s1 trev = rv,
      get_heap s1 ttws = tw &
      get_heap s1 ttgts = tg].

Arguments trblk : simpl never.

(** Pin: lazily sampling pp (put tpp). *)
Lemma trblk_set_pp (pp : PP) rv tw tg s0 s1 :
  trblk None rv tw tg (s0, s1) ->
  trblk (Some pp) rv tw tg (s0, set_heap s1 tpp (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(** TQUERY commit at tweak [t]: put tgts (grow), put tws (rcons). *)
Lemma trblk_qupd (pp : PP) (t : adrs_sf_ch) (xy : N × N) tw tg s0 s1 :
  trblk (Some pp) false tw tg (s0, s1) ->
  trblk (Some pp) false (rcons tw t) (setm tg (size tw) (t, xy))
    (s0, set_heap (set_heap s1 ttgts (setm tg (size tw) (t, xy)))
           ttws (rcons tw t)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

(** GETPP: flip the phase (put rev). *)
Lemma trblk_set_rev (po : option PP) tw tg s0 s1 :
  trblk po false tw tg (s0, s1) ->
  trblk po true tw tg (s0, set_heap s1 trev true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked COLLQ (pp pinned: SMTCR state untouched) *)

(** [code_link] of a [ret] under a bind collapses (used to discharge
    the trailing [ret] of [tr_slot_grind]/list builders). *)
Lemma code_link_ret_bind {A B : choiceType} (a : A) (p : raw_package)
    (k : A -> raw_code B) :
  bind (code_link (ret a) p) k = k a.
Proof. by []. Qed.

(** Left unit of [bind] (the trailing [ret] of a COLLQ post-process). *)
Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

(** [code_link] of an [opr] under a bind exposes the resolved oracle. *)
Lemma code_link_opr_bind {A B C : choiceType} (o : opsig) (m : src o)
    (kk : tgt o -> raw_code A) (p : raw_package) (k1 : A -> raw_code B) :
  bind (code_link (opr o m kk) p) k1
  = bind (resolve p o m) (λ r, bind (code_link (kk r) p) k1).
Proof. by rewrite /= bind_assoc. Qed.

Lemma r_collq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T CTH) (x : tc_M CTH) rv tw tg
    (c0 : raw_code B) (k1 : tc_N CTH -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (tc_eval CTH pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (resolve (SMT b) tr_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_cq b t x).
eapply (r_get_bind_rhs tpp (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure values of the COLLQ-routed leaf loops

    The walk computes a [chain]; the per-chain ends are [chain_ends];
    the anchor is [shrincs_fxmss_wots_public_key]; the grinding answers are [Hgrind]-lists. *)

Local Notation fwchain pp zi i x :=
  (chain (fun pos y => F pp (cadrs zi i pos) y) x 0 w.-1).

(** Pure recursive ends value mirroring [tr_cends] (offset [i]). *)
Fixpoint fcends pp (zi : nat * nat) (i : nat) (xs : seq N) : seq N :=
  match xs with
  | [::] => [::]
  | x :: xs' => fwchain pp zi i x :: fcends pp zi i.+1 xs'
  end.

(** [fcends] at any offset [i] is the chain-ends map over the shifted
    iota. *)
Lemma fcends_E pp (zi : nat * nat) (i : nat) (xs : seq N) :
  fcends pp zi i xs
  = [seq chain (fun pos y => F pp (cadrs zi ix.1 pos) y) ix.2 0 w.-1
    | ix <- zip (iota i (size xs)) xs].
Proof.
elim: xs i => [|x xs IH] i //=.
by rewrite IH.
Qed.

(** [fcends] from offset 0 over an [l]-list is [chain_ends]. *)
Lemma fcends_chain_ends pp (zi : nat * nat) (xs : seq N) :
  size xs = l -> fcends pp zi 0 xs = fchain_ends zi pp xs.
Proof.
move=> hxs; rewrite fcends_E /chain_ends hxs.
apply/eq_in_map => -[i x] _ /=.
by case: zi.
Qed.

(** The anchor value: [Tl] at [padrs] of the ends IS [shrincs_fxmss_wots_public_key]. *)
Lemma anchor_pk pp (zi : nat * nat) (xs : seq N) :
  Tl pp (padrs zi) (fchain_ends zi pp xs) = fpk_of zi pp xs.
Proof. by rewrite /shrincs_fxmss_wots_public_key; case: zi. Qed.

(** Walk loop: [tr_walk zi i k n x] (linked) lands on the chain value
    [n] steps up from [x] at position [k]. *)
Lemma r_walk_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (i n k : nat) (x : N) rv tw tg
         (c0 : raw_code B) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (chain (fun pos y => F pp (cadrs zi i pos) y) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_walk zi i k n x) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> zi i n.
elim: n => [|n IH] k x rv tw tg c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_collq_known b).
  rewrite collq_F_E.
  apply: IH.
  by rewrite chainS in h.
Qed.

(** Per-chain ends: [tr_cends zi i xs] (linked) lands on [fcends]. *)
Lemma r_cends_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (i : nat) (xs : seq N) rv tw tg
         (c0 : raw_code B) (k1 : chList N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (fcends pp zi i xs) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_cends zi i xs) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> zi i xs; elim: xs i => [|x xs IH] i rv tw tg c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_walk_spec b pp post zi i w.-1 0 x).
  rewrite code_link_bind bind_assoc.
  apply: (IH i.+1).
  by rewrite code_link_ret_bind.
Qed.

(** Anchor: [tr_anchor zi xs] (linked) lands on [shrincs_fxmss_wots_public_key] (= [Tl] of the
    ends), for a leaf key list of size [l]. *)
Lemma r_anchor_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (xs : seq N) rv tw tg
         (c0 : raw_code B) (k1 : N -> raw_code B),
  size xs = l ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (fpk_of zi pp xs) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_anchor zi xs) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> zi xs rv tw tg c0 k1 hxs h.
rewrite /tr_anchor code_link_bind bind_assoc.
eapply (r_cends_spec b pp post zi 0 xs).
rewrite /= bind_assoc.
eapply (r_collq_known b pp _ _ rv tw tg _ _ post).
rewrite collq_Tl_E bind_ret_l.
rewrite (fcends_chain_ends pp zi xs hxs) anchor_pk.
exact: h.
Qed.

(** Grinding loop: [tr_grind zi d cs] (linked) lands on the [Hgrind]
    answer list. *)
Lemma r_grind_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (d : D) (cs : seq nat) rv tw tg
         (c0 : raw_code B) (k1 : chList 'nat -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (gadrs zi) (d, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_grind zi d cs) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> zi d cs; elim: cs => [|c cs IH] rv tw tg c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_collq_known b).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite collq_H_E /= in h *.
Qed.

(** Grindability of one slot through the answer list = [find_ctr]'s
    [isSome] (= [slot_grindable]); [grind_prp] at an [Hgrind] answer IS
    [good_ctr] at the same counter. *)
Local Notation gprp := (@grind_prp w l S_wn).
Local Notation ffind_ctr zi :=
  (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2).
Local Notation fgood_ctr zi :=
  (good_ctr PP D Hgrind S_wn zi.1 zi.2).

Lemma has_grind_find_ctr pp (zi : nat * nat) (d : D) :
  has gprp [seq Hgrind pp (gadrs zi) (d, c) | c <- iota 0 c_max]
  = isSome (ffind_ctr zi pp d).
Proof.
rewrite has_map /find_ctr.
rewrite (eq_has (a2 := fgood_ctr zi pp d)); last first.
  by move=> c /=; rewrite /good_ctr /digest_of /grind_adrs; case: zi.
rewrite has_count -size_filter.
by case: [seq c <- iota 0 c_max | fgood_ctr zi pp d c].
Qed.

(** One presampled slot: [tr_slot_grind sp sd j] lands on the slot's
    grindability bool. *)
Lemma r_slot_grind_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (j : nat) rv tw tg
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (match getm sd j with
              | Some d => slot_grindable PP D Hgrind S_wn c_max
                            h_sf pp sp j d
              | None => true
              end) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_slot_grind sp sd j) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd j rv tw tg c0 k1 h.
rewrite /tr_slot_grind.
case E: (getm sd j) => [d|]; rewrite E /= in h.
- rewrite code_link_bind bind_assoc.
  eapply (r_grind_spec b pp post (posid (spath sp j)) d (iota 0 c_max)).
  rewrite code_link_ret_bind has_grind_find_ctr.
  rewrite -/(slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d).
  exact: h.
- by rewrite code_link_ret_bind; exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked TQUERY (commit an internal node) *)

(** The committed-queue form of [trblk]: [tw = unzip1 Q],
    [tg = qmap_from 0 Q]. *)
Local Notation trblkQ po rv Q :=
  (trblk po rv (unzip1 Q) (qmap_from 0 Q)).

(** [trblk_qupd] in queue form: a TQUERY at tweak [t], message [xy]
    grows the queue by [(t, xy)]. *)
Lemma trblkQ_upd (pp : PP) (Q : seq (adrs_sf_ch * (N × N))) (t : adrs_sf_ch)
    (xy : N × N) s0 s1 :
  trblkQ (Some pp) false Q (s0, s1) ->
  trblkQ (Some pp) false (rcons Q (t, xy)) (s0,
     set_heap (set_heap s1 ttgts (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, xy)))
       ttws (rcons (unzip1 Q) t)).
Proof.
move=> hpre.
have hsz : size (unzip1 Q) = size Q by rewrite /unzip1 size_map.
rewrite /unzip1 map_rcons -/(unzip1 Q) qmap_from_rcons add0n -hsz.
exact: (trblk_qupd pp t xy (unzip1 Q) (qmap_from 0 Q) s0 s1 hpre).
Qed.

Lemma r_tquery_known (b : bool) {B : choiceType} (pp : PP)
    (q : seq bool) (xy : N × N) (Q : seq (adrs_sf_ch * (N × N)))
    (c0 : raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < n_max - 1)%N ->
  tnode q \notin unzip1 Q ->
  ⊢ ⦃ λ '(s0, s1), trblkQ (Some pp) false (rcons Q (tnode q, xy)) (s0, s1) ⦄
     c0 ≈ k1 (th_eval TH pp (tnode q) xy) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblkQ (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (resolve (SMT b) tr_tqo (tnode q, xy)) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh h.
rewrite (resolve_tq b (tnode q) xy).
eapply (r_get_bind_rhs trev false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs ttws (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
eapply (r_get_bind_rhs ttgts (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (trblkQ_upd pp Q (tnode q) xy s0 s1 hpre).
eapply (r_get_bind_rhs tpp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
exact: h.
Qed.

(** All presampled slots: [tr_gcheck sp sd js] lands on the conjunction
    of slot grindabilities (= [sd_grindable] over [iota 0 q_s]). *)
Lemma r_gcheck_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) rv tw tg
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (all (fun j => match getm sd j with
                | Some d => slot_grindable PP D Hgrind S_wn c_max
                              h_sf pp sp j d
                | None => true
                end) js) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_gcheck sp sd js) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd js; elim: js => [|j js IH] rv tw tg c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_slot_grind_spec b pp post sp sd j).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite code_link_ret_bind.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The bottom-up tree commit (the heart of GEN)

    [tr_tree sp xss pos t] (linked) lands on [tval pp sp xss pos t],
    growing the committed queue by the internal-node targets of [t]
    under [pos] in [int_under] order. *)

(** The committed entries of sub-shape [t] at [pos] (the [int_under]
    order, paired with the honest children values). *)
(** The committed entries of sub-shape [t] at [pos]: at each internal
    node [q], the tweak [tnode q] and the children's [tval] values (the
    actual TQUERY message).  For [t] a subtree of [tshape sp] this is
    [node_children] ([tree_commits_commitq] below). *)
Fixpoint tree_commits (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : seq (adrs_sf_ch * (N × N)) :=
  match t with
  | BLeaf _ => [::]
  | BNode tl tr =>
      tree_commits pp sp xss (rcons pos false) tl
      ++ tree_commits pp sp xss (rcons pos true) tr
      ++ [:: (tnode pos, (tval pp sp xss (rcons pos false) tl,
                          tval pp sp xss (rcons pos true) tr))]
  end.

(** The node-case tweak list of [int_under] splits into left ++ right ++
    the node itself; used to thread the uniqueness/freshness side
    conditions of [r_tree_spec]. *)
Lemma int_under_node (pos : seq bool) (tl tr : bt unit) :
  [seq tnode q | q <- int_under pos (BNode tl tr)]
  = [seq tnode q | q <- int_under (rcons pos false) tl]
    ++ [seq tnode q | q <- int_under (rcons pos true) tr]
    ++ [:: tnode pos].
Proof. by rewrite /= !map_cat. Qed.

(** [uniq] is permutation-stable, so any reassociation/reordering of a
    cat is uniq iff the original is.  Bridge to membership reasoning. *)
Lemma uniq_perm_catAC (A B C : seq adrs_sf_ch) :
  uniq (A ++ B ++ C) -> uniq (B ++ A ++ C).
Proof. by move=> hu; rewrite -(perm_uniq (s1 := A ++ B ++ C)) // perm_catCA. Qed.

(** Swap the trailing two blocks under a [uniq] cat. *)
Lemma uniq_swap_tail (X A B : seq adrs_sf_ch) :
  uniq (X ++ A ++ B) -> uniq (X ++ B ++ A).
Proof.
move=> hu; rewrite -(perm_uniq (s1 := X ++ A ++ B)) //.
by rewrite perm_cat2l perm_catC.
Qed.

(** Membership in a [uniq] cat: pairwise-disjoint blocks.  Derived
    facts for the node case are stated via [perm]-stable [uniq]. *)
Lemma uniq_cat4_perm (A B C E : seq adrs_sf_ch) :
  perm_eq (A ++ B ++ C ++ E) (A ++ B ++ E ++ C).
Proof.
by rewrite perm_cat2l perm_cat2l perm_catC.
Qed.

(** The three node-case side facts, from the parent uniqueness
    [uniq (mapL ++ mapR ++ [:: tp] ++ Qs)]. *)
Lemma node_sides (mL mR Qs : seq adrs_sf_ch) (tp : adrs_sf_ch) :
  uniq (mL ++ mR ++ [:: tp] ++ Qs) ->
  [/\ uniq (mL ++ Qs),
      uniq (mR ++ Qs ++ mL)
    & tp \notin Qs ++ mL ++ mR].
Proof.
move=> hu.
have hperm : perm_eq (mL ++ mR ++ [:: tp] ++ Qs)
                     (tp :: (mL ++ mR ++ Qs)).
  rewrite -cat1s -[tp :: (mL ++ mR ++ Qs)]cat1s catA.
  by rewrite (perm_catCA (mL ++ mR) [:: tp] Qs) -catA.
have hu2 : uniq (tp :: (mL ++ mR ++ Qs)) by rewrite -(perm_uniq hperm).
move: hu2; rewrite cons_uniq => /andP[htp hmLmRQs].
split.
- have hp : perm_eq (mL ++ mR ++ Qs) ((mL ++ Qs) ++ mR).
    by rewrite -catA perm_cat2l perm_catC.
  by move: hmLmRQs; rewrite (perm_uniq hp) cat_uniq => /and3P[hh _ _]; exact: hh.
- by apply: uniq_swap_tail; apply: uniq_perm_catAC; exact: hmLmRQs.
- have e3 : (tp \in mL ++ mR ++ Qs) = (tp \in Qs ++ mL ++ mR).
    by rewrite !mem_cat orbA orbC.
  by rewrite -e3.
Qed.

Lemma unzip1_cat (s t : seq (adrs_sf_ch * (N × N))) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
Proof. by rewrite /unzip1 map_cat. Qed.

Lemma unzip1_tree_commits pp sp xss pos t :
  unzip1 (tree_commits pp sp xss pos t) = [seq tnode q | q <- int_under pos t].
Proof.
elim: t pos => [u|tl IHl tr IHr] pos //=.
by rewrite !unzip1_cat IHl IHr !map_cat.
Qed.

Lemma size_tree_commits pp sp xss pos t :
  size (tree_commits pp sp xss pos t) = size (int_under pos t).
Proof.
elim: t pos => [u|tl IHl tr IHr] pos //=.
by rewrite !size_cat IHl IHr.
Qed.

(** Leaf key list of the value tree at a leaf position. *)
Lemma anchor_key_size (sp : seq bool) (xss : seq (seq N)) (pos : seq bool) :
  (forall xs, xs \in xss -> size xs = l) ->
  index pos (leaf_paths (tshape sp)) < size xss ->
  size (nth [::] xss (index pos (leaf_paths (tshape sp)))) = l.
Proof.
move=> hall hlt; apply: hall; exact: mem_nth.
Qed.

Lemma r_tree_spec (b : bool) {B : choiceType} (pp : PP)
    (sp : seq bool) (xss : seq (seq N)) (post : postcond B B)
    (hkeys : forall xs, xs \in xss -> size xs = l) :
  forall (pos : seq bool) (t : bt unit)
         (Q : seq (adrs_sf_ch * (N × N)))
         (c0 : raw_code B) (k1 : N -> raw_code B),
  (forall p, p \in leaf_paths t ->
     index (pos ++ p) (leaf_paths (tshape sp)) < size xss) ->
  uniq ([seq tnode q | q <- int_under pos t] ++ unzip1 Q) ->
  (size Q + size (int_under pos t) <= n_max - 1)%N ->
  ⊢ ⦃ λ '(s0, s1),
        trblkQ (Some pp) false (Q ++ tree_commits pp sp xss pos t) (s0, s1) ⦄
     c0 ≈ k1 (tval pp sp xss pos t) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), trblkQ (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (code_link (tr_tree sp xss pos t) (SMT b)) k1 ⦃ post ⦄.
Proof.
move=> pos t; move: pos.
elim: t => [u|tl IHl tr IHr] pos Q c0 k1 hidx huniq hbud h /=.
- (* leaf: anchor build, no TQUERY (tree_commits = [::]) *)
  apply: (r_anchor_spec b pp post (posid pos)
            (nth [::] xss (index pos (leaf_paths (tshape sp))))).
  + apply: hkeys; apply: mem_nth.
    by have := hidx [::]; rewrite cats0 mem_seq1 eqxx => /(_ erefl).
  + move: h => /=; rewrite cats0.
    by rewrite /anchor_val.
- (* node: recurse left, recurse right, TQUERY at pos *)
  (* the three side facts, from [huniq] via [int_under_node] + [node_sides] *)
  move: huniq; rewrite int_under_node -catA -catA => huniq.
  have [huL huRcat hfresh] := node_sides _ _ _ _ huniq.
  (* budget bookkeeping: normalize hbud to a flat sum *)
  have hbud' : (size Q + size (int_under (rcons pos false) tl)
                + size (int_under (rcons pos true) tr)).+1 <= n_max - 1.
    move: hbud => /=; rewrite !size_cat /= => hb.
    apply: leq_trans hb.
    by rewrite !addnA addn1.
  rewrite code_link_bind bind_assoc.
  (* left subtree *)
  eapply (IHl (rcons pos false) Q).
  + move=> p hp; have := hidx (false :: p).
    rewrite -cat_rcons; apply.
    by rewrite /= mem_cat map_f.
  + exact: huL.
  + apply: leq_trans hbud'; apply: leqW; exact: leq_addr.
  rewrite code_link_bind bind_assoc.
  (* right subtree, queue grown by the left commits *)
  eapply (IHr (rcons pos true) (Q ++ tree_commits pp sp xss (rcons pos false) tl)).
  + move=> p hp; have := hidx (true :: p).
    rewrite -cat_rcons; apply.
    by rewrite /= mem_cat map_f ?orbT.
  + rewrite unzip1_cat unzip1_tree_commits; exact: huRcat.
  + rewrite size_cat size_tree_commits.
    by apply: leq_trans hbud'; exact: leqnSn.
  (* the TQUERY at pos: expose the resolved oracle, then commit *)
  rewrite code_link_opr_bind.
  eapply (r_tquery_known b pp pos
            (tval pp sp xss (rcons pos false) tl,
             tval pp sp xss (rcons pos true) tr)
            ((Q ++ tree_commits pp sp xss (rcons pos false) tl)
               ++ tree_commits pp sp xss (rcons pos true) tr)).
  + rewrite !size_cat !size_tree_commits.
    exact: hbud'.
  + rewrite !unzip1_cat !unzip1_tree_commits -catA.
    exact: hfresh.
  rewrite th_eval_tnode bind_ret_l.
  have hq : rcons ((Q ++ tree_commits pp sp xss (rcons pos false) tl)
                     ++ tree_commits pp sp xss (rcons pos true) tr)
              (tnode pos, (tval pp sp xss (rcons pos false) tl,
                           tval pp sp xss (rcons pos true) tr))
            = Q ++ tree_commits pp sp xss pos (BNode tl tr).
    by rewrite /= -cats1 -!catA.
  by rewrite hq; exact: h.
  Unshelve. all: exact: 'unit.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [tree_commits] over a real subtree = the [commitq] entries

    For [t] the shape-subtree at [pos] ([subtree_at (tshape sp) pos =
    Some t]) the fixpoint's children VALUES are exactly [node_children]
    ([tval_children]); hence [tree_commits] = the [int_under]-ordered
    [commitq] entries.  At the root this is [commitq] itself. *)

Lemma tree_commits_E (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  subtree_at (tshape sp) pos = Some t ->
  tree_commits pp sp xss pos t
  = [seq (tnode q, node_children pp sp xss q) | q <- int_under pos t].
Proof.
elim: t pos => [u|tl IHl tr IHr] pos hsub //=.
have hl : subtree_at (tshape sp) (rcons pos false) = Some tl.
  by rewrite -cats1 subtree_at_cat hsub.
have hr : subtree_at (tshape sp) (rcons pos true) = Some tr.
  by rewrite -cats1 subtree_at_cat hsub.
rewrite (IHl _ hl) (IHr _ hr) !map_cat /=.
by rewrite (tval_children pp sp xss pos tl tr hsub).
Qed.

Lemma tree_commits_commitq (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  tree_commits pp sp xss [::] (tshape sp) = commitq pp sp xss.
Proof. by rewrite /commitq -(tree_commits_E pp sp xss) ?subtree_at_nil. Qed.

(* ------------------------------------------------------------------ *)
(** ** Initial block precondition from [tr_inv]

    [tr_inv] forces the 9 shrincs_fxmss_*_loc equal (heap_ignore IGN) and pins the
    rhs SMTCR state to [None]'s shape (RTr None: po=None, tg=emptym,
    tw=[::], rv=false) when [Lst] (rhs) is None — the GEN entry state. *)

Lemma trinv_init s0 s1 :
  tr_inv (s0, s1) ->
  get_heap s1 (shrincs_fxmss_st_loc PP N) = None ->
  trblk None false [::] emptym (s0, s1).
Proof.
move=> /tr_invE [hign hRTr] hst.
rewrite hst in hRTr; case: hRTr => hpo htg htw hrv.
by split.
Qed.

(** [unzip1 emptym-queue] = [::]; the initial committed queue is []. *)
Lemma trblkQ_init s0 s1 :
  trblk None false [::] emptym (s0, s1) ->
  trblkQ None false ([::] : seq (adrs_sf_ch * (N × N))) (s0, s1).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** GEN side conditions: the [r_tree_spec] preconditions at the root

    The reduction's GEN routes the honest tree through TQUERY at the
    root [pos = [::]] of [tshape sp].  The leaf-index bound (every leaf
    path has an in-range key index), the tweak uniqueness and the
    budget [n_a - 1 <= n_max - 1] all come from tree_hop.v's pure layer. *)

Lemma gen_hidx (sp : seq bool) (xss : seq (seq N)) :
  size xss = size (leaf_paths (tshape sp)) ->
  forall p, p \in leaf_paths (tshape sp) ->
    index ([::] ++ p) (leaf_paths (tshape sp)) < size xss.
Proof. by move=> hsz p hp; rewrite cat0s hsz index_mem. Qed.

Lemma gen_uniq (sp : seq bool) :
  uniq ([seq tnode q | q <- int_under [::] (tshape sp)]
        ++ unzip1 ([::] : seq (adrs_sf_ch * (N × N)))).
Proof.
rewrite cats0 map_inj_in_uniq; first exact: int_under_uniq.
move=> p q; rewrite !int_under_internal => hp hq.
exact: (@tnode_tw_inj w l h_sf Hh sp p q hp hq).
Qed.

Lemma gen_bud (sp : seq bool) :
  (size (leaf_paths (tshape sp)) <= n_max)%N ->
  (size ([::] : seq (adrs_sf_ch * (N × N)))
   + size (int_under [::] (tshape sp)) <= n_max - 1)%N.
Proof.
move=> hcap; rewrite /= add0n int_under_size.
exact: internal_count_cap.
Qed.

(** [unzip1] of the committed queue is the committed tweak list. *)
Lemma unzip1_commitq (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  unzip1 (commitq pp sp xss) = commit_tws sp.
Proof. by rewrite /commitq /commit_tws /unzip1 -map_comp. Qed.

(** Setting the SAME location to the SAME value on both sides preserves
    [heap_ignore] for ANY ignore set (the [shrincs_fxmss_*_loc] mirror: they sit
    OUTSIDE [IGN], forced equal, so a two-sided identical write keeps the
    off-[IGN] agreement). *)
Lemma heap_ignore_set_both (L : Locations) (l0 : Location) (v : l0) s0 s1 :
  heap_ignore L (s0, s1) ->
  heap_ignore L (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h l1 hni.
rewrite /get_heap /set_heap !setmE.
case: (_ == _)%B => //=.
exact: (h l1 hni).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Coupling the key sampler with its per-leaf size witness

    [sample_keys n] draws [n] independent [l]-length key lists; the
    coupled continuation may therefore assume every drawn leaf list has
    size [l] ([hkeys]).  Mirrors UDHop's [r_sample_seq_size], one level
    up (a list of fixed-length lists). *)

Lemma r_sample_seq_size_l {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k0 k1 : chList N -> raw_code B) :
  (forall xs : seq N, size xs = n -> ⊢ ⦃ pre ⦄ k0 xs ≈ k1 xs ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xs ← sample_seq dN n ;; k0 xs ≈ xs ← sample_seq dN n ;; k1 xs
  ⦃ post ⦄.
Proof.
elim: n k0 k1 => [|n IH] k0 k1 hk /=.
- exact: (hk [::] erefl).
- rewrite !bind_assoc.
  eapply r_scheme_bind; [exact: prog_valid|] => x.
  rewrite !bind_assoc.
  apply: IH => xs hxs.
  apply: (hk (x :: xs)).
  by rewrite /= hxs.
Qed.

Lemma r_sample_keys_size {B : choiceType} (n : nat) (pre : precond)
    (post : postcond B B) (k0 k1 : chList (chList N) -> raw_code B) :
  (forall xss : seq (seq N),
     size xss = n ->
     (forall xs, xs \in xss -> size xs = l) ->
     ⊢ ⦃ pre ⦄ k0 xss ≈ k1 xss ⦃ post ⦄) ->
  ⊢ ⦃ pre ⦄
    xss ← skeys n ;; k0 xss ≈ xss ← skeys n ;; k1 xss
  ⦃ post ⦄.
Proof.
elim: n k0 k1 => [|n IH] k0 k1 hk /=.
- by apply: (hk [::]) => // xs; rewrite in_nil.
- rewrite !bind_assoc.
  apply: (r_sample_seq_size_l l) => xs hxs.
  rewrite !bind_assoc.
  apply: IH => xss hsz hxss.
  apply: (hk (xs :: xss)); first by rewrite /= hsz.
  move=> ys; rewrite inE => /orP[/eqP ->|hin]; first exact: hxs.
  exact: hxss.
Qed.

(** [get_pre_cond] for [tr_inv] at any location off [IGN] (the
    [shrincs_fxmss_*_loc] mirror: forced equal by [heap_ignore IGN]). *)
Lemma tr_inv_get_pre (l0 : Location) :
  l0.1 \notin domm IGN -> get_pre_cond l0 tr_inv.
Proof.
move=> hl0 s0 s1 [hign _].
exact: hign.
Qed.

Ltac tr_get_pre :=
  apply: tr_inv_get_pre; rewrite /IGN; fmap_solve.

(** Setting a location that is neither in [IGN] nor read by [RTr] (i.e.
    a [shrincs_fxmss_*_loc] OTHER than [shrincs_fxmss_st_loc]) on BOTH sides preserves
    [tr_inv]: [heap_ignore] survives ([heap_ignore_set_both]) and [RTr]
    is read off [shrincs_fxmss_st_loc] + the 4 SMTCR locs, all untouched. *)
Lemma tr_inv_set_fx (l0 : Location) (v : l0) s0 s1 :
  l0.1 != (shrincs_fxmss_st_loc PP N).1 ->
  l0.1 != (tcr_pp_loc TH).1 ->
  l0.1 != (tcr_tgts_loc TH).1 ->
  l0.1 != (tcr_tws_loc TH).1 ->
  l0.1 != (tcr_rev_loc).1 ->
  tr_inv (s0, s1) ->
  tr_inv (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h1 h2 h3 h4 h5 /tr_invE [hign hRTr].
apply: tr_invI; first by apply: heap_ignore_set_both.
rewrite !get_set_heap_neq //; by rewrite eq_sym.
Qed.

Ltac tr_put_tr :=
  let s0 := fresh "s0" in let s1 := fresh "s1" in let hp := fresh "hp" in
  rewrite /put_pre_cond; move=> s0 s1 hp;
  refine (tr_inv_set_fx _ _ _ _ _ _ _ _ _ hp); by [].

Ltac tr_put_pre :=
  repeat (apply: put_pre_cond_conj; last (apply: put_pre_cond_rem; by []));
  tr_put_tr.

(** Extract [heap_ignore IGN] from any precond obtained by extending
    [tr_inv] with [⋊]-conjuncts. *)
Ltac tr_get_hign hh hign :=
  first
    [ move/tr_invE: hh => [hign _]
    | let z := fresh "z" in case: hh => hh z; tr_get_hign hh hign ].

(** Remember + couple a shared [get ℓ] (ℓ off [IGN]) under a precond
    extending [tr_inv]; keeps the [rem_lhs]/[rem_rhs] for later use. *)
Ltac tr_sync_get x :=
  let x' := fresh x "z" in
  eapply r_get_remember_lhs => x;
  eapply r_get_remember_rhs => x';
  eapply (r_fact (x' = x));
    [ let s0 := fresh "s0" in let s1 := fresh "s1" in
      let hh := fresh "hh" in let hl := fresh "hl" in
      let hr := fresh "hr" in let hign := fresh "hign" in
      move=> s0 s1 [[hh hl] hr];
      tr_get_hign hh hign;
      rewrite /rem_inv /= in hl hr;
      rewrite -hr -hl; symmetry; apply: hign; rewrite /IGN; fmap_solve
    | let e := fresh "e" in move=> e; subst x' ].


(** The FORGE verdict: [forge_keep]'s [fverd keepAnchor] equals
    [forge_red]'s classify-and-CHECK, under [tr_inv] + the remembered
    honest state [Lst = Some st].  The FColl CHECK wins by
    [shrincs_fxmss_forgery_case_FColl] (the colliding node's committed target is
    [node_children q], and the [Htree]-collision holds). *)
Lemma r_forge_verdict (st : FXST) (lg : seq M)
    (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  ⊢ ⦃ λ '(s0, s1),
        (tr_inv ⋊ rem_lhs Lst (Some st) ⋊ rem_rhs Lst (Some st)) (s0, s1) ⦄
     ret (fverdN keepA st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 with
          | FColl q x _ =>
              v ← get trev ;;
              ans ← (#assert v ;;
                     tgts ← get ttgts ;;
                     match getm tgts (tnode_index st.2.1 q) with
                     | Some (t0, m0) =>
                         ppo ← get tpp ;;
                         match ppo with
                         | Some pp =>
                             ret ((x != m0)
                                  && (th_eval TH pp t0 x == th_eval TH pp t0 m0))
                         | None =>
                             pp ← dPP ;;
                             #put tpp := Some pp ;;
                             ret ((x != m0)
                                  && (th_eval TH pp t0 x == th_eval TH pp t0 m0))
                         end
                     | None => ret false
                     end) ;;
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && ans)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepA fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ tr_inv (s0, s1) ⦄.
Proof.
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
eapply (r_fact (st.1.2 = fxroot st.1.1 st.2.1 st.2.2)).
  { move=> s0 s1 [[hinv _] hr].
    rewrite /rem_inv /= in hr.
    move/tr_invE: hinv => [_ hRTr].
    by rewrite hr in hRTr; case: hRTr. }
move=> hroot.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
- (* FColl: real CHECK wins (Htree collision at the committed node) *)
  eapply (r_get_rhs_known trev true).
    { move=> s0 s1 [[hinv _] hr].
      rewrite /rem_inv /= in hr.
      move/tr_invE: hinv => [_ hRTr].
      by rewrite hr in hRTr; case: hRTr. }
  rewrite [assertD true _]/= [bind (getr _ _) _]/=.
  eapply (r_get_rhs_known ttgts
            (qmap_from 0 (commitq st.1.1 st.2.1 st.2.2))).
    { move=> s0 s1 [[hinv _] hr].
      rewrite /rem_inv /= in hr.
      move/tr_invE: hinv => [_ hRTr].
      by rewrite hr in hRTr; case: hRTr. }
  (* the colliding node [q] is an internal position; its committed
     target is [node_children q] = the [shrincs_fxmss_forgery_case_FColl]'s [y] *)
  case Eans: P; last first.
  + (* P = false: both sides return false (CHECK result irrelevant) *)
    destruct (qmap_from 0 (commitq st.1.1 st.2.1 st.2.2)
                (tnode_index st.2.1 q)) as [[t0 m0]|] eqn:Eg;
      rewrite Eg /=.
    * eapply (r_get_rhs_known tpp (Some st.1.1)).
        { move=> s0 s1 [[hinv _] hr].
          rewrite /rem_inv /= in hr.
          move/tr_invE: hinv => [_ hRTr].
          by rewrite hr in hRTr; case: hRTr. }
      apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
    * apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
  + (* P = true: the verifying FColl forgery yields the collision *)
    have hvm : fxvermd st.1.1 (fxroot st.1.1 st.2.1 st.2.2)
                 sg.1.1 d sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [qrel [ltr [hq hsub hy hcoll hne]]] :
      exists qrel ltr,
        [/\ q = qrel,
            subtree_at (valtree st.1.1 st.2.1 st.2.2) qrel
              = Some (BNode ltr.1 ltr.2),
            y = (val_bt (nhash st.1.1) (rcons q false) ltr.1,
                 val_bt (nhash st.1.1) (rcons q true) ltr.2),
            nhash st.1.1 q x.1 x.2 = nhash st.1.1 q y.1 y.2
          & x <> y].
	      exact: (shrincs_fxmss_forgery_case_FColl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hvm E).
    subst qrel.
    have hqin : q \in int_under [::] (tshape st.2.1).
      have hq0 := internal_pathsP hsub.
      rewrite internal_paths_valtree in hq0.
      by rewrite int_under_internal.
    have hyc : y = node_children st.1.1 st.2.1 st.2.2 q.
      by rewrite /node_children hsub /= hy.
    rewrite (getm_commitq st.1.1 st.2.1 st.2.2 q hqin) -hyc /=.
    eapply (r_get_rhs_known tpp (Some st.1.1)).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/tr_invE: hinv => [_ hRTr].
        by rewrite hr in hRTr; case: hRTr. }
    move: hcoll hne {E hyc hy hsub}; case: x => x1 x2; case: y => y1 y2 /= hcoll hne.
    rewrite !th_eval_tnode.
    have hans : ((x1, x2) != (y1, y2)) &&
                (nhash st.1.1 q x1 x2 == nhash st.1.1 q y1 y2).
      apply/andP; split; first by apply/eqP.
      by apply/eqP.
    apply r_ret => s0 s1 hpre; split.
    * by rewrite hans.
    * by case: hpre => [[hinv _] _].
- (* FEscape: non-FColl, [keepA] matches on both sides *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- (* FShort: non-FColl *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- (* FAnchor: nulled in both (keepAnchor FAnchor = false) *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
Qed.

(** The IDEAL FORGE verdict: [forge_keep]'s [fverd keepColl] equals
    [forge_red]'s classify-and-CHECK under [SMT false] (CHECK always
    answers [false], matching [keepColl]'s nulling of the FColl case). *)
Lemma r_forge_verdict_ideal (st : FXST) (lg : seq M)
    (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  ⊢ ⦃ λ '(s0, s1),
        (tr_inv ⋊ rem_lhs Lst (Some st) ⋊ rem_rhs Lst (Some st)) (s0, s1) ⦄
     ret (fverdN keepC st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 with
          | FColl q x _ =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && false)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepC fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ tr_inv (s0, s1) ⦄.
Proof.
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
- (* FColl: ideal CHECK answers false; [keepColl FColl = false] *)
  apply r_ret => s0 s1 hpre; split.
  + by rewrite andbF.
  + by case: hpre => [[hinv _] _].
- apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
- apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
Qed.

Lemma R_tree_real (b : bool) :
  perfect IG (G6 b) (R_tree b ∘ SMT true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ tr_inv).
{ rewrite /tr_inv. ssprove_invariant. by rewrite /rel_empty /RTr. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5 /gen5_body.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/tr_invE: hinv => [hign _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1 (hign (shrincs_fxmss_st_loc PP N)) // /IGN; fmap_solve. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 => [pk|] e0; first by discriminate e0.
  (* drop the machinery; switch to the explicit block precondition *)
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), trblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    apply: (trinv_init s0 s1 hinv).
    rewrite /rem_inv /= in hrem1.
    by rewrite -hrem1. }
  simpl.
  (* the COLLQ pin: SM-TCR's lazy pp is sampled here, coupled to G6f's
     eager [pp ← dPP] *)
  rewrite (resolve_cq true (encode_adrs (gadrs (0, 0))) (inr (inl [::]))).
  eapply (r_get_bind_rhs tpp None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (trblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  (* the dead [dN], [dR], the keys and the digests: pointwise sync,
     SM-TCR state untouched *)
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_sample_keys_size (size (leaf_paths (tshape arg)))).
  move=> xss hxsz hkeys; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  eapply (r_scheme_bind (fillc (iota 0 n_max) emptym));
    first exact: fill_code_valid.
  move=> sd; cbv beta.
  (* grindability through COLLQ: [tr_gcheck] = [sd_grindable], so the
     two #asserts coincide *)
  rewrite code_link_bind.
  eapply (r_gcheck_spec true pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  (* the honest tree, built bottom-up through TQUERY *)
  rewrite code_link_bind.
  eapply (r_tree_spec true pp arg xss _ hkeys [::] (tshape arg) [::]).
  + apply: gen_hidx; by rewrite hxsz.
  + exact: gen_uniq.
  + by apply: gen_bud.
  rewrite tval_root tree_commits_commitq /=.
  (* GETPP: reveal pp, flip the phase *)
  rewrite (resolve_gp true Datatypes.tt).
  eapply (r_get_bind_rhs tpp (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (trblk_set_rev _ _ _ _ _ hpre). }
  (* the COMMIT tail: both sides store the same state and return *)
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrev htws htgts.
  split; first by [].
  apply: tr_invI.
  - apply: heap_ignore_set_both.
    apply: heap_ignore_set_both.
    exact: hign.
  - get_heap_simpl.
    rewrite hpp hrev htws htgts /=.
    split=> //.
    by rewrite unzip1_commitq.
- (* SIGN: identical opr-free body, [code_link] is the identity.  The
     lifted body reads the used-set [us], gates on
     [leaf_okP … arg.2 && arg.2 ∉ domm us], and — when valid+fresh —
     signs the presampled digest at slot [lidx … arg.2]; both sides run
     the SAME body so every get/put/assert mirrors. *)
  rewrite /sign5 /sign5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. }
  move=> sc.
  ssprove_sync => hsc.
  ssprove_sync. { tr_get_pre. }
  move=> v.
  ssprove_sync => vSome.
  ssprove_sync. { tr_get_pre. }
  move=> us.
  ssprove_sync. { tr_get_pre. }
  move=> lg.
  ssprove_sync. { tr_get_pre. }
  move=> mp.
  ssprove_sync. { tr_get_pre. }
  move=> tb.
  ssprove_sync. { tr_get_pre. }
  move=> sd.
  case: [&& leaf_okP h_sf (getSome v vSome).2.1 arg.2 & arg.2 \notin domm us];
    last first.
  { ssprove_sync. { tr_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  case: (sd (lidx h_sf (getSome v vSome).2.1 arg.2)) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
    + ssprove_sync. { tr_put_pre. }
      ssprove_sync. { tr_put_pre. }
      by apply r_ret.
    + ssprove_sync. { tr_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
	  case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
  + ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    by apply r_ret.
  + ssprove_sync. { tr_put_pre. } by apply r_ret.
- (* HASH: identical opr-free body, same pure sync as SIGN *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. }
  move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { tr_get_pre. }
  move=> mp.
  case: (mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
  by apply r_ret.
- (* FORGE: bookkeeping is now b-unconditional on BOTH sides; only the
     returned verdict is gated by [b].  Sync the shared bookkeeping, then
     [case: b]: the [b = true] verdict reuses [r_forge_verdict] UNCHANGED
     (the classify-and-CHECK at the bare-verdict layer), the [b = false]
     verdict is the constant [false] on both sides. *)
  destruct arg as [m sg].
  rewrite /forge_keep /forge_keep_body /forge_red.
  ssprove_code_simpl. simpl.
  (* the opr-free prefix: sync each shared get + assert; remember [Lst]
     to feed [RTr] at the CHECK *)
  ssprove_sync. { tr_get_pre. } move=> fc.
  ssprove_code_simpl. simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => sto0.
  eapply r_get_remember_rhs => sto1.
  eapply (r_fact (sto1 = sto0)).
    { move=> s0 s1 [[hinv h0] h1].
      move/tr_invE: hinv => [hign _].
      rewrite /rem_inv /= in h0 h1.
      by rewrite -h0 -h1 (hign (shrincs_fxmss_st_loc PP N) ltac:(rewrite /IGN; fmap_solve)). }
  move=> e; subst sto1.
  eapply r_assertD_same. move=> stSome.
  have Esto : sto0 = Some (getSome sto0 stSome).
    by case: sto0 stSome => [a|] stSome.
  set st := getSome sto0 stSome in Esto *.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. } move=> lg.
  ssprove_sync. { tr_get_pre. } move=> mp.
  ssprove_sync. { tr_get_pre. } move=> tb.
  ssprove_sync. { tr_get_pre. } move=> sd.
  (* the md sample/RO-lookup: shared, then the two verdicts *)
  case Emd: (mp (sg.1.2, (st.1, (sg.1.1, m)))) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    rewrite Esto.
    case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
    exact: (r_forge_verdict st lg tb sd m sg d). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
  rewrite Esto.
  case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
  exact: (r_forge_verdict st lg tb sd m sg d).
Qed.

Lemma R_tree_ideal (b : bool) :
  perfect IG (G7 b) (R_tree b ∘ SMT false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ tr_inv).
{ rewrite /tr_inv. ssprove_invariant. by rewrite /rel_empty /RTr. }
simplify_eq_rel arg.
- (* GEN: verbatim the real-side proof, [SMT false] *)
  rewrite /gen5 /gen5_body.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/tr_invE: hinv => [hign _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1 (hign (shrincs_fxmss_st_loc PP N)) // /IGN; fmap_solve. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), trblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    apply: (trinv_init s0 s1 hinv).
    rewrite /rem_inv /= in hrem1.
    by rewrite -hrem1. }
  simpl.
  rewrite (resolve_cq false (encode_adrs (gadrs (0, 0))) (inr (inl [::]))).
  eapply (r_get_bind_rhs tpp None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (trblk_set_pp pp _ _ _ _ _ hpre). }
  simpl.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dN)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x0; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid.
  move=> x1; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (@sample_keys_valid l N dN emptym [interface] _)).
  eapply (r_sample_keys_size (size (leaf_paths (tshape arg)))).
  move=> xss hxsz hkeys; cbv beta.
  rewrite code_link_bind (code_link_scheme _ _ _ _
             (fill_code_valid D dD emptym [interface] (iota 0 n_max) emptym)).
  eapply (r_scheme_bind (fillc (iota 0 n_max) emptym));
    first exact: fill_code_valid.
  move=> sd; cbv beta.
  rewrite code_link_bind.
  eapply (r_gcheck_spec false pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  rewrite code_link_bind.
  eapply (r_tree_spec false pp arg xss _ hkeys [::] (tshape arg) [::]).
  + apply: gen_hidx; by rewrite hxsz.
  + exact: gen_uniq.
  + by apply: gen_bud.
  rewrite tval_root tree_commits_commitq /=.
  rewrite (resolve_gp false Datatypes.tt).
  eapply (r_get_bind_rhs tpp (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (trblk_set_rev _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrev htws htgts.
  split; first by [].
  apply: tr_invI.
  - apply: heap_ignore_set_both.
    apply: heap_ignore_set_both.
    exact: hign.
  - get_heap_simpl.
    rewrite hpp hrev htws htgts /=.
    split=> //.
    by rewrite unzip1_commitq.
- (* SIGN: pure sync (opr-free); the lifted used-set/leaf-id body,
     mirrored on both sides exactly as in [R_tree_real]. *)
  rewrite /sign5 /sign5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. }
  move=> sc.
  ssprove_sync => hsc.
  ssprove_sync. { tr_get_pre. }
  move=> v.
  ssprove_sync => vSome.
  ssprove_sync. { tr_get_pre. }
  move=> us.
  ssprove_sync. { tr_get_pre. }
  move=> lg.
  ssprove_sync. { tr_get_pre. }
  move=> mp.
  ssprove_sync. { tr_get_pre. }
  move=> tb.
  ssprove_sync. { tr_get_pre. }
  move=> sd.
  case: [&& leaf_okP h_sf (getSome v vSome).2.1 arg.2 & arg.2 \notin domm us];
    last first.
  { ssprove_sync. { tr_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  case: (sd (lidx h_sf (getSome v vSome).2.1 arg.2)) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
    + ssprove_sync. { tr_put_pre. }
      ssprove_sync. { tr_put_pre. }
      by apply r_ret.
    + ssprove_sync. { tr_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
	  case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
  + ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    by apply r_ret.
  + ssprove_sync. { tr_put_pre. } by apply r_ret.
- (* HASH: pure sync *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. }
  move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { tr_get_pre. }
  move=> mp.
  case: (mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
  by apply r_ret.
- (* FORGE: ideal CHECK = false = keepColl(FColl).  As in the real side,
     the bookkeeping is now b-unconditional; [case: b] at the verdict
     reuses [r_forge_verdict_ideal] for [b = true], constant [false] for
     [b = false]. *)
  destruct arg as [m sg].
  rewrite /forge_keep /forge_keep_body /forge_red.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. } move=> fc.
  ssprove_code_simpl. simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => sto0.
  eapply r_get_remember_rhs => sto1.
  eapply (r_fact (sto1 = sto0)).
    { move=> s0 s1 [[hinv h0] h1].
      move/tr_invE: hinv => [hign _].
      rewrite /rem_inv /= in h0 h1.
      by rewrite -h0 -h1 (hign (shrincs_fxmss_st_loc PP N) ltac:(rewrite /IGN; fmap_solve)). }
  move=> e; subst sto1.
  eapply r_assertD_same. move=> stSome.
  have Esto : sto0 = Some (getSome sto0 stSome).
    by case: sto0 stSome => [a|] stSome.
  set st := getSome sto0 stSome in Esto *.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_get_pre. } move=> lg.
  ssprove_sync. { tr_get_pre. } move=> mp.
  ssprove_sync. { tr_get_pre. } move=> tb.
  ssprove_sync. { tr_get_pre. } move=> sd.
  case Emd: (mp (sg.1.2, (st.1, (sg.1.1, m)))) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { tr_put_pre. }
    ssprove_sync. { tr_put_pre. }
    rewrite Esto.
    case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
    exact: (r_forge_verdict_ideal st lg tb sd m sg d). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { tr_put_pre. }
  ssprove_sync. { tr_put_pre. }
  rewrite Esto.
  case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
  exact: (r_forge_verdict_ideal st lg tb sd m sg d).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The hop theorem (claim:fxmss-tree-tcr) *)

Theorem Tree_hop (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G6 b) (G7 b) A = AdvOf (SMTCR_game TH CTH (n_max - 1)) (A ∘ R_tree b).
Proof.
rewrite (Adv_perfect_l (R_tree_real b)) (Adv_perfect_r (R_tree_ideal b)).
by rewrite Adv_reduction.
Qed.

End FXMSSTreeHopProof.
