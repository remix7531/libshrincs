(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.tcrx_hop_proof

    Hop 8 (G7f -> G8f, [claim:fxmss-struct-tcr]): the [R_x] reduction
    package and the two
    [perfect] lemmas that assemble [Tcrx_hop], the direct analogue of
    the tree hop for the TWO structure-mismatch forgery cases (FEscape
    and FShort). It consumes [fxmss.tree_hop], [fxmss.late_games]
    (the [Gkeep keep b] game family), and [Sec.lib.games.tcrx] (the
    TCR-exclusive game interface).

    Its simulation follows [fxmss.tree_hop_proof]'s [R_tree] skeleton,
    with these structural changes:

    - [Txc] sums BOTH the tree-node hash [Htree] (message [inl (x,y)])
      AND the anchor compression [Tl] (message [inr ends]) into ONE
      [th_eval], because the F.9->F.10 collision crosses the two.  The
      collection [Cxc] therefore carries only the F-chain ([inl]) and
      the [Hgrind] grinding ([inr]) members; the anchor [Tl] is now
      committed as a TARGET (XQUERY), not via XCOLLQ.
    - [paired t] = the decoded type is TY_TREE_SF or TY_WOTS_PK_SF;
      [omega] swaps [shrincs_fxmss_adr_tree (z,i) <-> shrincs_fxmss_adr_pk (z,i)] (the canonical
      involution), identity elsewhere.
    - COMMIT routes EVERY node identifier of the honest tree through
      XQUERY at the type the honest signer uses: internal nodes at
      [shrincs_fxmss_adr_tree], message [inl (children)]; anchors at [shrincs_fxmss_adr_pk], message
      [inr (chain_ends)].  The F-chains and grinding run via XCOLLQ.
      Budget [2*n_max - 1 >= (n_a - 1) + n_a].
    - FORGE classifies with [shrincs_fxmss_forgery_case]; on FEscape submits XCHECK at the
      PARTNER tweak [shrincs_fxmss_adr_tree (shrincs_fxmss_pos_id q)] (message [inl x]) of the
      honest anchor's committed [shrincs_fxmss_adr_pk]; on FShort the mirror (XCHECK
      at [shrincs_fxmss_adr_pk (shrincs_fxmss_pos_id q)], message [inr (complete_ends)]).

    The target budget [2*n_max - 1] covers all internal nodes and leaves. *)

Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-prefix".
From Sec.lib Require Import prelude math.bin_tree math.merkle math.chain.
From Model Require Import math.encoding.
From Sec.lib Require Import sig.scheme games.thf games.tcrx toolkit.sample_seq.
From Sec.lib Require Import toolkit.relational_rules chain.core wots.games wots.tcr_hop.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games
  fxmss.scheme fxmss.games fxmss.late_games fxmss.tree_hop.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-prefix".

(** A generic [seq] permutation helper, proven BEFORE the package/sep
    scopes are opened (inside them the [perm_catCA] rewrite of [++] does
    not fire — the documented sep_scope reparse). *)
Lemma perm_mid3 (T : eqType) (a Lt Rt Q : seq T) :
  perm_eq (a ++ Lt ++ Rt ++ Q) (Lt ++ Rt ++ a ++ Q).
Proof.
apply: (perm_trans (y := Lt ++ a ++ Rt ++ Q)).
  by rewrite perm_catCA.
rewrite perm_cat2l.
by rewrite perm_catCA.
Qed.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Section FXMSSTCRXHopProof.

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
Context (Hh : (h_sf <= 255)%N).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(** Hash-domain inhabitant for the dead branches of the XQUERY/XCOLLQ
    post-processing (the answer is always the [inl]/[inr] branch the
    scheme uses; a closed [N] term is needed for the never-taken one).
    Exactly TreeHopProof's [n0]. *)
Context (n0 : N).

(* ------------------------------------------------------------------ *)
(** ** Shorthands (TreeHopProof's) *)

Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation posok := (shrincs_fxmss_pos_ok h_sf).
Local Notation subposok := (shrincs_fxmss_sub_pos_ok h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation valtree := (value_tree_x PP N F Tl h_sf).
Local Notation fxroot := (shrincs_fxmss_root_x PP N F Tl Htree h_sf).

(** Internal-node tweak (tree_hop.v's [tnode_tw]). *)
Local Notation tnode := (@tnode_tw w l h_sf).

(* ------------------------------------------------------------------ *)
(** ** The thf [Txc] for the structure hop (the proof architecture "Structure hop")

    [th_T := adrs_sf_ch], [th_M := (N × N) ∐ ('list N)] (children OR
    ends), [th_N := N], evaluated by [Htree]/[Tl] at the decoded
    address according to the message constructor. *)

Definition Txc : thf :=
  {| th_PP := PP ; th_T := adrs_sf_ch ;
     th_M := (N × N) ∐ ('list N) ; th_N := N ;
     th_eval := fun pp t m =>
       match m with
       | inl xy => Htree pp (decode_tweak t) xy
       | inr xs => Tl pp (decode_tweak t) xs
       end ;
     th_dPP := dPP ;
     th_dM := {code x ← dN ;; y ← dN ;; ret (inl (x, y) : (N × N) ∐ ('list N)) } ;
     th_dN := dN |}.

(** [Cxc]: the F-chain ([inl]) and [Hgrind] grinding ([inr]) members
    of the collection (the anchor [Tl] is committed as a target, so it
    is in [Txc]'s eval, not here). *)

Definition Cxc : thf_coll Txc :=
  Build_thf_coll Txc adrs_sf_ch (N ∐ (D × 'nat)) (N ∐ 'nat)
    (fun pp t x =>
       match x with
       | inl y => inl (F pp (decode_tweak t) y)
       | inr dc => inr (Hgrind pp (decode_tweak t) dc : 'nat)
       end).

(* ------------------------------------------------------------------ *)
(** ** The partition predicate and the pairing involution

    [paired t] = the decoded address is a TREESTATEFUL or WOTSPKSF
    address (the two halves T_2 / T_3 of the TCR-exclusive partition);
    [omega] swaps [shrincs_fxmss_adr_tree (z,i) <-> shrincs_fxmss_adr_pk (z,i)] (same node id), the
    identity off the two paired classes (and on non-canonical tuples,
    where [decode_tweak] falls back). *)

Definition paired (t : adrs_sf_ch) : bool :=
  adrs_type (decode_tweak t) \in [:: TY_TREE_SF ; TY_WOTS_PK_SF].

Definition omega (t : adrs_sf_ch) : adrs_sf_ch :=
  match decode_tweak t with
  | address.Fxmss z i => encode_adrs (address.Wc_pk z i)
  | address.Wc_pk z i => encode_adrs (address.Fxmss z i)
  | a => encode_adrs a
  end.

(** The two committed tweak families: internal nodes at [shrincs_fxmss_adr_tree],
    anchors at [shrincs_fxmss_adr_pk] (both keyed by [shrincs_fxmss_pos_id]). *)
Local Notation panchor p :=
  (@encode_adrs l w (@shrincs_fxmss_wots_pk_adrs l w (posid p))).

(** [tnode q = encode_adrs (shrincs_fxmss_adr_tree (h_sf - size q) (idx_of_path q))];
    spelled in [shrincs_fxmss_pos_id] form to match [panchor]. *)
Lemma tnode_posid (q : seq bool) :
  tnode q = encode_adrs (shrincs_fxmss_adr_tree (posid q).1 (posid q).2).
Proof. by rewrite /tnode_tw /shrincs_fxmss_pos_id. Qed.

(** [omega] swaps the two committed families. *)
Lemma omega_tnode (q : seq bool) : omega (tnode q) = panchor q.
Proof. by rewrite /omega /tnode_tw decode_tweakK /shrincs_fxmss_pos_id. Qed.

Lemma omega_panchor (p : seq bool) : omega (panchor p) = tnode p.
Proof. by rewrite /omega decode_tweakK /shrincs_fxmss_pos_id tnode_posid. Qed.

(** Both committed families are [paired]. *)
Lemma paired_tnode (q : seq bool) : paired (tnode q).
Proof. by rewrite /paired /tnode_tw decode_tweakK /= !inE eqxx. Qed.

Lemma paired_panchor (p : seq bool) : paired (panchor p).
Proof. by rewrite /paired decode_tweakK /= !inE eqxx orbT. Qed.

(* ------------------------------------------------------------------ *)
(** ** [Txc] / [Cxc] evaluation bridges (decode_tweakK) *)

(** XQUERY's [th_eval] answer at an encoded [shrincs_fxmss_adr_tree] tweak with [inl]
    message is the honest node hash. *)
Lemma th_eval_xnode pp (q : seq bool) (x y : N) :
  th_eval Txc pp (tnode q) (inl (x, y)) = nhash pp q x y.
Proof. by rewrite /= /tnode_tw decode_tweakK. Qed.

(** XQUERY's [th_eval] answer at an encoded [shrincs_fxmss_adr_pk] tweak with [inr]
    message is the anchor compression [Tl]. *)
Lemma th_eval_xanchor pp (zi : nat * nat) (ends : seq N) :
  th_eval Txc pp (encode_adrs (shrincs_fxmss_wots_pk_adrs zi)) (inr ends)
  = Tl pp (shrincs_fxmss_wots_pk_adrs zi) ends.
Proof. by rewrite /= decode_tweakK. Qed.

(** [Cxc]'s F-member at an encoded chain address. *)
Lemma collq_xF_E pp (a : adrs_sf) (x : N) :
  (if tc_eval Cxc pp (encode_adrs a) (inl x) is inl y then y else x)
  = F pp a x.
Proof. by rewrite {1}/tc_eval /= decode_tweakK. Qed.

(** [Cxc]'s Hgrind-member at an encoded grind address. *)
Lemma collq_xH_E pp (a : adrs_sf) (dc : D * nat) :
  (if tc_eval Cxc pp (encode_adrs a) (inr dc) is inr h then h else 0%N)
  = Hgrind pp a dc.
Proof. by rewrite {1}/tc_eval /= decode_tweakK. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure value layer (TreeHopProof's, redefined locally)

    [anchor_val] = the value-tree leaf fn; [tval] = the bottom-up
    value of a shape-subtree; [tval_root = fxroot]. *)

Local Notation fpk_of zi := (shrincs_fxmss_wots_public_key PP N F Tl zi.1 zi.2).
Local Notation fchain_ends zi := (chain_ends PP N F zi.1 zi.2).
Local Notation cadrs zi i pos := (shrincs_fxmss_wots_chain_adrs zi i pos).
Local Notation padrs zi := (shrincs_fxmss_wots_pk_adrs zi).
Local Notation gadrs zi := (shrincs_fxmss_wots_grind_adrs zi).

Definition anchor_val (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (p : seq bool) : N :=
  fpk_of (posid p) pp (nth [::] xss (index p (leaf_paths (tshape sp)))).

Fixpoint tval (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : N :=
  match t with
  | BLeaf _ => anchor_val pp sp xss pos
  | BNode tl tr =>
      nhash pp pos (tval pp sp xss (rcons pos false) tl)
                   (tval pp sp xss (rcons pos true) tr)
  end.

Lemma tval_valbt (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) :
  tval pp sp xss pos t
  = val_bt (nhash pp) pos
      (bt_posmap (fun p => anchor_val pp sp xss p) pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
by rewrite IHl IHr.
Qed.

Lemma tval_root (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  tval pp sp xss [::] (tshape sp) = fxroot pp sp xss.
Proof. by rewrite tval_valbt. Qed.

(** The anchor message committed at a leaf position: the honest
    [chain_ends] of that leaf's key list. *)
Definition anchor_ends (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (p : seq bool) : seq N :=
  fchain_ends (posid p) pp (nth [::] xss (index p (leaf_paths (tshape sp)))).

(** Pure recursive ends value mirroring [x_cends] (TreeHopProof's
    [fcends]). *)
Local Notation fwchain pp zi i x :=
  (chain (fun pos y => F pp (cadrs zi i pos) y) x 0 w.-1).

Fixpoint fcends pp (zi : nat * nat) (i : nat) (xs : seq N) : seq N :=
  match xs with
  | [::] => [::]
  | x :: xs' => fwchain pp zi i x :: fcends pp zi i.+1 xs'
  end.

Lemma fcends_E pp (zi : nat * nat) (i : nat) (xs : seq N) :
  fcends pp zi i xs
  = [seq chain (fun pos y => F pp (cadrs zi ix.1 pos) y) ix.2 0 w.-1
    | ix <- zip (iota i (size xs)) xs].
Proof. by elim: xs i => [|x xs IH] i //=; rewrite IH. Qed.

Lemma fcends_chain_ends pp (zi : nat * nat) (xs : seq N) :
  size xs = l -> fcends pp zi 0 xs = fchain_ends zi pp xs.
Proof.
move=> hxs; rewrite fcends_E !chain_ends_def hxs.
apply/eq_in_map => -[i x] _ /=; by case: zi.
Qed.

(** The anchor value: [Tl] at [padrs] of the ends IS [shrincs_fxmss_wots_public_key]. *)
Lemma anchor_pk pp (zi : nat * nat) (xs : seq N) :
  Tl pp (padrs zi) (fchain_ends zi pp xs) = fpk_of zi pp xs.
Proof. by rewrite !shrincs_fxmss_wots_public_key_def; case: zi. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure layer: the structure-mismatch forgeries yield TCR-X data

    The shrincs_fxmss_forgery_case classifier ([late_games.shrincs_fxmss_forgery_case]) is [merkle.extract]
    against the honest value tree.  FEscape gives a forged
    [Htree]-value at an honest ANCHOR position (= the anchor's [Tl]
    compression value); FShort a forged anchor whose [Tl]-value is the
    honest [Htree]-node value at an honest INTERNAL position.  Both are
    the TCR-X collisions across the [shrincs_fxmss_adr_tree]/[shrincs_fxmss_adr_pk] partner tweaks. *)

Local Notation shrincs_fxmss_forgery_case_at_N :=
  (shrincs_fxmss_forgery_case PP N D F Tl Hgrind Htree h_sf).
Local Notation fxvermd :=
  (shrincs_fxmss_verify_md PP N D F Tl Hgrind Htree S_wn h_sf).
Local Notation frecover := (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind).

(** The verify equation extracted from [fxvermd] (TreeHop's
    [shrincs_fxmss_verify_md_val_ap]; restated locally). *)
Lemma x_fxvermd_val_ap pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  val_ap (nhash pp) [::] (path_of_idx (h_sf - zi.1) zi.2) ap
         (frecover pp zi md ws)
  = Some (val_bt (nhash pp) [::] (valtree pp sp xss)).
Proof.
rewrite /shrincs_fxmss_verify_md => /and4P[_ _ _ /eqP].
by rewrite /shrincs_fxmss_root_x.
Qed.

(** FEscape extraction: position [q] is an honest ANCHOR, the forged
    node value [Htree pp (shrincs_fxmss_adr_tree shrincs_fxmss_pos_id q) x = a0] equals the honest
    anchor value at [q]. *)
Lemma shrincs_fxmss_forgery_case_FEscape pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) (q : seq bool) (x : N * N) (a0 : N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  shrincs_fxmss_forgery_case_at_N pp sp xss zi md ws ap = FEscape q x a0 ->
  [/\ subtree_at (tshape sp) q = Some (BLeaf tt),
      a0 = anchor_val pp sp xss q
    & nhash pp q x.1 x.2 = a0].
Proof.
move=> hver hcase.
have hval := x_fxvermd_val_ap _ _ _ _ _ _ _ hver.
have hok := extractP hval.
have heq : extract (nhash pp) [::] (valtree pp sp xss)
             (path_of_idx (h_sf - zi.1) zi.2) ap (frecover pp zi md ws)
           = FEscape q x a0 by exact: hcase.
rewrite heq in hok.
move: hok => [qrel [hq hsub hh]].
rewrite cat0s in hq; subst qrel.
move: hsub; rewrite /value_tree_x subtree_at_posmap.
case hsh: (subtree_at (tshape sp) q) => [[u|tl tr]|] //= [hav].
clear hsh; split.
- by case: u.
- by rewrite /anchor_val -hav.
- by rewrite hh /anchor_val -hav.
Qed.

(** FShort extraction: position [q] is an honest INTERNAL node, the
    forged anchor [frecover = a] equals the honest node value
    [nhash pp q (...) = a]. *)
Lemma shrincs_fxmss_forgery_case_FShort pp sp xss (zi : nat * nat) md (ws : seq N * nat)
    (ap : seq N) (q : seq bool) (a : N) :
  fxvermd pp (fxroot pp sp xss) zi md ws ap ->
  shrincs_fxmss_forgery_case_at_N pp sp xss zi md ws ap = FShort q a ->
  exists ltr,
    [/\ subtree_at (tshape sp) q = Some (BNode ltr.1 ltr.2),
        posid q = zi,
        a = frecover pp zi md ws
      & a = nhash pp q (tval pp sp xss (rcons q false) ltr.1)
                       (tval pp sp xss (rcons q true) ltr.2)].
Proof.
move=> hver hcase.
have hz1 : (zi.1 <= h_sf)%N by move: hver => /and4P[h _ _ _].
have hz2 : (zi.2 < 2 ^ (h_sf - zi.1))%N by move: hver => /and4P[_ /andP[h _] _ _].
have hval := x_fxvermd_val_ap _ _ _ _ _ _ _ hver.
have hok := extractP hval.
have heq : extract (nhash pp) [::] (valtree pp sp xss)
             (path_of_idx (h_sf - zi.1) zi.2) ap (frecover pp zi md ws)
           = FShort q a by exact: hcase.
rewrite heq in hok.
move: hok => [lr [rr [hq ha' hsub hval2]]].
rewrite cat0s in hq; subst q.
have hposid : posid (path_of_idx (h_sf - zi.1) zi.2) = zi.
  rewrite /shrincs_fxmss_pos_id size_path_of_idx idx_of_path_of_idx // subKn //.
  by case: (zi).
move: hsub; rewrite /value_tree_x subtree_at_posmap.
case hsh: (subtree_at (tshape sp) (path_of_idx (h_sf - zi.1) zi.2))
  => [[u|tl tr]|] //= [hl hr].
exists (tl, tr); split.
- by [].
- exact: hposid.
- by rewrite ha'.
- rewrite ha' hval2 /= -hl -hr.
  by rewrite !tval_valbt.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The TCRX game and its import (the reduction's import) *)

Local Notation TCRX b := (TCRX_game Txc Cxc paired omega (2 * n_max - 1) b).
Local Notation I_X := (I_TCRX Txc Cxc).

(** Opsigs as committed to [I_TCRX Txc Cxc]. *)
Definition x_xqo : opsig := (XQUERY, (th_T Txc × th_M Txc, th_N Txc)).
Definition x_gpo : opsig := (XGETPP, ('unit, th_PP Txc)).
Definition x_cko : opsig :=
  (XCHECK, (('nat × th_T Txc) × th_M Txc, 'bool)).
Definition x_cqo : opsig := (XCOLLQ, (tc_T Cxc × tc_M Cxc, tc_N Cxc)).

(* ------------------------------------------------------------------ *)
(** ** The oracle-routed leaf loops (chains + grinding via XCOLLQ)

    Identical in shape to TreeHopProof's [tr_walk]/[tr_cends]/[tr_grind]
    etc.; the F-chain members and grinding answer through XCOLLQ. *)

(** Walk chain [i] of anchor [zi] up from value [x] for [n] steps, one
    XCOLLQ (F member, [inl]) per step. *)
Fixpoint x_walk (zi : nat * nat) (i k n : nat) (x : N) : raw_code N :=
  if n is n'.+1
  then opr x_cqo (encode_adrs (cadrs zi i k), inl x)
         (λ r, x_walk zi i k.+1 n' (if r is inl y then y else x))
  else ret x.

#[local] Instance x_walk_valid (L : Locations) zi i k n (x : N) :
  ValidCode L I_X (x_walk zi i k n x).
Proof.
elim: n k x => [|n IH] k x /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; exact: IH.
Qed.

(** Per-chain ends of anchor [zi] from key list [xs]. *)
Fixpoint x_cends (zi : nat * nat) (i : nat) (xs : seq N) :
    raw_code (chList N) :=
  match xs with
  | [::] => ret [::]
  | x :: xs' =>
      e ← x_walk zi i 0 w.-1 x ;;
      es ← x_cends zi i.+1 xs' ;;
      ret (e :: es)
  end.

#[local] Instance x_cends_valid (L : Locations) zi i xs :
  ValidCode L I_X (x_cends zi i xs).
Proof.
elim: xs i => [|x xs IH] i /=.
- apply valid_ret.
- eapply valid_bind; first exact: x_walk_valid.
  move=> e; eapply valid_bind; first exact: IH.
  move=> es; apply valid_ret.
Qed.

(** Grind one anchor's slot: route Hgrind through XCOLLQ ([inr (d,c)]).*)
Fixpoint x_grind (zi : nat * nat) (d : D) (cs : seq nat) :
    raw_code (chList 'nat) :=
  match cs with
  | [::] => ret [::]
  | c :: cs' =>
      opr x_cqo (encode_adrs (gadrs zi), inr (d, c))
        (λ r, hs ← x_grind zi d cs' ;;
              ret ((if r is inr h then h else 0) :: hs))
  end.

#[local] Instance x_grind_valid (L : Locations) zi d cs :
  ValidCode L I_X (x_grind zi d cs).
Proof.
elim: cs => [|c cs IH] /=.
- apply valid_ret.
- eapply valid_opr; first by fmap_solve.
  move=> r; eapply valid_bind; [exact: IH|].
  move=> hs; apply valid_ret.
Qed.

Definition x_slot_grind (sp : seq bool) (sd : chMap 'nat D) (j : nat) :
    raw_code 'bool :=
  match getm sd j with
  | Some d =>
      hs ← x_grind (posid (spath sp j)) d (iota 0 c_max) ;;
      ret (has (@grind_prp w l S_wn) hs)
  | None => ret true
  end.

#[local] Instance x_slot_grind_valid (L : Locations) sp sd j :
  ValidCode L I_X (x_slot_grind sp sd j).
Proof.
rewrite /x_slot_grind; case: (getm sd j) => [d|]; last by apply valid_ret.
eapply valid_bind; first exact: x_grind_valid.
move=> hs; apply valid_ret.
Qed.

Fixpoint x_gcheck (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) :
    raw_code 'bool :=
  match js with
  | [::] => ret true
  | j :: js' =>
      b ← x_slot_grind sp sd j ;;
      bs ← x_gcheck sp sd js' ;;
      ret (b && bs)
  end.

#[local] Instance x_gcheck_valid (L : Locations) sp sd js :
  ValidCode L I_X (x_gcheck sp sd js).
Proof.
elim: js => [|j js IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: x_slot_grind_valid.
  move=> b; eapply valid_bind; first exact: IH.
  move=> bs; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The bottom-up tree commit (the heart of GEN)

    BOTH internal nodes and anchors are XQUERY TARGETS: a leaf at [pos]
    computes its ends (XCOLLQ chains) then commits [(panchor pos, inr
    ends)] via XQUERY (the answer = anchor value); an internal node
    commits [(tnode pos, inl (children))] via XQUERY (answer = node
    value). *)
Fixpoint x_tree (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : raw_code N :=
  match t with
  | BLeaf _ =>
      ends ← x_cends (posid pos) 0
               (nth [::] xss (index pos (leaf_paths (tshape sp)))) ;;
      opr x_xqo (panchor pos, inr ends) (λ y, ret y)
  | BNode tl tr =>
      lv ← x_tree sp xss (rcons pos false) tl ;;
      rv ← x_tree sp xss (rcons pos true) tr ;;
      opr x_xqo (tnode pos, inl (lv, rv)) (λ y, ret y)
  end.

#[local] Instance x_tree_valid (L : Locations) sp xss pos t :
  ValidCode L I_X (x_tree sp xss pos t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- eapply valid_bind; first exact: x_cends_valid.
  move=> ends; eapply valid_opr; first by fmap_solve.
  move=> y; apply valid_ret.
- eapply valid_bind; first exact: IHl.
  move=> lv; eapply valid_bind; first exact: IHr.
  move=> rv; eapply valid_opr; first by fmap_solve.
  move=> y; apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The combined commit-order list (tweaks)

    [xunder pos t] is the commit order of the TWEAKS over sub-shape [t]
    at [pos]: a leaf contributes [panchor pos], an internal node
    contributes its children-target [tnode pos] AFTER its subtrees.
    This interleaves the two committed families ([panchor] at leaves,
    [tnode] at internal nodes) in bottom-up order. *)

Fixpoint xunder (pos : seq bool) (t : bt unit) : seq adrs_sf_ch :=
  match t with
  | BLeaf _ => [:: panchor pos]
  | BNode tl tr =>
      xunder (rcons pos false) tl ++ xunder (rcons pos true) tr
        ++ [:: tnode pos]
  end.

(** [(2a-1) + (2b-1) + 1 = 2(a+b) - 1] for [a,b >= 1]. *)
Lemma xsize_arith (a b : nat) :
  (0 < a)%N -> (0 < b)%N ->
  ((2 * a - 1) + (2 * b - 1) + 1 = 2 * (a + b) - 1)%N.
Proof.
case: a => // a' _; case: b => // b' _.
rewrite !mul2n -!addnn !addSn !addnS /= !subn1 /= addn0.
congr (_.+1.+1.+1); exact: addnACA.
Qed.

Lemma xunder_size (pos : seq bool) (t : bt unit) :
  size (xunder pos t) = (2 * bt_nleaves t - 1)%N.
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
rewrite !size_cat IHl IHr /= addnA.
by apply: xsize_arith; exact: bt_nleaves_pos.
Qed.

(** Every committed tweak is a leaf [panchor] or internal [tnode]. *)
Lemma xunder_mem (pos : seq bool) (x : adrs_sf_ch) (t : bt unit) :
  x \in xunder pos t ->
  (exists2 p, x = panchor (pos ++ p) & p \in leaf_paths t) \/
  (exists2 q, x = tnode (pos ++ q) & q \in internal_paths t).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos /=.
- rewrite mem_seq1 => /eqP ->; left; exists [::]; first by rewrite cats0.
  by rewrite mem_seq1.
- rewrite !mem_cat mem_seq1 => /orP[hl|/orP[hr|/eqP ->]].
  + case: (IHl (rcons pos false) hl) => [[p hp hpin]|[q hq hqin]].
    * left; exists (false :: p); first by rewrite hp cat_rcons.
      by rewrite /= mem_cat map_f.
    * right; exists (false :: q); first by rewrite hq cat_rcons.
      by rewrite /= inE mem_cat map_f ?orbT.
  + case: (IHr (rcons pos true) hr) => [[p hp hpin]|[q hq hqin]].
    * left; exists (true :: p); first by rewrite hp cat_rcons.
      by rewrite /= mem_cat map_f ?orbT.
    * right; exists (true :: q); first by rewrite hq cat_rcons.
      by rewrite /= inE mem_cat map_f ?orbT.
  + right; exists [::]; first by rewrite cats0.
    by rewrite /= inE eqxx.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Position-size facts (leaf + internal positions of a wf shape) *)

Lemma leaf_path_pos_ok sp (p : seq bool) :
  p \in leaf_paths (tshape sp) -> posok p.
Proof. exact: shrincs_fxmss_leaf_pos_ok. Qed.

Lemma leaf_path_size sp (p : seq bool) :
  p \in leaf_paths (tshape sp) -> (size p <= h_sf)%N.
Proof.
by move=> hp; exact: (shrincs_fxmss_pos_ok_size h_sf p (leaf_path_pos_ok sp p hp)).
Qed.

(** Internal-position facts (TreeHop's [internal_path_size], restated). *)
Lemma int_path_size sp (q : seq bool) :
  q \in internal_paths (tshape sp) -> (size q <= h_sf)%N.
Proof. exact: internal_path_size. Qed.

(* ------------------------------------------------------------------ *)
(** ** The decoding tag of a committed tweak

    A committed tweak is [tnode r] (an [shrincs_fxmss_adr_tree]) or [panchor r] (an
    [shrincs_fxmss_adr_pk]); its [(type, shrincs_fxmss_pos_id)] tag identifies it uniquely, and on a
    wf shape [shrincs_fxmss_pos_id] is injective on leaf+internal positions, so the
    tags over the committed set are distinct ([xtag_inj_in]). *)

Definition xtag (x : adrs_sf_ch) : nat * (nat * nat) :=
  (adrs_type (decode_tweak x), adrs_keypair (decode_tweak x)).

Lemma xtag_tnode (q : seq bool) :
  posok q -> xtag (tnode q) = (TY_TREE_SF, posid q).
Proof.
move=> hq.
rewrite /xtag /tnode_tw decode_tweakK /shrincs_fxmss_pos_id.
rewrite (shrincs_fxmss_tree_node_adrs_keypair l w _ _
  (shrincs_fxmss_pos_id_bounded h_sf q Hh hq)).
by [].
Qed.

Lemma xtag_panchor (p : seq bool) :
  posok p -> xtag (panchor p) = (TY_WOTS_PK_SF, posid p).
Proof.
move=> hp.
rewrite /xtag decode_tweakK.
rewrite (shrincs_fxmss_wots_pk_adrs_keypair l w _
  (shrincs_fxmss_pos_id_bounded h_sf p Hh hp)).
by [].
Qed.

(** [xtag] is injective on the committed tweaks of a wf shape: same tag
    forces same family (type) and same position ([shrincs_fxmss_pos_id] inj). *)
Lemma omega_xtag_panchor (p : seq bool) :
  posok p -> xtag (omega (panchor p)) = (TY_TREE_SF, posid p).
Proof. by move=> hp; rewrite omega_panchor (xtag_tnode p hp). Qed.

Lemma omega_xtag_tnode (q : seq bool) :
  posok q -> xtag (omega (tnode q)) = (TY_WOTS_PK_SF, posid q).
Proof. by move=> hq; rewrite omega_tnode (xtag_panchor q hq). Qed.

(* ------------------------------------------------------------------ *)
(** ** The combined tweak-tag list and its uniqueness

    [xtags pos t] is the list of tags of all committed tweaks AND their
    [omega]-partners over [t] at [pos] — i.e. the [(type, shrincs_fxmss_pos_id)] tags
    over [{TREE, PK} × (leaf+internal positions)].  We prove it [uniq]:
    leaf and internal positions are distinct paths, [shrincs_fxmss_pos_id] is
    injective on them (both have size <= h_sf), and the two types are
    distinct; therefore the committed tweak list [xunder] together with
    its [omega]-image is [uniq] ([xunder_omega_uniq]), which yields BOTH
    the tweak-freshness AND the partner-freshness of every XQUERY. *)

(** All positions of a sub-shape (leaves then internals), re-based at
    [pos]; the underlying path set of the committed tags. *)
Definition allpos (pos : seq bool) (t : bt unit) : seq (seq bool) :=
  [seq pos ++ r | r <- leaf_paths t ++ internal_paths t].

(** A leaf path and an internal path of the same tree never coincide
    (a position is a leaf XOR an internal node): the leaf has
    [subtree_at = Some (BLeaf _)] while the internal one has
    [Some (BNode _ _)]. *)
Lemma internal_subtree (t : bt unit) (r : seq bool) :
  r \in internal_paths t -> exists u v, subtree_at t r = Some (BNode u v).
Proof.
elim: r t => [|b r IH] [a|tl tr] /=.
- by rewrite in_nil.
- by move=> _; exists tl, tr.
- by rewrite in_nil.
- rewrite inE mem_cat => /orP[/eqP //|].
  move=> /orP[/mapP[r' hr' [eb er]]|/mapP[r' hr' [eb er]]]; subst.
  + exact: (IH tl hr').
  + exact: (IH tr hr').
Qed.

Lemma leaf_internal_disjoint (t : bt unit) (r : seq bool) :
  r \in leaf_paths t -> r \in internal_paths t -> False.
Proof.
move=> hl hi.
have hsl := @leaf_paths_subtree t r hl.
have [u [v hbn]] := internal_subtree t r hi.
by rewrite hbn in hsl.
Qed.

(** [leaf_paths t ++ internal_paths t] is duplicate-free. *)
Lemma all_paths_uniq (t : bt unit) :
  uniq (leaf_paths t ++ internal_paths t).
Proof.
rewrite cat_uniq leaf_paths_uniq internal_paths_uniq andbT /=.
apply/hasPn => r hr; apply/negP => hl.
exact: (leaf_internal_disjoint t r hl hr).
Qed.

(** [shrincs_fxmss_pos_id] is injective on all positions of a wf shape. *)
Lemma posid_inj_all sp (r r' : seq bool) :
  r \in leaf_paths (tshape sp) ++ internal_paths (tshape sp) ->
  r' \in leaf_paths (tshape sp) ++ internal_paths (tshape sp) ->
  posid r = posid r' -> r = r'.
Proof.
rewrite !mem_cat => hr hr' he.
have hs : (size r <= h_sf)%N.
  by case/orP: hr => h; [exact: (leaf_path_size sp) | exact: (int_path_size sp)].
have hs' : (size r' <= h_sf)%N.
  by case/orP: hr' => h; [exact: (leaf_path_size sp) | exact: (int_path_size sp)].
exact: (shrincs_fxmss_pos_id_inj h_sf r r' hs hs' he).
Qed.

(* ------------------------------------------------------------------ *)
(** ** [map xtag] of the committed tweaks (and their partners)

    The tags over a sub-shape are, up to permutation, the [(PK,
    shrincs_fxmss_pos_id)] tags of the leaves followed by the [(TREE, shrincs_fxmss_pos_id)] tags
    of the internal nodes; the partner tags swap the two types. *)

(** Re-base a tag-map over [b :: _]-prefixed paths to a [rcons pos b]
    prefix (the [cat_rcons] reindexing matching the recursion). *)
Lemma tagmap_consb (X : nat) (pos : seq bool) (b : bool) (f : seq (seq bool)) :
  [seq (X, posid (pos ++ r)) | r <- [seq b :: r0 | r0 <- f]]
  = [seq (X, posid (rcons pos b ++ r)) | r <- f].
Proof. by rewrite -map_comp; apply/eq_map => r /=; rewrite cat_rcons. Qed.

Lemma map_xtag_xunder (pos : seq bool) (t : bt unit) :
  subposok pos t ->
  perm_eq [seq xtag x | x <- xunder pos t]
    ([seq (TY_WOTS_PK_SF, posid (pos ++ p)) | p <- leaf_paths t]
     ++ [seq (TY_TREE_SF, posid (pos ++ q)) | q <- internal_paths t]).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos hsub.
- have hpos : posok pos := shrincs_fxmss_sub_pos_ok_here h_sf pos _ hsub.
  by rewrite /= cats0 (xtag_panchor pos hpos).
- have hpos : posok pos := shrincs_fxmss_sub_pos_ok_here h_sf pos _ hsub.
  have hleft := shrincs_fxmss_sub_pos_ok_child h_sf pos false tl tr hsub.
  have hright := shrincs_fxmss_sub_pos_ok_child h_sf pos true tl tr hsub.
  rewrite [xunder _ _]/= [leaf_paths (BNode _ _)]/= [internal_paths (BNode _ _)]/=.
  rewrite !map_cat /= (xtag_tnode pos hpos).
  rewrite [in [seq _ | _ <- [seq false :: _ | _ <- internal_paths tl] ++ _]]map_cat.
  rewrite !tagmap_consb cats0.
  set Ll := [seq xtag x | x <- xunder (rcons pos false) tl].
  set Lr := [seq xtag x | x <- xunder (rcons pos true) tr].
  set LA := [seq (TY_WOTS_PK_SF, posid (rcons pos false ++ p)) | p <- leaf_paths tl].
  set LB := [seq (TY_TREE_SF, posid (rcons pos false ++ q)) | q <- internal_paths tl].
  set RA := [seq (TY_WOTS_PK_SF, posid (rcons pos true ++ p)) | p <- leaf_paths tr].
  set RB := [seq (TY_TREE_SF, posid (rcons pos true ++ q)) | q <- internal_paths tr].
  (* peel the trailing node target to the front-of-tail position *)
  apply: (perm_trans (y := (Ll ++ Lr) ++ [:: (TY_TREE_SF, posid pos)])).
    by rewrite -catA perm_cat2l perm_cat2l.
  apply: (perm_trans (y := ((LA ++ LB) ++ (RA ++ RB)) ++
                           [:: (TY_TREE_SF, posid pos)])).
    rewrite perm_cat2r; apply: perm_cat; [exact: IHl hleft | exact: IHr hright].
  (* reorder [(LA++LB)++(RA++RB)++[node]] to [(LA++RA)++[node]++(LB++RB)] *)
  rewrite -!catA -cat1s.
  rewrite perm_cat2l (perm_catCA LB RA (RB ++ [:: (TY_TREE_SF, posid pos)])).
  rewrite perm_cat2l.
  by rewrite catA perm_catC catA.
Qed.

(** The partner tags: [map (xtag \o omega)] swaps the two types. *)
Lemma map_xtag_omega_xunder (pos : seq bool) (t : bt unit) :
  subposok pos t ->
  perm_eq [seq xtag (omega x) | x <- xunder pos t]
    ([seq (TY_TREE_SF, posid (pos ++ p)) | p <- leaf_paths t]
     ++ [seq (TY_WOTS_PK_SF, posid (pos ++ q)) | q <- internal_paths t]).
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos hsub.
- have hpos : posok pos := shrincs_fxmss_sub_pos_ok_here h_sf pos _ hsub.
  by rewrite /= cats0 (omega_xtag_panchor pos hpos).
- have hpos : posok pos := shrincs_fxmss_sub_pos_ok_here h_sf pos _ hsub.
  have hleft := shrincs_fxmss_sub_pos_ok_child h_sf pos false tl tr hsub.
  have hright := shrincs_fxmss_sub_pos_ok_child h_sf pos true tl tr hsub.
  rewrite [xunder _ _]/= [leaf_paths (BNode _ _)]/= [internal_paths (BNode _ _)]/=.
  rewrite !map_cat /= (omega_xtag_tnode pos hpos).
  rewrite [in [seq _ | _ <- [seq false :: _ | _ <- internal_paths tl] ++ _]]map_cat.
  rewrite !tagmap_consb cats0.
  set Ll := [seq xtag (omega x) | x <- xunder (rcons pos false) tl].
  set Lr := [seq xtag (omega x) | x <- xunder (rcons pos true) tr].
  set LA := [seq (TY_TREE_SF, posid (rcons pos false ++ p)) | p <- leaf_paths tl].
  set LB := [seq (TY_WOTS_PK_SF, posid (rcons pos false ++ q)) | q <- internal_paths tl].
  set RA := [seq (TY_TREE_SF, posid (rcons pos true ++ p)) | p <- leaf_paths tr].
  set RB := [seq (TY_WOTS_PK_SF, posid (rcons pos true ++ q)) | q <- internal_paths tr].
  apply: (perm_trans (y := (Ll ++ Lr) ++ [:: (TY_WOTS_PK_SF, posid pos)])).
    by rewrite -catA perm_cat2l perm_cat2l.
  apply: (perm_trans (y := ((LA ++ LB) ++ (RA ++ RB)) ++
                           [:: (TY_WOTS_PK_SF, posid pos)])).
    rewrite perm_cat2r; apply: perm_cat; [exact: IHl hleft | exact: IHr hright].
  rewrite -!catA -cat1s.
  rewrite perm_cat2l (perm_catCA LB RA (RB ++ [:: (TY_WOTS_PK_SF, posid pos)])).
  rewrite perm_cat2l.
  by rewrite catA perm_catC catA.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Master uniqueness: committed tweaks + partners are all distinct

    [uniq (xunder [::] (tshape sp) ++ map omega (xunder [::] (tshape sp)))]
    — both the tweaks AND their [omega]-partners are pairwise distinct,
    which feeds every XQUERY's tweak-freshness AND partner-freshness. *)

(** A typed-tag list over the (uniq) positions of a wf shape is [uniq]
    ([posid] injective on them). *)
Lemma typed_tag_uniq sp (X : nat) :
  uniq [seq (X, posid r) | r <- leaf_paths (tshape sp)
                                  ++ internal_paths (tshape sp)].
Proof.
rewrite map_inj_in_uniq; first exact: all_paths_uniq.
move=> r r' hr hr' he.
have hpe : posid r = posid r' := f_equal snd he.
exact: (posid_inj_all sp r r' hr hr' hpe).
Qed.

(** The canonical tag list of the committed tweaks (PK on leaves, TREE
    on internals) is [uniq]: the two type-blocks are disjoint, each
    block [uniq]. *)
Lemma canon_tags_uniq sp :
  uniq ([seq (TY_WOTS_PK_SF, posid p) | p <- leaf_paths (tshape sp)]
        ++ [seq (TY_TREE_SF, posid q) | q <- internal_paths (tshape sp)]).
Proof.
have hPK := typed_tag_uniq sp TY_WOTS_PK_SF.
move: hPK; rewrite map_cat cat_uniq => /and3P[hl _ _].
rewrite cat_uniq hl /=.
apply/andP; split.
- apply/hasPn => z /mapP[q _ ->].
  by apply/negP => /mapP[p _ []].
- rewrite map_inj_in_uniq; first exact: internal_paths_uniq.
  move=> r r' hr hr' he.
  have hpe : posid r = posid r' := f_equal snd he.
  apply: (posid_inj_all sp r r').
  + by rewrite mem_cat hr orbT.
  + by rewrite mem_cat hr' orbT.
  + exact: hpe.
Qed.

(** The same with the types swapped (the partners). *)
Lemma canon_tags_swap_uniq sp :
  uniq ([seq (TY_TREE_SF, posid p) | p <- leaf_paths (tshape sp)]
        ++ [seq (TY_WOTS_PK_SF, posid q) | q <- internal_paths (tshape sp)]).
Proof.
have hTR := typed_tag_uniq sp TY_TREE_SF.
move: hTR; rewrite map_cat cat_uniq => /and3P[hl _ _].
rewrite cat_uniq hl /=.
apply/andP; split.
- apply/hasPn => z /mapP[q _ ->].
  by apply/negP => /mapP[p _ []].
- rewrite map_inj_in_uniq; first exact: internal_paths_uniq.
  move=> r r' hr hr' he.
  have hpe : posid r = posid r' := f_equal snd he.
  apply: (posid_inj_all sp r r').
  + by rewrite mem_cat hr orbT.
  + by rewrite mem_cat hr' orbT.
  + exact: hpe.
Qed.

(** Cross-disjointness of the four tag families (PK-leaf, TREE-int,
    TREE-leaf, PK-int): no tag appears in both [canon_tags] and
    [canon_tags_swap].  This is the {leaf} vs {internal} position
    disjointness ([leaf_internal_disjoint]). *)
Lemma canon_tags_cross_disjoint sp z :
  z \in [seq (TY_WOTS_PK_SF, posid p) | p <- leaf_paths (tshape sp)]
        ++ [seq (TY_TREE_SF, posid q) | q <- internal_paths (tshape sp)] ->
  z \in [seq (TY_TREE_SF, posid p) | p <- leaf_paths (tshape sp)]
        ++ [seq (TY_WOTS_PK_SF, posid q) | q <- internal_paths (tshape sp)] ->
  False.
Proof.
rewrite !mem_cat.
move=> /orP[/mapP[p hp hzp]|/mapP[q hq hzq]] /orP[/mapP[p' hp' hzp']|/mapP[q' hq' hzq']].
- by rewrite hzp in hzp'.
- (* (PK, posid p) = (PK, posid q'): leaf p, internal q', posid p = posid q' *)
  have hpe : posid p = posid q' := f_equal snd (etrans (esym hzp) hzq').
  have he : p = q'.
    apply: (posid_inj_all sp p q').
    + by rewrite mem_cat hp.
    + by rewrite mem_cat hq' orbT.
    + exact: hpe.
  by apply: (leaf_internal_disjoint (tshape sp) p hp); rewrite he.
- (* (TREE, posid q) = (TREE, posid p'): internal q, leaf p' *)
  have hpe : posid q = posid p' := f_equal snd (etrans (esym hzq) hzp').
  have he : q = p'.
    apply: (posid_inj_all sp q p').
    + by rewrite mem_cat hq orbT.
    + by rewrite mem_cat hp'.
    + exact: hpe.
  by apply: (leaf_internal_disjoint (tshape sp) p' hp'); rewrite -he.
- by rewrite hzq in hzq'.
Qed.

(** The full tag list (tweaks then partners) is [uniq]. *)
Lemma full_tags_uniq sp :
  uniq (([seq (TY_WOTS_PK_SF, posid p) | p <- leaf_paths (tshape sp)]
         ++ [seq (TY_TREE_SF, posid q) | q <- internal_paths (tshape sp)])
        ++ ([seq (TY_TREE_SF, posid p) | p <- leaf_paths (tshape sp)]
            ++ [seq (TY_WOTS_PK_SF, posid q) | q <- internal_paths (tshape sp)])).
Proof.
rewrite cat_uniq canon_tags_uniq canon_tags_swap_uniq andbT /=.
apply/hasPn => z hz; apply/negP => hz'.
exact: (canon_tags_cross_disjoint sp z hz' hz).
Qed.

(** A committed tweak decodes to [shrincs_fxmss_adr_tree (posid r)] or [shrincs_fxmss_adr_pk (posid r)]
    and is recovered from its decode by [encode_adrsK]; so [xtag]
    determines the decode, hence the tweak. *)
Lemma decode_tnode (r : seq bool) :
  decode_tweak (tnode r) = shrincs_fxmss_adr_tree (posid r).1 (posid r).2.
Proof. by rewrite /tnode_tw decode_tweakK /shrincs_fxmss_pos_id. Qed.

Lemma decode_panchor (r : seq bool) :
  decode_tweak (panchor r) = @shrincs_fxmss_wots_pk_adrs l w (posid r).
Proof. by rewrite decode_tweakK /shrincs_fxmss_pos_id. Qed.

(** Recover a committed tweak from its decode (it is in [encode_adrs]'s
    canonical image, where [decode_tweak] cancels). *)
Lemma encode_decode_tnode (r : seq bool) :
  encode_adrs (decode_tweak (tnode r)) = tnode r.
Proof. by rewrite decode_tnode /tnode_tw /shrincs_fxmss_pos_id. Qed.

Lemma encode_decode_panchor (r : seq bool) :
  encode_adrs (decode_tweak (panchor r)) = panchor r.
Proof. by rewrite decode_panchor /shrincs_fxmss_pos_id. Qed.

Lemma xtag_inj_combined sp :
  {in (xunder [::] (tshape sp) ++ [seq omega x | x <- xunder [::] (tshape sp)]) &,
     injective xtag}.
Proof.
move=> x y; rewrite !mem_cat.
move=> hx hy hxy.
(* decode each as tnode/panchor of a wf-shape position *)
have decode (z : adrs_sf_ch) :
  ((z \in xunder [::] (tshape sp))
   || (z \in [seq omega x0 | x0 <- xunder [::] (tshape sp)]))%B ->
  exists2 r, ((z == tnode r) || (z == panchor r))%B
           & r \in leaf_paths (tshape sp) ++ internal_paths (tshape sp).
  move=> /orP[hz|/mapP[z0 hz0 ->]].
  - case: (xunder_mem [::] z (tshape sp) hz) => [[p hp hpin]|[q hq hqin]].
    + exists p; first by rewrite hp cat0s eqxx orbT.
      by rewrite mem_cat hpin.
    + exists q; first by rewrite hq cat0s eqxx.
      by rewrite mem_cat hqin orbT.
  - case: (xunder_mem [::] z0 (tshape sp) hz0) => [[p hp hpin]|[q hq hqin]].
    + exists p; first by rewrite hp cat0s omega_panchor eqxx.
      by rewrite mem_cat hpin.
    + exists q; first by rewrite hq cat0s omega_tnode eqxx orbT.
      by rewrite mem_cat hqin orbT.
have [rx hrx hrxmem] := decode x hx.
have [ry hry hrymem] := decode y hy.
have hsx : posok rx := shrincs_fxmss_shape_pos_ok h_sf sp rx hrxmem.
have hsy : posok ry := shrincs_fxmss_shape_pos_ok h_sf sp ry hrymem.
(* [xtag = (adrs_type, adrs_keypair)]; on a committed tweak it is the
   constructor (type) + the position [posid r].  Equal [xtag] thus
   forces SAME family (TREE != PK) and SAME [posid], pinning the tweak
   ([tnode]/[panchor] are injective in [posid]). *)
move: hxy.
case/orP: hrx => /eqP ->; case/orP: hry => /eqP ->.
- rewrite (xtag_tnode rx hsx) (xtag_tnode ry hsy) => htag.
  have hpos := congr1 snd htag.
  by rewrite (posid_inj_all sp rx ry hrxmem hrymem hpos).
- by rewrite (xtag_tnode rx hsx) (xtag_panchor ry hsy).
- by rewrite (xtag_panchor rx hsx) (xtag_tnode ry hsy).
- rewrite (xtag_panchor rx hsx) (xtag_panchor ry hsy) => htag.
  have hpos := congr1 snd htag.
  by rewrite (posid_inj_all sp rx ry hrxmem hrymem hpos).
Qed.

Lemma xunder_omega_uniq sp :
  uniq (xunder [::] (tshape sp)
        ++ [seq omega x | x <- xunder [::] (tshape sp)]).
Proof.
rewrite -(map_inj_in_uniq (xtag_inj_combined sp)).
rewrite map_cat -map_comp.
have hperm :
  perm_eq ([seq xtag x | x <- xunder [::] (tshape sp)]
           ++ [seq (xtag \o omega) x | x <- xunder [::] (tshape sp)])
    (([seq (TY_WOTS_PK_SF, posid p) | p <- leaf_paths (tshape sp)]
      ++ [seq (TY_TREE_SF, posid q) | q <- internal_paths (tshape sp)])
     ++ ([seq (TY_TREE_SF, posid p) | p <- leaf_paths (tshape sp)]
         ++ [seq (TY_WOTS_PK_SF, posid q) | q <- internal_paths (tshape sp)])).
  apply: perm_cat.
	  - apply: (map_xtag_xunder [::] (tshape sp)).
	    exact: shrincs_fxmss_sub_pos_ok_root.
	  - apply: (map_xtag_omega_xunder [::] (tshape sp)).
	    exact: shrincs_fxmss_sub_pos_ok_root.
by rewrite (perm_uniq hperm) full_tags_uniq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** LateGames locations / bodies (TreeHopProof's shorthands) *)

Local Notation IG := (I_G0fL PP N D M R).
Local Notation FXSIG := (shrincs_fxmss_game_signature N R).
Local Notation FXST := (shrincs_fxmss_game_state PP N).
Local Notation ROIN := (shrincs_fxmss_random_oracle_input PP N M R).

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
Local Notation fillc := (fill_code D dD).
Local Notation sdgrind := (sd_grindable PP D Hgrind S_wn c_max h_sf).
Local Notation skeys := (@sample_keys l N dN).
Local Notation keepC := (keepColl N).
Local Notation keepNone := (keepNone N).
Local Notation fverdN :=
  (fverd PP N D M R F Tl Hgrind Htree S_wn h_sf).
Local Notation forge_keep :=
  (forge_keep_body PP N D M R F Tl Hgrind Htree dD S_wn h_sf q_f).

(** Keep the M5 leaf-id selectors folded under [simpl] so the SIGN-bullet
    [case:] scrutinees ([leaf_okP …], [lidx …]) match the goal verbatim. *)
Arguments leaf_okP : simpl never.
Arguments lidx : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The committed-target index of a forged structure case

    Targets are committed via XQUERY in [xunder [::] (tshape sp)] order;
    the XCHECK index of a node identifier is its position in that list.
    For a FEscape the honest target is the ANCHOR (committed at [panchor
    q]); for a FShort it is the internal NODE (committed at [tnode q]). *)

Definition xindex (sp : seq bool) (z : adrs_sf_ch) : nat :=
  index z (xunder [::] (tshape sp)).

(** The verifier's completed-ends list of a forged signature: the
    [complete_ends] argument of [shrincs_fxmss_recover_anchor], so [Tl pp (shrincs_fxmss_adr_pk zi)
    (fcomplete zi pp md ws) = shrincs_fxmss_recover_anchor pp zi md ws]. *)
Definition fcomplete (zi : nat * nat) (pp : PP) (md : D) (ws : seq N * nat) :
    seq N :=
  complete_ends PP N F zi.1 zi.2 pp
    (digest_of PP D Hgrind zi.1 zi.2 pp md ws.2) ws.1.

Lemma recover_fcomplete (zi : nat * nat) (pp : PP) (md : D) (ws : seq N * nat) :
  frecover pp zi md ws = Tl pp (shrincs_fxmss_wots_pk_adrs zi) (fcomplete zi pp md ws).
Proof. by rewrite /shrincs_fxmss_recover_anchor /fcomplete /shrincs_fxmss_wots_pk_adrs; case: zi. Qed.

(* ------------------------------------------------------------------ *)
(** ** The reduction package [R_x]

    Same locations as LateGames (shrincs_fxmss_*_loc), so SIGN/HASH are
    identical to [sign5_body]/[hash5_body]. GEN routes the pp-dependent
    computation through the TCRX oracles (XCOLLQ chains + grinding,
    XQUERY targets at both families, XGETPP); FORGE classifies and on
    FEscape/FShort submits XCHECK at the PARTNER tweak. *)

(** GEN: pin pp via one XCOLLQ (Hgrind member on a dummy, answer
    discarded); sample dead [dN]/[dR] and the keys/digests as G7f does;
    assert grindability through XCOLLQ; build the root bottom-up through
    XQUERY/XCOLLQ; XGETPP; store and return (pp, root). *)
Definition gen_redx (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get Lst ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   _ ← opr x_cqo (encode_adrs (gadrs (0, 0)), inl n0) (λ r, ret r) ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← skeys (size (leaf_paths (tshape sp))) ;;
   sd ← fillc (iota 0 n_max) emptym ;;
   gok ← x_gcheck sp sd (iota 0 (size (leaf_paths (tshape sp)))) ;;
   #assert gok ;;
   root ← x_tree sp xss [::] (tshape sp) ;;
   pp ← opr x_gpo Datatypes.tt (λ p, ret p) ;;
   #put Lst := Some ((pp, root), (sp, xss)) ;;
   #put Lsd := sd ;;
   ret (pp, root)).

(** FORGE: G7f's body up to the verdict, then classify; on FEscape
    submit XCHECK at the partner [shrincs_fxmss_adr_tree] tweak with the forged
    children; on FShort at the partner [shrincs_fxmss_adr_pk] tweak with the verifier's
    completed ends; else answer as G7f ([keepC]). *)
Definition forge_redx (b : bool) (m : M) (sg : FXSIG) : raw_code 'bool :=
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
     | FEscape q x _ =>
         ans ← opr x_cko ((xindex st.2.1 (panchor q), tnode q), inl x)
                 (λ a, ret a) ;;
         ret (P && ans)
     | FShort q _ =>
         ans ← opr x_cko ((xindex st.2.1 (tnode q), panchor q),
                          inr (fcomplete sg.1.1 st.1.1 md sg.2.1))
                 (λ a, ret a) ;;
         ret (P && ans)
     | fc' => ret (P && keepC fc')
     end
   else ret false).

#[export] Instance gen_redx_valid (sp : 'list 'bool) :
  ValidCode LateLocs0 I_X (gen_redx sp).
Proof.
rewrite /gen_redx.
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
eapply valid_bind; first exact: x_gcheck_valid. move=> gok.
eapply valid_assertD => _.
eapply valid_bind; first exact: x_tree_valid. move=> root.
eapply valid_bind.
  eapply valid_opr; first by fmap_solve. move=> p; apply valid_ret.
move=> pp.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

#[export] Instance forge_redx_valid (b : bool) (m : M) (sg : FXSIG) :
  ValidCode LateLocs0 I_X (forge_redx b m sg).
Proof.
rewrite /forge_redx.
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
- apply valid_ret.
- eapply valid_bind.
    eapply valid_opr; first by fmap_solve. move=> r0; apply valid_ret.
  move=> ans; apply valid_ret.
- eapply valid_bind.
    eapply valid_opr; first by fmap_solve. move=> r0; apply valid_ret.
  move=> ans; apply valid_ret.
- apply valid_ret.
Qed.

(** Parameterized by the FORGE guard [b] (the outer game's FORGE bit):
    at [b = false] FORGE returns [false] (XCHECK never invoked); at
    [b = true] it classifies and submits XCHECK. *)
(** DIRECTED package validity (M5): the lifted SIGN body makes the
    default [package] typeclass elaboration a >30-min wall, so we
    [notypeclasses refine] the raw package and discharge the
    [ValidPackage] obligation by hand — [valid_package_cons] peeled
    FORGE→HASH→SIGN→GEN over the four hand-proved [ValidCode]
    instances, exactly as [late_games.Gkeep]. *)
Definition R_x (b : bool) : package I_X IG.
Proof.
notypeclasses refine [package LateLocs0 ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen_redx sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option FXSIG } (m) {
      sign5 m
    } ;
    [ FXHASH ] : { ROIN ~> D } (x) {
      hash5 x
    } ;
    [ FXFORGE ] : { M × FXSIG ~> 'bool } '(m, sg) {
      forge_redx b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: forge_redx_valid. } }
    { intros x; exact: hash5_body_valid. } }
  { intros m; exact: sign5_body_valid. } }
{ intros sp; exact: gen_redx_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** Linked TCRX oracle bodies (resolve equations, computed once) *)

Local Notation xpp := (tcrx_pp_loc Txc).
Local Notation xtgts := (tcrx_tgts_loc Txc).
Local Notation xtws := (tcrx_tws_loc Txc).
Local Notation xrev := tcrx_rev_loc.

Lemma resolve_xcq (b : bool) (t : tc_T Cxc) (x : tc_M Cxc) :
  resolve (TCRX b) x_cqo (t, x) =
  (ppo ← get xpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put xpp := Some pp ;; ret pp
        end ;;
   ret (tc_eval Cxc pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_xq (b : bool) (t : th_T Txc) (x : th_M Txc) :
  resolve (TCRX b) x_xqo (t, x) =
  (revealed ← get xrev ;;
   #assert ~~ revealed ;;
   tws ← get xtws ;;
   #assert (size tws < 2 * n_max - 1)%N ;;
   #assert (t \notin tws) ;;
   #assert (~~ (paired t && (omega t \in tws))) ;;
   tgts ← get xtgts ;;
   #put xtgts := setm tgts (size tws) (t, x) ;;
   #put xtws := rcons tws t ;;
   ppo ← get xpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put xpp := Some pp ;; ret pp
        end ;;
   ret (th_eval Txc pp t x)).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_xgp (b : bool) (u : unit) :
  resolve (TCRX b) x_gpo u =
  (ppo ← get xpp ;;
   pp ← match ppo with
        | Some pp => ret pp
        | None => pp ← dPP ;; #put xpp := Some pp ;; ret pp
        end ;;
   #put xrev := true ;;
   ret pp).
Proof. by case: b; simplify_linking. Qed.

Lemma resolve_xck (j : nat) (t : th_T Txc) (x : th_M Txc) :
  resolve (TCRX true) x_cko ((j, t), x) =
  (revealed ← get xrev ;;
   #assert revealed ;;
   tgts ← get xtgts ;;
   match getm tgts j with
   | Some (t0, m0) =>
       ppo ← get xpp ;;
       pp ← match ppo with
            | Some pp => ret pp
            | None => pp ← dPP ;; #put xpp := Some pp ;; ret pp
            end ;;
       ret (((t == t0) || (paired t0 && (t == omega t0)))
            && (x != m0)
            && (th_eval Txc pp t0 m0 == th_eval Txc pp t x))
   | None => ret false
   end).
Proof. simplify_linking. reflexivity. Qed.

Lemma resolve_xck_false (j : nat) (t : th_T Txc) (x : th_M Txc) :
  resolve (TCRX false) x_cko ((j, t), x) = ret false.
Proof. simplify_linking. reflexivity. Qed.

(* Keep packages / oracle bodies / pure layer folded under [simpl]. *)
#[local] Arguments resolve : simpl never.
#[local] Arguments TCRX_game : simpl never.
#[local] Arguments th_eval : simpl never.
#[local] Arguments tc_eval : simpl never.
#[local] Arguments decode_tweak : simpl never.
#[local] Arguments shrincs_fxmss_forgery_case : simpl never.
#[local] Arguments shrincs_fxmss_verify_md : simpl never.

(* ------------------------------------------------------------------ *)
(** ** The GEN block precondition (TreeHopProof's [trblk]) *)

Definition IGN : Locations :=
  [fmap (tcrx_pp_loc Txc) ; (tcrx_tgts_loc Txc) ; (tcrx_tws_loc Txc)
      ; tcrx_rev_loc ].

Definition xblk (po : option PP) (rv : bool)
    (tw : seq (th_T Txc)) (tg : {fmap nat -> (th_T Txc × th_M Txc)}) :
    precond :=
  λ '(s0, s1),
  [/\ heap_ignore IGN (s0, s1),
      get_heap s1 xpp = po,
      get_heap s1 xrev = rv,
      get_heap s1 xtws = tw &
      get_heap s1 xtgts = tg].

Arguments xblk : simpl never.

Lemma xblk_set_pp (pp : PP) rv tw tg s0 s1 :
  xblk None rv tw tg (s0, s1) ->
  xblk (Some pp) rv tw tg (s0, set_heap s1 xpp (Some pp)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

Lemma xblk_qupd (pp : PP) (t : th_T Txc) (xy : th_M Txc) tw tg s0 s1 :
  xblk (Some pp) false tw tg (s0, s1) ->
  xblk (Some pp) false (rcons tw t) (setm tg (size tw) (t, xy))
    (s0, set_heap (set_heap s1 xtgts (setm tg (size tw) (t, xy)))
           xtws (rcons tw t)).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- apply: heap_ignore_set_r; first by rewrite mem_domm.
  by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite !get_set_heap_neq.
- by rewrite !get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq // get_set_heap_eq.
Qed.

Lemma xblk_set_rev (po : option PP) tw tg s0 s1 :
  xblk po false tw tg (s0, s1) ->
  xblk po true tw tg (s0, set_heap s1 xrev true).
Proof.
move=> [h0 h1 h2 h3 h4]; split.
- by apply: heap_ignore_set_r h0; rewrite mem_domm.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_eq.
- by rewrite get_set_heap_neq.
- by rewrite get_set_heap_neq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping the linked oracles under a pinned pp *)

Lemma code_link_ret_bind {A B : choiceType} (a : A) (p : raw_package)
    (k : A -> raw_code B) :
  bind (code_link (ret a) p) k = k a.
Proof. by []. Qed.

Lemma bind_ret_l {A B : choiceType} (a : A) (k : A -> raw_code B) :
  bind (ret a) k = k a.
Proof. by []. Qed.

Lemma code_link_opr_bind {A B : choiceType} (o : opsig) (m : src o)
    (kk : tgt o -> raw_code A) (p : raw_package) (k1 : A -> raw_code B) :
  bind (code_link (opr o m kk) p) k1
  = bind (resolve p o m) (λ r, bind (code_link (kk r) p) k1).
Proof. by rewrite /= bind_assoc. Qed.

(** XCOLLQ at pinned pp: SMTCR-style, the SM-TCR state is untouched. *)
Lemma r_xcollq_known (b : bool) {B : choiceType} (pp : PP)
    (t : tc_T Cxc) (x : tc_M Cxc) rv tw tg
    (c0 : raw_code B) (k1 : tc_N Cxc -> raw_code B) (post : postcond B B) :
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (tc_eval Cxc pp t x) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (resolve (TCRX b) x_cqo (t, x)) k1 ⦃ post ⦄.
Proof.
move=> h.
rewrite (resolve_xcq b t x).
eapply (r_get_bind_rhs xpp (Some pp)).
  { by move=> s0 s1 [_ h' _ _ _]. }
cbv beta iota.
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Pure values of the XCOLLQ-routed leaf loops *)

Lemma collq_xF_E' pp (zi : nat * nat) (i k : nat) (x : N) :
  (if tc_eval Cxc pp (encode_adrs (cadrs zi i k)) (inl x) is inl y then y else x)
  = F pp (cadrs zi i k) x.
Proof. exact: collq_xF_E. Qed.

Lemma collq_xH_E' pp (zi : nat * nat) (d : D) (c : nat) :
  (if tc_eval Cxc pp (encode_adrs (gadrs zi)) (inr (d, c)) is inr h then h else 0%N)
  = Hgrind pp (gadrs zi) (d, c).
Proof. exact: collq_xH_E. Qed.

(** Walk loop value. *)
Lemma r_xwalk_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (i n k : nat) (x : N) rv tw tg
         (c0 : raw_code B) (k1 : N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (chain (fun pos y => F pp (cadrs zi i pos) y) x k n) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (x_walk zi i k n x) (TCRX b)) k1 ⦃ post ⦄.
Proof.
move=> zi i n.
elim: n => [|n IH] k x rv tw tg c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_xcollq_known b).
  rewrite collq_xF_E'.
  apply: IH.
  by rewrite chainS in h.
Qed.

Lemma r_xcends_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (i : nat) (xs : seq N) rv tw tg
         (c0 : raw_code B) (k1 : chList N -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (fcends pp zi i xs) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (x_cends zi i xs) (TCRX b)) k1 ⦃ post ⦄.
Proof.
move=> zi i xs; elim: xs i => [|x xs IH] i rv tw tg c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_xwalk_spec b pp post zi i w.-1 0 x).
  rewrite code_link_bind bind_assoc.
  apply: (IH i.+1).
  by rewrite code_link_ret_bind.
Qed.

Lemma r_xgrind_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (zi : nat * nat) (d : D) (cs : seq nat) rv tw tg
         (c0 : raw_code B) (k1 : chList 'nat -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 [seq Hgrind pp (gadrs zi) (d, c) | c <- cs] ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (x_grind zi d cs) (TCRX b)) k1 ⦃ post ⦄.
Proof.
move=> zi d cs; elim: cs => [|c cs IH] rv tw tg c0 k1 h /=.
- exact: h.
- rewrite bind_assoc.
  eapply (r_xcollq_known b).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite collq_xH_E' /= in h *.
Qed.

Local Notation gprp := (@grind_prp w l S_wn).
Local Notation ffind_ctr zi :=
  (find_ctr PP D Hgrind S_wn c_max zi.1 zi.2).
Local Notation fgood_ctr zi :=
  (good_ctr PP D Hgrind S_wn zi.1 zi.2).

Lemma has_grind_find_ctr pp (zi : nat * nat) (d : D) :
  has gprp [seq Hgrind pp (gadrs zi) (d, c) | c <- iota 0 c_max]
  = isSome (ffind_ctr zi pp d).
Proof.
rewrite has_map !find_ctr_def.
rewrite (eq_has (a2 := fgood_ctr zi pp d)); last first.
  by move=> c /=; rewrite !good_ctr_def !digest_of_def /grind_adrs; case: zi.
rewrite has_count -size_filter.
by case: [seq c <- iota 0 c_max | fgood_ctr zi pp d c].
Qed.

Lemma r_xslot_grind_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (j : nat) rv tw tg
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (match getm sd j with
              | Some d => slot_grindable PP D Hgrind S_wn c_max
                            h_sf pp sp j d
              | None => true
              end) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (x_slot_grind sp sd j) (TCRX b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd j rv tw tg c0 k1 h.
rewrite /x_slot_grind.
case E: (getm sd j) => [d|]; rewrite E /= in h.
- rewrite code_link_bind bind_assoc.
  eapply (r_xgrind_spec b pp post (posid (spath sp j)) d (iota 0 c_max)).
  rewrite code_link_ret_bind has_grind_find_ctr.
  rewrite -/(slot_grindable PP D Hgrind S_wn c_max h_sf pp sp j d).
  exact: h.
- by rewrite code_link_ret_bind; exact: h.
Qed.

Lemma r_xgcheck_spec (b : bool) {B : choiceType} (pp : PP)
    (post : postcond B B) :
  forall (sp : seq bool) (sd : chMap 'nat D) (js : seq nat) rv tw tg
         (c0 : raw_code B) (k1 : 'bool -> raw_code B),
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ k1 (all (fun j => match getm sd j with
                | Some d => slot_grindable PP D Hgrind S_wn c_max
                              h_sf pp sp j d
                | None => true
                end) js) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblk (Some pp) rv tw tg (s0, s1) ⦄
     c0 ≈ bind (code_link (x_gcheck sp sd js) (TCRX b)) k1 ⦃ post ⦄.
Proof.
move=> sp sd js; elim: js => [|j js IH] rv tw tg c0 k1 h /=.
- exact: h.
- rewrite code_link_bind bind_assoc.
  eapply (r_xslot_grind_spec b pp post sp sd j).
  rewrite code_link_bind bind_assoc.
  apply: IH.
  by rewrite code_link_ret_bind.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Stepping one linked XQUERY (commit a target)

    The committed-queue form of [xblk]: [tw = unzip1 Q], [tg =
    qmap_from 0 Q].  An XQUERY at tweak [t], message [xy] grows the queue
    by [(t, xy)]; the freshness side conditions ([t ∉ tws] AND
    [omega t ∉ tws]) come from [xunder_omega_uniq]. *)

Local Notation xblkQ po rv Q :=
  (xblk po rv (unzip1 Q) (qmap_from 0 Q)).

Lemma xblkQ_upd (pp : PP) (Q : seq (th_T Txc * th_M Txc)) (t : th_T Txc)
    (xy : th_M Txc) s0 s1 :
  xblkQ (Some pp) false Q (s0, s1) ->
  xblkQ (Some pp) false (rcons Q (t, xy)) (s0,
     set_heap (set_heap s1 xtgts (setm (qmap_from 0 Q) (size (unzip1 Q)) (t, xy)))
       xtws (rcons (unzip1 Q) t)).
Proof.
move=> hpre.
have hsz : size (unzip1 Q) = size Q by rewrite /unzip1 size_map.
rewrite /unzip1 map_rcons -/(unzip1 Q) qmap_from_rcons add0n -hsz.
exact: (xblk_qupd pp t xy (unzip1 Q) (qmap_from 0 Q) s0 s1 hpre).
Qed.

Lemma r_xquery_known (b : bool) {B : choiceType} (pp : PP)
    (t : th_T Txc) (xy : th_M Txc) (Q : seq (th_T Txc * th_M Txc))
    (c0 : raw_code B) (k1 : N -> raw_code B) (post : postcond B B) :
  (size Q < 2 * n_max - 1)%N ->
  t \notin unzip1 Q ->
  (~~ (paired t && (omega t \in unzip1 Q))) ->
  ⊢ ⦃ λ '(s0, s1), xblkQ (Some pp) false (rcons Q (t, xy)) (s0, s1) ⦄
     c0 ≈ k1 (th_eval Txc pp t xy) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblkQ (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (resolve (TCRX b) x_xqo (t, xy)) k1 ⦃ post ⦄.
Proof.
move=> hbud hfresh hpart h.
rewrite (resolve_xq b t xy).
eapply (r_get_bind_rhs xrev false).
  by move=> s0 s1 [_ _ h' _ _].
cbv beta.
eapply r_bind_assertD_rhs; first by [].
move=> _.
eapply (r_get_bind_rhs xtws (unzip1 Q)).
  by move=> s0 s1 [_ _ _ h' _].
cbv beta.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; rewrite size_map.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hfresh.
move=> _.
eapply r_bind_assertD_rhs.
  by move=> s0 s1 _; exact: hpart.
move=> _.
eapply (r_get_bind_rhs xtgts (qmap_from 0 Q)).
  by move=> s0 s1 [_ _ _ _ h'].
cbv beta.
eapply r_put2_bind_rhs.
  by move=> s0 s1 hpre; exact: (xblkQ_upd pp Q t xy s0 s1 hpre).
eapply (r_get_bind_rhs xpp (Some pp)).
  by move=> s0 s1 [_ h' _ _ _].
exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The committed (tweak, message) queue of the tree commit

    A leaf at [pos] commits [(panchor pos, inr (anchor_ends pos))]; an
    internal node [(tnode pos, inl (children values))].  [unzip1
    (xtree_commits ...) = xunder ...]. *)

Fixpoint xtree_commits (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos : seq bool) (t : bt unit) : seq (th_T Txc * th_M Txc) :=
  match t with
  | BLeaf _ =>
      [:: (panchor pos, inr (anchor_ends pp sp xss pos) : th_M Txc)]
  | BNode tl tr =>
      xtree_commits pp sp xss (rcons pos false) tl
      ++ xtree_commits pp sp xss (rcons pos true) tr
      ++ [:: (tnode pos, inl (tval pp sp xss (rcons pos false) tl,
                              tval pp sp xss (rcons pos true) tr) : th_M Txc)]
  end.

Lemma unzip1_cat (s t : seq (th_T Txc * th_M Txc)) :
  unzip1 (s ++ t) = unzip1 s ++ unzip1 t.
Proof. by rewrite /unzip1 map_cat. Qed.

Lemma unzip1_xtree_commits pp sp xss pos t :
  unzip1 (xtree_commits pp sp xss pos t) = xunder pos t.
Proof.
elim: t pos => [[]|tl IHl tr IHr] pos //=.
by rewrite !unzip1_cat IHl IHr.
Qed.

Lemma size_xtree_commits pp sp xss pos t :
  size (xtree_commits pp sp xss pos t) = size (xunder pos t).
Proof. by rewrite -(unzip1_xtree_commits pp sp xss pos t) /unzip1 size_map. Qed.

(* ------------------------------------------------------------------ *)
(** ** The doubled-uniqueness invariant of the tree commit

    [xdbl L := uniq (L ++ map omega L)] — the committed tweaks AND their
    [omega]-partners are all distinct.  It is monotone under reordering
    (perm-stable) and a head-commit of [t0] with the rest in [L'] yields
    BOTH freshness facts [t0 ∉ L'] and [omega t0 ∉ L'].  Established at
    the root by [xunder_omega_uniq]. *)

Definition xdbl (L : seq (th_T Txc)) : bool := uniq (L ++ [seq omega x | x <- L]).

Lemma xdbl_perm (L L' : seq (th_T Txc)) : perm_eq L L' -> xdbl L = xdbl L'.
Proof.
move=> hp; rewrite /xdbl.
by rewrite (perm_uniq (perm_cat hp (perm_map omega hp))).
Qed.

(** A head-commit [xdbl (t0 :: L')] gives BOTH freshness facts: [t0 ∉
    L'] (the first block is uniq) and [omega t0 ∉ L'] (the [omega t0] of
    the partner block is disjoint from the first block, which contains
    [L']). *)
Lemma xdbl_head (t0 : th_T Txc) (L' : seq (th_T Txc)) :
  xdbl (t0 :: L') -> (t0 \notin L') && (omega t0 \notin L').
Proof.
rewrite /xdbl map_cons cat_cons cons_uniq cat_uniq.
move=> /andP[ht0 /and3P[_ hdis _]].
apply/andP; split.
- by move: ht0; rewrite mem_cat negb_or => /andP[].
- apply/negP => homg.
  move/negP: hdis; apply; apply/hasP.
  by exists (omega t0); rewrite // inE eqxx.
Qed.

(** Rotate a head element to between the second and third blocks: the
    [xdbl] of [t0 :: A ++ B ++ C] equals that of [A ++ B ++ t0 :: C].
    Proven at section-lemma level (concrete [seq (th_T Txc)], so the
    [perm_catCA] rewrites fire — they do not inside [r_xtree_spec]'s
    [set]-laden body). *)
Lemma xdbl_rot_head (t0 : th_T Txc) (A B C : seq (th_T Txc)) :
  xdbl (t0 :: (A ++ B ++ C)) = xdbl (A ++ B ++ t0 :: C).
Proof.
apply: xdbl_perm; rewrite -cat1s.
apply: (perm_trans (y := A ++ [:: t0] ++ B ++ C)).
  by rewrite perm_catCA.
rewrite perm_cat2l.
by rewrite perm_catCA.
Qed.

(** The node-commit freshness facts, from the flattened doubled-uniq
    [xdbl (A ++ B ++ [:: t0] ++ C)]: [t0 ∉ A ++ B ++ C] AND [omega t0 ∉
    A ++ B ++ C].  Proven at section level (concrete [seq (th_T Txc)])
    so the rotation/[xdbl_head] tactics behave; consumed term-level in
    [r_xtree_spec]. *)
Lemma node_fresh (t0 : th_T Txc) (A B C : seq (th_T Txc)) :
  xdbl (A ++ B ++ [:: t0] ++ C) ->
  (t0 \notin A ++ B ++ C) && (omega t0 \notin A ++ B ++ C).
Proof.
move=> hfull.
have hrot : xdbl (t0 :: (A ++ B ++ C)).
  by rewrite (xdbl_rot_head t0 A B C) -cat1s.
exact: (xdbl_head t0 (A ++ B ++ C) hrot).
Qed.

(** [xdbl] is hereditary under [subseq] (uniqueness of [L ++ map omega L]
    survives dropping elements). *)
Lemma xdbl_subseq (L1 L2 : seq (th_T Txc)) :
  subseq L1 L2 -> xdbl L2 -> xdbl L1.
Proof.
move=> hsub; rewrite /xdbl => hu.
have hsub2 : subseq (L1 ++ [seq omega x | x <- L1])
                    (L2 ++ [seq omega x | x <- L2]).
  by apply: cat_subseq => //; apply: map_subseq.
exact: subseq_uniq hsub2 hu.
Qed.

(** Reordering a committed list preserves [xdbl] (it is perm-stable). *)
Lemma xdbl_catCA (A B C : seq (th_T Txc)) :
  xdbl (A ++ B ++ C) = xdbl (B ++ A ++ C).
Proof. by apply: xdbl_perm; rewrite perm_catCA. Qed.

Lemma xdbl_catC (A B : seq (th_T Txc)) : xdbl (A ++ B) = xdbl (B ++ A).
Proof. by apply: xdbl_perm; rewrite perm_catC. Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf / node committed-value bridges

    The [th_eval] of the leaf anchor target is the value-tree leaf value
    ([anchor_val]); of the internal node target the node hash. *)

Lemma th_eval_leaf pp (sp : seq bool) (xss : seq (seq N)) (pos : seq bool) :
  size (nth [::] xss (index pos (leaf_paths (tshape sp)))) = l ->
  th_eval Txc pp (panchor pos) (inr (fcends pp (posid pos) 0
            (nth [::] xss (index pos (leaf_paths (tshape sp))))))
  = anchor_val pp sp xss pos.
Proof.
move=> hsz.
rewrite (fcends_chain_ends pp (posid pos) _ hsz).
rewrite /th_eval /= decode_tweakK.
rewrite -/(shrincs_fxmss_pos_id h_sf pos).
by rewrite anchor_pk.
Qed.

Lemma th_eval_node pp (pos : seq bool) (x y : N) :
  th_eval Txc pp (tnode pos) (inl (x, y)) = nhash pp pos x y.
Proof. exact: th_eval_xnode. Qed.

(* ------------------------------------------------------------------ *)
(** ** The bottom-up tree commit coupling (heart of GEN)

    [x_tree sp xss pos t] (linked) lands on [tval pp sp xss pos t],
    growing the committed queue by [xtree_commits] in [xunder] order.
    The two freshness conditions of every XQUERY come from [xdbl] (via
    [xdbl_head] after a [xdbl_perm] rotation). *)

Lemma r_xtree_spec (b : bool) {B : choiceType} (pp : PP)
    (sp : seq bool) (xss : seq (seq N)) (post : postcond B B)
    (hkeys : forall xs, xs \in xss -> size xs = l) :
  forall (pos : seq bool) (t : bt unit)
         (Q : seq (th_T Txc * th_M Txc))
         (c0 : raw_code B) (k1 : N -> raw_code B),
  (forall p, p \in leaf_paths t ->
     index (pos ++ p) (leaf_paths (tshape sp)) < size xss) ->
  xdbl (xunder pos t ++ unzip1 Q) ->
  (size Q + size (xunder pos t) <= 2 * n_max - 1)%N ->
  ⊢ ⦃ λ '(s0, s1),
        xblkQ (Some pp) false (Q ++ xtree_commits pp sp xss pos t) (s0, s1) ⦄
     c0 ≈ k1 (tval pp sp xss pos t) ⦃ post ⦄ ->
  ⊢ ⦃ λ '(s0, s1), xblkQ (Some pp) false Q (s0, s1) ⦄
     c0 ≈ bind (code_link (x_tree sp xss pos t) (TCRX b)) k1 ⦃ post ⦄.
Proof.
move=> pos t; move: pos.
elim: t => [u|tl IHl tr IHr] pos Q c0 k1 hidx hdbl hbud h /=.
- (* leaf: build ends via XCOLLQ, then XQUERY the anchor target *)
  rewrite code_link_bind bind_assoc.
  set keys := nth [::] xss (index pos (leaf_paths (tshape sp))).
  have hksz : size keys = l.
    apply: hkeys; apply: mem_nth.
    by have := hidx [::]; rewrite mem_seq1 eqxx => /(_ erefl); rewrite cats0.
  eapply (r_xcends_spec b pp post (posid pos) 0 keys).
  rewrite code_link_opr_bind.
  (* the anchor XQUERY: tweak [panchor pos], freshness from [xdbl] *)
  eapply (r_xquery_known b pp (panchor pos)
            (inr (fcends pp (posid pos) 0 keys) : th_M Txc) Q).
  + by move: hbud => /=; rewrite addn1.
  + have [h1 _] := andP (xdbl_head (panchor pos) (unzip1 Q) hdbl).
    by [].
  + have [_ h2] := andP (xdbl_head (panchor pos) (unzip1 Q) hdbl).
    by rewrite (negbTE h2) andbF.
  rewrite (th_eval_leaf pp sp xss pos hksz).
  move: h => /=; rewrite cats1 /anchor_ends -/keys.
  by rewrite (fcends_chain_ends pp (posid pos) keys hksz).
- (* node: recurse left, recurse right, XQUERY the node target *)
  rewrite code_link_bind bind_assoc.
  set Lt := xunder (rcons pos false) tl.
  set Rt := xunder (rcons pos true) tr.
  (* budget bookkeeping *)
  have hbud' : (size Q + size Lt + size Rt).+1 <= 2 * n_max - 1.
    move: hbud => /=; rewrite !size_cat /= => hb.
    apply: leq_trans hb.
    by rewrite !addnA addn1.
  (* the full doubled-uniq list, flattened *)
  have hfull : xdbl (Lt ++ Rt ++ [:: tnode pos] ++ unzip1 Q).
    by move: hdbl; rewrite /= -!catA.
  (* left subtree *)
  eapply (IHl (rcons pos false) Q).
  + move=> p hp; have := hidx (false :: p).
    rewrite -cat_rcons; apply.
    by rewrite /= mem_cat map_f.
  + (* [xdbl (Lt ++ unzip1 Q)] : subseq of [hfull] *)
    apply: (xdbl_subseq _ _ _ hfull).
    apply: cat_subseq; first exact: subseq_refl.
    rewrite catA; exact: suffix_subseq.
  + apply: leq_trans hbud'; apply: leqW; exact: leq_addr.
  rewrite code_link_bind bind_assoc.
  (* right subtree, queue grown by the left commits *)
  eapply (IHr (rcons pos true) (Q ++ xtree_commits pp sp xss (rcons pos false) tl)).
  + move=> p hp; have := hidx (true :: p).
    rewrite -cat_rcons; apply.
    by rewrite /= mem_cat map_f ?orbT.
  + (* [xdbl (Rt ++ unzip1 (Q ++ left_commits))]
       = [xdbl (Rt ++ unzip1 Q ++ Lt)] : perm of a subseq of [hfull] *)
    rewrite unzip1_cat unzip1_xtree_commits -/Lt -/Rt.
    have hperm : perm_eq (Rt ++ unzip1 Q ++ Lt) (Lt ++ Rt ++ unzip1 Q).
      by rewrite (catA Rt) perm_catC.
    rewrite (xdbl_perm _ _ hperm).
    apply: (xdbl_subseq _ _ _ hfull).
    apply: cat_subseq; first exact: subseq_refl.
    apply: cat_subseq; first exact: subseq_refl.
    exact: suffix_subseq.
  + rewrite size_cat size_xtree_commits -/Lt -/Rt.
    by apply: leq_trans hbud'; rewrite -addnA leqnSn.
  (* the node XQUERY at [pos]: expose the resolved oracle, then commit *)
  rewrite code_link_opr_bind.
  have hQrn : unzip1 ((Q ++ xtree_commits pp sp xss (rcons pos false) tl)
                        ++ xtree_commits pp sp xss (rcons pos true) tr)
              = unzip1 Q ++ Lt ++ Rt.
    by rewrite !unzip1_cat !unzip1_xtree_commits -/Lt -/Rt catA.
  (* freshness of [tnode pos] (and its partner) from [hfull] *)
  have [hfr hpr] := andP (node_fresh (tnode pos) Lt Rt (unzip1 Q) hfull).
  eapply (r_xquery_known b pp (tnode pos)
            (inl (tval pp sp xss (rcons pos false) tl,
                  tval pp sp xss (rcons pos true) tr) : th_M Txc)
            ((Q ++ xtree_commits pp sp xss (rcons pos false) tl)
               ++ xtree_commits pp sp xss (rcons pos true) tr)).
  + rewrite !size_cat !size_xtree_commits -/Lt -/Rt.
    exact: hbud'.
  + rewrite hQrn.
    move: hfr; rewrite !mem_cat !negb_or.
    by move=> /and3P[a1 a2 a3]; rewrite a1 a2 a3.
  + rewrite hQrn paired_tnode /= omega_tnode.
    move: hpr; rewrite omega_tnode !mem_cat !negb_or.
    by move=> /and3P[a1 a2 a3]; rewrite a1 a2 a3.
  rewrite th_eval_node bind_ret_l.
  have hq : rcons ((Q ++ xtree_commits pp sp xss (rcons pos false) tl)
                     ++ xtree_commits pp sp xss (rcons pos true) tr)
              (tnode pos, (inl (tval pp sp xss (rcons pos false) tl,
                                tval pp sp xss (rcons pos true) tr) : th_M Txc))
            = Q ++ xtree_commits pp sp xss pos (BNode tl tr).
    by rewrite /= -cats1 -!catA.
  by rewrite hq; exact: h.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The committed queue at the root and its index lookup

    [xcommitq pp sp xss] is the root commit [xtree_commits pp sp xss [::]
    (tshape sp)]; its first components are [xunder [::] (tshape sp)]. *)

Definition xcommitq (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
    seq (th_T Txc * th_M Txc) :=
  xtree_commits pp sp xss [::] (tshape sp).

Lemma unzip1_xcommitq (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
  unzip1 (xcommitq pp sp xss) = xunder [::] (tshape sp).
Proof. exact: unzip1_xtree_commits. Qed.

(** [qnth] through a map (TreeHop's local copy). *)
Lemma qnth_map {X Y : Type} (f : X -> Y) (s : seq X) (i : nat) :
  qnth [seq f x | x <- s] i = omap f (qnth s i).
Proof. by rewrite /qnth -map_drop; case: (drop i s). Qed.

(** In a queue with [uniq] first-components, an element is determined by
    its first component. *)
Lemma unzip1_uniq_pair (Q : seq (th_T Txc * th_M Txc)) (t : th_T Txc)
    (m1 m2 : th_M Txc) :
  uniq (unzip1 Q) -> (t, m1) \in Q -> (t, m2) \in Q -> m1 = m2.
Proof.
elim: Q => [|[t0 m0] Q IH] /=; first by rewrite in_nil.
rewrite inE => /andP[ht0 hu]; rewrite !inE.
move=> /orP[/eqP[e1 e1']|h1] /orP[/eqP[e2 e2']|h2].
- by rewrite e1' e2'.
- subst t0 m0; move/negP: ht0; case; apply/mapP; by exists (t, m2).
- subst t0 m0; move/negP: ht0; case; apply/mapP; by exists (t, m1).
- exact: IH.
Qed.

(** A committed pair [(t, msg)] with [t] at index [i] of a queue whose
    first-components are [uniq] is recovered from the [qmap_from 0]. *)
Lemma getm_qmap_pair (Q : seq (th_T Txc * th_M Txc)) (t : th_T Txc)
    (msg : th_M Txc) :
  uniq (unzip1 Q) -> (t, msg) \in Q ->
  getm (qmap_from 0 Q) (index t (unzip1 Q)) = Some (t, msg).
Proof.
move=> hu hmem.
have ht : t \in unzip1 Q by apply/mapP; exists (t, msg).
have hsz : size (unzip1 Q) = size Q by rewrite /unzip1 size_map.
have hi : index t (unzip1 Q) < size Q.
  by rewrite -hsz index_mem.
have := qmap_from_get 0 Q (index t (unzip1 Q)); rewrite add0n => ->.
rewrite /qnth (drop_nth (t, msg)) //=.
congr Some.
have h1 : (nth (t, msg) Q (index t (unzip1 Q))).1 = t.
  rewrite -(nth_map (t, msg) t fst); last by rewrite -hsz index_mem.
  by rewrite -/(unzip1 Q) nth_index.
have hin : nth (t, msg) Q (index t (unzip1 Q)) \in Q by apply: mem_nth.
case Enth: (nth (t, msg) Q (index t (unzip1 Q))) => [t' m'].
rewrite Enth /= in h1; subst t'.
rewrite Enth in hin.
by rewrite (unzip1_uniq_pair Q t m' msg hu hin hmem).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Membership of the forged-case targets in the committed queue

    A verifying FEscape at honest anchor [q] has its anchor target
    [(panchor q, inr (anchor_ends q))] in [xcommitq]; a FShort at honest
    internal [q] has its node target [(tnode q, inl (children))] there.
    Proven by induction over the shape subtree, mirroring TreeHop's
    [tree_commits_E]. *)

Lemma xanchor_mem (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos rq : seq bool) (t : bt unit) :
  subtree_at t rq = Some (BLeaf tt) ->
  (panchor (pos ++ rq), inr (anchor_ends pp sp xss (pos ++ rq)) : th_M Txc)
    \in xtree_commits pp sp xss pos t.
Proof.
elim: t pos rq => [[]|tl IHl tr IHr] pos rq.
- case: rq => [|b rq] //= _.
  by rewrite cats0 mem_seq1.
- case: rq => [|b rq] //=.
  rewrite !mem_cat.
  case: b => /= hsub.
  + have := IHr (rcons pos true) rq hsub.
    by rewrite cat_rcons => ->; rewrite orbT.
  + have := IHl (rcons pos false) rq hsub.
    by rewrite cat_rcons => ->.
Qed.

Lemma xnode_mem (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (pos rq : seq bool) (t tl tr : bt unit) :
  subtree_at t rq = Some (BNode tl tr) ->
  (tnode (pos ++ rq),
   inl (tval pp sp xss (rcons (pos ++ rq) false) tl,
        tval pp sp xss (rcons (pos ++ rq) true) tr) : th_M Txc)
    \in xtree_commits pp sp xss pos t.
Proof.
elim: t pos rq => [[]|tl0 IHl tr0 IHr] pos rq.
- by case: rq => [|b rq].
- case: rq => [|b rq] /=.
  + move=> [e1 e2]; subst tl0 tr0.
    by rewrite !mem_cat !cats0 mem_seq1 eqxx !orbT.
  + rewrite !mem_cat.
    case: b => /= hsub.
    * have := IHr (rcons pos true) rq hsub.
      by rewrite cat_rcons => ->; rewrite orbT.
    * have := IHl (rcons pos false) rq hsub.
      by rewrite cat_rcons => ->.
Qed.

(** The committed-queue index lookup for the two structure cases. *)
Lemma getm_xcommitq_anchor (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : seq bool) :
  uniq (xunder [::] (tshape sp)) ->
  subtree_at (tshape sp) q = Some (BLeaf tt) ->
  getm (qmap_from 0 (xcommitq pp sp xss)) (xindex sp (panchor q))
  = Some (panchor q, inr (anchor_ends pp sp xss q) : th_M Txc).
Proof.
move=> hu hsub.
have hmem := xanchor_mem pp sp xss [::] q (tshape sp) hsub.
rewrite cat0s in hmem.
rewrite /xindex -(unzip1_xcommitq pp sp xss).
apply: getm_qmap_pair => //.
by rewrite unzip1_xcommitq.
Qed.

Lemma getm_xcommitq_node (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : seq bool) (tl tr : bt unit) :
  uniq (xunder [::] (tshape sp)) ->
  subtree_at (tshape sp) q = Some (BNode tl tr) ->
  getm (qmap_from 0 (xcommitq pp sp xss)) (xindex sp (tnode q))
  = Some (tnode q,
          inl (tval pp sp xss (rcons q false) tl,
               tval pp sp xss (rcons q true) tr) : th_M Txc).
Proof.
move=> hu hsub.
have hmem := xnode_mem pp sp xss [::] q (tshape sp) tl tr hsub.
rewrite cat0s in hmem.
rewrite /xindex -(unzip1_xcommitq pp sp xss).
apply: getm_qmap_pair => //.
by rewrite unzip1_xcommitq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** GEN side conditions: the [r_xtree_spec] preconditions at the root

    The leaf-index bound, the doubled-uniqueness [xdbl] of the committed
    tweaks, and the budget [2*n_a - 1 <= 2*n_max - 1] all come from the
    pure layer ([xunder_omega_uniq], [xunder_size]). *)

Lemma gen_hidx (sp : seq bool) (xss : seq (seq N)) :
  size xss = size (leaf_paths (tshape sp)) ->
  forall p, p \in leaf_paths (tshape sp) ->
    index ([::] ++ p) (leaf_paths (tshape sp)) < size xss.
Proof. by move=> hsz p hp; rewrite cat0s hsz index_mem. Qed.

Lemma gen_xdbl (sp : seq bool) :
  xdbl (xunder [::] (tshape sp)
        ++ unzip1 ([::] : seq (th_T Txc * th_M Txc))).
Proof. by rewrite cats0 /xdbl; exact: xunder_omega_uniq. Qed.

Lemma gen_xuniq (sp : seq bool) : uniq (xunder [::] (tshape sp)).
Proof.
have := xunder_omega_uniq sp.
by rewrite cat_uniq => /and3P[hu _ _].
Qed.

Lemma gen_bud (sp : seq bool) :
  (size (leaf_paths (tshape sp)) <= n_max)%N ->
  (size ([::] : seq (th_T Txc * th_M Txc))
   + size (xunder [::] (tshape sp)) <= 2 * n_max - 1)%N.
Proof.
move=> hcap; rewrite /= add0n xunder_size.
have hle : (bt_nleaves (tshape sp) <= n_max)%N.
  by rewrite -size_leaf_paths.
apply: leq_sub2r.
by rewrite leq_mul2l hle orbT.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The invariant ([tr_inv] of TreeHopProof, for the 4 TCRX locs) *)

Definition IGN' : Locations :=
  [fmap xpp ; xtgts ; xtws ; xrev ].

Definition RXr (sto : option FXST)
    (po : option PP) (tg : {fmap nat -> (th_T Txc × th_M Txc)})
    (tw : seq (th_T Txc)) (rv : bool) : Prop :=
  match sto with
  | None => [/\ po = None, tg = emptym, tw = [::] & rv = false]
  | Some st =>
      [/\ po = Some st.1.1, rv = true,
          tg = qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2),
          tw = xunder [::] (tshape st.2.1)
        & st.1.2 = fxroot st.1.1 st.2.1 st.2.2]
  end.

Definition x_inv : precond :=
  heap_ignore IGN'
  ⋊ rel_app [:: (rhs, shrincs_fxmss_st_loc PP N) ; (rhs, xpp) ;
                (rhs, xtgts) ; (rhs, xtws) ; (rhs, xrev) ] RXr.

Arguments x_inv : simpl never.

Lemma x_invE s0 s1 :
  x_inv (s0, s1) ->
  heap_ignore IGN' (s0, s1) /\
  RXr (get_heap s1 (shrincs_fxmss_st_loc PP N)) (get_heap s1 xpp)
      (get_heap s1 xtgts) (get_heap s1 xtws) (get_heap s1 xrev).
Proof. by move=> [h1 h2]; split. Qed.

Lemma x_invI s0 s1 :
  heap_ignore IGN' (s0, s1) ->
  RXr (get_heap s1 (shrincs_fxmss_st_loc PP N)) (get_heap s1 xpp)
      (get_heap s1 xtgts) (get_heap s1 xtws) (get_heap s1 xrev) ->
  x_inv (s0, s1).
Proof. by move=> h1 h2; split. Qed.

(** [x_inv] forces the rhs SMTCR state to [None]'s shape (the GEN entry
    state) when [Lst] (rhs) is None. *)
Lemma xinv_init s0 s1 :
  x_inv (s0, s1) ->
  get_heap s1 (shrincs_fxmss_st_loc PP N) = None ->
  xblk None false [::] emptym (s0, s1).
Proof.
move=> /x_invE [hign hRXr] hst.
rewrite hst in hRXr; case: hRXr => hpo htg htw hrv.
by split.
Qed.

Lemma xblkQ_init s0 s1 :
  xblk None false [::] emptym (s0, s1) ->
  xblkQ None false ([::] : seq (th_T Txc * th_M Txc)) (s0, s1).
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Heap / precond plumbing (TreeHopProof's, for [IGN']) *)

Lemma heap_ignore_set_both (L : Locations) (l0 : Location) (v : l0) s0 s1 :
  heap_ignore L (s0, s1) ->
  heap_ignore L (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h l1 hni.
rewrite /get_heap /set_heap !setmE.
case: (_ == _)%B => //=.
exact: (h l1 hni).
Qed.

Lemma x_inv_get_pre (l0 : Location) :
  l0.1 \notin domm IGN' -> get_pre_cond l0 x_inv.
Proof. by move=> hl0 s0 s1 [hign _]; exact: hign. Qed.

Ltac x_get_pre :=
  apply: x_inv_get_pre; rewrite /IGN'; fmap_solve.

Lemma x_inv_set_fx (l0 : Location) (v : l0) s0 s1 :
  l0.1 != (shrincs_fxmss_st_loc PP N).1 ->
  l0.1 != xpp.1 ->
  l0.1 != xtgts.1 ->
  l0.1 != xtws.1 ->
  l0.1 != xrev.1 ->
  x_inv (s0, s1) ->
  x_inv (set_heap s0 l0 v, set_heap s1 l0 v).
Proof.
move=> h1 h2 h3 h4 h5 /x_invE [hign hRXr].
apply: x_invI; first by apply: heap_ignore_set_both.
rewrite !get_set_heap_neq //; by rewrite eq_sym.
Qed.

Ltac x_put_tr :=
  let s0 := fresh "s0" in let s1 := fresh "s1" in let hp := fresh "hp" in
  rewrite /put_pre_cond; move=> s0 s1 hp;
  refine (x_inv_set_fx _ _ _ _ _ _ _ _ _ hp); by [].

Ltac x_put_pre :=
  repeat (apply: put_pre_cond_conj; last (apply: put_pre_cond_rem; by []));
  x_put_tr.

(* ------------------------------------------------------------------ *)
(** ** Key sampler size coupling (TreeHopProof's) *)

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

(* ------------------------------------------------------------------ *)
(** ** Grindability sync ([x_gcheck] = [sdgrind]) loop

    Mirrors TreeHopProof's [r_slot_grind_spec]/[r_gcheck_spec], but
    those are already in this file ([r_xslot_grind_spec]/[r_xgcheck_spec]
    below the GEN block). *)

(* ------------------------------------------------------------------ *)
(** ** The FORGE verdict (the heart of the FORGE case)

    The REAL side: [forge_keep]'s [fverd keepColl] equals [forge_redx]'s
    classify-and-XCHECK; FEscape/FShort XCHECKs WIN by [shrincs_fxmss_forgery_case_FEscape]/
    [shrincs_fxmss_forgery_case_FShort] (the partner branch of [resolve_xck]); FColl/FAnchor
    nulled by [keepColl] on both sides. *)
Lemma r_forge_verdict (st : FXST) (lg : seq M)
    (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  ⊢ ⦃ λ '(s0, s1),
        (x_inv ⋊ rem_lhs Lst (Some st) ⋊ rem_rhs Lst (Some st)) (s0, s1) ⦄
     ret (fverdN keepC st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 with
          | FEscape q x _ =>
              v ← get xrev ;;
              ans ← (#assert v ;;
                     tgts ← get xtgts ;;
                     match getm tgts (xindex st.2.1 (panchor q)) with
                     | Some (t0, m0) =>
                         ppo ← get xpp ;;
                         match ppo with
                         | Some pp =>
                             ret (((tnode q == t0)
                                   || (paired t0 && (tnode q == omega t0)))
                                  && (inl x != m0)
                                  && (th_eval Txc pp t0 m0
                                      == th_eval Txc pp (tnode q) (inl x)))
                         | None =>
                             pp ← dPP ;;
                             #put xpp := Some pp ;;
                             ret (((tnode q == t0)
                                   || (paired t0 && (tnode q == omega t0)))
                                  && (inl x != m0)
                                  && (th_eval Txc pp t0 m0
                                      == th_eval Txc pp (tnode q) (inl x)))
                         end
                     | None => ret false
                     end) ;;
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && ans)
          | FShort q _ =>
              v ← get xrev ;;
              ans ← (#assert v ;;
                     tgts ← get xtgts ;;
                     match getm tgts (xindex st.2.1 (tnode q)) with
                     | Some (t0, m0) =>
                         ppo ← get xpp ;;
                         match ppo with
                         | Some pp =>
                             ret (((panchor q == t0)
                                   || (paired t0 && (panchor q == omega t0)))
                                  && (inr (fcomplete sg.1.1 st.1.1 d sg.2.1) != m0)
                                  && (th_eval Txc pp t0 m0
                                      == th_eval Txc pp (panchor q)
                                           (inr (fcomplete sg.1.1 st.1.1 d sg.2.1))))
                         | None =>
                             pp ← dPP ;;
                             #put xpp := Some pp ;;
                             ret (((panchor q == t0)
                                   || (paired t0 && (panchor q == omega t0)))
                                  && (inr (fcomplete sg.1.1 st.1.1 d sg.2.1) != m0)
                                  && (th_eval Txc pp t0 m0
                                      == th_eval Txc pp (panchor q)
                                           (inr (fcomplete sg.1.1 st.1.1 d sg.2.1))))
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
                   && keepC fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ x_inv (s0, s1) ⦄.
Proof.
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
eapply (r_fact (st.1.2 = fxroot st.1.1 st.2.1 st.2.2)).
  { move=> s0 s1 [[hinv _] hr].
    rewrite /rem_inv /= in hr.
    move/x_invE: hinv => [_ hRXr].
    by rewrite hr in hRXr; case: hRXr. }
move=> hroot.
have huniq : uniq (xunder [::] (tshape st.2.1)) := gen_xuniq st.2.1.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
- (* FColl: keepColl nulls it on both sides *)
  apply r_ret => s0 s1 hpre; split.
  + by rewrite andbF.
  + by case: hpre => [[hinv _] _].
- (* FEscape: real XCHECK wins (partner branch) *)
  case Eans: P; last first.
  + (* P = false: both sides false *)
    eapply (r_get_rhs_known xrev true).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    rewrite [assertD true _]/= [bind (getr _ _) _]/=.
    eapply (r_get_rhs_known xtgts
              (qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2))).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    destruct (qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2)
                (xindex st.2.1 (panchor q))) as [[t0 m0]|] eqn:Eg;
      rewrite Eg /=.
    * eapply (r_get_rhs_known xpp (Some st.1.1)).
        { move=> s0 s1 [[hinv _] hr].
          rewrite /rem_inv /= in hr.
          move/x_invE: hinv => [_ hRXr].
          by rewrite hr in hRXr; case: hRXr. }
      apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
    * apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
  + (* P = true: the verifying FEscape forgery wins XCHECK *)
    have hvm : fxvermd st.1.1 (fxroot st.1.1 st.2.1 st.2.2)
                 sg.1.1 d sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [hsub ha0 hcoll] := shrincs_fxmss_forgery_case_FEscape _ _ _ _ _ _ _ _ _ _ hvm E.
    eapply (r_get_rhs_known xrev true).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    rewrite [assertD true _]/= [bind (getr _ _) _]/=.
    eapply (r_get_rhs_known xtgts
              (qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2))).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    rewrite (getm_xcommitq_anchor st.1.1 st.2.1 st.2.2 q huniq hsub).
    eapply (r_get_rhs_known xpp (Some st.1.1)).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    apply r_ret => s0 s1 hpre; split; last by case: hpre => [[hinv _] _].
    (* the win predicate: partner branch [tnode q = omega (panchor q)],
       distinct constructors, equal evals *)
    rewrite paired_panchor omega_panchor eqxx andbT orbT andTb.
    rewrite [_ != _]/= andTb.
    case: x ha0 hcoll {E} => x1 x2 ha0 hcoll.
    rewrite th_eval_node.
    have hev : th_eval Txc st.1.1 (panchor q)
                 (inr (anchor_ends st.1.1 st.2.1 st.2.2 q))
               = anchor_val st.1.1 st.2.1 st.2.2 q.
      rewrite /th_eval /= decode_tweakK /anchor_ends /anchor_val.
      exact: (anchor_pk st.1.1 (posid q)
                (nth [::] st.2.2 (index q (leaf_paths (tshape st.2.1))))).
    rewrite hev -ha0.
    by rewrite hcoll eqxx.
- (* FShort: real XCHECK wins (partner branch) *)
  case Eans: P; last first.
  + eapply (r_get_rhs_known xrev true).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    rewrite [assertD true _]/= [bind (getr _ _) _]/=.
    eapply (r_get_rhs_known xtgts
              (qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2))).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    destruct (qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2)
                (xindex st.2.1 (tnode q))) as [[t0 m0]|] eqn:Eg;
      rewrite Eg /=.
    * eapply (r_get_rhs_known xpp (Some st.1.1)).
        { move=> s0 s1 [[hinv _] hr].
          rewrite /rem_inv /= in hr.
          move/x_invE: hinv => [_ hRXr].
          by rewrite hr in hRXr; case: hRXr. }
      apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
    * apply r_ret => s0 s1 hpre.
      split; last by case: hpre => [[hinv _] _].
      by [].
  + have hvm : fxvermd st.1.1 (fxroot st.1.1 st.2.1 st.2.2)
                 sg.1.1 d sg.2.1 sg.2.2.
      move: Eans; rewrite /P -hroot => /andP[/andP[h _] _]; exact: h.
    have [ltr [hsub hpid ha hnode]] := shrincs_fxmss_forgery_case_FShort _ _ _ _ _ _ _ _ _ hvm E.
    eapply (r_get_rhs_known xrev true).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    rewrite [assertD true _]/= [bind (getr _ _) _]/=.
    eapply (r_get_rhs_known xtgts
              (qmap_from 0 (xcommitq st.1.1 st.2.1 st.2.2))).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    rewrite (getm_xcommitq_node st.1.1 st.2.1 st.2.2 q ltr.1 ltr.2 huniq hsub).
    eapply (r_get_rhs_known xpp (Some st.1.1)).
      { move=> s0 s1 [[hinv _] hr].
        rewrite /rem_inv /= in hr.
        move/x_invE: hinv => [_ hRXr].
        by rewrite hr in hRXr; case: hRXr. }
    apply r_ret => s0 s1 hpre; split; last by case: hpre => [[hinv _] _].
    rewrite paired_tnode omega_tnode eqxx andbT orbT andTb.
    rewrite [_ != _]/= andTb.
    have hevn : th_eval Txc st.1.1 (tnode q)
                  (inl (tval st.1.1 st.2.1 st.2.2 (rcons q false) ltr.1,
                        tval st.1.1 st.2.1 st.2.2 (rcons q true) ltr.2))
                = a.
      by rewrite (th_eval_xnode st.1.1 q) -hnode.
    have heva : th_eval Txc st.1.1 (panchor q)
                  (inr (fcomplete sg.1.1 st.1.1 d sg.2.1)) = a.
      rewrite hpid /th_eval /= decode_tweakK.
      rewrite ha recover_fcomplete /fcomplete /shrincs_fxmss_wots_pk_adrs.
      by case: (sg.1.1).
    by rewrite hevn heva eqxx.
- (* FAnchor: nulled in both (keepColl FAnchor = false) *)
  apply r_ret => s0 s1 hpre; split; first by [].
  by case: hpre => [[hinv _] _].
Qed.

(** The IDEAL FORGE verdict: [fverd keepNone] equals [forge_redx]'s
    classify-and-XCHECK under [TCRX false] (XCHECK always answers
    [false], matching [keepNone]'s nulling of every case). *)
Lemma r_forge_verdict_ideal (st : FXST) (lg : seq M)
    (tb : chMap (('nat × 'nat) × M) R) (sd : chMap 'nat D)
    (m : M) (sg : FXSIG) (d : D) :
  ⊢ ⦃ λ '(s0, s1),
        (x_inv ⋊ rem_lhs Lst (Some st) ⋊ rem_rhs Lst (Some st)) (s0, s1) ⦄
     ret (fverdN keepNone st st.2.2 st.2.1 lg sd tb m sg d)
     ≈ (match shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2 with
          | FEscape q x _ =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && false)
          | FShort q _ =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d) && false)
          | fc' =>
              ret (((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2
                     && (m \notin lg))
                    && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d)
                   && keepNone fc')
          end)
  ⦃ λ '(b0, s0) '(b1, s1), b0 = b1 ∧ x_inv (s0, s1) ⦄.
Proof.
set P := ((fxvermd st.1.1 st.1.2 sg.1.1 d sg.2.1 sg.2.2 && (m \notin lg))
          && ~~ coll_ev D M R sd tb (sg.1.1, m) sg.1.2 d).
rewrite /fverd -/P.
case E: (shrincs_fxmss_forgery_case_at_N st.1.1 st.2.1 st.2.2 sg.1.1 d sg.2.1 sg.2.2)
  => [q x y|q x a0|q a|]; rewrite /=.
all: apply r_ret => s0 s1 hpre; split;
     [ by rewrite /keepNone andbF
     | by case: hpre => [[hinv _] _] ].
Qed.

(* ------------------------------------------------------------------ *)
(** ** The two [perfect] lemmas *)

Local Notation G7 b :=
  (G7f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).
Local Notation G8 b :=
  (G8f PP N D M R F Tl Hgrind Htree dPP dN dR dD S_wn c_max h_sf
     q_s q_h n_max q_f b).

Lemma R_x_real (b : bool) :
  perfect IG (G7 b) (R_x b ∘ TCRX true).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ x_inv).
{ rewrite /x_inv. ssprove_invariant. by rewrite /rel_empty /RXr. }
simplify_eq_rel arg.
- (* GEN *)
  rewrite /gen5 /gen5_body.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/x_invE: hinv => [hign _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1 (hign (shrincs_fxmss_st_loc PP N)) // /IGN'; fmap_solve. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), xblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    apply: (xinv_init s0 s1 hinv).
    rewrite /rem_inv /= in hrem1.
    by rewrite -hrem1. }
  simpl.
  rewrite (resolve_xcq true (encode_adrs (gadrs (0, 0))) (inl n0)).
  eapply (r_get_bind_rhs xpp None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (xblk_set_pp pp _ _ _ _ _ hpre). }
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
  eapply (r_xgcheck_spec true pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  rewrite code_link_bind.
  eapply (r_xtree_spec true pp arg xss _ hkeys [::] (tshape arg) [::]).
  + apply: gen_hidx; by rewrite hxsz.
  + exact: gen_xdbl.
  + by apply: gen_bud.
  rewrite tval_root /xcommitq /=.
  rewrite (resolve_xgp true Datatypes.tt).
  eapply (r_get_bind_rhs xpp (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (xblk_set_rev _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrev htws htgts.
  split; first by [].
  apply: x_invI.
  - apply: heap_ignore_set_both.
    apply: heap_ignore_set_both.
    exact: hign.
  - get_heap_simpl.
    rewrite hpp hrev htws htgts /=.
    split=> //.
    by rewrite unzip1_xcommitq.
- (* SIGN: pure sync (opr-free) *)
  rewrite /sign5 /sign5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. }
  move=> sc.
  ssprove_sync => hsc.
  ssprove_sync. { x_get_pre. }
  move=> v.
  ssprove_sync => vSome.
  ssprove_sync. { x_get_pre. }
  move=> us.
  ssprove_sync. { x_get_pre. }
  move=> lg.
  ssprove_sync. { x_get_pre. }
  move=> mp.
  ssprove_sync. { x_get_pre. }
  move=> tb.
  ssprove_sync. { x_get_pre. }
  move=> sd.
  case: [&& leaf_okP h_sf (getSome v vSome).2.1 arg.2 & arg.2 \notin domm us];
    last first.
  { ssprove_sync. { x_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  case: (sd (lidx h_sf (getSome v vSome).2.1 arg.2)) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
    + ssprove_sync. { x_put_pre. }
      ssprove_sync. { x_put_pre. }
      by apply r_ret.
    + ssprove_sync. { x_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
	  case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
  + ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    by apply r_ret.
  + ssprove_sync. { x_put_pre. } by apply r_ret.
- (* HASH: pure sync *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. }
  move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { x_get_pre. }
  move=> mp.
  case: (mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
  by apply r_ret.
- (* FORGE: bookkeeping is now b-unconditional on BOTH sides; only the
     returned verdict is gated by [b].  Sync the shared bookkeeping, then
     [case: b]: the [b = true] verdict reuses [r_forge_verdict] UNCHANGED
     (classify-and-XCHECK at the bare-verdict layer), the [b = false]
     verdict is the constant [false] on both sides. *)
  destruct arg as [m sg].
  rewrite /forge_keep /forge_keep_body /forge_redx.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. } move=> fc.
  eapply rel_jdg_replace; [| reflexivity | solve [ssprove_match_commut_gen]].
  simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => sto0.
  eapply r_get_remember_rhs => sto1.
  eapply (r_fact (sto1 = sto0)).
    { move=> s0 s1 [[hinv h0] h1].
      move/x_invE: hinv => [hign _].
      rewrite /rem_inv /= in h0 h1.
      by rewrite -h0 -h1 (hign (shrincs_fxmss_st_loc PP N) ltac:(rewrite /IGN'; fmap_solve)). }
  move=> e; subst sto1.
  eapply r_assertD_same. move=> stSome.
  have Esto : sto0 = Some (getSome sto0 stSome).
    by case: sto0 stSome => [a|] stSome.
  set st := getSome sto0 stSome in Esto *.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. } move=> lg.
  ssprove_sync. { x_get_pre. } move=> mp.
  ssprove_sync. { x_get_pre. } move=> tb.
  ssprove_sync. { x_get_pre. } move=> sd.
  case Emd: (mp (sg.1.2, (st.1, (sg.1.1, m)))) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    rewrite Esto.
    case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
    exact: (r_forge_verdict st lg tb sd m sg d). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
  rewrite Esto.
  case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
  exact: (r_forge_verdict st lg tb sd m sg d).
Qed.

Lemma R_x_ideal (b : bool) :
  perfect IG (G8 b) (R_x b ∘ TCRX false).
Proof.
ssprove_share. eapply prove_perfect.
eapply (eq_rel_perf_ind _ _ x_inv).
{ rewrite /x_inv. ssprove_invariant. by rewrite /rel_empty /RXr. }
simplify_eq_rel arg.
- (* GEN: verbatim the real-side proof, [TCRX false] *)
  rewrite /gen5 /gen5_body.
  eapply r_get_remember_lhs => sto.
  eapply r_get_remember_rhs => sto'.
  eapply (r_fact (sto' = sto)).
    { move=> s0 s1 [[hinv hrem0] hrem1].
      move/x_invE: hinv => [hign _].
      rewrite /rem_inv /= in hrem0 hrem1.
      by rewrite -hrem0 -hrem1 (hign (shrincs_fxmss_st_loc PP N)) // /IGN'; fmap_solve. }
  move=> e; subst sto'.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> e0 _.
  rewrite code_link_assertD.
  eapply r_assertD; first by [].
  move=> hcap _.
  case: sto e0 => [pk|] e0; first by discriminate e0.
  eapply rpre_weaken_rule with
    (pre := λ '(s0, s1), xblk None false [::] emptym (s0, s1));
    last first.
  { move=> s0 s1 [[hinv hrem0] hrem1].
    apply: (xinv_init s0 s1 hinv).
    rewrite /rem_inv /= in hrem1.
    by rewrite -hrem1. }
  simpl.
  rewrite (resolve_xcq false (encode_adrs (gadrs (0, 0))) (inl n0)).
  eapply (r_get_bind_rhs xpp None).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  rewrite !bind_assoc.
  eapply r_scheme_bind; first exact: prog_valid.
  move=> pp; cbv beta.
  eapply r_put_bind_rhs.
    { move=> s0 s1 hpre; exact: (xblk_set_pp pp _ _ _ _ _ hpre). }
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
  eapply (r_xgcheck_spec false pp _ arg sd (iota 0 (size (leaf_paths (tshape arg))))).
  rewrite code_link_assertD.
  rewrite -[all _ _]/(sdgrind pp arg sd).
  eapply r_assertD_same.
  move=> e1.
  rewrite code_link_bind.
  eapply (r_xtree_spec false pp arg xss _ hkeys [::] (tshape arg) [::]).
  + apply: gen_hidx; by rewrite hxsz.
  + exact: gen_xdbl.
  + by apply: gen_bud.
  rewrite tval_root /xcommitq /=.
  rewrite (resolve_xgp false Datatypes.tt).
  eapply (r_get_bind_rhs xpp (Some pp)).
    { by move=> s0 s1 [_ h _ _ _]. }
  cbv beta iota.
  eapply r_put_rhs_weak.
    { move=> s0 s1 hpre; exact: (xblk_set_rev _ _ _ _ _ hpre). }
  eapply r_put_lhs; eapply r_put_lhs.
  eapply r_put_rhs; eapply r_put_rhs.
  apply r_ret => s0 s1 hpre.
  case: hpre => s1c [hpre1 ->].
  case: hpre1 => s1d [hpre2 ->].
  case: hpre2 => s0c [hpre3 ->].
  case: hpre3 => s0d [hblk ->].
  case: hblk => hign hpp hrev htws htgts.
  split; first by [].
  apply: x_invI.
  - apply: heap_ignore_set_both.
    apply: heap_ignore_set_both.
    exact: hign.
  - get_heap_simpl.
    rewrite hpp hrev htws htgts /=.
    split=> //.
    by rewrite unzip1_xcommitq.
- (* SIGN: pure sync *)
  rewrite /sign5 /sign5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. }
  move=> sc.
  ssprove_sync => hsc.
  ssprove_sync. { x_get_pre. }
  move=> v.
  ssprove_sync => vSome.
  ssprove_sync. { x_get_pre. }
  move=> us.
  ssprove_sync. { x_get_pre. }
  move=> lg.
  ssprove_sync. { x_get_pre. }
  move=> mp.
  ssprove_sync. { x_get_pre. }
  move=> tb.
  ssprove_sync. { x_get_pre. }
  move=> sd.
  case: [&& leaf_okP h_sf (getSome v vSome).2.1 arg.2 & arg.2 \notin domm us];
    last first.
  { ssprove_sync. { x_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dR)).
  eapply r_scheme_bind; first exact: prog_valid. move=> r.
  case: (sd (lidx h_sf (getSome v vSome).2.1 arg.2)) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
	    case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
    + ssprove_sync. { x_put_pre. }
      ssprove_sync. { x_put_pre. }
      by apply r_ret.
    + ssprove_sync. { x_put_pre. } by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
	  case: (shrincs_fxmss_sign_x _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (lidx h_sf (getSome v vSome).2.1 arg.2) r d) => [sg|].
  + ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    by apply r_ret.
  + ssprove_sync. { x_put_pre. } by apply r_ret.
- (* HASH: pure sync *)
  rewrite /hash5 /hash5_body.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. }
  move=> hc.
  ssprove_sync => hhc.
  ssprove_sync. { x_get_pre. }
  move=> mp.
  case: (mp arg) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    by apply r_ret. }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  rewrite !bind_assoc /=.
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
  by apply r_ret.
- (* FORGE: ideal XCHECK = false = keepNone.  As on the real side, the
     bookkeeping is now b-unconditional; [case: b] at the verdict reuses
     [r_forge_verdict_ideal] for [b = true], constant [false] for
     [b = false]. *)
  destruct arg as [m sg].
  rewrite /forge_keep /forge_keep_body /forge_redx.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. } move=> fc.
  eapply rel_jdg_replace; [| reflexivity | solve [ssprove_match_commut_gen]].
  simpl.
  ssprove_sync => hfc.
  eapply r_get_remember_lhs => sto0.
  eapply r_get_remember_rhs => sto1.
  eapply (r_fact (sto1 = sto0)).
    { move=> s0 s1 [[hinv h0] h1].
      move/x_invE: hinv => [hign _].
      rewrite /rem_inv /= in h0 h1.
      by rewrite -h0 -h1 (hign (shrincs_fxmss_st_loc PP N) ltac:(rewrite /IGN'; fmap_solve)). }
  move=> e; subst sto1.
  eapply r_assertD_same. move=> stSome.
  have Esto : sto0 = Some (getSome sto0 stSome).
    by case: sto0 stSome => [a|] stSome.
  set st := getSome sto0 stSome in Esto *.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_get_pre. } move=> lg.
  ssprove_sync. { x_get_pre. } move=> mp.
  ssprove_sync. { x_get_pre. } move=> tb.
  ssprove_sync. { x_get_pre. } move=> sd.
  case Emd: (mp (sg.1.2, (st.1, (sg.1.1, m)))) => [d|].
  { ssprove_code_simpl. simpl.
    ssprove_sync. { x_put_pre. }
    ssprove_sync. { x_put_pre. }
    rewrite Esto.
    case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
    exact: (r_forge_verdict_ideal st lg tb sd m sg d). }
  rewrite (code_link_scheme _ _ _ _ (prog_valid dD)).
  eapply r_scheme_bind; first exact: prog_valid. move=> d.
  ssprove_code_simpl. simpl.
  ssprove_sync. { x_put_pre. }
  ssprove_sync. { x_put_pre. }
  rewrite Esto.
  case: b; last (apply r_ret => s0 s1 [[hinv _] _]; split; [by [] | exact: hinv]).
  exact: (r_forge_verdict_ideal st lg tb sd m sg d).
Qed.

(* ------------------------------------------------------------------ *)
(** ** The hop theorem (claim:fxmss-struct-tcr) *)

Theorem Tcrx_hop (b : bool) (A : nom_package)
    (VA : ValidPackage (loc A) IG A_export A) :
  Adv (G7 b) (G8 b) A
  = AdvOf (TCRX_game Txc Cxc paired omega (2 * n_max - 1)) (A ∘ R_x b).
Proof.
rewrite (Adv_perfect_l (R_x_real b)) (Adv_perfect_r (R_x_ideal b)).
by rewrite Adv_reduction.
Qed.

End FXMSSTCRXHopProof.
