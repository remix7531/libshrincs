(** * SHRINCS.FXMSS.Scheme

    FXMSS (flexible XMSS), the stateful Merkle layer of SHRINCS, as a
    [sig_scheme] with a pure correctness lemma.  Definitions +
    correctness only; NO security proofs here (those are later P6
    files; see theories/SHRINCS/FXMSS/PROOF_PLAN.md).

    Counterparts: xmss.tex sec:fxmss description ("Flexible XMSS: a
    unified public-key recovery routine": the imaginary balanced
    embedding of declared height h_sf, the signing algorithm
    fxmss.sign_P and the shape-agnostic fxmss.pkFromSig);
    schrincs.tex alg:sign-stateful / alg:verify (stateful branch: the
    leaf identifier (z_star, i_star) on the wire, the stateful message
    digest Hmsg^sf and randomness PRFmsg^stateful, the stateful
    counter q with persist-before-release update);
    construction.tex sec:functions (Hmsg^sf, PRFmsg^stateful, PRF_f,
    the tree hash H on TREESTATEFUL addresses) and
    sec:adressing-stateful (address discipline; SHRINCS.Addressing);
    security.tex sec:fxmss-proof (the EU-CMA experiment whose step 1
    has the adversary submit the tree structure — here the [SParam]
    of the [sig_scheme]).

    ** Tree representation

    The imaginary balanced tree of declared height [h_sf] never
    materializes: nodes are bool paths (HBS.Math.BinTree), and the
    paper's (height z, horizontal index i) coordinates are recovered
    as [pos_id p = (h_sf - size p, idx_of_path p)] — the path/(z, i)
    conversions of BinTree carry all coordinate arithmetic.  The
    actual tree is a [bt unit] (the SHAPE) whose leaves are the
    WOTS+C anchors, sitting at arbitrary depths <= h_sf; evaluation
    ([val_bt]), authentication paths ([cons_ap]) and verification
    ([val_ap]) come from HBS.Math.Merkle with the position-tweaked
    node hash [node_hash] (H at the TREESTATEFUL address of the
    computed node).  Balanced XMSS and UXMSS are the instances
    [perfect_bt] (HBS.Math.MerkleBalanced) and [uxmss_bt]
    (HBS.Math.MerkleSkewed); their leafpos maps of the tex are the
    [leaf_paths] enumerations of those shapes (see PROOF_PLAN.md).

    ** Shape parameter encoding (SParam)

    The adversary of the FXMSS EU-CMA experiment chooses the tree
    structure before key generation (security.tex step 1), so
    [SParam] must be a [choice_type] encoding of an arbitrary shape.
    We use the preorder bit serialization ['list 'bool]
    ([encode_shape]: false = anchor, true = internal node followed by
    the two subtrees) with the fuelled parser [decode_shape];
    [decode_shapeK] (decode o encode = id) makes the encoding
    surjective onto all shapes, so the adversary loses no power.
    Shapes deeper than [h_sf] (whose nodes would not fit in the
    imaginary balanced tree, making the position-to-address map
    non-injective) and non-parsing strings are NORMALIZED to the
    trivial single-anchor shape [BLeaf tt] ([shape_of]); this is the
    total-function counterpart of the tex's footnote that ill-formed
    structure/queries are answered bot.

    ** Building blocks (construction.tex sec:functions, stateful)

    - [F], [Tl], [Hgrind]: the WOTS+C leaf layer, exactly as in
      SHRINCS.WOTSC.Scheme (chain hash, pk compression Theta_l,
      grinding hash), instantiated per anchor at its (z_star, i_star).
    - [Htree]: the tree-node hash H : B^n x B^288 x B^2n -> B^n on
      TREESTATEFUL (type 9) addresses; the 2n-byte two-children input
      is modeled as a pair [N * N].
    - [Hmsg]: the stateful message digest Hmsg^sf(R, PKseed, PKroot,
      idx, M) -> B^2n, transcribed argument-for-argument as a pure
      function [R -> PP -> N -> nat * nat -> M -> D]; the 33-byte
      leaf identifier idx is the pair (z_star, i_star).  Modeled PURE
      with the randomness R as an explicit argument; the random-oracle
      treatment (reprogramming hop F.2 -> F.3) lives at the games
      layer (PROOF_PLAN.md).  The PKroot argument is instantiated
      with the FXMSS root PKsf, per the security.tex F.0 -> F.1
      footnote (the rkTCR notion ignores this argument, so folding
      the SHRINCS-level PKroot into the root slot is WLOG).
    - [PRFf]: PRF_f(PKseed, SKseed, ADRS_sf) deriving the WOTS+C
      chain starts at WOTSPRFSF (type 12) addresses (khf-style pure
      function; the PRF game hop F.1 -> F.2 is a games-layer matter).
    - [PRFmsg]: PRFmsg^stateful(SKprf, idx, M) deriving the message
      randomness R (schrincs.tex alg:sign-stateful line R <- ...).

    ** Keys, signatures, state

    - sk = (PKseed, SKseed, SKprf, shape encoding, counter q): the
      stateful counter lives INSIDE Sk (HBS.Sig.Scheme convention:
      stateful signing as key update; the tex's persist-before-release
      rule is the [sign sk m = Some (sig, sk')] shape).  The tex's SK
      additionally caches PKsf/PKroot; here they are recomputed (pure
      functions of the seeds, a documented representation choice).
    - pk = (PKseed, PKsf) with PKsf = [fx_root] (the val_bt of the
      WOTS+C anchor values under [node_hash]).
    - signature = ((z_star, i_star), R, (wots chain values, counter),
      auth path): the leaf identifier and randomness on the wire as
      in schrincs.tex alg:sign-stateful's output
      R || idx || sigma_tree (the PKsl component is SHRINCS-level,
      not FXMSS-level).  AUTH PATH ORIENTATION: top-down (root-side
      sibling first), the [cons_ap]/[val_ap] convention — the
      REVERSE of the tex's bottom-up A_1..A_{h_sf - z_star}; a pure
      wire-format presentation choice.

    ** Signing schedule (documented deviation)

    The tex parameterizes signing by a shape-specific leaf-placement
    map leafpos_P(q); here the q-th signature uses the q-th leaf of
    the shape in left-to-right order ([leaf_paths] enumeration).  For
    the balanced shape this is leafpos_B(q) = (0, q) literally; for
    the UXMSS spine it is leafpos_U(q+1) (MerkleSkewed's
    [spine_path], whose (z, i) coordinates are proved to match
    leafpos_U there).  Left-to-right order is injective for every
    shape, which is all the tex requires of a placement map
    (schrincs.tex, "provided the placement map is injective").  The
    EU-CMA experiment of security.tex additionally lets the adversary
    pick WHICH leaf each query uses; the formalized experiment is the
    counter-schedule instantiation — see PROOF_PLAN.md ("EU-CMA
    model") for the discussion.

    ** Verification (xmss.tex fxmss.pkFromSig + schrincs.tex
       alg:verify, stateful branch)

    - bounds check z_star <= h_sf and i_star < 2^(h_sf - z_star)
      (alg:verify line 3);
    - recompute the digest with the leaf identifier bound in;
    - recover the WOTS+C anchor value from the one-time signature
      ([recover_anchor]; [verify_sigE] relates it to WOTSC's
      verify_sig);
    - walk up h_sf - z_star steps with [val_ap] at the imaginary-tree
      TREESTATEFUL addresses and compare with PKsf.
    The tex's signature-size check |sigma_tree| = l*n + c +
    (h_sf - z_star)*n (alg:verify line 4) is [size ws.1 == l] (in
    [wots_checks]) plus the auth-path length, which [val_ap] enforces
    structurally (it returns None unless size ap = path length;
    [fx_sign_auth_size] records the honest length).

    ** Other documented deviations

    - The WOTS+C chain starts are derived via [PRFf] (the scheme
      proper, wotsc.tex kg), while the standalone WOTSC.Scheme of P5
      SAMPLES them; the two meet at the F.1 -> F.2 PRF hop, after
      which FXMSS's leaves are exactly P5's sampled instances.
    - Grinding failure: [sign] refuses (None) when the bounded
      grinding search of the leaf instance fails (the c_max cap
      deviation of HBS.Games.STCRP / WOTSC.Scheme); the counter does
      NOT advance on refusal (nothing was released).  The tex grinds
      unboundedly.
    - [sign] refuses (None) when the counter exceeds the shape's
      leaf count (the tex's cap(P) check, alg:sign-stateful line 3).

    Style: theories/SHRINCS/WOTSC/Scheme.v. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import Prelude Math.BinTree Math.Merkle Sig.Scheme.
From SHRINCS Require Import Addressing WOTSC.Scheme.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

(* ------------------------------------------------------------------ *)
(** ** Shape (de)serialization and generic tree helpers

    Section-free: none of this depends on the FXMSS parameters. *)

Set Implicit Arguments.
Unset Strict Implicit.

(** Preorder bit serialization of a shape: [false] = anchor leaf,
    [true] = internal node followed by left then right subtree. *)
Fixpoint encode_shape (t : bt unit) : seq bool :=
  match t with
  | BLeaf _ => [:: false]
  | BNode l r => true :: encode_shape l ++ encode_shape r
  end.

(** Fuelled preorder parser; returns the tree and the unconsumed
    suffix.  Fuel [size s] always suffices ([decode_shape_auxP]). *)
Fixpoint decode_shape_aux (fuel : nat) (s : seq bool)
    : option (bt unit * seq bool) :=
  match fuel with
  | 0 => None
  | fuel'.+1 =>
      match s with
      | false :: s' => Some (BLeaf tt, s')
      | true :: s' =>
          match decode_shape_aux fuel' s' with
          | Some (l, s'') =>
              match decode_shape_aux fuel' s'' with
              | Some (r, s''') => Some (BNode l r, s''')
              | None => None
              end
          | None => None
          end
      | [::] => None
      end
  end.

(** Total parser: non-parsing strings (including those with trailing
    junk) decode to the trivial single-anchor shape. *)
Definition decode_shape (s : seq bool) : bt unit :=
  if decode_shape_aux (size s) s is Some (t, [::]) then t else BLeaf tt.

Lemma decode_shape_auxP (t : bt unit) (rest : seq bool) (fuel : nat) :
  size (encode_shape t) <= fuel ->
  decode_shape_aux fuel (encode_shape t ++ rest) = Some (t, rest).
Proof.
elim: t rest fuel => [[]|l IHl r IHr] rest [|fuel] //=.
rewrite ltnS size_cat => hsz.
have h1 : size (encode_shape l) <= fuel := leq_trans (leq_addr _ _) hsz.
have h2 : size (encode_shape r) <= fuel := leq_trans (leq_addl _ _) hsz.
by rewrite -catA (IHl _ _ h1) (IHr _ _ h2).
Qed.

Lemma decode_shapeK : cancel encode_shape decode_shape.
Proof.
move=> t; rewrite /decode_shape.
have := decode_shape_auxP [::] (leqnn (size (encode_shape t))).
by rewrite cats0 => ->.
Qed.

(** Every member of [leaf_paths] really is an anchor (the
    unit-shaped strengthening of BinTree's [leaf_paths_correct]). *)
Lemma leaf_paths_subtree (t : bt unit) (p : seq bool) :
  p \in leaf_paths t -> subtree_at t p = Some (BLeaf tt).
Proof.
elim: t p => [[]|l IHl r IHr] p /=.
- by rewrite inE => /eqP ->.
- rewrite mem_cat => /orP[] /mapP[q hq ->] /=.
  + exact: IHl.
  + exact: IHr.
Qed.

(** Decorating a shape with position-dependent leaf values: the
    arbitrary-shape counterpart of MerkleBalanced's [perfect_bt]
    leaf-value assignment.  [pos] is the absolute position of the
    subtree's root. *)
Section PosMap.

Context {A B : Type} (f : seq bool -> B).

Fixpoint bt_posmap (pos : seq bool) (t : bt A) : bt B :=
  match t with
  | BLeaf _ => BLeaf (f pos)
  | BNode l r =>
      BNode (bt_posmap (rcons pos false) l) (bt_posmap (rcons pos true) r)
  end.

Lemma bt_depth_posmap pos t : bt_depth (bt_posmap pos t) = bt_depth t.
Proof. by elim: t pos => [//|l IHl r IHr] pos /=; rewrite IHl IHr. Qed.

Lemma subtree_at_posmap pos t p :
  subtree_at (bt_posmap pos t) p
  = omap (bt_posmap (pos ++ p)) (subtree_at t p).
Proof.
elim: p pos t => [|b p IH] pos [a|l r] //=.
- by rewrite cats0.
- by rewrite cats0.
- by case: b; rewrite IH cat_rcons.
Qed.

End PosMap.

Unset Implicit Arguments.

Section FXMSSScheme.

(* ------------------------------------------------------------------ *)
(** ** Context: types, building blocks, samplers, parameters *)

(** Public parameter (PKseed), hash domain (n-byte strings), message
    digest space (the 2n-bit output of Hmsg^sf, = the WOTS+C message
    space), user message space, digest randomness space, secret-seed
    space (SKseed), PRF-key space (SKprf). *)
Context (PP N D M R Ks Kp : choice_type).

(** WOTS+C leaf layer (wotsc.tex; SHRINCS.WOTSC.Scheme). *)
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).

(** Tree-node hash H on TREESTATEFUL addresses; the 2n-byte
    two-children message as a pair (header). *)
Context (Htree : PP -> adrs_sf -> N * N -> N).

(** Stateful message digest Hmsg^sf(R, PKseed, PKroot, idx, M)
    (construction.tex sec:functions), transcribed argument order;
    idx = (z_star, i_star). *)
Context (Hmsg : R -> PP -> N -> nat * nat -> M -> D).

(** PRF_f(PKseed, SKseed, ADRS_sf) and
    PRFmsg^stateful(SKprf, idx, M) (construction.tex). *)
Context (PRFf : PP -> Ks -> adrs_sf -> N).
Context (PRFmsg : Kp -> nat * nat -> M -> R).

(** Samplers for key generation (seeds only; all leaf secrets are
    PRF-derived, per the tex). *)
Context (dPP : dist PP) (dKs : dist Ks) (dKp : dist Kp).

(** WOTS+C parameters (wotsc.tex; see WOTSC.Scheme header) and the
    declared imaginary-tree height h_sf (xmss.tex: nodes are
    (z, i) with z <= h_sf, i < 2^(h_sf - z)). *)
Context (w l S_wn c_max : nat).
Context (h_sf : nat).

(** Leaf-layer shorthand: the WOTS+C signing function of the
    instance anchored at (z, i). *)
Local Notation wsign_sig z i :=
  (sign_sig PP N D F Hgrind w l S_wn c_max z i).

(* ------------------------------------------------------------------ *)
(** ** Positions, addresses, node hash *)

(** Paper coordinates of the node at absolute path [p]: height
    z = h_sf - size p (distance from the imaginary leaf level),
    horizontal index i = the path bits read MSB-first. *)
Definition pos_id (p : seq bool) : nat * nat :=
  (h_sf - size p, idx_of_path p).

(** TREESTATEFUL (type 9) address of the node computed at position
    [pos] (xmss.tex: tree height z, tree index i). *)
Definition node_hash (pp : PP) (pos : seq bool) (x y : N) : N :=
  Htree pp (tree_node_adrs (h_sf - size pos) (idx_of_path pos)) (x, y).

(** Position-to-coordinates injectivity inside the declared height —
    the distinct-tweaks backbone of the later tree hops. *)
Lemma pos_id_inj (p q : seq bool) :
  size p <= h_sf -> size q <= h_sf -> pos_id p = pos_id q -> p = q.
Proof.
move=> hp hq [e1 e2].
have hsz : size p = size q by rewrite -(subKn hp) e1 (subKn hq).
by rewrite -[p]path_of_idx_of_path -[q]path_of_idx_of_path hsz e2.
Qed.

Lemma node_adrs_inj (p q : seq bool) :
  size p <= h_sf -> size q <= h_sf ->
  tree_node_adrs (h_sf - size p) (idx_of_path p)
    = tree_node_adrs (h_sf - size q) (idx_of_path q) ->
  p = q.
Proof.
move=> hp hq [e1 e2].
by apply: pos_id_inj => //; rewrite /pos_id e1 e2.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Shapes *)

(** A shape fits the imaginary balanced tree iff no node is deeper
    than h_sf. *)
Definition wf_shape (t : bt unit) : bool := bt_depth t <= h_sf.

(** Decode + normalize (header: ill-formed parameters give the
    trivial single-anchor shape). *)
Definition shape_of (sp : seq bool) : bt unit :=
  if wf_shape (decode_shape sp) then decode_shape sp else BLeaf tt.

Lemma wf_shape_of sp : bt_depth (shape_of sp) <= h_sf.
Proof. by rewrite /shape_of; case: ifP. Qed.

(** Surjectivity onto well-formed shapes: the adversary can submit
    any tree that fits the declared height. *)
Lemma shape_of_encode (t : bt unit) :
  wf_shape t -> shape_of (encode_shape t) = t.
Proof. by move=> h; rewrite /shape_of decode_shapeK h. Qed.

(** Path of the q-th leaf (left-to-right signing schedule, header). *)
Definition sign_path (sp : seq bool) (q : nat) : seq bool :=
  nth [::] (leaf_paths (shape_of sp)) q.

Lemma sign_path_leaf (sp : seq bool) (q : nat) :
  q < size (leaf_paths (shape_of sp)) ->
  subtree_at (shape_of sp) (sign_path sp q) = Some (BLeaf tt).
Proof. by move=> hq; apply: leaf_paths_subtree; exact: mem_nth. Qed.

Lemma sign_path_size (sp : seq bool) (q : nat) :
  q < size (leaf_paths (shape_of sp)) ->
  size (sign_path sp q) <= h_sf.
Proof.
move=> hq.
have hleaf : leaf_at (shape_of sp) (sign_path sp q) = Some tt.
  by rewrite /leaf_at sign_path_leaf.
exact: leq_trans (leaf_at_size hleaf) (wf_shape_of sp).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Leaf instances (WOTS+C at the anchors) *)

(** Chain starts of the instance anchored at zi = (z_star, i_star):
    PRF_f at the WOTSPRFSF (type 12) addresses, one per chain
    (wotsc.tex kg / construction.tex fig:wots-prf-sf-adrs). *)
Definition leaf_sk (pp : PP) (ks : Ks) (zi : nat * nat) : seq N :=
  [seq PRFf pp ks (wotsc_prf_adrs zi j) | j <- iota 0 l].

Lemma size_leaf_sk pp ks zi : size (leaf_sk pp ks zi) = l.
Proof. by rewrite size_map size_iota. Qed.

(** Compressed WOTS+C public key of the anchor at zi. *)
Definition leaf_pk (pp : PP) (ks : Ks) (zi : nat * nat) : N :=
  pk_of PP N F Tl w l zi.1 zi.2 pp (leaf_sk pp ks zi).

(* ------------------------------------------------------------------ *)
(** ** The value tree and the root *)

(** The shape decorated with the anchor public keys (the honest
    Merkle tree; xmss.tex treeNode_P). *)
Definition value_tree (pp : PP) (ks : Ks) (t : bt unit) : bt N :=
  bt_posmap (fun p => leaf_pk pp ks (pos_id p)) [::] t.

(** PKsf, the FXMSS public-key root. *)
Definition fx_root (pp : PP) (ks : Ks) (t : bt unit) : N :=
  val_bt (node_hash pp) [::] (value_tree pp ks t).

(* ------------------------------------------------------------------ *)
(** ** Signing (pure) *)

(** Signature carrier: leaf identifier (z_star, i_star), digest
    randomness R, WOTS+C signature (chain values, grind counter),
    authentication path (top-down; header). *)
Definition fxsig : Type :=
  (((nat * nat) * R) * ((seq N * nat) * seq N))%type.

(** schrincs.tex alg:sign-stateful, FXMSS slice: look up the q-th
    anchor, derive R and the digest (leaf identifier bound in), sign
    with the anchor's WOTS+C instance, attach the authentication
    path.  None on counter exhaustion or grinding failure (header).
    The [cons_ap] None branch is unreachable (the signing path stays
    inside the tree; [isSome_cons_ap]). *)
Definition fx_sign (pp : PP) (ks : Ks) (kp : Kp) (sp : seq bool) (q : nat)
    (m : M) : option fxsig :=
  if q < size (leaf_paths (shape_of sp)) then
    match
      wsign_sig (pos_id (sign_path sp q)).1 (pos_id (sign_path sp q)).2 pp
        (leaf_sk pp ks (pos_id (sign_path sp q)))
        (Hmsg (PRFmsg kp (pos_id (sign_path sp q)) m) pp
           (fx_root pp ks (shape_of sp)) (pos_id (sign_path sp q)) m),
      cons_ap (node_hash pp) [::] (value_tree pp ks (shape_of sp))
        (sign_path sp q)
    with
    | Some ws, Some ap =>
        Some ((pos_id (sign_path sp q),
               PRFmsg kp (pos_id (sign_path sp q)) m),
              (ws, ap))
    | _, _ => None
    end
  else None.

(* ------------------------------------------------------------------ *)
(** ** Verification (pure) *)

(** The recovered anchor value: WOTS+C pkFromSig at the claimed leaf
    identifier (xmss.tex fxmss.pkFromSig step 1) — complete the
    chains from the signature values at the recomputed digest and
    recompress. *)
Definition recover_anchor (pp : PP) (zi : nat * nat) (md : D)
    (ws : seq N * nat) : N :=
  Tl pp (wotsc_pk_adrs zi)
     (complete_ends PP N F w l zi.1 zi.2 pp
        (digest_of PP D Hgrind w l zi.1 zi.2 pp md ws.2) ws.1).

(** The WOTS+C-side checks of the flexible verifier: digest (at the
    signature's counter) in the post-grinding space, and exactly l
    chain values (wotsc.tex vf; the size check is part of the tex's
    |sigma_tree| length equation, header). *)
Definition wots_checks (pp : PP) (zi : nat * nat) (md : D)
    (ws : seq N * nat) : bool :=
  valid_digest w S_wn (digest_of PP D Hgrind w l zi.1 zi.2 pp md ws.2)
  && (size ws.1 == l).

(** Bridge to WOTSC.Scheme's verifier: verify_sig against a root is
    exactly [wots_checks] plus anchor-value comparison.  Later hop
    files rewrite along this to reuse the P5 analysis. *)
Lemma verify_sigE (pp : PP) (rt : N) (zi : nat * nat) (md : D)
    (ws : seq N * nat) :
  verify_sig PP N D F Tl Hgrind w l S_wn zi.1 zi.2 pp rt md ws
  = wots_checks pp zi md ws && (recover_anchor pp zi md ws == rt).
Proof. by rewrite /verify_sig /wots_checks /recover_anchor andbA. Qed.

(** The flexible verifier (xmss.tex fxmss.pkFromSig + schrincs.tex
    alg:verify stateful branch): bounds-check the leaf identifier,
    recompute the digest with the identifier bound in, recover the
    anchor value, walk up h_sf - z_star steps along the imaginary
    parent map (z+1, floor(i/2)) — i.e. along the path
    [path_of_idx (h_sf - z_star) i_star] — and compare with the
    root.  [val_ap] returns None unless the auth path has exactly
    the path's length, which subsumes the tex's size check. *)
Definition fx_verify (pp : PP) (rt : N) (m : M) (sg : fxsig) : bool :=
  let: ((zi, r), (ws, ap)) := sg in
  [&& (zi.1 <= h_sf)%N,
      (zi.2 < 2 ^ (h_sf - zi.1))%N,
      wots_checks pp zi (Hmsg r pp rt zi m) ws
    & val_ap (node_hash pp) [::] (path_of_idx (h_sf - zi.1) zi.2) ap
        (recover_anchor pp zi (Hmsg r pp rt zi m) ws) == Some rt].

(* ------------------------------------------------------------------ *)
(** ** Size sanity: the tex's path-length claim *)

(** The honest authentication path has length h_sf - z_star,
    determined by the leaf identifier alone (xmss.tex: "The path
    length h_sf - z_star is determined by the leaf identifier and
    need not be transmitted separately"). *)
Lemma fx_sign_auth_size pp ks kp sp q m zi r ws ap :
  fx_sign pp ks kp sp q m = Some ((zi, r), (ws, ap)) ->
  size ap = (h_sf - zi.1)%N.
Proof.
rewrite /fx_sign; case: ifP => // hq.
have hszp := sign_path_size sp q hq.
case E1: (wsign_sig _ _ _ _ _) => [ws'|] //=.
case E2: (cons_ap _ _ _ _) => [ap'|] //=.
case=> e1 _ _ e4; subst.
by rewrite (size_cons_ap E2) /pos_id /= subKn.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Correctness *)

(** THE pure correctness lemma: an honest signature (any seeds, any
    in-budget counter, successful grinding) verifies under the
    honest root.  Composes WOTSC's [verify_sign_sig] (the leaf) with
    Merkle's [val_ap_correct] (the tree walk). *)
Theorem fx_verify_sign (pp : PP) (ks : Ks) (kp : Kp) (sp : seq bool)
    (q : nat) (m : M) (sg : fxsig) :
  fx_sign pp ks kp sp q m = Some sg ->
  fx_verify pp (fx_root pp ks (shape_of sp)) m sg.
Proof.
rewrite /fx_sign; case: ifP => // hq.
set t := shape_of sp.
set p := sign_path sp q.
set zi := pos_id p.
set r := PRFmsg kp zi m.
set md := Hmsg r pp (fx_root pp ks t) zi m.
case E1: (wsign_sig _ _ _ _ _) => [ws|] //=.
case E2: (cons_ap _ _ _ _) => [ap|] //=.
case=> <- {sg}.
(* path facts *)
have hszp : size p <= h_sf := sign_path_size sp q hq.
have hsub : subtree_at t p = Some (BLeaf tt) := sign_path_leaf sp q hq.
have hpath : path_of_idx (h_sf - zi.1) zi.2 = p.
  by rewrite /zi /pos_id /= subKn // path_of_idx_of_path.
(* the anchor of the value tree at p is the honest WOTS+C pk *)
have hsubv : subtree_at (value_tree pp ks t) p
             = Some (BLeaf (leaf_pk pp ks (pos_id p))).
  by rewrite /value_tree subtree_at_posmap hsub.
(* tree walk: the honest auth path verifies to the root *)
have hval := val_ap_correct E2 hsubv.
(* leaf: the honest WOTS+C signature verifies to the honest leaf pk *)
have hxs : size (leaf_sk pp ks zi) = l := size_leaf_sk pp ks zi.
have hver := verify_sign_sig PP N D F Tl Hgrind w l S_wn c_max zi.1 zi.2
               pp (leaf_sk pp ks zi) md ws hxs E1.
rewrite verify_sigE in hver.
move/andP: hver => [hchecks /eqP hrec].
(* assemble the verifier's four conjuncts *)
rewrite /fx_verify; apply/and4P; split.
- by rewrite /zi /pos_id /= leq_subr.
- by rewrite /zi /pos_id /= subKn // idx_of_path_lt.
- exact: hchecks.
- apply/eqP; rewrite -/md hpath hrec.
  exact: hval.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The scheme as a [sig_scheme]

    Stateful signing as key update (HBS.Sig.Scheme): the counter
    advances only when a signature is released.  [SParam] is the
    encoded adversary-chosen shape; keygen normalizes it and derives
    everything else from the sampled seeds. *)

Definition FXMSS : sig_scheme := {|
  Pk := PP × N ;
  Sk := PP × (Ks × (Kp × (('list 'bool) × 'nat))) ;
  Msg := M ;
  Sig := (('nat × 'nat) × R) × ((('list N) × 'nat) × ('list N)) ;
  SParam := 'list 'bool ;
  keygen := fun sp => {code
    pp ← dPP ;;
    ks ← dKs ;;
    kp ← dKp ;;
    ret ((pp, (ks, (kp, (sp, 0)))), (pp, fx_root pp ks (shape_of sp))) } ;
  sign := fun sk m => {code
    ret (omap
      (fun sg =>
         (sg, (sk.1, (sk.2.1, (sk.2.2.1, (sk.2.2.2.1, sk.2.2.2.2.+1))))))
      (fx_sign sk.1 sk.2.1 sk.2.2.1 sk.2.2.2.1 sk.2.2.2.2 m)) } ;
  verify := fun pk m sg => fx_verify pk.1 pk.2 m sg
|}.

(** Correctness through the scheme record: the public key produced
    by [keygen] from the same seeds and shape parameter accepts
    every signature [sign] releases. *)
Lemma FXMSS_verify_sign (pp : PP) (ks : Ks) (kp : Kp) (sp : seq bool)
    (q : nat) (m : M) (sg : fxsig) :
  fx_sign pp ks kp sp q m = Some sg ->
  verify FXMSS (pp, fx_root pp ks (shape_of sp)) m sg.
Proof. exact: fx_verify_sign. Qed.

End FXMSSScheme.
