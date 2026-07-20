(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * SHRINCS.fxmss.games

    Game-instance scaffolding for the FXMSS EU-CMA proof: the [khf] instances for the
    two PRFs under attack ([Kf] for PRF_f, [Kpm] for PRFmsg^stateful),
    the pure "sampled-keys" layer (the scheme's functions re-keyed on
    an explicit per-anchor key list), and the top of the game chain:

      [G0f] — the flat ROM EU-CMA game pair for FXMSS (the formal
              security statement of thm:fxmss-main lives on this pair;
              "modeling Hmsg^sf as a random oracle" = the [FXHASH]
              oracle / lazily sampled digest map below);
      [G1f] — G0f after the PRF_f swap (hop 1, tex F.1 -> F.2): the
              per-anchor WOTS+C chain starts are independently sampled
              ([sample_keys]) instead of PRF_f-derived;
      [G2f] — G1f after the PRFmsg swap (hop 2; the tex absorbs this
              PRF distance into runtime, F.0 -> F.1 note): the
              signature randomness R comes from a lazily sampled
              random function table at the key (leaf id, message).

    The two hops live in [fxmss.prf_hop].

    ** Adversary-chosen leaf ids

       FXSIGN takes
       [(M × ('nat × 'nat))] — the message plus an adversary-chosen,
       structure-matching leaf id [zi] (security.tex F.0).  SIGN
       validates [zi] against the committed shape ([leaf_okP], bot on
       mismatch), refuses re-used ids via the used-set location
       [shrincs_fxmss_used_loc],
       and signs at slot [lidx st.2.1 zi].  Interface [I_G0f → I_G0fL].
       Games are assembled by the directed [valid_package_cons] idiom
       because the used-set body defeats the plain
       [package] TC search).

    ** G0f, the ROM EU-CMA encoding (the proof architecture "The top game G0f")

    - [FXGEN (sp)]: one-shot.  The adversary submits the tree
      structure (security.tex experiment step 1) as the encoded shape
      [sp] ([SParam] of fxmss.scheme; surjectivity onto well-formed
      shapes is [shrincs_fxmss_shape_encode]).  Samples pp/ks/kp, derives ALL
      per-anchor chain-start lists ([leaf_sks], pure PRF_f
      evaluations), stores them with the shape and returns
      (pp, PKsf).  By [shrincs_fxmss_root_xE] the stored root IS the scheme's
      [shrincs_fxmss_root]; precomputing [leaf_sks] at GEN instead of
      re-deriving per signature is value-equal (PRF_f is a pure
      function) and gives all three games literally the same
      SIGN/HASH/FORGE bodies over the stored key list.
    - The [n_max] cap: GEN asserts
      [size (leaf_paths (shrincs_fxmss_shape sp)) <= n_max] — the tex's cap(P)
      at the parameter level; the PRF_f reduction's query budget is
      [(n_max * l).+1].
    - [FXSIGN (m, zi)]: budget [q_s] is enforced by the per-call counter
      [shrincs_fxmss_scnt_loc], so refused queries consume budget. A
      log-size budget would admit unboundedly many refused queries, each
      evaluating PRFmsg and the digest
      oracle — so no PRF/reprogramming reduction could be query-
      bounded; the experiment also indexes queries 1..q_s.
      The signing leaf is the validated, fresh adversary-selected id [zi]; the
      digest is read through the LAZY RO MAP [shrincs_fxmss_rom_loc] at
      (R, (pk, (leaf id, m))) — the full Hmsg^sf input — NOT counted
      against the adversary's HASH budget.  Refusals (counter
      exhausted / grinding failure) return None and are NOT logged
      (EUCMA convention: forging on a refused message still counts —
      strictly stronger).
    - [FXHASH (x)]: the adversary's random-oracle interface, budget
      [q_h]; same lazy map.
    - [FXFORGE (m, sg)]: real = the flexible verifier with the digest
      read through the RO map ([shrincs_fxmss_verify_md] + lazy read) plus
      freshness [m \notin log]; ideal = ret false (HBS.games.THF
      real/ideal convention).  EU-CMA "success" = [AdvOf (G0f) A].
      BUDGET [q_f] (counter [shrincs_fxmss_fcnt_loc]; [q_f := 1] recovers the
      tex experiment's single forgery output): an UNBOUNDED FORGE
      oracle makes the reprogramming hop information-theoretically
      FALSE — each real-branch call performs an uncounted lazy rom
      read, and K calls on one message plant K correlated rom
      entries that a later SIGN hits with probability K/|R| (the
      full analysis is in the [fxmss.repro_hop] header). The [q_f]
      budget is therefore threaded through the whole game family.

    ** G1f / G2f vestigial samples

    [G1f]'s GEN carries a dead [_ ← dN] sample in the slot where
    G0f sampled the PRF_f key (and [G2f] additionally a dead
    [_ ← dR] in PRFmsg's key slot): they mirror the PRF reductions'
    PIN query (one unconditional EVAL at GEN time, at a tweak/leaf-id
    disjoint from every honest query point), which on the real side
    realizes the PRF key sampling at a fixed program point and on the
    ideal side lazily samples one dead table entry.  The pin is what
    makes both perfect lemmas hold WITHOUT losslessness assumptions
    on the samplers (the no-losslessness discipline of P5); the dead
      samples are dead code from G1f/G2f onward. See [fxmss.prf_hop]
      for the full coupling argument.

    ** Locations

    - [shrincs_fxmss_st_loc]  400: option ((pp, PKsf), (sp, xss)) — the static
      state, written once by GEN (also the one-shot flag);
      [xss : 'list ('list N)] is the per-anchor chain-start list, in
      [leaf_paths] order.

    ** Oracle-body normal form (proof ergonomics; semantically
       irrelevant)

    Every oracle body reads ALL its locations first, then branches /
    samples, then writes, then returns; and the lazy-RO read always
    ENDS in a write ([#put ... := setm mp x md], also on a table hit,
    where [setm] re-stores the present value — the same map).  This
    reads-then-writes discipline keeps the relational proofs of
    prf_hop.v one-pass (gets extracted against the invariant, one
    case split per lazy map, one put block per leaf), and the
    uniform [setm] write makes the two branches share one
    continuation.  Each oracle is observationally the natural one.
    - [shrincs_fxmss_kp_loc]  401: option Kp (G0f/G1f only; in G2f PRFmsg is a
      table).
    - [shrincs_fxmss_q_loc]   402: compatibility location for the game family.
    - [shrincs_fxmss_scnt_loc]403: the SIGN call budget counter.
    - [shrincs_fxmss_log_loc] 404: signed messages.
    - [shrincs_fxmss_rom_loc] 405: the Hmsg^sf lazy RO map.
    - [shrincs_fxmss_hcnt_loc]406: the adversary's HASH budget counter.
    - [shrincs_fxmss_rt_loc]  407: the PRFmsg table (G2f only).
    - [shrincs_fxmss_fcnt_loc]408: the FORGE call budget counter.

    The game instances follow [SHRINCS.wotsc.games] and the generic
    flattened-game pattern in [HBS.wots.games]. *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HBS Require Import prelude math.bin_tree math.merkle math.chain
  math.encoding sig.scheme games.thf games.prf toolkit.sample_seq.
From SHRINCS Require Import addressing wotsc.scheme wotsc.games fxmss.scheme.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

(* ------------------------------------------------------------------ *)
(** ** Generic tree facts (section-free)

    [leaf_paths_uniq]: distinct leaves have distinct paths — the
    index/nth round trip on the leaf enumeration ([index_sign_path]
    below) and the later hybrid bookkeeping depend on it.
    [eq_bt_posmap]: [bt_posmap] only looks at leaf positions. *)

Lemma leaf_paths_uniq {A : Type} (t : bt A) : uniq (leaf_paths t).
Proof.
elim: t => [a|l IHl r IHr] //=.
rewrite cat_uniq !map_inj_uniq ?IHl ?IHr //=; first last.
- by move=> p q [].
- by move=> p q [].
rewrite andbT; apply/hasPn => x /mapP[q _ ->].
by apply/negP => /mapP[q' _].
Qed.

Lemma eq_bt_posmap {A B : Type} (f g : seq bool -> B) (pos : seq bool)
    (t : bt A) :
  (forall q, q \in leaf_paths t -> f (pos ++ q) = g (pos ++ q)) ->
  bt_posmap f pos t = bt_posmap g pos t.
Proof.
elim: t pos => [a|l IHl r IHr] pos h /=.
- have := h [::]; rewrite inE cats0 => /(_ (eqxx _)) ->; reflexivity.
- congr BNode; [apply: IHl | apply: IHr] => q hq;
    rewrite cat_rcons; apply: h; rewrite /= mem_cat; apply/orP.
  + by left; apply: map_f.
  + by right; apply: map_f.
Qed.

Section FXMSSGames.

(* ------------------------------------------------------------------ *)
(** ** Context: same as fxmss.scheme, minus the pure [Hmsg] (the
    digest hash is the RO map here; [Hmsg] is kept ONLY as input to
    the scheme-bridge sanity lemmas), plus the samplers [dN] (leaf
    keys; = shrincs_fxmss_wots_scheme's), [dR] (digest randomness; G2f's table values)
    and [dD] (digest space; the lazy RO), and the experiment budgets
    [q_s] (signing), [q_h] (adversary HASH), [n_max] (anchor cap),
    [q_f] (FORGE calls; header). *)

Context {w l : nat}.
Local Notation adrs_sf := (addressing.adrs_sf l w).
Local Notation adrs_sf_ch := (addressing.adrs_sf_ch l w).

Context (PP N D M R Ks Kp : choice_type).
Context (F : PP -> adrs_sf -> N -> N).
Context (Tl : PP -> adrs_sf -> seq N -> N).
Context (Hgrind : PP -> adrs_sf -> D * nat -> nat).
Context (Htree : PP -> adrs_sf -> N * N -> N).
Context (Hmsg : R -> PP -> N -> nat * nat -> M -> D).
Context (PRFf : PP -> Ks -> adrs_sf -> N).
Context (PRFmsg : Kp -> nat * nat -> M -> R).
Context (dPP : dist PP) (dKs : dist Ks) (dKp : dist Kp).
Context (dN : dist N) (dR : dist R) (dD : dist D).
Context (S_wn c_max : nat).
Context (h_sf : nat).
Context (q_s q_h n_max : nat).
Context (q_f : nat).

(** Shorthands for the section-instantiated scheme operations. *)
Local Notation tshape := (shrincs_fxmss_shape h_sf).
Local Notation spath := (shrincs_fxmss_sign_path h_sf).
Local Notation posid := (shrincs_fxmss_pos_id h_sf).
Local Notation nhash := (shrincs_fxmss_node_hash PP N Htree h_sf).
Local Notation fleaf_sk := (shrincs_fxmss_leaf_secret PP N Ks PRFf).
Local Notation fpk_of zi := (shrincs_fxmss_wots_public_key PP N F Tl zi.1 zi.2).
Local Notation fvalue_tree := (shrincs_fxmss_value_tree PP N Ks F Tl PRFf h_sf).
Local Notation ffx_root := (shrincs_fxmss_root PP N Ks F Tl Htree PRFf h_sf).
Local Notation fsign_sig zi :=
  (shrincs_fxmss_wots_sign PP N D F Hgrind S_wn c_max zi.1 zi.2).
Local Notation fwots_checks := (shrincs_fxmss_wots_checks PP N D Hgrind S_wn).
Local Notation frecover := (shrincs_fxmss_recover_anchor PP N D F Tl Hgrind).
Local Notation ffx_sign :=
  (shrincs_fxmss_sign PP N D M R Ks Kp F Tl Hgrind Htree Hmsg PRFf PRFmsg
     S_wn c_max h_sf).
Local Notation ffx_verify :=
  (shrincs_fxmss_verify PP N D M R F Tl Hgrind Htree Hmsg S_wn h_sf).

(* ------------------------------------------------------------------ *)
(** ** The khf instances under attack (the proof architecture hops 1-2)

    [Kf]: PRF_f keyed by SKseed, message = (PKseed, encoded stateful
    address) — the FULL PRF_f input of construction.tex; [th_eval]
    decodes with wotsc.games' proven-cancelling [decode_tweak] (the
    junk branch on non-canonical tuples is dead code, [kh_evalE_Kf]).
    Outputs are n-byte strings, ideal sampler [dN].

    [Kpm]: PRFmsg^stateful keyed by SKprf, message = (leaf id, M),
    outputs digest randomness R, ideal sampler [dR]. *)

Definition Kf : khf :=
  {| kh_K := Ks ; kh_M := PP × adrs_sf_ch ; kh_N := N ;
     kh_eval := fun ks pa => PRFf pa.1 ks (decode_tweak pa.2) ;
     kh_dK := dKs ; kh_dN := dN |}.

Definition Kpm : khf :=
  {| kh_K := Kp ; kh_M := ('nat × 'nat) × M ; kh_N := R ;
     kh_eval := fun kp zim => PRFmsg kp zim.1 zim.2 ;
     kh_dK := dKp ; kh_dN := dR |}.

(** Sanity: on encoded (canonical) inputs the instances evaluate the
    scheme's PRFs — the hop file's interface to [kh_eval]. *)
Lemma kh_evalE_Kf (ks : Ks) (pp : PP) (a : adrs_sf) :
  kh_eval Kf ks (pp, encode_adrs a) = PRFf pp ks a.
Proof. by rewrite /= decode_tweakK. Qed.

Lemma kh_evalE_Kpm (kp : Kp) (zi : nat * nat) (m : M) :
  kh_eval Kpm kp (zi, m) = PRFmsg kp zi m.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** The sampled-keys pure layer

    The games G1f/G2f hold an explicit per-anchor key list
    [xss : seq (seq N)] (in [leaf_paths] order) where the scheme
    derives keys via PRF_f.  [value_tree_x]/[shrincs_fxmss_root_x]/[shrincs_fxmss_sign_x]
    are the scheme's functions re-keyed on that list; instantiating
    [xss := leaf_sks pp ks sp] recovers the scheme exactly
    ([value_tree_xE], [shrincs_fxmss_root_xE], [shrincs_fxmss_sign_xE]), which is how G0f
    (the honest game) is expressed over the same code skeleton. *)

Definition leaf_sks (pp : PP) (ks : Ks) (sp : seq bool) : seq (seq N) :=
  [seq fleaf_sk pp ks (posid p) | p <- leaf_paths (tshape sp)].

Definition value_tree_x (pp : PP) (sp : seq bool) (xss : seq (seq N)) :
    bt N :=
  bt_posmap
    (fun p => fpk_of (posid p) pp
                (nth [::] xss (index p (leaf_paths (tshape sp)))))
    [::] (tshape sp).

Definition shrincs_fxmss_root_x (pp : PP) (sp : seq bool) (xss : seq (seq N)) : N :=
  val_bt (nhash pp) [::] (value_tree_x pp sp xss).

(** At the PRF_f-derived key list, the sampled-keys tree IS the
    scheme's tree (and similarly the root). *)
Lemma value_tree_xE (pp : PP) (ks : Ks) (sp : seq bool) :
  value_tree_x pp sp (leaf_sks pp ks sp) = fvalue_tree pp ks (tshape sp).
Proof.
apply: eq_bt_posmap => q hq /=.
rewrite /leaf_sks (nth_map [::]) ?index_mem // nth_index //.
Qed.

Lemma shrincs_fxmss_root_xE (pp : PP) (ks : Ks) (sp : seq bool) :
  shrincs_fxmss_root_x pp sp (leaf_sks pp ks sp) = ffx_root pp ks (tshape sp).
Proof. by rewrite /shrincs_fxmss_root_x value_tree_xE. Qed.

(** The signing-schedule position of the q-th leaf path. *)
Lemma index_sign_path (sp : seq bool) (q : nat) :
  q < size (leaf_paths (tshape sp)) ->
  index (spath sp q) (leaf_paths (tshape sp)) = q.
Proof.
move=> hq; rewrite /shrincs_fxmss_sign_path index_uniq //; exact: leaf_paths_uniq.
Qed.

(** Signing at a GIVEN digest and randomness from the stored key
    list: the in-game signer of all three games (the digest comes
    from the RO map, the randomness from PRFmsg / the table). *)
Definition shrincs_fxmss_sign_x (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : nat) (r : R) (md : D) : option (shrincs_fxmss_signature N R) :=
  match
    fsign_sig (posid (spath sp q)) pp (nth [::] xss q) md,
    cons_ap (nhash pp) [::] (value_tree_x pp sp xss) (spath sp q)
  with
  | Some ws, Some ap => Some ((posid (spath sp q), r), (ws, ap))
  | _, _ => None
  end.

(** The scheme's signer is [shrincs_fxmss_sign_x] at the derived keys, the
    PRFmsg randomness and the pure-Hmsg digest — the honesty bridge
    for G0f's SIGN. *)
Lemma shrincs_fxmss_sign_xE (pp : PP) (ks : Ks) (kp : Kp) (sp : seq bool)
    (q : nat) (m : M) :
  ffx_sign pp ks kp sp q m
  = if q < size (leaf_paths (tshape sp)) then
      shrincs_fxmss_sign_x pp sp (leaf_sks pp ks sp) q
        (PRFmsg kp (posid (spath sp q)) m)
        (Hmsg (PRFmsg kp (posid (spath sp q)) m) pp (ffx_root pp ks (tshape sp))
           (posid (spath sp q)) m)
    else None.
Proof.
rewrite /shrincs_fxmss_sign /shrincs_fxmss_sign_x value_tree_xE.
case: ifP => // hq.
by rewrite /leaf_sks (nth_map [::]) //.
Qed.

(** The flexible verifier with the digest passed in (the games read
    it from the RO map): [shrincs_fxmss_verify] factors through it. *)
Definition shrincs_fxmss_verify_md (pp : PP) (rt : N) (zi : nat * nat) (md : D)
    (ws : seq N * nat) (ap : seq N) : bool :=
  [&& (zi.1 <= h_sf)%N,
      (zi.2 < 2 ^ (h_sf - zi.1))%N,
      fwots_checks pp zi md ws
    & val_ap (nhash pp) [::] (path_of_idx (h_sf - zi.1) zi.2) ap
        (frecover pp zi md ws) == Some rt].

Lemma shrincs_fxmss_verify_mdE (pp : PP) (rt : N) (m : M) (zi : nat * nat) (r : R)
    (ws : seq N * nat) (ap : seq N) :
  ffx_verify pp rt m ((zi, r), (ws, ap))
  = shrincs_fxmss_verify_md pp rt zi (Hmsg r pp rt zi m) ws ap.
Proof. by []. Qed.

(** Sanity (the sampled-keys analogue of [shrincs_fxmss_verify_sign]): a
    signature [shrincs_fxmss_sign_x] releases verifies under the sampled-keys
    root AT THE SAME DIGEST — the coherence of the G1f/G2f
    definitions (G0f's case is [shrincs_fxmss_sign_xE] + the scheme's
    [shrincs_fxmss_verify_sign]). *)
Lemma shrincs_fxmss_sign_x_verifies (pp : PP) (sp : seq bool) (xss : seq (seq N))
    (q : nat) (r : R) (md : D) (sg : shrincs_fxmss_signature N R) :
  q < size (leaf_paths (tshape sp)) ->
  size (nth [::] xss q) = l ->
  shrincs_fxmss_sign_x pp sp xss q r md = Some sg ->
  shrincs_fxmss_verify_md pp (shrincs_fxmss_root_x pp sp xss) sg.1.1 md sg.2.1 sg.2.2.
Proof.
move=> hq hxs.
rewrite /shrincs_fxmss_sign_x.
set p := spath sp q.
set zi := posid p.
case E1: (fsign_sig _ _ _ _) => [ws|] //=.
case E2: (cons_ap _ _ _ _) => [ap|] //= [<-] /=.
have hszp : size p <= h_sf := shrincs_fxmss_sign_path_size h_sf sp q hq.
have hsub : subtree_at (tshape sp) p = Some (BLeaf tt)
  := shrincs_fxmss_sign_path_leaf h_sf sp q hq.
have hpath : path_of_idx (h_sf - zi.1) zi.2 = p.
  by rewrite /zi /shrincs_fxmss_pos_id /= subKn // path_of_idx_of_path.
have hsubv : subtree_at (value_tree_x pp sp xss) p
             = Some (BLeaf (fpk_of (posid p) pp (nth [::] xss q))).
  rewrite /value_tree_x subtree_at_posmap hsub /=.
  by rewrite index_sign_path.
have hval := val_ap_correct E2 hsubv.
have hver := shrincs_fxmss_wots_verify_sign PP N D F Tl Hgrind S_wn c_max zi.1 zi.2
               pp (nth [::] xss q) md ws hxs E1.
rewrite (shrincs_fxmss_wots_verifyE PP N D F Tl Hgrind S_wn) in hver.
move/andP: hver => [hchecks /eqP hrec].
rewrite /shrincs_fxmss_verify_md; apply/and4P; split.
- by rewrite /zi /shrincs_fxmss_pos_id /= leq_subr.
- by rewrite /zi /shrincs_fxmss_pos_id /= subKn // idx_of_path_lt.
- exact: hchecks.
- apply/eqP; rewrite hpath hrec.
  exact: hval.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The n-fold per-anchor key sampler (G1f/G2f key generation) *)

Fixpoint sample_keys (n : nat) : raw_code (chList (chList N)) :=
  match n with
  | 0 => ret [::]
  | n'.+1 =>
      xs ← sample_seq dN l ;;
      xss ← sample_keys n' ;;
      ret (xs :: xss)
  end.

#[export] Instance sample_keys_valid (L : Locations) (I : Interface)
    (n : nat) :
  ValidCode L I (sample_keys n).
Proof.
elim: n => [|n IH] /=.
- apply valid_ret.
- eapply valid_bind; first exact: sample_seq_valid.
  move=> xs; eapply valid_bind; [exact: IH | move=> xss; apply valid_ret].
Qed.

(* ------------------------------------------------------------------ *)
(** ** M5 lift: adversary-chosen leaf-id validation + slot selection

    The lifted SIGN oracle takes an adversary-chosen leaf id
    [zi : nat * nat] alongside the message (security.tex F.0: sign
    queries are [(M_i, (z*_i, i*_i))]).  [leaf_okP sp zi] validates
    [zi] against the committed tree structure [sp] (non-matching ids
    are answered bot); [lidx sp zi] is the [leaf_paths]-schedule slot
    the oracle signs at for a validated id (this REPLACES the
    left-to-right [shrincs_fxmss_q_loc] counter — with the counter schedule the
    two coincided, [index_sign_path]).  The three [leafid_index_*]
    facts are the pure selection layer the lifted hops consume:
    roundtrip = the signed slot's anchor is [zi] (replaces
    [index_sign_path]); lt = slot in range; inj = pairwise-distinct
    ids pick pairwise-distinct slots (the used-set/one-time core that
    replaces the counter lockstep). *)

Definition leaf_okP (sp : seq bool) (zi : nat * nat) : bool :=
  [&& (zi.1 <= h_sf)%N, (zi.2 < 2 ^ (h_sf - zi.1))%N
    & (path_of_idx (h_sf - zi.1) zi.2 \in leaf_paths (tshape sp))].

Definition lidx (sp : seq bool) (zi : nat * nat) : nat :=
  index (path_of_idx (h_sf - zi.1) zi.2) (leaf_paths (tshape sp)).

Lemma leafid_index_roundtrip (sp : seq bool) (zi : nat * nat) :
  leaf_okP sp zi -> posid (spath sp (lidx sp zi)) = zi.
Proof.
case/and3P => h1 h2 hin.
rewrite /shrincs_fxmss_sign_path /lidx nth_index //.
rewrite /shrincs_fxmss_pos_id size_path_of_idx idx_of_path_of_idx // subKn //.
by case: (zi).
Qed.

Lemma leafid_index_lt (sp : seq bool) (zi : nat * nat) :
  leaf_okP sp zi -> (lidx sp zi < size (leaf_paths (tshape sp)))%N.
Proof. by case/and3P => _ _ hin; rewrite /lidx index_mem. Qed.

Lemma leafid_index_inj (sp : seq bool) (zi zi' : nat * nat) :
  leaf_okP sp zi -> leaf_okP sp zi' -> lidx sp zi = lidx sp zi' -> zi = zi'.
Proof.
move=> h h' he.
by rewrite -(leafid_index_roundtrip sp zi h)
           -(leafid_index_roundtrip sp zi' h') he.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Interface and locations *)

Definition FXGEN : nat := 100.
Definition FXSIGN : nat := 101.
Definition FXFORGE : nat := 102.
Definition FXHASH : nat := 103.

(** The signature carrier (= [Sig shrincs_fxmss_scheme]) and the Hmsg^sf RO domain:
    prefix = randomness R, suffix = (pk, (leaf id, message)) — the
    full Hmsg^sf input split for the later reprogramming hop. *)
Definition shrincs_fxmss_game_signature : choice_type :=
  (('nat × 'nat) × R) × ((('list N) × 'nat) × ('list N)).

Definition shrincs_fxmss_random_oracle_input : choice_type := R × ((PP × N) × (('nat × 'nat) × M)).

(** The lifted interface: FXSIGN takes the adversary-chosen leaf id
    [(M × ('nat × 'nat))].  [I_G0f → I_G0fL] — every downstream hop
    file re-types against it. *)
Definition I_G0fL :=
  [interface
    [ FXGEN ] : { 'list 'bool ~> PP × N } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option shrincs_fxmss_game_signature } ;
    [ FXHASH ] : { shrincs_fxmss_random_oracle_input ~> D } ;
    [ FXFORGE ] : { M × shrincs_fxmss_game_signature ~> 'bool }
  ].

(** The static-state carrier: ((pp, PKsf), (sp, xss)). *)
Definition shrincs_fxmss_game_state : choice_type :=
  (PP × N) × (('list 'bool) × ('list ('list N))).

Definition shrincs_fxmss_st_loc := mkloc 400 (None : option shrincs_fxmss_game_state).
Definition shrincs_fxmss_kp_loc := mkloc 401 (None : option Kp).
Definition shrincs_fxmss_scnt_loc := mkloc 403 (0 : 'nat).
Definition shrincs_fxmss_log_loc := mkloc 404 ([::] : seq M).
Definition shrincs_fxmss_rom_loc := mkloc 405 (emptym : chMap shrincs_fxmss_random_oracle_input D).
Definition shrincs_fxmss_hcnt_loc := mkloc 406 (0 : 'nat).
Definition shrincs_fxmss_rt_loc := mkloc 407 (emptym : chMap (('nat × 'nat) × M) R).
Definition shrincs_fxmss_fcnt_loc := mkloc 408 (0 : 'nat).

(** M5 NEW (410): the used-leaf-id set — records the leaf ids already
    queried so SIGN can refuse re-used ids (tex F.0 "all queried leaf
    identifiers are pairwise distinct").  REPLACES the [shrincs_fxmss_q_loc]
    counter (402), which the lift deletes (the counter schedule is
    gone; the signing slot is [lidx st.2.1 zi] instead). *)
Definition shrincs_fxmss_used_loc := mkloc 410 (emptym : chMap ('nat × 'nat) 'unit).

(** The two lifted location sets: G0f/G1f share [G01Locs] (they carry
    the PRFmsg key [shrincs_fxmss_kp_loc]); G2f uses [G2Locs] (PRFmsg is a table
    [shrincs_fxmss_rt_loc], no key). *)
Definition G01Locs : Locations :=
  [fmap shrincs_fxmss_st_loc ; shrincs_fxmss_kp_loc ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ;
        shrincs_fxmss_log_loc ; shrincs_fxmss_rom_loc ; shrincs_fxmss_hcnt_loc ; shrincs_fxmss_fcnt_loc ].
Definition G2Locs : Locations :=
  [fmap shrincs_fxmss_st_loc ; shrincs_fxmss_used_loc ; shrincs_fxmss_scnt_loc ; shrincs_fxmss_log_loc ;
        shrincs_fxmss_rom_loc ; shrincs_fxmss_hcnt_loc ; shrincs_fxmss_rt_loc ; shrincs_fxmss_fcnt_loc ].

(* ------------------------------------------------------------------ *)
(** ** Lifted oracle bodies (M5)

    Factored into named definitions with hand-proved [ValidCode]
    instances so the three games are assembled by the DIRECTED
    [valid_package_cons] idiom: the plain [package] typeclass search on
    a used-set/lifted-SIGN body is a >30-min / 50GB wall
    (M5_LIFT_DESIGN.md §5, LateGames row; peel FORGE->HASH->SIGN->GEN).

    HASH and FORGE are identical across G0f/G1f/G2f (they never touch
    the leaf schedule); [sign01f_body] is shared by G0f/G1f (digest
    still lazy-rom, PRFmsg keyed by the adversary id [mz.2]); G2f has
    its own [sign2f_body] (randomness from the [shrincs_fxmss_rt_loc] table).  The
    digest stays LAZY-ROM here — the per-leaf presample [sd] enters
    later, at the digest hop. *)

Definition shrincs_fxmss_hash_body (x : shrincs_fxmss_random_oracle_input) : raw_code D :=
  (hc ← get shrincs_fxmss_hcnt_loc ;;
   #assert (hc < q_h)%N ;;
   mp ← get shrincs_fxmss_rom_loc ;;
   md ← (match getm mp x with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put shrincs_fxmss_rom_loc := setm mp x md ;;
   #put shrincs_fxmss_hcnt_loc := hc.+1 ;;
   ret md).

Definition shrincs_fxmss_forge_body (b : bool) (m : M) (sg : shrincs_fxmss_game_signature) : raw_code 'bool :=
  (fc ← get shrincs_fxmss_fcnt_loc ;;
   #assert (fc < q_f)%N ;;
   st ← getSome shrincs_fxmss_st_loc ;;
   lg ← get shrincs_fxmss_log_loc ;;
   mp ← get shrincs_fxmss_rom_loc ;;
   md ← (match getm mp (sg.1.2, (st.1, (sg.1.1, m))) with
         | Some d => ret d
         | None => d ← dD ;; ret d
         end) ;;
   #put shrincs_fxmss_rom_loc := setm mp (sg.1.2, (st.1, (sg.1.1, m))) md ;;
   #put shrincs_fxmss_fcnt_loc := fc.+1 ;;
   ret (if b then
          shrincs_fxmss_verify_md st.1.1 st.1.2 sg.1.1 md sg.2.1 sg.2.2
          && (m \notin lg)
        else false)).

(** The lifted G0f/G1f SIGN body: takes [mz : M × ('nat × 'nat)],
    validates the id ([leaf_okP]) and refuses re-used ids
    ([mz.2 \notin domm us]), records the used id, keys PRFmsg / the RO
    map on [mz.2] directly, signs at slot [lidx st.2.1 mz.2].  The
    [sc < q_s] budget is kept; refusals burn budget. *)
Definition sign01f_body (mz : M × ('nat × 'nat)) :
    raw_code ('option shrincs_fxmss_game_signature) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome shrincs_fxmss_st_loc ;;
   kp ← getSome shrincs_fxmss_kp_loc ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get shrincs_fxmss_log_loc ;;
   mp ← get shrincs_fxmss_rom_loc ;;
   if [&& leaf_okP st.2.1 mz.2 & mz.2 \notin domm us] then
     md ← (match getm mp (PRFmsg kp mz.2 mz.1, (st.1, (mz.2, mz.1))) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
     #put shrincs_fxmss_rom_loc :=
       setm mp (PRFmsg kp mz.2 mz.1, (st.1, (mz.2, mz.1))) md ;;
     match shrincs_fxmss_sign_x st.1.1 st.2.1 st.2.2 (lidx st.2.1 mz.2)
             (PRFmsg kp mz.2 mz.1) md with
     | Some sg =>
         #put shrincs_fxmss_log_loc := rcons lg mz.1 ;;
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret (Some sg)
     | None =>
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

Definition gen0f_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get shrincs_fxmss_st_loc ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   ks ← dKs ;;
   kp ← dKp ;;
   #put shrincs_fxmss_kp_loc := Some kp ;;
   #put shrincs_fxmss_st_loc :=
     Some ((pp, shrincs_fxmss_root_x pp sp (leaf_sks pp ks sp)),
           (sp, leaf_sks pp ks sp)) ;;
   ret (pp, shrincs_fxmss_root_x pp sp (leaf_sks pp ks sp))).

(** Validity (hand-proved; [ssprove_valid] chokes on the sampler /
    getSome forms).  HASH/FORGE are validated over BOTH location sets. *)
#[export] Instance shrincs_fxmss_hash_body_valid01 (I : Interface) (x : shrincs_fxmss_random_oracle_input) :
  ValidCode G01Locs I (shrincs_fxmss_hash_body x).
Proof.
rewrite /shrincs_fxmss_hash_body.
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

#[export] Instance shrincs_fxmss_hash_body_valid2 (I : Interface) (x : shrincs_fxmss_random_oracle_input) :
  ValidCode G2Locs I (shrincs_fxmss_hash_body x).
Proof.
rewrite /shrincs_fxmss_hash_body.
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

#[export] Instance shrincs_fxmss_forge_body_valid01 (I : Interface) (b : bool)
    (m : M) (sg : shrincs_fxmss_game_signature) :
  ValidCode G01Locs I (shrincs_fxmss_forge_body b m sg).
Proof.
rewrite /shrincs_fxmss_forge_body.
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

#[export] Instance shrincs_fxmss_forge_body_valid2 (I : Interface) (b : bool)
    (m : M) (sg : shrincs_fxmss_game_signature) :
  ValidCode G2Locs I (shrincs_fxmss_forge_body b m sg).
Proof.
rewrite /shrincs_fxmss_forge_body.
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

#[export] Instance sign01f_body_valid (I : Interface)
    (mz : M × ('nat × 'nat)) :
  ValidCode G01Locs I (sign01f_body mz).
Proof.
rewrite /sign01f_body.
eapply valid_getr; first by fmap_solve. move=> sc.
eapply valid_assertD => _.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => hSt.
eapply valid_getr; first by fmap_solve. move=> kpo.
eapply valid_assertD => hKp.
eapply valid_getr; first by fmap_solve. move=> us.
eapply valid_getr; first by fmap_solve. move=> lg.
eapply valid_getr; first by fmap_solve. move=> mp.
case: ifP => _; last first.
  eapply valid_putr; first by fmap_solve. apply valid_ret.
eapply valid_bind.
  case: (getm mp _) => [d|]; first by apply valid_ret.
  by eapply valid_bind; first eapply valid_scheme, prog_valid;
     move=> d; apply valid_ret.
move=> md.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
case: (shrincs_fxmss_sign_x _ _ _ _ _ _) => [sg|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  apply valid_ret.
- eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

#[export] Instance gen0f_body_valid (I : Interface) (sp : 'list 'bool) :
  ValidCode G01Locs I (gen0f_body sp).
Proof.
rewrite /gen0f_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> ks.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> kp.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

(* ------------------------------------------------------------------ *)
(** ** G0f: the flat ROM EU-CMA game pair (DIRECTED assembly) *)

Definition G0f (b : bool) : game I_G0fL.
Proof.
notypeclasses refine [package G01Locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen0f_body sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option shrincs_fxmss_game_signature } (mz) {
      sign01f_body mz
    } ;
    [ FXHASH ] : { shrincs_fxmss_random_oracle_input ~> D } (x) {
      shrincs_fxmss_hash_body x
    } ;
    [ FXFORGE ] : { M × shrincs_fxmss_game_signature ~> 'bool } '(m, sg) {
      shrincs_fxmss_forge_body b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: shrincs_fxmss_forge_body_valid01. } }
    { intros x; exact: shrincs_fxmss_hash_body_valid01. } }
  { intro mz; exact: sign01f_body_valid. } }
{ intro sp; exact: gen0f_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** G1f: after the PRF_f swap (hop 1)

    Same locations and same SIGN/HASH/FORGE bodies as G0f; only GEN
    differs: the per-anchor keys are sampled ([sample_keys]) and the
    PRF_f key slot degenerates to the dead [_ ← dN] (header). *)

Definition gen1f_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get shrincs_fxmss_st_loc ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   kp ← dKp ;;
   xss ← sample_keys (size (leaf_paths (tshape sp))) ;;
   #put shrincs_fxmss_kp_loc := Some kp ;;
   #put shrincs_fxmss_st_loc := Some ((pp, shrincs_fxmss_root_x pp sp xss), (sp, xss)) ;;
   ret (pp, shrincs_fxmss_root_x pp sp xss)).

#[export] Instance gen1f_body_valid (I : Interface) (sp : 'list 'bool) :
  ValidCode G01Locs I (gen1f_body sp).
Proof.
rewrite /gen1f_body.
eapply valid_getr; first by fmap_solve. move=> sto.
eapply valid_assertD => _.
eapply valid_assertD => _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> pp.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> _.
eapply valid_bind; first by eapply valid_scheme, prog_valid. move=> kp.
eapply valid_bind; first by apply sample_keys_valid. move=> xss.
eapply valid_putr; first by fmap_solve.
eapply valid_putr; first by fmap_solve.
apply valid_ret.
Qed.

Definition G1f (b : bool) : game I_G0fL.
Proof.
notypeclasses refine [package G01Locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen1f_body sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option shrincs_fxmss_game_signature } (mz) {
      sign01f_body mz
    } ;
    [ FXHASH ] : { shrincs_fxmss_random_oracle_input ~> D } (x) {
      shrincs_fxmss_hash_body x
    } ;
    [ FXFORGE ] : { M × shrincs_fxmss_game_signature ~> 'bool } '(m, sg) {
      shrincs_fxmss_forge_body b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: shrincs_fxmss_forge_body_valid01. } }
    { intros x; exact: shrincs_fxmss_hash_body_valid01. } }
  { intro mz; exact: sign01f_body_valid. } }
{ intro sp; exact: gen1f_body_valid. }
Defined.

(* ------------------------------------------------------------------ *)
(** ** G2f: after the PRFmsg swap (hop 2)

    The signature randomness comes from the lazy table [shrincs_fxmss_rt_loc]
    at the pairwise-reused key (leaf id, message): a REFUSED query
    re-asked with the same message deterministically reproduces the
    same refusal (table semantics; the proof architecture hop 2 discussion —
    the bridge to per-query-fresh randomness is the reprogramming
    hop's business).  [shrincs_fxmss_kp_loc] is gone; GEN carries the two dead
    samples (header). *)

Definition gen2f_body (sp : 'list 'bool) : raw_code (PP × N) :=
  (sto ← get shrincs_fxmss_st_loc ;;
   #assert ~~ (isSome sto) ;;
   #assert (size (leaf_paths (tshape sp)) <= n_max)%N ;;
   pp ← dPP ;;
   _ ← dN ;;
   _ ← dR ;;
   xss ← sample_keys (size (leaf_paths (tshape sp))) ;;
   #put shrincs_fxmss_st_loc := Some ((pp, shrincs_fxmss_root_x pp sp xss), (sp, xss)) ;;
   ret (pp, shrincs_fxmss_root_x pp sp xss)).

(** The lifted G2f SIGN body: as [sign01f_body] but the signature
    randomness [r] comes from the [shrincs_fxmss_rt_loc] table at the key
    [(mz.2, mz.1)] (the adversary id, message), and the RO map key is
    [(r, (st.1, (mz.2, mz.1)))]. *)
Definition sign2f_body (mz : M × ('nat × 'nat)) :
    raw_code ('option shrincs_fxmss_game_signature) :=
  (sc ← get shrincs_fxmss_scnt_loc ;;
   #assert (sc < q_s)%N ;;
   st ← getSome shrincs_fxmss_st_loc ;;
   us ← get shrincs_fxmss_used_loc ;;
   lg ← get shrincs_fxmss_log_loc ;;
   mp ← get shrincs_fxmss_rom_loc ;;
   tb ← get shrincs_fxmss_rt_loc ;;
   if [&& leaf_okP st.2.1 mz.2 & mz.2 \notin domm us] then
     r ← (match getm tb (mz.2, mz.1) with
          | Some r => ret r
          | None => r ← dR ;; ret r
          end) ;;
     #put shrincs_fxmss_used_loc := setm us mz.2 Datatypes.tt ;;
     #put shrincs_fxmss_rt_loc := setm tb (mz.2, mz.1) r ;;
     md ← (match getm mp (r, (st.1, (mz.2, mz.1))) with
           | Some d => ret d
           | None => d ← dD ;; ret d
           end) ;;
     #put shrincs_fxmss_rom_loc := setm mp (r, (st.1, (mz.2, mz.1))) md ;;
     match shrincs_fxmss_sign_x st.1.1 st.2.1 st.2.2 (lidx st.2.1 mz.2) r md with
     | Some sg =>
         #put shrincs_fxmss_log_loc := rcons lg mz.1 ;;
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret (Some sg)
     | None =>
         #put shrincs_fxmss_scnt_loc := sc.+1 ;;
         ret None
     end
   else
     #put shrincs_fxmss_scnt_loc := sc.+1 ;;
     ret None).

#[export] Instance gen2f_body_valid (I : Interface) (sp : 'list 'bool) :
  ValidCode G2Locs I (gen2f_body sp).
Proof.
rewrite /gen2f_body.
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

#[export] Instance sign2f_body_valid (I : Interface)
    (mz : M × ('nat × 'nat)) :
  ValidCode G2Locs I (sign2f_body mz).
Proof.
rewrite /sign2f_body.
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
case: (shrincs_fxmss_sign_x _ _ _ _ _ _) => [sg|].
- eapply valid_putr; first by fmap_solve.
  eapply valid_putr; first by fmap_solve.
  apply valid_ret.
- eapply valid_putr; first by fmap_solve. apply valid_ret.
Qed.

Definition G2f (b : bool) : game I_G0fL.
Proof.
notypeclasses refine [package G2Locs ;
    [ FXGEN ] : { 'list 'bool ~> PP × N } (sp) {
      gen2f_body sp
    } ;
    [ FXSIGN ] : { M × ('nat × 'nat) ~> 'option shrincs_fxmss_game_signature } (mz) {
      sign2f_body mz
    } ;
    [ FXHASH ] : { shrincs_fxmss_random_oracle_input ~> D } (x) {
      shrincs_fxmss_hash_body x
    } ;
    [ FXFORGE ] : { M × shrincs_fxmss_game_signature ~> 'bool } '(m, sg) {
      shrincs_fxmss_forge_body b m sg
    }
  ].
eapply valid_package_cons.
{ eapply valid_package_cons.
  { eapply valid_package_cons.
    { eapply valid_package_cons.
      { apply: valid_empty_package. }
      { intros [m sg]; exact: shrincs_fxmss_forge_body_valid2. } }
    { intros x; exact: shrincs_fxmss_hash_body_valid2. } }
  { intro mz; exact: sign2f_body_valid. } }
{ intro sp; exact: gen2f_body_valid. }
Defined.

End FXMSSGames.
