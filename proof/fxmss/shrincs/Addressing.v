(** * SHRINCS.Addressing

    The STATEFUL address space ADRS_sf of SHRINCS as a structured Coq
    type, with the injectivity/disjointness lemmas that discharge the
    distinct-tweaks side conditions of the SM-* games, and an encoding
    into a [choice_type] for use as a thf tweak space ([th_T]).

    Counterpart: construction.tex, "Addressing scheme" (sec:adressing),
    stateful layout sec:adressing-stateful (fig:adrs-sf), per-type
    figures (fig:wots-grind-sf-adrs .. fig:wots-prf-sf-adrs) and the
    type-tag table (tab:address-types).

    The stateful path uses a fixed 36-byte address layout
    (fig:adrs-sf), in field order:

      | node height | node index | type   | chain index | hash index |
      |   1 byte    |  32 bytes  | 1 byte |   1 byte    |   1 byte   |

    with the five stateful type tags (tab:address-types; tags 0-7 are
    the stateless side and tag ranges are disjoint between paths):

      type  8  WOTSGRINDSF   WOTS+C digest grinding     (fig:wots-grind-sf-adrs)
      type  9  TREESTATEFUL  stateful Merkle tree node  (fig:tree-stateful-adrs)
      type 10  WOTSHASHSF    WOTS+C chain hashing       (fig:wots-hash-sf-adrs)
      type 11  WOTSPKSF      WOTS+C pk compression      (fig:wots-pk-sf-adrs)
      type 12  WOTSPRFSF     WOTS+C secret derivation   (fig:wots-prf-sf-adrs)

    Field discipline transcribed from the figures (fields not listed
    are zero on a type change, exactly as on the stateless side):

      type  8: height/index = WOTS+C anchor (z_star, i_star); chain = hash = 0
      type  9: height/index = tree node (z, i);       chain = hash = 0
      type 10: height/index = anchor (z_star, i_star); chain = chain index;
               hash = position within the chain
      type 11: height/index = anchor (z_star, i_star); chain = hash = 0
      type 12: height/index = anchor (z_star, i_star); chain = chain index;
               hash = 0

    MODELING CHOICES (documented deviations):
    - Fields are unbounded [nat] rather than 1-/32-byte words: byte
      widths only matter for the byte serialization (out of scope, as
      is the SHA-256 instantiation); the proofs consume exactly
      injectivity and pairwise disjointness, which hold a fortiori on
      the [nat] model.  (The tex bounds: z <= 255, i < 2^(h_sf - z),
      chain index < l, hash index <= 255.)
    - One constructor per stateful type tag, so the tex's "set type to
      X and zero the unused fields" discipline on a mutable 36-byte
      buffer becomes constructor application; the zero-initialization
      of unused fields reappears verbatim in [encode_adrs].
    - The stateless 32-byte layout (types 0-7) is NOT modeled here: it
      lives on the SPX side (P7) and shares no tweak space with the
      stateful path (disjoint type tags plus distinct PKseed padding,
      construction.tex sec:adressing). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From HB Require Import structures.
From HBS Require Import Prelude.
Set Warnings "notation-overridden,ambiguous-paths".

Import PackageNotation.
#[local] Open Scope package_scope.

(* ------------------------------------------------------------------ *)
(** ** Type tags (construction.tex tab:address-types, stateful rows) *)

Definition TY_WOTS_GRIND_SF : nat := 8.   (* tex: \WOTSGRINDSF  *)
Definition TY_TREE_SF       : nat := 9.   (* tex: \TREESTATEFUL *)
Definition TY_WOTS_HASH_SF  : nat := 10.  (* tex: \WOTSHASHSF   *)
Definition TY_WOTS_PK_SF    : nat := 11.  (* tex: \WOTSPKSF     *)
Definition TY_WOTS_PRF_SF   : nat := 12.  (* tex: \WOTSPRFSF    *)

(* ------------------------------------------------------------------ *)
(** ** The stateful address type

    One constructor per stateful type tag; constructor arguments are
    exactly the active (non-zero) fields of the corresponding figure,
    in layout order. *)

Inductive adrs_sf : Type :=
  | AdrGrind of nat & nat
    (** [AdrGrind z_star i_star]: type 8 (WOTSGRINDSF), digest grinding for
        the WOTS+C instance anchored at (z_star, i_star). *)
  | AdrTree of nat & nat
    (** [AdrTree z i]: type 9 (TREESTATEFUL), internal node (z, i) of
        the imaginary balanced Merkle tree, z in {1..h_sf}. *)
  | AdrChain of nat & nat & nat & nat
    (** [AdrChain z_star i_star chain pos]: type 10 (WOTSHASHSF), hash at
        position [pos] of chain [chain] of the instance at (z_star, i_star). *)
  | AdrPk of nat & nat
    (** [AdrPk z_star i_star]: type 11 (WOTSPKSF), pk compression of the
        instance at (z_star, i_star). *)
  | AdrPrf of nat & nat & nat
    (** [AdrPrf z_star i_star chain]: type 12 (WOTSPRFSF), secret derivation
        for chain [chain] of the instance at (z_star, i_star). *).

(* ------------------------------------------------------------------ *)
(** ** Field projections (the five 36-byte-layout fields) *)

Definition adrs_type (a : adrs_sf) : nat :=
  match a with
  | AdrGrind _ _     => TY_WOTS_GRIND_SF
  | AdrTree _ _      => TY_TREE_SF
  | AdrChain _ _ _ _ => TY_WOTS_HASH_SF
  | AdrPk _ _        => TY_WOTS_PK_SF
  | AdrPrf _ _ _     => TY_WOTS_PRF_SF
  end.

Definition adrs_height (a : adrs_sf) : nat :=
  match a with
  | AdrGrind z _ | AdrTree z _ | AdrChain z _ _ _ | AdrPk z _ | AdrPrf z _ _ => z
  end.

Definition adrs_index (a : adrs_sf) : nat :=
  match a with
  | AdrGrind _ i | AdrTree _ i | AdrChain _ i _ _ | AdrPk _ i | AdrPrf _ i _ => i
  end.

Definition adrs_chain (a : adrs_sf) : nat :=
  match a with
  | AdrChain _ _ c _ | AdrPrf _ _ c => c
  | _ => 0
  end.

Definition adrs_hash (a : adrs_sf) : nat :=
  match a with
  | AdrChain _ _ _ p => p
  | _ => 0
  end.

(** The key-pair / leaf identifier (node height, node index): for the
    WOTS+C types it is the anchor (z_star, i_star); for tree addresses the
    node position. *)
Definition adrs_keypair (a : adrs_sf) : nat * nat :=
  (adrs_height a, adrs_index a).

(** Sanity: the tags really are the stateful range 8..12 of
    tab:address-types. *)
Lemma adrs_type_range a :
  (TY_WOTS_GRIND_SF <= adrs_type a) && (adrs_type a <= TY_WOTS_PRF_SF).
Proof. by case: a. Qed.

(* ------------------------------------------------------------------ *)
(** ** Smart constructors mirroring the tex's field discipline

    wotsc.tex derives, from a global ADRS anchored at the key pair
    (z_star, i_star), the sibling addresses of one WOTS+C instance by "set
    type to X, set chain/hash fields, zero the rest".  Structured
    counterpart: each setter takes the anchor and the active fields. *)

Definition wotsc_grind_adrs (t : nat * nat) : adrs_sf :=
  AdrGrind t.1 t.2.

Definition wotsc_chain_adrs (t : nat * nat) (i pos : nat) : adrs_sf :=
  AdrChain t.1 t.2 i pos.

Definition wotsc_pk_adrs (t : nat * nat) : adrs_sf :=
  AdrPk t.1 t.2.

Definition wotsc_prf_adrs (t : nat * nat) (i : nat) : adrs_sf :=
  AdrPrf t.1 t.2 i.

Definition tree_node_adrs (z i : nat) : adrs_sf :=
  AdrTree z i.

(* ------------------------------------------------------------------ *)
(** ** Decidable equality (BinTree.eq_bt pattern) *)

Definition eq_adrs (a b : adrs_sf) : bool :=
  match a, b with
  | AdrGrind z i, AdrGrind z' i' => (z == z') && (i == i')
  | AdrTree z i, AdrTree z' i' => (z == z') && (i == i')
  | AdrChain z i c p, AdrChain z' i' c' p' =>
      [&& z == z', i == i', c == c' & p == p']
  | AdrPk z i, AdrPk z' i' => (z == z') && (i == i')
  | AdrPrf z i c, AdrPrf z' i' c' => [&& z == z', i == i' & c == c']
  | _, _ => false
  end.

Lemma eq_adrsP : Equality.axiom eq_adrs.
Proof.
case=> [z i|z i|z i c p|z i|z i c] [z' i'|z' i'|z' i' c' p'|z' i'|z' i' c'] /=;
  try by constructor.
- by apply: (iffP andP) => [[/eqP-> /eqP->]|[-> ->]] //; split; apply/eqP.
- by apply: (iffP andP) => [[/eqP-> /eqP->]|[-> ->]] //; split; apply/eqP.
- by apply: (iffP and4P) => [[/eqP-> /eqP-> /eqP-> /eqP->]|[-> -> -> ->]] //;
    split; apply/eqP.
- by apply: (iffP andP) => [[/eqP-> /eqP->]|[-> ->]] //; split; apply/eqP.
- by apply: (iffP and3P) => [[/eqP-> /eqP-> /eqP->]|[-> -> ->]] //;
    split; apply/eqP.
Qed.

HB.instance Definition _ := hasDecEq.Build adrs_sf eq_adrsP.

(* ------------------------------------------------------------------ *)
(** ** Injectivity (per constructor)

    These (together with the disjointness lemmas below) discharge the
    distinct-tweaks side conditions of the SM-TCR / SM-PRE / SM-UD
    games: two hash calls of the scheme collide on their tweak only if
    they are the same call. *)

Lemma AdrGrind_inj z i z' i' :
  AdrGrind z i = AdrGrind z' i' -> z = z' /\ i = i'.
Proof. by case=> -> ->. Qed.

Lemma AdrTree_inj z i z' i' :
  AdrTree z i = AdrTree z' i' -> z = z' /\ i = i'.
Proof. by case=> -> ->. Qed.

(** Chain-address injectivity in (leaf identifier, chain, position). *)
Lemma AdrChain_inj z i c p z' i' c' p' :
  AdrChain z i c p = AdrChain z' i' c' p' ->
  [/\ z = z', i = i', c = c' & p = p'].
Proof. by case=> -> -> -> ->. Qed.

Lemma AdrPk_inj z i z' i' :
  AdrPk z i = AdrPk z' i' -> z = z' /\ i = i'.
Proof. by case=> -> ->. Qed.

Lemma AdrPrf_inj z i c z' i' c' :
  AdrPrf z i c = AdrPrf z' i' c' -> [/\ z = z', i = i' & c = c'].
Proof. by case=> -> -> ->. Qed.

(* ------------------------------------------------------------------ *)
(** ** Pairwise disjointness of the five classes

    Distinct type tags are distinct tweaks regardless of the field
    values (tab:address-types: the type byte alone determines the
    class). *)

Lemma adrs_grind_neq_tree z i z' i' : AdrGrind z i <> AdrTree z' i'.
Proof. by []. Qed.

Lemma adrs_grind_neq_chain z i z' i' c p : AdrGrind z i <> AdrChain z' i' c p.
Proof. by []. Qed.

Lemma adrs_grind_neq_pk z i z' i' : AdrGrind z i <> AdrPk z' i'.
Proof. by []. Qed.

Lemma adrs_grind_neq_prf z i z' i' c : AdrGrind z i <> AdrPrf z' i' c.
Proof. by []. Qed.

Lemma adrs_tree_neq_chain z i z' i' c p : AdrTree z i <> AdrChain z' i' c p.
Proof. by []. Qed.

Lemma adrs_tree_neq_pk z i z' i' : AdrTree z i <> AdrPk z' i'.
Proof. by []. Qed.

Lemma adrs_tree_neq_prf z i z' i' c : AdrTree z i <> AdrPrf z' i' c.
Proof. by []. Qed.

Lemma adrs_chain_neq_pk z i c p z' i' : AdrChain z i c p <> AdrPk z' i'.
Proof. by []. Qed.

Lemma adrs_chain_neq_prf z i c p z' i' c' : AdrChain z i c p <> AdrPrf z' i' c'.
Proof. by []. Qed.

Lemma adrs_pk_neq_prf z i z' i' c : AdrPk z i <> AdrPrf z' i' c.
Proof. by []. Qed.

(* ------------------------------------------------------------------ *)
(** ** Encoding into a [choice_type] (the thf tweak space)

    [thf]'s [th_T] must be a [choice_type] (HBS.Games.THF), and
    [adrs_sf] is a bare inductive; we therefore fix the 'nat-tuple
    representation below and a proven-injective encoder.  The tuple
    mirrors fig:adrs-sf in field order

        (node height, (node index, (type, (chain index, hash index))))

    and [encode_adrs] is literally the figure's field assignment: the
    projections of the structured address, with unused fields zero
    (the tex's zero-initialization on type change).  [decode_adrs]
    dispatches on the type tag; it does not validate that the fields
    the figures set to zero are zero (non-canonical tuples decode to
    the address ignoring them), which is harmless: only the
    cancellation [encode_adrsK] — hence injectivity of the encoder on
    the canonical image — is consumed. *)

Definition adrs_sf_ch : choice_type :=
  'nat × ('nat × ('nat × ('nat × 'nat))).

Definition encode_adrs (a : adrs_sf) : adrs_sf_ch :=
  (adrs_height a, (adrs_index a, (adrs_type a, (adrs_chain a, adrs_hash a)))).

Definition decode_adrs (x : adrs_sf_ch) : option adrs_sf :=
  let: (z, (i, (t, (c, p)))) := x in
  if t == TY_WOTS_GRIND_SF then Some (AdrGrind z i)
  else if t == TY_TREE_SF then Some (AdrTree z i)
  else if t == TY_WOTS_HASH_SF then Some (AdrChain z i c p)
  else if t == TY_WOTS_PK_SF then Some (AdrPk z i)
  else if t == TY_WOTS_PRF_SF then Some (AdrPrf z i c)
  else None.

Lemma encode_adrsK : pcancel encode_adrs decode_adrs.
Proof. by case. Qed.

Lemma encode_adrs_inj : injective encode_adrs.
Proof. exact: pcan_inj encode_adrsK. Qed.
