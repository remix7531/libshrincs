# Proof Style Guide

This guide covers the public specifications and both internal backends.
`spec.v` transcribes the reference, `sha256.v` defines SHA, `contracts.v`
owns public C contracts and `games.v` owns the security experiments.
`theorem.v` composes completed proofs. Use short specification comments to
explain the role of each definition group, game behavior, constraints and
invariants. Reading guidance belongs in `README.md`.

The backend style sections use `Model` for shared Gallina proofs under
`internal/common/`, `Sec` for SSProve under `internal/ssprove/`, and `Vst`
for VST under `internal/vst/`. The audit files follow the same conventions.

## Repo-wide file & directory naming

Every directory and file under `proof/` is `snake_case`
(`support/contract/buffer.v`, `wots/hop/chain_tcr.v`,
`lib/chain/core.v`, `internal/common/bytes.v`). There is one logical root, `Shrincs`,
declared once as the theory `Shrincs` in `proof/dune` (no nested theory
anywhere). A qualified backend name starts with
`Shrincs.internal`, such as `Shrincs.internal.ssprove.wots.hop` or
`Shrincs.internal.vst.support.contract.gprog`.

A file's *name* should describe its *content* (the concept(s) it bundles),
not merely the one function it happens to serve, unless it genuinely IS a
function-specific lemma bundle — in which case say so in the file header.

## Casing (CompCert / Rocq-stdlib style)

Casing of *terms* (as opposed to file/directory names, see above) follows
the CompCert / Rocq-stdlib convention in the `Vst` tree and the MathComp
convention in the `Sec` tree — this guide keeps calling them `Vst` and
`Sec` for short (see "Repo-wide file & directory naming" above):

| category                         | casing                  | examples                          |
|----------------------------------|-------------------------|-----------------------------------|
| the one logical root              | `CamelCase`             | `Shrincs`                          |
| type / record / inductive names  | `lowercase` snake_case  | `adrs`, `sig_scheme`, `byte`      |
| inductive constructors           | `CamelCase`             | `Vint`-style                      |
| record builders                  | lowercase `mk*`         | `mkint`, `mk` (as CompCert does)  |
| definitions / functions / lemmas | `lowercase` snake_case  | `to_byte`, `set_payload_a`        |

Documented exceptions (deliberate, not drift):

- **Crypto / paper notation** keeps the paper's spelling: `PP`, `N`, `M`, `F`,
  `T_sf`, the `dN`/`dPP`/`dM`/`dK` samplers, the `th_*`/`kh_*` hash
  evaluators, and the game/reduction zoo (`G0w`, `Fw`, `RC`, `*_loc`, ...). These
  mirror the security paper, the way CompCert keeps `Vint`.
- **C-macro mirrors** keep the C `#define` spelling in ALL_CAPS: the address
  type/layer tags `SF_SHRINCS_WOTS_*`, `SL_*`, so the proof reads against the C.
- **External names embedded in an identifier** keep their source casing: a lemma
  about the `Vint` constructor or a `Tarray` is `..._Vint` / `..._Tarray`; a
  MathComp view is `andP` / `eqP`. Do not snake_case a name you do not own.
- **VST-mandated names** `Vprog` / `Gprog` stay as VST requires them.

## Cross-tree naming convention

The goal is **uniformity and predict-the-statement-from-the-name**, favouring
longer descriptive names over abbreviations. A reader should be able to guess
a lemma's statement from its name, and find the same concept under the same
name in all three trees.

### Scheme prefix

- Every WOTS+C-specific top-level definition and lemma carries the
  `shrincs_wots_` prefix (already established: `shrincs_wots_chain_adrs`,
  `shrincs_wots_chain_iter`, `shrincs_wots_derive_sk`, `shrincs_wots_pk_adrs`,
  `shrincs_wots_hash_adrs`, `shrincs_wots_prf_adrs`, ...). The scheme record is
  `shrincs_wots_scheme`.
- Generic, scheme-agnostic machinery (the hash-based-signature library slice in
  `Shrincs.internal.ssprove.lib.*`, pure mathematics, the machine integers) does NOT
  take the prefix — it is reusable across the SHRINCS family, so it stays named
  by what it is (`chain_cat`, `Word.repr`, `digits_w`), not by WOTS+C.

### Lemma-name suffixes (uniform across trees)

| suffix       | statement shape                                             |
|--------------|------------------------------------------------------------|
| `_inj`       | injectivity: `f x = f y -> x = y`                          |
| `_congr`     | congruence / respects a relation: `R x y -> f x = f y`     |
| `_eq`        | a definitional / reflective equality (`... = 240`)         |
| `_range`     | a numeric bound (`0 <= x < N`, `x < 2 ^ k`)                |
| `_spec`      | a characterization lemma (VST: a `funspec`)               |
| `_length`    | a fact about `Datatypes.length` (a `nat`)                  |
| `_Zlength`   | a fact about `Zlength` (a `Z`)                             |

`_inj` and `_congr` are **different facts** — injectivity of the whole map vs.
"agrees on the relevant part, so the outputs agree" (e.g.
`shrincs_wots_hash_adrs_congr : adrs_struct_eq b a -> ... b i = ... a i`). Keep
both; do not rename one into the other.

### Length lemmas are subject-first

Domain lemmas put the subject first: `<subject>_length` / `<subject>_Zlength`
(`to_byte_length`, `pkgen_block_Zlength`, `chain_tips_Zlength`). The
`length_<subject>` / `Zlength_<subject>` word order is reserved for the small
set of generic list helpers that mirror a VST/stdlib lemma of that exact name
(`Zlength_app`, `Zlength_map`), where matching the ecosystem name aids search.
Do not have both orders for one fact. (On the VST side this shakes out as
predominantly `<subject>_Zlength` — `pkgen_block_Zlength`, `chain_Zlength` —
with `Zlength_<subject>` kept only for the generic helpers that shadow a
Floyd lemma of that name, e.g. `Zlength_concat_fixed`.)

### One concept, one name across trees

The same object gets one name in `Model`, `Vst`, and `Sec`:

- `shrincs_wots_hash_adrs` (model) and `shrincs_wots_chain_adrs` (Sec) look like a
  naming duplication but are NOT: the model primitive
  `shrincs_wots_hash_adrs (a : adrs) (i : nat) : adrs` sets the HASH type tag
  (matching the C `SF_SHRINCS_WOTS_HASH`), while
  `shrincs_wots_chain_adrs (t) (i pos) : adrs_sf` is the Sec tweak-space wrapper
  that calls it. Different arity, different type; keep both distinct names.
- the per-scheme constant `constant_sum` (a `nat`) is the one definition; the VST
  reflection `constant_sum_eq : Z.of_nat constant_sum = 240` and the concrete
  instantiation live beside it under the `_eq` / instantiation-suffix rules.

### Instantiation namespaces

Two distinct concrete layers, kept distinct:

- **`_shrincs`** — the concrete SHRINCS *parameters* (numbers): `w_shrincs = 16`,
  `chain_count_shrincs = 32`, `c_max_shrincs = 2^16`.
- **`_sha256`** — the parameter record at the *hash functions* of `spec.v`
  (`wc_sha256`), which instantiates the abstract hash interface.

An identifier never mixes the two; `_shrincs` answers "which numbers", `_sha256`
answers "which hash".

## Comments

Shared taxonomy across all three trees:

- **File header** — a `(** * <Module>` doc comment followed by a prose
  paragraph stating what the file defines/proves and its place in the proof
  (Model: its slot in the L0-L3 stack; Sec/Vst: what it proves and how it
  fits). `(** ... *)` doc comments describe the `Definition`/`Lemma`
  immediately below them and never appear inside a `Proof`; `(* ... *)` plain
  comments are for everything inside proofs.
- **Section banner** — a fixed-width rule then a `(** ** Title *)`, used to
  mark the major phases of a file. The exact glyph/width differs slightly
  per tree (Model and Vst use 65 `=` between `(* ` and ` *)`, 71 characters
  total; Sec uses 66 `-`, 72 characters total) — see each tree's section
  below for the exact rule and worked example; this is a real, harmless
  divergence, not something to harmonize away.
- **Inline** — `(* ... *)` on or just above a tactic, labeling case splits,
  induction steps, and any non-obvious move.
- ASCII only, in code and comments: `->` not the arrow glyph, `<=` spelled
  out, `x` not `×`, `--` not an em dash, `w^l` not a superscript. (A doc
  comment's prose paragraph may use the paper's own notation, e.g. `∘`, `Σ`,
  as the Sec file headers already do — but never inside an identifier or a
  tactic.)

### Comment scope

A comment earns its place by saying something the code cannot: the
statement being specified, an invariant the surrounding steps rely on, a
trust decision, or a non-obvious constraint (a library quirk, an ordering
requirement, a reason an easier-looking alternative is wrong). It does not
narrate tactics — `induction n.` does not need `(* induct on n *)` beside
it. It does not carry a change-log: git history owns the past, so a
comment states the present invariant, not how the code used to look or why
it changed (a note that starts "X used to be Y" should end up saying only
what X *is* and, if still relevant, why). This is a comment-content rule,
not a call to delete graveyard prose that is secretly load-bearing — if a
"historical" note is the only place a present fact about a type or an
invariant is written down (e.g. why a byte range is intrinsic to a type,
not an accident of one construction), keep the fact and drop the history
around it.

Trust-surface blocks are the load-bearing exception to "keep it short":
`AUDIT NOTE` and `IMPORT DISCIPLINE` comments exist to
carry exactly the
reasoning a reviewer cannot reconstruct from the statement alone — they are
mandatory wherever the surrounding claim depends on them, and are not
subject to trimming for brevity.

## Licensing header

Every hand-written file opens with the same 5-line MIT block the C
sources carry (`src/`, `include/`) — it is the file PREFIX: line 1 of
the file, then exactly one blank line, then the file-header doc
comment. Generated files (`clight/`) are exempt.

```coq
(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)
```

## Formatting

- 2-space indentation throughout; each nesting level adds 2.
- Prefer repetition over premature abstraction; do not compress whitespace or
  join lines for compactness.
- Break long multi-argument tactic/lemma applications at the opening
  parenthesis and align the continuations, rather than letting one line run
  on — Sec's
  `rewrite (Adv_perfect_l (R_gr_real PP N M F T_sf H_grind dPP dN dM w ...))`
  and Vst's `forward_call (v_acc, acc_s1_1a, mkUInt64 n1 Hn1, ...)` both
  follow this.
- Blank lines separate logical phases of a proof (setup, each hop/stage, the
  final assembly); no blank lines inside a run of similar steps (a block of
  `Local Abbreviation`, a block of `assert`/`set`). This applies to the
  proof-script-heavy Sec and Vst trees; Model's files are mostly
  `Definition`s and rarely need it.

## Imports

- Group imports by origin. In VST files, establish the VST environment
  before importing MathComp. In SSProve files, use the library prelude
  before backend proof modules. Keep ordinary Gallina proofs in the
  established Stdlib style.
- In MathComp word code, import `BinInt` rather than `ZArith`, whose
  natural-number power notation shadows `expn`. Use `%nat` for MathComp
  natural numbers, since `%N` belongs to the binary natural-number scope.
  Open `Z_scope` by name for integer literals, since `%Z` can select
  MathComp's integer scope.
- The four public definition files must import no internal proof module.
  They may import external libraries and generated Clight programs.
  `sha256.v` owns the word codecs. `contracts.v` owns shared `CompSpecs`.
- Keep VST memory lemmas and SSProve algorithm correspondence proofs in
  their backends. Shared word bounds belong in `internal/common/bytes.v`.
  Small proofs needed to construct dependent values and instances may
  remain beside their definitions. Preserve the reference names and loop
  structure in `spec.v`.

## Honesty / audit constraints

The honesty gate lives in **`proof/audit/check.sh`** (run via
`dune build @proof/audit`),
reading its allowlist from **`proof/audit/allowed.txt`**. One scope, not
three: the trees are gated together, since one theorem
(`theorem.v`'s `shrincs_correct_and_secure`) spans all of
them. The build gate checks seven properties:

0. **Built and reviewed**: every source the theory compiled has its `.vo`
   and is tracked by git. The theory in `proof/dune` takes every `.v` file
   under `proof/`, so an untracked file there is compiled and this gate
   refuses it. The generated Clight programs are the exception. Dune
   rebuilds by content, so an object is never older than its source.
1. **No proof gaps**: no `Admitted.`, `admit.`, `give_up.` in any source
   the theory compiled, `audit/` excepted (its two files are queries, not
   proofs). Gates 1 and 2 read the sources in the audit's sandbox, which
   are exactly the ones that were compiled.
2. **No declared assumptions**: every top-level `Axiom`, `Parameter`, and
   section `Hypothesis` or `Conjecture` under `proof/` is checked by source
   text, and **no file may declare one**. The security statement names its
   six reductions and bounds the forger by their advantages against the
   hash games (PRF, SM-UD, STCRP, SM-TCR at the public key hash, SM-TCR at
   the chain hash, SM-PRE), so no hardness axiom is needed.
   There are no declaration exemptions. Section `Context` and `Variable`
   binders are discharged at `End` and are exempt from this scan.
   A theorem must not take an advantage
   bound or the existence of a reduction as a premise — every reduction
   is *constructed*; the only admissible hypotheses are data side
   conditions (e.g. `Hrange`) and, in Sec, adversary-validity
   (`ValidPackage`).
3. **Headline pin** — `audit/probe.v` must literally probe
   `shrincs_correct_and_secure` and `sha256_c_correct`, so neither
   can be silently renamed or swapped for a weaker namesake.
4. **Closed axiom base** — `Print Assumptions` on those two theorems must
   stay within `allowed.txt`. Adding a dependency that drags in a new
   axiom fails the audit.
5. **Statement pin**: `audit/statement.v` carries reviewed copies of
   both public statements and the kernel must accept each live
   theorem at that exact type, so a dropped conjunct or a weakened bound
   is a compile failure rather than a diff a reviewer has to notice.
6. **Public import boundary**: `sha256.v`, `spec.v`, `contracts.v` and
   `games.v` may not import `Shrincs.internal` modules.

A theorem whose *statement* smuggles an advantage bound or a reduction's
existence as a premise would still pass all seven gates. That anti-pattern
is banned by this section, not caught mechanically. Gate 5 is what pins
the public statements against silent drift once reviewed. It
does not review it for you.

---

# Model

Except for the representation and SHA interfaces listed above, Model
files are ordinary Gallina + `lia`/`induction`/`cbn`/stdlib rewrites
(no ssreflect idiom, no VST tactics). One tactic per line; `by (...)` for
1-3 tactic leaves; `{ }` blocks with `-`/`+`/`*` bullets for branching.

Section banner: a 65-`=` rule (71 characters total between and including
`(* ` and ` *)`) then `(** ** Title *)`.

# Sec (SSProve)

The proof is written in **Rocq** in the **ssreflect / MathComp** idiom, on
top of **SSProve** (state-separating proofs).

## Tactics

- **One tactic per line is the default.** Each logically distinct step gets
  its own line, so the proof reads as a sequence of moves and a failure
  points at one line.
- **`;` chaining is idiomatic here**, unlike a VST development — but only to
  keep a *single thought* together, not to pack unrelated steps. Use it when:
  - the same tactic discharges all generated subgoals (`... => t; rewrite /tweak_lt => ->`);
  - a short fixed sequence is applied to a structurally repeated goal
    (`eapply r_put_lhs; eapply r_put_lhs; eapply r_put_lhs.`);
  - an ssreflect intro/rewrite pattern belongs to one `move`
    (`move=> hgood hus.`, `case: hpre => s1c [hpre1 ->].`).
  Do not chain two independent high-level steps just to save a line.
- **`by [ ... ]` / `by tac`** closes a goal that finishes in 1-3 tactics; prefer it
  for leaf goals (`Proof. by rewrite -addn1 chain_cat. Qed.`, `by []`). For
  anything longer, open the proof out into lines.
- **`Set Default Goal Selector "!"`** is on project-wide (in `prelude.v`): a tactic
  must solve exactly the goal it is written against. Multiple goals are dispatched
  with bullets or an explicit selector, never by letting a tactic fall through to
  the next goal.
- `do N tac` is fine for genuinely repeated identical steps.
- Keep lines readable (~80 cols); wrap long applications rather than letting
  them run (see the shared Formatting section for the worked example).

## Branching

- Use ssreflect bullets `-` (level 1), `+` (level 2), `*` (level 3); the `!`
  selector forbids silent multi-goal application, so bullets carry the structure.
- `[ a | b ]` branch syntax is allowed inside short single-line proofs
  (`apply: lerD; [exact: lexx | exact: hUD0]`). For multi-line cases use bullets.
- Each branch starts on its own line; label every nontrivial case with an inline
  comment naming what it proves:
  ```coq
  case: d => [|d'].
  - (* d = 0 : chain of length zero is the identity *)
    ...
  - (* d = d'.+1 : peel one hash and recurse *)
    ...
  ```

## Naming

- **Hypotheses use a lowercase `h` prefix + a short descriptive tail**: `hpre`,
  `hgood`, `hus`, `hrange`, `hpp`. Reserve capital `H...` only where an existing
  convention already uses it; do not introduce VST-style `H`-names. Name
  hypotheses at introduction (`move=> hgood hus.`) rather than relying on
  autogenerated `H`/`H0`.
- **Lemmas** are named `operation_operand` or `predicate_subject`:
  `chain_cat`, `chain_rcons`, `unzip1_wq`, `qnth_cat_r`, `tlt_notin`,
  `th_eval_wtw`. The name should let a reader predict the statement. Note the
  `_inj`/`_congr` split from the shared table is load-bearing here: the tweak
  maps have injectivity lemmas conditional on their index bounds
  (`chain_tweak_inj`, `prf_tweak_inj`), distinct from the address congruence lemmas.
- **Games / reductions** carry descriptive names: the forge games
  `G_forge_sampledkey` / `G_forge_uniformchains` / `G_forge_keyed` and the post-hop
  intermediates `G_post_grind` / `G_post_compress` / `G_post_chain`; the
  reductions `R_ud`, `R_grind`, `R_compress`, `R_chain_tcr`, `R_chain_pre`,
  `R_prf`, with their perfect-indistinguishability lemmas `R_*_real` /
  `R_*_ideal` and the matching `*_loc` location set (prefixes `forge_`,
  `ud_hybrid_`, `r_ud_`, `r_grind_`, `r_compress_`, `r_chain_tcr_`,
  `r_chain_pre_`, `r_prf_`). Match these names when extending the tree.
- **Parameters travel as one record.** Files take a single
  `Context (P : wc_params)` (`Shrincs.internal.ssprove.wots.params`); scheme and game constants are
  plain definitions applied to `P` (`digest_of P`, `shrincs_wots_scheme P`,
  `wsigs P`, ...), never per-file `Local Abbreviation` pins of parameter-applied
  constants. Hop-LOCAL proof abbreviations (invariant shapes, `r_*_tail`-style
  scaffolding inside one hop file) may still use `Local Abbreviation`; use `set`
  only for a local subterm introduced inside a single proof.

## Comments

Three levels, matching the existing files (the shared taxonomy above applies;
these are the exact per-tree numbers/examples):

1. **File header** — `(** * Logical.Module.Name` followed by a prose paragraph
   stating what the file proves and how it fits the proof:
   ```coq
   (** * Shrincs.internal.ssprove.wots.hop.chain_tcr

       The SM-TCR(F) chain hop ... *)
   ```
2. **Section header banner** — a 66-dash rule, then a `(** ** Title *)`:
   ```coq
   (* ------------------------------------------------------------------ *)
   (** ** Pure layer: classification of chain forgeries *)
   ```
   The rule is exactly 66 dashes between `(* ` and ` *)`. Use these to mark the
   major phases of a long file (pure layer, each `G_post_*`, the reduction package).
3. **Inline** — `(* ... *)` on or just above the tactic, used to label case splits,
   induction steps, and any non-obvious move.

- Put a one-line `(** ... *)` above a lemma when its name does not fully convey the
  statement (`(** [unzip1] commutes with the re-tagging. *)`).
- Document the proof strategy in the file/section header for the hop files; the
  long relational proofs lean on these maps.

## SSProve conventions

- Build games and reductions with **package notation** (`[package ...]`,
  `{ #def ... }`); reach for procedural `{ }` blocks only inside ordinary Rocq
  proofs, not to structure code.
- Relational proofs go through the project's relational rule lemmas
  (`r_put_lhs`/`r_put_rhs`, `r_get_rhs_known`, `r_ret`, `r_reflexivity_alt`, ...).
  When you need a new such rule, state it as a **generic** lemma in
  `Shrincs.internal.ssprove.lib.toolkit.relational_rules` rather than a one-off inside a hop — keep all
  hops drawing from one shared set.
- Invariants are `heap_ignore <locs>` refined with `rel_app`/`couple_*`; define the
  location set and the invariant once per package and reuse the helper update
  lemmas (`heap_ignore_set_r` + a membership proof) instead of re-deriving them.
- A game hop is three pieces: the two `*_real` / `*_ideal` `perfect` lemmas and the
  `Adv_perfect_l/r` + `Adv_reduction` rewrite that turns the hop into an `AdvOf`
  term. `theorem.v` is the model for assembling hops with `Adv_triangle` + `lerD`.

## Reuse over duplication

The generic, hash-parameterized chain machinery lives in `Shrincs.internal.ssprove.lib.chain.*`
(scheme functions, root sampling, forgery analysis, the SM-TCR/SM-PRE decision
layer, the SM-UD maps); the WOTS+C hops *instantiate* it at the address-wrapped
chain hash `Fw` rather than re-deriving it. When a lemma/definition is generic
over the tweak/address transformer (pure `qnth`/`fmap` bookkeeping, per-chain
induction skeletons), put it in `Shrincs.internal.ssprove.lib.chain.*` and instantiate it in the hop,
so the hop's obligation shrinks to "instantiate + discharge the wrapper". A new
generic relational rule goes in `Shrincs.internal.ssprove.lib.toolkit.relational_rules`, not a one-off
inside a hop. Factor a repeated tactic block into a named lemma or a small
`Ltac`/`Notation` only once the same shape has appeared 3+ times; below that
threshold, prefer repetition.

# Vst (VST)

## Tactics

- **One tactic per line.** Never chain independent tactics with `;` on one line.
- Semicolons are allowed inside `by (...)` or `ltac:(...)` for short inline proofs:
  ```coq
  assert (H : 0 <= x) by (apply Z.div_pos; lia).
  ```
- A trailing `; solver` is allowed when the solver (e.g. `lia`, `nia`, `reflexivity`)
  closes all remaining subgoals in one shot:
  ```coq
  apply limb_add_0; lia.
  apply limb_add_2_u64; lia.
  ```
- A `; ` chain is allowed when all generated subgoals use the same tactic sequence:
  ```coq
  apply Zbits.eqmod_add;
      apply Zbits.eqmod_sym;
      apply Zbits.eqmod_mod;
      lia.
  ```
- `by (...)` is for proofs that fit on one line (1-3 tactics). Use `{ }` blocks for anything longer.
- `do N tactic` is allowed for repeated identical tactics (e.g. `do 3 f_equal.`), but not for VST tactics like `forward` -- each `forward` should be on its own line with a comment.
- `ltac:(...)` is for very short proof obligations passed as arguments (1-2 tactics). If longer than ~60 characters, assert separately first.

## Assertions

- Short proof: `assert (H : statement) by (tactic1; tactic2).`
- Long proof:
  ```coq
  assert (H : statement).
  { tactic1.
    tactic2.
    tactic3. }
  ```
- Group similar assertions together without blank lines between them:
  ```coq
  assert (Hm0 : 0 <= m0 < B) by (subst m0; apply Z.mod_pos_bound; lia).
  assert (Hm1 : 0 <= m1 < B) by (subst m1; apply Z.mod_pos_bound; lia).
  assert (Hm2 : 0 <= m2 < B) by (subst m2; apply Z.mod_pos_bound; lia).
  ```

## Branching

- Use `{ }` blocks with bullets (up to 3 nesting levels): `-` (level 1), `+` (level 2), `*` (level 3).
- `[ | ]` syntax is allowed in short single-line proofs (e.g. inside `by (...)`).
  For multi-line branching, use `{ }` with bullets instead.
- Each branch gets its own line:
  ```coq
  assert (0 <= t0).
  { subst t0. apply Z.add_nonneg_nonneg.
    - lia.
    - apply Z.mul_nonneg_nonneg; lia. }
  ```
- Closing `}` goes on the last line of the block when short, or on its own line when the block is long.
- Add a short comment on each major branch or conjunct explaining what it proves:
  ```coq
  repeat split.
  - (* conjunct 0: (sum / B^0) mod B = a0 *)
    rewrite Z.pow_0_r, Z.div_1_r.
    ...
  - (* conjunct 1: (sum / B^1) mod B = a1 *)
    rewrite Z.pow_1_r.
    ...
  ```

## Formatting

- Contents of `{ }` blocks are indented by 2 relative to the `assert` or tactic that opened them.
- Bullet points (`-`, `+`, `*`) are indented to the block level, with their body indented by 2 more.
- For complex proofs, document the proof strategy in the lemma's doc comment before `Proof.`

## Comments

Three levels (the shared taxonomy above applies; these are the exact
per-tree numbers/examples):

1. **Section headers** (file-level):
   ```coq
   (* ================================================================= *)
   (** ** Section Name *)
   (* ================================================================= *)
   ```
   Subsections use `(** *** Subsection Name *)`. The rule is exactly 65 `=`
   between `(* ` and ` *)`, 71 characters total.

2. **Proof phases** (inside proof bodies):
   ```coq
   (* ===== Stage 1: Reduce 512 -> 385 bits ===== *)
   ```

3. **Inline** (tactic-level):
   ```coq
   (* muladd_fast(&acc, n0, N_C_0) *)
   ```

## Context & Naming

- Hypothesis names: `H` prefix + descriptive (`Hd0`, `Hchain`, `Hr_z_bnd`).
- Intermediate values: `set (name := expr).` with short descriptive names.
- `clear` intermediates as soon as they are no longer needed. Large VST contexts slow down tactics significantly.
- Use `clear -` (keep only listed hypotheses) at stage boundaries to reset the context.
- `rename H into Hname` immediately after `Intros` to give hypotheses meaningful names.

## VST proof style

- Comment before each `forward_call` explaining the C operation.
- Side condition proofs in `{ }` blocks.
- `Intros` / `rename H` / `assert` / `clear` each on their own line:
  ```coq
  (* secp256k1_u128_from_u64(&t, d0) *)
  forward_call (v_t, mkUInt64 d0 Hd0, Tsh).
  Intros t_init.
  rename H into Ht_init.
  ```
