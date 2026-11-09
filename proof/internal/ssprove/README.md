# WOTS+C, machine-checked (Rocq / SSProve)

A machine-checked one-time security proof of **WOTS+C** — the grinding Winternitz
one-time signature that forms the leaf of the
[SHRINCS](https://eprint.iacr.org/2025/2203) hash-based signature scheme — in
[Rocq](https://rocq-prover.org) on top of [SSProve](https://github.com/SSProve/ssprove).

The proof reduces WOTS+C forgery to standard hash-function assumptions, with **no
admitted goals**, checked automatically by `assumptions/check.sh`. The abstract headline
theorem (`shrincs_wots_secure`) and its spec-parameter instantiation
(`shrincs_wots_secure_shrincs`) add no axioms beyond the fixed classical baseline
recorded in `proof/assumptions/allowed.txt`. The concrete corollary over real SHA-256
(`shrincs_wots_secure_sha256`, in `axioms.v`) additionally rests on 6 named
hash-hardness axioms, by design. It is a self-contained proof-of-concept: a generic
hash-based-signature library (`lib/`), the WOTS+C scheme and proof (under `wots/`,
including `wots/hop/`/`wots/bound/`), `bridge.v`, which bridges this tree's
math layer directly to the shared `Model.wots` (also used by the VST proof, at
`proof/model/wots.v`), and `wots/model_bridge.v`, which uses that bridge to prove the
games scheme's public key / signing / verification agree with `Model.wots` end to end
at the concrete SHA-256 instantiation. Naming was originally
chosen to track the shrincs-bip specification's `wots_c_*` algorithm names
and `chain_count`/`constant_sum` parameters; after libshrincs's multi-scheme
rename this repo's own identifiers are now `shrincs_wots_*`/`SF_SHRINCS_WOTS_*`
(shrincs-bip's own reference implementation is unaffected and keeps `wots_c_*`).

## The theorem

[`shrincs_wots_secure`](wots/theorem.v) bounds the advantage in the one-time,
known-message forgery experiment for **keyed** WOTS+C — chain starts PRF-derived
from a hidden SKseed on `SF_SHRINCS_WOTS_PRF` addresses, as in the spec — by a sum of
advantages against the leaf-hash assumptions:

```
Adv(G_forge_keyed_real, G_forge_keyed_ideal, A)
  <=            AdvOf(PRF on SKseed)  (A ∘ R_prf,true)      -- key derivation
    +  Σ_{s<w-2} AdvOf(SM-UD on F)    (A ∘ R_ud,true,s)     -- chain-value undetectability
    +           AdvOf(S-TCR on H_grind)(A ∘ R_grind)        -- the grinding search
    +           AdvOf(SM-TCR on T_sf) (A ∘ R_compress)     -- public-key compression
    +           AdvOf(SM-TCR on F)    (A ∘ R_chain)        -- chain target collisions
    +           AdvOf(SM-PRE on F)    (A ∘ R_preimage)     -- chain preimages
    +  Σ_{s<w-2} AdvOf(SM-UD on F)    (A ∘ R_ud,false,s)
    +           AdvOf(PRF on SKseed)  (A ∘ R_prf,false)
```

Every `R_*` is an explicitly constructed reduction package; the left-hand side is the
forgery success probability. The middle six terms are the ideal-key stepping theorem
`shrincs_wots_secure_ideal_sk` (chain starts sampled); the PRF hop composes with it by the
advantage triangle. Side conditions: `Hrange` (the grinding hash's output lies below
`w^chain_count`) and `Hcc` (at least one chain) — both discharged in
[`instantiation.v`](wots/instantiation.v), which states the bound at
the spec's numbers (`shrincs_wots_secure_shrincs`: w = 16, chain_count = 32,
constant_sum = 240, a 16-bit counter, 16-byte values, uniform samplers).

[`shrincs_wots_secure_kots`](wots/theorem.v) restates the SAME bound over the
**standard** known-message valid-commit notion `KOTS_vc_game`
([`lib/sig/kots.v`](lib/sig/kots.v)) instead of the bespoke `G_forge_keyed`:
[`wots/kots_link.v`](wots/kots_link.v) proves the two games are PERFECTLY,
unconditionally, the same experiment, so the bound carries over unchanged
(`shrincs_wots_secure_kots_ideal_sk` is the matching ideal-key sibling of
`shrincs_wots_secure_ideal_sk`). The concrete SHA-256 corollary has the same
pair: [`shrincs_wots_secure_sha256`](axioms.v) and its
KOTS-notion restatement `shrincs_wots_secure_kots_sha256` — the statement a
referee who only trusts the standard notion should read.

## What to verify by hand

The Rocq kernel has already checked every inference of the proof. What it *cannot*
check is that the **definitions and the statement** mean what you intend — that is the
entire human review surface:

1. **The hash assumptions** — [`lib/games/`](lib/games/): `smtcr.v` /
   `smpre.v` / `smud.v` (single-function multi-target target-collision / preimage /
   undetectability — the SPHINCS+ tweakable-hash notions), `stcrp.v` (the
   predicate-parameterized variant for the grinding search), `prf.v` (the keyed-hash
   distinguishing game for the SKseed derivation), and `thf.v` (the tweakable-hash
   record and the **real/ideal game-pair convention**:
   `AdvOf(G,A) := Adv(G(true),G(false),A)` is the search-game success probability).
   `thf.v`'s header also carries a **4-copy lazy-`pp`-sampling AUDIT NOTE**: the
   identical "sample `th_dPP` once, share it via `<game>_pp_loc`" idiom is
   deliberately duplicated across `SMTCR`/`SMPRE`/`SMUD`/`STCRP` (rather than
   factored into one helper, so the reduction proofs can pattern-match each
   game's unfolded oracle code) — an auditor should confirm the four copies stay
   identical, since a divergent copy is exactly the unsoundness the duplication
   could otherwise hide.
2. **The experiment** — [`lib/sig/kots.v`](lib/sig/kots.v): the one-time
   *known-message* forgery game pair (see *Scope*): the plain `KOTS_game` and
   its VALID-COMMIT variant `KOTS_vc_game` (COMMIT `fail`s outright on a sign
   refusal instead of revealing a `None` signature — see that file's header
   for the rationale). `KOTS_vc_game` is now MACHINE-LINKED, perfectly and
   unconditionally, to the flat, WOTS+C-specialized games this proof
   establishes: [`wots/kots_link.v`](wots/kots_link.v) proves `G_forge_keyed`
   (the headline's keyed variant, [`hop/prf.v`](wots/hop/prf.v)) and
   `G_forge_sampledkey` (the ideal-key variant, [`wots/games.v`](wots/games.v))
   ARE `KOTS_vc_game` at the keyed / ideal-key schemes, with no side
   condition — see `shrincs_wots_secure_kots` and
   `shrincs_wots_secure_kots_sha256` (point 4 below), which restate the
   headline bounds directly over `KOTS_vc_game`. A referee content with the
   standard notion can therefore read `lib/sig/scheme.v` + `lib/sig/kots.v` +
   the `shrincs_wots_secure_kots_sha256` statement and stop there; the flat
   games below (`G_forge_sampledkey`/`G_forge_uniformchains`/`G_forge_keyed`)
   become proof-internal scaffolding rather than trusted surface, once
   `kots_link.v` is accepted. **Still forward scaffolding, not machine-linked
   to this proof**: the plain (non-valid-commit) `KOTS_game` and its adaptive
   cousin `EUCMA_game` ([`lib/sig/eucma.v`](lib/sig/eucma.v)) remain generic
   game definitions for a future multi-scheme layer (`EUCMA_game` is
   unreferenced outside its own file).
3. **The scheme** — [`scheme.v`](wots/scheme.v),
   [`addressing.v`](addressing.v) (the spec's 22-byte stateful
   address rows, types 16/17/18/21/22) and the keyed scheme `shrincs_wots_keyed` in
   [`hop/prf.v`](wots/hop/prf.v): do
   `shrincs_wots_pubkey_gen`/`shrincs_wots_sign`/`shrincs_wots_verify` (PRF key derivation, grinding,
   chains, public-key compression) and the address structure faithfully define
   WOTS+C? This is the artifact's specification of the scheme; the pure contract it
   is bridged against is the shared [`Model.wots`](../model/wots.v) (also used by the
   VST proof), with the digit/chain/counter equivalences proved in
   [`bridge.v`](bridge.v). The games↔model correspondence is now proved
   **end-to-end** in [`wots/model_bridge.v`](wots/model_bridge.v): at the concrete
   truncated-SHA256 instantiation, the games scheme computes the same thing as the
   ground-truth `Model.wots`, discharged as plain equalities through the
   `encode16`/`decode16` dictionary — the four headliners are `pubkey_gen_modelE`
   (keyed public key), `find_counter_modelE` (grinding search), `verify_modelE`
   (boolean verification) and `sign_modelE` (partial signing).
   `scheme.digest_of` reads MSB-first, matching `Model.wots.base_2b`, so
   `model_bridge.digest_of_modelE` proves the two digit vectors *equal* (no
   `[i ↔ chain_count-1-i]` relabeling).
4. **The statement** — [`theorem.v`](wots/theorem.v): quantified over
   *all* valid adversaries; the left side is the advantage in (2); each right-hand
   term is the advantage against one assumption of (1) composed with an *explicit*
   reduction; no reduction or advantage bound is smuggled in as a hypothesis.
   `shrincs_wots_secure_kots`/`shrincs_wots_secure_kots_ideal_sk` (same file) and
   `shrincs_wots_secure_kots_sha256` ([`axioms.v`](axioms.v))
   restate `shrincs_wots_secure`/`shrincs_wots_secure_ideal_sk`/
   `shrincs_wots_secure_sha256` over the standard `KOTS_vc_game` notion of point 2,
   via the unconditional link in `kots_link.v` — read whichever form matches the
   notion you trust.
5. **The trusted base** —
   [`assumptions/allowed.txt`](../assumptions/allowed.txt): the inherited
   library baseline, plus (only for the concrete
   `shrincs_wots_secure_sha256` corollary) 6 named hash-hardness axioms in
   [`axioms.v`](axioms.v) — PRF, SM-UD, STCRP, SM-TCR at the
   pk-compression hash, SM-TCR at the chain hash, SM-PRE. **The abstract theorems add
   none of these** — `assumptions/check.sh` enforces both facts via `Print Assumptions`.
   Each of the 6 is *minimal* along both axes a statement can be minimal:
   it is **scoped to valid adversaries** (the `VB` premise bounds `AdvOf G B`
   only for packages honestly implementing the game's adversary interface —
   strictly weaker than an unconditional bound; each application pays a
   one-line `valid_adv_link` discharge from the reduction's bundled
   validity), and it is **anchor-free by construction**: the game instances
   inside the axioms are built from `wc_sha256_core`, the anchor-free core
   record (`params.wc_params_core`), so no axiom mentions the imaginary-tree
   anchor or its range proofs at any depth — a syntactic fact about the
   statements, machine-tied to the full instances by the definitional witness
   `wc_sha256_coreE` (see `axioms.v`'s header, "REVIEWER NOTE").

The reductions, relational invariants, and tactic proofs do **not** need reading —
they are what the kernel checked.

## Building and the honesty gate

Requires [Nix](https://nixos.org) with flakes (Rocq 9.2 + MathComp 2.6; SSProve is fetched
from GitHub pinned to commit `fdbf1c4` on first `nix develop`). Run from the repo
root (`libshrincs/`):

```sh
nix develop                       # enter the toolchain
make ssprove-prove                 # type-check every proof in this tree
bash proof/assumptions/check.sh    # the honesty gate
# or, combined: `make audit` (also builds+checks the vst tree's honesty gate)
```

`assumptions/check.sh` fails unless: no proof gaps (`Admitted`/`admit.`/`give_up`); no
`Axiom`/`Conjecture`/section `Hypothesis` anywhere except exactly the 6 named
hash-game axioms in `axioms.v`; `Print Assumptions` on the headline theorems
and the pure milestones stays within the classical baseline plus those same 6 axioms;
and every source has an up-to-date `.vo`.

## Layout

The WOTS+C scheme and proof live under `wots/` (so they take the `Sec.wots.*`
logical namespace, leaving the top-level `Sec.*` namespace free for future
schemes); the shared substrate — `addressing.v`, `bridge.v`, `lib/` — stays at the
top level. Everything sits under a single Rocq logical root declared in the
`proof/_RocqProject`: `Sec` (this whole directory — the scheme + proof, the
`bridge.v` model bridge, and the `lib/` generic substrate). The neutral model lives
under the `Model` root, and the cross-cutting assumption probes under `Assumptions`
(`proof/assumptions/`, one level up).

- **`bridge.v`** — the proved equivalences between the shared
  [`Model.wots`](../model/wots.v) (also used by the VST proof) and this repo's math
  layer (MSB-first bit-group digits vs LSB-first `digits_w`, the counter search, the
  chain recursion), plus (in `axioms.v`) the
  instantiation to concrete SHA-256. `wots/model_bridge.v` then consumes these
  equivalences to prove the full games↔`Model.wots` correspondence (pubkey, counter,
  signing, verification) at that instantiation. The big-endian byte-encoding lemmas
  it builds on (`be_num`, `digits_w_split`) live in the shared
  [`Model.math.encoding`](../model/math/encoding.v).
- **`lib/`** — hash-based signatures in SSProve: `prelude.v` (shared imports), the
  assumption games (`games/`, including `prf_derive.v`, the generic PRF-derived-keys
  loop machinery factored out of the WOTS+C PRF hop — instantiated at
  `wots/hop/prf.v`), the signature/experiment framework (`sig/`, including the
  generic known-message experiment pair `kots.v`), a relational and sampling
  toolkit (`toolkit/`), and a generic Winternitz-chain layer (`chain/`: scheme
  functions, root sampling, forgery analysis, the SM-TCR/SM-PRE decision layer, the
  SM-UD sampling maps) — all parameterized by an abstract tweakable hash. The
  shared combinatorial core (digit/checksum combinatorics) lives outside this tree,
  in `Model.math` (`proof/model/math/`).
- **`wots/`** — the WOTS+C scheme (`scheme.v`; the shared `addressing.v` stays at
  the top level), its game scaffolding (`games.v`, `analysis.v`), one reduction per
  assumption (`wots/hop/`: `Grind`, `Compress`, the chain halves `ChainTCR`/`ChainPRE`
  over their shared `ChainCommon`, `UD`, and the key-derivation hop `Prf` with the
  keyed game `G_forge_keyed`), the per-hop advantage bounds (`wots/bound/`), the
  assembling `theorem.v`, the spec-parameter corollary (`instantiation.v`), the
  concrete SHA-256 connection (`axioms.v`), the games↔`Model.wots`
  correspondence (`model_bridge.v`), and the link to the standard KOTS notion
  (`kots_link.v`) — all under the `Sec.wots.*` namespace.

42 source files, ~13,050 lines. SSProve is the only external Rocq dependency.

## Scope

- **Known-message (one-time), not adaptive EU-CMA.** Security is in the known-message
  experiment ([`kots.v`](lib/sig/kots.v)), where the signed message is fixed
  before the public key is shown — a deliberate scoping choice (one-time WOTS+ is known
  to be adaptively EU-CMA, [arXiv:2002.07419](https://arxiv.org/abs/2002.07419)) that
  matches what the SHRINCS tower consumes.
- **Classical model.** SSProve models classical adversaries; the reductions are
  model-agnostic (they relay oracles and never inspect the adversary), so a QROM bound
  is the same expression read with the assumptions' QROM advantages.
- **Bounded grinding.** The capped grinding search yields a small statistical term,
  `0` in the unbounded idealization.
- **Abstract, with a concrete SHA-256 corollary.** The headline theorems are proved
  over abstract tweakable-hash families; [`axioms.v`](axioms.v)
  instantiates them with the spec's real truncated-SHA-256 construction (via
  [`Model.wots`](../model/wots.v)), yielding `shrincs_wots_secure_sha256`: an
  unconditional bound modulo 6 named hash-hardness axioms.
