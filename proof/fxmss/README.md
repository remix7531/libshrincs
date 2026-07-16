# Vendored FXMSS proof

A **self-contained, vendored snapshot** of the complete EU-CMA security proof for
**FXMSS** — the fixed/counter-schedule unbalanced XMSS of WOTS+C leaves — copied
verbatim from the `verified-spec-2` development. It is kept deliberately isolated from
libshrincs's native `Sec.*` proof tree.

## Entry theorem

`SHRINCS.FXMSS.Theorem.FXMSS_secure` (`shrincs/FXMSS/Theorem.v`) — the end-to-end EU-CMA
advantage bound for FXMSS. `Qed`, admit-free. It bounds the forging advantage by the
telescoping sum of the per-primitive reduction terms (PRF over the secret-key seed, PRF
over the message randomizer, digest reprogramming, digest, grind, the leaf terms, tree
SM-TCR, and TCRX), assembled from the per-hop lemmas in this tree.

## Why this is separate from `Sec.*`

libshrincs's native WOTS+C proof (`Sec.wots.*`) is a re-engineered development whose
public interface diverged from the WOTS+C that the FXMSS proof is written against
(`SHRINCS.WOTSC.*`): different definition names and types, a different `Addressing`, and
no `FixedSumOTS` leaf-OTS abstraction (the interface the FXMSS leaf reduction targets).
FXMSS therefore cannot compile against `Sec.wots`/`Sec.lib` without a full re-derivation.
Rather than duplicate that effort now, this tree vendors FXMSS together with the exact
dependencies it needs, under their **original logical names**, so every import resolves
with zero rewrites.

## Layout & logical names

Mapped in `proof/_RocqProject` (roots disjoint from `Sec`/`Model`/`Vst`/`Assumptions`):

| directory         | logical root   | contents |
|-------------------|----------------|----------|
| `fxmss/hbs/`       | `HBS`          | the SSProve/HBS framework closure — `Prelude`, `Math.{BinTree,Merkle,Chain,Encoding}`, `Sig.{Scheme,KOTS}`, `Games.{THF,PRF,SMTCR,SMPRE,SMUD,STCRP,TCRX}`, `Toolkit.{SampleSeq,ROPlus,Reprogram}` |
| `fxmss/examples/`  | `HBS.Examples` | `FixedSumOTS.*` — the generic Winternitz-with-checksum one-time signature the FXMSS leaf reduces to (WOTS+C is proved to *be* a `FixedSumOTS`) |
| `fxmss/shrincs/`   | `SHRINCS`      | `Addressing`, the WOTS+C leaf (`WOTSC/*`, import-closure only), and the FXMSS proof (`FXMSS/*`) |

No `SHRINCS.SPX` is present — this is FXMSS only.

## Vendored-snapshot conventions (deliberate exceptions to STYLE.md)

This is a faithful copy, not a native port, so it intentionally departs from
`proof/STYLE.md`:
- **CamelCase filenames** are kept — required, since the copied imports name CamelCase modules.
- **Original identifiers and file headers** are preserved verbatim (no `shrincs_fxmss_`
  prefixing, no re-bannering).

The file set is exactly what `verified-spec-2` builds for `FXMSS_secure` (59 files); the
two upstream dead-code files — a superseded single-leaf hop and a prototype — are omitted.

## Building

`make prove` and `make ssprove-prove` (from `proof/`, inside `nix develop .#ssprove`)
build this tree automatically: the file list and `-Q` maps are in `proof/_RocqProject`
and `rocq makefile` regenerates the rules. No Makefile edit is needed.

## Trust surface

`FXMSS_secure` is admit-free and introduces **no new axiom, parameter, or trust anchor**.
Its `Print Assumptions` cone is the classical/SSProve baseline already whitelisted for the
`[ssprove]` tree in `proof/assumptions/allowed.txt` (propositional/functional
extensionality, indefinite description, strict-Prop proof irrelevance, the real-number
carrier, and mathcomp-analysis's `realsum.__admitted__interchange_psum`).

A standalone probe `proof/assumptions/fxmss.v` runs `Print Assumptions FXMSS_secure` for
manual/CI review. It is intentionally **not** wired into `make audit`'s automated gate:
doing so requires an `[fxmss]` section in `proof/assumptions/allowed.txt`, which — per
libshrincs `AGENTS.md` — needs explicit approval, even though it would only repeat the
existing `[ssprove]` baseline names.

## TODO: reconciliation

Longer term, FXMSS should be ported into `Sec.fxmss.*`, reusing the native `Sec.wots`
WOTS+C and `Sec.lib` framework (adding the missing Merkle-tree and `FixedSumOTS` machinery
under `Sec.lib`), retiring this vendored tree. That is a substantial re-derivation — the
WOTS+C interface must be re-targeted lemma-by-lemma — and is intentionally deferred.
