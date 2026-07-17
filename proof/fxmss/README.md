# FXMSS proof and compatibility boundary

The complete EU-CMA security proof for **FXMSS**, the fixed/counter-schedule
unbalanced XMSS of WOTS+C leaves.  It originated in `verified-spec-2` and
retains its original logical roots, while compatible generic definitions are
imported from libshrincs rather than duplicated.

## Entry theorem

`SHRINCS.FXMSS.Theorem.FXMSS_secure` (`shrincs/FXMSS/Theorem.v`) — the end-to-end EU-CMA
advantage bound for FXMSS. `Qed`, admit-free. It bounds the forging advantage by the
telescoping sum of the per-primitive reduction terms (PRF over the secret-key seed, PRF
over the message randomizer, digest reprogramming, digest, grind, the leaf terms, tree
SM-TCR, and TCRX), assembled from the per-hop lemmas in this tree.

## Compatibility boundary

`Prelude`, `Sig.{Scheme,KOTS}`, `Games.{THF,PRF,SMTCR,SMPRE,SMUD,STCRP}`,
and `Toolkit.SampleSeq` are compatibility exports of native `Sec.lib`
modules; they contain no duplicate definitions.  The adaptive PRF game needed
by FXMSS lives in `Sec.lib.games.prf_adaptive`.

The retained modules are the minimal incompatible closure.  TCRX, random-oracle
reprogramming, and Merkle-tree machinery have no native counterpart.
`FixedSumOTS` and the WOTS+C hop files expose banked relational invariants used
directly by the multi-leaf proof.  Native `Sec.wots.hop.*` fixes one anchor in
`wc_params`; FXMSS instead proves multi-instance hops over up to `n_max`
independently addressed leaves.  Replacing those files requires generalizing
the native library's reductions, not merely changing imports.

The FXMSS address encoder now follows `Model.address`'s canonical 22-byte flat
view, payload placement, and stateful tags 16, 17, 18, 21, and 22.  Its fields
remain abstract `nat`s; a concrete model bridge must discharge the bounds that
`Model.address.adrs` enforces intrinsically.

## Layout & logical names

Mapped in `proof/_RocqProject` (roots disjoint from `Sec`/`Model`/`Vst`/`Assumptions`):

| directory         | logical root   | contents |
|-------------------|----------------|----------|
| `fxmss/hbs/`       | `HBS`          | native compatibility exports plus the FXMSS-only framework closure |
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

A standalone probe `proof/assumptions/fxmss.v` runs `Print Assumptions
FXMSS_secure` during `make audit`.  Its cone is checked against the existing
`[ssprove]` classical baseline; no allowlist entry or trust anchor is added.

Further consolidation requires an anchor-indexed generalization of the native
WOTS+C hop interfaces.  That should be done in `Sec.lib` before the banked
multi-leaf reductions are moved, so the existing single-anchor proof remains
small and reviewable.
