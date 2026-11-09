# The proof trees

Three trees, one claim: the C in `../src/` implements WOTS+C correctly, and WOTS+C is one-time known-message unforgeable (valid-commit notion), both statements anchored to the same neutral model.

```
internal/common/ the shared model: Shrincs.internal.common.wots (the scheme), Shrincs.internal.common.address,
               machine integers, the pure math island (internal/common/math/),
               supporting theory (internal/common/theory/), and the end-to-end
               correctness theorem (internal/common/correct/wots.v), and the
               FIPS 180-4 definition (sha256.v)
internal/vst/  semax_body proofs relating every shrincs_wots_* C function
               to Shrincs.internal.common.wots (see internal/vst/README.md)
internal/ssprove/ the security games, hops, and headline theorems
               (see internal/ssprove/README.md)
assumptions/   the honesty gate: per-tree Print Assumptions probes
               (model.v / ssprove.v / vst.v), one sectioned allowlist
               (allowed.txt), one check.sh; `make audit` runs it and
               prints the TRUST SURFACE table
STYLE.md       the unified proof style guide
```

The build lives here: `_RocqProject` + the generated `Makefile.coq`; `make -C proof <target>` (or the routing targets at the repo root).

## Cross-tree bridge points

Both proof trees are pinned to the model at a small, reviewable set of files; this is where "the C / the game actually computes WOTS+C" is anchored to `Shrincs.internal.common.wots`, and it is the surface a reviewer checks to trust that the two proofs are about the *same* scheme:

- **VST refinement**: `internal/vst/support/contract/radrs.v` (the flat "under-construction" ADRS the C mutates in place, refining the dependent `Shrincs.internal.common.address.adrs`) plus the funspecs written over `Shrincs.internal.common.wots`; the `semax_body` proofs relate each `shrincs_wots_*` C function to that model.
- **SHA-256**: `sha256.v` defines the hash, `internal/common/sha256.v` wraps it in the model byte types, and `internal/vst/sha256/correct.v` proves that the C component implements the canonical contract. `internal/vst/sha256/sync.v` checks that the proof-side definitions match the specification.
- **Security**: `internal/ssprove/addressing.v` (the exact tweak encoding of the model's ADRS), `internal/ssprove/bridge.v` (the digit / chain / counter equivalences to `Shrincs.internal.common.wots`), `internal/ssprove/axioms.v` (the concrete SHA-256 instantiation of the abstract tweakable hashes and the 6 hash-game axioms, THE trust-surface file), and `internal/ssprove/wots/model_bridge.v` (the end-to-end games↔`Shrincs.internal.common.wots` correspondence: pubkey, counter, signing, verification).

Each tree's own `README.md` carries a "What to verify by hand" checklist for its side.

## Four skins, one concept

The same WOTS+C concept is spelled four ways across the layers: a reviewer jumping between the SSProve games, the shared model, and the C wire format should expect the name to change shape at each boundary, on purpose:

| concept              | SSProve games (`Shrincs.internal.ssprove.wots.*`)         | model / C-refinement (`shrincs_wots_*`)                          | C constants / wire format (`SF_SHRINCS_WOTS_*`) | dependent address ctor (`Wc_*`) |
|----------------------|---------------------------------------|-------------------------------------------------------------------|--------------------------------------------------|----------------------------------|
| address / tweak      | `shrincs_wots_chain_adrs` / `_pk_adrs` / `_prf_adrs` / `_grind_adrs` (`wots/addressing.v`, over a `nat * nat` tweak) | `shrincs_wots_hash_adrs` / `_pk_adrs` / `_prf_adrs` / `_grind_adrs` (`Shrincs.internal.common.address`) | `SF_SHRINCS_WOTS_HASH`=16 / `_PK`=17 / `_PRF`=21 / `_GRIND`=22 (type byte) | `Wc_hash` / `Wc_pk` / `Wc_prf` / `Wc_grind` |
| chain hash (`F`)     | `thf_chain` (the `thf` game instance)  | `Shrincs.internal.common.wots.F` (backs `shrincs_thash` in `src/thash.c`)            | `SF_SHRINCS_WOTS_HASH` = 16                       | `Wc_hash`                        |
| pk compression (`T_sf`) | `thf_pkcompress`                   | `Shrincs.internal.common.wots.T_sf`                                                  | `SF_SHRINCS_WOTS_PK` = 17                         | `Wc_pk`                          |
| grinding (`H_grind`) | `thf_grind`                            | `Shrincs.internal.common.wots.H_grind`, `find_counter`                               | `SF_SHRINCS_WOTS_GRIND` = 22                      | `Wc_grind`                       |
| PRF (key derivation) | `khf_prf` (the `khf` game instance)    | `Shrincs.internal.common.wots.PRF`, `shrincs_wots_derive_sk`                         | `SF_SHRINCS_WOTS_PRF` = 21                        | `Wc_prf`                         |
| scheme ops (keygen/sign/verify) | `shrincs_wots_scheme` (a `sig_scheme`: `shrincs_wots_pubkey`/`shrincs_wots_sign`/`shrincs_wots_verify` in `wots/scheme.v`) | `shrincs_wots_pubkey_gen` / `_sign` / `_verify` / `_pubkey_from_sig` (`Shrincs.internal.common.wots`, refining `src/wots.c` 1:1) | `SHRINCS_WOTS_PK_BYTES`=16, `SHRINCS_WOTS_SIG_BYTES`=514 | n/a (caller-supplied base address) |

`shrincs_wots_hash_adrs` (model) and `shrincs_wots_chain_adrs` (Sec) look like the same name reused, but are not: different arity, different type; see the "one concept, one name" note in `STYLE.md` for why that pair is a documented exception. The full naming rationale (casing table, suffix conventions, instantiation namespaces) is canonical in `STYLE.md`.
