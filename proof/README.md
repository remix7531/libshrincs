# The proof trees

The shared neutral model supports the C correctness proof. The generic WOTS+C security reductions bound one-time known-message forgery advantage against the public hash games.

```
internal/common/ the shared model: Shrincs.internal.common.wots (the scheme), Shrincs.internal.common.address,
               machine integers, the pure math island (internal/common/math/),
               supporting theory (internal/common/theory/), and the end-to-end
               correctness theorem (internal/common/correct/wots.v), and the
               FIPS 180-4 definition (sha256.v)
internal/vst/  semax_body proofs relating every shrincs_wots_* C function
               to Shrincs.internal.common.wots (see internal/vst/README.md)
internal/ssprove/ the security games, hops, and headline theorems
assumptions/   the honesty gate: per-tree Print Assumptions probes
               (model.v / ssprove.v / vst.v), one sectioned allowlist
               (allowed.txt), one check.sh; `make audit` runs it and
               prints the TRUST SURFACE table
STYLE.md       the unified proof style guide
```

The build lives here: `_RocqProject` + the generated `Makefile.coq`; `make -C proof <target>` (or the routing targets at the repo root).

## Cross-tree bridge points

The C proofs and security reductions have explicit interfaces for review:

- **VST refinement**: `internal/vst/support/contract/radrs.v` (the flat "under-construction" ADRS the C mutates in place, refining the dependent `Shrincs.internal.common.address.adrs`) plus the funspecs written over `Shrincs.internal.common.wots`; the `semax_body` proofs relate each `shrincs_wots_*` C function to that model.
- **SHA-256**: `sha256.v` defines the hash, `internal/common/sha256.v` wraps it in the model byte types, and `internal/vst/sha256/correct.v` proves that the C component implements the canonical contract. `internal/vst/sha256/sync.v` checks that the proof-side definitions match the specification.
- **Security**: `games.v` defines the public experiments. `internal/ssprove/wots/params.v` gives the generic model one hash interface, encodings and static target classes. `internal/ssprove/wots/theorem.v` bounds forgery advantage using constructed reductions.
- **Literal instance**: `internal/ssprove/instance.v` supplies the parameter record and proves adapters to `spec.v`. `internal/ssprove/security.v` transfers correctness and the security bound to the literal WOTS+C functions.

`internal/vst/README.md` describes the C proof and its review points.
