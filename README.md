# libshrincs

Formally verified [SHRINCS](https://eprint.iacr.org/2025/2203) constructions. First construction: **WOTS+C**, the SHRINCS leaf one-time signature.

> **Status.** Proof-of-concept first construction (WOTS+C) toward full SHRINCS. The C in `src/` and its VST contracts are provisional and will change.

The C correctness proof and the generic security reductions are machine-checked:

- **`proof/internal/vst/`**: the C in `src/` is functionally correct (Rocq 9.2 + VST/CompCert).
- **`proof/internal/ssprove/`**: generic WOTS+C one-time known-message security is bounded by explicit reductions against the hash games in `proof/games.v`.

## Build & verify

```sh
nix develop      # shared Rocq 9.2, MathComp 2.6 and OCaml 5.3 toolchain
make test        # C self-consistency / tamper tests + SHA-256 KATs
make prove       # both proof trees
make audit       # proofs + the honesty gate; ends with the TRUST SURFACE table
make check       # everything: static analysis, sanitizers, CompCert, ctgrind, proofs
```

`make audit` checks proof gaps and enumerates the inherited library assumptions in [`proof/assumptions/allowed.txt`](proof/assumptions/allowed.txt). The security bound constructs each reduction and states its advantage explicitly.

SHA-256 is defined by the FIPS 180-4 transcription in `proof/sha256.v`. The proofs in `proof/internal/vst/sha256/` establish that `src/sha256.c` implements that definition.

## Layout

```
src/ include/       the C library (wots.c, thash.c, sha256.c, util.c)
test/               C tests, KAT vectors, ctgrind harness
proof/internal/common/        the shared neutral model (both proofs' common ground)
proof/internal/vst/          functional correctness of the C
proof/internal/ssprove/      one-time security of the scheme
proof/assumptions/  the honesty gate: per-tree probes + one allowlist
proof/STYLE.md      the proof style guide
```

Start with [`proof/README.md`](proof/README.md) for how the trees fit together and what to verify by hand.

## License

MIT; see [`LICENSE`](LICENSE). Copyright (c) 2026 remix7531 <remix7531@mailbox.org>.
