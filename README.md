# libshrincs

Formally verified [SHRINCS](https://eprint.iacr.org/2025/2203) constructions. First construction: **WOTS+C**, the SHRINCS leaf one-time signature.

> **Status.** Proof-of-concept first construction (WOTS+C) toward full SHRINCS. The C in `src/` and its VST contracts are provisional and will change.

Two independent, machine-checked proofs over one shared model (`proof/model/`):

- **`proof/vst/`**: the C in `src/` is functionally correct (Rocq 9.2 + VST/CompCert).
- **`proof/ssprove/`**: the scheme is one-time known-message unforgeable (the valid-commit experiment `KOTS_vc_game`), reduced to standard hash assumptions (Rocq + SSProve/MathComp), and provably computes the same thing as the model the C is verified against.

## Build & verify

```sh
nix develop      # shared Rocq 9.2, MathComp 2.6 and OCaml 5.3 toolchain
make test        # C self-consistency / tamper tests + SHA-256 KATs
make prove       # both proof trees
make audit       # proofs + the honesty gate; ends with the TRUST SURFACE table
make check       # everything: static analysis, sanitizers, CompCert, ctgrind, proofs
```

`make audit` is the claim of this repository: no admitted goals, and every assumption both proofs rest on enumerated in one table, including six named hash-game axioms (declared in [`proof/ssprove/axioms.v`](proof/ssprove/axioms.v), allowlisted in [`proof/assumptions/allowed.txt`](proof/assumptions/allowed.txt)) and the inherited library baselines.

SHA-256 is defined by the FIPS 180-4 transcription in `proof/model/sha256_spec.v`. The proofs in `proof/vst/sha256/` establish that `src/sha256.c` implements that definition.

## Layout

```
src/ include/       the C library (wots.c, thash.c, sha256.c, util.c)
test/               C tests, KAT vectors, ctgrind harness
proof/model/        the shared neutral model (both proofs' common ground)
proof/vst/          functional correctness of the C
proof/ssprove/      one-time security of the scheme
proof/assumptions/  the honesty gate: per-tree probes + one allowlist
proof/STYLE.md      the proof style guide
```

Start with [`proof/README.md`](proof/README.md) for how the trees fit together and what to verify by hand; each tree's own `README.md` has its reading guide.

## License

MIT; see [`LICENSE`](LICENSE). Copyright (c) 2026 remix7531 <remix7531@mailbox.org>.
