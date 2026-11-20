# libshrincs

Formally verified [SHRINCS](https://eprint.iacr.org/2025/2203) constructions. First construction: WOTS+C, the SHRINCS leaf one-time signature.

Two machine-checked proofs use the literal specification in [proof/spec.v](proof/spec.v):

- `proof/internal/vst/` proves that the C computes the specification functions, using Rocq 9.2 and VST with CompCert.
- `proof/internal/ssprove/` bounds the advantage in the known-message experiment `KOTS_vc_game` by six explicit reductions against hash games on truncated SHA-256. The concrete scheme directly calls the specification functions.

The statements and composition proofs in [proof/theorem.v](proof/theorem.v) connect both proofs. Correctness and security quantify over the node height, node index, tree balance and tree depth.

[proof/spec.v](proof/spec.v) transcribes the WOTS+C part of the shrincs-bip Python reference at commit `4fe68e3`. The C tests and kernel specification checks read the same reference vectors. [proof/contracts.v](proof/contracts.v) states the C contracts, [proof/games.v](proof/games.v) defines the security experiments and [proof/schemes.v](proof/schemes.v) instantiates them at the specification. These files and the SHA definition import no internal proof modules.

The adversary commits a message before key generation. Successful signing returns the public key and signature. Failed signing aborts the experiment. Later forgery queries succeed only for a valid signature on a different message. This is the experiment proved here. The theorem makes no equivalence claim about another security notion or about the full FXMSS construction.

The hash games use one `Th` on packed tweaks and byte sequence messages. Targets belong to static address classes. Chain targets use type 16, compression type 17 and grinding type 22. The chain and compression experiments expose `EVAL` only outside their target class, sharing the same lazily sampled public seed. The bounded grinding experiment exposes no evaluation oracle. [proof/README.md](proof/README.md) describes the oracle restrictions and byte encodings.

## Build and verify

```sh
dune build                       # C library
dune test                        # C tests and audit regressions
dune build @proof/prove          # both proof trees
dune build @proof/audit          # proofs and the honesty gate
dune build @test/spec-test       # specification vectors in the Rocq kernel
dune build @check                # source checks, sanitizers, compilers and proofs
```

The build uses three Dune files under one `dune-project`. The root [dune](dune) builds the C library per compiler configuration, [test/dune](test/dune) builds and runs the tests, and [proof/dune](proof/dune) extracts the Clight programs, compiles the proofs and runs the audit. Objects live under `_build/default`. Touching a source or restoring its contents before the next build leaves its compiled objects unchanged. A changed comment can rebuild importers because Rocq records source positions in its objects.

`dune build @proof/audit` checks source registration, proof gaps, declared assumptions, both public statement pins, their assumption cones and the public import boundary. Its trust surface report is `_build/default/proof/audit-report.txt`. The project declares no assumption. The cone holds only principles inherited from the proof libraries, recorded in [proof/audit/allowed.txt](proof/audit/allowed.txt). `dune build @proof/audit-test` runs the audit regressions and is included in `dune test` and `dune build @check`.

To regenerate the reference vectors, run `python3 test/spec/gen_vectors.py --shrincs-bip ../shrincs-bip -o test/spec/vectors/wots_c.kat`. The generated case count must match the static target list in `test/dune`.

SHA-256 is defined by the FIPS 180-4 transcription in `proof/sha256.v`. The proofs in `proof/internal/vst/sha256/` establish that `src/sha256.c` implements that definition.

## Layout

```text
include/shrincs.h        the public C interface
src/                     the C library and its internal headers
test/                    C tests, vectors and ctgrind
test/spec/               reference generator and kernel specification checks
proof/spec.v             the literal WOTS+C specification
proof/sha256.v           the FIPS 180-4 definition and word codecs
proof/contracts.v        the public C contracts and shared CompSpecs
proof/games.v            the security experiments
proof/schemes.v          the hash instances and the concrete scheme
proof/theorem.v          the public statements and composition proofs
proof/internal/common/   shared word bounds
proof/internal/vst/      functional correctness of the C
proof/internal/ssprove/  one-time security of the scheme
proof/audit/             theorem pins, source gates and assumption allowlist
proof/STYLE.md           the proof style guide
```

Start with [proof/README.md](proof/README.md) for the experiment details and proof structure.

## License

MIT. See [LICENSE](LICENSE). Copyright 2026 remix7531, remix7531@mailbox.org.
