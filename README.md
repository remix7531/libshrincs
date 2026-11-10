# libshrincs

The C library implements the BIP WOTS+C algorithms in `proof/spec.v`. Its public interface exports key generation, signing and public key recovery. The VST proofs under `proof/internal/vst/` establish the three contracts in `proof/contracts.v` and link the four translation units with no remaining imports.

The SSProve development under `proof/internal/ssprove/` proves correctness and bounds the concrete KOTS advantage through six explicit hash-game reductions. `proof/games.v` defines the common hash interface, restricted evaluation oracles and concrete signature scheme.

`make test` checks the C implementation. `make prove` builds both proof stacks, `make audit` checks their inherited assumptions and `make spec-test` checks the literal specification against the committed reference vectors. `make check` runs the compiler, sanitizer, source, proof and vector checks.

See `proof/README.md` for the proof layout and `proof/STYLE.md` for its conventions.
