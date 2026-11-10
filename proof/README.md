# The proof

The public definitions are `sha256.v`, `spec.v`, `contracts.v` and `games.v`. They state the hash, literal BIP algorithms, C contracts and security experiments without importing internal proof modules.

`internal/vst/` proves each C body, assembles its translation unit and links the four units. `contracts.v` supplies the shared CompSpecs. `internal/ssprove/shape.v` proves algorithm laws, `instance.v` instantiates the generic WOTS+C model and `security.v` transfers its correctness and reduction bound to the literal specification.

`_RocqProject` registers the sources under the Shrincs root. The standalone queries under `assumptions/` inspect the literal algorithms, generic and concrete security statements, linked C component and SHA correctness theorem. `make audit` compiles those queries and compares their assumptions with the per-tree allowlist.

The C tests and `make spec-test` use `test/spec/vectors/wots_c.kat`. The specification check evaluates every reference case in the Rocq kernel virtual machine.
