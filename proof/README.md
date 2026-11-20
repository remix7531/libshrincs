# The proof

Read `spec.v` for the literal WOTS+C and stateful FXMSS algorithms, `sha256.v` for the FIPS 180-4 hash definition, `contracts.v` for the public C contracts, `games.v` for the security experiments and `schemes.v` for their instances at the specification. These five files import no `Shrincs.internal` module. `theorem.v` composes completed proofs over those definitions.

`spec.v` transcribes WOTS+C and stateful FXMSS from shrincs-bip `impl/shrincs.py` at commit `4fe68e3`. The C computes the WOTS+C functions. Its public interface exports key generation, signing and public key recovery, with the reference parameter order and internally constructed addresses. Signing and recovery distinguish success from failure, and their contracts leave output contents unspecified on failure. Fixed-size byte strings are tuples throughout both proofs.

The WOTS+C headline `shrincs_correct_and_secure` has three conjuncts. A successfully generated signature recovers the generated public key. The linked C component satisfies the three public contracts with no remaining imports. The advantage in the concrete KOTS experiment is bounded by the advantages of six explicit reductions against the declared hash games. Correctness and security quantify over the node height, node index, tree balance and tree depth. The standalone SHA theorem states its public complete-digest contract.

The KOTS adversary commits a message before either seed is sampled. The experiment permits one successful commit. Key generation samples the public and secret seeds, then signing either returns a signature or aborts the experiment. Only success releases the public key and signature. The public key contains the public seed and root. Subsequent `KFORGE` queries accept exactly valid signatures on messages distinct from the committed message in the real game, and always return false in the ideal game. The theorem bounds distinguishing advantage between these two games. It asserts no equivalence to an external security definition.

The FXMSS headline `shrincs_fxmss_correct_and_secure` states total key generation on legal structures, verification of honest signatures and a classical-ROM EU-CMA bound for the stateful construction. The adversary chooses a balanced tree of depth 1..64 or an unbalanced tree of depth 1..255 and a sixteen-byte partner root before key generation. The public key contains the public seed, partner root and stateful root. Signing logs every submitted context-message pair and consumes the next leaf before grinding; failure returns `None`. A forgery must verify on a pair never submitted for signing. Only `H_msg_sf` is a random oracle. This theorem does not cover the stateless fallback or an FXMSS C implementation.

The hash experiments use one `Th` on packed tweaks and byte sequence messages, returning sixteen bytes. Each experiment shares one lazily sampled public seed among its oracles. Chain targets have address type 16, compression targets type 17, tree targets type 18 and grinding targets type 22. The paired TCRX experiment pairs compression and tree tweaks. Target queries require membership in the static class. In SM-TCR, SM-PRE and SM-UD, `EVAL` requires nonmembership and accepts arbitrary byte sequence messages before or after seed revelation. Reveal closes target selection. Target budgets, distinct tweaks and the recorded target messages remain separate checks. SM-PRE and real SM-UD sample hidden sixteen-byte nodes and encode them as hash messages. Ideal SM-UD samples independent sixteen-byte outputs.

Compression encodes a list of sixteen-byte chain ends by concatenation. Its injectivity proof covers lists of every length. Grinding places the first twelve digest bytes in three big-endian tweak payload words. The message contains the remaining twenty digest bytes, four zero bytes and a two-byte counter. The encoding equation identifies this input to `Th` with `H_grind` from the literal specification. Bounded STCRP searches counters below `wots_c_counter_max` and returns the first hash passing the digit-sum test, aborting on exhaustion. Its forgery check requires a different message and an equal encoded hash, but does not require the candidate counter to be the first acceptable one. It exposes no evaluation oracle. The FXMSS option-valued STCRP game consumes a target slot and returns `None` on exhaustion; its `EVAL` oracle is restricted to tweaks outside the grinding class.

The WOTS+C budgets and reductions are explicit in its theorem. PRF uses the secret seed as its key. The reductions are `R_prf`, `R_ud`, `R_grind`, `R_compress`, `R_chain_tcr` and `R_chain_pre` under `internal/ssprove/wots/hop/`. The FXMSS reductions in `internal/ssprove/fxmss/theorem.v` are `fxmss_R_prf`, `fxmss_R_prf_msg`, `fxmss_R_grind`, `fxmss_R_ud`, `fxmss_R_chain_tcr`, `fxmss_R_chain_pre`, `fxmss_R_compress`, `fxmss_R_tree` and `fxmss_R_paired`. Its bound also includes digest-collision and random-oracle reprogramming terms. The theorem has no running-time model; its batch reductions complete hash chains after seed revelation.

`internal/vst/` proves the C bodies, builds each translation unit as a component and links them. `support/` holds helper contracts, memory lemmas and tactics. Its `base.v` reuses the shared `CompSpecs` from `contracts.v`. The private SHA clone is checked against the public SHA definition by `sha256/sync.v`, and `sha256/correct.v` identifies the exported component contract with the public one.

`internal/ssprove/` contains the generic WOTS+C model and game hops under `wots/` and the stateful FXMSS model and game hops under `fxmss/`. `hash.v` identifies the hash calls of `spec.v` with `Th` at the tweak of their address. `wots/instance.v` instantiates the model with the carriers, hashes and addresses of `spec.v`. Its proved adapters identify the model operations with the literal algorithms. `wots/security.v` transfers correctness and the reduction bound to the concrete scheme.

The C tests and WOTS+C specification checks read `test/spec/vectors/wots_c.kat`; the FXMSS specification checks read `test/spec/vectors/fxmss.kat`. The generators `test/spec/gen_vectors.py` and `test/spec/gen_fxmss_vectors.py` verify the pinned reference revision. `dune build @test/spec-test` checks each case in the kernel virtual machine.

`proof/dune` declares the single `Shrincs` theory, extracts the four Clight programs and compiles every proof source except the three standalone audit queries. Objects live under `_build/default/proof`. `proof/_RocqProject` supplies that load path to editors and MCP. The audit receives the tracked source list from the build, checks every compiled source against it, and enforces proof gaps, declared assumptions, the statement pins and assumption cones for `shrincs_correct_and_secure`, `shrincs_fxmss_correct_and_secure` and `sha256_c_correct`, the public import boundary and the protocol-abort guard pins. `dune build @proof/audit-test` exercises the scanners and gates. The allowlist in `audit/allowed.txt` records the inherited library principles. The full `dune build @check` includes both audits and the specification vectors.

## Where files go

- The top level of `proof/` is the audit surface and nothing else: `spec.v`, `sha256.v`, `contracts.v`, `games.v`, `schemes.v` and `theorem.v`. The audit applies the import boundary to every file at this level except `theorem.v`.
- `theorem.v` composes completed results. No backend proof and no public definition imports it. Every `Theorem` it states must be probed in `audit/probe.v` and pinned in `audit/statement.v`.
- `internal/ssprove/` holds one directory per scheme, `wots/` and `fxmss/`. `lib/` is independent of any scheme: it imports `games.v` and neither `spec.v` nor `schemes.v`. `hash.v` identifies the specification hashes with `Th` for every address class.
- `internal/ssprove/wots/hop/` holds the WOTS+C hash-game reductions and their perfect simulations.
- `internal/ssprove/fxmss/model/` holds tree evaluation, authentication paths, signature encodings and correctness of the specification experiment.
- `internal/ssprove/fxmss/bridge/` identifies the model and its oracles with the public stateful specification and experiment.
- `internal/ssprove/fxmss/prf/` holds the leaf-key and message-randomness PRF reductions.
- `internal/ssprove/fxmss/digest/` holds digest sampling, collision filtering and the coupling invariant.
- `internal/ssprove/fxmss/repro/` holds the random-oracle reprogramming hop and its signing invariant.
- `internal/ssprove/fxmss/leaf/` holds the WOTS+C leaf collection, batch sampling and known-message experiment.
- `internal/ssprove/fxmss/leaf/grind/` holds the option-valued grinding reduction and simulation.
- `internal/ssprove/fxmss/leaf/compress/` holds the leaf-compression SM-TCR reduction and simulation.
- `internal/ssprove/fxmss/leaf/chain_tcr/` holds the chain SM-TCR reduction and simulation.
- `internal/ssprove/fxmss/leaf/chain_pre/` holds the chain SM-PRE reduction and simulation.
- `internal/ssprove/fxmss/tree/` holds tree-forgery classification and the static tree-class SM-TCR reduction.
- `internal/ssprove/fxmss/paired/` holds the paired compression/tree TCRX reduction and simulation.
- `internal/ssprove/fxmss/bound/` holds the leaf, digest and reprogramming bounds and the canonical-forger endpoint.
- `internal/ssprove/lib/chain/` holds generic hash-chain analysis, target loops and root sampling.
- `internal/ssprove/lib/games/` holds PRF memoization, static and scheduled batches and the stateful ROM experiment.
- `internal/ssprove/lib/math/` holds binary trees, paths, Merkle folds, collision extraction and finite-map bounds.
- `internal/ssprove/lib/toolkit/` holds relational and probability rules, sampling, heap observations and random-oracle reprogramming.
- `internal/ssprove/wots/guard/` and `internal/ssprove/fxmss/guard/` hold protocol-abort guards for their scheme games; `internal/ssprove/lib/guard/` holds guards for the shared games and packages. `audit/guards.v` pins their full types and covers every game inventoried by gate 7.
- `internal/vst/` holds one directory per C translation unit, with one `body_<function>.v` per C function and a `component.v` that builds the unit. A file holds one `semax_body`, because one file is checked on one core. `sha256/verif/logical.v` is the exception, with six short proofs. `support/` holds what several units share, and `link.v` joins the units.
- `internal/vst/sha256/clone.v` is a private restatement of `sha256.v`, and `sync.v` proves that the two agree. A new derived fact about SHA-256 goes in `clone.v`, never in `sha256.v`.
- `internal/common/` holds word and byte facts that depend on neither backend.
- Every source under `proof/` is compiled into the theory, and the audit refuses one that git does not track.
- A name added to `audit/allowed.txt` changes the trust surface, and the commit message says so.

See the root [README.md](../README.md) for build targets and [STYLE.md](STYLE.md) for proof style.
