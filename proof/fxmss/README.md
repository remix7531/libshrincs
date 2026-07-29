# FXMSS proof

This tree contains the complete SSProve EU-CMA proof for FXMSS, the
counter-scheduled unbalanced Merkle signature scheme with WOTS+C leaves.

## Entry theorem

`SHRINCS.fxmss.theorem.shrincs_fxmss_secure` is the end-to-end bound. It
telescopes reductions for the secret-seed PRF, message-randomizer PRF, random
oracle reprogramming, digest collisions, grinding, leaf attacks, tree-node
SM-TCR, and structural TCRX.

The theorem is proved without admits. Its hash assumptions and security games
remain explicit advantage terms; they are not axioms.

## Library boundary

This tree holds no library of its own. Signature schemes, hash games, PRF
games, sequence sampling, Merkle/binary-tree maths, the random-oracle
toolkit and the generic chain ladder all come from `Sec.lib`, which the
native WOTS+C proof shares. The adaptive PRF game is
`Sec.lib.games.prf_adaptive`.

`Sec.lib.chain.core` is the ONE generic fixed-sum Winternitz development:
one chain fold (`Sec.lib.math.chain.chain`), one forgery classifier, one
`fixed_sum_scheme`. `Sec.lib.wots.*` carries its SM-UD/SM-TCR/SM-PRE
reductions. Both anchored ladders instantiate it: the native
`Sec.wots.hop.*` reductions fix one anchor in `wc_params`, while FXMSS
needs banked reductions over up to `n_max` independently addressed
leaves.

FXMSS and native WOTS+C share `Model.address.adrs` and the finite SSProve
encoding from `Sec.addressing`. The FXMSS facade accepts natural-number
coordinates through exact-or-zero smart constructors. Every injectivity use
proves the required field bounds. The height bound is the address's one-byte
height field, `h_sf <= 255`, matching the spec's `FXMSS_HEIGHT = 255`; the
eight-byte index field is bounded separately, per position, by the shape
well-formedness predicate `shrincs_fxmss_wf_shape` (honest side) and by the
verifier's `shrincs_fxmss_leaf_id_ok` — the spec's
`leaf_index < 2 ** min(64, leaf_depth)`.

## Layout

| Directory | Logical root | Contents |
|---|---|---|
| `fxmss/shrincs/` | `SHRINCS` | native-address FXMSS construction and security proof |

The reusable hash-based-signature, Merkle, random-oracle and fixed-sum WOTS
infrastructure this tree used to carry under `fxmss/hbs/` (logical root
`HBS`) now lives under `proof/ssprove/lib` as `Sec.lib.*`; the `HBS` root is
retired.

All physical and logical path segments below the roots use snake_case.
FXMSS-specific construction identifiers use the `shrincs_fxmss_` prefix;
paper game and reduction names retain their notation.

`wotsc/{grind_hop,compress_hop,chain_hop,zero_chain_hop,zero_games}.v` were
deleted as dead code at commit `4c47aea`; they were the closest worked
example of a single-anchor hop stack and can be recovered from git history.

## Building and trust audit

From the repository root:

```sh
make fxmss-prove   # builds just this tree (a cold run also generates Makefile.coq, which needs clightgen once)
make prove         # all four trees (model + ssprove + fxmss + vst)
make audit
```

`ssprove-prove` builds only the native `ssprove/` tree; this tree has its own
`fxmss-prove` target so it can be checked on its own.

`proof/assumptions/fxmss.v` prints the assumptions of
`shrincs_fxmss_secure`. The audit diffs that cone against its OWN `[fxmss]`
section of `proof/assumptions/allowed.txt` — the classical SSProve baseline
and nothing else (no `sha256.SHA256`, no `eps_*`, no `sha256_*_secure`) — not
against `[ssprove]`'s wider section, so FXMSS cannot silently acquire one of
ssprove's hash-game entries and stay green.
