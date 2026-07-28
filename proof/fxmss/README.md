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

The proof reuses compatibility exports of `Sec.lib` for signature schemes,
hash games, PRF games, and sequence sampling. The adaptive PRF game used by
FXMSS is provided by `Sec.lib.games.prf_adaptive`.

`HBS.wots.*` is reusable fixed-sum Winternitz proof infrastructure. Its chain
analysis and SM-UD/SM-TCR/SM-PRE reductions are used by the
multi-leaf proof. The native `Sec.wots.hop.*` reductions fix one anchor in
`wc_params`; FXMSS instead needs banked reductions over up to `n_max`
independently addressed leaves.

FXMSS and native WOTS+C share `Model.address.adrs` and the finite SSProve
encoding from `Sec.addressing`. The FXMSS facade accepts natural-number
coordinates through exact-or-zero smart constructors. Every injectivity use
proves the required field bounds; in particular, the headline theorem assumes
`h_sf <= 64`.

## Layout

| Directory | Logical root | Contents |
|---|---|---|
| `fxmss/hbs/` | `HBS` | reusable HBS, Merkle, random-oracle, and fixed-sum WOTS infrastructure |
| `fxmss/shrincs/` | `SHRINCS` | native-address FXMSS construction and security proof |

All physical and logical path segments below the roots use snake_case.
FXMSS-specific construction identifiers use the `shrincs_fxmss_` prefix;
paper game and reduction names retain their notation.

## Building and trust audit

From the repository root:

```sh
make ssprove-prove
make prove
make audit
```

`proof/assumptions/fxmss.v` prints the assumptions of
`shrincs_fxmss_secure`. The audit checks that cone against the existing
SSProve baseline and adds no FXMSS-specific allowlist entry.
