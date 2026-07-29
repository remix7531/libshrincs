# The proof trees

Three native trees establish the implementation claim: the C in `../src/`
implements WOTS+C correctly, and WOTS+C is one-time known-message unforgeable
(valid-commit notion), both statements anchored to the same neutral model.  A
fourth, abstract tree proves EU-CMA security of multi-leaf FXMSS but is not yet
connected to the C/model refinement.

```
model/         the shared model: Model.wots (the scheme), Model.address,
               machine integers, the pure math island (model/math/),
               supporting theory (model/theory/), and the end-to-end
               correctness theorem (model/correct/wots.v); plus
               Model.shrincs, the definition-for-definition port of the
               normative Python spec (conventions in model/PORTING.md)
vst/           semax_body proofs relating every shrincs_wots_* C function
               to Model.wots (see vst/README.md)
ssprove/       the security games, hops, and headline theorems
               (see ssprove/README.md)
fxmss/         the abstract multi-leaf FXMSS proof and its retained
               multi-anchor reduction machinery (see fxmss/README.md)
assumptions/   the honesty gate: per-tree Print Assumptions probes
               (model.v / ssprove.v / fxmss.v / vst.v), one sectioned allowlist
               (allowed.txt), one check.sh; `make audit` runs it and
               prints the TRUST SURFACE table
STYLE.md       the unified proof style guide
```

The build lives here: `_RocqProject` + the generated `Makefile.coq`; `make -C proof <target>` (or the routing targets at the repo root).

## Cross-tree bridge points

The native VST and SSProve trees are pinned to the model at a small, reviewable
set of files; this is where "the C / the game actually computes WOTS+C" is
anchored to `Model.wots`, and it is the surface a reviewer checks to trust that
the two proofs are about the *same* scheme:

- **VST refinement**: `vst/contract/radrs.v` (the flat "under-construction" ADRS the C mutates in place, refining the dependent `Model.address.adrs`) plus the funspecs written over `Model.wots`; the `semax_body` proofs relate each `shrincs_wots_*` C function to that model.
- **Security**: `ssprove/addressing.v` (the exact tweak encoding of the model's ADRS), `ssprove/bridge.v` (the digit / chain / counter equivalences to `Model.wots`), `ssprove/axioms.v` (the concrete SHA-256 instantiation of the abstract tweakable hashes and the 6 hash-game axioms, THE trust-surface file), and `ssprove/wots/model_bridge.v` (the end-to-end games↔`Model.wots` correspondence: pubkey, counter, signing, verification).

Each tree's own `README.md` carries a "What to verify by hand" checklist for its side.

## Four skins, one concept

The same WOTS+C concept is spelled four ways across the layers: a reviewer jumping between the SSProve games, the shared model, and the C wire format should expect the name to change shape at each boundary, on purpose:

| concept              | SSProve games (`Sec.wots.*`)         | model / C-refinement (`shrincs_wots_*`)                          | C constants / wire format (`SF_SHRINCS_WOTS_*`) | dependent address ctor (`Wc_*`) |
|----------------------|---------------------------------------|-------------------------------------------------------------------|--------------------------------------------------|----------------------------------|
| address / tweak      | `shrincs_wots_chain_adrs` / `_pk_adrs` / `_prf_adrs` / `_grind_adrs` (`wots/addressing.v`, over a `nat * nat` tweak) | `shrincs_wots_hash_adrs` / `_pk_adrs` / `_prf_adrs` / `_grind_adrs` (`Model.address`) | `SF_SHRINCS_WOTS_HASH`=16 / `_PK`=17 / `_PRF`=21 / `_GRIND`=22 (type byte) | `Wc_hash` / `Wc_pk` / `Wc_prf` / `Wc_grind` |
| chain hash (`F`)     | `thf_chain` (the `thf` game instance)  | `Model.wots.F` (backs `shrincs_thash` in `src/thash.c`)            | `SF_SHRINCS_WOTS_HASH` = 16                       | `Wc_hash`                        |
| pk compression (`T_sf`) | `thf_pkcompress`                   | `Model.wots.T_sf`                                                  | `SF_SHRINCS_WOTS_PK` = 17                         | `Wc_pk`                          |
| grinding (`H_grind`) | `thf_grind`                            | `Model.wots.H_grind`, `find_counter`                               | `SF_SHRINCS_WOTS_GRIND` = 22                      | `Wc_grind`                       |
| PRF (key derivation) | `khf_prf` (the `khf` game instance)    | `Model.wots.PRF`, `shrincs_wots_derive_sk`                         | `SF_SHRINCS_WOTS_PRF` = 21                        | `Wc_prf`                         |
| scheme ops (keygen/sign/verify) | `shrincs_wots_scheme` (a `sig_scheme`: `shrincs_wots_pubkey`/`shrincs_wots_sign`/`shrincs_wots_verify` in `wots/scheme.v`) | `shrincs_wots_pubkey_gen` / `_sign` / `_verify` / `_pubkey_from_sig` (`Model.wots`, refining `src/wots.c` 1:1) | `SHRINCS_WOTS_PK_BYTES`=16, `SHRINCS_WOTS_SIG_BYTES`=514 | n/a (caller-supplied base address) |

`shrincs_wots_hash_adrs` (model) and `shrincs_wots_chain_adrs` (Sec) look like the same name reused, but are not: different arity, different type; see the "one concept, one name" note in `STYLE.md` for why that pair is a documented exception. The full naming rationale (casing table, suffix conventions, instantiation namespaces) is canonical in `STYLE.md`.

## Known findings

Load-bearing negative results and open gaps, so a reader does not re-derive
them. Each is a *deliberate* state of the tree, not an oversight.

- **The native WOTS+C ladder is NOT demoted to a corollary of the FXMSS leaf
  bound (NO-GO).** The tempting simplification — drop `ssprove/wots/hop/*` and
  re-derive `shrincs_wots_secure*` from `Leaf_MIW_km_bound` at `n_max = 1` via
  the `KOTS_vc` ↔ `MIW_kmS` link lemma — was probed mechanically and rejected on
  three blockers. (1) *Digit order*: the two schemes are the same generic
  `Sec.lib.wots.wotsc` construction at different `dig_msb`, native `true` vs
  FXMSS `false`; every other argument, including all three anchored addresses,
  coincides by conversion. (2) *Collections*: the five banked leaf collections
  (`CUD_leaf`, `CFl_leaf` ×2, `CPl_leaf`, `CGl_leaf`) are strict **supersets** of
  the native 2-member `coll_chain`/`coll_pkcompress`/`coll_grind` — they carry
  the FXMSS tree hash `Htree`, which WOTS+C does not have. Demoting would
  therefore silently **strengthen** the six hash-game axioms (each quantified
  over a larger collection) while **weakening** nothing in the headline
  theorem's favour: the same axiom name would stand for a strictly stronger
  assumption. (3) *Budgets/anchors* do not line up at `n_max = 1` without
  restating the frozen native statements. The native ladder is kept on purpose;
  the P7 link lemma remains as the stated (unused-by-the-headline) bridge.
  Probes archived at scratchpad `p8-evidence/` (`p8_baseline.v`,
  `p8_demote_probe.v`, `p8_probe_a.v`, `p8_probe_b1.v`, `p8_probe_b1b.v`,
  `p8_probe_b2.v`).
- **`dig_msb` divergence.** `Sec.lib.wots.wotsc` is parameterized by
  `dig_msb : bool`; the native wrapper instantiates it MSB-first (`true`,
  matching the spec, `Model.wots` and the C), the FXMSS wrapper LSB-first
  (`false`). This is benign for every statement the two trees actually make —
  both are pk-level (public key / forgery) claims, and the digit order is an
  internal bookkeeping convention that both sides use consistently — but it is
  the reason the two schemes are not convertible. Unifying it is possible but
  re-orders digits inside the ~12.5k lines of `leaf2_*` target bookkeeping, so
  it is only worth bundling into a window that already rebuilds those
  transcripts.
- **FXMSS model bridge coverage.** `ssprove/fxmss/model_bridge.v` establishes
  agreement at the *verification* level (the game's verifier and
  `Model.fxmss`'s agree). Two lemmas are open: the **auth-path signing
  agreement** lemma, and the **leaf-schedule permutation** lemma (the games walk
  the leaf schedule left-to-right, the spec's `leaf_select` right-to-left; the
  two are a permutation of each other). Neither is needed for the FXMSS EU-CMA
  headline, which is stated over the games; both are needed before the FXMSS
  tree can be anchored to the C the way the native tree is.
- **Upstream spec bug (to be reported).** `shrincs.py:1245-1249`: at depth 0 the
  UXMSS `leaf_select` returns `(1, 254)` instead of `None`. The two
  formalizations deliberately disagree here: `Model.fxmss.fxmss_leaf_select`
  follows the *intended* behaviour (`None`), while `Model.shrincs`, being a
  transcription of the spec, reproduces the bug (`Some (1, 254)`) with a
  comment at the site. They agree at every depth the spec's own parameter sets
  reach, so this is a latent bug rather than a live one.
