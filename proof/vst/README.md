# WOTS+C Formally Verified (VST)

Machine-checked functional-correctness proof of a C implementation of
**WOTS+C** — the grinding / constant-sum Winternitz variant that
replaces RFC 8391 WOTS+'s checksum chains with a search for a counter
that maps the message to base-`w` digits of a fixed sum — using VST on
Rocq 9.0 + CompCert.

## What is proved

- Gallina model of WOTS+C key generation, signing (grinding search),
  and verification, with a top-level round-trip theorem `wots_correct`.
- VST `semax_body` proofs for every C function against funspecs over that
  model, including the grinding loop — the WOTS+C scheme steps (`shrincs_wots_*`
  in `src/wots.c`) and the shared SHRINCS tweakable hash (`shrincs_thash` /
  `shrincs_adrs_put32` in `src/thash.c`, its own Clight TU like `sha256`).
  The `pubkey_from_sig`/`verify` POSTs state the residual ADRS buffer
  *exactly* (`shrincs_wots_pk_adrs a` when the digest at that counter is
  constant-sum, else `shrincs_wots_grind_adrs a`) rather than behind an
  existential — the C code is deterministic there, so the spec says so;
  `sign` keeps an existential since its residual genuinely depends on the
  ground counter found by grinding.
- Zero `Admitted.`. Trusted base: two SHA-256 assumptions — `Parameter SHA256`
  (the abstract hash in the shared model) and `Axiom body_sha256` (the C `sha256`
  function meets its funspec).

Scope: functional correctness, not EU-CMA. One-time use is a caller
obligation.

## Parameters

`n=16`, `w=16`, `len=32`, constant digit-sum target `S=240`, counter
search space `c_max=2^16`, hash `SHA-256` truncated to 16 bytes. The
16-bit big-endian grinding counter is prepended to the signature.

- `SHRINCS_WOTS_PK_BYTES  = 16` (`T_sf` compression of the chain tips)
- `SHRINCS_WOTS_SIG_BYTES = 514` (2-byte counter + `len * n` = `2 + 32*16`)

This is the SHRINCS stateful (FXMSS) leaf construction: every tweakable
hash is `SHA-256(pk_seed ‖ zeros(48) ‖ ADRS ‖ M)[:16]` (no bitmasks), and
domain separation lives in a 22-byte `ADRS`. `test/wots/vectors/wotsc.kat`
(regenerable with `make gen-vectors`) cross-checks the compiled C against
the authoritative Python reference `shrincs-bip/impl/shrincs.py`
byte-for-byte — pk, sig, counter, digits, and an `H_grind` intermediate.

## Build

Run from the repo root (`libshrincs/`):

```
nix develop .#vst   # devshell with CompCert, VST, rocq-mcp
make                # build the C library (build/libwots.a) only
make test           # self-consistency + tamper suite + SHA-256 KATs/CAVS
make extract        # clightgen: C -> Clight AST for vst-prove
make vst-prove      # VST / Rocq proofs for this tree
make check          # full CI gate: static + sanitizers + CompCert + ctgrind
                     #               + extract + prove (both trees) + audit
make check-ct       # ctgrind constant-time check (gcc + clang + CompCert)
make clean
```

## Layout

```
include/                  wots.h, thash.h, sha256.h, util.h
src/                       wots.c, thash.c, sha256.c, util.c
test/                      runner.c, common.{c,h}
test/wots/                 wots.c, gen_vectors.py, vectors/
test/sha256/                sha256.c, vectors/
test/ctgrind/                ctgrind.c
proof/vst/                 model/, contract/, verif/, clight/
```

## Side channels

`shrincs_wots_verify` and `shrincs_wots_pubkey_from_sig` operate only on public
inputs (`pk`, `sig`, `msg`, `pk_seed`), so their timing is not
security-relevant. `shrincs_wots_sign` and `shrincs_wots_pubkey_gen` consume
`sk_seed`; both are checked under `make check-ct` (valgrind/ctgrind
with `sk_seed` marked uninitialized) against gcc, clang, and
CompCert builds. The grinding loop's trip count depends on `msg`,
which is public, so it does not leak `sk_seed`. This rules out
secret-dependent branches and secret-dependent memory addresses on
the paths actually exercised, but is not a proof.

## License

MIT. See the repository-root `LICENSE`.
