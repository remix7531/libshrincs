# Porting `shrincs.py` to `Model.shrincs`

`proof/model/shrincs.v` is a port of the normative Python spec,
`shrincs-bip/impl/shrincs.py` — same function names, same argument names,
same definition order, same section structure. This file is the complete
list of places where that is not literally possible, one row per Python
construct, so a reviewer holding the two files side by side never has to
guess whether a difference is deliberate.

The port is **complete**: all 50 of the spec's functions, in the spec's
order, under the spec's own section headings. The spec uses no classes, no
dataclasses, no dicts, no sets, no comprehensions with `if`, no string
formatting, no exceptions other than bare `assert`/`raise`, and no library
beyond `math.ceil`/`math.floor`, `hashlib.sha256` and `typing.Optional` —
so the construct table below is exhaustive for this spec, not merely for
the part that happened to be ported first.

Two rules govern everything below:

1. **Definitions only.** No lemmas, no dependent types, no invariants
   pushed into types, no `fin`. The port is a transcription; everything one
   may *conclude* about it goes in a theory file above it. This is a
   deliberate break from the dependent-typed models that preceded this
   one (`Model.wots` / `Model.fxmss`, both since retired), which encoded
   bounds in types and paid for it in every definition.
2. **The Python-facing signature is the spec's signature.** Every ported
   function takes and returns what the Python takes and returns, at `Z` and
   `bytes`. Gallina's structural-recursion requirement is absorbed by a
   `fold_left` over the loop's own `range`, or confined to a `*_loop`
   helper; it never leaks into a spec function's type.

## Types and values

| Python | Gallina | why |
|---|---|---|
| `bytes`, `bytearray` | `Notation bytes := (list byte)`, with `byte = Model.byte.byte` | one representation for both. `Model.byte.byte` is the repo's existing 8-bit modular integer (`machine.Byte.int`), which is what `Model.sha256.SHA256` already consumes and produces — using anything else would need a conversion at every hash call. `byte_val : byte >-> Z` is a coercion, so `x[j]` reads as an integer without ceremony. |
| `int` | `Z` | Python ints are unbounded and signed (`state_ctr` is explicitly allowed to be negative), which is exactly `Z`. `nat` would be wrong for `state_ctr` and unusable for literals like `2^61 - 1` (`lia` cannot see through `nat`'s abstract-large-number notation — see `model/bounded.v`'s header). |
| `Optional[X]` | `option X` | direct, in both directions: as a return type (`wots_c_map_digest`) and as a parameter (`slh_dsa_sign`'s `opt_rand`, matched with `match ... with None => ... end`). |
| `tuple[A, B]`, `tuple[A, B, C]` | `A * B`, `A * B * C` | direct; `(a, b, c)` on both sides. Destructuring assignment (`a, b, c = f(...)`) is `let '(a, b, c) := f ... in`. |
| `b""` | `[]` | the empty byte string; `sig += x` on an accumulator is `sig ++ x`. |
| `list[int]` | `list Z` | direct. |
| `list[bytes]` | `list bytes` | direct. |
| `bool` | `bool` | `bool`, not `Prop`: the spec's conditions are decidable tests and are used as such. `Bool` is imported so `&&` / `\|\|` / `negb` resolve under an open `Z_scope`. |

## Byte-string syntax

Python gets these from `bytes` / `bytearray` syntax; Gallina needs named
functions. They are the "Python-to-Gallina plumbing" section at the top of
`shrincs.v` — the only definitions in the file with no Python counterpart.

| Python | Gallina | notes |
|---|---|---|
| `x[i]` | `index x i : Z` | Python raises `IndexError` out of range; `index` reads `0`. |
| `l[i]` at a `list[int]` | `index_int l i : Z` | the `base_2b` index vectors. Same out-of-range convention. |
| `x == y` at byte strings | `bytes_eqb x y : bool` | `list_eq_dec byte_eq_dec`. |
| `x[i:j]` | `slice x i j` | out-of-range endpoints clip, as Python's own slicing does. `x[:k]` is `slice x 0 k`. |
| `x[i:j] = v` | `set_slice x i j v` | a functional update that keeps the Python slice indices verbatim: `firstn i x ++ v ++ skipn j x`. Every slice assignment in the spec has `len v = j - i` (Python would otherwise resize the bytearray); at other lengths `set_slice` splices, Python resizes. |
| `x[i] = v` | `set_index x i v` | `set_slice x i (i+1) [byte_mod256 v]`. Python raises `ValueError` outside `[0,256)`; `byte_mod256` truncates. |
| `x + y` | `x ++ y` | direct. |
| `n.to_bytes(k)` | `to_bytes n k` | big-endian, which is `int.to_bytes`'s default byte order. Python raises `OverflowError` when `n` does not fit; `to_bytes` truncates (each byte is `byte_mod256`). |
| `int.from_bytes(x)` | `from_bytes x` | big-endian, same defaulting. (Not yet in the sample — first needed by `wots_c_pubkey_from_sig`.) |
| `len(x)` | `len x : Z` | `Z.of_nat (length x)`. |
| `sum(l)` | `sum_list l : Z` | not named `sum`: that is Rocq's disjoint-union type former. |
| `zip(s1, s2)` | `combine s1 s2` | both truncate to the shorter argument. A pattern lambda over a `combine` needs its type written out (`fun '((b1, b2) : byte * byte) => ...`), otherwise the `byte >-> Z` coercion has nothing to fire on. |

## Arithmetic

Python's `//` and `%` round toward minus infinity and take the divisor's
sign; `Z.div` / `Z.modulo` do exactly the same (`Z.quot` / `Z.rem`, the
truncating pair, are the wrong ones).

| Python | Gallina |
|---|---|
| `a // b` | `a / b` |
| `a % b` | `a mod b` |
| `a ** b` | `a ^ b` |
| `a << b`, `a >> b` | `Z.shiftl a b`, `Z.shiftr a b` |
| `a ^ b` (xor) | `Z.lxor a b` |
| `floor(a / b)` (nonneg ints) | `a / b` |
| `ceil(a / b)` (nonneg ints) | `(a + b - 1) / b` |
| `a == b`, `a < b`, `a <= b`, `a > b`, `a >= b` | `a =? b`, `a <? b`, `a <=? b`, `a >? b`, `a >=? b` |
| `a <= b <= c` (chained) | `(a <=? b) && (b <=? c)` |
| `min(a, b)` | `Z.min a b` |
| `0x36`, `0xFF` | `0x36`, `0xFF` — Rocq accepts hex `Z` literals, so the spec's spelling survives |

`floor` / `ceil` appear only in the derived-constants block, applied to
float division of nonnegative integer literals, so the rewrite above is
exact there. All 24 constants are checked numerically against the Python.

## Control flow

**There are no fuel parameters and no invented budgets in the port.** A
Python loop is either a fold over its own `range`, or — when it returns out
of the middle — a recursion on a quantity the spec itself decrements. Those
are the only two shapes.

| Python | Gallina | notes |
|---|---|---|
| `range(a, b)`, `range(n)` | `range a b`, `range 0 n` | a plumbing helper: `map (fun k => a + Z.of_nat k) (seq 0 (Z.to_nat (b - a)))`. Empty when `b <= a`, as Python's is. |
| `for i in range(...): ...` | `fold_left (fun '(<acc>) i => ...) (range ...) <init>` | **shape 1, the default.** The loop variable keeps its Python name as the fold's second binder; the loop-carried variables keep their Python names as the accumulator pattern. `wots_chain_iter`, `wots_c_pubkey_gen` and `base_2b`'s outer loop are all this. |
| loop-carried variables | the fold's accumulator, same names | `node`, `ADRS`, `wots_pk`, `j`, `acc`, `bits_filled`. A tuple accumulator is destructured with `fun '(a, b, c) => ...`, which nests left, matching `((a, b), c)`. |
| a loop that returns only some of its state | project the fold's result | `wots_chain_iter` ends in `fst (fold_left ...)`: the spec returns `node`, not `ADRS`. |
| `baseb[i] = e` inside a `for` | `baseb ++ [e]` in the accumulator | the pre-sized output array (`[0] * outlen`, `[b''] * N`) has no counterpart; the accumulator grows in the spec's own index order. |
| `for ...: ... return e` (early exit) | `Fixpoint <name>_loop (<quantity> : nat) ...` | **shape 2**, used only when the spec returns out of the middle of the loop and the *first* hit is the point of the function. The recursion is structural on the quantity the loop decrements, and the parameter is **named after that quantity** — never `fuel`. `wots_c_grind_to_constant_sum_loop`'s is `remaining`: the number of counters left in the spec's own `range(2**16)` span. |
| `while c: ...` | shape 2, on the quantity `c` measures | the only one is `base_2b`'s inner `while bits_filled < b`. Each iteration adds exactly 8 bits, so `ceil((b - bits_filled) / 8)` is the loop's *exact remaining trip count*, not an upper bound; the parameter is `bytes_to_read` and the caller recomputes it from its own `bits_filled` on entry. |
| a recursive function on a height | shape 2, on the height itself | `fxmss_node_loop (node_height : nat)`, structural on `node_height` because that is what the spec decrements (`child_height = node_height - 1`). It is the *same* `node_height` the spec passes, at `nat` rather than `Z`; `fxmss_node` converts once on the way in, so there is no second copy to keep in sync. Reaching `O` in a non-leaf branch is exactly where the spec's recursion runs away. |
| nested `for` loops | nested folds over the two `range`s | `fors_sign` and `fors_pubkey_from_sig`; the shared accumulator (`sig`, or `offset`) passes through the inner fold's initial value and out of its result, so the two loops consume/produce in exactly the spec's order. |
| a loop that reassigns the function's own parameters | those parameters ride the accumulator | `hypertree_sign`/`hypertree_verify` reassign `message`, `leaf_index` and `tree_index`; note `leaf_index` is recomputed from the OLD `tree_index`, before the shift, and the fold preserves that. |
| early `return` | a nested `if ... then ... else ...` chain, in the spec's order | e.g. `shrincs_sf_leaf_select` and `shrincs_verify`: each `return` becomes a `then` branch and the fall-through becomes the trailing `else`. |
| `if / elif / else` | `if / else if / else` | direct. |
| `raise` | `None`, or a documented default | see the next section. |
| `assert` | see the next section. |

If a future loop has **no** spec-stated decreasing quantity, that is a
finding to report, not a place to invent a budget.

## `assert` and `raise`

The policy, in order of preference:

1. **The function is already `Optional`** (`wots_c_map_digest`,
   `wots_c_pubkey_from_sig`, `fxmss_pubkey_from_sig`,
   `shrincs_sf_leaf_select`): the failure is `None`. No decision to make.
2. **The function can `raise` on input it is reachable with**
   (`wots_c_grind_to_constant_sum`'s `raise RuntimeError("Unreachable")`):
   the return type becomes `option`, and the raise is `None`. This is the
   only signature change in the port, and it matches what
   the predecessor model's `find_counter` already did.
3. **The `assert` is a sanity check on a well-formedness the callers
   guarantee**: it becomes a *caller obligation*, stated in the ported
   docstring, and the body stays total. The total behaviour is whatever the
   plumbing already does — `index` reads `0` past the end, `to_bytes`
   truncates — never a new special case.
4. **The `assert` guards a genuine crash and the return type is not
   `Optional`** (`fxmss_node`'s two anti-infinite-recursion asserts): it
   becomes an explicit branch returning a documented default, `zeros 16`
   (a 16-byte hash, the function's own return shape). Each such site is
   named in the function's doc comment.

Every `assert` and `raise` in the spec — all 12 — with its verdict:

| site | Python | verdict |
|---|---|---|
| `xor` | `len(s1) == len(s2)` | (3) caller obligation; `combine` stops at the shorter, as `zip` does. |
| `base_2b` | `len(x) >= ceil(outlen * b / 8)` | (3) caller obligation; a short `x` reads as zero bytes. |
| `hmac_sha256` | `len(key) <= 64` | (3) caller obligation; `zeros (64 - len key)` is empty and `xor` stops at 64. |
| `H_grind` | `counter <= 0xFFFF` | (3) caller obligation, and unreachable from the spec's own callers (`counter` is a loop index below `2**16` or two bytes off a signature). |
| `wots_c_grind_to_constant_sum` | `raise RuntimeError("Unreachable")` | (2) `option (Z * list Z)`. The only signature change in the port. |
| `wots_c_sign` | (inherits the above through destructuring) | (4) `None` arm returns `zeros (2 + WOTS_C_CHAINS_SIZE)`, keeping the spec's signature. |
| `fxmss_node` | `node_index == 0` (UXMSS), `node_depth < tree_depth` (BXMSS) | (4) explicit branch, `zeros 16`. |
| `fxmss_sign` | `leaf_index == 1 or leaf_depth == tree_depth` (UXMSS), `leaf_depth == tree_depth` (BXMSS) | (4) explicit branch, `zeros (2 + WOTS_C_CHAINS_SIZE + 16 * leaf_depth)` — the length the docstring states. |
| `fxmss_pubkey_from_sig` | `leaf_index < 2 ** min(64, leaf_depth)` | (1) the function is already `Optional`, so it is `None`. |
| `slh_dsa_sign` | `len(ctx) < 256` | (3) caller obligation; `to_bytes (len ctx) 1` truncates. |
| `slh_dsa_verify` | `len(ctx) < 256` | (3) caller obligation, as above. |
| `shrincs_keygen` | `len(seed) == 48`, `len(sf_structure) == 2` | (3) caller obligations; a short `seed` slices short and a short `sf_structure` reads as zeros. |

Only two of the twelve change observable behaviour on input the spec's own
callers can produce, and both are (4) branches whose condition the spec
itself computes: `fxmss_node`'s and `fxmss_sign`'s tree-shape checks. The
rest are either already `Optional`, or guards on well-formedness that only
a caller outside the spec can violate.

## Mutation: the `ADRS` bytearray

This is the only place the port is not a literal transcription, and it is
the one convention to check when reviewing.

Python's `ADRS` is a caller-owned `bytearray(22)` that every callee mutates
**in place**. Since a ported function keeps the spec's signature, a
callee's mutations are not visible to its caller. That is sound throughout
the spec because no `ADRS` field is ever read across a call boundary: every
consumer writes each field it hashes before hashing it. Concretely:

- **Within a function**, `ADRS` is threaded by shadowing `let`s, in the
  spec's statement order, so a write is visible to everything after it:
  `let ADRS := set_index ADRS 9 SF_WOTS_C_PRF in ...`.
- **Through a loop**, `ADRS` rides in the fold's accumulator, so a write
  made in one iteration is visible to the next and to the statements after
  the loop (`wots_c_pubkey_gen`). Nothing is lost inside a function.
- **Out of a function**, it is always dropped — the signature forces it.
  Each call site where the caller goes on to use `ADRS` carries a comment
  naming the fields the callee wrote and why they are overwritten
  (`wots_c_pubkey_gen`'s `wots_chain_iter` call; `fxmss_node_loop`'s two
  recursive calls).

**The check has been carried out at all 50 functions** — see the appendix
at the end of this file. It holds everywhere. Two sites are genuinely
load-bearing rather than vacuous, and both carry a comment in the source.

## SHA-256

The spec calls `hashlib.sha256`. The port's `sha256` is
`Model.sha256.SHA256`, the repo's single trust anchor — a `Parameter`
whose *type* already carries both facts the spec's docstring states:

```coq
Parameter SHA256 : BList.t byte sha256_max_input_len -> Vec.t byte hash_bytes.
```

`BList.clip` injects a plain `bytes` into that input type and `Vec.to_list`
projects the output back out, so the port's `sha256 : bytes -> bytes` has
the spec's signature. The clip never truncates anything a real SHRINCS call
produces; it exists only to satisfy `SHA256`'s type without threading a
length invariant through the file. This is exactly what the predecessor
model already did.

Everything above `sha256` is an ordinary ported definition, not a new
assumption:

| spec | port |
|---|---|
| `sha256` | `Model.sha256.SHA256` via `BList.clip` / `Vec.to_list` |
| `hmac_sha256` | `xor` + `repeat` + two `sha256` calls, as written |
| `T_sl`, `T_sf`, `T_k`, `F`, `H` | `slice (sha256 (pk_seed ++ zeros 48 ++ ADRS ++ M)) 0 16` — five separate definitions, as in the spec, even though they are convertible |
| `H_grind` | `slice (sha256 (... ++ slice ADRS 0 10 ++ ...)) 0 16` |
| `PRF`, `H_msg_sl`, `H_msg_sf`, `PRF_msg_sl`, `PRF_msg_sf` | ditto, from `sha256` / `hmac_sha256` |

`Print Assumptions` on any ported function therefore reports exactly
`SHA256` and nothing else — the model tree's existing allowlist entry.
`base_2b` and `shrincs_sf_leaf_select` are `Closed under the global
context`.

## Names, order, comments

- **Function names, argument names and argument order** are the Python's,
  unchanged — including `F`, `H`, `PRF`, `T_sf`, `H_grind`, `ADRS`, `M_1`,
  `M_2`, `M_l`. `STYLE.md` already exempts crypto/paper notation from
  snake_case.
- **Definition order** is the Python's. The sample has gaps (it carries
  only the six validation targets and their transitive needs); it does not
  reorder.
- **Section structure** is the Python's: each `#  Helper functions`,
  `#  Parameters`, `#  Primitive cryptographic functions`, ... comment
  becomes a `Model`-style section banner (65 `=`, then `(** ** Title *)`).
- **Constants** keep their names and their defining expressions, as `Z`
  (`WOTS_C_CONSTANT_SUM := WOTS_C_CHAIN_COUNT * (2 ^ WOTS_C_CHAIN_BITS - 1) / 2`,
  not `240`), so a reader checks the *derivation*, not an evaluated number.
  All four constant blocks port whole, including the ones no ported
  function uses yet.
- **Docstrings** become the definition's `(** ... *)` doc comment,
  verbatim modulo two mechanical rewrites: `` `x` `` becomes `[x]`
  (coqdoc), and non-ASCII is spelled out (`STYLE.md`). Any extra paragraph
  is a *porting* note (a caller obligation, a truncation, an escape) and
  says so.
- **Inline comments** stay on the statement they were on
  (`(* chain index *)`, `(* zero hash index *)`,
  `(* Catch and throw if control would enter an infinite recursive loop. *)`).
- **Bugs are ported, not fixed.** `shrincs_sf_leaf_select`'s depth-0 UXMSS
  fall-through (`shrincs.py:1245-1249`) returns `(1, 254)` where `None` was
  meant; the port returns `Some (1, 254)` and carries a comment pointing at
  the "Upstream spec bug" entry in `proof/README.md`. Since this file is now
  the only model in the tree, that is the only formalization of the case —
  nothing anywhere quietly implements the intended behaviour instead. The
  depth-0 shape is excluded where it belongs, as a stated side condition on
  the security theorem (`SHRINCS.fxmss.scheme.shrincs_fxmss_wf_shape`),
  rather than by making it unrepresentable in a second model.

## Validation

`proof/model/shrincs.v` compiles clean (`coqc`, no `Admitted`).
`Print Assumptions` on each of the 50 ported functions reports `SHA256`
and nothing else; 8 of them (`repeat`, `zeros`, `concat`, `xor`,
`base_2b`, `wots_tw_message_to_indexes`,
`wots_tw_message_to_indexes_alt`, `shrincs_sf_leaf_select`) are `Closed
under the global context`.

Everything executable was checked against the Python by running both:

- `base_2b` at `b = 1, 2, 3, 4, 5, 6, 7, 8, 12, 13, 16, 24` over a 10-byte
  input, plus `outlen = 0` and an `outlen` that consumes the whole input —
  15 cases in all. This is the check that matters most, because it is what
  pins `base_2b_fill`'s per-iteration trip count `(b - bits_filled + 7) / 8`
  at every residue of `bits_filled` mod 8.
- `range` at `a < b`, `a = b` and `a > b`.
- `to_bytes`, `slice`, `set_slice`, `set_index`, `xor`, `zeros`, `concat`,
  `len`, `sum_list`.
- all 13 derived constants: `240`, `17`, `5776`, `4594`, `480`, `36`,
  `2240`, `3520`, ...
- `shrincs_sf_leaf_select` at 12 `(structure, state_ctr)` pairs spanning
  both shapes, depth 0, the last valid counter, one past it, a negative
  counter and an unknown shape — including the depth-0 UXMSS bug, which
  reproduces as `Some (1, 254)`.

- **`wots_tw_message_to_indexes`** and **`wots_tw_message_to_indexes_alt`**
  on three 16-byte messages (mixed, all-zero, all-`0xFF`). This is the
  strongest end-to-end check available without a concrete SHA-256: it
  exercises `base_2b` at two widths, the checksum, and the back-to-front
  array fill. The two formulations agree with each other *and* with
  Python on all three.
- **`from_bytes`** (including the empty string), **`bytes_eqb`**,
  **`index_int`**, and `to_bytes` at 4 and 8 bytes.
- **All 38 constants**, in all four blocks.
- The **index and offset arithmetic** of every hash-dependent function,
  extracted as standalone expressions and diffed against the same
  expressions taken from the spec: the WOTS `steps` and per-chain slice
  bounds (both the TW `i*16` and the `+C` `2 + i*16` forms); `xmss_sign`'s
  auth-path sibling indices and `xmss_pubkey_from_sig`'s
  `(k+1, keypair_index >> (k+1), (keypair_index >> k) & 1)` walk, at five
  keypair indices; `hypertree_sign`/`_verify`'s five-layer
  `(leaf_index, tree_index)` walk and per-layer signature slices, at three
  starting indices; `fors_sign`'s `i * 2**a + index_set[i]` leaf and
  `i * 2**(a-j) + ((index_set[i] >> j) ^ 1)` sibling indices over the full
  10x13 forest; `fors_pubkey_from_sig`'s running `offset` over all 140
  signature blocks together with its per-node tree index and branch bit;
  `slh_dsa_digest_message`'s three digest offsets and two moduli;
  `fxmss_pubkey_from_sig`'s and `shrincs_verify`'s signature-length
  arithmetic at four lengths including a non-conforming one; and
  `fxmss_pubkey_from_sig`'s `ADRS[0] += 1` walk.

All of the above is one script on each side, canonicalized and `diff`ed:
**58 blocks, zero differences.**

What is still checked only by reading: the *hash argument layouts* — the
exact byte string each `sha256` call is handed, and the order of the
`ADRS` writes that precede it. Those cannot be executed while `SHA256` is
a `Parameter`. A concrete-SHA-256 instantiation (or extraction against the
C implementation's KATs) would close this last gap and is the natural
follow-up.

## DECISIONS

Five judgment calls the maintainer may want to overturn. Each is cheap to
reverse *now* and expensive after the full port.

1. **`byte` is `Model.byte.byte`, and `bytes` is `list byte`.**
   *Alternative:* `list Z` with a range side condition, or CompCert's
   `Byte.int`. Chosen because `Model.sha256.SHA256` already speaks
   `Model.byte.byte`, so any other choice pays a conversion at every hash
   call, and because `byte_val : byte >-> Z` makes `x[i]` read like Python.
   *Cost:* every byte literal goes through `byte_mod256`, which truncates
   silently where Python raises.

2. **All spec arithmetic is `Z`; `nat` appears only as a recursion
   variable.** *Alternative:* `nat` for the things that are structurally
   counts (heights, lengths, chain indices), which would remove most
   `Z.to_nat`s. Rejected: `state_ctr` is explicitly allowed to be
   negative, `2**61 - 1` appears in a docstring bound, and a mixed
   `nat`/`Z` port would make every signature a judgment call. The cost is
   one `Z.to_nat` per loop entry, all of them inside a `range` or a
   `*_loop` wrapper.

3. **No fuel parameters: a loop is a `fold_left` over its own `range`, or
   a `Fixpoint` on a quantity the spec itself decrements.** *(Ruled by
   the maintainer; the original proposal was a uniform leading
   `fuel : nat` on every loop, and was overridden.)* The cost of the rule
   is that each loop needs one judgment — which of the two shapes it is —
   instead of none; the benefit is that nothing in the file is a budget
   the spec did not state, so a reviewer never has to ask whether a bound
   is big enough. *Alternative:* well-founded recursion on the `Z`
   quantity directly, which would keep even the `nat` conversions out of
   the file — rejected because it needs a measure and an accessibility
   proof, i.e. proof obligations in a proof-free file. The four `nat`
   parameters in the port are `n` (`to_bytes_loop`, the spec's own byte
   count), `bytes_to_read` (`base_2b_fill`, the `while`'s exact remaining
   trip count), `remaining` (the grind loop's counter span) and
   `node_height` (`fxmss_node_loop`, the spec's own recursion variable).

4. **Callee `ADRS` mutations are dropped at the function boundary.**
   *Alternative:* every function returns `(result, ADRS)`, making the
   port mechanically sound with no per-site argument — at the price of
   changing all ~20 signatures that take an `ADRS`, which is exactly the
   thing the "as close as possible" directive is protecting. Chosen with
   a stated global invariant and per-site comments. The obligation to
   re-check it at all 50 functions **has been discharged** — see the
   appendix; it is sound everywhere, load-bearing at exactly two sites.
   It remains the decision with the most reliance on human checking, so
   the appendix, not the code, is what a future spec revision must be
   diffed against.

5. **A crashing `assert` in a non-`Optional` function returns
   `zeros 16`.** *Alternative:* make those functions `option bytes` too
   (honest, but changes `fxmss_node`'s signature and infects every caller
   with `option` plumbing the Python does not have), or return `[]`
   (visibly wrong length, so a later length lemma catches it). `zeros 16`
   keeps the shape every hash in the file has. Only `fxmss_node` is
   affected in the sample; `xmss_node` and `fors_node` have no such
   asserts, so the blast radius of the whole port is one function.

## Size

**1,833 lines, 50 of 50 functions.** Measured, by section:

| section | lines | functions |
|---|---:|---:|
| file header | 52 | — |
| plumbing (no Python counterpart) | 73 | — |
| helper functions | 59 | 5 |
| constants, all four blocks | 55 | 38 constants |
| primitives | 37 | 2 |
| tweaked hashes | 196 | 11 |
| Winternitz | 372 | 11 |
| XMSS | 134 | 3 |
| hypertree | 84 | 2 |
| FXMSS | 201 | 3 |
| FORS | 179 | 4 |
| SLH-DSA | 184 | 5 |
| SHRINCS | 207 | 4 |
| **total** | **1833** | **50** |

1.33x the Python's 1,373 lines, against a P12a projection of ~1,853 (1.1%
under). The docstrings carry over nearly 1:1 and are ~55% of the volume on
both sides; the fold rendering of a loop is close to line-for-line with the
Python. The only structural additions are 12 plumbing definitions and 6
recursion helpers:

| helper | recurses on |
|---|---|
| `to_bytes_loop` | `n`, the spec's own byte count |
| `base_2b_fill` | `bytes_to_read`, the `while`'s exact remaining trip count |
| `wots_c_grind_to_constant_sum_loop` | `remaining`, the counter span |
| `xmss_node_loop`, `fors_node_loop`, `fxmss_node_loop` | `node_height`, the spec's own recursion variable |

Every other loop in the spec — 21 of them — is a `fold_left` over its own
`range`, with no helper at all.

## Appendix: the `ADRS` drop-at-boundary verdict, per function

The obligation stated under "Mutation" above, discharged at every function
that passes an `ADRS` to a callee. The question at each site is: *after the
call, does the caller read an `ADRS` byte the callee wrote, before
rewriting it?* "Read" means fed to a hash (the tweaked hashes take the
whole `ADRS`, except `H_grind`/`H_msg_sf`/`PRF_msg_sf`, which take a
prefix) or read with `index`.

Byte ranges are the spec's: `[0]` anchor tag, `[1:9]` anchor index, `[9]`
type, `[10:14]` / `[14:18]` / `[18:22]` the three payload words.

| function | callees that write `ADRS` | verdict |
|---|---|---|
| `wots_chain_iter` | — (only `F`, read-only) | vacuous |
| `wots_tw_message_to_indexes`, `_alt` | — (no `ADRS`) | n/a |
| `wots_tw_pubkey_gen` | `wots_chain_iter` → `[18:22]` | SOUND — next iteration rewrites `[18:22]`; post-loop `[14:22] = zeros(8)` covers it before `T_sl` |
| `wots_tw_sign` | `wots_chain_iter` → `[18:22]` | SOUND — rewritten each iteration; nothing after the loop reads `ADRS` |
| `wots_tw_pubkey_from_sig` | `wots_chain_iter` → `[18:22]` | **SOUND, load-bearing** — this loop never rewrites `[18:22]` itself. No hash in the body reads `ADRS` outside `wots_chain_iter`, which sets `[18:22]` before each of its own hashes; post-loop `[14:22] = zeros(8)` covers it before `T_sl`. Commented at the site. |
| `wots_c_grind_to_constant_sum`, `wots_c_map_digest` | — (`H_grind` is read-only, and reads `[0:10]`, which includes the `[9]` just written) | vacuous |
| `wots_c_pubkey_gen` | `wots_chain_iter` → `[18:22]` | SOUND — as `wots_tw_pubkey_gen` |
| `wots_c_sign` | `wots_c_grind_to_constant_sum` → `[9]`; `wots_chain_iter` → `[18:22]` | SOUND — the loop rewrites `[9]` and `[18:22]` every iteration; nothing after reads `ADRS` |
| `wots_c_pubkey_from_sig` | `wots_c_map_digest` → `[9]`; `wots_chain_iter` → `[18:22]` | SOUND — `[9]` is rewritten immediately after; `[18:22]` as in `wots_tw_pubkey_from_sig` |
| `xmss_node` | itself, `wots_tw_pubkey_gen` → `[9:22]` | SOUND — the four statements after the recursion rewrite all of `[9:22]`; nothing in this subtree touches `[0:9]` |
| `xmss_sign` | `wots_tw_sign` → `[9]`,`[14:22]`; `xmss_node` → `[9:22]` | SOUND — every `xmss_node` call rewrites all of `[9:22]` before it hashes; `[10:14]` set here is exactly what `xmss_node` overwrites at height 0 |
| `xmss_pubkey_from_sig` | `wots_tw_pubkey_from_sig` → `[9]`,`[14:22]` | SOUND — `[9]` and `[10:14]` are set immediately after, `[14:18]`/`[18:22]` at the top of each loop iteration, all before the first `H` |
| `hypertree_sign`, `hypertree_verify` | `xmss_sign`, `xmss_pubkey_from_sig` → `[9:22]` | SOUND — each iteration re-sets `[0]`,`[1:9]`, and each callee re-derives all of `[9:22]` |
| `fxmss_node` | itself, `wots_c_pubkey_gen` → `[9:22]` | SOUND — leaf branch sets `[0]`,`[1:9]` and the callee sets `[9:22]`; internal branch rewrites all 22 bytes after the recursion |
| `fxmss_sign` | `wots_c_sign` → `[9]`,`[10:14]`,`[14:22]`; `fxmss_node` → all 22 | SOUND — `fxmss_node` re-derives every byte it hashes |
| `fxmss_pubkey_from_sig` | `wots_c_pubkey_from_sig` → `[9]`,`[10:14]`,`[14:22]` | **SOUND, load-bearing** — the loop's `ADRS[0] += 1` genuinely *reads* `[0]`. `wots_c_pubkey_from_sig` provably never writes `[0]` (or `[1:9]`), so the read sees the `leaf_height` set before the call, exactly as in Python. This is the only cross-call `ADRS` read in the spec. |
| `fors_sk_gen`, `fors_node` | `fors_sk_gen` → `[9]`,`[14:22]` | SOUND — the three statements after rewrite `[9]`,`[14:18]`,`[18:22]`; `[0:9]` and `[10:14]` are never touched |
| `fors_sign` | `fors_sk_gen`, `fors_node` → `[9]`,`[14:22]` | SOUND — this function never hashes `ADRS` itself; each callee re-derives what it hashes |
| `fors_pubkey_from_sig` | — (writes `ADRS` only itself) | vacuous |
| `slh_dsa_sign_internal` | `fors_sign` → `[9]`,`[14:22]` | SOUND — `fors_pubkey_from_sig`, called next with the same `ADRS`, sets `[9]`,`[14:18]`,`[18:22]` before its first `F`; `hypertree_sign` builds its own `ADRS` |
| `slh_dsa_verify_internal` | `fors_pubkey_from_sig` → `[9]`,`[14:22]` | SOUND — nothing after reads `ADRS` |
| `slh_dsa_sign`, `slh_dsa_verify` | — (no `ADRS`) | n/a |
| `shrincs_keygen` | `xmss_node` → `[9:22]` | SOUND — `fxmss_node` is handed a fresh `bytearray(22)`, not this one |
| `shrincs_sf_leaf_select` | — (no `ADRS`) | n/a |
| `shrincs_sign`, `shrincs_verify` | — (`PRF_msg_sf`/`H_msg_sf` are read-only; `fxmss_sign`/`fxmss_pubkey_from_sig` build their own) | vacuous |

**Result: sound at every one of the 50 functions.** Two sites are
load-bearing rather than vacuous — `wots_tw_pubkey_from_sig` /
`wots_c_pubkey_from_sig`'s un-rewritten `[18:22]`, and
`fxmss_pubkey_from_sig`'s `ADRS[0] += 1` — and both carry a comment in the
source pointing at this table. If a future spec revision adds a read of
`ADRS` across a call boundary, this is the table that has to change, and
DECISION 4 is the one to revisit.
