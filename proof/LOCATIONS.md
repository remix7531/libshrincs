# SSProve heap-location id registry

Every SSProve `Location` in this repo is `mkloc <id> <init>`, where `<id> :
nat` is a hand-picked literal — there is no allocator. Each family below
owns a disjoint range by convention; this file is the single authoritative
index, so a new family can pick a free range without grepping the whole
tree. `mkloc` ids are internal-only: no proof script or spec references the
literal number outside the `Definition` site itself, so moving one is a
pure one-line edit with zero call-site churn.

Package interface **operation ids** (`LCOMMIT`/`LGETPP`/.../`QUERY`/`REPRO`,
plain `nat` constants, not `mkloc`) are a separate namespace and are not
tracked here.

## proof/ssprove (native `Sec.*` tree)

| range   | file                          | members |
|---------|-------------------------------|---------|
| 20-22   | ssprove/lib/toolkit/ro_plus.v | ro_map/qcnt_loc (20-21; 22 reserved) |
| 31-33   | ssprove/lib/games/prf_adaptive.v | prf_key/tab/cnt_loc |
| 44-47   | ssprove/lib/games/smtcr.v     | tcr_pp/tgts/tws/rev_loc |
| 54-57   | ssprove/lib/games/smpre.v     | pre_pp/tgts/tws/rev_loc |
| 64-66   | ssprove/lib/games/smud.v      | ud_pp/tws/rev_loc |
| 74-77   | ssprove/lib/games/stcrp.v     | stcr_pp/tgts/tws/rev_loc |
| 78      | ssprove/lib/toolkit/ro_plus.v | ro_rcnt_loc (moved off 64: collided with smud's ud_pp_loc) |
| 84-85   | ssprove/lib/games/prf.v       | prf_k/qs_loc |
| 95-98   | ssprove/lib/games/tcrx.v      | tcrx_pp/tgts/tws/rev_loc |
| 115-116 | ssprove/lib/sig/kots.v        | kots_pk/log_loc |
| 125-127 | ssprove/lib/sig/eucma.v       | eucma_sk/pk/log_loc |
| 200-201 | ssprove/lib/wots/games.v      | g0_pk/log_loc |
| 210-211 | ssprove/lib/wots/analysis.v   | g0v_pk/log_loc |
| 230-233 | ssprove/lib/wots/tcr_hop.v    | rt_pk/log/sig_loc, gm_sig_loc |
| 240-242 | ssprove/lib/wots/pre_hop.v    | rp_pk/log/sig_loc |
| 250-253 | ssprove/lib/wots/ud_hop.v     | hud_pk/log_loc (250-251), rud_pk/log_loc (252-253) |
| 300-302 | ssprove/wots/games.v          | forge_pk/log/sig_loc |
| 310-315 | ssprove/wots/hop/ud.v         | ud_hybrid_*(310-312), r_ud_*(313-315) |
| 330-332 | ssprove/wots/hop/grind.v      | r_grind_pk/log/sig_loc |
| 340-342 | ssprove/wots/hop/compress.v   | r_compress_pk/log/sig_loc |
| 350-352 | ssprove/wots/hop/chain_tcr.v  | r_chain_tcr_pk/log/sig_loc |
| 360-362 | ssprove/wots/hop/chain_pre.v  | r_chain_pre_pk/log/sig_loc |
| 370-372 | ssprove/wots/hop/prf.v        | r_prf_pk/log/sig_loc |

Note: `ro_map_loc`/`ro_qcnt_loc` (20-21) were left where they already were
relative to each other; only the colliding member (`ro_rcnt_loc`, old id 64)
moved, to 78, to keep the diff minimal.

The eight families in ranges 20-22, 78, 95-98 and 200-253 used to live under
`proof/fxmss/hbs` (logical root `HBS`), which was retired: the generic
hash-based-signature library it held is now `Sec.lib.*` and both the native
WOTS+C proof and the FXMSS tree instantiate it. Only the file paths moved --
every id is unchanged.

## proof/fxmss/shrincs/wotsc (standalone FXMSS WOTS+C tree)

| range   | file          | members |
|---------|---------------|---------|
| 900-902 | wotsc/games.v | g0w_pk/log/sig_loc (moved off 300-302: collided with ssprove/wots/games.v's forge_*) |

(the other wotsc/*.v id families — grind_hop/compress_hop/chain_hop/
zero_chain_hop/zero_games — were removed as dead code in a concurrent
phase and are not tracked here.)

## proof/fxmss/shrincs/fxmss (the FXMSS EU-CMA top-level tree)

| range   | file                    | members |
|---------|-------------------------|---------|
| 400-410 | fxmss/games.v           | shrincs_fxmss_st/kp/scnt/log/rom/hcnt/rt/fcnt/used_loc (402 unused; 409 lives in digest_hop.v) |
| 409     | fxmss/digest_hop.v      | shrincs_fxmss_sd_loc (canonical definer; late_games.v imports it) |
| 420     | fxmss/leaf_reduction.v  | rl_pks_loc |
| 440-447 | fxmss/prf_hop.v         | rp_st/kp/used/scnt/log/rom/hcnt/fcnt_loc |
| 460-466 | fxmss/prf_hop.v         | rm_st/used/scnt/log/rom/hcnt/fcnt_loc |
| 470     | fxmss/leaf_km.v         | mkm_tgts_loc |
| 480-486 | fxmss/repro_hop.v       | rr_st/used/scnt/log/hcnt/rt/fcnt_loc |
| 500-504 | fxmss/leaf_reduction.v  | miw_pp/tgts/tws/rev/slog_loc (moved off 64-67,69: see FINDING below) |
| 600-605 | fxmss/leaf2_chain_tcr.v | rct_rev/tws/tgts/slog/pp/cnt_loc |
| 610-614 | fxmss/leaf2_compress.v  | rcp_rev/tws/tgts/slog/pp_loc (moved off 600-604: collided with leaf2_chain_tcr.v) |
| 700-705 | fxmss/leaf2_chain_pre.v | rpr_rev/tws/tgts/slog/pp/cnt_loc |
| 710-714 | fxmss/leaf2_ud.v        | rud_rev/tws/tgts/slog/pp_loc (moved off 700-704: collided with leaf2_chain_pre.v) |
| 800-805 | fxmss/leaf2_grind.v     | rgr_rev/tws/tgts/slog/pp/cnt_loc |

## De-duplicated definitions

Two locations were defined twice (same name, same id, two files), with
resolution depending on `Require` import order:

- `shrincs_fxmss_fcnt_loc` (408): canonical in `fxmss/games.v`. The
  redundant re-definition in `fxmss/repro_hop.v` is deleted — that file
  already `Require Import`s `fxmss.games` directly, and every other
  consumer of this name (`tree_hop_proof.v`, `leaf_km.v`, `leaf_reduction.v`,
  `connect_hop.v`, `prf_hop.v`, `digest_hop.v`, the `digest_hop_bound_*`
  files, `grind_assert_hop.v`, `late_games.v`) also requires `fxmss.games`
  directly, so no further change was needed.
- `shrincs_fxmss_sd_loc` (409): canonical in `fxmss/digest_hop.v`. The
  redundant re-definition in `fxmss/late_games.v` is deleted. **This one
  needed `Require Export`, not `Require Import`**: plain `Require Import`
  only opens a module's namespace for the *current* file, it does not
  propagate to files that later `Require Import` the current file. Since
  `tree_hop_proof.v`, `tcrx_hop_proof.v`, `leaf_km.v`, and `leaf_reduction.v`
  all reference `shrincs_fxmss_sd_loc` while requiring only
  `fxmss.late_games` (not `fxmss.digest_hop` directly), a plain
  `Require Import fxmss.digest_hop` inside `late_games.v` left them unable
  to resolve the name — confirmed empirically: `tree_hop_proof.v` and
  `tcrx_hop_proof.v` both failed to compile with "The reference
  shrincs_fxmss_sd_loc was not found in the current environment" before
  `late_games.v` was switched to `Require Export fxmss.digest_hop`. This is
  live evidence that the Require-order hazard the phase brief flagged was
  real, not hypothetical.

## FINDING (RESOLVED): the id-64/66 split exposed live aliasing in leaf2_ud.v

Classification: **live aliasing**, confirmed by direct proof-state
inspection via rocq-mcp (not a mundane fset/ordering issue). Splitting the
id-64 collision (this phase's mandate) made `leaf2_ud.v` stop compiling,
because its `heap_ignore` set `IGNU` was silently relying on the
collision. The split is APPLIED (never reverted) and the invariant has
been made honest; see **The repair** at the end of this section.

**Root cause.** `leaf2_ud.v`'s `IGNU` (`heap_ignore` location set for the
leaf-level SM-UD hop) deliberately omitted
`Upp := ud_pp_loc TF` and `Urv := ud_rev_loc` from its explicit member
list. Its own pre-existing comment (`leaf2_ud.v:1550-1555`) explains why:

> NB: [Upp]/[Urv] are OMITTED: [Upp] shares id [64] with [Lpp] and [Urv]
> shares id [66] with [Ltw].  [heap_ignore] ignores by ID, so those ids are
> still ignored (via [Lpp]/[Ltw]); listing the type-conflicting duplicates
> would make [IGNU] type-inconsistent with the composite location union
> (which resolves id 66 to the game's [Ltw : seq], not [Urv : bool]),
> breaking the [fsubmap] well-formedness check.

i.e. two location pairs were conflated by raw numeric id, one same-typed
and one differently-typed:

1. **`Upp` (`ud_pp_loc TF`, id 64, `option (th_PP TF)` = `option PP` at
   this instantiation) vs `Lpp` (`miw_pp_loc PP`, id 64 before this phase,
   moved to id 500 by this phase's split, also `option PP`).** Same id
   AND same type at the FXMSS instantiation — the dangerous case the
   phase brief named explicitly.
2. **`Urv` (`ud_rev_loc`, id 66, `bool`) vs `Ltw` (`miw_tws_loc`, id 66
   before this phase, moved to id 502, `seq adrs_sf_ch`).** Same id,
   *different* types — this is the pair the comment says could not even
   be listed together in one `Locations` fmap literal (one key, two
   types), which is exactly why the omission existed in the first place.

**Confirmed failure site (compiler + interactive reproduction agree).**
`Lemma udpin_set_both_pp` (`leaf2_ud.v:1720-1734`) proves that setting
*both* `Lpp` and `Upp` to `Some pp` simultaneously preserves
`heap_ignore IGNU`:
```
Definition IGNU : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rud_pp_loc ; rud_tgts_loc ; rud_tws_loc ; rud_rev_loc ; rud_slog_loc ;
        Utw ].
...
Lemma udpin_set_both_pp (pp : PP) lsl ltw ltg rtg utw s0 s1 :
  udpin None false lsl ltw ltg rtg utw (s0, s1) ->
  udpin (Some pp) false lsl ltw ltg rtg utw
    (set_heap s0 Lpp (Some pp), set_heap s1 Upp (Some pp)).
Proof.
move=> [hign [hL1 hL2 hL3 hL4 hL5] [hr1 hr2 hr3 hr4 hr5] [hu1 hu2 hu3] hm].
case: hm => he1 he2 he3; split.
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.   (* leaf2_ud.v:1728 *)
  exact: hign.
...
```
Compiler error (`make -C proof fxmss-prove`): `File
"./fxmss/shrincs/fxmss/leaf2_ud.v", line 1728, characters 34-53: Error:
No applicable tactic.`

Reproduced interactively with rocq-mcp at the exact tactic. Goal
immediately before the failing `apply: heap_ignore_set_r; first by
rewrite mem_domm.`:
```
hign : heap_ignore IGNU (s0, s1)
hL1 : get_heap s0 Lpp = None      hu1 : get_heap s1 Upp = None
...
|- heap_ignore IGNU (s0, set_heap s1 Upp (Some pp))
```
`heap_ignore_set_r : ℓ.1 \in domm L -> heap_ignore L (s0,s1) ->
heap_ignore L (s0, set_heap s1 ℓ v)`. Applied with `ℓ := Upp`, its first
premise is `Upp.1 \in domm IGNU`. Before this phase, `Upp.1 = 64 = Lpp.1`,
so `rewrite mem_domm` closed it by numeric coincidence even though `Upp`
is never itself a member of `IGNU`'s literal list — only `Lpp` is. After
the split, `Upp.1 = 64` while `IGNU`'s corresponding key is `Lpp.1 = 500`,
so the membership is false and `rewrite mem_domm` has nothing to close;
Coq reports "No applicable tactic."

**What the conflation let the proof skip.** `udpin_set_both_pp` never
proves (or even states) that writing to the SM-UD game's own `pp` cell is
safe under `heap_ignore IGNU` — it gets that fact for free purely because
`Upp` and `Lpp` used to be bit-for-bit the same `Location` value (same id,
same type at this instantiation). The proof genuinely relies on two
conceptually distinct heap cells — one belonging to the generic,
reusable `Sec.lib.games.smud` game, the other to this scheme's own
leaf-reduction bookkeeping — being *literally* the same memory cell.

**Second instance (identified by inspection; the compiler had not reached
it, `make` stopping at the first error).** `Lemma ud_inv_reveal` has the
identical shape for the `Urv`/`Ltw` (id 66) pair:
```
- apply: heap_ignore_set_l; first by rewrite mem_domm.
  apply: heap_ignore_set_r; first by rewrite mem_domm.   (* Urv *)
  apply: heap_ignore_set_r; first by rewrite mem_domm.   (* rud_pp_loc *)
  apply: heap_ignore_set_r; first by rewrite mem_domm.   (* rud_rev_loc *)
  exact: hign.
```
The second line (`Urv`) would have failed the same way, by the same
`mem_domm`-on-a-no-longer-shared-id argument as above.

**The repair (applied).** `IGNU` is made honest — `Upp` and `Urv` are
listed literally, alongside `Utw`, so all three SM-UD cells appear:
```
Definition IGNU : Locations :=
  [fmap Lpp ; Ltg ; Ltw ; Lrv ; Lsl ;
        rud_pp_loc ; rud_tgts_loc ; rud_tws_loc ; rud_rev_loc ; rud_slog_loc ;
        Upp ; Utw ; Urv ].
```
The original comment's objection ("listing the type-conflicting
duplicates would make `IGNU` type-inconsistent … breaking the `fsubmap`
well-formedness check") was an artefact of the collision, not of the
proof: with ids 64/65/66 no longer shared with anything in `MKMLocs`,
each is a distinct key of the `Locations` fmap and `fsubmap IGNU (unionm
L₀ L₁)` — the `Invariant_heap_ignore` side condition at both `perfect`
sites in the file — is still discharged by `fmap_solve` unchanged.

The repair is confined to that one `Definition` (plus its comment).
**No proof script anywhere changed**: `udpin_set_both_pp`,
`ud_inv_reveal`, `udpin_set_utw`, `ud_inv_setsl`, `ud_inv_pin`,
`Hl_real_perfect`, `Hl_ideal_perfect` and every downstream lemma in
`leaf2_ud.v` / `leaf2_theorem.v` / `theorem.v` close verbatim, because
the `mem_domm` membership premises are now discharged by genuine
membership instead of numeric coincidence. No further instances beyond
the two documented above were found (the whole tree recompiles green).

The ignore-set is also semantically unchanged with respect to the
pre-phase build: before, `IGNU` ignored ids
`{64,65,66,67,69,470,700..704}`, covering `Upp`/`Urv` only via the
`Lpp`/`Ltw` aliases; now it ignores
`{64,65,66,470,500,502,503,504,710..714}` — the same *cells*, each named
once, none riding on another's id.
