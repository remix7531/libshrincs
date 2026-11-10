#!/usr/bin/env bash
# ============================================================================
# The honesty gate.  ONE tree, seven gates.  Run inside `nix develop`, via
# `make audit` or standalone once the tree is built:
#
#     nix develop -c bash proof/audit/check.sh
#
#   gate 0  build freshness -- every .v listed in _RocqProject is tracked
#           by git and has an up-to-date .vo, and no .vo exists without a
#           registered source (so the gates below read a tree that actually
#           compiles, not just source text that looks right)
#   gate 1  proof gaps -- no Admitted / admit. / give_up. in any tracked or
#           registered source, EXCEPT audit/ itself (probe.v and statement.v
#           are queries, not proofs, and this file's own prose names them)
#   gate 2  no declared assumptions -- no Axiom/Axioms/Conjecture/
#           Parameter(s)/Hypothesis/Hypotheses declaration anywhere.
#           Catches a smuggled assumption by SOURCE TEXT even when nothing
#           uses it, which no cone check can see.
#   gate 3  headline pin -- audit/probe.v must probe the two literal
#           theorem names below, so neither can be silently renamed,
#           dropped, or replaced by a weaker namesake in the probe
#   gate 4  cone diff -- the actual Print Assumptions cone of BOTH probed
#           theorems must be a subset of audit/allowed.txt
#   gate 5  statement pins -- audit/statement.v carries reviewed copies
#           of both public theorem statements and
#           the KERNEL must accept the live theorem at that exact type, so
#           a dropped conjunct or a weakened bound is a compile failure
#           here rather than a diff a reviewer has to notice
#   gate 6  public definitions import no Shrincs.internal module
#
#   (KNOWN TRAP: coqc chats "Fetching opaque proofs from disk" on stderr;
#   the grep -v strip below is why gates 4 and 5 shell out to coqc
#   directly and must not be removed.)
#
# On success prints the TRUST SURFACE table, sourced from allowed.txt's
# per-entry provenance comments.
# ============================================================================

set -u
cd "$(dirname "$0")/.."   # audit/ -> proof/

AUDIT=audit
ALLOWED=$AUDIT/allowed.txt
PROBE=$AUDIT/probe.v
STATEMENT=$AUDIT/statement.v
HEADLINE=shrincs_correct_and_secure
SECOND=sha256_c_correct

# No _RocqProject here: gates 4 and 5 compile standalone files that are
# deliberately absent from the default build, so they get the load path and
# the warning flags by hand.  Keep the -w list in sync with _RocqProject's.
COQFLAGS=(-q -Q . Shrincs -w -notation-overridden,-ambiguous-paths)

fail() { printf 'AUDIT FAIL (%s): %s\n' "$1" "$2" >&2; exit 1; }

# ---- the scanned sources ---------------------------------------------------
# What the gates read is what git tracks plus what the build registers. A
# stray untracked file is not part of the proof and is not scanned. A
# registered source that git does not track would be built but never
# reviewed, so gate 0 rejects it. The generated Clight programs are the one
# exception: they are registered, rebuilt from the C by `make extract`, and
# ignored by git.
git rev-parse --is-inside-work-tree > /dev/null 2>&1 \
  || fail "sources" "not inside a git work tree, so the tracked sources are unknown"
mapfile -t registered < <(grep -E '^[a-z][A-Za-z0-9_/.]*\.v$' _RocqProject)
mapfile -t sources < <(
  { printf '%s\n' "${registered[@]}"; git ls-files -- '*.v' ":(exclude)$AUDIT/*"; } \
    | sort -u | sed 's|^|./|')

# ---- gate 0: build freshness ----------------------------------------------
# Every source line of _RocqProject (they all start with a lowercase
# directory or file name; flags start with `-`, comments with `#`).
for vf in "${registered[@]}"; do
  vo=${vf%.v}.vo
  case "$vf" in
    clight/*) ;;
    *) git ls-files --error-unmatch -- "$vf" > /dev/null 2>&1 \
         || fail "gate 0" "$vf is registered in _RocqProject but not tracked by git" ;;
  esac
  [ -f "$vo" ] || fail "gate 0" "$vo missing (run make prove)"
  [ "$vf" -nt "$vo" ] && fail "gate 0" "$vo older than $vf (run make prove)"
done
# A compiled file with no registered source is loadable under the Shrincs
# root by any import that names it, and nothing above would rebuild or scan
# it. The audit's own two queries are compiled by gates 4 and 5.
stale=$(comm -23 \
  <(find . -name '*.vo' -not -path "./$AUDIT/*" | sed -e 's|^\./||' -e 's|\.vo$|.v|' | sort) \
  <(printf '%s\n' "${registered[@]}" | sort))
[ -n "$stale" ] && fail "gate 0" "compiled file(s) with no source registered in _RocqProject:
$stale"

# ---- gate 1: proof gaps ----------------------------------------------------
GAP_RE='(^|[^A-Za-z_.])(Admitted|admit|give_up)\.'
hits=$(grep -nE "$GAP_RE" "${sources[@]}")
[ -n "$hits" ] && fail "gate 1" "proof gap:
$hits"

# ---- gate 2: no declared assumptions --------------------------------------
# Scan complete commands after removing nested comments and strings.
# Attributes and declaration modifiers can span lines.
# Variable and Context declarations are exempt, including section binders.
if ! hits=$(awk -f "$AUDIT/declarations.awk" "${sources[@]}"); then
  fail "gate 2" "$hits"
fi
# ---- gate 3: headline pin --------------------------------------------------
# Cheap, and it runs before the two slow compiles: a probe that no longer
# names the theorems proves nothing about them.
grep -q "^Print Assumptions $HEADLINE\." "$PROBE" \
  || fail "gate 3" "$PROBE does not probe $HEADLINE"
grep -q "^Print Assumptions $SECOND\." "$PROBE" \
  || fail "gate 3" "$PROBE does not probe $SECOND"

# ---- gate 4: cone diff -----------------------------------------------------
found=$AUDIT/probe.found
if ! coqc "${COQFLAGS[@]}" "$PROBE" > "$AUDIT/probe.out" 2>&1; then
  grep -v '^Fetching opaque proofs from disk' "$AUDIT/probe.out" >&2
  fail "gate 4" "$PROBE does not compile"
fi
grep -v '^Fetching opaque proofs from disk' "$AUDIT/probe.out" \
  | awk '/^[A-Za-z_][^[:space:]]* : / { print $1 }' | sort -u > "$found"

# allowed.txt -> bare names: drop `#` comments (whole-line and trailing) and
# the [section] headers, which are human navigation only.  Unlike the old
# per-tree allowed.txt, gate 4 diffs ONE flat name set against the whole file.
allowed_names=$AUDIT/allowed.names
sed -e 's/#.*$//' -e '/^\[/d' -e 's/[[:space:]]*$//' -e '/^$/d' "$ALLOWED" \
  | sort -u > "$allowed_names"

extra=$(comm -23 "$found" "$allowed_names")
[ -n "$extra" ] && fail "gate 4" "assumption(s) in the theorem cone but not in $ALLOWED:
$extra"

# ---- gate 5: statement pin -------------------------------------------------
# Gates 0-4 pin the headline theorem's NAME and its ASSUMPTION CONE, but
# nothing above checks that its STATEMENT is still the one a reviewer read:
# a conjunct could be dropped, a bound weakened, an argument reordered, and
# every gate so far would stay green as long as SOME term by that name
# exists with a clean cone.
#
# audit/statement.v closes that gap.  It carries a hand-pasted copy of the
# reviewed statement, and `Check (<headline> : <that type>).` type-checks
# only if the KERNEL accepts the LIVE theorem at the pasted type.  The grep
# guards the pin itself, so statement.v cannot quietly stop pinning by
# deleting its Check.
if ! bash "$AUDIT/statement.sh" "$STATEMENT" "$AUDIT/statement.out" "${COQFLAGS[@]}"; then
  fail "gate 5" "$STATEMENT does not compile -- the built theorem's statement has drifted from the reviewed copy"
fi

# ---- gate 6: public definition imports -------------------------------------
if ! hits=$(awk -v forbid_internal=1 -f "$AUDIT/declarations.awk" \
    sha256.v spec.v contracts.v games.v); then
  fail "gate 6" "$hits"
fi

# ---- TRUST SURFACE ---------------------------------------------------------
echo "gates 0-6 green"
printf '\n'
printf '================================================================================\n'
printf 'TRUST SURFACE: %s\n' "$HEADLINE"
printf '               %s\n' "(and $SECOND, probed alongside it)"
printf '================================================================================\n'
printf '%-2s %-54s %s\n' "" "ASSUMPTION" "PROVENANCE"
grep -E '^[A-Za-z_]' "$ALLOWED" | while IFS= read -r line; do
  name=${line%%[[:space:]]*}
  note=$(printf '%s' "$line" | sed -n 's/^[^#]*#[[:space:]]*//p')
  if grep -qx "$name" "$found"; then mark='*'; else mark=' '; fi
  printf '%-2s %-54s %s\n' "$mark" "$name" "$note"
done
printf '================================================================================\n'
printf '(* = reached by this build'"'"'s cone; unmarked = allowlisted but not reached)\n'

exit 0
