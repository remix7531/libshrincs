#!/usr/bin/env bash
# ============================================================================
# The honesty gate. One tree, eight gates. Run by proof/dune:
#
#     nix develop . --command dune build @proof/audit
#
# The rule runs this script in the build directory, next to the sources the
# Shrincs theory compiled and their objects, and passes it the list of files
# git tracks under proof/.
#
#   gate 0  built and reviewed -- every .v the theory compiled has its .vo
#           and is tracked by git, the generated Clight programs excepted
#           (so the gates below read a tree that actually compiles, and
#           nothing is built that a reviewer cannot see). Dune rebuilds by
#           content, so an object here is never older than its source.
#   gate 1  proof gaps -- no Admitted / admit. / give_up. in any source the
#           theory compiled, EXCEPT audit/ itself (probe.v and statement.v
#           are queries, not proofs, and this file's own prose names them)
#   gate 2  no declared assumptions -- no Axiom/Axioms/Conjecture/
#           Parameter(s)/Hypothesis/Hypotheses declaration anywhere.
#           Catches a smuggled assumption by SOURCE TEXT even when nothing
#           uses it, which no cone check can see.
#   gate 3  headline pin -- audit/probe.v must probe every Theorem that
#           theorem.v states, so none can be dropped from the probe or
#           replaced there by a weaker namesake
#   gate 4  cone diff -- the actual Print Assumptions cone of BOTH probed
#           theorems must be a subset of audit/allowed.txt
#   gate 5  statement pins -- audit/statement.v carries reviewed copies
#           of both public theorem statements and
#           the KERNEL must accept the live theorem at that exact type, so
#           a dropped conjunct or a weakened bound is a compile failure
#           here rather than a diff a reviewer has to notice
#   gate 6  public definitions import no Shrincs.internal module
#   gate 7  full-type pins for all guard lemmas and a pinned guard per game
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
PINNED=$AUDIT/pinned.names

# Gates 4 and 5 compile standalone files that are deliberately outside the
# theory, so they get the load path and the warning flags by hand.  Keep the
# -w list in sync with the flags of the theory in proof/dune.
COQFLAGS=(-q -Q . Shrincs -w -notation-overridden,-ambiguous-paths)

fail() { printf 'AUDIT FAIL (%s): %s\n' "$1" "$2" >&2; exit 1; }

[ "$#" -eq 1 ] || fail "arguments" "expected one argument, the list of files git tracks under proof/"
TRACKED=$1
[ -s "$TRACKED" ] || fail "arguments" "$TRACKED is missing or empty, so the tracked sources are unknown"

# ---- the scanned sources ---------------------------------------------------
# The theory in proof/dune compiles every .v file under proof/ except the
# audit's own two queries, plus the Clight programs it generates from the C.
# Those are exactly the .v files of this directory, and they are what the
# gates read.
mapfile -t sources < <(find . -name '*.v' -not -path "./$AUDIT/*" | sort)
[ "${#sources[@]}" -gt 0 ] || fail "sources" "no source found (run through dune build @proof/audit)"

# ---- gate 0: built and reviewed -------------------------------------------
# A source git does not track would be compiled into the theory, and loadable
# by any import that names it, without ever reaching a reviewer.
for vf in "${sources[@]}"; do
  [ -f "${vf%.v}.vo" ] || fail "gate 0" "${vf%.v}.vo missing"
  case "$vf" in
    ./clight/*) ;;
    *) grep -qxF "proof/${vf#./}" "$TRACKED" \
         || fail "gate 0" "${vf#./} is compiled into the theory but not tracked by git" ;;
  esac
done

while IFS= read -r tracked_source; do
  case "$tracked_source" in
    proof/audit/*) continue ;;
    proof/*.v)
      [ -f "${tracked_source#proof/}" ] \
        || fail "gate 0" "$tracked_source is tracked but absent from the theory" ;;
    *) fail "arguments" "unexpected tracked source path: $tracked_source" ;;
  esac
done < "$TRACKED"

while IFS= read -r object; do
  [ -f "${object%.vo}.v" ] \
    || fail "gate 0" "$object has no source in the theory"
done < <(find . -name '*.vo' -not -path "./$AUDIT/*" | sort)

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
# The public claims are the Theorem commands of theorem.v, each written
# `Theorem name :` on one line. A claim in any other form would escape the
# probe and the statement pin, so it is refused here.
# Cheap, and it runs before the two slow compiles: a probe that no longer
# names the theorems proves nothing about them.
sed -n 's/^Theorem \([A-Za-z_][A-Za-z0-9_]*\) :.*/\1/p' theorem.v > "$PINNED"
[ -s "$PINNED" ] || fail "gate 3" "theorem.v states no Theorem, so there is nothing to pin"
claims=$(grep -cE '^(Theorem|Lemma|Corollary|Fact|Proposition|Remark) ' theorem.v)
[ "$claims" -eq "$(wc -l < "$PINNED")" ] \
  || fail "gate 3" "theorem.v states a claim that is not a one-line Theorem command"
while IFS= read -r theorem; do
  grep -q "^Print Assumptions $theorem\." "$PROBE" \
    || fail "gate 3" "$PROBE does not probe $theorem"
done < "$PINNED"

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
if ! bash "$AUDIT/statement.sh" "$PINNED" "$STATEMENT" "$AUDIT/statement.out" "${COQFLAGS[@]}"; then
  fail "gate 5" "$STATEMENT does not compile -- the built theorem's statement has drifted from the reviewed copy"
fi

# ---- gate 6: public definition imports -------------------------------------
# Every source at the top level is a public definition file, except
# theorem.v, which composes the internal results.
mapfile -t public < <(find . -maxdepth 1 -name '*.v' -not -name theorem.v | sort)
[ "${#public[@]}" -gt 0 ] || fail "gate 6" "no public definition file found"
if ! hits=$(awk -v forbid_internal=1 -f "$AUDIT/declarations.awk" "${public[@]}"); then
  fail "gate 6" "$hits"
fi

# ---- gate 7: protocol-abort guards ----------------------------------------
# Reviewed full-type pins plus kernel-classified game coverage (including
# inferred aliases and nested modules). Dune supplies the compiled sources.
# Do not compare mtimes: Dune builds by content.
if ! python3 "$AUDIT/guard_inventory.py" "$AUDIT/guards.v" "$AUDIT" "${COQFLAGS[@]}"; then
  fail "gate 7" "protocol-abort guard coverage or statement pin failed"
fi

# ---- TRUST SURFACE ---------------------------------------------------------
echo "gates 0-7 green"
printf '\n'
printf '================================================================================\n'
printf 'TRUST SURFACE: %s\n' "$(paste -sd ' ' "$PINNED")"
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
