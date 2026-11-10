#!/usr/bin/env bash
# Honesty gate for the three libshrincs proof trees (model, ssprove, vst).
# Run inside `nix develop`, via `make audit` or standalone once the trees are
# built:  nix develop -c bash proof/assumptions/check.sh
#
# Four gates run per tree (model first -- the shared trust root):
#   0. build freshness -- every tree/*.v in _RocqProject has an up-to-date .vo.
#   1. proof gaps      -- no Admitted / admit. / give_up. in the tree.
#   2. assumption confinement -- every Axiom/Parameter/Conjecture/Hypothesis
#      declaration lives in an allowlisted file (model -> machine.v and the
#      discharged address.v Hpb hypothesis; ssprove and vst permit none).
#      Catches a smuggled assumption by SOURCE TEXT even if unused.
#      A confinement check, not exact-name: a new assumption inside an allowed
#      file is caught by gate 3 iff an audited theorem uses it.
#   3. Print Assumptions cone diff -- compile the tree's assumptions/<tree>.v
#      probe with coqc, extract the axiom names, diff against the tree's
#      section of allowed.txt.  This is the real cone check; gate 2 is the belt
#      for the declared-but-unused case no dependency tool can see.
#
# KNOWN TRAP: gate 3 strips "Fetching opaque proofs from disk" stderr lines
# before parsing (VST/CompCert print them cold; they are NOT axioms) -- do not
# remove that grep -v.  That is why gate 3 shells to coqc, not rocq-mcp.
#
# On success prints the TRUST SURFACE table (every gate-3 assumption + one-line
# provenance).  allowed.txt is INI-sectioned ([model]/[ssprove]/[vst]); `#`
# comments and trailing provenance notes are ignored.

set -uo pipefail
cd "$(dirname "$0")/.."   # assumptions/ -> proof/

ASSUMPTIONS_DIR=assumptions
ALLOWLIST="$ASSUMPTIONS_DIR/allowed.txt"
fail=0

# Assumption-declaration keywords for gate 2: global assumptions
# (Axiom/Axioms/Conjecture/Parameter/Parameters) and section Hypothesis, with
# an optional Local/Global/#[..] prefix so none can hide behind one, keyed on
# the "name :" colon so prose can't match. Variable/Context are discharged at
# Qed, are not assumptions, and are NOT matched.
ASSUME_RE='^[[:space:]]*((#\[[^]]*\]|Local|Global|Polymorphic|Monomorphic)[[:space:]]+)*(Axioms?|Conjecture|Parameters?|Hypothesis|Hypotheses)[[:space:]]+[A-Za-z_][A-Za-z0-9_'\'' ]*:'

# Allowlist section extraction (shared by gate 3 and the TRUST SURFACE table).
# Emits "name<TAB>provenance" per real entry in [section]; skips blank / `#`
# lines and splits a trailing `# ...` note off an entry.
section_entries() {
  local section="$1"
  awk -v want="[$section]" '
    $0 == want { infile=1; next }
    /^\[/      { infile=0 }
    infile {
      line = $0
      sub(/^[[:space:]]+/, "", line)
      if (line == "" || substr(line,1,1) == "#") next
      hashpos = index(line, "#")
      if (hashpos > 0) {
        namepart = substr(line, 1, hashpos-1)
        provpart = substr(line, hashpos+1)
      } else {
        namepart = line
        provpart = ""
      }
      gsub(/[[:space:]]+$/, "", namepart)
      gsub(/^[[:space:]]+/, "", provpart)
      gsub(/[[:space:]]+$/, "", provpart)
      print namepart "\t" provpart
    }
  ' "$ALLOWLIST"
}

provenance_for() {
  local section="$1" name="$2"
  section_entries "$section" \
    | awk -F'\t' -v n="$name" '$1 == n { print $2; found=1; exit } END { if (!found) print "" }'
}

# Gate 0: every tree/*.v listed in _RocqProject has an up-to-date .vo (the
# assumptions/ probes are excluded from the default build on purpose).
tree_directory() {
  case "$1" in
    model) printf '%s\n' internal/common ;;
    ssprove) printf '%s\n' internal/ssprove ;;
    vst) printf '%s\n' internal/vst ;;
    clight) printf '%s\n' clight ;;
    *) printf 'Unknown proof tree: %s\n' "$1" >&2; return 1 ;;
  esac
}

gate0_build_freshness() {
  local tree="$1"
  local directory
  directory=$(tree_directory "$tree") || return 1
  local source_pattern="^\s*${directory}/.*\.v\s*$"
  if [ "$tree" = model ]; then
    source_pattern='^\s*(internal/common/.*|sha256)\.v\s*$'
  fi

  local ok=1
  while IFS= read -r vfile; do
    local vo="${vfile%.v}.vo"
    if [ ! -e "$vo" ] || [ "$vfile" -nt "$vo" ]; then
      echo "FAIL: $vfile has no up-to-date .vo (build failed or stale)"
      ok=0
    fi
  done < <(grep -E "$source_pattern" _RocqProject)
  [ "$ok" = 1 ]
}

# Gate 1: no proof gaps in the tree ($@ adds ssprove's assumptions/ probe dir).
gate1_proof_gaps() {
  local tree="$1"; shift
  local directory
  directory=$(tree_directory "$tree") || return 1

  if grep -rnE --include='*.v' '(^|[^A-Za-z_.])(Admitted|admit|give_up)\.' "$directory" "$@"; then
    echo "FAIL: proof gaps found"
    return 1
  fi
  return 0
}

# Gate 2: every ASSUME_RE hit in the scope dirs ($@) must match allowed_re (its
# tree's allowlisted declaration file, or the one discharged Hypothesis) --
# anything else is a smuggled assumption.  See the header note for the rationale.
gate2_confined() {
  local label="$1" allowed_re="$2"; shift 2
  local hits
  hits=$(grep -rnE --include='*.v' "$ASSUME_RE" "$@" | grep -vE "$allowed_re" || true)
  if [ -n "$hits" ]; then
    echo "FAIL: $label declares an assumption outside its allowlisted file(s):"
    echo "$hits"
    return 1
  fi
  return 0
}

gate2_model() {
  gate2_confined model \
    'internal/common/machine\.v:|internal/common/address\.v:.*Hypothesis Hpb' \
    internal/common sha256.v
}

gate2_ssprove() {
  gate2_confined ssprove \
    '$^' \
    internal/ssprove "$ASSUMPTIONS_DIR"
}

gate2_vst() {
  gate2_confined vst \
    '$^' \
    internal/vst
}

# Gate 3: compile the tree's Print Assumptions probe, extract the axiom names
# (stripping the opaque-proof-fetch log first -- see the header KNOWN TRAP), and
# diff against the tree's allowed.txt section.
#   tree   -- "model" | "ssprove" | "vst"   qflags -- -Q load-path flags for coqc
gate3_assumptions() {
  local tree="$1" qflags="$2"
  local probe="$ASSUMPTIONS_DIR/$tree.v"

  local ok=1

  if ! coqc -q \
      -w -notation-overridden,-ambiguous-paths \
      $qflags \
      "$probe" > "$ASSUMPTIONS_DIR/$tree.out" 2>&1; then
    echo "FAIL: $probe does not compile"
    cat "$ASSUMPTIONS_DIR/$tree.out"
    return 1
  fi

  grep -v '^Fetching opaque proofs from disk' "$ASSUMPTIONS_DIR/$tree.out" \
    | awk '/^[A-Za-z_][^[:space:]]* : / { print $1 }' \
    | sort -u > "$ASSUMPTIONS_DIR/$tree.found"

  if [ -s "$ASSUMPTIONS_DIR/$tree.found" ]; then
    local extra
    if extra=$(comm -23 "$ASSUMPTIONS_DIR/$tree.found" \
                 <(section_entries "$tree" | cut -f1 | sort -u)); [ -n "$extra" ]; then
      echo "FAIL: $tree assumptions outside the allowed baseline:"
      echo "$extra"
      ok=0
    fi
  fi
  [ "$ok" = 1 ]
}

# TRUST SURFACE report (printed once every gate is green). The large, low-signal
# ssprove/vst classical-logic baselines are grouped into one summary row each;
# every named trust anchor / advantage bound / hash-game axiom is still listed.
# Reporting only -- gate 3 already diffed the FULL found set against the FULL
# allowlist.
CLASSICAL_MODEL=()
CLASSICAL_SSPROVE=(
  Axioms.R
  boolp.constructive_indefinite_description
  boolp.functional_extensionality_dep
  boolp.propositional_extensionality
)
CLASSICAL_VST=(
  Axioms.prop_ext
  ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec
  Classical_Prop.classic
  Ensembles.Extensionality_Ensembles
  FunctionalExtensionality.functional_extensionality_dep
)

is_classical() {
  local name="$1" arrname="$2"
  local -n arr="$arrname"
  local x
  for x in ${arr[@]+"${arr[@]}"}; do
    [ "$x" = "$name" ] && return 0
  done
  return 1
}

print_trust_surface_rows() {
  local tree="$1" classical_arrname="$2"
  local name prov
  while IFS= read -r name; do
    [ -z "$name" ] && continue
    is_classical "$name" "$classical_arrname" && continue
    prov=$(provenance_for "$tree" "$name")
    printf '%-8s  %-42s  %s\n' "$tree" "$name" "$prov"
  done < "$ASSUMPTIONS_DIR/$tree.found"
}

print_trust_surface() {
  echo
  echo "================================================================================"
  echo "TRUST SURFACE"
  echo "================================================================================"
  printf '%-8s  %-42s  %s\n' "TREE" "ASSUMPTION" "PROVENANCE"
  printf '%-8s  %-42s  %s\n' "--------" "------------------------------------------" "----------"
  print_trust_surface_rows model CLASSICAL_MODEL
  printf '%-8s  %-42s  %s\n' "ssprove" "(classical baseline, ${#CLASSICAL_SSPROVE[@]} entries)" \
    "SSProve/mathcomp-analysis library axioms -- excluded middle, choice, prop/functional extensionality"
  print_trust_surface_rows ssprove CLASSICAL_SSPROVE
  printf '%-8s  %-42s  %s\n' "vst" "(classical baseline, ${#CLASSICAL_VST[@]} entries)" \
    "CompCert/Coq-stdlib library axioms -- excluded middle, extensionality, classical reals decidability"
  print_trust_surface_rows vst CLASSICAL_VST
  echo "================================================================================"
}

# Run all three trees (model first -- the shared trust root). Quiet on success:
# one line per tree; gates speak only when they FAIL.
tree_fail=0
gate0_build_freshness model || tree_fail=1
gate1_proof_gaps model sha256.v || tree_fail=1
gate2_model || tree_fail=1
gate3_assumptions model "-Q . Shrincs" || tree_fail=1
[ "$tree_fail" = 0 ] && echo "model    gates 0-3 green" || fail=1

tree_fail=0
gate0_build_freshness ssprove || tree_fail=1
gate1_proof_gaps ssprove "$ASSUMPTIONS_DIR" || tree_fail=1
gate2_ssprove || tree_fail=1
gate3_assumptions ssprove "-Q . Shrincs" || tree_fail=1
[ "$tree_fail" = 0 ] && echo "ssprove  gates 0-3 green" || fail=1

tree_fail=0
gate0_build_freshness vst || tree_fail=1
gate0_build_freshness clight || tree_fail=1
gate1_proof_gaps vst || tree_fail=1
gate2_vst || tree_fail=1
gate3_assumptions vst "-Q . Shrincs" || tree_fail=1
[ "$tree_fail" = 0 ] && echo "vst      gates 0-3 green" || fail=1

if [ "$fail" = 0 ]; then
  print_trust_surface
  echo
  echo "== assumptions/check.sh: ALL GATES GREEN =="
else
  echo
  echo "== assumptions/check.sh: FAILED =="
fi
exit "$fail"
