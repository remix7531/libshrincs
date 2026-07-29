#!/usr/bin/env bash
# Honesty gate for the four libshrincs proof trees (model, ssprove, fxmss,
# vst).
# Run inside `nix develop`, via `make audit` or standalone once the trees are
# built:  nix develop -c bash proof/assumptions/check.sh
#
# Five gates run per tree (model first -- the shared trust root):
#   0. build freshness -- every tree/*.v in _RocqProject has an up-to-date .vo.
#   1. proof gaps      -- no Admitted / admit. / give_up. in the tree.
#   2. assumption confinement -- every Axiom/Parameter/Conjecture/Hypothesis
#      declaration lives in the tree's one allowlisted file (model -> machine.v
#      + sha256.v + the address.v Hpb hypothesis; ssprove -> axioms.v; fxmss ->
#      none, no assumption declaration is permitted anywhere in the tree; vst ->
#      gprog.v).  Catches a smuggled assumption by SOURCE TEXT even if unused.
#      A confinement check, not exact-name: a new assumption inside an allowed
#      file is caught by gate 3 iff an audited theorem uses it.
#   3. Print Assumptions cone diff -- compile the tree's assumptions/<tree>.v
#      probe with coqc, extract the axiom names, diff against the tree's OWN
#      section of allowed.txt.  This is the real cone check; gate 2 is the belt
#      for the declared-but-unused case no dependency tool can see.  Each tree
#      is diffed against its own section -- fxmss is NOT re-checked against
#      ssprove's wider baseline, so it cannot silently acquire ssprove's
#      eps_*/sha256_*_secure entries and stay green.
#   4. axiom STATEMENT pinning -- gate 3 diffs axiom NAMES only, so an axiom
#      could be silently RESTATED (weakened, or its quantification widened)
#      under an allowlisted name and stay green.  Gate 4 hashes each found
#      axiom's full printed statement from the same probe output and diffs the
#      digests against assumptions/statements.sha256.  Fails if a digest
#      differs or a found axiom has no pinned entry.
#
# KNOWN TRAP: gates 3/4 strip "Fetching opaque proofs from disk" stderr lines
# before parsing (VST/CompCert print them cold; they are NOT axioms) -- do not
# remove that grep -v.  That is why gate 3 shells to coqc, not rocq-mcp.
#
# On success prints the TRUST SURFACE table (every gate-3 assumption + one-line
# provenance).  allowed.txt is INI-sectioned ([model]/[ssprove]/[fxmss]/[vst]);
# `#` comments and trailing provenance notes are ignored.

set -uo pipefail
cd "$(dirname "$0")/.."   # assumptions/ -> proof/

ASSUMPTIONS_DIR=assumptions
ALLOWLIST="$ASSUMPTIONS_DIR/allowed.txt"
STATEMENTS="$ASSUMPTIONS_DIR/statements.sha256"
fail=0

# Every coqc -Q load-path mapping this project uses, derived mechanically
# from _RocqProject so gate 3 can never go stale again (a hand-maintained
# copy previously kept a `-Q fxmss/examples HBS.Examples` entry for a
# directory that no longer exists). A tree not using one of these mappings
# just ignores the extra, unused logical path.
QFLAGS=$(grep -E '^-Q ' _RocqProject | tr '\n' ' ')

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
gate0_build_freshness() {
  local tree="$1"

  local ok=1
  while IFS= read -r vfile; do
    local vo="${vfile%.v}.vo"
    if [ ! -e "$vo" ] || [ "$vfile" -nt "$vo" ]; then
      echo "FAIL: $vfile has no up-to-date .vo (build failed or stale)"
      ok=0
    fi
  done < <(grep -E "^\s*${tree}/.*\.v\s*$" _RocqProject)
  [ "$ok" = 1 ]
}

# Gate 1: no proof gaps in the tree ($@ adds ssprove's assumptions/ probe dir).
gate1_proof_gaps() {
  local tree="$1"; shift

  if grep -rnE --include='*.v' '(^|[^A-Za-z_.])(Admitted|admit|give_up)\.' "$tree" "$@"; then
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
    'model/(machine|sha256)\.v:|model/address\.v:.*Hypothesis Hpb' \
    model
}

gate2_ssprove() {
  gate2_confined ssprove \
    'ssprove/axioms\.v:' \
    ssprove "$ASSUMPTIONS_DIR"
}

gate2_vst() {
  gate2_confined vst \
    'vst/contract/gprog\.v:' \
    vst
}

# Gate 3: compile the tree's Print Assumptions probe, extract the axiom names
# (stripping the opaque-proof-fetch log first -- see the header KNOWN TRAP), and
# diff against the tree's OWN allowed.txt section (every tree gets one; none
# currently needs to borrow another tree's).
#   tree -- probe/tree name, also the default allowlist section name;
#   qflags -- coqc load paths; allow_section -- override when a tree's
#   section is named differently from the tree itself.
gate3_assumptions() {
  local tree="$1" qflags="$2" allow_section="${3:-$1}"
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
    local found_for_diff="$ASSUMPTIONS_DIR/$tree.found"
    if [ "$tree" = fxmss ]; then
      # fxmss.v doesn't pull in the same short-name imports ssprove.v does,
      # so coqc prints these two classical entries fully qualified; fold
      # them back to the spellings used everywhere else before diffing.
      found_for_diff="$ASSUMPTIONS_DIR/$tree.normalized"
      sed \
        -e 's/^Axioms\.R$/R/' \
        -e 's/^FunctionalExtensionality\.functional_extensionality_dep$/functional_extensionality_dep/' \
        "$ASSUMPTIONS_DIR/$tree.found" | sort -u > "$found_for_diff"
    fi
    local extra
    if extra=$(comm -23 "$found_for_diff" \
                 <(section_entries "$allow_section" | cut -f1 | sort -u)); [ -n "$extra" ]; then
      echo "FAIL: $tree assumptions outside the allowed baseline:"
      echo "$extra"
      ok=0
    fi
  fi
  [ "$ok" = 1 ]
}

# Gate 4 helper: emit one `<name> <digest>` line per axiom in a probe's
# output, where <digest> is the sha256 of the axiom's whole printed
# STATEMENT with whitespace squeezed to single spaces (so re-indentation or
# a line rewrap is not a change).  Every probe sets `Set Printing Width
# 4000`, so a statement is normally one line; an over-long one wraps onto
# indented continuation lines, which are folded back in here.
statement_digests() {
  grep -v '^Fetching opaque proofs from disk' "$1" \
    | awk '
        /^[A-Za-z_][^[:space:]]* : / {
          if (n != "") print n "\t" s
          n = $1; s = $0; next
        }
        /^[[:space:]]/ { if (n != "") s = s " " $0; next }
        { if (n != "") print n "\t" s; n = ""; s = "" }
        END { if (n != "") print n "\t" s }
      ' \
    | while IFS=$'\t' read -r n s; do
        printf '%s %s\n' "$n" \
          "$(printf '%s' "$s" | tr -s '[:space:]' ' ' | sed -e 's/^ //' -e 's/ $//' \
             | sha256sum | cut -d' ' -f1)"
      done \
    | sort -u
}

# Gate 4: every axiom the probe found must have the SAME printed statement
# it had when statements.sha256 was pinned.  Names are recorded per tree,
# because the same axiom prints differently under different trees' notation
# scopes (mathcomp's `seq` vs stdlib's `list`, qualified vs short names).
# Regenerate a line ONLY together with a deliberate, reviewed trust-surface
# change -- that is the whole point of the gate.
gate4_statements() {
  local tree="$1"
  local got="$ASSUMPTIONS_DIR/$tree.digests"

  statement_digests "$ASSUMPTIONS_DIR/$tree.out" > "$got"

  local ok=1 name digest pinned
  while read -r name digest; do
    pinned=$(awk -v t="$tree" -v n="$name" '$1 == t && $2 == n { print $3 }' "$STATEMENTS")
    if [ -z "$pinned" ]; then
      echo "FAIL: $tree $name has no pinned statement digest in $STATEMENTS"
      ok=0
    elif [ "$pinned" != "$digest" ]; then
      echo "FAIL: $tree $name statement CHANGED (pinned $pinned, found $digest)"
      ok=0
    fi
  done < "$got"
  [ "$ok" = 1 ]
}

# TRUST SURFACE report (printed once every gate is green). The large, low-signal
# ssprove/vst classical-logic baselines are grouped into one summary row each;
# every named trust anchor / advantage bound / hash-game axiom is still listed.
# Reporting only -- gate 3 already diffed the FULL found set against the FULL
# allowlist.
CLASSICAL_MODEL=()
CLASSICAL_SSPROVE=(
  R
  SPropBase.ax_proof_irrel
  boolp.constructive_indefinite_description
  boolp.functional_extensionality_dep
  boolp.propositional_extensionality
  functional_extensionality_dep
  realsum.__admitted__interchange_psum
)
CLASSICAL_VST=(
  Axioms.prop_ext
  ClassicalDedekindReals.sig_forall_dec
  ClassicalDedekindReals.sig_not_dec
  Classical_Prop.classic
  Ensembles.Extensionality_Ensembles
  Eqdep.Eq_rect_eq.eq_rect_eq
  FunctionalExtensionality.functional_extensionality_dep
)

is_classical() {
  local name="$1" arrname="$2"
  case "$name" in
    Axioms.R) name=R ;;
    FunctionalExtensionality.functional_extensionality_dep)
      name=functional_extensionality_dep ;;
  esac
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
    "SSProve/mathcomp-analysis library axioms -- excluded middle, choice, prop/functional extensionality, proof irrelevance, one admitted realsum lemma"
  print_trust_surface_rows ssprove CLASSICAL_SSPROVE
  printf '%-8s  %-42s  %s\n' "fxmss" "(shared SSProve classical baseline)" \
    "FXMSS_secure adds no project-local axiom or parameter"
  print_trust_surface_rows fxmss CLASSICAL_SSPROVE
  printf '%-8s  %-42s  %s\n' "vst" "(classical baseline, ${#CLASSICAL_VST[@]} entries)" \
    "CompCert/Coq-stdlib library axioms -- excluded middle, extensionality, UIP, classical reals decidability"
  print_trust_surface_rows vst CLASSICAL_VST
  echo "================================================================================"
}

# Run all four trees (model first -- the shared trust root). Quiet on success:
# one line per tree; gates speak only when they FAIL.
tree_fail=0
gate0_build_freshness model || tree_fail=1
gate1_proof_gaps model || tree_fail=1
gate2_model || tree_fail=1
gate3_assumptions model "$QFLAGS" || tree_fail=1
gate4_statements model || tree_fail=1
[ "$tree_fail" = 0 ] && echo "model    gates 0-4 green" || fail=1

tree_fail=0
gate0_build_freshness ssprove || tree_fail=1
gate1_proof_gaps ssprove "$ASSUMPTIONS_DIR" || tree_fail=1
gate2_ssprove || tree_fail=1
gate3_assumptions ssprove "$QFLAGS" || tree_fail=1
gate4_statements ssprove || tree_fail=1
[ "$tree_fail" = 0 ] && echo "ssprove  gates 0-4 green" || fail=1

tree_fail=0
gate0_build_freshness fxmss || tree_fail=1
gate1_proof_gaps fxmss || tree_fail=1
gate2_confined fxmss 'a^' fxmss || tree_fail=1
gate3_assumptions fxmss "$QFLAGS" || tree_fail=1
gate4_statements fxmss || tree_fail=1
[ "$tree_fail" = 0 ] && echo "fxmss    gates 0-4 green" || fail=1

tree_fail=0
gate0_build_freshness vst || tree_fail=1
gate1_proof_gaps vst || tree_fail=1
gate2_vst || tree_fail=1
gate3_assumptions vst "$QFLAGS" || tree_fail=1
gate4_statements vst || tree_fail=1
[ "$tree_fail" = 0 ] && echo "vst      gates 0-4 green" || fail=1

if [ "$fail" = 0 ]; then
  print_trust_surface
  echo
  echo "== assumptions/check.sh: ALL GATES GREEN =="
else
  echo
  echo "== assumptions/check.sh: FAILED =="
fi
exit "$fail"
