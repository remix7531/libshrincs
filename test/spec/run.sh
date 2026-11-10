#!/usr/bin/env bash
# Check Shrincs.spec against the reference vectors, inside the Rocq kernel.
#
# Run through `make spec-test` once proof/spec.vo is built. Every case of
# test/spec/vectors/wots_c.kat becomes one Rocq file, and each file compiles
# only if the specification returns the recorded result. The cases run in
# parallel. The two key generations and the two signatures take minutes each.
set -euo pipefail
cd "$(dirname "$0")/../../proof"

vectors=../test/spec/vectors/wots_c.kat
work=../build/spec-test
flags=(-q -Q . Shrincs -Q "$work" SpecTest -w -notation-overridden,-ambiguous-paths,-abstract-large-number)

[ -f spec.vo ] || { echo "spec-test: proof/spec.vo is missing (run make prove)" >&2; exit 1; }
[ spec.v -nt spec.vo ] && { echo "spec-test: proof/spec.vo is older than spec.v (run make prove)" >&2; exit 1; }

rm -rf "$work"
mkdir -p "$work"
cp ../test/spec/harness.v "$work/harness.v"
coqc "${flags[@]}" "$work/harness.v"

cases=$(awk -v out="$work" -f ../test/spec/kat_to_v.awk "$vectors")

check() {
  local file=${!#}
  local log=${file%.v}.log
  if ! coqc "$@" > "$log" 2>&1; then
    printf 'spec-test FAIL: %s\n' "$file" >&2
    cat "$log" >&2
    return 255
  fi
}
export -f check

printf '%s\0' "$work"/case_*.v \
  | xargs -0 -n 1 -P "$(nproc)" bash -c 'check "$@"' check "${flags[@]}"

checked=$(find "$work" -name 'case_*.vo' | wc -l)
[ "$checked" -eq "$cases" ] || { echo "spec-test: $checked of $cases cases compiled" >&2; exit 1; }
printf 'Specification vectors: %d cases agree with the reference.\n' "$cases"
