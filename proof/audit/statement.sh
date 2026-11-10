#!/usr/bin/env bash
set -eu

statement=$1
output=$2
shift 2

for theorem in shrincs_correct_and_secure sha256_c_correct; do
  if ! grep -q "^Check ($theorem :" "$statement"; then
    printf 'Statement pin missing for %s in %s\n' "$theorem" "$statement" >&2
    exit 1
  fi
done

if ! coqc "$@" "$statement" > "$output" 2>&1; then
  grep -v '^Fetching opaque proofs from disk' "$output" >&2 || true
  exit 1
fi
