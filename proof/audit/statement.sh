#!/usr/bin/env bash
set -eu

names=$1
statement=$2
output=$3
shift 3

if ! [ -s "$names" ]; then
  printf 'No theorem names in %s\n' "$names" >&2
  exit 1
fi

while IFS= read -r theorem; do
  if ! grep -q "^Check ($theorem :" "$statement"; then
    printf 'Statement pin missing for %s in %s\n' "$theorem" "$statement" >&2
    exit 1
  fi
done < "$names"

if ! coqc "$@" "$statement" > "$output" 2>&1; then
  grep -v '^Fetching opaque proofs from disk' "$output" >&2 || true
  exit 1
fi
