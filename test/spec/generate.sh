#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -lt 3 ]; then
  printf 'generate.sh: expected a vector file, output directory and target files\n' >&2
  exit 1
fi

vector_file=$1
output_directory=$2
shift 2
script_directory=$(cd "$(dirname "$0")" && pwd)
case_count=$(awk -v out="$output_directory" -f "$script_directory/kat_to_v.awk" "$vector_file")

if [ "$case_count" -ne "$#" ]; then
  printf 'Specification target count mismatch: %s cases for %s declared targets\n' "$case_count" "$#" >&2
  exit 1
fi
