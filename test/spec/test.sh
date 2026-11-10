#!/usr/bin/env bash
set -euo pipefail
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT

cat > "$temporary/one.kat" <<'EOF'
function = base_2b
x = 00
b = 4
outlen = 2
output = 0 0
EOF
mkdir "$temporary/generated"
bash generate.sh "$temporary/one.kat" "$temporary/generated" case_001.v
test -f "$temporary/generated/case_001.v"

cat "$temporary/one.kat" > "$temporary/two.kat"
printf '\n' >> "$temporary/two.kat"
cat "$temporary/one.kat" >> "$temporary/two.kat"
if bash generate.sh "$temporary/two.kat" "$temporary/generated" case_001.v > "$temporary/rejected.out" 2>&1; then
  printf 'Specification count test failed: extra case was accepted\n' >&2
  exit 1
fi
grep -q '2 cases for 1 declared targets' "$temporary/rejected.out"

if bash generate.sh "$temporary/one.kat" "$temporary/generated" case_001.v case_002.v > "$temporary/rejected.out" 2>&1; then
  printf 'Specification count test failed: missing case was accepted\n' >&2
  exit 1
fi
grep -q '1 cases for 2 declared targets' "$temporary/rejected.out"
printf 'Specification case count tests passed.\n'
