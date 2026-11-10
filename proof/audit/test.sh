#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
temporary=$(mktemp -d)
trap 'rm -rf "$temporary"' EXIT

expect_rejected() {
  if "$@" > "$temporary/rejected.out" 2>&1; then
    printf 'AUDIT TEST FAIL: command unexpectedly succeeded: %s\n' "$*" >&2
    exit 1
  fi
}

cat > "$temporary/hidden.v" <<'EOF'
#[local,
  polymorphic]
Parameter
  hidden
  : nat.
EOF
expect_rejected awk -f audit/declarations.awk "$temporary/hidden.v"
grep -q 'assumption declared: Parameter hidden : nat' "$temporary/rejected.out"

cat > "$temporary/comments.v" <<'EOF'
(* Axiom comment : True.
   (* Parameter nested : nat. *)
*)
Definition text := "Axiom string : True. (* "" *)".
Definition another := "first
Parameter string : nat.
last".
(* ignored *) Definition value := Some.Module.constant.
EOF
awk -f audit/declarations.awk "$temporary/comments.v"

cat > "$temporary/comment_string.v" <<'EOF'
(* "*)" "(*" *)
(* "doubled ""*)"" quote" *)
Definition comment_string_value := 0.
EOF
coqc -q "$temporary/comment_string.v" > "$temporary/comment_string.out" 2>&1
awk -f audit/declarations.awk "$temporary/comment_string.v"

cat > "$temporary/comment_string.v" <<'EOF'
(* "unterminated
EOF
expect_rejected awk -f audit/declarations.awk "$temporary/comment_string.v"
grep -q 'unclosed string in comment' "$temporary/rejected.out"

cat > "$temporary/hidden.v" <<'EOF'
(* outer (* inner *) *) #[local]
Axiom (* gap *)
  hidden : True.(* trailing comment *)
EOF
expect_rejected awk -f audit/declarations.awk "$temporary/hidden.v"
grep -q 'assumption declared: Axiom hidden : True' "$temporary/rejected.out"

cat > "$temporary/hidden.v" <<'EOF'
Timeout 5 Time #[local] Axiom hidden : True.
EOF
expect_rejected awk -f audit/declarations.awk "$temporary/hidden.v"
grep -q 'assumption declared: Axiom hidden : True' "$temporary/rejected.out"

mkdir -p "$temporary/internal/common"
cat > "$temporary/internal/common/machine.v" <<'EOF'
Module Type WORDSIZE.
Parameter
  wordsize : nat.
Axiom wordsize_not_zero : wordsize <> 0%nat.
End WORDSIZE.
EOF
expect_rejected awk -f audit/declarations.awk "$temporary/internal/common/machine.v"
grep -q 'assumption declared: Parameter wordsize : nat' "$temporary/rejected.out"
grep -q 'assumption declared: Axiom wordsize_not_zero : wordsize <> 0%nat' "$temporary/rejected.out"

cat > "$temporary/internal/common/address.v" <<'EOF'
Section AddrParams.
Hypothesis
  Hpb : (0 < pos_bound)%nat.
End AddrParams.
EOF
expect_rejected awk -f audit/declarations.awk "$temporary/internal/common/address.v"
grep -q 'assumption declared: Hypothesis Hpb : (0 < pos_bound)%nat' "$temporary/rejected.out"

# No file is exempt by name: the specification itself may not declare an assumption.
cat > "$temporary/shrincs.v" <<'EOF'
Parameter eps : nat.
Axiom secure : eps = 0.
EOF
(cd "$temporary" && expect_rejected awk -f "$OLDPWD/audit/declarations.awk" ./shrincs.v)
grep -q 'assumption declared: Parameter eps : nat' "$temporary/rejected.out"
grep -q 'assumption declared: Axiom secure : eps = 0' "$temporary/rejected.out"

while IFS= read -r import; do
  printf '%s\n' "$import" > "$temporary/internal_import.v"
  awk -f audit/declarations.awk "$temporary/internal_import.v"
  expect_rejected awk -v forbid_internal=1 -f audit/declarations.awk "$temporary/internal_import.v"
  grep -q 'internal import in public definition:' "$temporary/rejected.out"
done <<'EOF'
Require Shrincs.internal.hidden.
Require Import Shrincs.internal.hidden.
Require Export Shrincs.spec Shrincs.internal.hidden.
From Shrincs.internal Require hidden.
From Shrincs.internal Require Import hidden.
From Shrincs.internal.common Require Export hidden.
From Shrincs Require internal.hidden.
From Shrincs Require Import spec internal.hidden.
From Shrincs Require Export internal.hidden.
Import Shrincs.internal.hidden.
Export Shrincs.internal.hidden.
EOF

cat > "$temporary/internal_import.v" <<'EOF'
Timeout 5 Time #[local]
From (* outer (* inner *) *) Shrincs
  Require
  Import spec
  (* Require Import Shrincs.spec. *) internal.hidden.
EOF
expect_rejected awk -v forbid_internal=1 -f audit/declarations.awk "$temporary/internal_import.v"
grep -q 'internal import in public definition: From Shrincs Require Import spec internal.hidden' "$temporary/rejected.out"

cat > "$temporary/public_imports.v" <<'EOF'
Require Import Stdlib.Lists.List Shrincs.spec Shrincs.sha256.
Require Export Shrincs.contracts Shrincs.games.
From Stdlib Require Import Lists.List.
From Shrincs Require Import spec sha256 contracts games.
From Shrincs.internal_alias Require Import public.
From Other.Shrincs Require Import internal.hidden.
Require Import Other.Shrincs.internal.hidden Shrincs.internal_alias.public.
(* From Shrincs.internal Require Import hidden.
   (* Require Import Shrincs.internal.hidden. *) *)
Definition text := "Require Import Shrincs.internal.hidden. ""quoted""".
Definition multiline_text := "From Shrincs
Require Import internal.hidden.".
EOF
awk -v forbid_internal=1 -f audit/declarations.awk "$temporary/public_imports.v"

# Use the production SHA statement with a small independent interface.
# Its proposition has a proof, but accepting True in its place is unsound.
cat > "$temporary/interface.v" <<'EOF'
From Stdlib Require Import List.
Import ListNotations.
Module NullExtension.
Definition Espec := 0.
End NullExtension.
Definition sha256_QP := 0.
Module Hash.
Definition spec_sha256 := tt.
End Hash.
Definition emp := 0.
Definition VSU (_ : nat) (_ _ : list nat) (_ : nat)
    (_ : list unit) (_ : nat) : Prop := True /\ True.
Theorem shrincs_correct_and_secure : True.
Proof. exact I. Qed.
Check (shrincs_correct_and_secure : True).
EOF
awk '/^Check \(sha256_c_correct :/ { pin = 1 } pin { print } pin && /\)\./ { exit }' \
  audit/statement.v > "$temporary/pin.v"
test -s "$temporary/pin.v"
cat "$temporary/interface.v" > "$temporary/positive.v"
cat >> "$temporary/positive.v" <<'EOF'
Theorem sha256_c_correct : True /\ True.
Proof. split; exact I. Qed.
EOF
cat "$temporary/pin.v" >> "$temporary/positive.v"
bash audit/statement.sh "$temporary/positive.v" "$temporary/positive.out" -q
cat "$temporary/interface.v" > "$temporary/weakened.v"
cat >> "$temporary/weakened.v" <<'EOF'
Theorem sha256_c_correct : True.
Proof. exact I. Qed.
EOF
cat "$temporary/pin.v" >> "$temporary/weakened.v"
expect_rejected bash audit/statement.sh "$temporary/weakened.v" "$temporary/weakened.out" -q
grep -q 'expected to have type' "$temporary/weakened.out"
expect_rejected bash audit/statement.sh "$temporary/interface.v" "$temporary/missing.out" -q
grep -q 'Statement pin missing for sha256_c_correct' "$temporary/rejected.out"

# An old bundled WOTS AST can be newer than all C inputs. Changing the
# extraction recipe must still replace it with one AST per translation unit.
mkdir -p "$temporary/extraction/proof/clight" "$temporary/extraction/src" "$temporary/extraction/include" "$temporary/bin"
cp Makefile "$temporary/extraction/proof/Makefile"
touch "$temporary/extraction/proof/_RocqProject"
touch "$temporary/extraction/src/"{util,sha256,thash,wots}.c
touch "$temporary/extraction/include/"{util,sha256,thash,wots}.h
touch -t 200001010000 "$temporary/extraction/src/"*.c "$temporary/extraction/include/"*.h "$temporary/extraction/proof/Makefile"
for unit in util sha256 thash wots; do
  printf 'old bundled AST\n' > "$temporary/extraction/proof/clight/$unit.v"
done
touch -t 200101010000 "$temporary/extraction/proof/clight/"*.v
cat > "$temporary/bin/clightgen" <<'EOF'
#!/usr/bin/env bash
set -eu
output=
source=
sources=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    -o) output=$2; shift 2 ;;
    *.c) source=$1; sources=$((sources + 1)); shift ;;
    -include*) exit 1 ;;
    *) shift ;;
  esac
done
test -n "$output"
test -n "$source"
test "$sources" -eq 1
printf '%s\n' "$source" > "$output"
EOF
chmod +x "$temporary/bin/clightgen"
make --no-print-directory -s -C "$temporary/extraction/proof" -q extract
touch "$temporary/extraction/proof/Makefile"
PATH="$temporary/bin:$PATH" make --no-print-directory -s -C "$temporary/extraction/proof" extract
for unit in util sha256 thash wots; do
  grep -qx "../src/$unit.c" "$temporary/extraction/proof/clight/$unit.v"
done

printf 'Audit regression tests passed.\n'
