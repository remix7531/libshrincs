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
printf '%s\n' shrincs_correct_and_secure sha256_c_correct > "$temporary/pinned.names"
cat "$temporary/interface.v" > "$temporary/positive.v"
cat >> "$temporary/positive.v" <<'EOF'
Theorem sha256_c_correct : True /\ True.
Proof. split; exact I. Qed.
EOF
cat "$temporary/pin.v" >> "$temporary/positive.v"
bash audit/statement.sh "$temporary/pinned.names" "$temporary/positive.v" "$temporary/positive.out" -q
cat "$temporary/interface.v" > "$temporary/weakened.v"
cat >> "$temporary/weakened.v" <<'EOF'
Theorem sha256_c_correct : True.
Proof. exact I. Qed.
EOF
cat "$temporary/pin.v" >> "$temporary/weakened.v"
expect_rejected bash audit/statement.sh "$temporary/pinned.names" "$temporary/weakened.v" "$temporary/weakened.out" -q
grep -q 'expected to have type' "$temporary/weakened.out"
expect_rejected bash audit/statement.sh "$temporary/pinned.names" "$temporary/interface.v" "$temporary/missing.out" -q
grep -q 'Statement pin missing for sha256_c_correct' "$temporary/rejected.out"
expect_rejected bash audit/statement.sh "$temporary/absent.names" "$temporary/positive.v" "$temporary/positive.out" -q
grep -q 'No theorem names in' "$temporary/rejected.out"

# Gate 0 on a one-file theory: the list of tracked sources is required, an
# object must exist, and a compiled source git does not track is refused.
mkdir -p "$temporary/gate0/audit"
cp audit/check.sh "$temporary/gate0/audit/check.sh"
touch "$temporary/gate0/reviewed.v" "$temporary/gate0/reviewed.vo"
printf 'proof/reviewed.v\n' > "$temporary/tracked.txt"
expect_rejected bash "$temporary/gate0/audit/check.sh"
grep -q 'AUDIT FAIL (arguments)' "$temporary/rejected.out"
expect_rejected bash "$temporary/gate0/audit/check.sh" "$temporary/absent.txt"
grep -q 'AUDIT FAIL (arguments)' "$temporary/rejected.out"
touch "$temporary/gate0/stray.v" "$temporary/gate0/stray.vo"
expect_rejected bash "$temporary/gate0/audit/check.sh" "$temporary/tracked.txt"
grep -q 'AUDIT FAIL (gate 0): stray.v is compiled into the theory but not tracked by git' "$temporary/rejected.out"
rm "$temporary/gate0/stray.v" "$temporary/gate0/stray.vo" "$temporary/gate0/reviewed.vo"
expect_rejected bash "$temporary/gate0/audit/check.sh" "$temporary/tracked.txt"
grep -q 'AUDIT FAIL (gate 0): ./reviewed.vo missing' "$temporary/rejected.out"

touch "$temporary/gate0/reviewed.vo" "$temporary/gate0/orphan.vo"
expect_rejected bash "$temporary/gate0/audit/check.sh" "$temporary/tracked.txt"
grep -q 'AUDIT FAIL (gate 0): ./orphan.vo has no source in the theory' "$temporary/rejected.out"
rm "$temporary/gate0/orphan.vo"
printf 'proof/absent.v\n' >> "$temporary/tracked.txt"
expect_rejected bash "$temporary/gate0/audit/check.sh" "$temporary/tracked.txt"
grep -q 'AUDIT FAIL (gate 0): proof/absent.v is tracked but absent from the theory' "$temporary/rejected.out"

# Gate 3 takes the public claims from theorem.v: a tree without one is refused,
# a claim in another form is refused, and every claim must be probed.
mkdir -p "$temporary/gate3/audit"
cp audit/check.sh audit/declarations.awk "$temporary/gate3/audit/"
touch "$temporary/gate3/theorem.v" "$temporary/gate3/theorem.vo"
printf 'proof/theorem.v\n' > "$temporary/tracked3.txt"
expect_rejected bash "$temporary/gate3/audit/check.sh" "$temporary/tracked3.txt"
grep -q 'AUDIT FAIL (gate 3): theorem.v states no Theorem' "$temporary/rejected.out"
printf 'Theorem claim : True.\nProof. exact I. Qed.\nLemma unpinned : True.\nProof. exact I. Qed.\n' \
  > "$temporary/gate3/theorem.v"
expect_rejected bash "$temporary/gate3/audit/check.sh" "$temporary/tracked3.txt"
grep -q 'AUDIT FAIL (gate 3): theorem.v states a claim that is not a one-line Theorem command' "$temporary/rejected.out"
printf 'Theorem claim : True.\nProof. exact I. Qed.\n' > "$temporary/gate3/theorem.v"
printf 'Print Assumptions other.\n' > "$temporary/gate3/audit/probe.v"
expect_rejected bash "$temporary/gate3/audit/check.sh" "$temporary/tracked3.txt"
grep -q 'AUDIT FAIL (gate 3): audit/probe.v does not probe claim' "$temporary/rejected.out"

printf 'Audit regression tests passed.\n'
