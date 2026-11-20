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

# Gate 7 uses an independent, small game interface. The production classifier
# and pin compiler still run in Rocq; inferred result types are not mocked.
audit_directory=$PWD/audit
base=$temporary/guard_base
mkdir -p "$base/internal/ssprove/lib/guard" "$base/audit"
cat > "$base/internal/ssprove/lib/prelude.v" <<'EOF'
Inductive game (E : Type) : Type := Game : game E.
Definition AdvOf {E : Type} (_ : game E) : Prop := True /\ True.
EOF
cat > "$base/games.v" <<'EOF'
From Shrincs.internal.ssprove.lib Require Import prelude.
Definition explicit : game nat := Game nat.
Module Outer.
Module Inner.
Section Parameters.
Variable E : Type.
Definition nested := Game E.
End Parameters.
End Inner.
End Outer.
Module Alias := Outer.
EOF
cat > "$base/schemes.v" <<'EOF'
From Shrincs Require Import games.
Definition inferred (n : nat) := if Nat.eqb n 0 then explicit else explicit.
EOF
cat > "$base/internal/ssprove/lib/guard/fixture.v" <<'EOF'
From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import games schemes.
Lemma explicit_guard : AdvOf explicit.
Proof. exact (conj I I). Qed.
Module Outer.
Section Parameters.
Variable E : Type.
Lemma nested_guard : AdvOf (games.Outer.Inner.nested E).
Proof. exact (conj I I). Qed.
End Parameters.
End Outer.
Lemma inferred_guard (n : nat) : AdvOf (Shrincs.schemes.inferred n).
Proof. exact (conj I I). Qed.
EOF
cat > "$base/audit/guards.v" <<'EOF'
From Shrincs.internal.ssprove.lib Require Import prelude guard.fixture.
From Shrincs Require Import games schemes.
Check (Shrincs.internal.ssprove.lib.guard.fixture.explicit_guard : AdvOf Shrincs.games.explicit).
Check (Shrincs.internal.ssprove.lib.guard.fixture.Outer.nested_guard : forall E, AdvOf (Shrincs.games.Outer.Inner.nested E)).
Check (Shrincs.internal.ssprove.lib.guard.fixture.inferred_guard : forall n, AdvOf (Shrincs.schemes.inferred n)).
EOF
for source in internal/ssprove/lib/prelude games schemes internal/ssprove/lib/guard/fixture; do
  coqc -q -Q "$base" Shrincs "$base/$source.v"
done

guard_reset() {
  rm -rf "$temporary/gate7"
  cp -R "$base" "$temporary/gate7"
}

guard_check() (
  cd "$temporary/gate7"
  python3 "$audit_directory/guard_inventory.py" audit/guards.v audit -q -Q . Shrincs
)

guard_accept() {
  guard_check > "$temporary/accepted.out" 2>&1 || {
    cat "$temporary/accepted.out" >&2
    exit 1
  }
  grep -qxF 'guard coverage: 3 games, 3 pinned guards' "$temporary/accepted.out"
  printf 'Gate 7 fixture %s: accepted (3 games, 3 pinned guards).\n' "$1"
}

guard_reject() {
  expect_rejected guard_check
  grep -qF "$2" "$temporary/rejected.out"
  printf 'Gate 7 fixture %s: rejected: %s\n' "$1" "$2"
}

guard_compile() {
  coqc -q -Q "$temporary/gate7" Shrincs "$temporary/gate7/$1.v"
}

guard_reset
guard_accept inferred_alias_and_nested_scopes

# Declaration wrappers must not hide an inferred game from the inventory.
cat > "$temporary/gate7/schemes.v" <<'EOF'
From Stdlib Require Import Program.Tactics.
From Shrincs Require Import games.
#[local] Program Definition inferred (n : nat) :=
  if Nat.eqb n 0 then explicit else explicit.
EOF
guard_compile schemes
guard_compile internal/ssprove/lib/guard/fixture
guard_accept declaration_modifiers

# Apparent declarations, module boundaries and pins are inert in comments
# and strings, including doubled quotes and quotes inside nested comments.
guard_reset
cat >> "$temporary/gate7/schemes.v" <<'EOF'
From Stdlib Require Import Strings.String.
(* Module Fake. (* Definition missing := explicit. *) End Fake. *)
(* "*)" "(*" *)
Definition text := "Module Fake. Definition missing := explicit.
End Fake. ""quoted"" (* not a comment *)"%string.
EOF
cat >> "$temporary/gate7/internal/ssprove/lib/guard/fixture.v" <<'EOF'
(* Lemma fake : True. (* Theorem also_fake : True. *) *)
From Stdlib Require Import Strings.String.
Definition text := "Lemma fake : True. Module Unclosed."%string.
EOF
cat >> "$temporary/gate7/audit/guards.v" <<'EOF'
(* Check (Shrincs.internal.ssprove.lib.guard.fixture.fake : True). *)
From Stdlib Require Import Strings.String.
Definition text := "Check (Shrincs.internal.ssprove.lib.guard.fixture.fake : True)."%string.
EOF
guard_compile schemes
guard_compile internal/ssprove/lib/guard/fixture
guard_accept fake_declarations

guard_reset
cat >> "$temporary/gate7/schemes.v" <<'EOF'
Definition unguarded := inferred.
EOF
guard_compile schemes
guard_reject missing_game_guard 'Shrincs.schemes.unguarded has no pinned guard'

guard_reset
cat >> "$temporary/gate7/internal/ssprove/lib/guard/fixture.v" <<'EOF'
Lemma unpinned : True.
Proof. exact I. Qed.
EOF
guard_compile internal/ssprove/lib/guard/fixture
guard_reject missing_full_type_pin 'Shrincs.internal.ssprove.lib.guard.fixture.unpinned has no full-type Check'

guard_reset
sed -i 's/Lemma explicit_guard : AdvOf explicit\./Lemma explicit_guard : True./; 0,/exact (conj I I)/s//exact I/' \
  "$temporary/gate7/internal/ssprove/lib/guard/fixture.v"
guard_compile internal/ssprove/lib/guard/fixture
guard_reject weakened_guard 'expected to have type'
grep -qF 'audit/guards.v does not compile' "$temporary/rejected.out"

# A fake pin may neither cover a game nor count as the lemma's full-type pin.
for hiding in comment string; do
  guard_reset
  pin=$(sed -n '/^Check .*\.inferred_guard /p' "$base/audit/guards.v")
  sed -i '/^Check .*\.inferred_guard /d' "$temporary/gate7/audit/guards.v"
  if [ "$hiding" = comment ]; then
    printf '(* outer (* %s *) *)\n' "$pin" >> "$temporary/gate7/audit/guards.v"
  else
    printf 'From Stdlib Require Import Strings.String.\nDefinition text := "%s"%%string.\n' "$pin" \
      >> "$temporary/gate7/audit/guards.v"
  fi
  guard_reject "fake_pin_in_$hiding" 'Shrincs.schemes.inferred has no pinned guard'
  grep -qF 'Shrincs.internal.ssprove.lib.guard.fixture.inferred_guard has no full-type Check' \
    "$temporary/rejected.out"
done

# A compiled module signature is outside the scanner's supported scopes;
# refusing it is safer than silently skipping declarations in its body.
guard_reset
printf 'Module Type Signature. End Signature.\n' >> "$temporary/gate7/games.v"
guard_compile games
guard_reject unsupported_scope 'unsupported scope Module Type Signature'

# Malformed-source cases exercise the scanner directly.

guard_reset
printf 'End Missing.\n' >> "$temporary/gate7/games.v"
guard_reject unmatched_end 'unmatched End Missing'

guard_reset
printf 'Section Unclosed.\n' >> "$temporary/gate7/games.v"
guard_reject unclosed_scope 'unclosed scope'

for kind in comment string comment_string; do
  guard_reset
  case "$kind" in
    comment) input='(* unclosed'; diagnostic='unclosed comment' ;;
    string) input='Definition text := "unclosed'; diagnostic='unclosed string' ;;
    comment_string) input='(* "unclosed'; diagnostic='unclosed string in comment' ;;
  esac
  printf '%s\n' "$input" >> "$temporary/gate7/games.v"
  guard_reject "unterminated_$kind" "$diagnostic"
done

guard_reset
printf 'Definition unfinished := 0\n' >> "$temporary/gate7/games.v"
guard_reject unfinished_command 'unfinished Rocq command'

guard_reset
rm "$temporary/gate7/games.vo"
guard_reject missing_object 'games.v: inventory needs a built .vo'

guard_reset
rm "$temporary/gate7/audit/guards.v"
guard_reject missing_guards 'audit/guards.v missing'

# Neither an empty game inventory nor an empty pin set is a passing audit.
guard_reset
printf 'Definition value := 0.\n' > "$temporary/gate7/games.v"
printf 'Definition value := 0.\n' > "$temporary/gate7/schemes.v"
guard_compile games
guard_compile schemes
rm "$temporary/gate7/internal/ssprove/lib/guard/fixture.v"
guard_reject empty_games 'empty guard inventory'
printf '(* No pins. *)\n' > "$temporary/gate7/audit/guards.v"
guard_reject empty_inventory 'empty guard inventory'

# The command-output mode shares the declaration scanner's lexer. Check the
# exact enclosing scopes, modifier removal and comment/string masking.
cat > "$temporary/scoped_commands.v" <<'EOF'
From Stdlib Require Import Strings.String.
Module Outer.
Module Export Inner.
Section Parameters.
Variable E : Type.
Section Nested.
#[local] Program Definition identity (x : E) := x.
(* Module Fake. (* Section Hidden. *) End Fake. *)
(* "*)" "(*" *)
Definition text := "End Nested.
Module Fake. ""quoted"" (* not a comment *)"%string.
End Nested.(* Axiom hidden : True. *)
End Parameters.
End Inner.
End Outer.
Module Alias := Outer.Inner.
Redirect "ignored.out" Time #[local] Definition value := 0.
EOF
cat > "$temporary/scoped_commands.expected" <<'EOF'
		From Stdlib Require Import Strings.String
		Module Outer
Outer		Module Export Inner
Outer.Inner		Section Parameters
Outer.Inner	Parameters	Variable E : Type
Outer.Inner	Parameters	Section Nested
Outer.Inner	Parameters.Nested	Definition identity (x : E) := x
Outer.Inner	Parameters.Nested	Definition text := STRING %string
Outer.Inner	Parameters.Nested	End Nested
Outer.Inner	Parameters	End Parameters
Outer.Inner		End Inner
Outer		End Outer
		Module Alias := Outer.Inner
		Definition value := 0
EOF
awk -v emit_commands=1 -f audit/declarations.awk "$temporary/scoped_commands.v" \
  > "$temporary/scoped_commands.actual"
diff -u "$temporary/scoped_commands.expected" "$temporary/scoped_commands.actual"
printf 'Audit command-output fixture passed.\n'

printf 'Audit regression tests passed.\n'
