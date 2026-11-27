#!/bin/bash
# Test of scans/scan.py on a small hand-made translation: a clean one passes, one with every blocking violation fails,
# and the statement / type-variable mismatches are reported. Runs no model. Needs lake and the repository's lean/.lake/packages.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; W="$(dirname "$HERE")"; REPO="$(dirname "$W")"
export PATH="$HOME/.elan/bin:$PATH"
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
fail=0
mk() { # mk <dir>: skeleton project with built Batteries
  python3 "$W/mk_lean_skeleton.py" "$1" >/dev/null
  mkdir -p "$1/.lake"; python3 -c "import shutil,sys; shutil.copytree(sys.argv[1], sys.argv[2], ignore=shutil.ignore_patterns('.git','docs'))" "$REPO/lean/.lake/packages" "$1/.lake/packages"
}
cat > "$T/stmts.jsonl" <<'J'
{"thy":"mini","name":"good_id","kind":"theorem","origin":"script","type_vars":["'a"],"constants":["mini$good"]}
{"thy":"mini","name":"two_tv","kind":"theorem","origin":"script","type_vars":["'a","'b"],"constants":["mini$good","mini$other"]}
{"thy":"mini","name":"absent","kind":"theorem","origin":"script","type_vars":[],"constants":[]}
{"thy":"mini","name":"good","kind":"constant","type_vars":["'a"],"ty":0,"tys":[]}
J
printf 'hol4\tlean\tkind\nmini$good_id\tMini.good_id\tthm\nmini$two_tv\tMini.good_id\tthm\nmini$absent\tMini.absent\tthm\nmini$good\tMini.good\tconst\nmini$other\tMini.other\tconst\n' > "$T/NAMES.tsv"
echo "=== clean translation (translate phase: sorry theorem allowed)"
mk "$T/c"
cat > "$T/c/CakeML/Misc/Misc.lean" <<'L'
namespace Mini
def good (α : Type) (x : α) : α := x
theorem good_id (α : Type) (x : α) : good α x = x := by sorry
end Mini
L
python3 "$W/scans/scan.py" --lean "$T/c" --statements "$T/stmts.jsonl" --names "$T/NAMES.tsv" > "$T/c.out" 2>&1; rc=$?; cat "$T/c.out"
[ $rc -eq 0 ] && echo "PASS  clean translation: exit 0" || { echo "FAIL  clean translation exit $rc"; fail=1; }
grep -q "TYVARS.*two_tv" "$T/c.out" && grep -q "MISSING-THM.*absent" "$T/c.out" && echo "PASS  type-variable and missing-theorem mismatches reported" || { echo "FAIL  mismatches not reported"; fail=1; }
python3 "$W/scans/scan.py" --lean "$T/c" --statements "$T/stmts.jsonl" --names "$T/NAMES.tsv" --phase proved --no-build > "$T/c2.out" 2>&1; rc=$?
[ $rc -eq 1 ] && grep -q "sorry-after-proving" "$T/c2.out" && echo "PASS  phase proved: sorry theorem is blocking (exit 1)" || { echo "FAIL  phase proved exit $rc"; fail=1; }
echo "=== translation with every violation"
mk "$T/v"
cat > "$T/v/CakeML/Misc/Misc.lean" <<'L'
namespace Mini
def good (α : Type) (x : α) : α := x
def bad1 : Nat := sorry
axiom ax : 1 = 2
partial def loop (n : Nat) : Nat := loop n
opaque op : Nat
def f (n : Nat) : Nat := if h : n = 0 then 0 else f (n - 1)
decreasing_by sorry
theorem nd : 2 + 2 = 4 := by native_decide
-- a comment mentioning sorry, axiom, native_decide and partial def must not count
end Mini
L
python3 "$W/scans/scan.py" --lean "$T/v" > "$T/v.out" 2>&1; rc=$?; cat "$T/v.out"
[ $rc -eq 1 ] && echo "PASS  violations: exit 1" || { echo "FAIL  violations exit $rc"; fail=1; }
for k in sorry-in-def "axiom" native_decide decreasing_by-sorry "partial/opaque/unsafe"; do grep -q "^BLOCKING	$k" "$T/v.out" && echo "PASS  found $k" || { echo "FAIL  missing $k"; fail=1; }; done
echo "=== changed lakefile (new dependency)"
cp -r "$T/c" "$T/l"; echo 'require mathlib from git "https://example.invalid/mathlib"' >> "$T/l/lakefile.lean"
python3 "$W/scans/scan.py" --lean "$T/l" --no-build > "$T/l.out" 2>&1; rc=$?
[ $rc -eq 1 ] && grep -q "frozen-file" "$T/l.out" && echo "PASS  frozen-file violation" || { echo "FAIL  frozen-file exit $rc"; fail=1; }
[ $fail -eq 0 ] && echo "ALL SCAN TESTS PASSED" || echo "SOME SCAN TESTS FAILED"
exit $fail
