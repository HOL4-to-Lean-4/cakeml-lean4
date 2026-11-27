#!/bin/bash
# Test of the blocking prover preflight. Needs: built upstream CakeML/HOL4 scripts (CAKEMLDIR, HOLDIR), and the
# repository's lean/.lake/packages (run `lake build` in lean/ once). Runs no model.
#  1. clean prover workspace            -> preflight passes (exit 0)
#  2. plant HOL4 proof text in a Lean comment, a .md, a re-flowed comment, a code string, forbidden files
#                                        -> preflight fails (exit non-zero) each time
#  3. a translation whose comments quote HOL4 proofs -> mk_prove_ws strips them and the preflight then passes
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; W="$(dirname "$HERE")"; REPO="$(dirname "$W")"
export CAKEMLDIR="${CAKEMLDIR:-/root/upstream/cakeml}" HOLDIR="${HOLDIR:-/root/upstream/HOL}"
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
fail=0
expect() { # expect <0|nonzero> <description> <command...>
  want="$1"; desc="$2"; shift 2
  out="$("$@" 2>&1)"; rc=$?
  if { [ "$want" = 0 ] && [ $rc -eq 0 ]; } || { [ "$want" != 0 ] && [ $rc -ne 0 ]; }; then echo "PASS  ($rc) $desc"; else echo "FAIL  ($rc) $desc"; echo "$out" | tail -5; fail=1; fi
  LAST="$out"
}
# real HOL4 proof text, taken from the upstream script
python3 - "$CAKEMLDIR" "$T" <<'PY'
import sys, re, io
t = io.open(sys.argv[1] + "/semantics/proofs/typeSoundScript.sml", encoding="utf-8").read()
m = [x for x in re.finditer(r"^Proof\b(.*?)^QED", t, re.S | re.M) if len(x.group(1).split("\n")) > 6][0]
io.open(sys.argv[2] + "/real_proof.txt", "w", encoding="utf-8").write("Proof" + m.group(1) + "QED\n")
# a real statement (outside any proof) that a translator may legitimately quote
m = re.search(r"^Theorem (\w+)(\[.*?\])?:\n(.*?)^Proof", t, re.S | re.M)
io.open(sys.argv[2] + "/real_stmt.txt", "w", encoding="utf-8").write("Theorem " + m.group(1) + ":\n" + m.group(3))
PY
echo "--- real proof text used for planting (first 4 lines):"; head -4 "$T/real_proof.txt"
# fake translation: skeleton + one module with statement comment and a sorry theorem
python3 "$W/mk_lean_skeleton.py" "$T/tr/lean" >/dev/null
{ echo "/- HOL4:"; cat "$T/real_stmt.txt"; echo "-/"; echo "theorem demo : True := by sorry"; } > "$T/tr/lean/CakeML/Semantics/Proofs/TypeSound.lean"
echo "# Conventions" > "$T/tr/lean/CONVENTIONS.md"
PK="$REPO/lean/.lake/packages"
[ -d "$PK" ] || { echo "SKIP: $PK missing (run lake build in lean/)"; exit 2; }
echo "=== 1. clean workspace"
expect 0 "mk_prove_ws on a clean translation, preflight passes" python3 "$W/mk_prove_ws.py" --translation "$T/tr" --out "$T/p1" --name t
WS="$T/p1/ws"
expect 0 "preflight on the clean workspace (re-run)" python3 "$W/preflight_prover.py" "$WS"
echo "=== 2. plant proof text in a COPY of the clean workspace; each must FAIL"
plant() { rm -rf "$T/pl"; cp -r "$WS" "$T/pl"; }
F="$T/pl/lean/CakeML/Semantics/Proofs/TypeSound.lean"
plant; { echo "/- proof idea:"; cat "$T/real_proof.txt"; echo "-/"; } >> "$F"
expect nz "real HOL4 Proof..QED text in a Lean comment" python3 "$W/preflight_prover.py" "$T/pl"
plant; printf '/-\n  >- simp[]\n  >- (rw[] >> metis_tac[type_v_rules])\n-/\n' >> "$F"
expect nz "synthetic '>- simp[..]' tactic lines in a Lean comment" python3 "$W/preflight_prover.py" "$T/pl"
plant; printf -- '-- fs[Once type_v_cases] >> rw[]\n' >> "$F"
expect nz "tactic line in a Lean -- comment" python3 "$W/preflight_prover.py" "$T/pl"
plant; { echo "# notes"; cat "$T/real_proof.txt"; } > "$T/pl/NOTES.md"
expect nz "real proof text in a stray Markdown file (also an unexpected file)" python3 "$W/preflight_prover.py" "$T/pl"
plant; { echo "# notes"; cat "$T/real_proof.txt"; } > "$T/pl/lean/CONVENTIONS.md"
expect nz "real proof text in lean/CONVENTIONS.md" python3 "$W/preflight_prover.py" "$T/pl" --no-inventory
plant; printf 'Proof\n  rw[] >> simp[]\nQED\n' > "$T/pl/lean/NOTES.md"
expect nz "Proof ... QED block in .md" python3 "$W/preflight_prover.py" "$T/pl" --no-inventory
plant; python3 - "$T/real_proof.txt" "$F" <<'PY'
import sys, re
t = re.sub(r"\s+", " ", open(sys.argv[1], encoding="utf-8").read())      # re-flowed onto one line
open(sys.argv[2], "a", encoding="utf-8").write("/- " + t + " -/\n")
PY
expect nz "re-flowed proof text in a comment (single line)" python3 "$W/preflight_prover.py" "$T/pl"
plant; python3 - "$T/real_proof.txt" "$F" <<'PY'
import sys, re
t = re.sub(r"\s+", "", open(sys.argv[1], encoding="utf-8").read()).replace('"', "")[:300]
open(sys.argv[2], "a", encoding="utf-8").write('def hidden : String := "' + t + '"\n')
PY
expect nz "proof text hidden in a Lean string literal (code)" python3 "$W/preflight_prover.py" "$T/pl"
plant; cp "$CAKEMLDIR/semantics/proofs/primSemEnvScript.sml" "$T/pl/lean/primSemEnvScript.sml"
expect nz "a HOL4 script copied into the workspace" python3 "$W/preflight_prover.py" "$T/pl"
plant; mkdir -p "$T/pl/hol4"; echo x > "$T/pl/hol4/x.txt"
expect nz "hol4/ directory present" python3 "$W/preflight_prover.py" "$T/pl"
plant; ln -s "$CAKEMLDIR/semantics/proofs" "$T/pl/lean/link"
expect nz "symlink to the HOL4 sources" python3 "$W/preflight_prover.py" "$T/pl"
expect nz "unreadable HOL4 scripts: refuses to pass unchecked" python3 "$W/preflight_prover.py" "$WS" --cakeml "$T/nonexistent"
echo "=== 3. translation with HOL4 proof text in its comments: mk_prove_ws strips it, then preflight passes"
cp -r "$T/tr" "$T/tr2"
{ echo "/- HOL4 proof (copied by a careless translator):"; cat "$T/real_proof.txt"; echo "-/"; } >> "$T/tr2/lean/CakeML/Semantics/Proofs/TypeSound.lean"
{ echo "Notes"; cat "$T/real_proof.txt"; } >> "$T/tr2/lean/CONVENTIONS.md"
echo "Termination notes" > "$T/tr2/lean/PROGRESS.tsv"; mkdir -p "$T/tr2/hol4"; echo "x" > "$T/tr2/hol4/a"
expect 0 "mk_prove_ws strips planted proof text, preflight passes" python3 "$W/mk_prove_ws.py" --translation "$T/tr2" --out "$T/p2" --name t2
echo "$LAST" | head -3
echo "removed lines per file:"; tail -n +2 "$T/p2/strip_report.tsv" | cut -f1 | sort | uniq -c
expect 0 "stripped workspace passes standalone preflight" python3 "$W/preflight_prover.py" "$T/p2/ws"
[ ! -e "$T/p2/ws/hol4" ] && [ ! -e "$T/p2/ws/lean/PROGRESS.tsv" ] && echo "PASS  hol4/ and PROGRESS.tsv were not copied" || { echo "FAIL  disallowed inputs copied"; fail=1; }
if [ $fail -eq 0 ]; then echo "ALL PREFLIGHT TESTS PASSED"; else echo "SOME PREFLIGHT TESTS FAILED"; fi
exit $fail
