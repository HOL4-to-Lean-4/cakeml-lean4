#!/bin/bash
# First run of a translator workspace, then resume it after every usage limit (drive_translate.sh).
# usage: drive_part.sh TRANSLATE_ROOT WSDIR
set -uo pipefail
R="$(cd "$1" && pwd)"; W="$2"; HERE="$(cd "$(dirname "$0")" && pwd)"
[ -f "$R/$W.done" ] || bash "$HERE/run_translate.sh" "$R" "$W" "$W/BRIEF.md" "$W"
python3 - "$R/$W.jsonl" > "$R/$W.session" <<'PY'
import json, sys
s = None
for l in open(sys.argv[1]):
    try: o = json.loads(l)
    except Exception: continue
    s = o.get("session_id") or s
print(s)
PY
python3 - "$R/$W.jsonl" <<'PY' && exec bash "$HERE/drive_translate.sh" "$R" "$W" "$W" 1
import json, re, sys
r = None
for l in open(sys.argv[1]):
    try: o = json.loads(l)
    except Exception: continue
    if o.get("type") == "result": r = o
sys.exit(0 if r is None or re.search(r"hit your .*limit", r.get("result") or "") else 1)
PY
echo "$W finished in the first run"
