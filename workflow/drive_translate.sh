#!/bin/bash
# Keep resuming a translator run while it stops at a usage limit: after each stop, sleep until the reset time the CLI
# reports (plus 3 minutes), then resume the same session. usage: drive_translate.sh TRANSLATE_ROOT WSDIR OUTPREFIX FIRST_N [MAX]
set -uo pipefail
R="$(cd "$1" && pwd)"; W="$2"; P="$3"; n="$4"; MAX="${5:-20}"; HERE="$(cd "$(dirname "$0")" && pwd)"
while [ "$n" -le "$MAX" ]; do
  bash "$HERE/resume_translate.sh" "$R" "$W" "$P" "r$n"
  wait_s=$(python3 - "$R/$P.r$n.jsonl" <<'PY'
import json, re, sys, datetime as dt
r = None
for l in open(sys.argv[1]):
    try: o = json.loads(l)
    except Exception: continue
    if o.get("type") == "result": r = o
t = (r or {}).get("result") or ""
m = re.search(r"hit your .*limit.*resets (?:(\w{3} \d+), )?(\d+)(?::(\d+))?\s*(am|pm)\s*\(UTC\)", t)
if r is not None and not m:
    print(0); sys.exit()
now = dt.datetime.now(dt.timezone.utc)
if not m:
    print(1800); sys.exit()
h = int(m.group(2)) % 12 + (12 if m.group(4) == "pm" else 0); mi = int(m.group(3) or 0)
d = now.date()
if m.group(1):
    d = dt.datetime.strptime(f"{m.group(1)} {now.year}", "%b %d %Y").date()
t0 = dt.datetime(d.year, d.month, d.day, h, mi, tzinfo=dt.timezone.utc)
if t0 < now and not m.group(1): t0 += dt.timedelta(days=1)
print(max(60, int((t0 - now).total_seconds()) + 180))
PY
)
  [ "$wait_s" = "0" ] && { echo "finished at r$n"; exit 0; }
  echo "r$n stopped at a limit; sleeping $wait_s s"; sleep "$wait_s"; n=$((n+1))
done
