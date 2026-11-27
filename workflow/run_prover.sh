#!/bin/bash
# One proving session (Claude Opus 5.5), launched from a prover workspace made by mk_prove_ws.py.
# usage: run_prover.sh PROVE_ROOT        (PROVE_ROOT contains ws/, settings.json)
# Refuses to start unless the blocking preflight passes. Never uses --dangerously-skip-permissions: the
# settings.json written by mk_prove_ws.py is the only permission source (--setting-sources "").
# NOT run by the preparation work; the run itself is a model call.
set -euo pipefail
P="$(cd "$1" && pwd)"; HERE="$(cd "$(dirname "$0")" && pwd)"
python3 "$HERE/preflight_prover.py" "$P/ws" || { echo "preflight failed: not starting"; exit 1; }
cd "$P/ws"
date -u +%FT%TZ > "$P/run.start"
env -u CLAUDECODE claude -p "$(cat "$P/ws/BRIEF.md")" --model "${MODEL:-claude-opus-5-5}" --effort high \
  --settings "$P/settings.json" --setting-sources "" --strict-mcp-config --disable-slash-commands \
  --tools "Read,Write,Edit,Glob,Grep,Bash" --permission-mode dontAsk --output-format stream-json --verbose \
  < /dev/null > "$P/run.jsonl" 2> "$P/run.err" || true
echo "rc=$?" > "$P/run.done"; date -u +%FT%TZ >> "$P/run.done"
