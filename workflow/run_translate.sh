#!/bin/bash
# One translator run, in its own workspace, from a folder made by mk_translate_ws.py.
# usage: run_translate.sh TRANSLATE_ROOT WSDIR BRIEF OUTPREFIX     (e.g. run_translate.sh $WORK_ROOT/translate_opus ws1 ws1/BRIEF.md ws1)
# The model comes from TRANSLATE_ROOT/meta.json. Permissions: only TRANSLATE_ROOT/settings.json (--setting-sources "" ignores all
# other settings); never --dangerously-skip-permissions. Not run by the preparation work: this starts a model call.
set -euo pipefail
R="$(cd "$1" && pwd)"; W="$2"; BR="$3"; OUT="$R/$4"
MODEL="$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['model'])" "$R/meta.json")"
cd "$R/$W"
date -u +%FT%TZ > "$OUT.start"
env -u CLAUDECODE claude -p "$(cat "$R/$BR")" --model "$MODEL" --effort high --settings "$R/settings.json" --setting-sources "" \
  --strict-mcp-config --disable-slash-commands --tools "Read,Write,Edit,Glob,Grep,Bash" --permission-mode dontAsk \
  --output-format stream-json --verbose < /dev/null > "$OUT.jsonl" 2> "$OUT.err" || true
echo "rc=$?" > "$OUT.done"; date -u +%FT%TZ >> "$OUT.done"
