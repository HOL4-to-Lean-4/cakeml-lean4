#!/bin/bash
# Resume a translator run that stopped early (for example at a usage limit), in the same session and with the same settings.
# usage: resume_translate.sh TRANSLATE_ROOT WSDIR OUTPREFIX TAG     (writes OUTPREFIX.TAG.jsonl/.err/.done; session id from OUTPREFIX.session)
set -euo pipefail
R="$(cd "$1" && pwd)"; W="$2"; OUT="$R/$3"; TAG="$4"
MODEL="$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['model'])" "$R/meta.json")"
SID="$(cat "$OUT.session")"
cd "$R/$W"
date -u +%FT%TZ > "$OUT.$TAG.start"
env -u CLAUDECODE claude -p "Your run was interrupted by a usage limit. Continue the task of BRIEF.md from where you stopped; check the current state of lean/ first. Same rules as before." \
  --resume "$SID" --model "$MODEL" --effort high --settings "$R/settings.json" --setting-sources "" \
  --strict-mcp-config --disable-slash-commands --tools "Read,Write,Edit,Glob,Grep,Bash" --permission-mode dontAsk \
  --output-format stream-json --verbose < /dev/null > "$OUT.$TAG.jsonl" 2> "$OUT.$TAG.err" || true
echo "rc=$?" > "$OUT.$TAG.done"; date -u +%FT%TZ >> "$OUT.$TAG.done"
