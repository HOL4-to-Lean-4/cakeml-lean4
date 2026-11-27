#!/bin/bash
# Astra audit of every unit of one translation: run_audit.sh UNITS_ROOT/<name> [MODEL]
# Uses candle-hol4-lean4-study/tools/astra_gateway/codex_astra.sh (read-only sandbox, the reported model logged in each meta.json).
set -euo pipefail
R="$(cd "$1" && pwd)"; M="${2:-gpt-6.2-astra}"
CA="${CODEX_ASTRA:-$(cd "$(dirname "$0")/../../.." && pwd)/candle-hol4-lean4-study/tools/astra_gateway/codex_astra.sh}"
tail -n +2 "$R/units.tsv" | cut -f1 | while read -r mod; do
  [ -s "$R/out/$mod.last" ] && continue
  mkdir -p "$R/out"; bash "$CA" "$R/$mod" "$R/out/$mod" "$M" < "$R/$mod/PROMPT.md" || echo "unit $mod rc=$?" >&2
done
