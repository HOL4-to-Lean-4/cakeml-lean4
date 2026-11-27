#!/bin/bash
# Export all theorem/definition statements of the milestone-1 theories from the BUILT upstream theories
# (no --fast: the theories were built with proofs checked).
# usage: run_export.sh [OUT_DIR]   (default: manifest/milestone1)
# env: HOLDIR, CAKEMLDIR (defaults /root/upstream/...), POLYML_DIR
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
export HOLDIR="${HOLDIR:-/root/upstream/HOL}" CAKEMLDIR="${CAKEMLDIR:-/root/upstream/cakeml}"
# Poly/ML: set POLYML_DIR (holding bin/ and lib/), or have `poly` on PATH (the pinned v5.9.2 build).
if [ -n "${POLYML_DIR:-}" ]; then export PATH="$POLYML_DIR/bin:$PATH" LD_LIBRARY_PATH="$POLYML_DIR/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"; fi
command -v poly >/dev/null || { echo "poly not found: set POLYML_DIR"; exit 2; }
OUT="${1:-$REPO/manifest/milestone1}"
TMP="$(mktemp -d)"
TSV="$REPO/manifest/milestone1/theories.tsv"
# theory names, from script paths
tail -n +2 "$TSV" | cut -f1 | while read -r p; do b="$(basename "$p")"; echo "${b%Script.sml}"; done > "$TMP/thys.txt"
# run inside the objs directory of the last theory: HOL4's loader resolves the first module relative to
# the working directory; all other directories are given by absolute path.
cat > "$TMP/run.sml" <<SML
val C = OS.Process.getEnv "CAKEMLDIR" |> valOf;
val _ = List.app (fn d => Meta.loadPath := (C ^ "/" ^ d ^ "/.hol/objs") :: !Meta.loadPath)
  ["misc","semantics","semantics/ffi","semantics/proofs","basis/pure"];
val _ = use "$HERE/export_theories.sml";
SML
sed -i '1i infix |> fun x |> f = f x;' "$TMP/run.sml"
cd "$CAKEMLDIR/semantics/proofs/.hol/objs"
EXPORT_THYS="$TMP/thys.txt" EXPORT_OUT="$TMP/export.raw" "$HOLDIR/bin/hol" run "$TMP/run.sml" > "$TMP/hol.log" 2>&1 || { tail -30 "$TMP/hol.log"; exit 1; }
cd "$REPO"
python3 -I "$HERE/postprocess.py" "$TMP/export.raw" "$TSV" "$CAKEMLDIR" "$OUT"
rm -rf "$TMP"
