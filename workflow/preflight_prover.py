#!/usr/bin/env python3
"""Blocking preflight for a PROVER workspace. Exit 0 only if the workspace holds no HOL4 proof text and no
HOL4 source tree. Any finding gives a non-zero exit (1 = findings, 2 = the check itself could not run).

usage: preflight_prover.py WORKSPACE [--cakeml DIR] [--holdir DIR] [--manifest TSV ...] [--no-inventory]

What it checks (see hol4proof.py for the detectors):
  1. Forbidden files anywhere in the workspace (also under `.lake`): HOL4 scripts and theory files
     (*Script.sml, *Theory.sml/.sig/.dat/.ui/.uo, Holmakefile, any *.sml/*.sig, hol4/, HOL4-src/, cakeml/,
     .git, source trees of the pinned upstream), symlinks, and (inventory) files outside the allowed layout.
  2. HOL4 proof text in EVERY text file: Lean comments, Markdown, tsv, json, anything. REGION (a line of a
     proof region of the scripts of all milestones, or of the HOL4 library scripts), WINDOW (re-flowed
     proof text), VOC (HOL4 tactic vocabulary). In Lean code only WINDOW hits count.
The proof index is built from the HOL4 scripts (default CAKEMLDIR and HOLDIR from the environment). If the
scripts cannot be read the preflight FAILS: it never passes unchecked.
The old Phase 1 `prooftext.py` only printed a count; this one blocks."""
import argparse, fnmatch, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hol4proof

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FORBIDDEN_NAME = ["*Script.sml", "*Theory.sml", "*Theory.sig", "*Theory.dat", "*Theory.ui", "*Theory.uo", "Holmakefile", "*.sml", "*.sig", "*.ML",
                  "holbuild.toml", "holproject.toml", "holextra.manifest.toml"]
FORBIDDEN_DIR = ["hol4", "HOL4-src", "HOL4", "cakeml", "CakeML-src", ".git", ".hol", "upstream", "vendor", "runs", "proofs_hol4"]
# Layout of a prover workspace (relative to its root). Everything else is unexpected.
ALLOWED_ROOT_FILES = {"BRIEF.md"}
ALLOWED_ROOT_DIRS = {"lean", "hol4_statements"}
SKIP_BINARY_EXT = (".olean", ".ilean", ".o", ".a", ".so", ".c", ".hash", ".trace", ".ir", ".rlean", ".ltar", ".bc", ".export", ".dylib", ".dll")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("workspace")
    ap.add_argument("--cakeml", default=os.environ.get("CAKEMLDIR", "/root/upstream/cakeml"))
    ap.add_argument("--holdir", default=os.environ.get("HOLDIR", "/root/upstream/HOL"))
    ap.add_argument("--manifest", action="append", help="theories.tsv (default: every manifest/*/theories.tsv of this repository)")
    ap.add_argument("--statements", default=os.path.join(REPO, "manifest", "milestone1", "statements.jsonl"),
                    help="statements.jsonl; hol4_statements/*.txt identical to its regeneration are exempt from the WINDOW scan")
    ap.add_argument("--no-inventory", action="store_true", help="skip the allowed-layout check (e.g. for a workspace already worked in)")
    a = ap.parse_args()
    ws = os.path.abspath(a.workspace)
    if not os.path.isdir(ws):
        print("PREFLIGHT ERROR: not a directory:", ws)
        return 2
    tsvs = a.manifest or sorted(os.path.join(REPO, "manifest", d, "theories.tsv") for d in os.listdir(os.path.join(REPO, "manifest"))
                                if os.path.exists(os.path.join(REPO, "manifest", d, "theories.tsv")))
    try:
        ix = hol4proof.build_index(a.cakeml, tsvs, a.holdir if os.path.isdir(a.holdir) else None)
    except OSError as e:
        print("PREFLIGHT ERROR: cannot read the HOL4 scripts, so nothing can be verified:", e)
        return 2
    if ix.nscripts == 0 or not ix.lines:
        print("PREFLIGHT ERROR: empty proof index")
        return 2
    exempt = {}
    if os.path.exists(a.statements):
        exempt = {os.path.join("hol4_statements", t + ".txt"): x for t, x in hol4proof.render_statements(a.statements).items()}
    bad = []
    nfiles = 0
    for root, dirs, files in os.walk(ws):
        rel_root = os.path.relpath(root, ws)
        for d in list(dirs):
            full = os.path.join(root, d)
            if os.path.islink(full):
                bad.append((os.path.join(rel_root, d), 0, "SYMLINK", "directory symlink"))
                dirs.remove(d)
            elif d in FORBIDDEN_DIR:
                bad.append((os.path.relpath(full, ws), 0, "FORBIDDEN-DIR", d))
                dirs.remove(d)
        if rel_root == "." and not a.no_inventory:
            for d in dirs:
                if d not in ALLOWED_ROOT_DIRS:
                    bad.append((d, 0, "UNEXPECTED-DIR", "not in the prover layout"))
        for f in files:
            full = os.path.join(root, f)
            rel = os.path.relpath(full, ws)
            if os.path.islink(full):
                bad.append((rel, 0, "SYMLINK", "file symlink"))
                continue
            if any(fnmatch.fnmatch(f, p) for p in FORBIDDEN_NAME):
                bad.append((rel, 0, "FORBIDDEN-FILE", f))
                continue
            if rel_root == "." and not a.no_inventory and f not in ALLOWED_ROOT_FILES:
                bad.append((rel, 0, "UNEXPECTED-FILE", "not in the prover layout"))
            if f.endswith(SKIP_BINARY_EXT):
                continue
            nfiles += 1
            if rel in exempt and open(full, encoding="utf-8").read() == exempt[rel]:
                continue
            for ln, reason, sn in hol4proof.check_file(full, ix):
                bad.append((rel, ln, reason, sn))
    for rel, ln, reason, sn in bad:
        print(f"{reason}\t{rel}:{ln}\t{sn}")
    print(f"PREFLIGHT {'FAILED' if bad else 'OK'}: {nfiles} text files checked against {ix.nscripts} HOL4 scripts "
          f"({ix.nregions} proof regions); {len(bad)} finding(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
