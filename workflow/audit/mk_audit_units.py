#!/usr/bin/env python3
"""Build one audit unit per translated module (Astra audits module by module; DECISIONS items 5, 8).

usage: mk_audit_units.py TRANSLATION_ROOT NAME OUTDIR
  TRANSLATION_ROOT: a translator workspace (holds lean/ and hol4/), e.g. WORK_ROOT/translate_opus/merged or .../ws2A
  NAME: sonnet | opus.  Writes OUTDIR/<NAME>/<Module>/{lean/,hol4/,PROMPT.md} and OUTDIR/<NAME>/units.tsv.
Lean files are copied with comments removed (as in Phase 1, audit/real/build_units.py), without .lake; hol4/ is copied whole
(scripts with proofs, saved statements, library sources: the auditor may read proofs)."""
import io, os, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from lean_strip import strip_comments
import modules

src, name, out = sys.argv[1], sys.argv[2], sys.argv[3]
brief = io.open(os.path.join(HERE, "BRIEF_audit.md"), encoding="utf-8").read()
mods = [l.rstrip("\n").split("\t") for l in io.open(os.path.join(src, "MODULES.tsv"), encoding="utf-8") if l.strip() and not l.startswith("script")]
root = os.path.join(out, name); os.makedirs(root, exist_ok=True)
rows = []
for script, mod, f in mods:
    u = os.path.join(root, mod)
    if os.path.exists(u): shutil.rmtree(u)
    for dp, dn, fn in os.walk(os.path.join(src, "lean")):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for x in fn:
            s = os.path.join(dp, x); r = os.path.relpath(s, src); d = os.path.join(u, r)
            os.makedirs(os.path.dirname(d), exist_ok=True)
            if x.endswith(".lean"):
                io.open(d, "w", encoding="utf-8", newline="\n").write(strip_comments(io.open(s, encoding="utf-8").read()))
            elif x in ("NAMES.tsv", "lakefile.lean", "lean-toolchain"):
                shutil.copy(s, d)
    shutil.copytree(os.path.join(src, "hol4"), os.path.join(u, "hol4"), ignore=shutil.ignore_patterns(".git"))
    io.open(os.path.join(u, "PROMPT.md"), "w", encoding="utf-8").write(brief.replace("@MODULE@", mod).replace("@FILE@", f))
    rows.append((mod, f, script))
io.open(os.path.join(root, "units.tsv"), "w", encoding="utf-8").write("module\tfile\tscript\n" + "".join("\t".join(r) + "\n" for r in rows))
print(f"{len(rows)} units in {root}")
