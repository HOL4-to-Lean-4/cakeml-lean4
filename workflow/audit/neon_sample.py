#!/usr/bin/env python3
"""Neon's sample (DECISIONS item 14): every finding on a definition, datatype or inductive, plus 20% of the other findings,
drawn evenly from the two translations and across classes, with a fixed seed.
usage: neon_sample.py OUT.json AUDIT_ROOT/sonnet AUDIT_ROOT/opus   (reads <root>/out/*.last, Astra's JSON answers)"""
import glob, io, json, math, os, random, re, sys
SEED, RATE = 20261127, 0.20
out, roots = sys.argv[1], sys.argv[2:]
allf = []
for r in roots:
    name = os.path.basename(r.rstrip("/"))
    for p in sorted(glob.glob(os.path.join(r, "out", "*.last"))):
        t = io.open(p, encoding="utf-8").read(); m = re.search(r"\{.*\}", t, re.S)
        try: j = json.loads(m.group(0))
        except Exception: print("unparsed", p, file=sys.stderr); continue
        for f in j.get("findings", []):
            allf.append(dict(f, translation=name, module=j.get("module"), uid=f"{name}:{j.get('module')}:{f.get('id')}"))
defs = [f for f in allf if f.get("kind") in ("definition", "datatype", "inductive")]
rest = [f for f in allf if f not in defs]
rng = random.Random(SEED); pick = []
for tr in sorted({f["translation"] for f in rest}):
    for cl in sorted({f.get("class") for f in rest}):
        g = sorted([f for f in rest if f["translation"] == tr and f.get("class") == cl], key=lambda f: f["uid"])
        if g: pick += rng.sample(g, max(1, math.ceil(RATE * len(g))))
s = defs + pick
json.dump({"seed": SEED, "rate": RATE, "total": len(allf), "definitions": len(defs), "sampled_rest": len(pick), "findings": s,
           "unsampled": [f["uid"] for f in rest if f not in pick]}, io.open(out, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
print(f"{len(allf)} findings: {len(defs)} on definitions + {len(pick)} of {len(rest)} others -> {len(s)} for Neon")
