#!/usr/bin/env python3
"""Structural scans of a Lean translation. Exit status: 0 = no blocking violation, 1 = blocking violation, 2 = the scan could not run.

usage: scan.py [--lean DIR] [--phase translate|proved] [--statements statements.jsonl] [--names NAMES.tsv]
               [--allow-opaque FILE] [--no-build] [--require-all] [--out REPORT.tsv]

Blocking (DECISIONS item 12c; one finding = exit 1):
  sorry-in-def     a `sorry` (sorryAx) in anything that is not a theorem (defs, instances, inductives, `decreasing_by sorry`).
                   Phase `translate`: theorems may be sorry (they are the targets). Phase `proved`: no sorry anywhere.
  axiom            a declared `axiom`, or a declaration that depends on an axiom other than propext, Classical.choice, Quot.sound.
  native_decide    the text `native_decide` / `decide +kernel`, or a dependency on Lean.ofReduceBool.
  decreasing_by-sorry   `decreasing_by` whose block contains `sorry` (text) .
  partial / opaque / unsafe   `partial def`, `opaque`, `unsafe`, `implemented_by`, `extern`, unless the constant is named in --allow-opaque
                   (HOL4 itself leaves it unspecified; the list is a reviewed file).
  frozen-file      lakefile.lean, lake-manifest.json or lean-toolchain differ from this repository's lean/ (new dependency or toolchain).
  build-failed     `lake build` fails.
Reported, not blocking (unless --require-all): statements.jsonl against the Lean environment, through NAMES.tsv
  (columns: hol4, lean, kind with hol4 = `thy$name`, kind in thm|const|type):
  MISSING-THM / MISSING-CONST / MISSING-TYPE   mapped HOL4 item with no Lean constant of that name
  TYVARS           number of HOL4 type variables differs from the number of type binders of the Lean constant
  STMT-CONSTS      constants of the HOL4 statement (mapped) missing from, or extra in, the Lean statement
  UNMAPPED-CONST   constants of milestone theories used by a statement that NAMES.tsv does not map
Port notes vs Phase 1: KernelCheck.lean (sorry/axiom per constant) and TyVarsTS.lean (type binders) are in Dump.lean, run
with `lake env lean --run`. Not ported: the Phase 1 type-hash comparison of statements (it needs a canonical
HOL4-to-Lean term map, which Phase 2 does not have), `Frozen.lean` hashes (needed only after proving; see README), and the
transcript scan (scan2.py)."""
import argparse, csv, io, json, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import hol4proof

REPO = os.path.dirname(os.path.dirname(HERE))
FROZEN = ["lakefile.lean", "lake-manifest.json", "lean-toolchain"]
TXT = [
    ("axiom", re.compile(r"^[ \t]*(?:@\[[^\n]*\][ \t]*)?(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+)*axiom\b", re.M)),
    ("native_decide", re.compile(r"\bnative_decide\b|decide\s*\+kernel|\bofReduceBool\b")),
    # `opaque` itself is checked on the environment (below), where --allow-opaque applies
    ("partial/unsafe/extern", re.compile(r"(?:^|\s)partial\s+(?:def|instance|abbrev)\b|(?:^|\s)unsafe\s|\bimplemented_by\b|@\[\s*extern\b|@\[\s*export\b")),
]


def lake_bin():
    return shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")


def text_scan(lean_dir):
    out = []
    for dp, dn, fn in os.walk(lean_dir):
        dn[:] = [d for d in dn if d not in (".lake", "scratch")]
        for f in fn:
            if not f.endswith(".lean") or f == "lakefile.lean":
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, lean_dir)
            code, _ = hol4proof.lean_split(io.open(p, encoding="utf-8").read())
            for kind, rx in TXT:
                for m in rx.finditer(code):
                    out.append((kind, rel, code.count("\n", 0, m.start()) + 1, m.group(0).strip()[:60]))
            for m in re.finditer(r"decreasing_by", code):
                tail = code[m.end():]
                end = re.search(r"\n(?=[^\s])", tail)       # next line at column 0 ends the declaration
                blk = tail[: end.start()] if end else tail
                if re.search(r"\bsorry\b", blk):
                    out.append(("decreasing_by-sorry", rel, code.count("\n", 0, m.start()) + 1, "decreasing_by ... sorry"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", default=os.path.join(REPO, "lean"))
    ap.add_argument("--phase", choices=["translate", "proved"], default="translate")
    ap.add_argument("--statements", default=os.path.join(REPO, "manifest", "milestone1", "statements.jsonl"))
    ap.add_argument("--names")
    ap.add_argument("--root", default="CakeML")
    ap.add_argument("--allow-opaque", help="file: one Lean constant name per line that HOL4 leaves unspecified")
    ap.add_argument("--no-build", action="store_true")
    ap.add_argument("--require-all", action="store_true", help="make the mismatch lists blocking too")
    ap.add_argument("--out", help="write all findings as TSV")
    a = ap.parse_args()
    L = os.path.abspath(a.lean)
    blocking, info = [], []
    # frozen files
    for f in FROZEN:
        c, p = os.path.join(REPO, "lean", f), os.path.join(L, f)
        if L != os.path.join(REPO, "lean") and (not os.path.exists(p) or io.open(p, encoding="utf-8").read() != io.open(c, encoding="utf-8").read()):
            blocking.append(("frozen-file", f, 0, "differs from the repository's lean/" + f))
    if blocking:   # a changed dependency or toolchain: nothing else can be trusted or built
        for b in blocking:
            print("BLOCKING\t" + "\t".join(str(x) for x in b))
        print("SCAN FAILED")
        return 1
    blocking += text_scan(L)
    if not a.no_build:
        r = subprocess.run([lake_bin(), "build"], cwd=L, capture_output=True, text=True)
        if r.returncode != 0:
            blocking.append(("build-failed", "lake build", 0, (r.stdout + r.stderr).strip().split("\n")[-1][:200]))
    rows = []
    r = subprocess.run([lake_bin(), "env", "lean", "--run", os.path.join(HERE, "Dump.lean"), a.root], cwd=L, capture_output=True, text=True)
    if r.returncode != 0:
        print("SCAN ERROR: environment dump failed:\n" + (r.stdout + r.stderr)[-1500:], file=sys.stderr)
        return 2
    allow = set(io.open(a.allow_opaque).read().split()) if a.allow_opaque else set()
    C = {}
    for l in r.stdout.split("\n"):
        if l.startswith("C\t"):
            _, mod, name, kind, so, rb, uns, nb, oax, cons = l.split("\t")
            name = name.replace("«", "").replace("»", ""); cons = cons.replace("«", "").replace("»", "")
            C[name] = dict(mod=mod, kind=kind, sorry=so == "1", rb=rb == "1", uns=uns == "1", nb=int(nb), oax=[x for x in oax.split(",") if x], cons=set(x for x in cons.split(",") if x))
    for n, c in sorted(C.items()):
        loc = c["mod"]
        if c["kind"] == "axiom":
            blocking.append(("axiom", loc, 0, n))
        elif c["oax"]:
            blocking.append(("axiom", loc, 0, f"{n} uses {','.join(c['oax'])}"))
        if c["rb"]:
            blocking.append(("native_decide", loc, 0, f"{n} depends on Lean.ofReduceBool"))
        if c["sorry"] and (c["kind"] != "theorem" or a.phase == "proved"):
            blocking.append(("sorry-in-def" if c["kind"] != "theorem" else "sorry-after-proving", loc, 0, n))
        if (c["kind"] == "opaque" or c["uns"]) and n not in allow:
            blocking.append(("partial/opaque/unsafe", loc, 0, f"{n} ({c['kind']}{', unsafe/partial' if c['uns'] else ''})"))
    # ---- statements.jsonl against the Lean environment (reported) ----
    names = a.names or os.path.join(L, "NAMES.tsv")
    nm = {}
    if os.path.exists(names):
        for r_ in csv.reader(io.open(names, encoding="utf-8"), delimiter="\t"):
            if len(r_) >= 3 and r_[0] != "hol4" and not r_[0].startswith("#"):
                nm[r_[0]] = (r_[1].replace("«", "").replace("»", ""), r_[2])
    else:
        info.append(("NO-NAMES", names, 0, "NAMES.tsv missing: statement/type-variable comparison skipped"))
    if nm and os.path.exists(a.statements):
        recs = [json.loads(x) for x in io.open(a.statements, encoding="utf-8")]
        thys = {r_["thy"] for r_ in recs}
        constkeys = {r_["thy"] + "$" + r_["name"] for r_ in recs if r_["kind"] == "constant"}
        for r_ in recs:
            key = r_["thy"] + "$" + r_["name"]
            if r_["kind"] == "theorem" and r_.get("origin") == "script":
                k = ("thm", key)
            elif r_["kind"] == "constant":
                k = ("const", key)
            elif r_["kind"] == "type":
                k = ("type", key)
            else:
                continue
            if key not in nm:
                info.append(("UNMAPPED-" + k[0].upper(), r_["thy"], 0, key))
                continue
            ln = nm[key][0]
            c = C.get(ln)
            if c is None:
                info.append(("MISSING-" + k[0].upper(), r_["thy"], 0, f"{key} -> {ln}"))
                continue
            exp = len(r_["type_vars"]) if k[0] != "type" else r_["arity"]
            if k[0] == "thm" or k[0] == "const":
                if c["nb"] != exp:
                    info.append(("TYVARS", c["mod"], 0, f"{key} -> {ln}: HOL4 {exp} type variable(s), Lean {c['nb']} type binder(s)"))
            elif c["nb"] != exp:
                info.append(("TYVARS", c["mod"], 0, f"type {key} -> {ln}: HOL4 arity {exp}, Lean {c['nb']} binder(s)"))
            if k[0] == "thm":
                want, miss = set(), []
                for cn in r_["constants"]:
                    if cn.split("$")[0] not in thys:
                        continue
                    if cn in nm:
                        want.add(nm[cn][0])
                    else:
                        miss.append(cn)
                for cn in miss:
                    info.append(("UNMAPPED-CONST", r_["thy"], 0, f"{key} uses {cn}"))
                tyc = {x for x in c["cons"] if C.get(x, {}).get("kind") in ("def", "inductive", "ctor", "opaque", "axiom")}
                mapped = {nm[x][0] for x in constkeys if x in nm}
                lacking, extra = sorted(want - c["cons"]), sorted(x for x in (tyc & mapped) - want if ".match_" not in x)
                if lacking or extra:
                    info.append(("STMT-CONSTS", c["mod"], 0, f"{key} -> {ln}: missing in Lean {lacking[:6]}; extra in Lean {extra[:6]}"))
    allrows = [("BLOCKING",) + b for b in blocking] + [("info",) + i for i in info]
    if a.out:
        with io.open(a.out, "w", encoding="utf-8", newline="\n") as f:
            f.write("level\tcheck\twhere\tline\tdetail\n")
            for r_ in allrows:
                f.write("\t".join(str(x) for x in r_) + "\n")
    for r_ in allrows:
        print("\t".join(str(x) for x in r_))
    cnt = {}
    for b in blocking:
        cnt[b[0]] = cnt.get(b[0], 0) + 1
    ic = {}
    for i in info:
        ic[i[0]] = ic.get(i[0], 0) + 1
    ncon = len(C)
    print(f"SCAN: {ncon} constants in {a.root}.*, {sum(1 for c in C.values() if c['kind']=='theorem')} theorems, "
          f"{sum(1 for c in C.values() if c['kind']=='theorem' and c['sorry'])} with sorry; blocking {cnt or 0}; reported {ic or 0}")
    bad = bool(blocking) or (a.require_all and any(not i[0].startswith("NO-NAMES") for i in info))
    print("SCAN " + ("FAILED" if bad else "OK"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
