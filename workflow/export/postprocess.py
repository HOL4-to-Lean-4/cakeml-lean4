"""Turn the raw export of export_theories.sml into manifest/milestone1/statements.jsonl and
export_counts.tsv, check every statement, and compare with theories.tsv.
usage: postprocess.py RAW THEORIES_TSV CAKEMLDIR OUT_DIR
Adapted from candle-hol4-lean4-study/tools/hol4_query/postprocess.py (new term encoding, see
export_theories.sml). Fails (non-zero exit) on a record with a SML error, an ill-typed term or a
statement that is not of type bool."""
import collections, csv, hashlib, io, json, os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.setrecursionlimit(200000)

raw, tsv, cakeml, out = sys.argv[1:5]
rows = [json.loads(l) for l in io.open(raw, encoding="utf-8") if l.strip()]
errs = [r for r in rows if r["kind"] == "error"]
BOOL, FUN = "min$bool", "min$fun"


class Rec:
    def __init__(s, r):
        s.r = r
        s.tys = r.get("tys", [])
        s.tv = set()
        s.consts = set()
        s.tyinfo = {}

    def tyi(s, i):
        if i in s.tyinfo:
            return s.tyinfo[i]
        t = s.tys[i]
        if isinstance(t, str):
            s.tv.add(t)
            res = (t, ())
        else:
            res = (t[0], tuple(t[1:]))
        s.tyinfo[i] = res
        return res


def typeof_struct(rec, t):
    """Canonical type id of term t; checks that every application is well typed."""
    canon = rec.canon = getattr(rec, "canon", {})
    memo = rec.memo = getattr(rec, "memo", {})

    inv = rec.inv = getattr(rec, "inv", {})

    def cid(n, args):
        if (n, args) not in canon:
            inv[len(canon)] = (n, args)
            canon[(n, args)] = len(canon)
        return canon[(n, args)]

    def struct(i):
        if i not in memo:
            n, args = rec.tyi(i)
            memo[i] = cid(n, tuple(struct(a) for a in args))
        return memo[i]
    def go(t):
        k = t[0]
        if k == "v":
            return struct(t[2])
        if k == "c":
            rec.consts.add(t[1])
            return struct(t[2])
        if k == "a":
            f, x = go(t[1]), go(t[2])
            n, args = inv[f]
            assert n == FUN and args[0] == x, "ill-typed application"
            return args[1]
        if k == "l":
            return cid(FUN, (struct(t[2]), go(t[3])))
        raise AssertionError(k)
    return go(t), canon.get((BOOL, ()))


# ---- names declared in the scripts (to tell script-level from generated theorems) ----
tsvrows = list(csv.reader(io.open(tsv, encoding="utf-8"), delimiter="\t"))[1:]


from hol4proof import strip_comments  # noqa: E402


decl = {}
KW = re.compile(r"^(Theorem|Triviality|Definition|Inductive|CoInductive|Datatype)\b[ \t]*([A-Za-z_][\w']*)?([^\n:]*)", re.M)
OLD = re.compile(r"(?:store_thm|save_thm|Q\.store_thm)\s*\(\s*\"([\w']+)\"")
for p, *_ in tsvrows:
    t = strip_comments(io.open(os.path.join(cakeml, p), encoding="utf-8", errors="replace").read())
    thy = os.path.basename(p)[: -len("Script.sml")]
    thms, defs, local = set(), set(), set()
    nblocks = collections.Counter()
    for m in KW.finditer(t):
        k, n, attrs = m.group(1), m.group(2), m.group(3)
        nblocks[k] += 1
        if k in ("Theorem", "Triviality"):
            (local if (k == "Triviality" or "local" in attrs) else thms).add(n)
        elif k == "Definition" and n:
            defs.add(n)
        elif k in ("Inductive", "CoInductive") and n:
            defs.add(n)
    thms |= {m.group(1) for m in OLD.finditer(t)}
    decl[thy] = (thms, defs, local, nblocks)

recs, stat = [], collections.defaultdict(collections.Counter)
bad = []
seen = set()
for r in rows:
    if r["kind"] == "error":
        continue
    thy, k = r["thy"], r["kind"]
    if k in ("theorem", "definition", "axiom"):
        rec = Rec(r)
        try:
            for t in r["hyps"] + [r["concl"]]:
                ty, b = typeof_struct(rec, t)
                assert ty == b, "statement is not of type bool"
        except AssertionError as e:
            bad.append((thy, r["name"], str(e)))
        thms, defs, local, _ = decl[thy]
        n = r["name"]
        origin = "script" if (n in thms or n in defs or (n.endswith("_def") and n[:-4] in defs)) else "generated"
        key = (thy, r["name"])
        assert key not in seen, key
        seen.add(key)
        stat[thy][k + ":" + origin] += 1
        recs.append({"thy": thy, "name": r["name"], "kind": k, "origin": origin, "private": r["private"], "line": r["line"], "type_vars": sorted(rec.tv),
                     "constants": sorted(rec.consts), "hyps": r["hyps"], "concl": r["concl"], "tys": r["tys"], "pretty": r["pretty"]})
    elif k == "constant":
        rec = Rec(r)
        rec.tyi(r["ty"])
        for i in range(len(rec.tys)):
            rec.tyi(i)
        stat[thy]["constant"] += 1
        recs.append({"thy": thy, "name": r["name"], "kind": k, "type_vars": sorted(rec.tv), "ty": r["ty"], "tys": r["tys"]})
    else:
        stat[thy]["type"] += 1
        recs.append({"thy": thy, "name": r["name"], "kind": k, "arity": r["arity"]})

os.makedirs(out, exist_ok=True)
sp = os.path.join(out, "statements.jsonl")
with io.open(sp, "w", encoding="utf-8", newline="\n") as f:
    for x in recs:
        f.write(json.dumps(x, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n")

# ---- counts vs theories.tsv ----
hdr = ["theory", "tsv_theorems", "tsv_definitions", "script_theorems", "script_local", "script_definition_blocks",
       "export_theorems_script", "export_definitions_script", "export_generated", "constants", "types", "unexplained_missing"]
lines = ["\t".join(hdr)]
tot = collections.Counter()
for p, ln, th, df in tsvrows:
    thy = os.path.basename(p)[: -len("Script.sml")]
    s = stat[thy]
    thms, defs, local, nb = decl[thy]
    exported = {x["name"] for x in recs if x["thy"] == thy and x["kind"] in ("theorem", "definition", "axiom")}
    miss = sorted([n for n in thms if n not in exported] + [n for n in defs if n not in exported and n + "_def" not in exported and n + "_rules" not in exported])
    row = [thy, th, df, len(thms), len(local), nb["Definition"] + nb["Inductive"] + nb["CoInductive"] + nb["Datatype"],
           s["theorem:script"], s["definition:script"], s["theorem:generated"] + s["definition:generated"] + s["axiom:generated"],
           s["constant"], s["type"], ",".join(miss) or "-"]
    lines.append("\t".join(str(x) for x in row))
    for i in range(1, 11):
        tot[hdr[i]] += int(row[i])
lines.append("\t".join(["TOTAL"] + [str(tot[h]) for h in hdr[1:11]] + [""]))
io.open(os.path.join(out, "export_counts.tsv"), "w", encoding="utf-8", newline="\n").write("\n".join(lines) + "\n")
print("\n".join(lines))
sha = hashlib.sha256(open(sp, "rb").read()).hexdigest()
print("records", len(recs), "sml errors", len(errs), "ill-typed", len(bad), "size", os.path.getsize(sp), "sha256", sha)
for e in errs[:20]:
    print("ERROR", e)
for b in bad[:20]:
    print("ILLTYPED", b)
sys.exit(1 if errs or bad else 0)
