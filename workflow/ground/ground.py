#!/usr/bin/env python3
"""HOL4 and Lean check of audit findings (DECISIONS item 10: the check script settles unsampled and disputed findings,
the author decides ties).

usage: ground.py WORK_ROOT OUT.json [--translations sonnet opus]
For every Astra finding (WORK_ROOT/audit/<t>/out/*.last):
  lean_check  -> written to <translation>/merged/lean/Ground/<id>.lean and run with `lake env lean` (120 s). It must compile,
                 contain no `sorry`/`admit`/`axiom`/`native_decide`, and then supports the finding's Lean side.
  hol4_check  -> proved in HOL4 (upstream pins, all milestone-1 theories loaded) with fixed tactics (EVAL, simp, metis; 60 s each).
                 PROVED supports the finding's HOL4 side. FAILED is not a refutation.
Status per finding: "supported" (every given check passed), "partly" (some passed), "unchecked" (no check given or none passed)."""
import glob, io, json, os, re, shutil, subprocess, sys, tempfile

W, OUT = sys.argv[1], sys.argv[2]
TS = sys.argv[sys.argv.index("--translations") + 1:] if "--translations" in sys.argv else ["sonnet", "opus"]
HOLDIR = os.environ.get("HOLDIR", "/root/upstream/HOL"); CAKEML = os.environ.get("CAKEMLDIR", "/root/upstream/cakeml")
POLY = os.environ.get("POLYML_DIR", "/home/user/candle-hol4-lean4-study/_build/polyml")
THYS = ["misc", "namespace", "mllist", "mlstring", "tokens", "ast", "ffi", "fpSem", "lexer_fun", "tokenUtils", "namespaceProps", "gram",
        "semanticPrimitives", "evaluate", "typeSystem", "primTypes", "typeSoundInvariants", "cmlPtreeConversion", "semantics",
        "semanticPrimitivesProps", "typeSysProps", "weakening", "primSemEnv", "evaluateProps", "typeSound"]
BAD = re.compile(r"\bsorry\b|\badmit\b|^\s*axiom\b|native_decide", re.M)


def findings(t):
    for p in sorted(glob.glob(os.path.join(W, "audit", t, "out", "*.last"))):
        j = json.loads(re.search(r"\{.*\}", io.open(p, encoding="utf-8").read(), re.S).group(0))
        for f in j.get("findings", []):
            yield dict(f, translation=t, module=j.get("module"), uid=f"{t}:{j.get('module')}:{f.get('id')}")


def lean_check(t, f):
    src = f["lean_check"]
    if BAD.search(src):
        return "rejected (uses sorry/admit/axiom/native_decide)"
    L = os.path.join(W, "translate_" + t, "merged", "lean"); d = os.path.join(L, "Ground"); os.makedirs(d, exist_ok=True)
    fn = os.path.join(d, re.sub(r"\W", "_", f["uid"]) + ".lean"); io.open(fn, "w", encoding="utf-8").write(src)
    try:
        r = subprocess.run(["lake", "env", "lean", fn], cwd=L, capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return "timeout"
    errs = [l for l in (r.stdout + r.stderr).split("\n") if "error" in l]
    return "compiles" if r.returncode == 0 and not errs else "fails: " + (errs[0][:200] if errs else f"rc={r.returncode}")


def hol4_batch(items):
    if not items:
        return {}
    q = lambda s: '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", " ") + '"'
    sml = ['val _ = List.app load ["' + '","'.join(t + "Theory" for t in THYS) + '"];', "open HolKernel boolLib bossLib;", "val _ = new_theory \"ground_scratch\";",
           "".join(f"open {t}Theory; " for t in THYS),
           'fun try_tac nm tm = let val t = Parse.Term [QUOTE tm] in (let val th = Tactical.TAC_PROOF (([], t), FIRST [CONV_TAC EVAL, simp[], (simp[] THEN metis_tac[])]) in print ("@@" ^ nm ^ "\\tPROVED\\n") end) handle e => print ("@@" ^ nm ^ "\\tFAILED\\t" ^ String.translate (fn #"\\n" => " " | c => str c) (exn_to_string e) ^ "\\n") end handle e => print ("@@" ^ nm ^ "\\tPARSE-ERROR\\t" ^ String.translate (fn #"\\n" => " " | c => str c) (exn_to_string e) ^ "\\n");']
    for uid, tm in items:
        sml.append(f"val _ = try_tac {q(uid)} {q(tm)};")
    d = tempfile.mkdtemp(); fn = os.path.join(d, "ground.sml"); io.open(fn, "w", encoding="utf-8").write("\n".join(sml) + "\n")
    env = dict(os.environ, HOLDIR=HOLDIR, CAKEMLDIR=CAKEML, PATH=f"{POLY}/bin:{HOLDIR}/bin:" + os.environ["PATH"], LD_LIBRARY_PATH=f"{POLY}/lib")
    r = subprocess.run(["hol", "run", fn], cwd=os.path.join(CAKEML, "semantics", "proofs"), env=env, capture_output=True, text=True, timeout=60 * 60)
    res = {}
    for l in (r.stdout + r.stderr).split("\n"):
        if l.startswith("@@"):
            p = l[2:].split("\t"); res[p[0]] = " ".join(p[1:])[:240]
    if not res:
        res["__error__"] = (r.stdout + r.stderr)[-1500:]
    return res


allf = [f for t in TS for f in findings(t)]
hol = hol4_batch([(f["uid"], f["hol4_check"]) for f in allf if f.get("hol4_check")])
out = []
for f in allf:
    r = {"uid": f["uid"], "translation": f["translation"], "module": f["module"], "declaration": f.get("declaration"), "class": f.get("class"), "kind": f.get("kind")}
    checks = []
    if f.get("lean_check"):
        r["lean"] = lean_check(f["translation"], f); checks.append(r["lean"] == "compiles")
    if f.get("hol4_check"):
        r["hol4"] = hol.get(f["uid"], "no result"); checks.append(r["hol4"].startswith("PROVED"))
    r["status"] = "supported" if checks and all(checks) else ("partly" if any(checks) else "unchecked")
    out.append(r)
json.dump({"hol4_errors": hol.get("__error__"), "findings": out}, io.open(OUT, "w", encoding="utf-8"), indent=1, ensure_ascii=False)
from collections import Counter
print(Counter((r["translation"], r["status"]) for r in out))
