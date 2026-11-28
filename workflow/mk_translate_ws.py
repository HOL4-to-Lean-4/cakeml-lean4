#!/usr/bin/env python3
"""Create the two isolated TRANSLATOR workspaces (Sonnet 5.5 and Opus 5.5) of a milestone, and later the stage-2 copies.

usage:
  mk_translate_ws.py stage1 [--work-root WORK_ROOT] [--milestone milestone1] [--which sonnet opus] [--force]
  mk_translate_ws.py stage2 NAME [--parts 4]      # NAME = sonnet|opus; after stage 1 finished: copies ws1 to ws2A.. with assignments
  mk_translate_ws.py merge NAME                   # stage-2 parts -> <WORK_ROOT>/translate_NAME/merged/lean (+ NAMES.tsv rows)

WORK_ROOT defaults to ~/work/cakeml_m1 ($WORK_ROOT). Layout:
  WORK_ROOT/translate_<name>/ws1/     the only folder the model reads and writes
       hol4/cakeml/            the full HOL4 scripts of the milestone (with proofs: translators see them) + helper .sml
       hol4/HOL4-src/          HOL4 library sources (*.sml, *.sig of src/), hol4/HOL4-examples/ example theories in the closure
       hol4/export/            saved statements per theory as HOL4 prints them (no proofs), NAMES_TEMPLATE.tsv
       TARGETS.tsv, MODULES.tsv, BRIEF.md, lean/ (Lake skeleton with built Batteries, one stub module per theory)
  WORK_ROOT/translate_<name>/settings.json   permissions for `claude -p` (copied in approach from Phase 1 mk_ws.py)
Each model has its own folder; the settings deny the other workspaces, the upstream trees, this repository, the Phase 1
study, ~/.claude and ~/.codex. No model is run here; run_translate.sh starts one."""
import argparse, csv, glob, io, json, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hol4proof, modules

REPO = os.path.dirname(HERE)
MODELS = {"sonnet": "claude-sonnet-5-5", "opus": "claude-opus-5-5"}
EXAMPLE_DIRS = ["examples/pl-semantics/lprefix_lub", "examples/formal-languages/context-free", "examples/machine-code/hoare-triple"]


def work_root(a):
    return os.path.abspath(os.path.expanduser(getattr(a, "work_root", None) or os.environ.get("WORK_ROOT", "~/work/cakeml_m1"))).rstrip("/")


def abs_deny(p):
    return "//" + os.path.abspath(p).lstrip("/") + "/**"


def settings(deny_dirs):
    deny = [f"{t}({abs_deny(d)})" for d in deny_dirs for t in ("Read", "Edit")]
    deny += ["Read(~/.claude/**)", "Read(~/.codex/**)", "Read(~/.config/**)", "Read(~/.ssh/**)", "WebFetch", "WebSearch", "Task", "Agent",
             "Bash(git:*)", "Bash(curl:*)", "Bash(wget:*)", "Bash(gh:*)", "Bash(ssh:*)"]
    allow = ["Read(./**)", "Edit(./**)", "Write(./**)", "Read(~/.elan/toolchains/leanprover--lean4---v4.28.0/**)", "Glob", "Grep",
             "Bash(lake build:*)", "Bash(lake env lean:*)", "Bash(cd lean)", "Bash(cd lean && lake build:*)", "Bash(cd lean && lake env lean:*)", "Bash(cd lean; lake build:*)", "Bash(date -u:*)", "Bash(ls:*)"]
    return {"permissions": {"allow": allow, "deny": deny}}


def declarations(cakeml, tsv_rows):
    """TARGETS rows: kind, theory, name, script, line, attrs (from the script text, comments removed, line numbers kept)."""
    KW = re.compile(r"^(Theorem|Triviality|Definition|Inductive|CoInductive|Datatype)\b[ \t]*([A-Za-z_][\w']*)?([^\n:]*)", re.M)
    OLD = re.compile(r"(?:store_thm|save_thm|Q\.store_thm)\s*\(\s*\"([\w']+)\"")
    rows = []
    for p in tsv_rows:
        t = hol4proof.strip_comments(io.open(os.path.join(cakeml, p), encoding="utf-8", errors="replace").read())
        thy = os.path.basename(p)[: -len("Script.sml")]
        for m in KW.finditer(t):
            k, n, at = m.group(1), m.group(2) or "-", m.group(3).strip()
            kind = {"Theorem": "theorem", "Triviality": "theorem", "Definition": "definition", "Inductive": "inductive",
                    "CoInductive": "inductive", "Datatype": "datatype"}[k]
            if k == "Triviality" and "local" not in at:
                at = (at + " local").strip()
            rows.append((kind, thy, n, os.path.basename(p), t.count("\n", 0, m.start()) + 1, at or "-", p))
        for m in OLD.finditer(t):
            rows.append(("theorem", thy, m.group(1), os.path.basename(p), t.count("\n", 0, m.start()) + 1, "old-style", p))
    return rows


def copy_hol4(a, ws, scripts, milestone):
    cakeml, holdir = a.cakeml, a.holdir
    for p in scripts:
        dst = os.path.join(ws, "hol4", "cakeml", p)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy(os.path.join(cakeml, p), dst)
    for d in sorted({os.path.dirname(p) for p in scripts}):                 # helper libraries next to the scripts
        for f in glob.glob(os.path.join(cakeml, d, "*.sml")) + glob.glob(os.path.join(cakeml, d, "*.sig")):
            b = os.path.basename(f)
            if not b.endswith(("Script.sml", "Theory.sml", "Theory.sig")) and "heap" not in b:
                shutil.copy(f, os.path.join(ws, "hol4", "cakeml", d, b))
    ign = shutil.ignore_patterns(".hol", ".git", "*Theory.sml", "*Theory.sig", "*.dat", "*.uo", "*.ui", "*.o", "*.so", "*.a", "*.olean", "*.ML.bak")

    def keep_src(src, names):
        return [n for n in names if os.path.isfile(os.path.join(src, n)) and not n.endswith((".sml", ".sig"))] + list(ign(src, names))
    shutil.copytree(os.path.join(holdir, "src"), os.path.join(ws, "hol4", "HOL4-src"), ignore=keep_src)
    for d in EXAMPLE_DIRS:
        shutil.copytree(os.path.join(holdir, d), os.path.join(ws, "hol4", "HOL4-examples", os.path.basename(d)), ignore=keep_src)
    # drop empty directories
    for dp, dn, fn in os.walk(os.path.join(ws, "hol4", "HOL4-src"), topdown=False):
        if not os.listdir(dp):
            os.rmdir(dp)


def fill(t, d):
    for k, v in d.items():
        t = t.replace("{{" + k + "}}", str(v))
    assert "{{" not in t, re.findall(r"\{\{\w+\}\}", t)
    return t


def stage1(a):
    ms = a.milestone
    wr = work_root(a)
    tsv = os.path.join(REPO, "manifest", ms, "theories.tsv")
    scripts = [r[0] for r in list(csv.reader(io.open(tsv, encoding="utf-8"), delimiter="\t"))[1:]]
    stm = os.path.join(REPO, "manifest", ms, "statements.jsonl")
    if not os.path.exists(stm):
        sys.exit("run workflow/export/run_export.sh first (statements.jsonl missing)")
    pk = os.path.join(REPO, "lean", ".lake", "packages")
    if not os.path.isdir(pk):
        sys.exit("build the skeleton first: cd lean && lake build")
    decls = declarations(a.cakeml, scripts)
    nthm = sum(1 for d in decls if d[0] == "theorem")
    nloc = sum(1 for d in decls if d[0] == "theorem" and "local" in d[5])
    ndef = sum(1 for d in decls if d[0] != "theorem")
    for name in a.which:
        root = os.path.join(wr, "translate_" + name)
        ws = os.path.join(root, "ws1")
        if os.path.exists(ws):
            if not a.force:
                sys.exit("exists: " + ws + " (--force)")
            shutil.rmtree(ws)
        os.makedirs(ws)
        copy_hol4(a, ws, scripts, ms)
        ex = os.path.join(ws, "hol4", "export")
        os.makedirs(ex)
        for thy, text in hol4proof.render_statements(stm).items():
            io.open(os.path.join(ex, thy + ".txt"), "w", encoding="utf-8", newline="\n").write(text)
        shutil.copy(tsv, os.path.join(ex, "theories.tsv"))
        with io.open(os.path.join(ex, "NAMES_TEMPLATE.tsv"), "w", encoding="utf-8", newline="\n") as f:
            f.write("hol4\tlean\tkind\n")
            for l in io.open(stm, encoding="utf-8"):
                r = json.loads(l)
                k = {"constant": "const", "type": "type"}.get(r["kind"]) or ("thm" if r["kind"] == "theorem" and r.get("origin") == "script" else None)
                if k:
                    f.write(f"{r['thy']}${r['name']}\t{r['thy']}.{r['name']}\t{k}\n")
        with io.open(os.path.join(ws, "TARGETS.tsv"), "w", encoding="utf-8", newline="\n") as f:
            f.write("kind\ttheory\tname\tscript\tline\tattributes\n")
            for d in decls:
                f.write("\t".join(str(x) for x in d[:6]) + "\n")
        with io.open(os.path.join(ws, "MODULES.tsv"), "w", encoding="utf-8", newline="\n") as f:
            f.write("script\tmodule\tfile\n")
            for p in scripts:
                f.write(f"{p}\t{modules.module_of(p)}\tlean/{modules.file_of(p)}\n")
        subprocess.check_call([sys.executable, os.path.join(HERE, "mk_lean_skeleton.py"), os.path.join(ws, "lean")], stdout=subprocess.DEVNULL)
        os.makedirs(os.path.join(ws, "lean", ".lake"))
        shutil.copytree(pk, os.path.join(ws, "lean", ".lake", "packages"), ignore=shutil.ignore_patterns(".git", "docs"), symlinks=False)
        brief = fill(io.open(os.path.join(HERE, "briefs", "translate_stage1.md"), encoding="utf-8").read(),
                     dict(MILESTONE=ms.replace("milestone", ""), NSCRIPTS=len(scripts), NTHEOREMS=nthm, NLOCAL=nloc, NDEFS=ndef))
        io.open(os.path.join(ws, "BRIEF.md"), "w", encoding="utf-8", newline="\n").write(brief)
        others = [os.path.join(wr, "translate_" + o) for o in MODELS if o != name]
        deny = [a.cakeml, a.holdir, REPO, os.path.dirname(REPO), "/mnt", os.path.expanduser("~/astra_ws"), os.path.expanduser("~/upstream")] + others + \
            [os.path.join(wr, d) for d in os.listdir(wr) if d.startswith("prove_")]
        json.dump(settings(deny), io.open(os.path.join(root, "settings.json"), "w", encoding="utf-8"), indent=1)
        json.dump({"name": name, "model": MODELS[name], "milestone": ms, "created": __import__("datetime").datetime.now(__import__("datetime").timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")},
                  io.open(os.path.join(root, "meta.json"), "w", encoding="utf-8"))
        print(f"{ws}: {len(scripts)} scripts, {nthm} theorems ({nloc} local), {ndef} definition blocks, model {MODELS[name]}")


def stage2(a):
    wr = work_root(a)
    root = os.path.join(wr, "translate_" + a.name)
    ws1 = os.path.join(root, "ws1")
    base = list(csv.DictReader(io.open(os.path.join(ws1, "TARGETS.tsv"), encoding="utf-8"), delimiter="\t"))
    mods = {r["script"]: r for r in csv.DictReader(io.open(os.path.join(ws1, "MODULES.tsv"), encoding="utf-8"), delimiter="\t")}
    byscript = {}
    for r in base:
        if r["kind"] == "theorem":
            byscript.setdefault(r["script"], []).append(r)
    scripts_full = {os.path.basename(p): p for p in mods}
    groups = [[] for _ in range(a.parts)]
    load = [0] * a.parts
    for s, rs in sorted(byscript.items(), key=lambda x: -len(x[1])):
        i = load.index(min(load))
        groups[i].append(s)
        load[i] += len(rs)
    brief = fill(io.open(os.path.join(HERE, "briefs", "translate_stage2.md"), encoding="utf-8").read(),
                 dict(MILESTONE="1", NSCRIPTS=len(mods), NTHEOREMS=sum(len(v) for v in byscript.values()), NPARTS=a.parts))
    io.open(os.path.join(root, "stage2_brief.md"), "w", encoding="utf-8", newline="\n").write(brief)
    for i, g in enumerate(groups):
        L = "ABCDEFGH"[i]
        w = os.path.join(root, "ws2" + L)
        assert not os.path.exists(w), w
        shutil.copytree(ws1, w, ignore=shutil.ignore_patterns("PROGRESS.tsv", "scratch", "BRIEF.md"))
        io.open(os.path.join(w, "BRIEF.md"), "w", encoding="utf-8", newline="\n").write(brief)
        with io.open(os.path.join(w, "ASSIGNMENT.tsv"), "w", encoding="utf-8", newline="\n") as f:
            f.write("theory\tname\tscript\tline\tlean_file\n")
            for s in sorted(g, key=lambda s: list(scripts_full).index(s)):
                for r in byscript[s]:
                    f.write(f"{r['theory']}\t{r['name']}\t{s}\t{r['line']}\t{mods[scripts_full[s]]['file']}\n")
        print(w, sum(len(byscript[s]) for s in g), "theorems,", len(g), "modules")


def merge(a):
    root = os.path.join(work_root(a), "translate_" + a.name)
    m = os.path.join(root, "merged")
    assert not os.path.exists(m), m
    shutil.copytree(os.path.join(root, "ws1", "lean"), m + "/lean", ignore=shutil.ignore_patterns("scratch"))
    names = {}
    order = []
    np_ = os.path.join(m, "lean", "NAMES.tsv")
    if not os.path.exists(np_):
        np_ = os.path.join(root, "ws1", "hol4", "export", "NAMES_TEMPLATE.tsv")
        print("warning: stage 1 wrote no lean/NAMES.tsv; starting from the template")
    for l in io.open(np_, encoding="utf-8").read().split("\n")[1:]:
        if l.strip():
            k = l.split("\t")[0]
            names[k] = l
            order.append(k)
    for L in "ABCDEFGH":
        w = os.path.join(root, "ws2" + L)
        if not os.path.isdir(w):
            continue
        asg = list(csv.DictReader(io.open(os.path.join(w, "ASSIGNMENT.tsv"), encoding="utf-8"), delimiter="\t"))
        for f in sorted({r["lean_file"] for r in asg}):
            shutil.copy(os.path.join(w, f), os.path.join(m, f))
            print(L, f)
        mine = {f"{r['theory']}${r['name']}" for r in asg}
        wn = os.path.join(w, "lean", "NAMES.tsv")
        for l in (io.open(wn, encoding="utf-8").read().split("\n")[1:] if os.path.exists(wn) else []):
            if l.strip():
                k = l.split("\t")[0]
                if k in mine or k not in names:
                    if k not in names:
                        order.append(k)
                    names[k] = l
    io.open(os.path.join(m, "lean", "NAMES.tsv"), "w", encoding="utf-8", newline="\n").write("hol4\tlean\tkind\n" + "\n".join(names[k] for k in order) + "\n")
    print("merged into", m + "/lean")


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    for n in ("stage1", "stage2", "merge"):
        p = sp.add_parser(n)
        p.add_argument("--work-root")
        p.add_argument("--cakeml", default=os.environ.get("CAKEMLDIR", "/root/upstream/cakeml"))
        p.add_argument("--holdir", default=os.environ.get("HOLDIR", "/root/upstream/HOL"))
        if n == "stage1":
            p.add_argument("--milestone", default="milestone1")
            p.add_argument("--which", nargs="+", default=list(MODELS), choices=list(MODELS))
            p.add_argument("--force", action="store_true")
        else:
            p.add_argument("name", choices=list(MODELS))
        if n == "stage2":
            p.add_argument("--parts", type=int, default=4)
    a = ap.parse_args()
    {"stage1": stage1, "stage2": stage2, "merge": merge}[a.cmd](a)


if __name__ == "__main__":
    main()
