#!/usr/bin/env python3
"""Build a PROVER workspace from a translation, then run the blocking preflight.

usage: mk_prove_ws.py --translation DIR [--out PROVE_ROOT] [--statements statements.jsonl] [--name NAME]
  DIR  a translation: either a directory that holds `lean/` (a translator workspace) or the `lean/` directory itself.
  PROVE_ROOT (default $WORK_ROOT/prove_<name>) gets:
     ws/            the only folder the prover can read  (BRIEF.md, lean/, hol4_statements/)
     settings.json  permissions for `claude -p` (copied in approach from Phase 1: allow ./** and the Lean toolchain,
                    deny the study, upstream sources, other workspaces, ~/.claude, web, git, subagents)
     strip_report.tsv  what was removed (file, line, reason; never the removed text)
Allowed inputs ONLY: the Lean sources of the translation (lakefile.lean, lake-manifest.json, lean-toolchain, CakeML.lean,
CakeML/**/*.lean, CONVENTIONS.md), Batteries from this repository's lean/.lake/packages, and HOL4 statements printed
without proofs (from statements.jsonl). Everything else is not copied: PROGRESS.tsv, notes, reports, scratch files,
.lake of the translation, HOL4 scripts, upstream trees, earlier proofs.
HOL4 proof text found in Lean comments or Markdown is removed line by line (and Proof..QED / Termination..End blocks
inside comments), then preflight_prover.py must pass; if it does not, this script exits non-zero and no run may start
(run_prover.sh checks again)."""
import argparse, io, json, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hol4proof

REPO = os.path.dirname(HERE)
MARK = "[HOL4 proof text removed]"
KEEP_ROOT = ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "CakeML.lean", "CONVENTIONS.md"]
_WR = os.environ.get("WORK_ROOT", os.path.expanduser("~/work/cakeml_m1")).rstrip("/")


def strip_blocks(lines, is_comment_line):
    """Drop `Proof .. QED` and `Termination .. End` blocks inside comment text. lines: list of str. Returns set of 0-based indices."""
    kill, i = set(), 0
    while i < len(lines):
        if is_comment_line(i) and re.match(r"\s*(Proof\s*(\[[^\]]*\])?|Termination)\s*$", lines[i]):
            j = i
            while j < len(lines) and is_comment_line(j) and not re.match(r"\s*(QED|End)\b", lines[j]):
                j += 1
            if j < len(lines) and is_comment_line(j) and j - i < 400:
                kill |= set(range(i, j + 1))
                i = j
        i += 1
    return kill


def strip_lean(text, ix):
    """Return (new_text, [(line, reason)])."""
    lines = text.split("\n")
    code, com = hol4proof.lean_split(text)
    codelines = code.split("\n")
    comlines = {ln for ln, _ in com}
    is_c = lambda i: (i + 1) in comlines
    kill = {i: "BLOCK" for i in strip_blocks(lines, is_c)}
    for ln, reason, _ in hol4proof.check_text_lines(com, ix):
        kill.setdefault(ln - 1, reason)
    removed = []
    for i, reason in sorted(kill.items()):
        if i >= len(lines):
            continue
        cpart = codelines[i].strip() if i < len(codelines) else ""
        if not cpart:
            ind = re.match(r"\s*", lines[i]).group(0)
            lines[i] = ind + MARK
            removed.append((i + 1, reason))
        elif "--" in lines[i] and not lines[i].lstrip().startswith("/-"):
            k = lines[i].index("--")
            lines[i] = lines[i][:k].rstrip() + "  -- " + MARK
            removed.append((i + 1, reason))
    return "\n".join(lines), removed


def strip_md(text, ix):
    lines = text.split("\n")
    kill = {i: "BLOCK" for i in strip_blocks(lines, lambda i: True)}
    for ln, reason, _ in hol4proof.check_text_lines(list(enumerate(lines, 1)), ix):
        kill.setdefault(ln - 1, reason)
    removed = []
    for i, r in sorted(kill.items()):
        lines[i] = MARK
        removed.append((i + 1, r))
    return "\n".join(lines), removed


def abs_deny(p):
    return "//" + os.path.abspath(p).lstrip("/") + "/**"


def settings(ws_name_root, extra_deny):
    home = os.path.expanduser("~")
    deny = [f"{t}({abs_deny(d)})" for d in extra_deny for t in ("Read", "Edit")]
    deny += ["Read(~/.claude/**)", "Read(~/.codex/**)", "Read(~/.config/**)", "Read(~/.ssh/**)", "Read(~/.aws/**)", "WebFetch", "WebSearch", "Task", "Agent",
             "Bash(git:*)", "Bash(curl:*)", "Bash(wget:*)", "Bash(gh:*)", "Bash(ssh:*)", "Bash(python:*)", "Bash(python3:*)"]
    allow = ["Read(./**)", "Edit(./**)", "Write(./**)", "Read(~/.elan/toolchains/leanprover--lean4---v4.28.0/**)", "Glob", "Grep",
             "Bash(lake build:*)", "Bash(lake env lean:*)", "Bash(cd lean)", "Bash(date -u:*)", "Bash(ls:*)"]
    return {"permissions": {"allow": allow, "deny": deny}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--translation", required=True)
    ap.add_argument("--out")
    ap.add_argument("--name", default=None)
    ap.add_argument("--statements", default=os.path.join(REPO, "manifest", "milestone1", "statements.jsonl"))
    ap.add_argument("--cakeml", default=os.environ.get("CAKEMLDIR", "/root/upstream/cakeml"))
    ap.add_argument("--holdir", default=os.environ.get("HOLDIR", "/root/upstream/HOL"))
    ap.add_argument("--packages", default=os.path.join(REPO, "lean", ".lake", "packages"), help="built Batteries to copy (never taken from the translation)")
    ap.add_argument("--manifest", action="append")
    ap.add_argument("--force", action="store_true")
    a = ap.parse_args()
    tr = os.path.abspath(a.translation)
    src = tr if os.path.basename(tr) == "lean" else os.path.join(tr, "lean")
    name = a.name or os.path.basename(os.path.dirname(src))
    out = os.path.abspath(a.out or os.path.join(_WR, "prove_" + name))
    if os.path.exists(out):
        if not a.force:
            sys.exit("exists: " + out + " (use --force to rebuild)")
        shutil.rmtree(out)
    for need in ("lakefile.lean", "CakeML.lean"):
        if not os.path.exists(os.path.join(src, need)):
            sys.exit(f"not a translation (missing {need}): {src}")
    if not os.path.isdir(a.packages):
        sys.exit("no built Batteries at " + a.packages + " (run `lake build` in the repository's lean/ first)")
    tsvs = a.manifest or sorted(os.path.join(REPO, "manifest", d, "theories.tsv") for d in os.listdir(os.path.join(REPO, "manifest"))
                                if os.path.exists(os.path.join(REPO, "manifest", d, "theories.tsv")))
    ix = hol4proof.build_index(a.cakeml, tsvs, a.holdir if os.path.isdir(a.holdir) else None)
    ws = os.path.join(out, "ws")
    L = os.path.join(ws, "lean")
    os.makedirs(L)
    report = []
    # 1. Lean sources: allowlist copy
    files = [f for f in KEEP_ROOT if os.path.exists(os.path.join(src, f))]
    for dp, dn, fn in os.walk(os.path.join(src, "CakeML")):
        dn[:] = [d for d in dn if d not in (".lake", "scratch")]
        for f in fn:
            if f.endswith(".lean"):
                files.append(os.path.relpath(os.path.join(dp, f), src))
    for rel in sorted(files):
        t = io.open(os.path.join(src, rel), encoding="utf-8").read()
        for _ in range(3):
            t2, rm = (strip_md if rel.endswith(".md") else strip_lean)(t, ix) if rel.endswith((".md", ".lean")) else (t, [])
            report += [(rel, ln, r) for ln, r in rm]
            if t2 == t:
                break
            t = t2
        d = os.path.dirname(os.path.join(L, rel))
        os.makedirs(d, exist_ok=True)
        io.open(os.path.join(L, rel), "w", encoding="utf-8", newline="\n").write(t)
    # 2. Batteries from the repository (never from the translation)
    shutil.copytree(a.packages, os.path.join(L, ".lake", "packages"), ignore=shutil.ignore_patterns(".git", "docs", "*.md.bak"), symlinks=False)
    # 3. HOL4 statements without proofs
    sd = os.path.join(ws, "hol4_statements")
    os.makedirs(sd)
    for thy, text in hol4proof.render_statements(a.statements).items():
        io.open(os.path.join(sd, thy + ".txt"), "w", encoding="utf-8", newline="\n").write(text)
    # 4. brief
    shutil.copy(os.path.join(HERE, "briefs", "prove.md"), os.path.join(ws, "BRIEF.md"))
    # 5. settings (outside the workspace), report (no removed text)
    deny = [os.path.expanduser("~/work"), "/root/upstream", REPO, os.path.dirname(REPO) + "/candle-hol4-lean4-study", _WR]
    # the workspace itself is below WORK_ROOT: deny every sibling instead of the root
    sib = [os.path.join(_WR, d) for d in (os.listdir(_WR) if os.path.isdir(_WR) else []) if os.path.join(_WR, d) != out]
    deny = [d for d in deny if d != _WR and d != os.path.expanduser("~/work")] + sib + [os.path.join(_WR, "translate_sonnet"), os.path.join(_WR, "translate_opus")]
    json.dump(settings(out, deny), io.open(os.path.join(out, "settings.json"), "w", encoding="utf-8"), indent=1)
    with io.open(os.path.join(out, "strip_report.tsv"), "w", encoding="utf-8", newline="\n") as f:
        f.write("file\tline\treason\n")
        for rel, ln, r in report:
            f.write(f"{rel}\t{ln}\t{r}\n")
    print(f"workspace {ws}: {len(files)} Lean/Markdown files, {len(report)} HOL4-proof lines removed (strip_report.tsv)")
    # 6. blocking preflight
    cmd = [sys.executable, os.path.join(HERE, "preflight_prover.py"), ws, "--cakeml", a.cakeml, "--holdir", a.holdir, "--statements", a.statements]
    for t in tsvs:
        cmd += ["--manifest", t]
    rc = subprocess.call(cmd)
    if rc != 0:
        open(os.path.join(out, "PREFLIGHT_FAILED"), "w").write("preflight_prover.py failed; do not run the prover on this workspace\n")
        print("PREFLIGHT FAILED: the workspace must not be used", file=sys.stderr)
    sys.exit(rc)


if __name__ == "__main__":
    main()
