"""Shared detection of HOL4 proof text (used by preflight_prover.py and mk_prove_ws.py).

Adapted from candle-hol4-lean4-study/proving_nohol4/prooftext.py (REGION = a line that occurs in a proof
region of the HOL4 scripts; VOC = tactic vocabulary). Differences: (1) it is a library whose findings
are blocking, (2) it also finds HOL4 proof text that was re-flowed across lines (WINDOW: a run of
WINDOW_LEN characters, whitespace removed, taken from a proof region of the CakeML scripts), (3) it
looks at every text file, not only Lean comments, and at Lean code for WINDOW hits, (4) HOL4 library
scripts (HOLDIR) are checked by REGION lines only.
"""
import glob, io, os, re

WINDOW_LEN = 60
MIN_LINE = 12
N = lambda s: re.sub(r"\s+", "", s)


def regions(t):
    """Proof regions of a HOL4 script: `Proof .. QED`, `Termination .. End`, old-style prove/store_thm tails."""
    out = [m.group(1) for m in re.finditer(r"^(?:Proof\b|Termination\b)(.*?)^(?:QED|End)\b", t, re.S | re.M)]
    for m in re.finditer(r"(?:store_thm|Q\.prove|\bprove|tprove|save_thm)\s*\(.*?(?=^(?:Theorem|Definition|Triviality|val |Datatype|Inductive|End|QED|Overload))", t, re.S | re.M):
        s = m.group(0)
        k = max(s.rfind("`,"), s.rfind("”,"))
        out.append(s[k + 2:] if k > 0 else "")
    return out


class Index:
    def __init__(self):
        self.lines = set()      # normalised proof lines (>= MIN_LINE chars)
        self.windows = set()    # WINDOW_LEN-char windows of normalised proof regions (CakeML scripts only)
        self.nscripts = 0
        self.nregions = 0

    def add_script(self, path, windows=True):
        t = io.open(path, encoding="utf-8", errors="replace").read()
        self.nscripts += 1
        for r in regions(t):
            self.nregions += 1
            self.lines |= {N(l) for l in r.split("\n") if len(N(l)) >= MIN_LINE}
            if windows:
                n = N(r)
                self.windows |= {n[i:i + WINDOW_LEN] for i in range(0, max(0, len(n) - WINDOW_LEN + 1))}


# Vocabulary that only HOL4 proofs use (Lean has no `fs[`, `_tac`, `Cases_on`, ...). `simp[`/`rw[` alone are
# ambiguous with Lean and are only caught through REGION / WINDOW.
VOC = re.compile(
    r"(?:^|\s)>-|^\s*>>|\b\w+_tac\b|\b\w+_TAC\b|\bCases_on\b|\bInduct_on\b|\bqexists\w*|\bqspec\w*|\bqabbrev_tac\b"
    r"|\bmetis_tac\b|\bfirst_x_assum\b|\bfirst_assum\b|\bimp_res_tac\b|\bho_match_mp_tac\b|\bsrw_tac\b|\bMESON_TAC\b"
    r"|\b(?:gvs|gs|fs|rfs)\s*\[|^\s*QED\s*$|^\s*Proof\s*(?:\[[^\]]*\])?\s*$|^\s*Termination\s*$|\bWF_REL_TAC\b|\brpt\s+(?:strip|gen|disch)\w*"
    r"|\bsimp\s*\[[^\]]*\]\s*>>|\bfs\s*\[[^\]]*\]\s*>>")


def lean_split(t):
    """Split a Lean file into (code_text, comments) where code_text keeps line structure with comment and
    string-free positions blanked, and comments is a list of (line_number, line_text) for every line that has
    comment text (`--` line comments, nested `/- -/` block and doc comments)."""
    code, com = [], []
    i, depth, ln, cur, curln = 0, 0, 1, [], 1
    n = len(t)
    while i < n:
        two = t[i:i + 2]
        c = t[i]
        if depth == 0:
            if c == '"':
                j = i + 1
                while j < n and t[j] != '"':
                    j += 2 if t[j] == "\\" else 1
                seg = t[i:j + 1]
                code.append(seg)
                ln += seg.count("\n")
                i = j + 1
                continue
            if c == "'":
                m = re.match(r"'(?:\\.[^']*|[^\\'])'", t[i:i + 12])
                if m and not (i and (t[i - 1].isalnum() or t[i - 1] in "_'")):
                    code.append(m.group(0))
                    i += m.end()
                    continue
            if two == "--":
                j = t.find("\n", i)
                j = n if j < 0 else j
                com.append((ln, t[i + 2:j]))
                code.append(" " * (j - i))
                i = j
                continue
            if two == "/-":
                depth, curln, cur = 1, ln, []
                code.append("  ")
                i += 2
                continue
            code.append(c)
            if c == "\n":
                ln += 1
            i += 1
        else:
            if two == "/-":
                depth += 1
                cur.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
                if depth == 0:
                    com.extend((curln + k, s) for k, s in enumerate("".join(cur).split("\n")))
                    code.append(" ")
                else:
                    cur.append("  ")
            else:
                cur.append(c)
                if c == "\n":
                    code.append("\n")
                    ln += 1
                i += 1
    if depth:  # unterminated comment: treat the rest as comment
        com.extend((curln + k, s) for k, s in enumerate("".join(cur).split("\n")))
    return "".join(code), [x for x in com if x[1].strip()]


def _windows_hit(lines, index):
    """lines: list of (ln, text). Returns {ln: snippet} for lines overlapped by a WINDOW hit on the
    whitespace-free concatenation."""
    chars, lnof = [], []
    for ln, s in lines:
        for ch in s:
            if not ch.isspace():
                chars.append(ch)
                lnof.append(ln)
    t = "".join(chars)
    hit = {}
    W = WINDOW_LEN
    S = index.windows
    if not S or len(t) < W:
        return hit
    i = 0
    while i + W <= len(t):
        if t[i:i + W] in S:
            for k in range(i, i + W):
                hit.setdefault(lnof[k], t[i:i + W])
            i += W // 2
        else:
            i += 1
    return hit


def check_text_lines(lines, index, use_voc=True):
    """lines: list of (ln, text) of prose or comment text. Returns sorted [(ln, reason, snippet)]."""
    found = {}
    for ln, s in lines:
        x = N(s)
        if len(x) >= MIN_LINE and x in index.lines:
            found.setdefault(ln, ("REGION", s.strip()[:120]))
        elif use_voc and VOC.search(s):
            found.setdefault(ln, ("VOC", s.strip()[:120]))
    for ln, snip in _windows_hit(lines, index).items():
        found.setdefault(ln, ("WINDOW", snip))
    return sorted((ln, r, sn) for ln, (r, sn) in found.items())


def check_file(path, index):
    """Findings for one text file: [(line, reason, snippet)]. Binary files return []."""
    try:
        b = open(path, "rb").read()
    except OSError:
        return [(0, "UNREADABLE", path)]
    if b"\0" in b[:4096]:
        return []
    t = b.decode("utf-8", errors="replace")
    if path.endswith(".lean"):
        code, com = lean_split(t)
        out = check_text_lines(com, index)
        # code: only re-flowed/long HOL4 proof text (WINDOW) counts; Lean tactics look like HOL4 ones.
        code_lines = list(enumerate(code.split("\n"), 1))
        for ln, sn in _windows_hit(code_lines, index).items():
            out.append((ln, "WINDOW-IN-CODE", sn))
        return sorted(out)
    return check_text_lines(list(enumerate(t.split("\n"), 1)), index)


def build_index(cakeml_dir, theories_tsvs, hol_dir=None):
    ix = Index()
    seen = set()
    for tsv in theories_tsvs:
        for line in io.open(tsv, encoding="utf-8").read().split("\n")[1:]:
            p = line.split("\t")[0]
            if p and p not in seen:
                seen.add(p)
                ix.add_script(os.path.join(cakeml_dir, p))
    if hol_dir:
        dirs = [os.path.join(hol_dir, "src"), os.path.join(hol_dir, "examples", "pl-semantics", "lprefix_lub"),
                os.path.join(hol_dir, "examples", "formal-languages", "context-free"),
                os.path.join(hol_dir, "examples", "machine-code", "hoare-triple")]
        for d in dirs:
            for p in glob.glob(d + "/**/*Script.sml", recursive=True):
                ix.add_script(p, windows=False)
    return ix


def render_statements(jsonl_path):
    """{theory: text} of the `hol4_statements/<theory>.txt` files: HOL4's own printing of every stored
    statement (thm_to_string, which cannot contain a proof). Shared by mk_prove_ws.py (writes them) and
    preflight_prover.py (a file identical to its regeneration is exempt from the WINDOW scan: the printed
    statements legitimately share text with proofs that quote them)."""
    import json
    per = {}
    for l in io.open(jsonl_path, encoding="utf-8"):
        r = json.loads(l)
        if r["kind"] in ("theorem", "definition", "axiom"):
            per.setdefault(r["thy"], []).append(r)
    out = {}
    for thy, rs in per.items():
        o = [f"HOL4 theory {thy}: stored statements, as HOL4 prints them (no proofs). `type_vars` are the HOL4 type variables.\n\n"]
        for r in rs:
            o.append(f"=== {r['kind']} {thy}.{r['name']}   [type_vars: {' '.join(r['type_vars']) or '-'}]\n{r['pretty'].strip()}\n\n")
        out[thy] = "".join(o)
    return out


def strip_comments(t):
    """Remove (nested) SML comments, keeping string literals and line structure."""
    o, i, d = [], 0, 0
    while i < len(t):
        two = t[i:i + 2]
        if two == "(*":
            d += 1
            i += 2
        elif d and two == "*)":
            d -= 1
            i += 2
        elif d == 0 and t[i] == '"':
            j = i + 1
            while j < len(t) and t[j] != '"':
                j += 2 if t[j] == "\\" else 1
            o.append(t[i:j + 1])
            i = j + 1
        else:
            if d == 0 or t[i] == "\n":
                o.append(t[i])
            i += 1
    return "".join(o)
