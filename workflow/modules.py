"""Single source of truth for the milestone-1 module list: HOL4 script path -> Lean module.

Rule (DECISIONS item 13 and README): one Lean module per HOL4 theory, mirroring CakeML's directory
tree under `lean/CakeML/`. Every path segment and the theory name are UpperCamelCased
(`semantics/proofs/typeSoundScript.sml` -> `CakeML.Semantics.Proofs.TypeSound`, file
`lean/CakeML/Semantics/Proofs/TypeSound.lean`; `lexer_fun` -> `LexerFun`; `basis/pure/mllist` ->
`CakeML.Basis.Pure.Mllist`). A later milestone adds its rows to its own theories.tsv and the same rule applies.
"""
import csv, io, os

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)


def camel(s):
    return "".join(p[:1].upper() + p[1:] for p in s.split("_") if p)


def module_of(script_path):
    d, f = os.path.split(script_path)
    assert f.endswith("Script.sml"), script_path
    segs = [camel(x) for x in d.split("/") if x] + [camel(f[: -len("Script.sml")])]
    return "CakeML." + ".".join(segs)


def file_of(script_path):
    return module_of(script_path).replace(".", "/") + ".lean"


def theories(milestone="milestone1"):
    p = os.path.join(REPO, "manifest", milestone, "theories.tsv")
    rows = list(csv.reader(io.open(p, encoding="utf-8"), delimiter="\t"))[1:]
    return [r[0] for r in rows]


def all_modules():
    out = []
    for m in sorted(d for d in os.listdir(os.path.join(REPO, "manifest")) if d.startswith("milestone")):
        for s in theories(m):
            if (s, m) not in [(x, y) for x, y, _ in out]:
                out.append((s, m, module_of(s)))
    return out


if __name__ == "__main__":
    for s, m, mod in all_modules():
        print(s, mod, sep="\t")
