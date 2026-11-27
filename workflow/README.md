# workflow

Scripts and briefs for the migration, adapted from `candle-hol4-lean4-study` (Phase 1). Nothing here calls a model on its own:
`run_translate.sh` and `run_prover.sh` start a `claude -p` run and are the only places that do.
Defaults: `WORK_ROOT=~/work/cakeml_m1`, `CAKEMLDIR=/root/upstream/cakeml`, `HOLDIR=/root/upstream/HOL`, Lean 4.28.0 through elan
(`~/.elan/bin` on `PATH`). Python 3, standard library only.

## Rules the tooling enforces (DECISIONS 1-13)
- Translators (Sonnet 5.5 and Opus 5.5, one separate run each) see the full HOL4 scripts including proofs.
- Provers never see HOL4 proofs: the prover workspace is built from an allowlist (Lean sources of the translation, Batteries from this
  repository, HOL4 statements printed without proofs), no source trees, no earlier proofs, and `preflight_prover.py` **fails with a
  non-zero exit** if any file holds HOL4 proof text. `run_prover.sh` runs it again before it starts the model.
- Every model run has its own folder and `settings.json` (read/write only its workspace and the Lean toolchain; no web, git, subagents;
  `--setting-sources ""`); `--dangerously-skip-permissions` is never used. Approach copied from Phase 1 `mk_ws.py` / `setup.py`.
  The `settings.json` files were generated but not exercised against a live `claude` (no model run in the preparation).

## Scripts
| Path | What it does |
|---|---|
| `export/run_export.sh` | HOL4 export of every stored theorem, definition and axiom, plus the constants and type operators, of the theories in `manifest/milestone1/theories.tsv`, from the **built** upstream theories (`.dat` files; proofs were checked when they were built, no `--fast`). Writes `manifest/milestone1/statements.jsonl` and `export_counts.tsv`. About 20 s. |
| `export/export_theories.sml` | The exporter (adapted from Phase 1 `export_statements.sml`): raw kernel terms with every type explicit, types interned per record, plus HOL4's own print of the statement. Reads `DB.thy`, so also `private` theorems that are stored; `[local]` theorems are not stored in the theory and cannot be exported. |
| `export/postprocess.py` | Checks every statement (type `bool`, every application well typed; exit 1 otherwise), computes type variables and constants, marks `origin` = `script` (named in the script) or `generated` (by `Datatype`/`Inductive`/`Definition`), compares with `theories.tsv`. |
| `hol4proof.py` | Shared detection of HOL4 proof text: REGION (a line of a `Proof..QED`/`Termination..End`/old-style proof of the scripts), WINDOW (60 characters of proof text, whitespace removed, so re-flowed text is found), VOC (HOL4 tactic vocabulary), Lean-aware comment/string splitter. |
| `preflight_prover.py WS` | Blocking check of a prover workspace (exit 1 on findings, 2 if the HOL4 scripts cannot be read). Looks at every text file, also under `.lake`; forbids HOL4 scripts and theory files, `hol4/`, `cakeml/`, `.git`, symlinks, and files outside the prover layout. |
| `mk_prove_ws.py --translation DIR` | Builds `prove_<name>/{ws,settings.json,strip_report.tsv}` from a translation, strips HOL4 proof text from Lean comments and Markdown (line by line and `Proof..QED`/`Termination..End` blocks), then runs the preflight; non-zero exit and a `PREFLIGHT_FAILED` marker if it does not pass. `strip_report.tsv` has file, line and reason, never the removed text. `briefs/prove.md` becomes `BRIEF.md`. |
| `run_prover.sh PROVE_ROOT` | Opus 5.5 proving session (preflight first). |
| `mk_translate_ws.py stage1` | Creates `translate_sonnet/` and `translate_opus/` under `WORK_ROOT`: the 25 scripts with proofs, HOL4 library sources, HOL4 example theories, `hol4/export/` (stored statements, `NAMES_TEMPLATE.tsv`), `TARGETS.tsv`, `MODULES.tsv`, the stage-1 brief, a Lake skeleton with built Batteries. `stage2 NAME` makes the stage-2 copies with assignments (4 parts by module); `merge NAME` puts the parts together. |
| `run_translate.sh` | One translator run (model from `meta.json`). |
| `mk_lean_skeleton.py`, `modules.py` | The Lake project and the module map (script path -> `CakeML.<Dir>.<Name>`, mirrored under `lean/CakeML/`). One source of truth; later milestones add their `theories.tsv`. |
| `scans/scan.py` (+ `scans/Dump.lean`) | Structural scans (below). |
| `ledger.py` | Appends rows to `ledger/costs.csv` (existing header) from a `claude -p --output-format json` result (or stream-json) or a codex/gateway `meta.json`; idempotent by (workflow, run). |
| `briefs/translate_stage1.md`, `translate_stage2.md`, `prove.md` | The briefs. The two translation briefs start with a list of the changes against the Phase 1 `lessons_stage*` briefs. |
| `tests/test_preflight.sh`, `tests/test_scan.sh` | Tests (no model). `tests/*.out` hold the last outputs. |

### scans/scan.py
Exit 1 on: `sorry` in anything that is not a theorem (phase `translate`; in phase `proved` on any `sorry`), any `axiom` or dependence on a
non-standard axiom, `native_decide` / `decide +kernel` / `ofReduceBool`, `decreasing_by` with `sorry`, `partial` / `opaque` / `unsafe` /
`implemented_by` / `extern` (unless named in `--allow-opaque`), changed `lakefile.lean` / `lake-manifest.json` / `lean-toolchain`, failed `lake build`.
It also lists (non-blocking, `--require-all` makes them blocking), through `lean/NAMES.tsv`: missing theorems, constants and types, type-variable
count mismatches, and constants of a HOL4 statement that are missing from or extra in the Lean statement.
**Not ported:** the Phase 1 type-hash comparison of statements and `Frozen.lean` (post-proof frozen-statement check: needed when the Opus
proof run finishes; it needs the repaired translation as a base), and the transcript scan `scan2.py` (to adapt per run). The statement comparison is
by constant set and type-variable count, not by term: a real term-level comparison needs an HOL4-to-Lean term map that Phase 2 does not have.

## Per-milestone order
1. **Prepare** (once per milestone): `export/run_export.sh`; `cd lean && lake build`; `mk_translate_ws.py stage1`.
2. **Translate both**: `run_translate.sh` for `translate_sonnet` and `translate_opus` (stage 1); `mk_translate_ws.py stage2 NAME`, run the four
   parts, `merge NAME`; `ledger.py` for every run.
3. **Scans**: `scans/scan.py --lean <merged>/lean` for both translations (blocking findings go to the repair list).
4. **Audit**: Astra audits both translations, Neon reviews a sample of Astra's findings; disputed and unsampled findings are settled by a HOL4 check
   script (items 5, 6, 10).
5. **Fixes**: at most three repair rounds (item 12), each repair or dismissal with a checked witness; re-run the scans.
6. **Prove, Opus translation only**: `mk_prove_ws.py --translation <repaired opus>`, `run_prover.sh`; then `scan.py --phase proved`.
7. **Record and push**: `ledger.py`, runs under `runs/<batch>/`, known-issues register, commit and push.

## Known limits
- `[local]`/`Triviality` theorems (119 in these scripts) are not stored in the compiled theories, so `statements.jsonl` does not have them; they
  are in `TARGETS.tsv` (read from the script text) and are translated, but are not checked by `scan.py`.
- `theories.tsv` counts 1,208 theorems and 617 definitions from the script text, including declarations inside comment blocks
  (`export_counts.tsv` shows the difference: 1,131 theorems and 604 definition blocks outside comments).
- The proof-text detection is heuristic (exact lines, 60-character windows, vocabulary); the strong guarantee is the allowlist construction of the
  prover workspace. A Lean program run by the prover could read files outside its workspace if the permission settings were weaker than assumed:
  scan the transcripts as Phase 1 did.
