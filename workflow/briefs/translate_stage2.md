<!-- ======================================================================================================
Changes versus the Phase 1 brief (candle-hol4-lean4-study/baselines/ts_runs_v2/run/briefs/lessons_stage2.md):
 1. Scope: all {{NTHEOREMS}} theorems of the 25 full scripts (including `[local]` and `Triviality` ones), split into
    {{NPARTS}} assignments by module; Phase 1 had 267 target theorems of a reduced development in 4 assignments.
 2. Module layout `lean/CakeML/<Dir>/<Name>.lean` (mirror of CakeML's tree) and `namespace <hol4 theory>`; names and kinds in
    `lean/NAMES.tsv` (rows kind `thm` must point at the Lean theorem you write; scan.py reads them).
 3. Contract wording (V-P preservation, V-C conservativity, saved theorems as reference) stated in the brief.
 4. No HOL4 proof text anywhere (rule 7); `sorry` is allowed only as the proof of a theorem.
 5. Reuse rules for later milestones (section "Reuse").
====================================================================================================== -->
# Translation task, stage 2 of 2: theorem statements (CakeML migration, milestone {{MILESTONE}})

You are a translator. Your job is to translate the theorem statements of the HOL4 CakeML development (the closure of
`semantics/proofs/typeSoundScript.sml`, {{NSCRIPTS}} scripts) into Lean 4. Stage 1 (already done by another run of the
same model) translated the datatypes, definitions, inductive relations and HOL4 library constants into the Lean project in
`lean/`, and wrote the naming and type conventions in `lean/CONVENTIONS.md` and the name table `lean/NAMES.tsv`.
**Your stage: add the Lean statements of the theorems assigned to you below, each with proof `sorry`.** Other runs do
the other assignments in parallel, in their own copies. Proofs are not translated: a separate prover proves the statements
later, without access to HOL4 proofs.

## The contract
- **V-P (preservation):** a Lean statement must not be weaker, stronger, more specific, vacuous or false when the HOL4 one is
  not; the types must be those of HOL4 (watch implicit type variables, numerals, `num` subtraction, overloads).
- **V-C (conservativity):** Lean must not prove equations about the mapped constants that HOL4 leaves open.
- `hol4/export/<theory>.txt` lists the saved statements of each theory as HOL4 stores them, with all types explicit where
  they matter and the type variables; use it to check the types of free variables and constants.
An audit will judge your statements against this contract.

## Your workspace: the current directory
- `hol4/cakeml/`: the HOL4 scripts (with proofs). `hol4/HOL4-src/`, `hol4/HOL4-examples/`: HOL4 sources for library constants.
  `hol4/export/`: saved statements as HOL4 prints them.
- `TARGETS.tsv`: all declarations (kind, theory, name, script, line, attributes).
- `ASSIGNMENT.tsv`: **your** theorems (theory, name, script, line, Lean file). Translate exactly these.
- `lean/`: the Lean 4.28.0 Lake project (Batteries only, already built), with stage 1's files, `CONVENTIONS.md` and `NAMES.tsv`.

## What to produce
1. For each assigned theorem, a Lean `theorem` in the Lean file named in `ASSIGNMENT.tsv`, in HOL4 source order, after the
   definitions it needs, inside `namespace <hol4 theory>`, with:
   - the same name as in HOL4 unless `CONVENTIONS.md` says otherwise or Lean rejects the name (then record the Lean name in
     `NAMES.tsv` and `PROGRESS.tsv`);
   - directly above it, the comment `/- HOL4: <the HOL4 statement, as in the source> -/` (statement only, see rule 7);
   - proof `:= by sorry` (or `:= sorry`).
   A HOL4 theorem that is a conjunction stays one Lean theorem with a conjunction. Keep HOL4's quantifier structure and
   hypotheses; do not strengthen, weaken, split or merge statements. `[local]` and `Triviality` theorems are translated like
   any other.
2. `lean/NAMES.tsv`: for each assigned theorem make sure the row `thy$name -> lean name, thm` exists and is right (edit the row; add it for `[local]` and `Triviality` theorems, which the template lacks).
3. `PROGRESS.tsv` in the workspace root, tab-separated: UTC time (`date -u +%FT%TZ`), theorem name, status (`done` /
   `problem`), short note. Append a line per theorem.

## Rules
1. Faithfulness first. Each Lean statement must mean exactly what the HOL4 statement means, with the same types (implicit HOL4
   type variables, numeral types, `num` subtraction, overloaded operators, sets and finite maps, and free variables, which
   HOL4 quantifies universally).
2. Do not change any existing declaration from stage 1 (definitions, datatypes, instances, `open`s, options, order). If a
   statement needs a HOL4 constant that stage 1 did not translate, add a faithful translation as a new definition in your
   assigned file, placed before its first use, with a `/- HOL4: ... -/` comment, a `NAMES.tsv` row, and a `PROGRESS.tsv` line
   with status `problem` and the note `added definition`. If you believe a stage 1 definition is wrong, do not edit it: log
   it with status `problem` and the precise reason.
3. `sorry` only as the proof of a theorem. No `axiom`, `partial`, `unsafe`, `implemented_by`, `extern`, `native_decide`,
   `opaque`, and no `sorry` inside a definition.
4. Edit only the Lean files named in your `ASSIGNMENT.tsv`, plus `lean/NAMES.tsv` rows for your theorems. Do not edit
   `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `CakeML.lean` or other files.
5. Imports: Lean core and Batteries only. Mathlib is not available. `lake build` must succeed at the end.
6. Clean room. Work only from files inside your workspace and your own knowledge of Lean and HOL4. You may read the Lean core and
   Batteries sources under `lean/.lake/packages/` and the toolchain directory. Do not read any other path on this machine. Do not
   use the web, web search, GitHub, git, MCP tools, browser tools, or tools that reach the user's computer. Do not look for
   existing Lean translations of CakeML anywhere. Do not spawn subagents or delegate.
7. No HOL4 proof text in anything you write (Lean comments, notes, `PROGRESS.tsv`): quote statements only. A blocking check
   rejects the prover workspace if it finds proof text, tactic scripts or `Proof ... QED` blocks of the scripts.

## Reuse (later milestones)
Names are an API: never rename an existing declaration; later milestones import these modules. A statement may use only
constants that stage 1 or earlier modules define; new library material goes to `CakeML/Prelude/` through a `problem` line,
not into a theory module. A module blocks reuse while it has an open finding on a definition, a confirmed V-P/V-C error, or
a scan failure (`sorry` outside theorem proofs, new axiom, `native_decide`, `decreasing_by sorry`, `partial`/`opaque`
without a HOL4 counterpart).

## Environment
Your tools are Read, Write, Edit, Glob, Grep and Bash. Bash runs only `lake build ...`, `lake env lean ...`, `cd lean`, `ls`
and `date -u ...`; everything else is refused. Use Glob and Grep to search, and Read to read. Never chain commands with pipes
or redirections.
- From `lean/`: `lake build CakeML.Misc.Misc` builds one module, `lake build` builds all.
- Quick checks: a scratch file `lean/scratch/T.lean` that imports built modules, checked with `lake env lean scratch/T.lean`.
- The machine is shared with other runs: one Lean process at a time, and use command timeouts.

## Final report
When you stop, reply with a summary only: theorems written out of the number assigned; any assigned theorem you could not
state and why; definitions you added; stage 1 definitions you believe are wrong (with reasons); every place where your
statement could differ in meaning from HOL4 and why; the final `lake build` result; and a confirmation that you followed the
clean-room rules and rule 7 (say so plainly if you broke any).
