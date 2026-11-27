<!-- ======================================================================================================
Changes versus the Phase 1 brief (candle-hol4-lean4-study/baselines/ts_runs_v2/run/briefs/lessons_stage1.md):
 1. Scope: the 25 full CakeML scripts of milestone 1 (closure of semantics/proofs/typeSoundScript.sml; 1,208 theorems,
    617 definitions as counted in theories.tsv from the script text, DECISIONS item 13; the scripts really declare
    {{NTHEOREMS}} theorems and {{NDEFS}} definition blocks outside comment blocks), not a 20-script reduction with a
    267-theorem target list. Nothing is left out.
 2. Translators see the full HOL4 scripts including proofs (as in Phase 1), but must not copy proof text anywhere
    (new rule 8): the prover workspace is built from the translation and a blocking preflight rejects HOL4 proof text.
 3. One Lean module per HOL4 theory, mirroring CakeML's directory tree under `lean/CakeML/` (module map in `MODULES.tsv`);
    package `cakeml`, root `CakeML.lean`. Phase 1 used one flat package `cml_ts`.
 4. Mechanical naming: every HOL4 item `thy$name` lives in `namespace thy` as `thy.name`; deviations and every library
    constant are recorded in `lean/NAMES.tsv` (machine-read by workflow/scans/scan.py). New in Phase 2.
 5. Reuse rules for later milestones (section "Reuse"): stable names, library constants in `CakeML/Prelude/`, never
    redefine something an earlier module has.
 6. Contract wording (preservation V-P and conservativity V-C, judged against saved theorems) is stated in the brief; in
    Phase 1 it was only in the audit brief. `hol4/export/` holds HOL4's stored statements as reference.
 7. `decreasing_by sorry`, `partial`, `opaque` without a HOL4 counterpart and any `sorry` in a definition are scan failures
    that block reuse (DECISIONS item 12c), not just a `problem` note.
 8. Model and run: Sonnet 5.5 and Opus 5.5 each translate once in their own workspace (DECISIONS items 1 and 4); the
    translator does not know about the other.
====================================================================================================== -->
# Translation task, stage 1 of 2: definitions (CakeML migration, milestone {{MILESTONE}})

You are a translator. Your job is to translate the HOL4 development of the CakeML semantics and type soundness
(`semantics/proofs/typeSoundScript.sml` and its closure, {{NSCRIPTS}} theory scripts) into Lean 4. The Lean files
you write are the base of a migration of all of CakeML: later milestones will import them, so they must be
faithful, complete and stable.

The translation has two stages. **This stage (yours): every datatype, type abbreviation, definition, inductive
relation, overload and HOL4 library constant that the theorem statements need.** Stage 2 (a later run) adds the
{{NTHEOREMS}} theorem statements of the scripts, each with proof `sorry`, on top of your files. Stage 2 will not change
your definitions, so they must be complete, faithful and named so that every theorem statement can be written.
Proofs are not translated: a separate prover proves the statements later, without access to HOL4 proofs.

## The contract (what faithful means)
- **V-P (preservation):** some fact HOL4 proves about the mapped constants becomes false or unprovable in Lean, or a
  Lean statement is weaker, stronger, a special case, vacuous or trivially true when the HOL4 one is not.
- **V-C (conservativity):** Lean proves an equation written only with mapped constants that HOL4 does not prove.
  Tier 1: no choice term in the equation (the image of `ARB` may appear). Tier 2: the equation needs a Hilbert-choice
  term. Only facts provable from the theorems that HOL4 theories save count: `hol4/export/` lists every saved theorem
  and definition of the {{NSCRIPTS}} theories as HOL4 stores it. Check there whether HOL4 itself proves a value before you
  decide that a corner case is unspecified (underspecified functions such as `HD []` must stay unspecified in Lean, not
  get a value).
- Comments and names are not defects. Different but equivalent formulations are fine if recorded.
An audit will judge your translation against exactly this contract.

## Inputs (all inside your working directory)
- `hol4/cakeml/`: the {{NSCRIPTS}} HOL4 theory scripts (`*Script.sml`, in their CakeML directories) and the helper files
  next to them (`preamble.sml`). **They contain full proofs.** Read them for statements, definitions, `Datatype`,
  `Inductive`, `Overload`, `Termination` and `Theorem ...[local]`/`Triviality` declarations.
- `hol4/HOL4-src/`: the HOL4 system sources (`src/` at the pinned commit), to look up library constants (lists,
  `pred_set`, `finite_map`, `alist`, `cardinal`, `toto`, `comparison`, `string`, `words`, `sorting`, ...).
  `hol4/HOL4-examples/`: the HOL4 example theories in the closure (`lprefix_lub`, context-free `grammar`, `peg`,
  `pegexec`, `location`, and `hoare-triple`: `tailrec`, `set_sep`, `prog`, `address`).
- `hol4/export/<theory>.txt`: the saved theorems and definitions of each theory as HOL4 prints them (no proofs), with
  their type variables; `hol4/export/NAMES_TEMPLATE.tsv`: every constant, type and theorem of the theories (see 4).
- `TARGETS.tsv`: every declaration of the scripts, one per line (kind, theory, name, script, line, attributes). All of
  it is in scope: {{NTHEOREMS}} theorems (including {{NLOCAL}} `[local]`/`Triviality` ones, which stage 2 also states),
  {{NDEFS}} definition blocks. Also translate every HOL4 library constant, type abbreviation or overload that a
  statement or a translated definition mentions.
- `MODULES.tsv`: HOL4 script path -> Lean module -> Lean file.
- `lean/`: a Lean 4.28.0 Lake project, package `cakeml`, Batteries as its only dependency (already built). It has one
  stub module per HOL4 theory, mirroring CakeML's directory tree (for example
  `semantics/proofs/typeSoundScript.sml` -> `lean/CakeML/Semantics/Proofs/TypeSound.lean`, module
  `CakeML.Semantics.Proofs.TypeSound`), and the root `lean/CakeML.lean` importing them.

## What to produce
1. The Lean definitions, in the module of the HOL4 theory that defines them, in HOL4 source order where Lean allows.
   Lean imports between modules follow the HOL4 `Ancestors`. Everything in the module of theory `thy` goes in
   `namespace thy` (the HOL4 theory name exactly, for example `namespace semanticPrimitives`), so that HOL4 `thy$name`
   is `thy.name` unless NAMES.tsv says otherwise.
2. HOL4 library constants and HOL4 example theories go in new modules `lean/CakeML/Prelude/<Name>.lean` (imported where
   needed and added to `lean/CakeML.lean`, the only existing file besides the stubs you may edit outside your modules).
3. Above each translated declaration, a comment with the original HOL4 **statement or definition text**:
   `/- HOL4: <the HOL4 definition, as in the source> -/`. For library constants name the HOL4 theory and constant.
   Quote only definitions, datatypes and statements. Never quote proofs, tactics or `Termination` proofs (rule 8).
4. `lean/NAMES.tsv`, tab-separated with the header `hol4	lean	kind`: one row per HOL4 constant (kind `const`), type
   (`type`), datatype constructor (`ctor`) and theorem (`thm`) of `hol4/export/NAMES_TEMPLATE.tsv`; the `lean` column is
   pre-filled with the default `thy.name`; fix every row where your Lean name or Lean kind differs and write `-` for
   items you did not translate (with the reason in PROGRESS.tsv). Add rows (kind `lib`) for the HOL4 library constants
   you mapped, with their Lean name. Machine-read by `scan.py`; wrong rows show up there.
5. `lean/CONVENTIONS.md`: the rules stage 2 and the later milestones must follow: the name of every translated HOL4
   constant and type that is not identical (table HOL4 name -> Lean name), namespaces and `open`s, how HOL4 types map
   (num, int, char, string, mlstring, sets, finite maps, options, pairs, words, ...), notation, overloads, and anything a
   statement writer needs. Include the module each name lives in. No HOL4 proof text.
6. `lean/PROGRESS.tsv`, tab-separated: UTC time (`date -u +%FT%TZ`), theory, name, status (`done` / `problem`), short note.
   Append a line for each translated declaration (or group).
7. `lean/ALLOW_OPAQUE.txt` (only if needed): one Lean name per line for constants that HOL4 itself leaves unspecified and
   that you had to make `opaque`; say why in `CONVENTIONS.md`.

## Rules
1. Faithfulness first. Each Lean definition must mean exactly what the HOL4 definition means, on all inputs, including
   edge cases (division and modulus, subtraction on naturals, characters and strings, order and duplicates in lists,
   partial functions and `ARB`, Hilbert choice, sets that may be infinite, finite maps, `Datatype` quirks such as
   `num`-indexed or recursive-through-list types). Where Lean cannot express the HOL4 meaning directly, choose the
   closest faithful encoding and record the choice in `CONVENTIONS.md`.
2. Definitions must be accepted by Lean as total definitions: no `partial`, no `axiom`, no `unsafe`, no `implemented_by`,
   no `extern`, no `native_decide`. `noncomputable` and `Classical` choice are fine (HOL4 is classical). Termination
   proofs must be real proofs. `decreasing_by sorry`, any `sorry` in a definition, and `opaque` without a HOL4
   counterpart are scan failures that block reuse of the module by later milestones: restructure the definition
   (measure, fuel with the HOL4 clock, well-founded relation) before you give up, and if you must, list each such case in
   `PROGRESS.tsv` with status `problem` and the exact obstacle.
3. Do not write the theorem statements (stage 2). You may state and prove small lemmas only when Lean needs them for a
   definition (for example termination), in `namespace Aux`, and the equations HOL4 generates for a definition only if
   Lean's own equation lemmas would not exist.
4. Imports: Lean core (`Init`, `Std`, `Lean`) and Batteries only. Mathlib is not available. Do not change `lakefile.lean`,
   `lake-manifest.json` or `lean-toolchain`.
5. `lake build` from `lean/` must succeed at the end with no errors. Warnings are fine. Keep the build green after each
   module; work through the modules in the order of `theories.tsv` (`MODULES.tsv` lists it).
6. Clean room. Work only from the files inside your working directory and your own knowledge of Lean and HOL4. You may
   read the Lean core and Batteries sources under `lean/.lake/packages/` and the toolchain directory
   (`$HOME/.elan/toolchains/leanprover--lean4---v4.28.0/`). Do not read any other path on this machine. Do not use the
   web, web search, GitHub, git, MCP tools, browser tools, or tools that reach the user's computer. Do not look for
   existing Lean translations of CakeML anywhere.
7. Do not spawn subagents or delegate. You do all the translating yourself.
8. No HOL4 proof text in anything you write: not in Lean comments, not in `CONVENTIONS.md`, `PROGRESS.tsv` or any other
   file. The prover workspace is built from your files; a blocking check rejects any file that contains tactic scripts,
   `Proof ... QED` blocks or `Termination` proofs of the scripts, and the line-by-line removal tool loses your useful
   comments around them.

## Reuse (later milestones)
- Names are an API. Never rename or move a declaration once it is in `NAMES.tsv`; later milestones and the prover refer
  to it. Prefer HOL4's names exactly (including case and underscores).
- A later milestone that needs a HOL4 theory already translated imports its module and does not redefine its constants.
  Library constants you add under `CakeML/Prelude/` are shared by all milestones: look there first, and put new library
  material there, not in a theory module.
- A module is reusable only if it has no open finding on a definition, no confirmed V-P/V-C error, and passes
  `workflow/scans/scan.py` (DECISIONS item 12). Write definitions so that this is likely: no hidden choice, no `sorry`.
- Use the same Lean type for the same HOL4 type everywhere and record it in `CONVENTIONS.md` once.

## Environment
Your tools are Read, Write, Edit, Glob, Grep and Bash. Bash runs only `lake build ...`, `lake env lean ...`, `cd lean`,
`ls` and `date -u ...`; everything else is refused. Use Glob and Grep to search, and Read to read. Never chain commands
with pipes or redirections.
- From `lean/`: `lake build CakeML.Misc.Misc` builds one module, `lake build` builds all.
- Quick checks: a scratch file `lean/scratch/T.lean` that imports built modules, checked with `lake env lean scratch/T.lean`.
  Use `#eval`/`#reduce`/`example` to test definitions on small inputs where that helps you check faithfulness.
- The machine is shared with other runs: one Lean process at a time, and use command timeouts.

## Final report
When you stop, reply with a summary only: modules written and declaration counts per module; every place where the Lean
meaning differs from HOL4 or where you made a modelling choice (sets, finite maps, chars/strings, div/mod, choice, `ARB`,
termination); every `sorry` in a definition and every `problem` line; any declaration you could not translate and why; the
final `lake build` result; and a confirmation that you followed the clean-room rules and rule 8 (say so plainly if you
broke any).
