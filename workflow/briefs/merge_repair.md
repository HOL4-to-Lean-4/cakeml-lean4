# Merge repair after stage 2 (CakeML migration)

This folder holds a Lean 4 translation of HOL4 theories of CakeML (`lean/`). Stage 2 wrote the theorem statements in
several parts that ran independently; their files were put together here. Some parts added the same helper or library
declaration (for example a HOL4 library constant) in different modules, so the project may not build.

Your only task: make `lake build` (run from `lean/`) succeed by resolving clashes between parts.
- Where two modules declare the same name, keep one declaration (in the module that the other imports, or in a
  `CakeML/Prelude/` module that both import) and delete the other. If the two copies differ, keep the one that matches the
  HOL4 definition better and record the choice.
- Do not change any theorem statement, and do not change any definition beyond moving or deleting a duplicate.
  Proofs stay `sorry`. Do not add `sorry` to any definition.
- Update `lean/NAMES.tsv` rows of moved declarations.
- `hol4/` (if present) is read-only reference.
- Write `MERGE_REPAIR.md`: every declaration you moved or deleted, from where to where, and why.

Finish with a short report: what clashed, what you changed, and the result of the final `lake build`.
