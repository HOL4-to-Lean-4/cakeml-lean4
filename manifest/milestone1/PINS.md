# Milestone 1 pins (draft, 27 November 2026)

Decision 9: the migration pins the current upstream `master` on freeze day.

| Component | Commit | Date |
|---|---|---|
| CakeML | `080a3bdd0ff444663865436b59819714452f969d` | 2026-11-25 |
| HOL4 | `5da890e716bb47caff1dd1adb23f074a83dd9ec2` (master) | 2026-11-27 |
| Poly/ML | v5.9.2, as in `candle-hol4-lean4-study/vendor` | |
| Lean | 4.28.0 | |

CakeML 080a3bd does not build with the study's HOL4 pin `9783a499` (`misc/preamble.sml` uses
`HOLFlags`, added to HOL4 later), so Phase 2 pins HOL4 master as well.

Checked 27 November in a cloud session: `Holmake typeSoundTheory` in `semantics/proofs` builds the
closure without `--fast` (34 theories: 25 CakeML scripts plus 9 HOL4 example theories, about 15 minutes
on 4 cores).

## Closure of `typeSound` (milestone 1 target `semantics_type_sound`)

`theories.tsv` lists the 25 CakeML scripts in a valid build order, with line, theorem
(`Theorem`/`Triviality`) and definition (`Definition`/`Datatype`/`Inductive`/`CoInductive`) counts from
the script text: 26,347 lines, 1,208 theorems, 617 definitions. Phase 1 translated a kernel-level
reduction of this closure (267 theorems, parser removed). HOL4 example theories in the closure (not
translated, need a Lean counterpart or a decision): `lprefix_lub`, context-free `grammar`, `peg`,
`pegexec`, `location`, and `hoare-triple` `tailrec`, `set_sep`, `prog`, `address` (pulled in by the
`cakeml-heap` of `misc`).
