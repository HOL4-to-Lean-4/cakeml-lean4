# cakeml-lean4

Migration of CakeML's HOL4 development to Lean 4: definitions and theorem statements are
translated from HOL4, checked, and then proved in Lean. HOL4 proofs are not translated.

The work proceeds by milestone theorems. Each milestone's dependency closure is translated
bottom-up in dependency order, and modules already done by an earlier milestone are reused.

1. Semantics and type soundness (the closure of the first study).
2. Candle `proves_sound` (done as a case study in
   [candle-hol4-lean4-study](https://github.com/HOL4-to-Lean-4/candle-hol4-lean4-study)).
3. `small_big_decs_equiv`, parser `completeness`, `infer_prog_sound`.
4. Larger milestones towards the compiler's top-level correctness theorem.

Workflow (decisions of 27 November 2026, `plan/DECISIONS.md`): Claude Sonnet 5.5 and Claude Opus 5.5
each translate the whole development once (definitions, then statements); GPT-6.2 Astra validates and
is a second prover; Gemini Neon reviews findings; HOL4 runs ground every disputed claim. The
migration runs on a local machine, except Astra, which runs through the cloud gateway. Aristotle is
not used.

## Layout

| Directory | Contents |
|---|---|
| `vendor/` | Pinned CakeML, HOL4 and Poly/ML commits, and the Docker recipe for HOL4 |
| `manifest/` | Freeze pins, theories in scope, dependency order, batch plan |
| `lean/` | One Lake project, one module per HOL4 theory, mirroring CakeML's directory tree |
| `workflow/` | Briefs and scripts for translation, validation, review and HOL4 grounding |
| `runs/<batch>/` | Transcripts, findings and reports per batch |
| `ledger/costs.csv` | Tokens, money and time for every model call |
| `plan/` | The study plan, in LaTeX |

## License

BSD 3-Clause (see `LICENSE`). The Lean code here is translated from CakeML's HOL4 sources,
which are BSD 3-Clause licensed by the CakeML developers; vendored upstream code in `vendor/`
keeps its own license files.
