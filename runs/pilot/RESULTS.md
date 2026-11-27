# Pilot, 27 November 2026 (DECISIONS item 15)

Scope: `semantics/namespaceScript.sml` and `semantics/proofs/namespacePropsScript.sml` (manifest/pilot; 120 theorems, 25 definition blocks),
pins of `manifest/milestone1/PINS.md`. Every step of the milestone ran once in a cloud session.

| Step | Sonnet 5.5 | Opus 5.5 |
|---|---|---|
| Stage 1 (definitions) | builds; 102 turns, 15 min, $3.45 | builds; 106 turns, 18 min, $5.47 |
| Stage 2 (120 statements, `sorry`) | 120 of 120, builds; $2.05 | 120 of 120, builds; $2.92 |
| Scans (`scan.py`) | 0 blocking | 0 blocking |
| Astra audit (gpt-6.2-astra, reported by the gateway), 2 units | 0 findings | 0 findings |
| Neon review | nothing to sample | nothing to sample |
| Prover preflight | | passed: 305 files, no HOL4 proof text, 0 lines stripped |
| Proving (Opus only) | | 120 of 120, no `sorry`, scan `--phase proved` 0 blocking; 25 min, $7.51 |

Cost: Claude $21.41 at API prices (Sonnet $5.50, Opus $15.90), 36.3 M tokens (over 90% cache reads); Astra 4 calls, 0.81 M tokens.
Rows in `ledger/costs.csv` (phase `pilot`).

Checks after proving: no theorem statement of the translation changed (all 120 compared after whitespace normalisation), every other
Lean file is byte-identical to the translation, and a scan of the prover's tool calls finds no path outside its workspace,
no HOL4 sources, no network or git use.

Problems found and fixed during the pilot: the type-variable scan counted relation arguments as type binders; names in guillemets
(`«namespace»`) did not match `NAMES.tsv`; the statement-constant comparison reported types and out-of-scope constants; `ledger.py`
skipped rows of a second arm with the same workflow; the model settings did not deny the other clones and the shared folder.

Not tested by the pilot: the Neon step (no findings), repair rounds, stage 2 with more than one part.
Transcripts: private raw repository, `cakeml-lean4/pilot-2026-11-27/`.
