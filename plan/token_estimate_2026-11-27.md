# Token estimate for the whole CakeML migration

Made on 27 November 2026 from `ledger/costs.csv` of `candle-hol4-lean4-study` (commit a4b5812) and a count of CakeML `master` at 080a3bd (25 November 2026).

## Basis

Tokens are input + output + cache read + cache write, as the CLIs report them. More than 90% are cache reads. USD is the API-equivalent price in the ledger; Astra and Neon ran on subscriptions and have no price.

Scaling is per HOL4 theorem (`Theorem` or `Triviality`). One migration pass per theorem is: Opus translates, Opus proves (without HOL4 proofs), Astra audits, Neon reviews. Baselines and ablations are not repeated.

| Milestone | Theorems | Opus translate | Opus prove | Sonnet translate |
|---|---|---|---|---|
| Candle | 278 | 36.6 M ($18.7) | 10.6 M ($10.9) | 22.2 M ($7.2) |
| Type soundness | 267 | 22.4 M ($25.4) | 34.0 M ($22.0) | 64.1 M ($17.5) |
| Per theorem (mean of the two) | | 108 k ($0.08) | 83 k ($0.06) | 160 k ($0.05) |

Astra audit on real errors: 13.8 M tokens for 63 units covering 7 translations (4 × 278 + 3 × 267 = 1,913 theorems), so 7 k per theorem audited. Neon: 52.8 M for 53 of the 63 units, so about 33 k per theorem.

Everything in the ledger so far (all arms, baselines, audits): 602 M tokens; Claude rows $418.

## CakeML size

| Part | Script lines | Theorems |
|---|---|---|
| compiler | 451,330 | 13,401 |
| examples | 191,485 | 5,836 |
| candle | 95,206 | 3,775 |
| pancake | 62,178 | 1,435 |
| semantics | 34,181 | 1,154 |
| basis | 31,035 | 1,258 |
| translator | 26,577 | 1,121 |
| characteristic | 13,766 | 507 |
| cv_translator, misc, tutorial | 12,180 | 720 |
| **All** | **917,972** | **29,207** |
| Without examples, pancake, tutorial | 662,168 | 21,860 |

## Estimate

| Model | Per theorem | Core (21,860) | All (29,207) |
|---|---|---|---|
| Opus 5.5 (translate + prove) | 191 k | 4.2 B tokens, about $3,100 | 5.6 B tokens, about $4,100 |
| Sonnet 5.5 instead of Opus for translation | 160 k | 3.5 B, about $1,000 (translation part) | 4.7 B, about $1,300 |
| GPT-6.2 Astra (audit) | 7 k | 160 M | 210 M |
| Gemini Neon (review) | 33 k | 720 M | 960 M |

A line-based scaling gives the same size: Opus used about 5 k tokens per package line (Candle 47 M for 8,766 lines, type soundness 56 M for 11,258 lines), so 3.4 B (core) to 4.8 B (all).

On the subscription: the type-soundness proving run ($22 API-equivalent, 34 M tokens) hit the usage limit once and was resumed. So one run of about $22 filled one to two usage windows; at that rate the core migration needs roughly 70 to 140 windows for Opus alone. The weekly limits of the plan are not published in tokens, so this count is rough.

## Limits of the estimate

- Two milestones only, both in the logic part of CakeML. Compiler proofs are longer (34 script lines per theorem against 25 for candle) and may cost more per theorem.
- One run per cell; no variance.
- Repair rounds, re-audits after fixes and failed proving attempts are not in the per-theorem rate, so the real total is likely higher.
- Astra and Neon counts include each CLI's fixed overhead per unit (suspected to be about 95 k input tokens per Codex call); fewer, larger units would lower them.

## With two translations (decision of 27 November)

Sonnet and Opus each translate the whole development once (`DECISIONS.md`). Translation alone:

| | Per theorem | Core (21,860) | All (29,207) |
|---|---|---|---|
| Opus 5.5 translation | 108 k ($0.08) | 2.4 B, about $1,800 | 3.2 B, about $2,400 |
| Sonnet 5.5 translation | 160 k ($0.05) | 3.5 B, about $1,000 | 4.7 B, about $1,300 |
| Both translations | 268 k ($0.13) | 5.9 B, about $2,800 | 7.8 B, about $3,700 |
| Opus proving, per translation proved | 83 k ($0.06) | 1.8 B, about $1,300 | 2.4 B, about $1,800 |
| Astra audit of both translations | 14 k | 310 M | 410 M |
| Neon review of both translations | 66 k | 1.4 B | 1.9 B |

So the core migration with both translations and one of them proved is about 7.7 B tokens and $4,100
of Claude use at API prices; with both proved, about 9.5 B and $5,400. Astra and Neon run on
subscriptions. Aristotle is dropped and adds nothing. The limits above still apply.