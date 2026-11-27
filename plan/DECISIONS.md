# Decisions for the whole migration

Decisions of the author for the CakeML migration in this repository. Phase 1 decisions are in
`candle-hol4-lean4-study/plan/v3`.

## 27 November 2026

The author's words: "whole migration: translate once with Sonnet and once with Opus; drop Aristotle; Astra moves to the cloud gateway".

1. **Two translations.** Claude Sonnet 5.5 and Claude Opus 5.5 each translate the whole migration once
   (definitions, then statements). Each translation is one run, with no repeat.
2. **Aristotle dropped.** Harmonic's Aristotle is not used. The ledger no longer has Aristotle columns.
3. **Astra in the cloud.** GPT-6.2 Astra runs through the cloud gateway, not on the local machine.
   Nothing is set up yet: the gateway's endpoint and access are still to be recorded here when
   they exist, and credentials stay out of this repository.

Not decided yet: which translation, or both, is proved in Lean; whether Astra and Neon audit both
translations or one. The cost of each choice is in `token_estimate_2026-11-27.md`.