# Decisions for the whole migration

Decisions of the author for the CakeML migration in this repository. Phase 1 decisions are in
`candle-hol4-lean4-study/plan/v3`.

## 27 November 2026

The author's words: "whole migration: translate once with Sonnet and once with Opus; drop Aristotle; Astra moves to the cloud gateway".

1. **Two translations.** Claude Sonnet 5.5 and Claude Opus 5.5 each translate the whole migration once
   (definitions, then statements). Each translation is one run, with no repeat.
2. **Aristotle dropped.** Harmonic's Aristotle is not used (it has dropped Lean support). The ledger no longer has Aristotle columns.
3. **Astra in the cloud.** GPT-6.2 Astra runs through the SSS cloud gateway, not on the local machine.
   Its settings are in the cloud environment "Default" only (see `candle-hol4-lean4-study/CLOUD.md`);
   the smoke test is still to do. Credentials stay out of this repository.

## 27 November 2026, second set

4. **Proving: the Opus translation only.** The Sonnet translation is not proved. A proof shows that a
   statement can be proved, not that it is faithful, so a second proof adds little.
5. **Audit: Astra audits both translations.** This gives the Opus against Sonnet comparison.
6. **Review: Neon reviews a small sample of Astra's findings only**, not all of them. In the audit on real
   errors of the first study it accepted 173 of 174 findings. The sample size is still to be fixed.
7. **Astra is not a prover.** The "second prover" role, already dropped in the first study, is removed.

8. **Timing: Astra and Neon come in after each milestone**, not once at the end of the migration
   (author: "we do it").

Order per milestone batch: Astra audits a translation once that translation's batch is done (Opus and
Sonnet each, independently, so neither waits for the other). Neon then reviews the sample of Astra's
findings, accepted findings are repaired, and the repaired Opus translation is proved, without HOL4 proofs.
Cost (core, 21,860 theorems, `token_estimate_2026-11-27.md`): both translations and Opus proving about
7.7 B tokens and $4,100 at API prices; Astra about 310 M tokens.

## 27 November 2026, third set (after Astra's readiness review of the migration)

Astra's review: `candle-hol4-lean4-study/plan/v3/readiness_astra_migration_2026-11-27.md`.

9. **Pin.** The migration pins the current upstream CakeML `master` on freeze day (author).
10. **Who settles findings.** Findings that are disputed, or that Neon does not sample, are settled by a
    HOL4 check script (the grounding step); the author decides ties (author).
11. **What blocks reuse of a module** by later milestones (author). Until resolved, these block:
    (a) any open finding on a definition or datatype; (b) a preservation error (V-P) on a theorem that a
    later milestone imports; (c) structural scan failures (`sorry` outside the targets, new `axiom`,
    `native_decide`, `decreasing_by sorry`, `partial` or `opaque` without a HOL4 counterpart).
    Recorded as known issues, not blocking: V-C errors on statements no later module uses, tier-2 choice
    cases and `unsure` items on such statements, naming and style. An item moves to the blocking list
    once a later milestone imports it.

## 27 November 2026, fourth set (after Astra's and Neon's review of item 11)

Reviews: `candle-hol4-lean4-study/plan/v3/reuse_rule_astra_2026-11-27.md` and `reuse_rule_neon_2026-11-27.md`.

12. **Item 11 is replaced by a tighter rule** (author). Until resolved, these block reuse and release of a
    module: (a) any confirmed V-P or V-C error on any theorem or definition in the manifest; (b) any open
    finding on a definition, datatype or inductive; (c) failures of the scripts: statement and type mismatches
    against the HOL4 export, vacuous statements, definitions without bodies, `sorry` outside the targets (and
    any `sorry` after proving), new or unapproved transitive axioms, `native_decide`, `decreasing_by sorry`,
    `partial` or `opaque` without a HOL4 counterpart. Known issues, not blocking: tier-2 choice cases and
    `unsure` items on statements no later module imports, and naming and style. A known issue blocks once a
    later module imports it. At most three repair rounds; blockers left at the cap stop the release and are
    never demoted. Every repair or dismissal needs a checked Lean or HOL4 witness or the author's tie-break.
    Every audit finding is logged before repair under the full Phase 1 contract, per translation; the
    findings left after repair go in a second table. The README claims "no known violations in the audited
    scope" and links a public known-issues register.
13. **Milestone 1 scope: full scripts** (author). All 25 scripts of the `typeSound` closure are translated
    as upstream has them (1,208 theorems, 617 definitions; `manifest/milestone1/`), with no reduction.
14. **Neon's sample** (author, "continue" to the proposal of 27 November): Neon reviews every finding on a
    definition, datatype or inductive, plus 20% of the other findings, drawn evenly from the Sonnet and Opus
    translations and across error classes (fixed seed). Settles open decision 6 above and plan v3.4, "Open", item 6.
15. **Pilot before milestone 1** (author): `namespace` and `namespaceProps` (manifest/pilot) go through every
    step once with both translators, to test the launch scripts, the ledger and the isolation.
