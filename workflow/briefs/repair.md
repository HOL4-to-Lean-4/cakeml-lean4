# Repair round {{ROUND}} of a HOL4-to-Lean 4 translation (CakeML migration)

`lean/` is a Lean 4 translation of HOL4 theories of CakeML (definitions, and theorem statements with proof `sorry`).
`hol4/` holds the HOL4 scripts (read-only reference) and `hol4/export/` the statements HOL4 saves.
An auditor reported the fidelity violations in `FINDINGS.json`, and they were accepted. Fix each of them.

Rules:
- The contract: V-P (preservation): the Lean declaration must have the meaning of the HOL4 one (a definition equal on every
  input; a statement neither weaker, stronger, a special case, vacuous nor trivially true when HOL4's is not; types as
  polymorphic as HOL4's). V-C (conservativity): Lean must not prove equations about mapped constants that HOL4's saved
  theorems leave open (for example the value of `HD []`).
- Make the smallest edit that fixes each finding. The proposed repair in a finding is a suggestion; check it against HOL4.
- Do not change anything a finding does not need. Theorem proofs stay `sorry`; no `sorry` in definitions; no `axiom`,
  `native_decide`, `partial` or new `opaque` (except a HOL4-unspecified value, which then goes in `lean/ALLOW_OPAQUE.txt`).
- If a fix changes a definition, adjust the statements that use it only as far as they must still typecheck, and keep their
  HOL4 meaning.
- If you find that a finding is wrong, do not change the code for it; say why, with the HOL4 and Lean lines.
- `cd lean && lake build` must succeed at the end. Keep `lean/NAMES.tsv` up to date.
- Write `REPAIRS.md`: for every finding id, what you changed (file, declaration) or why you did not.

Finish with a short report: fixed, not fixed (with reasons), and the final build result.
