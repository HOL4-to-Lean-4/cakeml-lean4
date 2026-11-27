# Fidelity audit of one module of a HOL4-to-Lean 4 translation

Part of the HOL4 development CakeML was translated to Lean 4.28.0 (core and Batteries, no Mathlib): definitions, datatypes, inductive relations, the HOL4 library
constants they use, and theorem statements whose proofs are `sorry`. It compiles. Names are HOL4's where possible (`lean/NAMES.tsv` maps HOL4 names to Lean names).

**Your scope is the single module `@MODULE@` (file `@FILE@`).** Find the places in it that violate fidelity to HOL4. The other modules are context; do not report on them.
The module may contain no violation, or any number. Report only what you believe is a violation; a wrong report counts against you just as a missed one does.

## Contract
- **V-P (preservation):** the Lean declaration does not have the meaning of the HOL4 one under the type mapping visible in the Lean library modules: a definition that differs on some input,
  or a statement that is weaker, stronger, a special case, false, vacuous or trivially true when the HOL4 one is not. A type more specific than HOL4's (lost polymorphism) is V-P.
- **V-C (conservativity):** Lean proves a specific equation, about a constant in the mapped vocabulary, that the theorems HOL4 saves about that constant leave open
  (for example the value of an underspecified function such as `HD []` outside its specification). The reference is the theorems HOL4 saves (`hol4/export/`), not unsaved kernel definitions.
- Not a violation: a different but equivalent formulation, a faithful choice of representation, extra auxiliary lemmas, missing proofs, style.

## Files (your working directory; everything is read-only, stay inside it)
- `lean/`: the translation (comments removed).
- `hol4/cakeml/`: the HOL4 theory scripts; `hol4/export/`: the statements HOL4 saves, per theory, as HOL4 prints them; `hol4/HOL4-src/`: HOL4 library sources.

You can only read files: do not run Lean or HOL4, use the network or start other agents.

## Method
Check every definition, datatype, inductive relation, opaque constant and theorem statement in the module against its HOL4 source and the saved statement.

## Output
Your final message is one JSON object and nothing else:

{"module": "@MODULE@", "checked": <number of declarations compared>, "findings": [
 {"id": "F1", "declaration": "<Lean name>", "kind": "definition" or "datatype" or "inductive" or "theorem", "lean": "<file:line>", "hol4": "<file:line>", "class": "V-P" or "V-C",
  "explanation": "<what differs, on which input, at most 120 words>", "repair": "<the Lean text you would put there>", "confidence": <0 to 1>,
  "lean_check": "<optional: a complete Lean file that imports modules of the project and compiles without `sorry` only if your claim is right; else null>",
  "hol4_check": "<optional: a HOL4 term that HOL4 can prove and that shows the HOL4 side of your claim; else null>"}]}

Use "findings": [] if you find no violation.
