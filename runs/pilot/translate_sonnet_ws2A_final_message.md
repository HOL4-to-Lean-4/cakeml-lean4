All 120 assigned theorems are now stated in Lean with proof `sorry`, in `lean/CakeML/Semantics/Proofs/NamespaceProps.lean`, in HOL4 source order. The final `lake build` of the whole project succeeded (35 jobs). Its only warnings are the expected "declaration uses `sorry`" ones.

**What changed**
- The theorems are inside `namespace namespaceProps`, after stage 1's `nsSub_compute_def`. Each has a `/- HOL4: … -/` comment above it, and the theorem names are unchanged.
- `lean/NAMES.tsv` gets one new row, `namespaceProps$lemma → namespaceProps.lemma`, because the `[local]` theorem `lemma` had none. The other 119 rows were already correct.
- `PROGRESS.tsv` has 120 `done` lines. Its timestamps are all one `date -u` reading taken just before writing the file, not 120 separate readings.
- I added no definitions.
- I found no stage 1 definition I believe is wrong.

**Where the Lean statement could differ from HOL4**
- **Type variables.** I matched every theorem's type-variable count against `hol4/export/namespaceProps.txt`. Two are easy to get wrong:
  - `nsOpen_some_from_same_mod_domain` has 5 type variables. `env2` has its own name and value types (`N2 V2`); only the module type is shared with `env1`.
  - `nsLookup_nsBind` has 6. Its two conjuncts are typed independently, so I used `{M1 N1 V1 M2 N2 V2}`.
- **Precedence in `nsLookupMod_FOLDR_nsLift_none`.** I read the right-hand side as `(prefix1 ∨ prefix2) ⇒ ∃p3 …`, with `⇔` binding weaker than `⇒`. The export's unparenthesised printing agrees with that reading.
- **Free variables.** Free HOL4 variables are Lean theorem arguments. In `nsLookupMod_nsAppend_some`, `x` stays outside the `∀e1 e2 path`.
- **Case expressions.** HOL4 `case` is a Lean `match` and `OPTION_MAP` is `Option.map`. Boolean equalities, as in `alistSub_cong`, are written as `↔`.
- **Local theorem name.** The theorem `lemma` is written `«lemma»` in Lean; its name is `namespaceProps.lemma`.
- **Elaborated types.** I printed the elaborated types of 11 theorems (the type-variable cases and the `match`, `IS_PREFIX`, `LIST_REL`, `insert` ones) and they read as intended. The other 109 I did not print.
- **Empty types.** I added no `Nonempty` hypotheses.

**Clean room and rule 7.** I read only files inside the workspace, and used no web, git, MCP or browser tools and no subagents. I read the HOL4 script, which includes proofs, but quoted only statements. My comments and `PROGRESS.tsv` contain no proof or tactic text. A final grep of the Lean file for tactic and proof markers found only stage 1's own two `rw` lines.

**Other notes**
- While checking, I temporarily added `set_option autoImplicit false` to rule out silently auto-bound variables. It compiled, and I removed the line afterwards.
- I left `lean/scratch/T.lean` behind, a scratch file of `#check` lines. I could not delete it.
- Two tool calls were denied. One was a compound `cd … && cat` command. The other was a write to `PROGRESS.tsv` while my working directory was `lean/`; it succeeded after I changed back to the workspace root.
