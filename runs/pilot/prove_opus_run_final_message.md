I proved all 120 `sorry` theorems in `lean/CakeML/Semantics/Proofs/NamespaceProps.lean`, which is the only file in the project that had any. The final `lake build` completes with no errors or warnings.

- **Proved:** 120 of 120. None of them relies on another `sorry` theorem; `uses_sorry` is "no" for every row.
- **Unproved:** none.
- **Refuted:** none. I did not create `Refuted.lean`.
- **Statements I suspect are wrong:** none. Before proving them I checked by hand that the trickier ones are true as stated, including the `nsAppend` lookup characterisations, `nsLookupMod_FOLDR_nsLift_none` and `nsDom_nsAppend_equal`.

**Checks:**
- A search of `lean/CakeML` finds no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `partial` or `opaque`.
- I printed the axioms of five of the larger proofs (`nsMap_I`, `nsMap_compose`, `nsDom_nsAppend_equal`, `nsLookupMod_FOLDR_nsLift_none`, `nsAll2_nsAppend`). They use only `propext` and `Quot.sound`. I added the `#print axioms` lines temporarily and removed them again.

**What I added to the file:**
- About 50 helper lemmas, all named `namespaceProps.Aux.*`. Most sit in one block after `nsSub_compute_def`; a few are placed just before the theorems that need them.
- Two `set_option linter.unusedSectionVars false` lines, to silence warnings. They change neither statements nor definitions, but they are the only lines outside proofs and `Aux` lemmas that I touched.
- No definitions, statements, names or imports were changed.

**Network access during the run:** the first `lake env lean` call printed "batteries: URL has changed", deleted `.lake/packages/batteries` and cloned it again from GitHub at revision 495c008c. That used the network, which the brief rules out. Lake did it on its own and I did not try to stop it. After that the project had to be rebuilt once with `lake build`, which succeeded. Whoever runs the comparison script may want to know the Batteries checkout was replaced.

`lean/PROGRESS.tsv` has one row per theorem, all marked `proved`.

RUN COMPLETE
