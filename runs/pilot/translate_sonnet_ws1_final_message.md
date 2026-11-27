Stage 1 is finished for both theories, and `lake build` from `lean/` succeeds (35 jobs). It reports no warnings, and no definition contains `sorry`, `partial`, `axiom` or `opaque`.

## Modules written
- **`CakeML/Prelude/`** has seven new library modules: `PredSet`, `Combin`, `Pair`, `BasicSize`, `HolList`, `HolOption` and `Alist`. They hold about 30 constants and small lemmas.
- **`CakeML/Semantics/Namespace.lean`** has the types `id` and `namespace` and the `alist` abbreviation. It has all 22 `namespaceScript` definitions. It also has the constants HOL4's datatype package generates: `id_CASE`, `id_size`, `idSET1`, `idSET2`, `idMAP`, `idREL`, `namespace_CASE`, `namespace_size`, `namespaceSET1/2/3`, `namespaceMAP` and `namespaceREL`. HOL4's stored equations are proved as theorems: `nsMap_def`, `nsLookup_def`, `nsLookupMod_def`, `nsAppend_def`, `namespaceSET{1,2,3}_thm`, `namespaceMAP_thm` and `namespace_size_def`. So is HOL4's induction principle `namespace_induction`.
- **`CakeML/Semantics/Proofs/NamespaceProps.lean`** has `alist_rel_restr`, `alistSub` and `nsSub_compute`, plus the equation `nsSub_compute_def`.
- **Other files:** `lean/NAMES.tsv` (174 rows), `CONVENTIONS.md`, `PROGRESS.tsv`, and the Prelude imports added to `CakeML.lean`. `ALLOW_OPAQUE.txt` isn't needed.

## Where Lean differs from HOL4 or I made a modelling choice
- **Not translated:** `id_CONS` and `namespace_CONS` are marked `-` in `NAMES.tsv`. They are internal to HOL4's type-definition package, and no theorem of the two scripts mentions them.
- **Names:** `namespace` is a Lean keyword, so the Lean namespace is `«namespace»`. The constructors are `namespace.id.Short`, `namespace.id.Long` and `namespace.namespace.Bind`, and they are exported. Bare `Bind` is ambiguous with Lean core's `Bind` class after `open «namespace»`, so write `«namespace».Bind`.
- **Types:** all type variables are `Type`. `bool` used as a predicate or relation result is `Prop`. Lean type variables may be empty where HOL4's are nonempty. `CONVENTIONS.md` says to add `Nonempty` hypotheses only where needed.
- **Datatype fields:** `Bind` is written with `List (N × V)` and `List (M × namespace M N V)`. Lean rejects the nested occurrence behind the `alist` abbreviation.
- **Classical equality:** `ALOOKUP`, `if` and `nsOpen` use classical equality. The files are `noncomputable`, and no definition asks for `DecidableEq`.
- **Nested recursion:** `nsMap`, `namespaceSET*`, `namespaceMAP` and `namespace_size` recurse through a list of pairs. They go through structural helpers (`Aux.*List`), and HOL4's equations are proved in HOL4's form.
- **`nsSub_compute`:** it uses well-founded recursion on `sizeOf` through a variant of `alist_rel_restr` (`Aux.alist_rel_restr_dep`). Its callback also receives the lookup fact. `nsSub_compute_def` proves HOL4's equation with the plain `alistSub`. I also checked four small examples, including the reversed-path argument and mismatches. They behave as HOL4 does.
- **Sets:** `nsDom` and `nsDomMod` keep HOL4's `GSPEC` form. `UNION`, `INSERT`, `IMAGE` and `BIGUNION` are defined by their membership predicate. HOL4 writes them with a set-builder, which means the same thing.
- **Core mappings:** `MAP`, `FOLDR`, `REVERSE`, `FST`, `SND`, `OPTION_MAP` and `o` map to Lean core (`List.map`, `List.foldr`, `List.reverse`, `Prod.fst`, `Prod.snd`, `Option.map`, `Function.comp`) with no new declaration. `I` gets its own `combin.I`, because Lean's `id` would clash with the type `namespace.id`.
- **`NAMES.tsv` rows:** the 120 stage-2 theorem rows keep the default name `namespaceProps.<name>` and don't exist in Lean yet. The one exception is `nsSub_compute_def`.

## Problems and deviations
- There is no `problem` line in `PROGRESS.tsv`.
- **Clean-room deviation:** my first `lake env lean` call made Lake delete the prebuilt `.lake/packages/batteries` ("URL has changed") and clone it again from GitHub at rev 495c008. I didn't ask for that and didn't touch the web otherwise. No module imports Batteries, so nothing depends on it. Please check whether you want that clone treated as a breach.
- **Scratch file:** `lean/scratch/T.lean` is still there. I blanked it, since I can't delete files.
- **Stale header comment:** the "25 scripts / 1,208 theorems" in the brief's header comment doesn't match `MODULES.tsv`. I followed `MODULES.tsv` (2 scripts, 120 theorems).

## Rule check
I worked only from the files in the working directory and my own knowledge. I used no web search, GitHub, git, MCP tools or subagents. I quoted no HOL4 proof text anywhere (rule 8). Where a termination argument exists, only the definition is quoted and the comment says the argument is omitted. The only Lean proofs are small lemmas needed for definitions or HOL4's stored equations (rule 3).
