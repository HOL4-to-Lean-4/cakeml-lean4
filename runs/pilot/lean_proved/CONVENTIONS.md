# Conventions for the Lean translation of CakeML (pilot: `namespace`, `namespaceProps`)

These rules bind stage 2 (theorem statements) and every later milestone. Names in `NAMES.tsv`
are an API: never rename or move them.

## 1. Modules and namespaces

| HOL4 theory | Lean module (file) | Lean namespace | imports |
|---|---|---|---|
| `namespace` | `CakeML.Semantics.Namespace` (`CakeML/Semantics/Namespace.lean`) | `«namespace»` | Prelude.Alist, PredSet, List, Pair |
| `namespaceProps` | `CakeML.Semantics.Proofs.NamespaceProps` (`CakeML/Semantics/Proofs/NamespaceProps.lean`) | `namespaceProps` | Semantics.Ast (HOL4 ancestor; still a stub), Semantics.Namespace |
| HOL4 library | `CakeML.Prelude.PredSet`, `.List`, `.Pair`, `.Alist` (`CakeML/Prelude/*.lean`) | `pred_set`, `list`, `pair`, `basicSize`, `alist` | Batteries.Data.List.Basic (for `List.Forall₂`) |

- Every HOL4 item `thy$name` is `thy.name` in Lean, apart from the cases in section 2.
- **`namespace` is a Lean keyword.** The HOL4 theory `namespace` is the Lean namespace
  `«namespace»`, and the HOL4 type `namespace` is `«namespace».namespace`. Write `«namespace»` (with the
  French quotes) wherever the word stands alone: `open «namespace»`, `«namespace».nsLookup`, and the
  type `«namespace» m n v` (once `«namespace»` is open), or `«namespace».namespace m n v` in full.
- Statement files: put the stage-2 statements of theory `namespaceProps` in `namespace namespaceProps`
  in `NamespaceProps.lean` and `open «namespace»` there (the definitions file already does this).
- Helper lemmas that I needed for definitions are in `<thy>.Aux` (`«namespace».Aux`, `namespaceProps.Aux`).
  These are not HOL4 theorems, except where marked "HOL4 `..._thm`/`..._def`" (section 5).

## 2. Names that are not the default `thy.name`

| HOL4 | Lean | kind | module | note |
|---|---|---|---|---|
| `namespace$namespace` | `«namespace».namespace` | type | Semantics.Namespace | `inductive`; write `«namespace» m n v` after `open «namespace»` |
| `namespace$Bind` | `«namespace».namespace.Bind` | ctor | Semantics.Namespace | alias `«namespace».Bind` (by `export`) |
| `namespace$Short` | `«namespace».id.Short` | ctor | Semantics.Namespace | alias `«namespace».Short` |
| `namespace$Long` | `«namespace».id.Long` | ctor | Semantics.Namespace | alias `«namespace».Long` |
| type abbreviation `namespace$alist` (`('k,'v) alist = ('k # 'v) list`) | `«namespace».alist k v` | abbrev | Semantics.Namespace | `abbrev`, reducible to `List (k × v)`; the constructor `Bind` is written with `List (n × v)` directly |
| `namespace$nsLookup_def` | `«namespace».nsLookup.eq_def` (clauses `.eq_1`, `.eq_2`) | thm | | Lean's equation lemmas |
| `namespace$nsLookupMod_def` | `«namespace».nsLookupMod.eq_def` (`.eq_1`, `.eq_2`) | thm | | Lean's equation lemmas |
| `namespace$nsAppend_def` | `«namespace».nsAppend.eq_1` | thm | | Lean's equation lemma |
| `namespace$nsMap_def` | `«namespace».nsMap.eq_1` | thm | | Lean's equation lemma |
| `namespaceProps$nsSub_compute_def` | `namespaceProps.nsSub_compute_def` | thm | Semantics.Proofs.NamespaceProps | proved here (Lean's own equation has a guard, see 7) |
| `namespace$id_CONS`, `namespace$namespace_CONS` | not translated (`-`) | const | | HOL4 datatype-package representation constructors |

Other HOL4 datatype-package equations that are proved in `«namespace».Aux`: `namespace_size_def`,
`namespaceMAP_thm`, `namespaceSET1_thm`, `namespaceSET2_thm`, `namespaceSET3_thm` (same statement as HOL4).
For `id` the Lean equation lemmas of `idMAP`, `idSET1`, `idSET2`, `id_size`, `id_CASE` are already
the HOL4 `*_thm`/`*_def` clauses.

### Name clashes to know about
- **`Bind`**: Lean core has the monad class `_root_.Bind`. After `open «namespace»`, the pattern `Bind a b`
  is *ambiguous* and Lean rejects it ("ambiguous pattern"). In patterns (`match`, `fun`, `cases`) write
  `«namespace».Bind a b`. In terms, `Bind a b` usually elaborates (the class cannot be applied to lists),
  but `«namespace».Bind` is the safe spelling.
- **`id`**: the HOL4 type `id` is `«namespace».id`. After `open «namespace»`, `id` may mean either this type or
  Lean's identity function `_root_.id`. Write the HOL4 identity `I` as `_root_.id` (or `fun x => x`).
  Do not name bound variables `id` if it can be avoided; HOL4 statements that use `id` as a variable name
  can use `i` instead (names of bound variables do not matter).
- `lemma` (HOL4 `Theorem lemma[local]` in namespaceProps) is not a keyword in Lean core/Batteries:
  `theorem lemma ...` in `namespace namespaceProps` gives `namespaceProps.lemma`.

## 3. Type variables and universes
- HOL4 orders type variables alphabetically: `('m,'n) id` and `('m,'n,'v) namespace`, with `'m` = module
  names, `'n` = short names, `'v` = values. Lean keeps this order: `«namespace».id m n`,
  `«namespace».namespace m n v`.
- Definitions are universe polymorphic (`Type u`). Statements may use `{m n v : Type _}` or plain `Type`.

## 4. Equality tests: `DecidableEq`
HOL4 equality is classical and always usable in `if` and in `ALOOKUP`. In Lean, the constants that test
equality of keys take instance arguments:

| constant | needs |
|---|---|
| `alist.ALOOKUP` | `[DecidableEq key]` |
| `nsLookup`, `nsSub`, `nsAll`, `nsAll2`, `nsDom` | `[DecidableEq m] [DecidableEq n]` |
| `nsLookupMod`, `nsOpen`, `nsDomMod` | `[DecidableEq m]` |
| `namespaceProps.alist_rel_restr`, `alistSub` | `[DecidableEq k]` |
| `namespaceProps.nsSub_compute` | `[DecidableEq m] [DecidableEq n]` |

Any `DecidableEq` instance decides the real `=` and all instances are equal (`Subsingleton`), so values do
not depend on the instance. Every type has one (`Classical.decEq`), so a statement with these instance
binders is equivalent to the HOL4 statement for all types. Stage-2 statements: add
`[DecidableEq m] [DecidableEq n]` binders (e.g. in a `variable` line). `«namespace».id m n` has a derived
`DecidableEq` instance (from those of `m`, `n`); `«namespace».namespace` has none (not needed; HOL4 `=` on
namespaces in statements is Lean `=` in `Prop`). For an `if` on a condition without an instance, use
`open Classical` locally.

## 5. Type mapping (HOL4 -> Lean)

| HOL4 | Lean | note |
|---|---|---|
| `bool` as the result of a predicate/relation (definitions with `⇔`, relations `R`, `P`) | `Prop` | `T`/`F` = `True`/`False`; `⇔` = `↔`; `=` between bools = `↔` (or `=` by `propext`) |
| `bool` stored as data | `Bool` | (not used in the pilot) |
| `num` | `Nat` | (only in size functions here) |
| `'a list` | `List α` | |
| `'a option` | `Option α` | `NONE`/`SOME` = `none`/`some` |
| `'a # 'b` | `α × β` | `FST`/`SND` = `.1`/`.2` (`Prod.fst`/`Prod.snd`) |
| `'a + 'b` | `α ⊕ β` | |
| `'a set` (= `'a -> bool`) | `pred_set.set α` (= `α → Prop`, a `def`) | possibly infinite; equality is extensional (`funext`, `propext`) |
| `('k,'v) alist` | `List (k × v)` (abbrev `«namespace».alist k v`) | order and duplicates kept; lookup finds the first |
| `('m,'n) id` | `«namespace».id m n` | |
| `('m,'n,'v) namespace` | `«namespace».namespace m n v` | nested inductive through `List (m × _)` |
| `int`, `char`, `string`, `mlstring`, `word`, `fmap`, `num` division | not used by the pilot modules | the first module that needs them fixes the mapping here. Known hazards: HOL4 `int` `/` and `%` floor (Lean `Int./`, `%` do not; `Int.fdiv`/`Int.fmod` floor) and `i / 0` is unspecified in HOL4; HOL4 `char` has 256 values (Lean `Char` is Unicode); HOL4 `fmap` is finite. |

## 6. Library constants (HOL4 -> Lean)

All are listed in `NAMES.tsv` with kind `lib`.

| HOL4 | Lean | note |
|---|---|---|
| `MAP f l` | `List.map f l` | |
| `FOLDR f e l` | `List.foldr f e l` | same argument order |
| `REVERSE l` | `List.reverse l` | |
| `l1 ++ l2` | `l1 ++ l2` | |
| `h::t`, `[]` | `h :: t`, `[]` | `CONS mn` = `List.cons mn` |
| `NULL l` | `l.isEmpty` (`Bool`; in a `Prop` position it means `l.isEmpty = true`) | |
| `MEM x l` | `x ∈ l` (`List.Mem`) | HOL4 `MEM x l` is `x IN LIST_TO_SET l`; same meaning |
| `EVERY P l` | `list.EVERY P l` | Prelude, HOL4 recursion equations; same as `∀ x ∈ l, P x` |
| `LIST_REL R l1 l2` | `List.Forall₂ R l1 l2` | Batteries; same lengths and pointwise `R` |
| `l1 ≼ l2` (`isPREFIX l1 l2`) | `l1 <+: l2` (`List.IsPrefix`) | `l1` is a prefix of `l2` |
| `IS_PREFIX l1 l2` (rich_list overload) | `l2 <+: l1` | **argument order flips**: `IS_PREFIX l1 l2` means `l2 ≼ l1` |
| `set l` (`LIST_TO_SET l`) | `list.LIST_TO_SET l` | |
| `list_size f l` | `list.list_size f l` | |
| `ALOOKUP l k` | `alist.ALOOKUP l k` | Prelude; `open alist (ALOOKUP)` to write `ALOOKUP` |
| `OPTION_MAP f x` | `Option.map f x` | |
| `OPTREL R x y` | `Option.Rel R x y` | core; `none`/`none` and `some`/`some` with `R` |
| `f ## g` (`PAIR_MAP`) | `Prod.map f g` | |
| `SUM_MAP f g` | `Sum.map f g` | |
| `setFST p`, `setSND p` | `pair.setFST p`, `pair.setSND p` | |
| `pair_size f g p` | `basicSize.pair_size f g p` | `1 + (f x + g y)` |
| `I` | `_root_.id` | see clash note |
| `f ∘ g` | `f ∘ g` | |
| `K x` | `fun _ => x` (`Function.const _ x`) | |
| `λ(x,v). t` (`UNCURRY`) | `fun (x, v) => t` | |
| `case x of NONE => a | SOME y => b` | `match x with \| none => a \| some y => b` | |
| `x IN s` | `x ∈ s` | instance `Membership α (pred_set.set α)`; unfolds to `s x` |
| `{}` / `∅` | `∅` (= `pred_set.EMPTY`) | |
| `𝕌(:α)` / `UNIV` | `pred_set.UNIV` | |
| `x INSERT s` | `insert x s` (= `pred_set.INSERT x s`) | |
| `{x}`, `{a; b}` | `{x}`, `{a, b}` | `{x}` is `insert x ∅`, as in HOL4 |
| `s ∪ t` | `s ∪ t` (= `pred_set.UNION s t`) | |
| `IMAGE f s` | `pred_set.IMAGE f s` | |
| `BIGUNION P` | `pred_set.BIGUNION P` | |
| `{x | P x}` (`GSPEC`) | `{ x | P x }` (macro for `pred_set.setOf fun x => P x`) | only the single-variable form; write `{f x | P x}` as `{ y | ∃ x, f x = y ∧ P x }` |

Hint for statement writers (not a HOL4 fact): membership in these sets unfolds by definition, e.g. `x ∈ insert a s` is
`x = a ∨ x ∈ s`, `x ∈ s ∪ t` is `x ∈ s ∨ x ∈ t`, `x ∈ nsDom e` is `∃ v, nsLookup e x = some v`; `Iff.rfl`,
`show` or `unfold` expose them, and set equality is proved by `funext x; apply propext`.

## 7. Modelling choices in the pilot definitions
- `nsDom`, `nsDomMod`: HOL4 writes `{n | (v,n) | v ∈ 𝕌(..) ∧ n ∈ 𝕌(..) ∧ P v n}`. The two `𝕌` conjuncts are
  always true and are left out: `nsDom env = { i | ∃ x, nsLookup env i = some x }` (same set).
- `nsOpen`: HOL4 `if NULL path` is `if path.isEmpty`.
- `nsMap`, `namespaceMAP`, `namespaceSET1/2/3`: well-founded recursion on `sizeOf` (real termination proofs).
  `nsMap`'s equation lemma `nsMap.eq_1` has exactly the HOL4 shape; `namespaceMAP`'s is stated with
  `fun p => (f1 p.1, namespaceMAP f1 f2 f3 p.2)` and `Aux.namespaceMAP_thm` gives the HOL4 `##` form.
- `namespaceSET1/2/3` are defined pointwise (`x ∈ namespaceSET3 (Bind a0 a1) ↔ (∃ p, p ∈ a0 ∧ x = p.2) ∨
  ∃ p, ∃ _ : p ∈ a1, x ∈ namespaceSET3 p.2`); the HOL4 `BIGUNION`/`IMAGE` equations are `Aux.namespaceSETk_thm`.
  `namespaceSET3` contains every value in the namespace, shadowed ones included, as in HOL4.
- `namespace_size` uses a mutual helper `«namespace».namespace_size_list` (not a HOL4 constant);
  `Aux.namespace_size_def` is the HOL4 equation.
- `nsSub_compute` (namespaceProps): HOL4's recursion passes `nsSub_compute (k::path) R` to `alistSub`. Lean
  cannot see that the arguments are smaller, so the recursive call is wrapped in
  `if _h : sizeOf v1 < sizeOf (Bind e1V e1M) then ... else False`. `alistSub` only applies its relation to
  values found by `ALOOKUP` in `e1M`, and these are always smaller, so the guard never fires:
  `namespaceProps.nsSub_compute_def` proves the exact HOL4 equation. Use that theorem, not the raw
  unfolding.
- No `sorry`, `partial`, `opaque`, `axiom` in any definition. No `ALLOW_OPAQUE.txt` is needed.

## 8. Reuse
- Later milestones import `CakeML.Semantics.Namespace` for `id`/`namespace` and never redefine them.
- New HOL4 library material goes into `CakeML/Prelude/` in the namespace of its HOL4 theory
  (`pred_set`, `list`, `pair`, `alist`, `basicSize`, ...); check there first.
