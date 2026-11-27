/-
HOL4 library: predicate sets (`pred_set` theory, and `bool$IN`).

HOL4's `'a set` is the type `'a -> bool`.  Here `pred_set.set α` is the type `α → Prop`,
wrapped in a `def` so that the set instances below do not apply to every function type.
Set equality is extensional (by `funext` and `propext`), as in HOL4.
Only the constants that the translated theories need are given.
-/

universe u v

namespace pred_set

/- HOL4: pred_set type abbreviation `'a set = 'a -> bool` -/
/-- HOL4 `'a set`. -/
def set (α : Type u) : Type u := α → Prop

variable {α : Type u} {β : Type v}

/- HOL4: bool$IN, `x IN s ⇔ s x` (IN_DEF) -/
/-- HOL4 `x IN s` is `x ∈ s`. -/
instance : Membership α (set α) := ⟨fun s x => s x⟩

/- HOL4: pred_set$GSPEC (set comprehension `{x | P x}`); `x ∈ {y | P y} ⇔ P x` -/
/-- HOL4 `{x | P x}`. -/
def setOf (p : α → Prop) : set α := p

/- HOL4: pred_set$EMPTY, `EMPTY = (\x:'a.F)` (EMPTY_DEF) -/
/-- HOL4 `EMPTY`, printed `∅`. -/
def EMPTY : set α := fun _ => False

instance : EmptyCollection (set α) := ⟨EMPTY⟩

/- HOL4: pred_set$UNIV, `UNIV = (\x:'a.T)` (UNIV_DEF) -/
/-- HOL4 `UNIV`, printed `𝕌(:α)`. -/
def UNIV : set α := fun _ => True

/- HOL4: pred_set$INSERT, `INSERT (x:'a) s = {y | (y = x) \/ y IN s}` (INSERT_DEF) -/
/-- HOL4 `x INSERT s`. -/
def INSERT (x : α) (s : set α) : set α := fun y => y = x ∨ y ∈ s

instance : Insert α (set α) := ⟨INSERT⟩

/- HOL4: the set literal `{x}` is `x INSERT {}` -/
instance : Singleton α (set α) := ⟨fun x => INSERT x EMPTY⟩

/- HOL4: pred_set$UNION, `UNION s t = {x:'a | x IN s \/ x IN t}` (UNION_DEF) -/
/-- HOL4 `s UNION t`, printed `s ∪ t`. -/
def UNION (s t : set α) : set α := fun x => x ∈ s ∨ x ∈ t

instance : Union (set α) := ⟨UNION⟩

/- HOL4: pred_set$IMAGE, `IMAGE (f:'a->'b) s = {f x | x IN s}` (IMAGE_DEF) -/
/-- HOL4 `IMAGE f s`. -/
def IMAGE (f : α → β) (s : set α) : set β := fun y => ∃ x, f x = y ∧ x ∈ s

/- HOL4: pred_set$BIGUNION, `BIGUNION P = { x | ?s. s IN P /\ x IN s}` -/
/-- HOL4 `BIGUNION P`. -/
def BIGUNION (P : set (set α)) : set α := fun x => ∃ s, s ∈ P ∧ x ∈ s

end pred_set

/-- HOL4 set comprehension `{x | P x}` (pred_set$GSPEC), as `pred_set.setOf`. -/
syntax (name := pred_setOf) "{" ident " | " term "}" : term

macro_rules (kind := pred_setOf)
  | `({ $x:ident | $p }) => `(pred_set.setOf fun $x:ident => $p)
