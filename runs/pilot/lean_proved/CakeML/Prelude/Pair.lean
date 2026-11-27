import CakeML.Prelude.PredSet

/-
HOL4 library: `pair` and `basicSize` constants with no exact Lean core counterpart.
`FST` = `Prod.fst`, `SND` = `Prod.snd`, `f ## g` (PAIR_MAP) = `Prod.map f g`, `(x,y)` = `(x, y)`.
-/

universe u v

namespace pair

variable {α : Type u} {β : Type v}

/- HOL4: pair$setFST, `setFST p = λx. x = FST p` (setFST_def) -/
/-- HOL4 `setFST p`. -/
def setFST (p : α × β) : pred_set.set α := fun x => x = p.1

/- HOL4: pair$setSND, `setSND p = λx. x = SND p` (setSND_def) -/
/-- HOL4 `setSND p`. -/
def setSND (p : α × β) : pred_set.set β := fun x => x = p.2

end pair

namespace basicSize

variable {α : Type u} {β : Type v}

/- HOL4: basicSize$pair_size, `pair_size f g (x, y) = 1 + (f x + g y)` (pair_size_def) -/
/-- HOL4 `pair_size f g p`. -/
def pair_size (f : α → Nat) (g : β → Nat) : α × β → Nat
  | (x, y) => 1 + (f x + g y)

end basicSize
