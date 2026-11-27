/-
HOL4 library: `alist` theory (association lists).

HOL4 tests key equality with its built-in (classical) equality.  Here the key type carries a
`DecidableEq` instance.  Every `DecidableEq` instance decides the real equality `=`, and any two
instances are equal (`Subsingleton (Decidable p)`), so the result does not depend on the
instance; a type without a computable instance can use `Classical.decEq`.
-/

universe u v

namespace alist

variable {α : Type u} {β : Type v}

/- HOL4: alist$ALOOKUP
     (ALOOKUP [] q = NONE) /\
     (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q)   (ALOOKUP_def) -/
/-- HOL4 `ALOOKUP l q`: the value of the first pair in `l` whose key is `q`. -/
def ALOOKUP [DecidableEq α] : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

end alist
