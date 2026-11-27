import Lean
open Lean

/-!
Environment dump for `scan.py`. Adapted from Phase 1's `KernelCheck.lean` (which constants depend on `sorryAx`,
declared axioms, other axioms) and `TyVarsTS.lean` (number of type-variable binders of every constant), but as a
stand-alone `lean --run` program: it loads the compiled root module and needs no `#eval` inside the project.
Usage (from the project root, after `lake build`):  lake env lean --run <this file> [RootModule]  (default `CakeML`)
Output, one TSV row per constant declared in a module under the root's namespace:
  C  module  name  kind  sorry  reduceBool  unsafe  nTypeBinders  otherAxioms  cakemlConstsInType
-/

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Number of leading binders whose type is a sort or a type former into a sort (HOL4 type variables become these). -/
def countTypeBinders : Expr → Nat
  | .forallE _ d b _ =>
      (if (d.getForallBody).isSort then 1 else 0) + countTypeBinders b
  | _ => 0

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

def main (args : List String) : IO UInt32 := do
  let root := (args.headD "CakeML").toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root }] {} (trustLevel := 0)
  let inRoot (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    let m := env.header.moduleNames[idx.toNat]!
    if root.isPrefixOf m then some m else none
  let mut rows := #[]
  for (n, ci) in env.constants.toList do
    let some m := inRoot n | continue
    if n.isInternal || n.isImplementationDetail then continue
    let k := kindOf ci
    if k == "rec" then continue
    let ctx : Core.Context := { fileName := "<scan>", fileMap := default }
    let (axs, _) ← (do
        let a ← (Lean.collectAxioms n : CoreM _)
        pure a).toIO ctx { env := env }
    let sorryUse := axs.contains ``sorryAx
    let rb := axs.contains ``Lean.ofReduceBool || axs.contains ``Lean.trustCompiler
    let other := axs.filter (fun a => !(stdAxioms.contains a) && a != ``sorryAx && a != ``Lean.ofReduceBool && a != ``Lean.trustCompiler)
    let uns : Bool := match ci with
      | .defnInfo d => decide (d.safety == .unsafe) || decide (d.safety == .partial)
      | .opaqueInfo d => d.isUnsafe
      | _ => false
    let consts := (ci.type.getUsedConstants.filter (fun c => c != n && (inRoot c).isSome)).toList
    rows := rows.push s!"C\t{m}\t{n}\t{k}\t{if sorryUse then 1 else 0}\t{if rb then 1 else 0}\t{if uns then 1 else 0}\t{countTypeBinders ci.type}\t{",".intercalate (other.toList.map toString)}\t{",".intercalate (consts.map toString)}"
  for r in rows.qsort (· < ·) do IO.println r
  return 0
