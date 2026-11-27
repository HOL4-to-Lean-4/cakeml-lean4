-- Translation of CakeML `semantics/namespaceScript.sml` (milestone pilot).
-- HOL4 theory `namespace`; Ancestors[qualified] alist.
-- `namespace` is a Lean keyword, so the Lean namespace (and the type) are written `«namespace»`.
import CakeML.Prelude.Alist
import CakeML.Prelude.PredSet
import CakeML.Prelude.List
import CakeML.Prelude.Pair

universe u1 u2 u3 u4 u5 u6

namespace «namespace»

open alist (ALOOKUP)

/- HOL4: Type alist = ``: ('k # 'v) list`` -/
/-- HOL4 type abbreviation `('k,'v) alist`. -/
abbrev alist (k : Type u1) (v : Type u2) : Type (max u1 u2) := List (k × v)

/- HOL4:
Datatype:
  id = Short 'n | Long 'm id
End
-/
/-- HOL4 `('m,'n) id`: short or module-qualified identifiers. -/
inductive id (m : Type u1) (n : Type u2) : Type (max u1 u2) where
  | Short : n → id m n
  | Long : m → id m n → id m n
  deriving DecidableEq

export id (Short Long)

/- HOL4:
Definition mk_id_def:
  mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
End
-/
def mk_id {m : Type u1} {n : Type u2} : List m → n → id m n
  | [], n => Short n
  | mn :: mns, n => Long mn (mk_id mns n)

/- HOL4:
Definition id_to_n_def:
 id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
End
-/
def id_to_n {m : Type u1} {n : Type u2} : id m n → n
  | Short n => n
  | Long _ i => id_to_n i

/- HOL4:
Definition id_to_mods_def:
  id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
End
-/
def id_to_mods {m : Type u1} {n : Type u2} : id m n → List m
  | Short _ => []
  | Long mn i => mn :: id_to_mods i

/- HOL4:
Datatype:
  namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
End
-/
/-- HOL4 `('m,'n,'v) namespace`.  The two `alist` arguments are written out as
`List (n × v)` and `List (m × «namespace» m n v)` (the same types). -/
inductive «namespace» (m : Type u1) (n : Type u2) (v : Type u3) : Type (max u1 u2 u3) where
  | Bind : List (n × v) → List (m × «namespace» m n v) → «namespace» m n v

export «namespace» (Bind)

section
variable {m : Type u1} {n : Type u2} {v : Type u3}

/- HOL4:
Definition nsLookup_def:
  nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
End
-/
def nsLookup [DecidableEq m] [DecidableEq n] : «namespace» m n v → id m n → Option v
  | Bind vs _, Short x => ALOOKUP vs x
  | Bind _ ms, Long mn i =>
    match ALOOKUP ms mn with
    | none => none
    | some env => nsLookup env i

/- HOL4:
Definition nsLookupMod_def:
  nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
End
-/
def nsLookupMod [DecidableEq m] : «namespace» m n v → List m → Option («namespace» m n v)
  | e, [] => some e
  | Bind _ ms, mn :: path =>
    match ALOOKUP ms mn with
    | none => none
    | some env => nsLookupMod env path

/- HOL4:
Definition nsOpen_def:
  nsOpen path (env:('m,'n,'v)namespace) =
    if NULL path then NONE else nsLookupMod env path
End
-/
def nsOpen [DecidableEq m] (path : List m) (env : «namespace» m n v) : Option («namespace» m n v) :=
  if path.isEmpty then none else nsLookupMod env path

/- HOL4:
Definition nsEmpty_def:
  nsEmpty = Bind [] []
End
-/
def nsEmpty : «namespace» m n v := Bind [] []

/- HOL4:
Definition nsAppend_def:
  nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
End
-/
def nsAppend : «namespace» m n v → «namespace» m n v → «namespace» m n v
  | Bind v1 m1, Bind v2 m2 => Bind (v1 ++ v2) (m1 ++ m2)

/- HOL4:
Definition nsLift_def:
  nsLift mn env = Bind [] [(mn,env)]
End
-/
def nsLift (mn : m) (env : «namespace» m n v) : «namespace» m n v := Bind [] [(mn, env)]

/- HOL4:
Definition alist_to_ns_def:
  alist_to_ns a = Bind a []
End
-/
def alist_to_ns (a : List (n × v)) : «namespace» m n v := Bind a []

/- HOL4:
Definition nsBind_def:
  nsBind k x (Bind v m) = Bind ((k,x)::v) m
End
-/
def nsBind (k : n) (x : v) : «namespace» m n v → «namespace» m n v
  | Bind vs ms => Bind ((k, x) :: vs) ms

/- HOL4:
Definition nsBindList_def:
  nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
End
-/
def nsBindList (l : List (n × v)) (e : «namespace» m n v) : «namespace» m n v :=
  List.foldr (fun (x, y) e => nsBind x y e) e l

/- HOL4:
Definition nsOptBind_def:
  nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
End
-/
def nsOptBind (o : Option n) (x : v) (env : «namespace» m n v) : «namespace» m n v :=
  match o with
  | none => env
  | some k => nsBind k x env

/- HOL4:
Definition nsSing_def:
  nsSing n x = Bind [(n,x)] []
End
-/
def nsSing (k : n) (x : v) : «namespace» m n v := Bind [(k, x)] []

/- HOL4:
Definition nsSub_def:
  nsSub r env1 env2 ⇔
     (∀id v1.
        nsLookup env1 id = SOME v1 ⇒
        ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
End
-/
def nsSub {α : Type u3} {β : Type u4} [DecidableEq m] [DecidableEq n]
    (r : id m n → α → β → Prop) (env1 : «namespace» m n α) (env2 : «namespace» m n β) : Prop :=
  (∀ (i : id m n) (v1 : α),
      nsLookup env1 i = some v1 →
      ∃ v2, nsLookup env2 i = some v2 ∧ r i v1 v2) ∧
  ∀ path, nsLookupMod env2 path = none → nsLookupMod env1 path = none

/- HOL4:
Definition nsAll_def:
  nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
End
-/
def nsAll [DecidableEq m] [DecidableEq n] (f : id m n → v → Prop) (env : «namespace» m n v) : Prop :=
  ∀ (i : id m n) (x : v), nsLookup env i = some x → f i x

/- HOL4:
Definition nsAll2_def:
  nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
End
-/
def nsAll2 {α : Type u3} {β : Type u4} [DecidableEq m] [DecidableEq n]
    (r : id m n → α → β → Prop) (env1 : «namespace» m n α) (env2 : «namespace» m n β) : Prop :=
  nsSub r env1 env2 ∧ nsSub (fun x y z => r x z y) env2 env1

/- HOL4:
Definition nsDom_def:
  nsDom (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
End
-/
/-- HOL4 `nsDom env`.  The HOL4 conjuncts `v ∈ 𝕌(:φ)` and `n ∈ 𝕌(:(ν, ξ) id)` are always true
and are left out. -/
def nsDom [DecidableEq m] [DecidableEq n] (env : «namespace» m n v) : pred_set.set (id m n) :=
  { i | ∃ x, nsLookup env i = some x }

/- HOL4:
Definition nsDomMod_def:
  nsDomMod (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:(ν, ξ, φ) namespace) ∧ n ∈ 𝕌(:ν list) ∧
                  nsLookupMod env n = SOME v}
End
-/
/-- HOL4 `nsDomMod env`.  The HOL4 conjuncts `v ∈ 𝕌(..)` and `n ∈ 𝕌(..)` are always true
and are left out. -/
def nsDomMod [DecidableEq m] (env : «namespace» m n v) : pred_set.set (List m) :=
  { p | ∃ e, nsLookupMod env p = some e }

/- HOL4:
Definition nsMap_def:
  nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
End
-/
def nsMap {w : Type u4} (f : v → w) : «namespace» m n v → «namespace» m n w
  | Bind vs ms => Bind (List.map (fun (k, x) => (k, f x)) vs) (List.map (fun p => (p.1, nsMap f p.2)) ms)
termination_by e => sizeOf e
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹_ ∈ ms›
  cases p with
  | mk a b => simp only [Prod.mk.sizeOf_spec] at h; simp only [«namespace».Bind.sizeOf_spec]; omega

end

/-! ## Constants generated by HOL4's `Datatype` package

HOL4 also defines, for each datatype, a case constant, a size function and the functorial
map / set / relator constants (`idMAP`, `idSET1`, ..., `namespaceREL`).  None of them has
a HOL4 source text other than the stored theorems in `hol4/export/namespace.txt`; the comments
below quote the stored characteristic equations (`*_thm`, `*_case_def`, `*_size_def`, `*REL_def`).
The representation constructors `id_CONS` and `namespace_CONS` are not translated
(internal to the HOL4 datatype package; see `PROGRESS.tsv`). -/

section
variable {m : Type u1} {n : Type u2}

/- HOL4 (stored): id_case_def
  (∀a0 f f0. id_CASE (Short a0) f f0 = f a0) ∧ ∀a0 a1 f f0. id_CASE (Long a0 a1) f f0 = f0 a0 a1 -/
/-- HOL4 `id_CASE` (the `case` constant of `id`). -/
def id_CASE {α : Type u3} (x : id m n) (f : n → α) (f0 : m → id m n → α) : α :=
  match x with
  | Short a0 => f a0
  | Long a0 a1 => f0 a0 a1

/- HOL4 (stored): id_size_def
  (∀f0 f1 a0. id_size f0 f1 (Short a0) = 1 + f1 a0) ∧
  ∀f0 f1 a0 a1. id_size f0 f1 (Long a0 a1) = 1 + (f0 a0 + id_size f0 f1 a1) -/
/-- HOL4 `id_size`. -/
def id_size (f0 : m → Nat) (f1 : n → Nat) : id m n → Nat
  | Short a0 => 1 + f1 a0
  | Long a0 a1 => 1 + (f0 a0 + id_size f0 f1 a1)

/- HOL4 (stored): idMAP_thm
  idMAP f1 f2 (Short a0) = Short (f2 a0) ∧ idMAP f1 f2 (Long a0 a1) = Long (f1 a0) (idMAP f1 f2 a1) -/
/-- HOL4 `idMAP f1 f2`: `f1` maps module names, `f2` maps names. -/
def idMAP {m' : Type u3} {n' : Type u4} (f1 : m → m') (f2 : n → n') : id m n → id m' n'
  | Short a0 => Short (f2 a0)
  | Long a0 a1 => Long (f1 a0) (idMAP f1 f2 a1)

/- HOL4 (stored): idSET1_thm
  idSET1 (Short a0) = ∅ ∧ idSET1 (Long a0 a1) = a0 INSERT idSET1 a1 -/
/-- HOL4 `idSET1`: the module names in an identifier. -/
def idSET1 : id m n → pred_set.set m
  | Short _ => ∅
  | Long a0 a1 => insert a0 (idSET1 a1)

/- HOL4 (stored): idSET2_thm
  idSET2 (Short a0) = {a0} ∧ idSET2 (Long a0 a1) = idSET2 a1 -/
/-- HOL4 `idSET2`: the (singleton) set of the short name of an identifier. -/
def idSET2 : id m n → pred_set.set n
  | Short a0 => {a0}
  | Long _ a1 => idSET2 a1

/- HOL4 (stored): idREL_def
  idREL =
  (λR1 R2 x y.
     ∃z. (∀p. p ∈ idSET1 z ⇒ R1 (FST p) (SND p)) ∧ (∀p. p ∈ idSET2 z ⇒ R2 (FST p) (SND p)) ∧ idMAP FST FST z = x ∧
         idMAP SND SND z = y) -/
/-- HOL4 `idREL R1 R2`: the relator of `id`. -/
def idREL {m' : Type u3} {n' : Type u4} (R1 : m → m' → Prop) (R2 : n → n' → Prop)
    (x : id m n) (y : id m' n') : Prop :=
  ∃ z : id (m × m') (n × n'),
    (∀ p, p ∈ idSET1 z → R1 p.1 p.2) ∧ (∀ p, p ∈ idSET2 z → R2 p.1 p.2) ∧
    idMAP Prod.fst Prod.fst z = x ∧ idMAP Prod.snd Prod.snd z = y

end

section
variable {m : Type u1} {n : Type u2} {v : Type u3}

/- HOL4 (stored): namespace_case_def
  ∀a0 a1 f. namespace_CASE (Bind a0 a1) f = f a0 a1 -/
/-- HOL4 `namespace_CASE` (the `case` constant of `namespace`). -/
def namespace_CASE {α : Type u4} (x : «namespace» m n v)
    (f : List (n × v) → List (m × «namespace» m n v) → α) : α :=
  match x with
  | Bind a0 a1 => f a0 a1

/- HOL4 (stored): namespace_size_def
  ∀f0 f1 f2 a0 a1.
    namespace_size f0 f1 f2 (Bind a0 a1) =
    1 + (list_size (pair_size f1 f2) a0 + list_size (pair_size f0 (namespace_size f0 f1 f2)) a1)
  Lean: the inner `list_size (pair_size f0 (namespace_size f0 f1 f2))` is the helper
  `namespace_size_list` (structural recursion through the nested list); the HOL4 equation is
  `Aux.namespace_size_def` below. -/
mutual
/-- HOL4 `namespace_size`. -/
def namespace_size (f0 : m → Nat) (f1 : n → Nat) (f2 : v → Nat) : «namespace» m n v → Nat
  | Bind a0 a1 => 1 + (list.list_size (basicSize.pair_size f1 f2) a0 + namespace_size_list f0 f1 f2 a1)
/-- Helper: `namespace_size_list f0 f1 f2 l = list_size (pair_size f0 (namespace_size f0 f1 f2)) l`. -/
def namespace_size_list (f0 : m → Nat) (f1 : n → Nat) (f2 : v → Nat) :
    List (m × «namespace» m n v) → Nat
  | [] => 0
  | (a, e) :: t => 1 + ((1 + (f0 a + namespace_size f0 f1 f2 e)) + namespace_size_list f0 f1 f2 t)
end

/- HOL4 (stored): namespaceMAP_thm
  namespaceMAP f1 f2 f3 (Bind a0 a1) = Bind (MAP (f2 ## f3) a0) (MAP (f1 ## namespaceMAP f1 f2 f3) a1) -/
/-- HOL4 `namespaceMAP f1 f2 f3`: maps module names, names and values. -/
def namespaceMAP {m' : Type u4} {n' : Type u5} {v' : Type u6}
    (f1 : m → m') (f2 : n → n') (f3 : v → v') : «namespace» m n v → «namespace» m' n' v'
  | Bind a0 a1 =>
    Bind (List.map (Prod.map f2 f3) a0) (List.map (fun p => (f1 p.1, namespaceMAP f1 f2 f3 p.2)) a1)
termination_by e => sizeOf e
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹_ ∈ a1›
  cases p with
  | mk a b => simp only [Prod.mk.sizeOf_spec] at h; simp only [«namespace».Bind.sizeOf_spec]; omega

/- HOL4 (stored): namespaceSET1_thm
  namespaceSET1 (Bind a0 a1) =
  BIGUNION (IMAGE setFST (set a1)) ∪ BIGUNION (IMAGE namespaceSET1 (BIGUNION (IMAGE setSND (set a1))))
  Lean: written pointwise; the HOL4 equation is `Aux.namespaceSET1_thm` below. -/
/-- HOL4 `namespaceSET1`: all module names in a namespace (at any depth). -/
def namespaceSET1 : «namespace» m n v → pred_set.set m
  | Bind _ a1 => fun x => (∃ p, p ∈ a1 ∧ x = p.1) ∨ ∃ p, ∃ _ : p ∈ a1, x ∈ namespaceSET1 p.2
termination_by e => sizeOf e
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹p ∈ a1›
  cases p with
  | mk a b => simp only [Prod.mk.sizeOf_spec] at h; simp only [«namespace».Bind.sizeOf_spec]; omega

/- HOL4 (stored): namespaceSET2_thm
  namespaceSET2 (Bind a0 a1) =
  BIGUNION (IMAGE setFST (set a0)) ∪ BIGUNION (IMAGE namespaceSET2 (BIGUNION (IMAGE setSND (set a1))))
  Lean: written pointwise; the HOL4 equation is `Aux.namespaceSET2_thm` below. -/
/-- HOL4 `namespaceSET2`: all short names bound in a namespace (at any depth). -/
def namespaceSET2 : «namespace» m n v → pred_set.set n
  | Bind a0 a1 => fun x => (∃ p, p ∈ a0 ∧ x = p.1) ∨ ∃ p, ∃ _ : p ∈ a1, x ∈ namespaceSET2 p.2
termination_by e => sizeOf e
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹p ∈ a1›
  cases p with
  | mk a b => simp only [Prod.mk.sizeOf_spec] at h; simp only [«namespace».Bind.sizeOf_spec]; omega

/- HOL4 (stored): namespaceSET3_thm
  namespaceSET3 (Bind a0 a1) =
  BIGUNION (IMAGE setSND (set a0)) ∪ BIGUNION (IMAGE namespaceSET3 (BIGUNION (IMAGE setSND (set a1))))
  Lean: written pointwise; the HOL4 equation is `Aux.namespaceSET3_thm` below. -/
/-- HOL4 `namespaceSET3`: all values bound in a namespace (at any depth, shadowed ones included). -/
def namespaceSET3 : «namespace» m n v → pred_set.set v
  | Bind a0 a1 => fun x => (∃ p, p ∈ a0 ∧ x = p.2) ∨ ∃ p, ∃ _ : p ∈ a1, x ∈ namespaceSET3 p.2
termination_by e => sizeOf e
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹p ∈ a1›
  cases p with
  | mk a b => simp only [Prod.mk.sizeOf_spec] at h; simp only [«namespace».Bind.sizeOf_spec]; omega

/- HOL4 (stored): namespaceREL_def
  namespaceREL =
  (λR1 R2 R3 x y.
     ∃z. (∀p. p ∈ namespaceSET1 z ⇒ R1 (FST p) (SND p)) ∧ (∀p. p ∈ namespaceSET2 z ⇒ R2 (FST p) (SND p)) ∧
         (∀p. p ∈ namespaceSET3 z ⇒ R3 (FST p) (SND p)) ∧ namespaceMAP FST FST FST z = x ∧
         namespaceMAP SND SND SND z = y) -/
/-- HOL4 `namespaceREL R1 R2 R3`: the relator of `namespace`. -/
def namespaceREL {m' : Type u4} {n' : Type u5} {v' : Type u6}
    (R1 : m → m' → Prop) (R2 : n → n' → Prop) (R3 : v → v' → Prop)
    (x : «namespace» m n v) (y : «namespace» m' n' v') : Prop :=
  ∃ z : «namespace» (m × m') (n × n') (v × v'),
    (∀ p, p ∈ namespaceSET1 z → R1 p.1 p.2) ∧ (∀ p, p ∈ namespaceSET2 z → R2 p.1 p.2) ∧
    (∀ p, p ∈ namespaceSET3 z → R3 p.1 p.2) ∧
    namespaceMAP Prod.fst Prod.fst Prod.fst z = x ∧ namespaceMAP Prod.snd Prod.snd Prod.snd z = y

end

/-! ## HOL4 characteristic equations that Lean's own equation lemmas do not state literally -/

namespace Aux
open pred_set

variable {m : Type u1} {n : Type u2} {v : Type u3}

theorem namespace_size_list_eq (f0 : m → Nat) (f1 : n → Nat) (f2 : v → Nat) :
    ∀ l : List (m × «namespace» m n v),
      namespace_size_list f0 f1 f2 l =
        list.list_size (basicSize.pair_size f0 (namespace_size f0 f1 f2)) l
  | [] => by unfold namespace_size_list list.list_size; exact Eq.refl 0
  | (a, e) :: t => by
    unfold namespace_size_list list.list_size basicSize.pair_size
    exact congrArg (fun r => 1 + ((1 + (f0 a + namespace_size f0 f1 f2 e)) + r))
      (namespace_size_list_eq f0 f1 f2 t)

/-- HOL4 `namespace_size_def`. -/
theorem namespace_size_def (f0 : m → Nat) (f1 : n → Nat) (f2 : v → Nat)
    (a0 : List (n × v)) (a1 : List (m × «namespace» m n v)) :
    namespace_size f0 f1 f2 (Bind a0 a1) =
      1 + (list.list_size (basicSize.pair_size f1 f2) a0 +
        list.list_size (basicSize.pair_size f0 (namespace_size f0 f1 f2)) a1) := by
  unfold namespace_size
  exact congrArg (fun r => 1 + (list.list_size (basicSize.pair_size f1 f2) a0 + r))
    (namespace_size_list_eq f0 f1 f2 a1)

/-- HOL4 `namespaceMAP_thm`. -/
theorem namespaceMAP_thm {m' : Type u4} {n' : Type u5} {v' : Type u6}
    (f1 : m → m') (f2 : n → n') (f3 : v → v') (a0 : List (n × v)) (a1 : List (m × «namespace» m n v)) :
    namespaceMAP f1 f2 f3 (Bind a0 a1) =
      Bind (List.map (Prod.map f2 f3) a0) (List.map (Prod.map f1 (namespaceMAP f1 f2 f3)) a1) := by
  unfold namespaceMAP
  exact Eq.refl _

private theorem mem_big_image_setFST {α : Type u1} {β : Type u2} (l : List (α × β)) (x : α) :
    x ∈ BIGUNION (IMAGE pair.setFST (list.LIST_TO_SET l)) ↔ ∃ p, p ∈ l ∧ x = p.1 := by
  constructor
  · rintro ⟨s, ⟨p, rfl, hp⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨pair.setFST p, ⟨p, rfl, hp⟩, hx⟩

private theorem mem_big_image_setSND {α : Type u1} {β : Type u2} (l : List (α × β)) (x : β) :
    x ∈ BIGUNION (IMAGE pair.setSND (list.LIST_TO_SET l)) ↔ ∃ p, p ∈ l ∧ x = p.2 := by
  constructor
  · rintro ⟨s, ⟨p, rfl, hp⟩, hx⟩
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨pair.setSND p, ⟨p, rfl, hp⟩, hx⟩

private theorem mem_big_image_sub {γ : Type u4} (F : «namespace» m n v → set γ)
    (a1 : List (m × «namespace» m n v)) (x : γ) :
    x ∈ BIGUNION (IMAGE F (BIGUNION (IMAGE pair.setSND (list.LIST_TO_SET a1)))) ↔
      ∃ p, ∃ _ : p ∈ a1, x ∈ F p.2 := by
  constructor
  · rintro ⟨s, ⟨e, rfl, he⟩, hx⟩
    obtain ⟨p, hp, rfl⟩ := (mem_big_image_setSND a1 e).1 he
    exact ⟨p, hp, hx⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨F p.2, ⟨p.2, rfl, (mem_big_image_setSND a1 p.2).2 ⟨p, hp, rfl⟩⟩, hx⟩

/-- HOL4 `namespaceSET1_thm`. -/
theorem namespaceSET1_thm (a0 : List (n × v)) (a1 : List (m × «namespace» m n v)) :
    namespaceSET1 (Bind a0 a1) =
      BIGUNION (IMAGE pair.setFST (list.LIST_TO_SET a1)) ∪
        BIGUNION (IMAGE namespaceSET1 (BIGUNION (IMAGE pair.setSND (list.LIST_TO_SET a1)))) := by
  unfold namespaceSET1
  funext x
  apply propext
  show _ ↔ (x ∈ BIGUNION _ ∨ x ∈ BIGUNION _)
  exact (or_congr (mem_big_image_setFST a1 x) (mem_big_image_sub namespaceSET1 a1 x)).symm

/-- HOL4 `namespaceSET2_thm`. -/
theorem namespaceSET2_thm (a0 : List (n × v)) (a1 : List (m × «namespace» m n v)) :
    namespaceSET2 (Bind a0 a1) =
      BIGUNION (IMAGE pair.setFST (list.LIST_TO_SET a0)) ∪
        BIGUNION (IMAGE namespaceSET2 (BIGUNION (IMAGE pair.setSND (list.LIST_TO_SET a1)))) := by
  unfold namespaceSET2
  funext x
  apply propext
  show _ ↔ (x ∈ BIGUNION _ ∨ x ∈ BIGUNION _)
  exact (or_congr (mem_big_image_setFST a0 x) (mem_big_image_sub namespaceSET2 a1 x)).symm

/-- HOL4 `namespaceSET3_thm`. -/
theorem namespaceSET3_thm (a0 : List (n × v)) (a1 : List (m × «namespace» m n v)) :
    namespaceSET3 (Bind a0 a1) =
      BIGUNION (IMAGE pair.setSND (list.LIST_TO_SET a0)) ∪
        BIGUNION (IMAGE namespaceSET3 (BIGUNION (IMAGE pair.setSND (list.LIST_TO_SET a1)))) := by
  unfold namespaceSET3
  funext x
  apply propext
  show _ ↔ (x ∈ BIGUNION _ ∨ x ∈ BIGUNION _)
  exact (or_congr (mem_big_image_setSND a0 x) (mem_big_image_sub namespaceSET3 a1 x)).symm

end Aux

end «namespace»
