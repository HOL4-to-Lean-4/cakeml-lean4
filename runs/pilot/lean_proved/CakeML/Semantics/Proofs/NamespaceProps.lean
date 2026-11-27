-- Translation of CakeML `semantics/proofs/namespacePropsScript.sml` (milestone pilot).
-- HOL4 theory `namespaceProps`; Ancestors ast namespace.
-- Stage 1: the definitions of the script.  Stage 2 adds the theorem statements.
import CakeML.Semantics.Ast
import CakeML.Semantics.Namespace

universe u1 u2 u3 u4

namespace namespaceProps

open «namespace»
open alist (ALOOKUP)

section
variable {k : Type u1} {α : Type u2} {β : Type u3}

/- HOL4:
Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End
-/
def alist_rel_restr [DecidableEq k] (R : k → α → β → Prop) (l1 : List (k × α)) (l2 : List (k × β)) :
    List k → Prop
  | [] => True
  | k1 :: keys =>
    match ALOOKUP l1 k1 with
    | none => False
    | some v1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys

/- HOL4:
Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End
-/
def alistSub [DecidableEq k] (R : k → α → β → Prop) (e1 : List (k × α)) (e2 : List (k × β)) : Prop :=
  alist_rel_restr R e1 e2 (List.map Prod.fst e1)

end

-- Helper lemmas for the termination of `nsSub_compute` and for its HOL4 equation.
namespace Aux

theorem ALOOKUP_mem {k : Type u1} {α : Type u2} [DecidableEq k] :
    ∀ (l : List (k × α)) (x : k) (y : α), ALOOKUP l x = some y → (x, y) ∈ l
  | [], _, _, h => by unfold ALOOKUP at h; cases h
  | (a, b) :: t, x, y, h => by
    unfold ALOOKUP at h
    split at h
    · cases h
      subst_vars
      exact List.Mem.head _
    · exact List.Mem.tail _ (ALOOKUP_mem t x y h)

theorem alist_rel_restr_congr {k : Type u1} {α : Type u2} {β : Type u3} [DecidableEq k]
    (R R' : k → α → β → Prop) (l1 : List (k × α)) (l2 : List (k × β))
    (h : ∀ x v1 v2, ALOOKUP l1 x = some v1 → ALOOKUP l2 x = some v2 → (R x v1 v2 ↔ R' x v1 v2)) :
    ∀ keys, alist_rel_restr R l1 l2 keys ↔ alist_rel_restr R' l1 l2 keys
  | [] => Iff.rfl
  | k1 :: keys => by
    unfold alist_rel_restr
    split
    · exact Iff.rfl
    · rename_i v1 h1
      split
      · exact Iff.rfl
      · rename_i v2 h2
        exact and_congr (h k1 v1 v2 h1 h2) (alist_rel_restr_congr R R' l1 l2 h keys)

theorem sizeOf_lt_of_ALOOKUP {m : Type u1} {n : Type u2} {v : Type u3} [DecidableEq m]
    (vs : List (n × v)) (ms : List (m × «namespace» m n v)) (x : m) (e : «namespace» m n v)
    (h : ALOOKUP ms x = some e) : sizeOf e < sizeOf (Bind vs ms) := by
  have h1 := List.sizeOf_lt_of_mem (ALOOKUP_mem ms x e h)
  simp only [Prod.mk.sizeOf_spec] at h1
  simp only [«namespace».Bind.sizeOf_spec]
  omega

end Aux

/- HOL4:
Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (\k v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
End
   Lean: the recursive call is guarded by `sizeOf v1 < sizeOf (Bind e1V e1M)`.  The guard holds
   at every point where `alistSub` uses its relation (`v1` is then an `ALOOKUP` result from
   `e1M`), so the guard does not change the value; the HOL4 equation is
   `nsSub_compute_def` below. -/
def nsSub_compute {m : Type u1} {n : Type u2} {α : Type u3} {β : Type u4}
    [DecidableEq m] [DecidableEq n] (path : List m) (R : id m n → α → β → Prop) :
    «namespace» m n α → «namespace» m n β → Prop
  | «namespace».Bind e1V e1M, «namespace».Bind e2V e2M =>
    alistSub (fun k v1 v2 => R (mk_id (List.reverse path) k) v1 v2) e1V e2V ∧
    alistSub (fun k v1 v2 =>
        if _h : sizeOf v1 < sizeOf (Bind e1V e1M) then nsSub_compute (k :: path) R v1 v2 else False)
      e1M e2M
termination_by e1 _ => sizeOf e1
decreasing_by exact _h

/-- HOL4 `nsSub_compute_def` (the equation HOL4 stores for `nsSub_compute`). -/
theorem nsSub_compute_def {m : Type u1} {n : Type u2} {α : Type u3} {β : Type u4}
    [DecidableEq m] [DecidableEq n] (path : List m) (e2V : List (n × β))
    (e2M : List (m × «namespace» m n β)) (e1V : List (n × α)) (e1M : List (m × «namespace» m n α))
    (R : id m n → α → β → Prop) :
    nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ↔
      alistSub (fun k v1 v2 => R (mk_id (List.reverse path) k) v1 v2) e1V e2V ∧
      alistSub (fun k v1 v2 => nsSub_compute (k :: path) R v1 v2) e1M e2M := by
  rewrite [nsSub_compute.eq_1]
  apply and_congr Iff.rfl
  apply Aux.alist_rel_restr_congr
  intro x v1 v2 h1 _
  exact Iff.of_eq (dif_pos (Aux.sizeOf_lt_of_ALOOKUP e1V e1M x v1 h1))

/-! ## Auxiliary lemmas for the stage-2 proofs (not HOL4 theorems) -/
namespace Aux
set_option linter.unusedSectionVars false

section
variable {α : Type u1}

theorem set_ext {s t : pred_set.set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

theorem mem_empty (x : α) : x ∈ (∅ : pred_set.set α) ↔ False := Iff.rfl

theorem mem_insert (x a : α) (s : pred_set.set α) : x ∈ (insert a s : pred_set.set α) ↔ x = a ∨ x ∈ s :=
  Iff.rfl

theorem mem_singleton (x a : α) : x ∈ ({a} : pred_set.set α) ↔ x = a :=
  ⟨fun h => h.elim (fun h => h) False.elim, Or.inl⟩

theorem mem_union (x : α) (s t : pred_set.set α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := Iff.rfl

theorem mem_image {β : Type u2} (f : α → β) (s : pred_set.set α) (y : β) :
    y ∈ pred_set.IMAGE f s ↔ ∃ x, f x = y ∧ x ∈ s := Iff.rfl

theorem mem_LIST_TO_SET (x : α) (l : List α) : x ∈ list.LIST_TO_SET l ↔ x ∈ l := Iff.rfl

theorem EVERY_iff (P : α → Prop) : ∀ l : List α, list.EVERY P l ↔ ∀ x, x ∈ l → P x
  | [] => by simp [list.EVERY]
  | h :: t => by
    simp only [list.EVERY, EVERY_iff P t, List.forall_mem_cons]

theorem map_eq_self (f : α → α) : ∀ l : List α, (∀ x, x ∈ l → f x = x) → List.map f l = l
  | [], _ => rfl
  | h :: t, H => by
    rw [List.map_cons, H h (List.mem_cons.mpr (Or.inl rfl)),
      map_eq_self f t (fun x hx => H x (List.mem_cons.mpr (Or.inr hx)))]

end

section
variable {k : Type u1} {α : Type u2} {β : Type u3} [DecidableEq k]

theorem ALOOKUP_nil' (x : k) : ALOOKUP ([] : List (k × α)) x = none := by
  simp only [ALOOKUP]

theorem ALOOKUP_cons' (a : k) (b : α) (t : List (k × α)) (x : k) :
    ALOOKUP ((a, b) :: t) x = if a = x then some b else ALOOKUP t x := by
  simp only [ALOOKUP]

theorem ALOOKUP_append_some (l1 l2 : List (k × α)) (x : k) (v : α)
    (h : ALOOKUP l1 x = some v) : ALOOKUP (l1 ++ l2) x = some v := by
  induction l1 with
  | nil => simp [ALOOKUP] at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases hx : a = x
    · simp only [List.cons_append, ALOOKUP_cons', hx, if_true] at h ⊢
      exact h
    · simp only [List.cons_append, ALOOKUP_cons', hx, if_false] at h ⊢
      exact ih h

theorem ALOOKUP_append_none (l1 l2 : List (k × α)) (x : k)
    (h : ALOOKUP l1 x = none) : ALOOKUP (l1 ++ l2) x = ALOOKUP l2 x := by
  induction l1 with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases hx : a = x
    · simp [ALOOKUP_cons', hx] at h
    · simp only [List.cons_append, ALOOKUP_cons', hx, if_false] at h ⊢
      exact ih h

theorem ALOOKUP_map (g : α → β) : ∀ (l : List (k × α)) (x : k),
    ALOOKUP (List.map (fun p => (p.1, g p.2)) l) x = Option.map g (ALOOKUP l x)
  | [], x => rfl
  | (a, b) :: t, x => by
    by_cases hx : a = x
    · simp [ALOOKUP_cons', hx]
    · simp [ALOOKUP_cons', hx, ALOOKUP_map g t x]

theorem ALOOKUP_isSome_iff : ∀ (l : List (k × α)) (x : k),
    (∃ y, ALOOKUP l x = some y) ↔ x ∈ List.map Prod.fst l
  | [], x => by simp [ALOOKUP]
  | (a, b) :: t, x => by
    by_cases hx : a = x
    · subst hx; simp [ALOOKUP_cons']
    · have hx' : x ≠ a := fun h => hx h.symm
      simp [ALOOKUP_cons', hx, hx', ← ALOOKUP_isSome_iff t x]

end

section
variable {m : Type u1} {n : Type u2} {v : Type u3} [DecidableEq m]

theorem nsLookupMod_nil (e : «namespace» m n v) : nsLookupMod e [] = some e := by
  simp only [nsLookupMod]

theorem nsLookupMod_cons (vs : List (n × v)) (ms : List (m × «namespace» m n v)) (a : m)
    (p : List m) :
    nsLookupMod (Bind vs ms) (a :: p) = (ALOOKUP ms a).bind (fun e => nsLookupMod e p) := by
  simp only [nsLookupMod]
  cases ALOOKUP ms a <;> rfl

theorem nsOpen_eq_some_iff (path : List m) (env opened : «namespace» m n v) :
    nsOpen path env = some opened ↔ path ≠ [] ∧ nsLookupMod env path = some opened := by
  cases path with
  | nil => simp [nsOpen]
  | cons a p => simp [nsOpen]

theorem nsAppend_Bind (v1 v2 : List (n × v)) (m1 m2 : List (m × «namespace» m n v)) :
    nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2) := by
  simp only [nsAppend]

theorem nil_ne_prefix {p1 p2 : List m} : ¬ (p1 ≠ [] ∧ ([] : List m) = p1 ++ p2) := by
  rintro ⟨h1, h2⟩
  cases p1 with
  | nil => exact h1 rfl
  | cons _ _ => simp at h2

theorem prefix_some {vs : List (n × v)} {ms : List (m × «namespace» m n v)} {a : m}
    {e : «namespace» m n v} (h : ALOOKUP ms a = some e) (l : List m) :
    ∃ p1 p2 e3, p1 ≠ [] ∧ a :: l = p1 ++ p2 ∧ nsLookupMod (Bind vs ms) p1 = some e3 :=
  ⟨[a], l, e, by simp, rfl, by simp [nsLookupMod_cons, h, nsLookupMod_nil]⟩

theorem prefix_none {vs : List (n × v)} {ms : List (m × «namespace» m n v)} {a : m}
    (h : ALOOKUP ms a = none) (l : List m) :
    ∀ p1 p2, p1 ≠ [] ∧ a :: l = p1 ++ p2 → nsLookupMod (Bind vs ms) p1 = none := by
  rintro p1 p2 ⟨h1, h2⟩
  cases p1 with
  | nil => exact absurd rfl h1
  | cons b t =>
    rw [List.cons_append] at h2
    obtain ⟨rfl, _⟩ := List.cons.inj h2
    simp [nsLookupMod_cons, h]

theorem nsLookupMod_Bind_nil_cons (vs : List (n × v)) (a : m) (p : List m) :
    nsLookupMod (Bind vs [] : «namespace» m n v) (a :: p) = none := by
  simp [nsLookupMod_cons, ALOOKUP_nil']

theorem nsLookupMod_nsSing_none {w : Type u4} (k : n) (z : v) (z' : w) (p : List m) :
    nsLookupMod (nsSing k z : «namespace» m n v) p = none →
      nsLookupMod (nsSing k z' : «namespace» m n w) p = none := by
  intro hp
  cases p with
  | nil => rw [nsLookupMod_nil] at hp; cases hp
  | cons a q => exact nsLookupMod_Bind_nil_cons _ a q

theorem nsLookupMod_nsBind_none (x : n) (y : v) (e : «namespace» m n v) (p : List m) :
    nsLookupMod (nsBind x y e) p = none ↔ nsLookupMod e p = none := by
  obtain ⟨vs, ms⟩ := e
  cases p with
  | nil => simp [nsLookupMod_nil]
  | cons a q => simp [nsBind, nsLookupMod_cons]

theorem nsLookupMod_lift_append_cons (mn : m) (e e2 : «namespace» m n v) (a : m) (q : List m) :
    nsLookupMod (nsAppend (nsLift mn e) e2) (a :: q) =
      if mn = a then nsLookupMod e q else nsLookupMod e2 (a :: q) := by
  obtain ⟨vs, ms⟩ := e2
  simp only [nsLift, nsAppend, List.nil_append, List.singleton_append, nsLookupMod_cons,
    ALOOKUP_cons']
  by_cases h : mn = a <;> simp [h]

theorem flat_of_domMod {vs : List (n × v)} {ms : List (m × «namespace» m n v)}
    (h : nsDomMod (Bind vs ms) = {[]}) : ms = [] := by
  cases ms with
  | nil => rfl
  | cons p t =>
    obtain ⟨a, e⟩ := p
    have h1 : [a] ∈ nsDomMod (Bind vs ((a, e) :: t)) :=
      ⟨e, by simp [nsLookupMod_cons, ALOOKUP_cons', nsLookupMod_nil]⟩
    rw [h] at h1
    exact absurd ((mem_singleton _ _).mp h1) (by simp)

theorem mem_nsDomMod (e : «namespace» m n v) (p : List m) :
    p ∈ nsDomMod e ↔ ∃ x, nsLookupMod e p = some x := Iff.rfl

/-- Induction principle for the nested type `namespace`. -/
theorem ns_induction {P : «namespace» m n v → Prop}
    (h : ∀ vs ms, (∀ p, p ∈ ms → P p.2) → P (Bind vs ms)) : ∀ e, P e
  | «namespace».Bind vs ms => h vs ms (fun p _hp => ns_induction h p.2)
termination_by e => sizeOf e
decreasing_by
  have h := List.sizeOf_lt_of_mem ‹_ ∈ ms›
  cases p with
  | mk a b => simp only [Prod.mk.sizeOf_spec] at h; simp only [«namespace».Bind.sizeOf_spec]; omega

theorem nsMap_Bind {w : Type u4} (f : v → w) (vs : List (n × v))
    (ms : List (m × «namespace» m n v)) :
    nsMap f (Bind vs ms) =
      Bind (List.map (fun p => (p.1, f p.2)) vs) (List.map (fun p => (p.1, nsMap f p.2)) ms) := by
  rw [nsMap]

theorem mem_namespaceSET3 (vs : List (n × v)) (ms : List (m × «namespace» m n v)) (x : v) :
    x ∈ namespaceSET3 (Bind vs ms) ↔
      (∃ p, p ∈ vs ∧ x = p.2) ∨ ∃ p, ∃ _ : p ∈ ms, x ∈ namespaceSET3 p.2 := by
  rw [namespaceSET3]
  try exact Iff.rfl

theorem nsBindList_Bind (vs : List (n × v)) (ms : List (m × «namespace» m n v)) :
    ∀ l : List (n × v), nsBindList l (Bind vs ms) = Bind (l ++ vs) ms
  | [] => rfl
  | (a, b) :: t => by
    show nsBind a b (nsBindList t (Bind vs ms)) = _
    simp [nsBindList_Bind vs ms t, nsBind]

end

section
variable {m : Type u1} {n : Type u2} {v : Type u3} [DecidableEq m] [DecidableEq n]

theorem nsLookup_short (vs : List (n × v)) (ms : List (m × «namespace» m n v)) (x : n) :
    nsLookup (Bind vs ms) (Short x) = ALOOKUP vs x := by
  simp only [nsLookup]

theorem nsLookup_long (vs : List (n × v)) (ms : List (m × «namespace» m n v)) (a : m)
    (i : id m n) :
    nsLookup (Bind vs ms) (Long a i) = (ALOOKUP ms a).bind (fun e => nsLookup e i) := by
  simp only [nsLookup]
  cases ALOOKUP ms a <;> rfl

theorem mem_nsDom (e : «namespace» m n v) (i : id m n) :
    i ∈ nsDom e ↔ ∃ x, nsLookup e i = some x := Iff.rfl

theorem nsLookup_nsBind_short (k : n) (x : v) (e : «namespace» m n v) :
    nsLookup (nsBind k x e) (Short k) = some x := by
  obtain ⟨vs, ms⟩ := e
  simp [nsBind, nsLookup_short, ALOOKUP_cons']

theorem nsLookup_nsBind_ne (i : id m n) (k : n) (x : v) (e : «namespace» m n v)
    (h : i ≠ Short k) : nsLookup (nsBind k x e) i = nsLookup e i := by
  obtain ⟨vs, ms⟩ := e
  cases i with
  | Short z =>
    have hz : k ≠ z := fun hh => h (by rw [hh])
    simp [nsBind, nsLookup_short, ALOOKUP_cons', hz]
  | Long a j => simp [nsBind, nsLookup_long]

end

end Aux

/-! ## Stage 2: theorem statements of `namespacePropsScript.sml` (HOL4 source order)

Type variables: `M` module names, `N` short names, `V`/`W`/`X`/`A`/`B` value types, `K` keys.
HOL4 free variables are explicit arguments (HOL4 quantifies them universally).  The HOL4 bound
variable name `id` is written `i` (clash with the type `«namespace».id`). -/

section Stage2
variable {M : Type _} {N : Type _} {V : Type _} {W : Type _} {X : Type _}
  {A : Type _} {B : Type _} {K : Type _}
  [DecidableEq M] [DecidableEq N] [DecidableEq K]

set_option linter.unusedSectionVars false

/- HOL4: !a b c d. mk_id a b = mk_id c d ⇔ (a = c) ∧ (b = d) -/
theorem mk_id_11 :
    ∀ (a : List M) (b : N) (c : List M) (d : N), mk_id a b = mk_id c d ↔ a = c ∧ b = d := by
  intro a b c d
  constructor
  · intro h
    induction a generalizing c with
    | nil =>
      cases c with
      | nil => simp [mk_id] at h; exact ⟨rfl, h⟩
      | cons c cs => simp [mk_id] at h
    | cons a as ih =>
      cases c with
      | nil => simp [mk_id] at h
      | cons c cs =>
        simp only [mk_id] at h
        obtain ⟨h1, h2⟩ := «namespace».id.Long.inj h
        obtain ⟨h3, h4⟩ := ih cs h2
        exact ⟨by rw [h1, h3], h4⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/- HOL4: !mn x. id_to_mods (mk_id mn x) = mn -/
theorem id_to_mods_mk_id : ∀ (mn : List M) (x : N), id_to_mods (mk_id mn x) = mn := by
  intro mn x
  induction mn with
  | nil => rfl
  | cons a as ih => simp [mk_id, id_to_mods, ih]

/- HOL4: !mn x. id_to_n (mk_id mn x) = x -/
theorem id_to_namemods_mk_id : ∀ (mn : List M) (x : N), id_to_n (mk_id mn x) = x := by
  intro mn x
  induction mn with
  | nil => rfl
  | cons a as ih => simp [mk_id, id_to_n, ih]

/- HOL4: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj : ∀ (i : id M N), ∃ (p : List M) (n : N), i = mk_id p n := by
  intro i
  induction i with
  | Short x => exact ⟨[], x, rfl⟩
  | Long mn i ih =>
    obtain ⟨p, n, h⟩ := ih
    exact ⟨mn :: p, n, by subst h; rfl⟩

/- HOL4: !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm : ∀ (i : id M N), mk_id (id_to_mods i) (id_to_n i) = i := by
  intro i
  induction i with
  | Short x => rfl
  | Long mn i ih => simp only [id_to_mods, id_to_n, mk_id, ih]

/- HOL4: (!id x. P id x ⇒ Q id x) ⇒ nsAll P e ⇒ nsAll Q e -/
theorem nsAll_mono (P Q : id M N → V → Prop) (e : «namespace» M N V) :
    (∀ i x, P i x → Q i x) → nsAll P e → nsAll Q e := by
  intro h hP i x hx
  exact h i x (hP i x hx)

/- HOL4: (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2) -/
theorem nsSub_mono (R1 R2 : id M N → A → B → Prop) (e1 : «namespace» M N A)
    (e2 : «namespace» M N B) :
    (∀ x y z, R1 x y z → R2 x y z) → (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  rintro h ⟨h1, h2⟩
  refine ⟨fun i v1 hv => ?_, h2⟩
  obtain ⟨v2, hv2, hr⟩ := h1 i v1 hv
  exact ⟨v2, hv2, h _ _ _ hr⟩

/- HOL4: (!x y z. nsLookup e1 x = SOME y ∧ nsLookup e2 x = SOME z ∧ R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2) -/
theorem nsSub_mono2 (R1 R2 : id M N → A → B → Prop) (e1 : «namespace» M N A)
    (e2 : «namespace» M N B) :
    (∀ x y z, nsLookup e1 x = some y ∧ nsLookup e2 x = some z ∧ R1 x y z → R2 x y z) →
      (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  rintro h ⟨h1, h2⟩
  refine ⟨fun i v1 hv => ?_, h2⟩
  obtain ⟨v2, hv2, hr⟩ := h1 i v1 hv
  exact ⟨v2, hv2, h _ _ _ ⟨hv, hv2, hr⟩⟩

/- HOL4: (!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2 -/
theorem nsAll2_mono (R1 R2 : id M N → A → B → Prop) (e1 : «namespace» M N A)
    (e2 : «namespace» M N B) :
    (∀ x y z, R1 x y z → R2 x y z) → nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  rintro h ⟨h1, h2⟩
  exact ⟨nsSub_mono R1 R2 e1 e2 h h1, nsSub_mono _ _ e2 e1 (fun x y z => h x z y) h2⟩

/- HOL4: !id. nsLookup nsEmpty id = NONE -/
theorem nsLookup_nsEmpty : ∀ (i : id M N), nsLookup (nsEmpty : «namespace» M N V) i = none := by
  intro i
  cases i <;> simp [nsEmpty, Aux.nsLookup_short, Aux.nsLookup_long, Aux.ALOOKUP_nil']

/- HOL4: !x y. nsLookupMod nsEmpty (x::y) = NONE -/
theorem nsLookupMod_nsEmpty :
    ∀ (x : M) (y : List M), nsLookupMod (nsEmpty : «namespace» M N V) (x :: y) = none := by
  intro x y
  exact Aux.nsLookupMod_Bind_nil_cons [] x y

/- HOL4: nsOpen [] env = NONE -/
theorem nsOpen_nil (env : «namespace» M N V) : nsOpen [] env = none := by
  simp [nsOpen]

/- HOL4: nsOpen (mn::path) env = nsLookupMod env (mn::path) -/
theorem nsOpen_cons (mn : M) (path : List M) (env : «namespace» M N V) :
    nsOpen (mn :: path) env = nsLookupMod env (mn :: path) := by
  simp [nsOpen]

/- HOL4: nsOpen path env = SOME opened ⇔
   path ≠ [] ∧ nsLookupMod env path = SOME opened -/
theorem nsOpen_eq_some (path : List M) (env opened : «namespace» M N V) :
    nsOpen path env = some opened ↔ path ≠ [] ∧ nsLookupMod env path = some opened := by
  exact Aux.nsOpen_eq_some_iff path env opened

/- HOL4: nsLookupMod env (path ++ suffix) =
   case nsLookupMod env path of
   | NONE => NONE
   | SOME opened => nsLookupMod opened suffix -/
theorem nsLookupMod_append (env : «namespace» M N V) (path suffix : List M) :
    nsLookupMod env (path ++ suffix) =
      match nsLookupMod env path with
      | none => none
      | some opened => nsLookupMod opened suffix := by
  induction path generalizing env with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a p ih =>
    obtain ⟨vs, ms⟩ := env
    rw [List.cons_append, Aux.nsLookupMod_cons, Aux.nsLookupMod_cons]
    cases ALOOKUP ms a with
    | none => rfl
    | some e => exact ih e

/- HOL4: ∀env path opened id.
   nsLookupMod env path = SOME opened ⇒
   nsLookup env (mk_id (path ++ id_to_mods id) (id_to_n id)) =
     nsLookup opened id -/
theorem nsLookup_after_nsLookupMod :
    ∀ (env : «namespace» M N V) (path : List M) (opened : «namespace» M N V) (i : id M N),
      nsLookupMod env path = some opened →
      nsLookup env (mk_id (path ++ id_to_mods i) (id_to_n i)) = nsLookup opened i := by
  intro env path
  induction path generalizing env with
  | nil =>
    intro opened i h
    rw [Aux.nsLookupMod_nil] at h
    cases h
    rw [List.nil_append, mk_id_thm]
  | cons a p ih =>
    intro opened i h
    obtain ⟨vs, ms⟩ := env
    rw [Aux.nsLookupMod_cons] at h
    show nsLookup (Bind vs ms) (Long a (mk_id (p ++ id_to_mods i) (id_to_n i))) = _
    rw [Aux.nsLookup_long]
    cases hA : ALOOKUP ms a with
    | none => rw [hA] at h; simp at h
    | some e => rw [hA] at h; exact ih e opened i h

/- HOL4: nsLookupMod env path = SOME opened ⇒
   nsLookupMod opened suffix = nsLookupMod env (path ++ suffix) -/
theorem nsLookupMod_after_nsLookupMod (env opened : «namespace» M N V) (path suffix : List M) :
    nsLookupMod env path = some opened →
      nsLookupMod opened suffix = nsLookupMod env (path ++ suffix) := by
  intro h
  simp [nsLookupMod_append, h]

/- HOL4: nsLookupMod env path = SOME opened ∧ nsAll P env ⇒
   nsAll
     (λid v. P (mk_id (path ++ id_to_mods id) (id_to_n id)) v)
     opened -/
theorem nsAll_after_nsLookupMod (env opened : «namespace» M N V) (path : List M)
    (P : id M N → V → Prop) :
    nsLookupMod env path = some opened ∧ nsAll P env →
      nsAll (fun i v => P (mk_id (path ++ id_to_mods i) (id_to_n i)) v) opened := by
  rintro ⟨h, hP⟩ i x hx
  apply hP
  rw [nsLookup_after_nsLookupMod env path opened i h]
  exact hx

/- HOL4: nsOpen path env = SOME opened ⇒
   nsLookup opened id =
     nsLookup env (mk_id (path ++ id_to_mods id) (id_to_n id)) -/
theorem nsLookup_after_nsOpen (path : List M) (env opened : «namespace» M N V) (i : id M N) :
    nsOpen path env = some opened →
      nsLookup opened i = nsLookup env (mk_id (path ++ id_to_mods i) (id_to_n i)) := by
  intro h
  exact (nsLookup_after_nsLookupMod env path opened i ((nsOpen_eq_some path env opened).mp h).2).symm

/- HOL4: nsOpen path env = SOME opened ⇒
   nsLookupMod opened suffix = nsLookupMod env (path ++ suffix) -/
theorem nsLookupMod_after_nsOpen (path suffix : List M) (env opened : «namespace» M N V) :
    nsOpen path env = some opened →
      nsLookupMod opened suffix = nsLookupMod env (path ++ suffix) := by
  intro h
  exact nsLookupMod_after_nsLookupMod env opened path suffix ((nsOpen_eq_some path env opened).mp h).2

/- HOL4: nsOpen path env = SOME opened ∧ nsAll P env ⇒
   nsAll
     (λid v. P (mk_id (path ++ id_to_mods id) (id_to_n id)) v)
     opened -/
theorem nsAll_after_nsOpen (path : List M) (env opened : «namespace» M N V)
    (P : id M N → V → Prop) :
    nsOpen path env = some opened ∧ nsAll P env →
      nsAll (fun i v => P (mk_id (path ++ id_to_mods i) (id_to_n i)) v) opened := by
  rintro ⟨h, hP⟩
  exact nsAll_after_nsLookupMod env opened path P ⟨((nsOpen_eq_some path env opened).mp h).2, hP⟩

/- HOL4: nsOpen path env1 = SOME opened1 ∧
   (∀p. nsLookupMod env1 p = NONE ⇔ nsLookupMod env2 p = NONE) ⇒
   ∃opened2. nsOpen path env2 = SOME opened2 -/
theorem nsOpen_some_from_same_mod_domain {N₂ : Type _} {V₂ : Type _} (path : List M)
    (env1 opened1 : «namespace» M N V) (env2 : «namespace» M N₂ V₂) :
    nsOpen path env1 = some opened1 ∧
      (∀ p, nsLookupMod env1 p = none ↔ nsLookupMod env2 p = none) →
      ∃ opened2, nsOpen path env2 = some opened2 := by
  rintro ⟨h, hd⟩
  obtain ⟨hne, hm⟩ := (Aux.nsOpen_eq_some_iff path env1 opened1).mp h
  cases h2 : nsLookupMod env2 path with
  | none =>
    have h3 := (hd path).mpr h2
    rw [hm] at h3
    cases h3
  | some o => exact ⟨o, (Aux.nsOpen_eq_some_iff path env2 o).mpr ⟨hne, h2⟩⟩

/- HOL4: nsAll2 R env1 env2 ∧ nsOpen path env1 = SOME opened1 ⇒
   ∃opened2.
     nsOpen path env2 = SOME opened2 ∧
     nsAll2
       (λid. R (mk_id (path ++ id_to_mods id) (id_to_n id)))
       opened1 opened2 -/
theorem nsAll2_after_nsOpen (R : id M N → A → B → Prop) (env1 opened1 : «namespace» M N A)
    (env2 : «namespace» M N B) (path : List M) :
    nsAll2 R env1 env2 ∧ nsOpen path env1 = some opened1 →
      ∃ opened2,
        nsOpen path env2 = some opened2 ∧
        nsAll2 (fun i => R (mk_id (path ++ id_to_mods i) (id_to_n i))) opened1 opened2 := by
  rintro ⟨⟨⟨hs1a, hs1b⟩, ⟨hs2a, hs2b⟩⟩, h⟩
  obtain ⟨hne, hm⟩ := (nsOpen_eq_some path env1 opened1).mp h
  cases h2 : nsLookupMod env2 path with
  | none =>
    have h3 := hs1b path h2
    rw [hm] at h3
    cases h3
  | some o =>
    refine ⟨o, (nsOpen_eq_some path env2 o).mpr ⟨hne, h2⟩, ?_⟩
    unfold nsAll2 nsSub
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i v1 hv
      rw [← nsLookup_after_nsLookupMod env1 path opened1 i hm] at hv
      obtain ⟨v2, hv2, hr⟩ := hs1a _ v1 hv
      exact ⟨v2, by rw [← nsLookup_after_nsLookupMod env2 path o i h2]; exact hv2, hr⟩
    · intro p hp
      rw [nsLookupMod_after_nsLookupMod env2 o path p h2] at hp
      rw [nsLookupMod_after_nsLookupMod env1 opened1 path p hm]
      exact hs1b _ hp
    · intro i v2 hv
      rw [← nsLookup_after_nsLookupMod env2 path o i h2] at hv
      obtain ⟨v1, hv1, hr⟩ := hs2a _ v2 hv
      exact ⟨v1, by rw [← nsLookup_after_nsLookupMod env1 path opened1 i hm]; exact hv1, hr⟩
    · intro p hp
      rw [nsLookupMod_after_nsLookupMod env1 opened1 path p hm] at hp
      rw [nsLookupMod_after_nsLookupMod env2 o path p h2]
      exact hs2b _ hp

/- HOL4: nsAll2 R env1 env2 ⇒ nsAll2 (λid y x. R id x y) env2 env1 -/
theorem nsAll2_flip (R : id M N → A → B → Prop) (env1 : «namespace» M N A)
    (env2 : «namespace» M N B) :
    nsAll2 R env1 env2 → nsAll2 (fun i y x => R i x y) env2 env1 := by
  rintro ⟨h1, h2⟩
  exact ⟨h2, h1⟩

/- HOL4: nsAll2 R env1 env2 ∧ nsOpen path env2 = SOME opened2 ⇒
   ∃opened1.
     nsOpen path env1 = SOME opened1 ∧
     nsAll2
       (λid. R (mk_id (path ++ id_to_mods id) (id_to_n id)))
       opened1 opened2 -/
theorem nsAll2_before_nsOpen (R : id M N → A → B → Prop) (env1 : «namespace» M N A)
    (env2 opened2 : «namespace» M N B) (path : List M) :
    nsAll2 R env1 env2 ∧ nsOpen path env2 = some opened2 →
      ∃ opened1,
        nsOpen path env1 = some opened1 ∧
        nsAll2 (fun i => R (mk_id (path ++ id_to_mods i) (id_to_n i))) opened1 opened2 := by
  rintro ⟨h, ho⟩
  obtain ⟨o1, h1, h2⟩ :=
    nsAll2_after_nsOpen (fun i y x => R i x y) env2 opened2 env1 path ⟨nsAll2_flip R env1 env2 h, ho⟩
  exact ⟨o1, h1, nsAll2_flip _ _ _ h2⟩

/- HOL4: !env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env -/
theorem nsAppend_nsEmpty :
    ∀ (env : «namespace» M N V), nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  intro env
  obtain ⟨vs, ms⟩ := env
  simp [nsEmpty, Aux.nsAppend_Bind]

/- HOL4: alist_to_ns [] = nsEmpty -/
theorem alist_to_ns_nil : alist_to_ns ([] : List (N × V)) = (nsEmpty : «namespace» M N V) := by
  rfl

/- HOL4: !r env. nsSub r nsEmpty env -/
theorem nsSub_nsEmpty :
    ∀ (r : id M N → A → B → Prop) (env : «namespace» M N B), nsSub r nsEmpty env := by
  intro r env
  refine ⟨fun i v1 h => ?_, fun p hp => ?_⟩
  · rw [nsLookup_nsEmpty] at h
    cases h
  · cases p with
    | nil => rw [Aux.nsLookupMod_nil] at hp; cases hp
    | cons a q => exact nsLookupMod_nsEmpty a q

/- HOL4: !f. nsAll f nsEmpty -/
theorem nsAll_nsEmpty : ∀ (f : id M N → V → Prop), nsAll f nsEmpty := by
  intro f i x h
  rw [nsLookup_nsEmpty] at h
  cases h

/- HOL4: !f. nsAll2 f nsEmpty nsEmpty -/
theorem nsAll2_nsEmpty : ∀ (f : id M N → A → B → Prop), nsAll2 f nsEmpty nsEmpty := by
  intro f
  exact ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩

/- HOL4: nsDom nsEmpty = {} -/
theorem nsDom_nsEmpty : nsDom (nsEmpty : «namespace» M N V) = ∅ := by
  apply Aux.set_ext
  intro i
  simp [Aux.mem_nsDom, Aux.mem_empty, nsLookup_nsEmpty]

/- HOL4: nsDomMod nsEmpty = {[]} -/
theorem nsDomMod_nsEmpty : nsDomMod (nsEmpty : «namespace» M N V) = {[]} := by
  apply Aux.set_ext
  intro p
  rw [Aux.mem_nsDomMod, Aux.mem_singleton]
  cases p with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a q => simp [nsLookupMod_nsEmpty]

/- HOL4: !f. nsMap f nsEmpty = nsEmpty -/
theorem nsMap_nsEmpty :
    ∀ (f : V → W), nsMap f (nsEmpty : «namespace» M N V) = nsEmpty := by
  intro f
  simp [nsEmpty, Aux.nsMap_Bind]

/- HOL4: !x y env. nsBind x y env ≠ nsEmpty -/
theorem nsBind_nsEmpty :
    ∀ (x : N) (y : V) (env : «namespace» M N V), nsBind x y env ≠ nsEmpty := by
  intro x y env
  obtain ⟨vs, ms⟩ := env
  simp [nsBind, nsEmpty]

/- HOL4: nsLookup (Bind v []) k = SOME x ⇔
   ∃y. k = Short y ∧ ALOOKUP v y = SOME x -/
theorem nsLookup_Bind_v_some (v : List (N × V)) (k : id M N) (x : V) :
    nsLookup (Bind v [] : «namespace» M N V) k = some x ↔
      ∃ y, k = Short y ∧ ALOOKUP v y = some x := by
  cases k with
  | Short y => simp [Aux.nsLookup_short]
  | Long a j => simp [Aux.nsLookup_long, Aux.ALOOKUP_nil']

/- HOL4: !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l) -/
theorem alist_to_ns_cons :
    ∀ (k : N) (v : V) (l : List (N × V)),
      (alist_to_ns ((k, v) :: l) : «namespace» M N V) = nsBind k v (alist_to_ns l) := by
  intro k v l
  rfl

/- HOL4: !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) -/
theorem nsAppend_nsBind :
    ∀ (k : N) (v : V) (e1 e2 : «namespace» M N V),
      nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) := by
  intro k v e1 e2
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  simp [nsBind, Aux.nsAppend_Bind]

/- HOL4: !al1 al2. nsAppend (alist_to_ns al1) (alist_to_ns al2) = alist_to_ns (al1 ++ al2) -/
theorem nsAppend_alist_to_ns :
    ∀ (al1 al2 : List (N × V)),
      nsAppend (alist_to_ns al1 : «namespace» M N V) (alist_to_ns al2) = alist_to_ns (al1 ++ al2) := by
  intro al1 al2
  simp [alist_to_ns, Aux.nsAppend_Bind]

/- HOL4: !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 -/
theorem nsAppend_assoc :
    ∀ (e1 e2 e3 : «namespace» M N V),
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  intro e1 e2 e3
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  obtain ⟨v3, m3⟩ := e3
  simp [Aux.nsAppend_Bind]

/- HOL4: (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
   Lean: the two conjuncts have independent type variables (HOL4 has 6). -/
theorem nsLookup_nsBind {M₁ : Type _} {N₁ : Type _} {V₁ : Type _}
    {M₂ : Type _} {N₂ : Type _} {V₂ : Type _}
    [DecidableEq M₁] [DecidableEq N₁] [DecidableEq M₂] [DecidableEq N₂] :
    (∀ (n : N₁) (v : V₁) (e : «namespace» M₁ N₁ V₁), nsLookup (nsBind n v e) (Short n) = some v) ∧
    (∀ (n : id M₂ N₂) (n' : N₂) (v : V₂) (e : «namespace» M₂ N₂ V₂),
      n ≠ Short n' → nsLookup (nsBind n' v e) n = nsLookup e n) := by
  exact ⟨fun n v e => Aux.nsLookup_nsBind_short n v e,
    fun n n' v e h => Aux.nsLookup_nsBind_ne n n' v e h⟩

/- HOL4: !n x e. nsAppend (nsSing n x) e = nsBind n x e -/
theorem nsAppend_nsSing :
    ∀ (n : N) (x : V) (e : «namespace» M N V), nsAppend (nsSing n x) e = nsBind n x e := by
  intro n x e
  obtain ⟨vs, ms⟩ := e
  simp [nsSing, nsBind, Aux.nsAppend_Bind]

/- HOL4: !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE -/
theorem nsLookup_nsSing :
    ∀ (n : N) (v : V) (i : id M N),
      nsLookup (nsSing n v) i = if i = Short n then some v else none := by
  intro n v i
  cases i with
  | Short x =>
    by_cases h : n = x
    · subst h
      simp [nsSing, Aux.nsLookup_short, Aux.ALOOKUP_cons']
    · have h' : x ≠ n := fun hh => h hh.symm
      simp [nsSing, Aux.nsLookup_short, Aux.ALOOKUP_cons', Aux.ALOOKUP_nil', h, h']
  | Long a j => simp [nsSing, Aux.nsLookup_long, Aux.ALOOKUP_nil']

/- HOL4: !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v -/
theorem nsAll_nsSing :
    ∀ (R : id M N → V → Prop) (n : N) (v : V), nsAll R (nsSing n v) ↔ R (Short n) v := by
  intro R n v
  constructor
  · intro h
    exact h (Short n) v (by rw [nsLookup_nsSing, if_pos rfl])
  · intro h i x hx
    rw [nsLookup_nsSing] at hx
    by_cases hi : i = Short n
    · rw [if_pos hi] at hx
      cases hx
      subst hi
      exact h
    · rw [if_neg hi] at hx
      cases hx

/- HOL4: !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2 -/
theorem nsAll2_nsSing :
    ∀ (R : id M N → A → B → Prop) (n1 : N) (v1 : A) (n2 : N) (v2 : B),
      nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ↔ n1 = n2 ∧ R (Short n1) v1 v2 := by
  intro R n1 v1 n2 v2
  constructor
  · rintro ⟨⟨h1, _⟩, _⟩
    obtain ⟨w, hw, hr⟩ := h1 (Short n1) v1 (by rw [nsLookup_nsSing, if_pos rfl])
    rw [nsLookup_nsSing] at hw
    by_cases hn : (Short n1 : id M N) = Short n2
    · rw [if_pos hn] at hw
      cases hw
      cases hn
      exact ⟨rfl, hr⟩
    · rw [if_neg hn] at hw
      cases hw
  · rintro ⟨rfl, hr⟩
    unfold nsAll2 nsSub
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i x hx
      rw [nsLookup_nsSing] at hx
      by_cases hi : i = Short n1
      · rw [if_pos hi] at hx
        cases hx
        subst hi
        exact ⟨v2, by rw [nsLookup_nsSing, if_pos rfl], hr⟩
      · rw [if_neg hi] at hx
        cases hx
    · intro p hp
      exact Aux.nsLookupMod_nsSing_none _ _ _ _ hp
    · intro i x hx
      rw [nsLookup_nsSing] at hx
      by_cases hi : i = Short n1
      · rw [if_pos hi] at hx
        cases hx
        subst hi
        exact ⟨v1, by rw [nsLookup_nsSing, if_pos rfl], hr⟩
      · rw [if_neg hi] at hx
        cases hx
    · intro p hp
      exact Aux.nsLookupMod_nsSing_none _ _ _ _ hp

/- HOL4: !f x v. nsMap f (nsSing x v) = nsSing x (f v) -/
theorem nsMap_nsSing :
    ∀ (f : V → W) (x : N) (v : V), nsMap f (nsSing x v : «namespace» M N V) = nsSing x (f v) := by
  intro f x v
  simp [nsSing, Aux.nsMap_Bind]

/- HOL4: !n1 n2 v. nsLookupMod (nsSing n2 v) n1 = if n1 = [] then SOME (nsSing n2 v) else NONE -/
theorem nsLookupMod_nsSing :
    ∀ (n1 : List M) (n2 : N) (v : V),
      nsLookupMod (nsSing n2 v) n1 = if n1 = [] then some (nsSing n2 v) else none := by
  intro n1 n2 v
  cases n1 with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a q => simp [nsSing, Aux.nsLookupMod_Bind_nil_cons]

/- HOL4: !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n' -/
theorem nsBind_11 :
    ∀ (x : N) (y : V) (n : «namespace» M N V) (x' : N) (y' : V) (n' : «namespace» M N V),
      nsBind x y n = nsBind x' y' n' ↔ x = x' ∧ y = y' ∧ n = n' := by
  intro x y n x' y' n'
  obtain ⟨vs, ms⟩ := n
  obtain ⟨vs', ms'⟩ := n'
  simp [nsBind, and_assoc]

/- HOL4: !x y n. nsDom (nsBind x y n) = Short x INSERT nsDom n -/
theorem nsDom_nsBind :
    ∀ (x : N) (y : V) (n : «namespace» M N V), nsDom (nsBind x y n) = insert (Short x) (nsDom n) := by
  intro x y n
  apply Aux.set_ext
  intro i
  rw [Aux.mem_insert, Aux.mem_nsDom, Aux.mem_nsDom]
  by_cases hi : i = Short x
  · subst hi
    simp [Aux.nsLookup_nsBind_short]
  · simp [Aux.nsLookup_nsBind_ne _ _ _ _ hi, hi]

/- HOL4: !x y. nsDom (nsSing x y) = {Short x} -/
theorem nsDom_nsSing :
    ∀ (x : N) (y : V), nsDom (nsSing x y : «namespace» M N V) = {Short x} := by
  intro x y
  have h := nsDom_nsBind x y (nsEmpty : «namespace» M N V)
  rw [nsDom_nsEmpty] at h
  exact h

/- HOL4: !x y n. nsDomMod (nsBind x y n) = nsDomMod n -/
theorem nsDomMod_nsBind :
    ∀ (x : N) (y : V) (n : «namespace» M N V), nsDomMod (nsBind x y n) = nsDomMod n := by
  intro x y n
  apply Aux.set_ext
  intro p
  obtain ⟨vs, ms⟩ := n
  rw [Aux.mem_nsDomMod, Aux.mem_nsDomMod]
  cases p with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a q => simp [nsBind, Aux.nsLookupMod_cons]

/- HOL4: !x y. nsDomMod (nsSing x y) = {[]} -/
theorem nsDomMod_nsSing :
    ∀ (x : N) (y : V), nsDomMod (nsSing x y : «namespace» M N V) = {[]} := by
  intro x y
  have h := nsDomMod_nsBind x y (nsEmpty : «namespace» M N V)
  rw [nsDomMod_nsEmpty] at h
  exact h

/- HOL4: !l x y. nsLookupMod (alist_to_ns l) (x::y) = NONE -/
theorem nsLookupMod_alist_to_ns :
    ∀ (l : List (N × V)) (x : M) (y : List M), nsLookupMod (alist_to_ns l) (x :: y) = none := by
  intro l x y
  exact Aux.nsLookupMod_Bind_nil_cons l x y

/- HOL4: !l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2 -/
theorem alist_to_ns_11 :
    ∀ (l1 l2 : List (N × V)), (alist_to_ns l1 : «namespace» M N V) = alist_to_ns l2 ↔ l1 = l2 := by
  intro l1 l2
  simp [alist_to_ns]

/- HOL4: !n v t.
    nsLookup n v = SOME t
    ⇒
    ?m. nsLookupMod n (id_to_mods v) = SOME m ∧ nsLookup m (Short (id_to_n v)) = SOME t -/
theorem nsLookup_to_nsLookupMod :
    ∀ (n : «namespace» M N V) (v : id M N) (t : V),
      nsLookup n v = some t →
      ∃ m, nsLookupMod n (id_to_mods v) = some m ∧ nsLookup m (Short (id_to_n v)) = some t := by
  intro n v t
  induction v generalizing n with
  | Short x => intro h; exact ⟨n, Aux.nsLookupMod_nil n, h⟩
  | Long a j ih =>
    intro h
    obtain ⟨vs, ms⟩ := n
    rw [Aux.nsLookup_long] at h
    cases hA : ALOOKUP ms a with
    | none => rw [hA] at h; simp at h
    | some e =>
      rw [hA] at h
      obtain ⟨m', h1, h2⟩ := ih e h
      refine ⟨m', ?_, h2⟩
      show nsLookupMod (Bind vs ms) (a :: id_to_mods j) = _
      rw [Aux.nsLookupMod_cons, hA]
      exact h1

/- HOL4: !l id v. nsLookup (alist_to_ns l) id = SOME v ⇔ ?x'. id = Short x' ∧ ALOOKUP l x' = SOME v -/
theorem nsLookup_alist_to_ns_some :
    ∀ (l : List (N × V)) (i : id M N) (v : V),
      nsLookup (alist_to_ns l) i = some v ↔ ∃ x', i = Short x' ∧ ALOOKUP l x' = some v := by
  intro l i v
  exact nsLookup_Bind_v_some l i v

/- HOL4: !l id. nsLookup (alist_to_ns l) id = NONE ⇔ !x'. id = Short x' ⇒ ALOOKUP l x' = NONE -/
theorem nsLookup_alist_to_ns_none :
    ∀ (l : List (N × V)) (i : id M N),
      nsLookup (alist_to_ns l) i = none ↔ ∀ x', i = Short x' → ALOOKUP l x' = none := by
  intro l i
  cases i with
  | Short y => simp [alist_to_ns, Aux.nsLookup_short]
  | Long a j => simp [alist_to_ns, Aux.nsLookup_long, Aux.ALOOKUP_nil']

/- HOL4: !l. nsDom (alist_to_ns l) = set (MAP (Short o FST) l) -/
theorem nsDom_alist_to_ns :
    ∀ (l : List (N × V)),
      nsDom (alist_to_ns l : «namespace» M N V) =
        list.LIST_TO_SET (List.map ((Short : N → id M N) ∘ Prod.fst) l) := by
  intro l
  apply Aux.set_ext
  intro i
  rw [Aux.mem_nsDom, Aux.mem_LIST_TO_SET]
  cases i with
  | Short x =>
    rw [alist_to_ns, Aux.nsLookup_short]
    simp only [Aux.ALOOKUP_isSome_iff]
    simp [List.mem_map]
  | Long a j => simp [alist_to_ns, Aux.nsLookup_long, Aux.ALOOKUP_nil', List.mem_map]

/- HOL4: !mn e id.
    nsLookup (nsLift mn e) id =
    case id of
    | Long mn' id' =>
      if mn = mn' then
        nsLookup e id'
      else
        NONE
    | Short _ => NONE -/
theorem nsLookup_nsLift :
    ∀ (mn : M) (e : «namespace» M N V) (i : id M N),
      nsLookup (nsLift mn e) i =
        match i with
        | Long mn' i' => if mn = mn' then nsLookup e i' else none
        | Short _ => none := by
  intro mn e i
  cases i with
  | Short x => simp [nsLift, Aux.nsLookup_short, Aux.ALOOKUP_nil']
  | Long a j =>
    simp only [nsLift, Aux.nsLookup_long, Aux.ALOOKUP_cons']
    by_cases h : mn = a <;> simp [h, Aux.ALOOKUP_nil']

/- HOL4: !mn e path.
    nsLookupMod (nsLift mn e) path =
    case path of
    | [] => SOME (nsLift mn e)
    | (mn'::path') =>
      if mn = mn' then
        nsLookupMod e path'
      else
        NONE -/
theorem nsLookupMod_nsLift :
    ∀ (mn : M) (e : «namespace» M N V) (path : List M),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn = mn' then nsLookupMod e path' else none := by
  intro mn e path
  cases path with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a q =>
    simp only [nsLift, Aux.nsLookupMod_cons, Aux.ALOOKUP_cons']
    by_cases h : mn = a <;> simp [h, Aux.ALOOKUP_nil']

/- HOL4: !m ns ns' m' id n.
   nsLookup (nsAppend (nsLift m ns) ns') (Short n) = nsLookup ns' (Short n) ∧
   nsLookup (nsAppend (nsLift m ns) ns') (Long m' id) =
     if m = m' then nsLookup ns id else nsLookup ns' (Long m' id) -/
theorem nsLookup_nsLift_append :
    ∀ (m : M) (ns ns' : «namespace» M N V) (m' : M) (i : id M N) (n : N),
      nsLookup (nsAppend (nsLift m ns) ns') (Short n) = nsLookup ns' (Short n) ∧
      nsLookup (nsAppend (nsLift m ns) ns') (Long m' i) =
        if m = m' then nsLookup ns i else nsLookup ns' (Long m' i) := by
  intro m ns ns' m' i n
  obtain ⟨vs, ms⟩ := ns'
  constructor
  · simp [nsLift, Aux.nsAppend_Bind, Aux.nsLookup_short]
  · simp only [nsLift, Aux.nsAppend_Bind, List.nil_append, List.singleton_append,
      Aux.nsLookup_long, Aux.ALOOKUP_cons']
    by_cases h : m = m' <;> simp [h]

/- HOL4: ∀e1 id e2.
    nsLookup (nsAppend e1 e2) id = NONE
    ⇔
    (nsLookup e1 id = NONE ∧
     (nsLookup e2 id = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ id_to_mods id = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3)) -/
theorem nsLookup_nsAppend_none :
    ∀ (e1 : «namespace» M N V) (i : id M N) (e2 : «namespace» M N V),
      nsLookup (nsAppend e1 e2) i = none ↔
        (nsLookup e1 i = none ∧
          (nsLookup e2 i = none ∨
            ∃ p1 p2 e3, p1 ≠ [] ∧ id_to_mods i = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  intro e1 i e2
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  rw [Aux.nsAppend_Bind]
  cases i with
  | Short x =>
    simp only [Aux.nsLookup_short, id_to_mods]
    cases h1 : ALOOKUP v1 x with
    | some w => rw [Aux.ALOOKUP_append_some _ _ _ _ h1]; simp
    | none =>
      rw [Aux.ALOOKUP_append_none _ _ _ h1]
      constructor
      · intro h; exact ⟨rfl, Or.inl h⟩
      · rintro ⟨_, h | ⟨p1, p2, e3, hp1, hp2, _⟩⟩
        · exact h
        · exact absurd ⟨hp1, hp2⟩ Aux.nil_ne_prefix
  | Long a j =>
    simp only [Aux.nsLookup_long, id_to_mods]
    cases h1 : ALOOKUP m1 a with
    | some e =>
      rw [Aux.ALOOKUP_append_some _ _ _ _ h1]
      constructor
      · intro h; exact ⟨h, Or.inr (Aux.prefix_some (vs := v1) h1 _)⟩
      · rintro ⟨h, _⟩; exact h
    | none =>
      rw [Aux.ALOOKUP_append_none _ _ _ h1]
      constructor
      · intro h; exact ⟨rfl, Or.inl h⟩
      · rintro ⟨_, h | ⟨p1, p2, e3, hp1, hp2, hp3⟩⟩
        · exact h
        · rw [Aux.prefix_none (vs := v1) h1 _ p1 p2 ⟨hp1, hp2⟩] at hp3
          cases hp3

/- HOL4: ∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
     !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE) -/
theorem nsLookup_nsAppend_some :
    ∀ (e1 : «namespace» M N V) (i : id M N) (e2 : «namespace» M N V) (v : V),
      nsLookup (nsAppend e1 e2) i = some v ↔
        nsLookup e1 i = some v ∨
        (nsLookup e1 i = none ∧ nsLookup e2 i = some v ∧
          ∀ p1 p2, p1 ≠ [] ∧ id_to_mods i = p1 ++ p2 → nsLookupMod e1 p1 = none) := by
  intro e1 i e2 v
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  rw [Aux.nsAppend_Bind]
  cases i with
  | Short x =>
    simp only [Aux.nsLookup_short, id_to_mods]
    cases h1 : ALOOKUP v1 x with
    | some w => rw [Aux.ALOOKUP_append_some _ _ _ _ h1]; simp
    | none =>
      rw [Aux.ALOOKUP_append_none _ _ _ h1]
      constructor
      · intro h; exact Or.inr ⟨rfl, h, fun p1 p2 hp => absurd hp Aux.nil_ne_prefix⟩
      · rintro (h | ⟨_, h, _⟩)
        · cases h
        · exact h
  | Long a j =>
    simp only [Aux.nsLookup_long, id_to_mods]
    cases h1 : ALOOKUP m1 a with
    | some e =>
      rw [Aux.ALOOKUP_append_some _ _ _ _ h1]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨_, _, hall⟩)
        · exact h
        · obtain ⟨p1, p2, e3, hp1, hp2, hp3⟩ := Aux.prefix_some (vs := v1) h1 (id_to_mods j)
          rw [hall p1 p2 ⟨hp1, hp2⟩] at hp3
          cases hp3
    | none =>
      rw [Aux.ALOOKUP_append_none _ _ _ h1]
      constructor
      · intro h; exact Or.inr ⟨rfl, h, Aux.prefix_none (vs := v1) h1 _⟩
      · rintro (h | ⟨_, h, _⟩)
        · simp at h
        · exact h

/- HOL4: !l. nsAppend (alist_to_ns l) e = nsBindList l e -/
theorem nsAppend_to_nsBindList (e : «namespace» M N V) :
    ∀ (l : List (N × V)), nsAppend (alist_to_ns l) e = nsBindList l e := by
  intro l
  obtain ⟨vs, ms⟩ := e
  rw [Aux.nsBindList_Bind, alist_to_ns, Aux.nsAppend_Bind, List.nil_append]

/- HOL4: !e1 e2 path.
    nsLookupMod (nsAppend e1 e2) path = NONE
    ⇔
    (nsLookupMod e1 path = NONE ∧
     (nsLookupMod e2 path = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3)) -/
theorem nsLookupMod_nsAppend_none :
    ∀ (e1 e2 : «namespace» M N V) (path : List M),
      nsLookupMod (nsAppend e1 e2) path = none ↔
        (nsLookupMod e1 path = none ∧
          (nsLookupMod e2 path = none ∨
            ∃ p1 p2 e3, p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  intro e1 e2 path
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  rw [Aux.nsAppend_Bind]
  cases path with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a p =>
    simp only [Aux.nsLookupMod_cons]
    cases h1 : ALOOKUP m1 a with
    | some e =>
      rw [Aux.ALOOKUP_append_some _ _ _ _ h1]
      constructor
      · intro h; exact ⟨h, Or.inr (Aux.prefix_some (vs := v1) h1 p)⟩
      · rintro ⟨h, _⟩; exact h
    | none =>
      rw [Aux.ALOOKUP_append_none _ _ _ h1]
      constructor
      · intro h; exact ⟨rfl, Or.inl h⟩
      · rintro ⟨_, h | ⟨p1, p2, e3, hp1, hp2, hp3⟩⟩
        · exact h
        · rw [Aux.prefix_none (vs := v1) h1 p p1 p2 ⟨hp1, hp2⟩] at hp3
          cases hp3

/- HOL4: !e1 e2 path.
    (nsLookupMod (nsAppend e1 e2) path = SOME x
     ⇔
     if path = [] then x = nsAppend e1 e2 else
     nsLookupMod e1 path = SOME x ∨
      (nsLookupMod e2 path = SOME x ∧
      !p1 p2. p1 ≠ [] ∧ path = p1++p2 ⇒ nsLookupMod e1 p1 = NONE)) -/
theorem nsLookupMod_nsAppend_some (x : «namespace» M N V) :
    ∀ (e1 e2 : «namespace» M N V) (path : List M),
      (nsLookupMod (nsAppend e1 e2) path = some x ↔
        if path = [] then x = nsAppend e1 e2 else
          nsLookupMod e1 path = some x ∨
          (nsLookupMod e2 path = some x ∧
            ∀ p1 p2, p1 ≠ [] ∧ path = p1 ++ p2 → nsLookupMod e1 p1 = none)) := by
  intro e1 e2 path
  obtain ⟨v1, m1⟩ := e1
  obtain ⟨v2, m2⟩ := e2
  rw [Aux.nsAppend_Bind]
  cases path with
  | nil =>
    rw [if_pos rfl, Aux.nsLookupMod_nil]
    exact ⟨fun h => (Option.some.inj h).symm, fun h => by rw [h]⟩
  | cons a p =>
    rw [if_neg (show a :: p ≠ [] by simp)]
    simp only [Aux.nsLookupMod_cons]
    cases h1 : ALOOKUP m1 a with
    | some e =>
      rw [Aux.ALOOKUP_append_some _ _ _ _ h1]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨_, hall⟩)
        · exact h
        · obtain ⟨p1, p2, e3, hp1, hp2, hp3⟩ := Aux.prefix_some (vs := v1) h1 p
          rw [hall p1 p2 ⟨hp1, hp2⟩] at hp3
          cases hp3
    | none =>
      rw [Aux.ALOOKUP_append_none _ _ _ h1]
      constructor
      · intro h; exact Or.inr ⟨h, Aux.prefix_none (vs := v1) h1 p⟩
      · rintro (h | ⟨h, _⟩)
        · simp at h
        · exact h

/- HOL4: !x y. nsDom (nsAppend (alist_to_ns x) y) = set (MAP (Short o FST) x) ∪ nsDom y -/
theorem nsDom_nsAppend_alist :
    ∀ (x : List (N × V)) (y : «namespace» M N V),
      nsDom (nsAppend (alist_to_ns x) y) =
        list.LIST_TO_SET (List.map ((Short : N → id M N) ∘ Prod.fst) x) ∪ nsDom y := by
  intro x y
  obtain ⟨yv, ym⟩ := y
  apply Aux.set_ext
  intro i
  rw [Aux.mem_union, Aux.mem_nsDom, Aux.mem_nsDom, Aux.mem_LIST_TO_SET, alist_to_ns,
    Aux.nsAppend_Bind, List.nil_append]
  cases i with
  | Short z =>
    simp only [Aux.nsLookup_short, Aux.ALOOKUP_isSome_iff]
    simp [List.mem_map]
  | Long a j => simp [Aux.nsLookup_long, List.mem_map]

/- HOL4: !e. nsAll (\n x. T) e -/
theorem eALL_T : ∀ (e : «namespace» M N V), nsAll (fun _n _x => True) e := by
  intro e i x _
  trivial

/- HOL4: !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v -/
theorem nsLookup_nsAll :
    ∀ (env : «namespace» M N V) (x : id M N) (P : id M N → V → Prop) (v : V),
      nsAll P env ∧ nsLookup env x = some v → P x v := by
  rintro env x P v ⟨h1, h2⟩
  exact h1 x v h2

/- HOL4: !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2) -/
theorem nsAll_nsAppend :
    ∀ (f : id M N → V → Prop) (e1 e2 : «namespace» M N V),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  rintro f e1 e2 ⟨h1, h2⟩ i x hx
  rcases (nsLookup_nsAppend_some e1 i e2 x).mp hx with h | ⟨_, h, _⟩
  · exact h1 i x h
  · exact h2 i x h

/- HOL4: !P x v e. P (Short x) v ∧ nsAll P e ⇒ nsAll P (nsBind x v e) -/
theorem nsAll_nsBind :
    ∀ (P : id M N → V → Prop) (x : N) (v : V) (e : «namespace» M N V),
      P (Short x) v ∧ nsAll P e → nsAll P (nsBind x v e) := by
  rintro P x v e ⟨h1, h2⟩ i y hy
  by_cases hi : i = Short x
  · subst hi
    rw [Aux.nsLookup_nsBind_short] at hy
    cases hy
    exact h1
  · rw [Aux.nsLookup_nsBind_ne _ _ _ _ hi] at hy
    exact h2 i y hy

/- HOL4: !P x v e. (x = NONE ∨ ?n. x = SOME n ∧ P (Short n) v) ∧ nsAll P e ⇒ nsAll P (nsOptBind x v e) -/
theorem nsAll_nsOptBind :
    ∀ (P : id M N → V → Prop) (x : Option N) (v : V) (e : «namespace» M N V),
      (x = none ∨ ∃ n, x = some n ∧ P (Short n) v) ∧ nsAll P e → nsAll P (nsOptBind x v e) := by
  rintro P x v e ⟨hx, he⟩
  rcases hx with rfl | ⟨k, rfl, hk⟩
  · exact he
  · exact nsAll_nsBind P k v e ⟨hk, he⟩

/- HOL4: !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l) -/
theorem nsAll_alist_to_ns :
    ∀ (R : id M N → V → Prop) (l : List (N × V)),
      list.EVERY (fun (n, v) => R (Short n) v) l → nsAll R (alist_to_ns l) := by
  intro R l h i x hx
  obtain ⟨y, rfl, hy⟩ := (nsLookup_alist_to_ns_some l i x).mp hx
  exact (Aux.EVERY_iff _ l).mp h (y, x) (Aux.ALOOKUP_mem l y x hy)

/- HOL4: !R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e -/
theorem nsAll_nsLift :
    ∀ (R : id M N → V → Prop) (mn : M) (e : «namespace» M N V),
      nsAll R (nsLift mn e) ↔ nsAll (fun i => R (Long mn i)) e := by
  intro R mn e
  constructor
  · intro h i x hx
    exact h (Long mn i) x (by rw [nsLookup_nsLift]; simpa using hx)
  · intro h i x hx
    rw [nsLookup_nsLift] at hx
    cases i with
    | Short z => simp at hx
    | Long a j =>
      by_cases hm : mn = a
      · subst hm
        simp at hx
        exact h j x hx
      · simp [hm] at hx

/- HOL4: !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1 -/
theorem nsAll_nsAppend_left :
    ∀ (P : id M N → V → Prop) (n1 n2 : «namespace» M N V), nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  intro P n1 n2 h i x hx
  exact h i x ((nsLookup_nsAppend_some n1 i n2 x).mpr (Or.inl hx))

/- HOL4: !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2 -/
theorem nsSub_conj :
    ∀ (P Q : id M N → A → B → Prop) (e1 : «namespace» M N A) (e2 : «namespace» M N B),
      nsSub (fun i x y => P i x y ∧ Q i x y) e1 e2 ↔ nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  intro P Q e1 e2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i x hx => ?_, h2⟩, ⟨fun i x hx => ?_, h2⟩⟩
    · obtain ⟨y, hy, hp, _⟩ := h1 i x hx
      exact ⟨y, hy, hp⟩
    · obtain ⟨y, hy, _, hq⟩ := h1 i x hx
      exact ⟨y, hy, hq⟩
  · rintro ⟨⟨hp1, hp2⟩, ⟨hq1, _⟩⟩
    refine ⟨fun i x hx => ?_, hp2⟩
    obtain ⟨y, hy, hp⟩ := hp1 i x hx
    obtain ⟨y', hy', hq⟩ := hq1 i x hx
    rw [hy] at hy'
    cases hy'
    exact ⟨y, hy, hp, hq⟩

/- HOL4: !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e -/
theorem nsSub_refl :
    ∀ (P : id M N → V → Prop) (R : id M N → V → V → Prop),
      (∀ n x, P n x → R n x x) → ∀ (e : «namespace» M N V), nsAll P e → nsSub R e e := by
  intro P R hPR e hP
  exact ⟨fun i x hx => ⟨x, hx, hPR i x (hP i x hx)⟩, fun p hp => hp⟩

/- HOL4: !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsSub_nsBind :
    ∀ (R : id M N → A → B → Prop) (x : N) (v1 : A) (v2 : B) (e1 : «namespace» M N A)
      (e2 : «namespace» M N B),
      R (Short x) v1 v2 ∧ nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  rintro R x v1 v2 e1 e2 ⟨hr, h1, h2⟩
  refine ⟨fun i y hy => ?_, fun p hp => ?_⟩
  · by_cases hi : i = Short x
    · subst hi
      rw [Aux.nsLookup_nsBind_short] at hy
      cases hy
      exact ⟨v2, Aux.nsLookup_nsBind_short _ _ _, hr⟩
    · rw [Aux.nsLookup_nsBind_ne _ _ _ _ hi] at hy
      obtain ⟨z, hz, hr'⟩ := h1 i y hy
      exact ⟨z, by rw [Aux.nsLookup_nsBind_ne _ _ _ _ hi]; exact hz, hr'⟩
  · rw [Aux.nsLookupMod_nsBind_none] at hp ⊢
    exact h2 p hp

/- HOL4: !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2') -/
theorem nsSub_nsAppend2 :
    ∀ (R : id M N → V → V → Prop) (e1 e2 e2' : «namespace» M N V),
      nsSub R e1 e1 ∧ nsSub R e2 e2' → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  rintro R e1 e2 e2' ⟨⟨h11, _⟩, ⟨h21, h22⟩⟩
  refine ⟨fun i x hx => ?_, fun p hp => ?_⟩
  · rcases (nsLookup_nsAppend_some e1 i e2 x).mp hx with h | ⟨hn, h, hall⟩
    · obtain ⟨y, hy, hr⟩ := h11 i x h
      exact ⟨y, (nsLookup_nsAppend_some e1 i e2' y).mpr (Or.inl hy), hr⟩
    · obtain ⟨y, hy, hr⟩ := h21 i x h
      exact ⟨y, (nsLookup_nsAppend_some e1 i e2' y).mpr (Or.inr ⟨hn, hy, hall⟩), hr⟩
  · obtain ⟨hn, h⟩ := (nsLookupMod_nsAppend_none e1 e2' p).mp hp
    exact (nsLookupMod_nsAppend_none e1 e2 p).mpr ⟨hn, h.imp (h22 p) (fun h => h)⟩

/- HOL4: !R mn e1 e1' e2 e2'.
    nsSub (\id. R (Long mn id)) e1 e1' ∧
    nsSub R e2 e2'
    ⇒
    nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2') -/
theorem nsSub_nsAppend_lift :
    ∀ (R : id M N → A → B → Prop) (mn : M) (e1 : «namespace» M N A) (e1' : «namespace» M N B)
      (e2 : «namespace» M N A) (e2' : «namespace» M N B),
      nsSub (fun i => R (Long mn i)) e1 e1' ∧ nsSub R e2 e2' →
        nsSub R (nsAppend (nsLift mn e1) e2) (nsAppend (nsLift mn e1') e2') := by
  rintro R mn e1 e1' e2 e2' ⟨⟨h11, h12⟩, ⟨h21, h22⟩⟩
  refine ⟨fun i x hx => ?_, fun p hp => ?_⟩
  · cases i with
    | Short z =>
      rw [(nsLookup_nsLift_append mn e1 e2 mn (Short z) z).1] at hx
      obtain ⟨y, hy, hr⟩ := h21 _ x hx
      exact ⟨y, by rw [(nsLookup_nsLift_append mn e1' e2' mn (Short z) z).1]; exact hy, hr⟩
    | Long a j =>
      rw [(nsLookup_nsLift_append mn e1 e2 a j (id_to_n j)).2] at hx
      by_cases hm : mn = a
      · subst hm
        rw [if_pos rfl] at hx
        obtain ⟨y, hy, hr⟩ := h11 j x hx
        exact ⟨y, by rw [(nsLookup_nsLift_append mn e1' e2' mn j (id_to_n j)).2, if_pos rfl]; exact hy,
          hr⟩
      · rw [if_neg hm] at hx
        obtain ⟨y, hy, hr⟩ := h21 _ x hx
        exact ⟨y, by rw [(nsLookup_nsLift_append mn e1' e2' a j (id_to_n j)).2, if_neg hm]; exact hy,
          hr⟩
  · cases p with
    | nil => rw [Aux.nsLookupMod_nil] at hp; cases hp
    | cons a q =>
      rw [Aux.nsLookupMod_lift_append_cons] at hp ⊢
      by_cases hm : mn = a
      · rw [if_pos hm] at hp ⊢
        exact h12 q hp
      · rw [if_neg hm] at hp ⊢
        exact h22 _ hp

/- HOL4: !R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2 -/
theorem alist_rel_restr_thm :
    ∀ (R : K → A → B → Prop) (e1 : List (K × A)) (e2 : List (K × B)) (keys : List K),
      alist_rel_restr R e1 e2 keys ↔
        ∀ k, k ∈ keys → ∃ v1 v2, ALOOKUP e1 k = some v1 ∧ ALOOKUP e2 k = some v2 ∧ R k v1 v2 := by
  intro R e1 e2 keys
  induction keys with
  | nil => simp [alist_rel_restr]
  | cons k1 ks ih =>
    simp only [alist_rel_restr]
    cases h1 : ALOOKUP e1 k1 with
    | none =>
      constructor
      · intro h; exact h.elim
      · intro h
        obtain ⟨w1, w2, hw1, _, _⟩ := h k1 (List.mem_cons.mpr (Or.inl rfl))
        rw [h1] at hw1
        cases hw1
    | some v1 =>
      cases h2 : ALOOKUP e2 k1 with
      | none =>
        constructor
        · intro h; exact h.elim
        · intro h
          obtain ⟨w1, w2, _, hw2, _⟩ := h k1 (List.mem_cons.mpr (Or.inl rfl))
          rw [h2] at hw2
          cases hw2
      | some v2 =>
        simp only []
        rw [ih]
        constructor
        · rintro ⟨hr, hall⟩ k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact ⟨v1, v2, h1, h2, hr⟩
          · exact hall k hk
        · intro h
          refine ⟨?_, fun k hk => h k (List.mem_cons.mpr (Or.inr hk))⟩
          obtain ⟨w1, w2, hw1, hw2, hr⟩ := h k1 (List.mem_cons.mpr (Or.inl rfl))
          rw [h1] at hw1
          rw [h2] at hw2
          cases hw1
          cases hw2
          exact hr

/- HOL4: !l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2') -/
theorem alistSub_cong :
    ∀ (l1 : List (K × A)) (l2 : List (K × B)) (l1' : List (K × A)) (l2' : List (K × B))
      (R R' : K → A → B → Prop),
      l1 = l1' ∧ l2 = l2' ∧
          (∀ n x y, ALOOKUP l1' n = some x ∧ ALOOKUP l2' n = some y → (R n x y ↔ R' n x y)) →
        (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  rintro l1 l2 l1' l2' R R' ⟨rfl, rfl, h⟩
  unfold alistSub
  exact Aux.alist_rel_restr_congr R R' l1 l2 (fun x v1 v2 h1 h2 => h x v1 v2 ⟨h1, h2⟩) _

/- HOL4: !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k) -/
theorem nsLookup_FOLDR_nsLift :
    ∀ (e : «namespace» M N V) (p : List M) (k : N),
      nsLookup (List.foldr nsLift e p) (mk_id p k) = nsLookup e (Short k) := by
  intro e p k
  induction p with
  | nil => rfl
  | cons a p ih => simp [mk_id, nsLookup_nsLift, ih]

theorem Aux.lookup_foldr_lift (e : «namespace» M N V) :
    ∀ (p : List M) (i : id M N) (v : V),
      nsLookup (List.foldr nsLift e p) i = some v ↔
        ∃ p2 n, i = mk_id (p ++ p2) n ∧ nsLookup e (mk_id p2 n) = some v := by
  intro p
  induction p with
  | nil =>
    intro i v
    simp only [List.foldr_nil, List.nil_append]
    constructor
    · intro h
      exact ⟨id_to_mods i, id_to_n i, (mk_id_thm i).symm, by rw [mk_id_thm]; exact h⟩
    · rintro ⟨p2, n, hi, h⟩
      subst hi
      exact h
  | cons a p ih =>
    intro i v
    rw [List.foldr_cons, nsLookup_nsLift]
    cases i with
    | Short z => simp [mk_id]
    | Long b j =>
      simp only []
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, ih j v]
        simp [mk_id]
      · have hba : b ≠ a := fun h => hab h.symm
        rw [if_neg hab]
        simp [mk_id, hba]

/- HOL4: !e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v) -/
theorem nsLookup_FOLDR_nsLift_some :
    ∀ (e : «namespace» M N V) (p : List M) (i : id M N) (v : V),
      nsLookup (List.foldr nsLift e p) i = some v ↔
        (p = [] ∧ nsLookup e i = some v) ∨
        (p ≠ [] ∧ ∃ p2 n, i = mk_id (p ++ p2) n ∧ nsLookup e (mk_id p2 n) = some v) := by
  intro e p i v
  rw [Aux.lookup_foldr_lift]
  by_cases hp : p = []
  · subst hp
    rw [← Aux.lookup_foldr_lift e [] i v]
    simp
  · simp [hp]

/- HOL4: !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE
   Lean: HOL4 `⇔` binds weaker than `⇒`, so the right side is the whole implication.
   `IS_PREFIX p1 p2` is `p2 ≼ p1`, i.e. `p2 <+: p1`. -/
theorem nsLookupMod_FOLDR_nsLift_none :
    ∀ (e : «namespace» M N V) (p1 p2 : List M),
      nsLookupMod (List.foldr nsLift e p1) p2 = none ↔
        ((p2 <+: p1 ∨ p1 <+: p2) → ∃ p3, p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none) := by
  intro e p1
  induction p1 with
  | nil =>
    intro p2
    constructor
    · intro h _
      exact ⟨p2, rfl, h⟩
    · intro h
      obtain ⟨p3, hp3, h3⟩ := h (Or.inr ⟨p2, rfl⟩)
      rw [List.nil_append] at hp3
      subst hp3
      exact h3
  | cons a p1 ih =>
    intro p2
    cases p2 with
    | nil =>
      constructor
      · intro h
        rw [List.foldr_cons, Aux.nsLookupMod_nil] at h
        cases h
      · intro h
        obtain ⟨p3, h3, _⟩ := h (Or.inl ⟨a :: p1, rfl⟩)
        simp at h3
    | cons b p2 =>
      rw [List.foldr_cons, nsLookupMod_nsLift]
      simp only []
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, ih p2]
        simp [List.cons_prefix_cons]
      · have hba : b ≠ a := fun h => hab h.symm
        rw [if_neg hab]
        simp [List.cons_prefix_cons, hab, hba]

/- HOL4: !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 -/
theorem nsAll2_conj :
    ∀ (P Q : id M N → A → B → Prop) (e1 : «namespace» M N A) (e2 : «namespace» M N B),
      nsAll2 (fun i x y => P i x y ∧ Q i x y) e1 e2 ↔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  intro P Q e1 e2
  have h1 := nsSub_conj P Q e1 e2
  have h2 := nsSub_conj (fun x y z => P x z y) (fun x y z => Q x z y) e2 e1
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨a, b⟩ := h1.mp ha
    obtain ⟨c, d⟩ := h2.mp hb
    exact ⟨⟨a, c⟩, ⟨b, d⟩⟩
  · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩
    exact ⟨h1.mpr ⟨a, b⟩, h2.mpr ⟨c, d⟩⟩

/- HOL4: !R e1 e2 n v1.
    nsLookup e1 n = SOME v1 ∧
    nsAll2 R e1 e2
    ⇒
    ?v2. nsLookup e2 n = SOME v2 ∧ R n v1 v2 -/
theorem nsAll2_nsLookup1 :
    ∀ (R : id M N → A → B → Prop) (e1 : «namespace» M N A) (e2 : «namespace» M N B)
      (n : id M N) (v1 : A),
      nsLookup e1 n = some v1 ∧ nsAll2 R e1 e2 → ∃ v2, nsLookup e2 n = some v2 ∧ R n v1 v2 := by
  rintro R e1 e2 n v1 ⟨h, ⟨⟨h1, _⟩, _⟩⟩
  exact h1 n v1 h

/- HOL4: !R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2 -/
theorem nsAll2_nsLookup2 :
    ∀ (R : id M N → A → B → Prop) (e1 : «namespace» M N A) (e2 : «namespace» M N B)
      (n : id M N) (v2 : B),
      nsLookup e2 n = some v2 ∧ nsAll2 R e1 e2 → ∃ v1, nsLookup e1 n = some v1 ∧ R n v1 v2 := by
  rintro R e1 e2 n v2 ⟨h, ⟨_, ⟨h2, _⟩⟩⟩
  exact h2 n v2 h

/- HOL4: !R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE) -/
theorem nsAll2_nsLookup_none :
    ∀ (R : id M N → A → B → Prop) (e1 : «namespace» M N A) (e2 : «namespace» M N B)
      (n : id M N),
      nsAll2 R e1 e2 → (nsLookup e1 n = none ↔ nsLookup e2 n = none) := by
  rintro R e1 e2 n ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
  constructor
  · intro h
    cases h' : nsLookup e2 n with
    | none => rfl
    | some v =>
      obtain ⟨w, hw, _⟩ := h2 n v h'
      rw [h] at hw
      cases hw
  · intro h
    cases h' : nsLookup e1 n with
    | none => rfl
    | some v =>
      obtain ⟨w, hw, _⟩ := h1 n v h'
      rw [h] at hw
      cases hw

/- HOL4: !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsAll2_nsBind :
    ∀ (R : id M N → A → B → Prop) (x : N) (v1 : A) (v2 : B) (e1 : «namespace» M N A)
      (e2 : «namespace» M N B),
      R (Short x) v1 v2 ∧ nsAll2 R e1 e2 → nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := by
  rintro R x v1 v2 e1 e2 ⟨hr, h1, h2⟩
  exact ⟨nsSub_nsBind R x v1 v2 e1 e2 ⟨hr, h1⟩, nsSub_nsBind _ x v2 v1 e2 e1 ⟨hr, h2⟩⟩

/- HOL4: !R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) -/
theorem nsAll2_nsBindList :
    ∀ (R : id M N → A → B → Prop) (l1 : List (N × A)) (l2 : List (N × B))
      (e1 : «namespace» M N A) (e2 : «namespace» M N B),
      List.Forall₂ (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2 →
        nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  rintro R l1 l2 e1 e2 ⟨hl, he⟩
  induction hl with
  | nil => exact he
  | @cons a b l1 l2 hab _ ih =>
    obtain ⟨x, y⟩ := a
    obtain ⟨x', y'⟩ := b
    obtain ⟨rfl, hr⟩ := hab
    exact nsAll2_nsBind R x y y' _ _ ⟨hr, ih⟩

theorem Aux.nsSub_append_of (R : id M N → A → B → Prop) (e1 e1' : «namespace» M N A)
    (e2 e2' : «namespace» M N B) (h1 : nsSub R e1 e2) (h1' : nsSub R e1' e2')
    (hl : ∀ i, nsLookup e1 i = none → nsLookup e2 i = none)
    (hm : ∀ p, nsLookupMod e1 p = none → nsLookupMod e2 p = none) :
    nsSub R (nsAppend e1 e1') (nsAppend e2 e2') := by
  obtain ⟨a1, a2⟩ := h1
  obtain ⟨c1, c2⟩ := h1'
  refine ⟨fun i x hx => ?_, fun p hp => ?_⟩
  · rcases (nsLookup_nsAppend_some e1 i e1' x).mp hx with h | ⟨hn, h, hall⟩
    · obtain ⟨y, hy, hr⟩ := a1 i x h
      exact ⟨y, (nsLookup_nsAppend_some e2 i e2' y).mpr (Or.inl hy), hr⟩
    · obtain ⟨y, hy, hr⟩ := c1 i x h
      exact ⟨y, (nsLookup_nsAppend_some e2 i e2' y).mpr
        (Or.inr ⟨hl i hn, hy, fun p1 p2 hp => hm p1 (hall p1 p2 hp)⟩), hr⟩
  · obtain ⟨hn, h⟩ := (nsLookupMod_nsAppend_none e2 e2' p).mp hp
    refine (nsLookupMod_nsAppend_none e1 e1' p).mpr ⟨a2 p hn, ?_⟩
    rcases h with h | ⟨p1, p2, e3, hp1, hp2, hp3⟩
    · exact Or.inl (c2 p h)
    · cases hc : nsLookupMod e1 p1 with
      | none => rw [hm p1 hc] at hp3; cases hp3
      | some e4 => exact Or.inr ⟨p1, p2, e4, hp1, hp2, hc⟩

/- HOL4: !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') -/
theorem nsAll2_nsAppend :
    ∀ (R : id M N → A → B → Prop) (e1 e1' : «namespace» M N A) (e2 e2' : «namespace» M N B),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' → nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  rintro R e1 e1' e2 e2' ⟨⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩, ⟨hc, hd⟩⟩
  have hl1 : ∀ i, nsLookup e1 i = none → nsLookup e2 i = none := by
    intro i h
    cases h' : nsLookup e2 i with
    | none => rfl
    | some w =>
      obtain ⟨u, hu, _⟩ := b1 i w h'
      rw [h] at hu
      cases hu
  have hl2 : ∀ i, nsLookup e2 i = none → nsLookup e1 i = none := by
    intro i h
    cases h' : nsLookup e1 i with
    | none => rfl
    | some w =>
      obtain ⟨u, hu, _⟩ := a1 i w h'
      rw [h] at hu
      cases hu
  exact ⟨Aux.nsSub_append_of R e1 e1' e2 e2' ⟨a1, a2⟩ hc hl1 b2,
    Aux.nsSub_append_of _ e2 e2' e1 e1' ⟨b1, b2⟩ hd hl2 a2⟩

/- HOL4: !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2) -/
theorem nsAll2_alist_to_ns :
    ∀ (R : id M N → A → B → Prop) (l1 : List (N × A)) (l2 : List (N × B)),
      List.Forall₂ (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 →
        nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := by
  intro R l1 l2 h
  have := nsAll2_nsBindList R l1 l2 (Bind [] []) (Bind [] []) ⟨h, nsAll2_nsEmpty R⟩
  rw [Aux.nsBindList_Bind, Aux.nsBindList_Bind, List.append_nil, List.append_nil] at this
  exact this

theorem Aux.lift_lk (mn : M) (e : «namespace» M N V) (i : id M N) (z : V) :
    nsLookup (nsLift mn e) (Long mn i) = some z ↔ nsLookup e i = some z := by
  rw [nsLookup_nsLift]
  simp

theorem Aux.lift_lkm (mn : M) (e : «namespace» M N V) (p : List M) :
    nsLookupMod (nsLift mn e) (mn :: p) = nsLookupMod e p := by
  rw [nsLookupMod_nsLift]
  simp

theorem Aux.lift_back (mn : M) (e : «namespace» M N V) (i : id M N) (z : V)
    (h : nsLookup (nsLift mn e) i = some z) : ∃ j, i = Long mn j ∧ nsLookup e j = some z := by
  rw [nsLookup_nsLift] at h
  cases i with
  | Short _ => simp at h
  | Long a j =>
    by_cases hm : mn = a
    · subst hm
      simp at h
      exact ⟨j, rfl, h⟩
    · simp [hm] at h

theorem Aux.lift_backm (mn : M) (e : «namespace» M N V) (e' : «namespace» M N W) (p : List M)
    (h : ∀ q, nsLookupMod e q = none → nsLookupMod e' q = none)
    (hp : nsLookupMod (nsLift mn e) p = none) : nsLookupMod (nsLift mn e') p = none := by
  rw [nsLookupMod_nsLift] at hp ⊢
  cases p with
  | nil => simp at hp
  | cons a q =>
    by_cases hm : mn = a
    · subst hm
      simp at hp ⊢
      exact h q hp
    · simp [hm]

/- HOL4: !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2 -/
theorem nsAll2_nsLift :
    ∀ (R : id M N → A → B → Prop) (mn : M) (e1 : «namespace» M N A) (e2 : «namespace» M N B),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔ nsAll2 (fun i => R (Long mn i)) e1 e2 := by
  intro R mn e1 e2
  constructor
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    unfold nsAll2 nsSub
    refine ⟨⟨fun i x hx => ?_, fun p hp => ?_⟩, ⟨fun i y hy => ?_, fun p hp => ?_⟩⟩
    · obtain ⟨y, hy, hr⟩ := a1 (Long mn i) x ((Aux.lift_lk mn e1 i x).mpr hx)
      exact ⟨y, (Aux.lift_lk mn e2 i y).mp hy, hr⟩
    · have := a2 (mn :: p) (by rw [Aux.lift_lkm]; exact hp)
      rw [Aux.lift_lkm] at this
      exact this
    · obtain ⟨x, hx, hr⟩ := b1 (Long mn i) y ((Aux.lift_lk mn e2 i y).mpr hy)
      exact ⟨x, (Aux.lift_lk mn e1 i x).mp hx, hr⟩
    · have := b2 (mn :: p) (by rw [Aux.lift_lkm]; exact hp)
      rw [Aux.lift_lkm] at this
      exact this
  · rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩
    unfold nsAll2 nsSub
    refine ⟨⟨fun i x hx => ?_, fun p hp => ?_⟩, ⟨fun i y hy => ?_, fun p hp => ?_⟩⟩
    · obtain ⟨j, rfl, hj⟩ := Aux.lift_back mn e1 i x hx
      obtain ⟨y, hy, hr⟩ := a1 j x hj
      exact ⟨y, (Aux.lift_lk mn e2 j y).mpr hy, hr⟩
    · exact Aux.lift_backm mn e2 e1 p a2 hp
    · obtain ⟨j, rfl, hj⟩ := Aux.lift_back mn e2 i y hy
      obtain ⟨x, hx, hr⟩ := b1 j y hj
      exact ⟨x, (Aux.lift_lk mn e1 j x).mpr hx, hr⟩
    · exact Aux.lift_backm mn e1 e2 p b2 hp

/- HOL4: !f l. nsMap f (alist_to_ns l) = alist_to_ns (MAP (\(k,v). (k, f v)) l) -/
theorem nsMap_alist_to_ns :
    ∀ (f : V → W) (l : List (N × V)),
      nsMap f (alist_to_ns l : «namespace» M N V) = alist_to_ns (List.map (fun (k, v) => (k, f v)) l) := by
  intro f l
  rw [alist_to_ns, Aux.nsMap_Bind, List.map_nil, alist_to_ns]

/- HOL4: ∀g e f. nsMap f (nsMap g e) = nsMap (f o g) e -/
theorem nsMap_compose :
    ∀ (g : V → W) (e : «namespace» M N V) (f : W → X), nsMap f (nsMap g e) = nsMap (f ∘ g) e := by
  intro g e f
  refine Aux.ns_induction (P := fun e => nsMap f (nsMap g e) = nsMap (f ∘ g) e)
    (fun vs ms ih => ?_) e
  simp only [Aux.nsMap_Bind, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  exact congrArg (Prod.mk p.1) (ih p hp)

/- HOL4: ∀ns. nsMap I ns = ns -/
theorem nsMap_I : ∀ (ns : «namespace» M N V), nsMap _root_.id ns = ns := by
  intro ns
  refine Aux.ns_induction (P := fun e => nsMap _root_.id e = e) (fun vs ms ih => ?_) ns
  show nsMap _root_.id (Bind vs ms) = Bind vs ms
  rw [Aux.nsMap_Bind]
  congr 1
  · exact Aux.map_eq_self _ vs (fun p _ => rfl)
  · exact Aux.map_eq_self _ ms (fun p hp => (congrArg (Prod.mk p.1) (ih p hp)).trans rfl)

/- HOL4: !n1 n2 f. nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2) -/
theorem nsMap_nsAppend :
    ∀ (n1 n2 : «namespace» M N V) (f : V → W),
      nsMap f (nsAppend n1 n2) = nsAppend (nsMap f n1) (nsMap f n2) := by
  intro n1 n2 f
  obtain ⟨v1, m1⟩ := n1
  obtain ⟨v2, m2⟩ := n2
  simp [Aux.nsAppend_Bind, Aux.nsMap_Bind]

/- HOL4: !n x f. nsLookupMod (nsMap f n) x = OPTION_MAP (nsMap f) (nsLookupMod n x) -/
theorem nsLookupMod_nsMap :
    ∀ (n : «namespace» M N V) (x : List M) (f : V → W),
      nsLookupMod (nsMap f n) x = Option.map (nsMap f) (nsLookupMod n x) := by
  intro n x f
  induction x generalizing n with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a p ih =>
    obtain ⟨vs, ms⟩ := n
    rw [Aux.nsMap_Bind, Aux.nsLookupMod_cons, Aux.nsLookupMod_cons, Aux.ALOOKUP_map]
    cases ALOOKUP ms a with
    | none => rfl
    | some e => exact ih e

/- HOL4: nsOpen path (nsMap f env) = OPTION_MAP (nsMap f) (nsOpen path env) -/
theorem nsOpen_nsMap (path : List M) (f : V → W) (env : «namespace» M N V) :
    nsOpen path (nsMap f env) = Option.map (nsMap f) (nsOpen path env) := by
  unfold nsOpen
  by_cases h : path.isEmpty <;> simp [h, nsLookupMod_nsMap]

/- HOL4: !n x f. nsLookup (nsMap f n) x = OPTION_MAP f (nsLookup n x) -/
theorem nsLookup_nsMap :
    ∀ (n : «namespace» M N V) (x : id M N) (f : V → W),
      nsLookup (nsMap f n) x = Option.map f (nsLookup n x) := by
  intro n x f
  induction x generalizing n with
  | Short z =>
    obtain ⟨vs, ms⟩ := n
    rw [Aux.nsMap_Bind, Aux.nsLookup_short, Aux.nsLookup_short, Aux.ALOOKUP_map]
  | Long a j ih =>
    obtain ⟨vs, ms⟩ := n
    rw [Aux.nsMap_Bind, Aux.nsLookup_long, Aux.nsLookup_long, Aux.ALOOKUP_map]
    cases ALOOKUP ms a with
    | none => rfl
    | some e => exact ih e

/- HOL4: !f n P. nsAll P (nsMap f n) ⇔ nsAll (\x y. P x (f y)) n -/
theorem nsAll_nsMap :
    ∀ (f : V → W) (n : «namespace» M N V) (P : id M N → W → Prop),
      nsAll P (nsMap f n) ↔ nsAll (fun x y => P x (f y)) n := by
  intro f n P
  constructor
  · intro h i x hx
    exact h i (f x) (by simp [nsLookup_nsMap, hx])
  · intro h i y hy
    rw [nsLookup_nsMap] at hy
    cases hx : nsLookup n i with
    | none => rw [hx] at hy; simp at hy
    | some x =>
      rw [hx] at hy
      simp at hy
      subst hy
      exact h i x hx

/- HOL4: !f n mn. nsLift mn (nsMap f n) = nsMap f (nsLift mn n) -/
theorem nsLift_nsMap :
    ∀ (f : V → W) (n : «namespace» M N V) (mn : M), nsLift mn (nsMap f n) = nsMap f (nsLift mn n) := by
  intro f n mn
  simp [nsLift, Aux.nsMap_Bind]

/- HOL4: !R f n1 n2.
    nsSub R (nsMap f n1) (nsMap f n2) ⇔ nsSub (\id x y. R id (f x) (f y)) n1 n2 -/
theorem nsSub_nsMap :
    ∀ (R : id M N → W → W → Prop) (f : V → W) (n1 n2 : «namespace» M N V),
      nsSub R (nsMap f n1) (nsMap f n2) ↔ nsSub (fun i x y => R i (f x) (f y)) n1 n2 := by
  intro R f n1 n2
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨w, hw, hr⟩ := h1 i (f x) (by simp [nsLookup_nsMap, hx])
      rw [nsLookup_nsMap] at hw
      cases hy : nsLookup n2 i with
      | none => rw [hy] at hw; simp at hw
      | some y =>
        rw [hy] at hw
        simp at hw
        subst hw
        exact ⟨y, rfl, hr⟩
    · have := h2 p (by simp [nsLookupMod_nsMap, hp])
      simpa [nsLookupMod_nsMap] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i w hw => ?_, fun p hp => ?_⟩
    · rw [nsLookup_nsMap] at hw
      cases hx : nsLookup n1 i with
      | none => rw [hx] at hw; simp at hw
      | some x =>
        rw [hx] at hw
        simp at hw
        subst hw
        obtain ⟨y, hy, hr⟩ := h1 i x hx
        exact ⟨f y, by simp [nsLookup_nsMap, hy], hr⟩
    · rw [nsLookupMod_nsMap] at hp ⊢
      simp at hp ⊢
      exact h2 p hp

/- HOL4: !x n. x ∈ nsDom n ⇔ ?v. nsLookup n x = SOME v -/
theorem nsLookup_nsDom :
    ∀ (x : id M N) (n : «namespace» M N V), x ∈ nsDom n ↔ ∃ v, nsLookup n x = some v := by
  intro x n
  exact Iff.rfl

/- HOL4: !l. nsDomMod (alist_to_ns l) = {[]} -/
theorem nsDomMod_alist_to_ns :
    ∀ (l : List (N × V)), nsDomMod (alist_to_ns l : «namespace» M N V) = {[]} := by
  intro l
  apply Aux.set_ext
  intro p
  rw [Aux.mem_nsDomMod, Aux.mem_singleton]
  cases p with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a q => simp [nsLookupMod_alist_to_ns]

/- HOL4: (?x. y = SOME x) ⇔ y ≠ NONE -/
theorem lemma (y : Option A) : (∃ x, y = some x) ↔ y ≠ none := by
  constructor
  · rintro ⟨x, rfl⟩ h
    cases h
  · intro h
    cases y with
    | none => exact absurd rfl h
    | some x => exact ⟨x, rfl⟩

theorem Aux.mem_nsDom_nsAppend (a b : «namespace» M N V) (i : id M N) :
    i ∈ nsDom (nsAppend a b) ↔
      i ∈ nsDom a ∨ (i ∉ nsDom a ∧ i ∈ nsDom b ∧
        ∀ p1 p2, p1 ≠ [] ∧ id_to_mods i = p1 ++ p2 → p1 ∉ nsDomMod a) := by
  simp only [Aux.mem_nsDom, Aux.mem_nsDomMod]
  constructor
  · rintro ⟨v, hv⟩
    rcases (nsLookup_nsAppend_some a i b v).mp hv with h | ⟨hn, h, hall⟩
    · exact Or.inl ⟨v, h⟩
    · refine Or.inr ⟨?_, ⟨v, h⟩, fun p1 p2 hp => ?_⟩
      · rintro ⟨w, hw⟩
        rw [hn] at hw
        cases hw
      · rintro ⟨e, he⟩
        rw [hall p1 p2 hp] at he
        cases he
  · rintro (⟨v, h⟩ | ⟨hn, ⟨v, h⟩, hall⟩)
    · exact ⟨v, (nsLookup_nsAppend_some a i b v).mpr (Or.inl h)⟩
    · refine ⟨v, (nsLookup_nsAppend_some a i b v).mpr (Or.inr ⟨?_, h, fun p1 p2 hp => ?_⟩)⟩
      · cases hc : nsLookup a i with
        | none => rfl
        | some w => exact absurd ⟨w, hc⟩ hn
      · cases hc : nsLookupMod a p1 with
        | none => rfl
        | some w => exact absurd ⟨w, hc⟩ (hall p1 p2 hp)

theorem Aux.mem_nsDomMod_nsAppend (a b : «namespace» M N V) (p : List M) :
    p ∈ nsDomMod (nsAppend a b) ↔
      p = [] ∨ (p ∈ nsDomMod a ∨ (p ∈ nsDomMod b ∧
        ∀ p1 p2, p1 ≠ [] ∧ p = p1 ++ p2 → p1 ∉ nsDomMod a)) := by
  by_cases hp : p = []
  · subst hp
    simp [Aux.mem_nsDomMod, Aux.nsLookupMod_nil]
  · have key := fun x => nsLookupMod_nsAppend_some x a b p
    simp only [if_neg hp] at key
    simp only [Aux.mem_nsDomMod, hp, false_or]
    constructor
    · rintro ⟨x, hx⟩
      rcases (key x).mp hx with h | ⟨h, hall⟩
      · exact Or.inl ⟨x, h⟩
      · refine Or.inr ⟨⟨x, h⟩, fun p1 p2 hq => ?_⟩
        rintro ⟨e, he⟩
        rw [hall p1 p2 hq] at he
        cases he
    · rintro (⟨x, h⟩ | ⟨⟨x, h⟩, hall⟩)
      · exact ⟨x, (key x).mpr (Or.inl h)⟩
      · refine ⟨x, (key x).mpr (Or.inr ⟨h, fun p1 p2 hq => ?_⟩)⟩
        cases hc : nsLookupMod a p1 with
        | none => rfl
        | some w => exact absurd ⟨w, hc⟩ (hall p1 p2 hq)

/- HOL4: !n1 n2 n3 n4.
    nsDom n1 = nsDom n3 ∧
    nsDom n2 = nsDom n4 ∧
    nsDomMod n1 = nsDomMod n3 ∧
    nsDomMod n2 = nsDomMod n4
    ⇒
    nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧
    nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4) -/
theorem nsDom_nsAppend_equal :
    ∀ (n1 n2 : «namespace» M N V) (n3 n4 : «namespace» M N W),
      nsDom n1 = nsDom n3 ∧ nsDom n2 = nsDom n4 ∧ nsDomMod n1 = nsDomMod n3 ∧
          nsDomMod n2 = nsDomMod n4 →
        nsDom (nsAppend n1 n2) = nsDom (nsAppend n3 n4) ∧
          nsDomMod (nsAppend n1 n2) = nsDomMod (nsAppend n3 n4) := by
  rintro n1 n2 n3 n4 ⟨hd1, hd2, hm1, hm2⟩
  constructor
  · apply Aux.set_ext
    intro i
    rw [Aux.mem_nsDom_nsAppend, Aux.mem_nsDom_nsAppend, hd1, hd2, hm1]
  · apply Aux.set_ext
    intro p
    rw [Aux.mem_nsDomMod_nsAppend, Aux.mem_nsDomMod_nsAppend, hm1, hm2]

/- HOL4: !mn n. nsDom (nsLift mn n) = IMAGE (Long mn) (nsDom n) -/
theorem nsDom_nsLift :
    ∀ (mn : M) (n : «namespace» M N V), nsDom (nsLift mn n) = pred_set.IMAGE (Long mn) (nsDom n) := by
  intro mn n
  apply Aux.set_ext
  intro i
  rw [Aux.mem_nsDom, Aux.mem_image, nsLookup_nsLift]
  cases i with
  | Short z => simp
  | Long a j =>
    by_cases h : mn = a
    · subst h
      simp [Aux.mem_nsDom]
    · simp [h]

/- HOL4: !mn n. nsDomMod (nsLift mn n) = [] INSERT IMAGE (CONS mn) (nsDomMod n) -/
theorem nsDomMod_nsLift :
    ∀ (mn : M) (n : «namespace» M N V),
      nsDomMod (nsLift mn n) = insert [] (pred_set.IMAGE (List.cons mn) (nsDomMod n)) := by
  intro mn n
  apply Aux.set_ext
  intro p
  rw [Aux.mem_nsDomMod, Aux.mem_insert, Aux.mem_image, nsLookupMod_nsLift]
  cases p with
  | nil => simp
  | cons a q =>
    by_cases h : mn = a
    · subst h
      simp [Aux.mem_nsDomMod]
    · simp [h]

/- HOL4: !n1 n2.nsDomMod n1 = {[]} ⇒ nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2 -/
theorem nsDom_nsAppend_flat :
    ∀ (n1 n2 : «namespace» M N V),
      nsDomMod n1 = {[]} → nsDom (nsAppend n1 n2) = nsDom n1 ∪ nsDom n2 := by
  intro n1 n2 h
  obtain ⟨v1, m1⟩ := n1
  obtain ⟨v2, m2⟩ := n2
  have hm := Aux.flat_of_domMod h
  subst hm
  apply Aux.set_ext
  intro i
  rw [Aux.mem_union, Aux.mem_nsDom, Aux.mem_nsDom, Aux.mem_nsDom, Aux.nsAppend_Bind,
    List.nil_append]
  cases i with
  | Short z =>
    simp only [Aux.nsLookup_short, Aux.ALOOKUP_isSome_iff]
    simp [List.map_append]
  | Long a j => simp [Aux.nsLookup_long, Aux.ALOOKUP_nil']

/- HOL4: !n1 n2.nsDomMod n1 = {[]} ⇒ nsDomMod (nsAppend n1 n2) = nsDomMod n2 -/
theorem nsDomMod_nsAppend_flat :
    ∀ (n1 n2 : «namespace» M N V), nsDomMod n1 = {[]} → nsDomMod (nsAppend n1 n2) = nsDomMod n2 := by
  intro n1 n2 h
  obtain ⟨v1, m1⟩ := n1
  obtain ⟨v2, m2⟩ := n2
  have hm := Aux.flat_of_domMod h
  subst hm
  apply Aux.set_ext
  intro p
  rw [Aux.mem_nsDomMod, Aux.mem_nsDomMod, Aux.nsAppend_Bind, List.nil_append]
  cases p with
  | nil => simp [Aux.nsLookupMod_nil]
  | cons a q => simp [Aux.nsLookupMod_cons]

/- HOL4: nsBindList [] env = env ∧
  nsBindList ((name,value)::bindings) env = nsBind name value (nsBindList bindings env) -/
theorem nsBindList_clauses (env : «namespace» M N V) (name : N) (value : V)
    (bindings : List (N × V)) :
    nsBindList [] env = env ∧
      nsBindList ((name, value) :: bindings) env = nsBind name value (nsBindList bindings env) := by
  exact ⟨rfl, rfl⟩

/- HOL4: nsBindList (bindings ++ locals) env =
  nsBindList bindings (nsBindList locals env) -/
theorem nsBindList_append (bindings locals : List (N × V)) (env : «namespace» M N V) :
    nsBindList (bindings ++ locals) env = nsBindList bindings (nsBindList locals env) := by
  obtain ⟨vs, ms⟩ := env
  simp [Aux.nsBindList_Bind, List.append_assoc]

/- HOL4: ∀bindings name env.
    nsLookup (nsBindList bindings env) (Short name) =
    case ALOOKUP bindings name of NONE => nsLookup env (Short name)
                               | SOME v => SOME v -/
theorem nsBindList_short_lookup :
    ∀ (bindings : List (N × V)) (name : N) (env : «namespace» M N V),
      nsLookup (nsBindList bindings env) (Short name) =
        match ALOOKUP bindings name with
        | none => nsLookup env (Short name)
        | some v => some v := by
  intro bindings name env
  obtain ⟨vs, ms⟩ := env
  rw [Aux.nsBindList_Bind, Aux.nsLookup_short, Aux.nsLookup_short]
  cases h : ALOOKUP bindings name with
  | none => exact Aux.ALOOKUP_append_none _ _ _ h
  | some w => exact Aux.ALOOKUP_append_some _ _ _ _ h

/- HOL4: ∀bindings env m name.
    nsLookup (nsBindList bindings env) (Long m name) =
    nsLookup env (Long m name) -/
theorem nsBindList_long_lookup :
    ∀ (bindings : List (N × V)) (env : «namespace» M N V) (m : M) (name : id M N),
      nsLookup (nsBindList bindings env) (Long m name) = nsLookup env (Long m name) := by
  intro bindings env m name
  obtain ⟨vs, ms⟩ := env
  rw [Aux.nsBindList_Bind, Aux.nsLookup_long, Aux.nsLookup_long]

/- HOL4: ALOOKUP locals fresh = NONE ⇒
  nsLookup (nsBindList locals (nsBind fresh value globals)) id =
    nsLookup (nsBind fresh value (nsBindList locals globals)) id -/
theorem nsBindList_global_bind_commute_lookup (locals : List (N × V)) (fresh : N) (value : V)
    (globals : «namespace» M N V) (i : id M N) :
    ALOOKUP locals fresh = none →
      nsLookup (nsBindList locals (nsBind fresh value globals)) i =
        nsLookup (nsBind fresh value (nsBindList locals globals)) i := by
  intro h
  obtain ⟨vs, ms⟩ := globals
  have e1 : nsBindList locals (nsBind fresh value (Bind vs ms)) =
      Bind (locals ++ (fresh, value) :: vs) ms := Aux.nsBindList_Bind _ _ _
  have e2 : nsBind fresh value (nsBindList locals (Bind vs ms)) =
      Bind ((fresh, value) :: (locals ++ vs)) ms := by
    rw [Aux.nsBindList_Bind]; rfl
  rw [e1, e2]
  cases i with
  | Short z =>
    rw [Aux.nsLookup_short, Aux.nsLookup_short, Aux.ALOOKUP_cons']
    by_cases hz : fresh = z
    · subst hz
      rw [if_pos rfl, Aux.ALOOKUP_append_none _ _ _ h, Aux.ALOOKUP_cons', if_pos rfl]
    · rw [if_neg hz]
      cases hl : ALOOKUP locals z with
      | none =>
        rw [Aux.ALOOKUP_append_none _ _ _ hl, Aux.ALOOKUP_append_none _ _ _ hl, Aux.ALOOKUP_cons',
          if_neg hz]
      | some w =>
        rw [Aux.ALOOKUP_append_some _ _ _ _ hl, Aux.ALOOKUP_append_some _ _ _ _ hl]
  | Long a j => rw [Aux.nsLookup_long, Aux.nsLookup_long]

/- HOL4: ∀bindings bindings' env env' id.
    LIST_REL (λ(x,v) (y,w). x = y ∧ R v w) bindings bindings' ∧
    OPTREL R (nsLookup env id) (nsLookup env' id) ⇒
    OPTREL R (nsLookup (nsBindList bindings env) id)
             (nsLookup (nsBindList bindings' env') id) -/
theorem nsBindList_LIST_REL_lookup (R : A → B → Prop) :
    ∀ (bindings : List (N × A)) (bindings' : List (N × B)) (env : «namespace» M N A)
      (env' : «namespace» M N B) (i : id M N),
      List.Forall₂ (fun (x, v) (y, w) => x = y ∧ R v w) bindings bindings' ∧
          Option.Rel R (nsLookup env i) (nsLookup env' i) →
        Option.Rel R (nsLookup (nsBindList bindings env) i)
          (nsLookup (nsBindList bindings' env') i) := by
  rintro bindings bindings' env env' i ⟨hl, he⟩
  induction hl with
  | nil => exact he
  | @cons a b l1 l2 hab _ ih =>
    obtain ⟨x, v⟩ := a
    obtain ⟨y, w⟩ := b
    obtain ⟨rfl, hr⟩ := hab
    show Option.Rel R (nsLookup (nsBind x v (nsBindList l1 env)) i)
      (nsLookup (nsBind x w (nsBindList l2 env')) i)
    by_cases hi : i = Short x
    · subst hi
      rw [Aux.nsLookup_nsBind_short, Aux.nsLookup_nsBind_short]
      exact Option.Rel.some hr
    · rw [Aux.nsLookup_nsBind_ne _ _ _ _ hi, Aux.nsLookup_nsBind_ne _ _ _ _ hi]
      exact ih

/- HOL4: LIST_REL (λ(x,v) (y,w). x = y ∧ R v w) bindings bindings' ⇒
  OPTREL R (ALOOKUP bindings name) (ALOOKUP bindings' name) -/
theorem ALOOKUP_LIST_REL_OPTREL (R : A → B → Prop) (bindings : List (K × A))
    (bindings' : List (K × B)) (name : K) :
    List.Forall₂ (fun (x, v) (y, w) => x = y ∧ R v w) bindings bindings' →
      Option.Rel R (ALOOKUP bindings name) (ALOOKUP bindings' name) := by
  intro h
  induction h with
  | nil => exact Option.Rel.none
  | @cons a b l1 l2 hab _ ih =>
    obtain ⟨x, v⟩ := a
    obtain ⟨y, w⟩ := b
    obtain ⟨rfl, hr⟩ := hab
    rw [Aux.ALOOKUP_cons', Aux.ALOOKUP_cons']
    by_cases hx : x = name
    · rw [if_pos hx, if_pos hx]
      exact Option.Rel.some hr
    · rw [if_neg hx, if_neg hx]
      exact ih

/- HOL4: EVERY (λentry. R (SND entry) (SND entry)) bindings ∧
  EVERY (λentry. ∀id.
    OPTREL R (nsLookup (SND entry) id) (nsLookup (SND entry) id)) modules ⇒
  ∀id. OPTREL R (nsLookup (Bind bindings modules) id)
    (nsLookup (Bind bindings modules) id) -/
theorem namespace_lookup_self_rel (R : V → V → Prop) (bindings : List (N × V))
    (modules : List (M × «namespace» M N V)) :
    list.EVERY (fun entry => R entry.2 entry.2) bindings ∧
        list.EVERY (fun entry => ∀ (i : id M N),
          Option.Rel R (nsLookup entry.2 i) (nsLookup entry.2 i)) modules →
      ∀ (i : id M N), Option.Rel R (nsLookup (Bind bindings modules) i)
        (nsLookup (Bind bindings modules) i) := by
  rintro ⟨hb, hm⟩ i
  cases i with
  | Short z =>
    rw [Aux.nsLookup_short]
    cases h : ALOOKUP bindings z with
    | none => exact Option.Rel.none
    | some v => exact Option.Rel.some ((Aux.EVERY_iff _ _).mp hb _ (Aux.ALOOKUP_mem _ _ _ h))
  | Long a j =>
    rw [Aux.nsLookup_long]
    cases h : ALOOKUP modules a with
    | none => exact Option.Rel.none
    | some e => exact (Aux.EVERY_iff _ _).mp hm _ (Aux.ALOOKUP_mem _ _ _ h) j

/- HOL4: ∀ns id v. nsLookup ns id = SOME v ⇒ v ∈ namespaceSET3 ns -/
theorem nsLookup_namespaceSET3 :
    ∀ (ns : «namespace» M N V) (i : id M N) (v : V), nsLookup ns i = some v → v ∈ namespaceSET3 ns := by
  intro ns i v
  induction i generalizing ns with
  | Short z =>
    intro h
    obtain ⟨vs, ms⟩ := ns
    rw [Aux.nsLookup_short] at h
    rw [Aux.mem_namespaceSET3]
    exact Or.inl ⟨(z, v), Aux.ALOOKUP_mem _ _ _ h, rfl⟩
  | Long a j ih =>
    intro h
    obtain ⟨vs, ms⟩ := ns
    rw [Aux.nsLookup_long] at h
    rw [Aux.mem_namespaceSET3]
    cases hA : ALOOKUP ms a with
    | none => rw [hA] at h; simp at h
    | some e =>
      rw [hA] at h
      exact Or.inr ⟨(a, e), Aux.ALOOKUP_mem _ _ _ hA, ih e h⟩

end Stage2

end namespaceProps
