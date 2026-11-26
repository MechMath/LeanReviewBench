import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Sum.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic
import dep.equational_theories.AdjoinFresh

namespace PartialMagma

abbrev PreExtension (α : Type) := α → α → Set α

abbrev Equiv.movePreExtension {α β : Type} (e : α ≃ β) (E : PreExtension β) : PreExtension α :=
  fun a b => { c | e c ∈ E (e a) (e b) }

class ExtensionRules where
  laws : ∀ {α : Type}, PreExtension α → Prop
  laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : laws E) : laws (Equiv.movePreExtension e E)

structure PreExtension.OK [r : ExtensionRules] {α : Type} (E : PreExtension α) : Prop where
  finite : Set.Finite {x : (α × α) × α | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  laws : ExtensionRules.laws E

open ExtensionRules

abbrev Extension (α : Type) [ExtensionRules] := {E : PreExtension α // E.OK}

class ExtensionBase [ExtensionRules]  where
  E : PreExtension ℕ
  ok : E.OK
  a : ℕ
  b : ℕ
  not_def {c} : c ∉ E a b

namespace ExtensionBase

variable [ExtensionRules] [ExtensionBase]

structure FreshSolution (F : Type) (E' : PreExtension (ℕ ⊕ F)) : Prop where
  base {a b c} : c ∈ E a b → (.inl c) ∈ E' (.inl a) (.inl b)
  ok : PreExtension.OK E' (α := (ℕ ⊕ F))
  ab_def : (E' (.inl a) (.inl b)).Nonempty

abbrev FreshExtension (F : Type) := {E' : PreExtension (ℕ ⊕ F) // FreshSolution F E'}

scoped infix:80 " ◯ " => E

noncomputable def dom : Finset ℕ :=
  insert a <| insert b <| ok.finite.toFinset.biUnion fun ((a, b), c) => {a, b, c}

@[scoped aesop safe forward]
theorem dom_r {a b c} (h : c ∈ a ◯ b) : b ∈ dom := sorry

noncomputable def dom_bound := dom.sup id + 1

theorem lt_dom_bound {x} (h : x ∈ dom) : x < dom_bound := sorry

namespace FreshExtension

variable {F : Type} [Countable F] (E' : FreshExtension F)

open AdjoinFresh

end FreshExtension

end ExtensionBase
