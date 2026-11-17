import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Order
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.AList
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Defs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Functor
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Preorder.Chain
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic.DeriveFintype
import dep.equational_theories.AdjoinFresh
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.FactsSyntax
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.ParseImplications
import dep.equational_theories.PartialMagma
import dep.equational_theories.Preorder

set_option backward.isDefEq.respectTransparency false

set_option backward.whnf.reducibleClassField false

namespace Eq713

namespace Greedy

noncomputable section

open AdjoinFresh PartialMagma

structure Laws {α : Type} (E : PreExtension α) : Prop where
  eq713 {x y yx yxx} : yx ∈ E y x → yxx ∈ E yx x → ∃yyxx, yyxx ∈ E y yxx ∧ x ∈ E y yyxx
  law2 {x y} : y ∉ E x y
  law3 {x xx} : xx ∈ E x x → ∃ xxx, xxx ∈ E xx x

def Laws_equiv {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : Laws E) :
  Laws (Equiv.movePreExtension e E) where
  eq713 yx_mem yxx_mem := sorry
  law2 xy_mem := sorry
  law3 xx_mem := sorry

scoped instance : ExtensionRules where
  laws := Laws
  laws_equiv := Laws_equiv

class Extension1 extends ExtensionBase where
  b_eq_a : b = a

namespace Extension1

variable [Extension1]

abbrev F := Fin 3

open ExtensionBase

@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inr 0)
  | extra1 : Next (.inr 0) (.inl a) (.inr 1)
  | extra2 : Next (.inl a) (.inr 1) (.inr 2)
  | extra3 : Next (.inl a) (.inr 0) (.inr 2)
  | extra4 : Next (.inl a) (.inr 2) (.inl a)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

end Extension1

class Extension2 extends ExtensionBase where
   a_ne_b : a ≠ b

namespace Extension2

variable [Extension2]

open ExtensionBase

attribute [scoped aesop safe destruct] a_ne_b

inductive Relevant : ℕ → Prop
  | mk {d} : a ∈ d ◯ b → Relevant d

theorem Relevant.bound {d} : Relevant d →  d < dom_bound
  := sorry

abbrev F := Unit ⊕ Fin dom_bound

inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr $ .inl ())
  | extra1 {d} (h: Relevant d) : Next (.inl d) (.inr $ .inl $ ()) (.inr $ .inr ⟨d, h.bound⟩)
  | extra2 {d} (h: Relevant d) : Next (.inl d) (.inr $ .inr ⟨d, h.bound⟩) (.inl b)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

end Extension2

open ExtensionBase

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := sorry

variable (e₀ : Extension ℕ)

include e₀ in
theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op y (op y (op (op y x) x))) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := sorry

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem _root_.PartialMagma.Extension.eq713 : Equation713 (GreedyMagma e₀) := sorry

theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y := sorry

end

end Greedy

open Greedy PartialMagma

end Eq713
